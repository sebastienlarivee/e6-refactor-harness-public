"""A typed host-only selector service, separate from the Lean warm broker.

Requests contain declaration records or complete indexed source examples and goal context.
Source record paths are provenance only: no request-supplied path is dereferenced.
This service never executes Lean or generates proof text.
Each pass receives a fresh capability; provider credentials remain on the host.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import replace
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import hashlib
import json
from pathlib import Path
import re
import secrets
import sqlite3
import threading
from typing import Any, Callable, Mapping
from uuid import uuid4

from lean_tools import decision_rerank, example_rerank
from lean_tools.rerank_service_client import canonical_json, digest, MAX_MESSAGE_BYTES
from .experiment import RerankSettings

_SHA = re.compile(r"[0-9a-f]{64}\Z")
_CONTEXT_FIELDS = {"goal", "hypotheses", "task_signature", "search_intent", "same_run_context", "source_sha256", "query"}
_UNSAFE_RECORD_FIELDS = {"path", "file", "candidate_path", "command", "argv", "proof", "body", "src"}


class DecisionService:
    def __init__(self, relay, settings: RerankSettings, *, binding: Mapping[str, str],
                 task_signature: str, root: str | Path, allowed_names: set[str] | None = None,
                 client_factory: Callable[..., Any] = decision_rerank.DecisionsClient,
                 search_extensions: bool = False, examples_index: Mapping[str, Any] | None = None):
        self.relay, self.settings = relay, settings
        self.binding = dict(binding)
        if set(self.binding) != {"task_id", "prefix_sha256", "environment_fingerprint"}:
            raise ValueError("Selector requires an exact frozen task and environment binding")
        self.task_signature = task_signature
        self.root = Path(root).resolve()
        self.root.mkdir(parents=True, exist_ok=True)
        self.allowed_names = allowed_names
        self.client_factory = client_factory
        if type(search_extensions) is not bool:
            raise ValueError("Search extensions require a frozen boolean")
        self.search_extensions = search_extensions
        self.examples_index = None
        if search_extensions:
            self.examples_index = self._prepared_examples_index(examples_index)
        self.token = secrets.token_urlsafe(32)
        self.url: str | None = None
        self._server = self._thread = None
        self._closed = False

    @classmethod
    def for_pass(cls, config: dict, capsule: Path, relay, settings: RerankSettings):
        from lean_tools import arena_workflow as arena, lean_source, goal_signature_index
        # These paths come solely from the frozen host configuration. No path
        # supplied over HTTP is dereferenced, and only the signature is sent.
        _, row = arena.load_task(Path(config["task"]))
        prefix_sha256 = lean_source.exact_source_prefix(row, Path(config["primary"])).sha256
        fingerprint = arena.measurement_environment_fingerprint(row, Path(config["primary"]),
            registry_path=Path(config["fingerprint_registry"]))
        artifact = config.get("retrieval_index")
        allowed = None
        if artifact:
            identity = artifact["identity"]
            if identity != goal_signature_index.identity(prefix_sha256, fingerprint, row["name"]):
                raise ValueError("Prepared retrieval index differs from the frozen task, prefix or environment")
            index = Path(artifact["path"]).resolve()
            if arena.sha256_file(index) != artifact["sha256"]:
                raise ValueError("Prepared retrieval index changed")
            with sqlite3.connect(index.as_uri() + "?mode=ro", uri=True) as connection:
                stored = connection.execute("SELECT value FROM metadata WHERE key='identity'").fetchone()
                if stored is None or json.loads(stored[0]) != identity:
                    raise ValueError("Prepared retrieval index metadata differs from its frozen identity")
                allowed = {item[0] for item in connection.execute("SELECT name FROM theorems")}
        return cls(relay, settings, binding={"task_id": row["name"], "prefix_sha256": prefix_sha256,
            "environment_fingerprint": fingerprint}, task_signature=row["signature"],
            root=Path(config["root"]) / "decision-service" / capsule.name, allowed_names=allowed,
            search_extensions=config.get("search_extensions", False), examples_index=config.get("examples_index"))

    def environment(self) -> dict[str, str]:
        if self.url is None or self._closed:
            raise RuntimeError("Selector service is not active")
        return {"LEAN_REFACTOR_RERANK_URL": self.url, "LEAN_REFACTOR_RERANK_TOKEN": self.token,
                "LEAN_REFACTOR_RERANK_CONFIG": json.dumps(self.settings.to_dict(), separators=(",", ":"))}

    @staticmethod
    def _file_sha256(path: Path) -> str:
        hasher = hashlib.sha256()
        with path.open("rb") as stream:
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                hasher.update(block)
        return hasher.hexdigest()

    def _prepared_examples_index(self, artifact):
        from lean_tools import proof_example_search as source
        if not isinstance(artifact, Mapping) or not {"path", "sha256", "identity"} <= set(artifact):
            raise ValueError("Search extensions require a frozen prepared example index")
        identity, checksum = artifact["identity"], artifact["sha256"]
        if (not isinstance(identity, dict) or not isinstance(checksum, str) or not _SHA.fullmatch(checksum)
                or identity.get("target") != self.binding["task_id"]
                or identity.get("prefix_sha256") != self.binding["prefix_sha256"]
                or identity.get("environment_fingerprint") != self.binding["environment_fingerprint"]
                or identity.get("task_signature_sha256") != source.sha256(self.task_signature)
                or identity.get("policy") != source.POLICY
                or identity.get("inspiration_modules")
                or identity.get("masks", {}).get("target_and_suffix") != "excluded-before-indexing"):
            raise ValueError("Prepared example index differs from the frozen task, prefix or environment")
        path = Path(artifact["path"]).resolve()
        if self._file_sha256(path) != checksum:
            raise ValueError("Prepared example index changed")
        with sqlite3.connect(path.as_uri() + "?mode=ro", uri=True) as connection:
            row = connection.execute("SELECT value FROM metadata WHERE key='identity'").fetchone()
            if row is None or source.binding(json.loads(row[0])) != identity:
                raise ValueError("Prepared example index metadata differs from its frozen identity")
        return {"path": path, "sha256": checksum, "identity": dict(identity)}

    def _validate_common(self, request: Any, *, examples: bool = False) -> tuple[list[dict], dict, dict]:
        if not isinstance(request, dict) or set(request) != {"candidates", "context", "binding"}:
            raise ValueError("Selector accepts only candidates, context and binding")
        candidates, context, binding = (request[key] for key in ("candidates", "context", "binding"))
        additional = {"examples_index_sha256", "examples_identity_sha256"} if examples else set()
        if not isinstance(binding, dict) or set(binding) != {*self.binding, "source_sha256", "goal_sha256", "pool_sha256", *additional}:
            raise ValueError("Invalid selector binding")
        if any(binding.get(key) != value for key, value in self.binding.items()):
            raise ValueError("Selector task, prefix or environment differs from this pass")
        if any(not isinstance(binding[key], str) or not _SHA.fullmatch(binding[key])
               for key in ("prefix_sha256", "source_sha256", "goal_sha256", "pool_sha256", *additional)):
            raise ValueError("Invalid selector digest")
        if not isinstance(context, dict) or set(context) - _CONTEXT_FIELDS:
            raise ValueError("Invalid selector goal context")
        if context.get("task_signature") != self.task_signature:
            raise ValueError("Selector task signature differs from the frozen task")
        if context.get("source_sha256") != binding["source_sha256"]:
            raise ValueError("Selector source digest differs from its goal context")
        if digest(context) != binding["goal_sha256"]:
            raise ValueError("Selector goal context digest mismatch")
        maximum = example_rerank.MAX_CANDIDATES if examples else self.settings.candidate_limit
        if not isinstance(candidates, list) or len(candidates) > maximum:
            raise ValueError("Selector pool exceeds the frozen candidate limit")
        if len(canonical_json(candidates)) > MAX_MESSAGE_BYTES - 1024 * 1024:
            raise ValueError("Selector pool leaves no room for a finite ranking response")
        if digest(candidates) != binding["pool_sha256"]:
            raise ValueError("Selector pool digest mismatch")
        return candidates, context, binding

    def validate(self, request: Any) -> tuple[list[dict], dict, dict]:
        candidates, context, binding = self._validate_common(request)
        for record in candidates:
            if not isinstance(record, dict) or set(record) & _UNSAFE_RECORD_FIELDS:
                raise ValueError("Selector candidates must be declaration records without paths or proof bodies")
            name = record.get("name")
            signature = record.get("type", record.get("signature"))
            if (not isinstance(name, str) or not name or not isinstance(signature, str) or not signature
                    or record.get("signature_truncated") or record.get("type_truncated")):
                raise ValueError("Selector requires exact complete declaration names and signatures")
            # The goal index enumerates theorems. Name/type oracle queries also
            # return legal definitions, instances and axioms, so their typed
            # query pool cannot be checked against that theorem-only table.
            indexed_goal = "query" not in context
            if name == self.binding["task_id"] or (indexed_goal and self.allowed_names is not None and name not in self.allowed_names):
                raise ValueError("Selector candidate is outside this exact prefix")
        # Pure schema/byte preparation completes before any provider credential
        # resolution or provider dispatch. It rejects incomplete signatures.
        if self.settings.core_config().mode == "decisions":
            decision_rerank.prepare_requests(candidates, context, config=self.settings.core_config())
        return candidates, context, binding

    def validate_examples(self, request: Any) -> tuple[list[dict], dict, dict]:
        if not self.search_extensions or self.examples_index is None:
            raise ValueError("Construction example ranking is not enabled for this frozen pass")
        candidates, context, binding = self._validate_common(request, examples=True)
        artifact = self.examples_index
        if (binding["examples_index_sha256"] != artifact["sha256"]
                or binding["examples_identity_sha256"] != digest(artifact["identity"])):
            raise ValueError("Construction example corpus differs from the frozen prepared index")
        example_rerank._validate_candidates(candidates)
        # The database is a frozen host path, never a candidate's provenance
        # path. Recheck its bytes before reading bodies, including on later calls.
        if self._file_sha256(artifact["path"]) != artifact["sha256"]:
            raise ValueError("Prepared example index changed")
        with sqlite3.connect(artifact["path"].as_uri() + "?mode=ro", uri=True) as connection:
            for record in candidates:
                row = connection.execute("SELECT record FROM examples WHERE id=?", (record["example_id"],)).fetchone()
                if row is None or canonical_json(example_rerank.index_candidate(record["example_id"], json.loads(row[0]))) != canonical_json(record):
                    raise ValueError("Construction example body or identity is outside the frozen source index")
                if record["name"] == self.binding["task_id"] or record["origin"] == "inspiration-source":
                    raise ValueError("Construction example is outside the exact source prefix/import closure")
        # Finish whole-record byte admission before credentials or ledger work.
        example_rerank.prepare_request(candidates, context, self.settings.core_config())
        return candidates, context, binding

    def rerank_examples(self, request: Any) -> dict[str, Any]:
        return self._rerank(request, examples=True)

    def rerank(self, request: Any) -> dict[str, Any]:
        return self._rerank(request)

    def _rerank(self, request: Any, *, examples: bool = False) -> dict[str, Any]:
        if self._closed:
            raise ValueError("Selector capability has been retired")
        candidates, context, binding = (self.validate_examples(request) if examples else self.validate(request))
        artifact_id = uuid4().hex
        pool_path = self.root / (artifact_id + "-pool.json")
        pool_bytes = canonical_json({"schema_version": 1, **request})
        pool_path.write_bytes(pool_bytes)
        pending: str | None = None

        def before_dispatch(call):
            nonlocal pending
            if examples:
                state = (call.get("request") or {}).get("state", {})
                call.setdefault("volume", {}).update(example_pool_bytes=len(canonical_json(state.get("examples", {}))),
                    context_bytes=len(canonical_json({key: value for key, value in state.items() if key != "examples"})),
                    state_example_count=len(state.get("examples", {})))
            pending = self.relay.begin_selector_call(call, binding)

        def on_call(call):
            nonlocal pending
            if pending is None:
                raise RuntimeError("Selector dispatch lacks its lifecycle marker")
            self.relay.settle_selector_call(pending, call)
            pending = None

        config = self.settings.core_config()
        if examples:
            config = example_rerank.bounded_config(config)
        try:
            with self.relay.selector_admission(config.timeout_seconds):
                if self._closed:
                    raise ValueError("Selector capability has been retired")
                client = self.client_factory(before_dispatch=before_dispatch, on_call=on_call)
                relay = self.relay

                class DeadlineClient:
                    def submit(self, payload, call_config):
                        timeout = relay.selector_timeout(call_config.timeout_seconds)
                        return client.submit(payload, replace(call_config, timeout_seconds=timeout))

                ranker = example_rerank if examples else decision_rerank
                result = ranker.rerank_candidates(candidates, context, config=config,
                    client=DeadlineClient(), enforce_billing=self.relay.metering_enabled)
        except Exception:
            # Exception text is deliberately not exported: a custom host
            # transport or credential resolver may put secrets in its message.
            result = {"status": "fallback", "matches": candidates, "scores": [], "calls": [],
                      "metadata": {"fallback_reason": "host_selector_unavailable"}}
        finally:
            if pending is not None:
                # A marker without a terminal callback may have been billed.
                self.relay.settle_selector_call(pending, {"dispatched": True, "usage": None,
                    "error": {"code": "missing_selector_settlement"}})
        if Counter(canonical_json(item) for item in result.get("matches", [])) != Counter(canonical_json(item) for item in candidates):
            raise ValueError("Selector changed the exact input candidate records")
        result["binding"] = binding
        result.setdefault("metadata", {}).update(transport="host_service", artifact_id=artifact_id,
            pool_artifact_sha256=digest({"schema_version": 1, **request}),
            pool_legality=("host_index_exact_source_records" if examples else
                           "host_index_name_membership" if self.allowed_names is not None and "query" not in context
                           else "client_exact_prefix_search"),
            signature_validation=("lexical_source_examples; callability_not_verified" if examples else
                                  "client_supplied_exact_records; final Lean checks remain authoritative"),
            selector_spent_usd=self.relay.status().get("selector_spent_usd"),
            metering_enabled=self.relay.metering_enabled)
        (self.root / (artifact_id + "-result.json")).write_bytes(canonical_json(result))
        # Full-pool batching repeats input state in replay evidence. Keep that
        # evidence in the host artifact, while capsules receive bounded charge,
        # timing, provider, score and hash facts once per call.
        public = {**result, "calls": [{key: value for key, value in call.items()
            if key not in {"request", "raw_response", "config"}} for call in result.get("calls", [])]}
        for call in public["calls"]:
            call.update(request_omitted=True, response_omitted=True, replay_artifact_id=artifact_id)
        if len(canonical_json(public)) > MAX_MESSAGE_BYTES:
            public = {"status": "fallback", "matches": candidates, "scores": [], "calls": [], "binding": binding,
                "metadata": {"fallback_reason": "capsule_response_byte_limit", "transport": "host_service",
                    "artifact_id": artifact_id, "selector_spent_usd": result["metadata"]["selector_spent_usd"],
                    "metering_enabled": self.relay.metering_enabled, "raw_accounting_in_host_artifact": True}}
        return public

    def __enter__(self):
        if self._server is not None or self._closed:
            raise RuntimeError("Selector service cannot be restarted")
        owner = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def setup(self):
                super().setup()
                self.connection.settimeout(owner.settings.timeout_seconds)

            def log_message(self, *args):
                pass

            def reply(self, status, value):
                data = canonical_json(value)
                self.send_response(status)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(data)))
                self.send_header("Connection", "close")
                self.end_headers()
                self.close_connection = True
                self.wfile.write(data)

            def do_POST(self):
                if (owner._closed or self.headers.get("Origin") or self.headers.get("Sec-Fetch-Site")
                        or not secrets.compare_digest(self.headers.get("Authorization", ""), "Bearer " + owner.token)):
                    self.reply(401, {"error": "Unauthorized"})
                    return
                if self.path not in {"/rerank", "/rerank-examples"} or (self.path == "/rerank-examples" and not owner.search_extensions):
                    self.reply(404, {"error": "Unsupported selector route"})
                    return
                lengths = self.headers.get_all("Content-Length", [])
                if (self.headers.get("Transfer-Encoding") or self.headers.get("Content-Encoding", "identity") != "identity"
                        or self.headers.get_content_type() != "application/json" or len(lengths) != 1
                        or not lengths[0].isdigit() or not 0 < int(lengths[0]) <= MAX_MESSAGE_BYTES):
                    self.reply(400, {"error": "Selector requires finite uncompressed JSON"})
                    return
                try:
                    raw = self.rfile.read(int(lengths[0]))
                    if len(raw) != int(lengths[0]):
                        raise ValueError("Incomplete selector request")
                    operation = owner.rerank_examples if self.path == "/rerank-examples" else owner.rerank
                    result = operation(json.loads(raw))
                    self.reply(200, result)
                except (ValueError, TypeError, KeyError, sqlite3.Error, decision_rerank.RerankError):
                    self.reply(400, {"error": "Invalid selector request or binding"})
                except OSError:
                    self.close_connection = True

            def do_GET(self):
                self.reply(404, {"error": "Unsupported selector route"})

        self._server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self._server.daemon_threads = True
        self.url = f"http://127.0.0.1:{self._server.server_port}/rerank"
        self._thread = threading.Thread(target=self._server.serve_forever, daemon=True)
        self._thread.start()
        return self

    def __exit__(self, *args):
        self._closed = True
        self.token = secrets.token_urlsafe(32)
        if self._server is not None:
            self._server.shutdown()
            self._server.server_close()
        if self._thread is not None:
            self._thread.join(timeout=2)

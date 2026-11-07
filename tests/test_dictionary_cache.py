"""Mock-native source/provenance guards; no Lean process is started."""
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from e6.deterministic_support import dictionary_cache as g


class GenericDictionaryTests(unittest.TestCase):
    row = {"name": "sample", "signature": "theorem sample : True"}
    source = row["signature"] + " := by\n  trivial\n"

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.work = Path(self.temp.name) / "private"
        self.config = {"task": str(Path(self.temp.name) / "task.json"),
                       "primary": str(Path(self.temp.name) / "project"), "task_sha256": "a" * 64}

    def scan(self, count=5):
        rows = [{"prefix_safe": True, "candidate_heuristic": True, "shape": "compound",
                 "count": 8, "nodes": 22, "roundtrip": {"status": "passed", "no_proving_calls": True,
                    "type": f"SomeClass SomeType{i}", "value": f"someDictionary{i}"}}
                for i in range(count)]
        return {"schema_version": 2, "status": "completed", "root_context_kind": "original_by_tactic_info",
                "root_start_byte": 123, "root_end_byte": 200, "local_instance_context": "captured_original_root_goal", "target_absent_from_analysis_env": True,
                "opened_proof_lambdas": False, "analysis": {"status": "completed", "proving_calls": 0,
                    "records": rows, "walk_cap_reached": True}}

    def generate(self, **changes):
        args = dict(config=self.config, source=self.source, signature=self.row["signature"],
                    workdir=self.work, timeout_seconds=900, max_candidates=4)
        args.update(changes)
        return g.generate_candidates(**args)

    def test_one_capture_fixed_cap_exact_source_edit_and_provenance(self):
        binding = {"harness_root_start_byte": 123, "harness_declaration_end_byte": 999, "source_sha256": g.digest(self.source)}
        with patch.object(g.arena, "load_task", return_value=(None, self.row)), \
             patch.object(g, "capture", return_value=(self.scan(), binding)) as capture:
            rows = self.generate(max_candidates=1000)
        self.assertEqual(1, capture.call_count)
        self.assertEqual(180, capture.call_args.args[-1])
        self.assertEqual(4, len(rows))
        for row in rows:
            self.assertEqual(g.digest(self.source), row["parent_sha256"])
            self.assertEqual(g.digest(row["source"]), row["source_sha256"])
            self.assertIs(row["requires_full_validation"], True)
            self.assertIs(row["native_full_source_validity"], False)
            edit, = row["edits"]
            self.assertEqual(self.source[:edit["start"]] + edit["new"] + self.source[edit["end"]:], row["source"])
            self.assertTrue(row["source"].endswith("  trivial\n"))
        receipt = json.loads((self.work / "dictionary-proposals.json").read_text())
        self.assertEqual(1, receipt["native_capture_calls"])
        self.assertEqual(0, receipt["proof_search_calls"])

    def test_scoped_option_by_indent_preserved(self):
        source = self.row["signature"] + " := set_option smartUnfolding false in by\n    trivial\n"
        site = g.target_site(self.row, source)
        rows = g.proposals(source, self.row, site, self.scan(1), {"harness_root_start_byte": 123, "harness_declaration_end_byte": 999}, 4)
        self.assertIn("false in by\n    letI", rows[0]["source"])
        self.assertTrue(rows[0]["source"].endswith("    trivial\n"))

    def test_current_cached_source_retains_scaffold_and_local_scope(self):
        declaration = (self.row["signature"] + " := by\n"
                       "  letI : SomeClass SomeType0 := someDictionary0\n"
                       "  have inner : True := by\n"
                       "    letI : SomeClass SomeType1 := someDictionary1\n"
                       "    trivial\n"
                       "  exact inner\n")
        task = {**self.row, "header": "import Lean\n-- α context\n", "contexts": [], "src": self.source}
        prefix = g.lean_source.render_environment(task) + g.lean_source.TARGET_BEGIN
        source = prefix + declaration + g.lean_source.TARGET_END
        site = g.target_site(task, source)
        scan = self.scan(1)
        # A dictionary discovered only in a nested proof is not root available.
        scan["analysis"]["records"].append({**scan["analysis"]["records"][0],
                                            "prefix_safe": False})
        binding = {"harness_root_start_byte": 123, "harness_declaration_end_byte": 999}
        with patch.object(g.arena, "load_task", return_value=(None, task)), \
             patch.object(g, "capture", return_value=(scan, binding)) as capture:
            rows = self.generate(source=source)
        self.assertEqual(source, capture.call_args.args[1])
        self.assertEqual(1, len(rows))
        edit, = rows[0]["edits"]
        self.assertEqual(site["insertion"], edit["start"])
        self.assertTrue(rows[0]["source"].startswith(prefix + self.row["signature"] + " := by\n"))
        self.assertTrue(rows[0]["source"].endswith("  exact inner\n" + g.lean_source.TARGET_END))
        self.assertEqual(source, rows[0]["source"][:edit["start"]] + rows[0]["source"][edit["start"] + len(edit["new"]):])
        self.assertGreater(site["by_start"], site["proof_offset_bytes"])

    def test_repeated_insertion_preserves_bounded_research_heuristic(self):
        # The census controls usefulness; the proposal layer intentionally does
        # not suppress a cache merely because its rendered letI already exists.
        binding = {"harness_root_start_byte": 123, "harness_declaration_end_byte": 999}
        scan = self.scan(1)
        scan["analysis"]["records"] *= 2
        first, = g.proposals(self.source, self.row, g.target_site(self.row, self.source), scan, binding, 4)
        source = first["source"]
        second, = g.proposals(source, self.row, g.target_site(self.row, source), scan, binding, 4)
        self.assertEqual(2, second["source"].count("  letI : SomeClass SomeType0 := someDictionary0\n"))
        self.assertEqual(g.digest(source), second["parent_sha256"])
        self.assertNotEqual(first["source_sha256"], second["source_sha256"])
        self.assertTrue(second["source"].endswith("  trivial\n"))

    def test_unsupported_shapes_never_capture(self):
        for source in (self.row["signature"] + " := True.intro\n",
                       self.row["signature"] + " := by trivial\n",
                       self.row["signature"] + " := by\n\ttrivial\n"):
            with self.subTest(source=source), patch.object(g.arena, "load_task", return_value=(None, self.row)), \
                 patch.object(g, "capture", side_effect=AssertionError("must not capture")):
                self.assertEqual([], self.generate(source=source))

    def test_signature_mismatch_and_extra_declaration_fail_closed(self):
        for changes in ({"signature": "theorem other : True"},
                        {"source": self.source + "theorem hidden : True := by trivial\n"}):
            with self.subTest(changes=changes), patch.object(g.arena, "load_task", return_value=(None, self.row)), \
                 patch.object(g, "capture", side_effect=AssertionError("must not capture")), self.assertRaises(Exception):
                self.generate(**changes)

    def test_missing_or_weakened_root_context_is_failure_not_empty(self):
        for key, value in (("root_context_kind", "closed_lambda_telescope"),
                           ("opened_proof_lambdas", True), ("root_start_byte", 124),
                           ("target_absent_from_analysis_env", False), ("schema_version", 1)):
            scan = self.scan()
            scan[key] = value
            with self.subTest(key=key), self.assertRaises(g.DictionaryDiscoveryError):
                g.proposals(self.source, self.row, g.target_site(self.row, self.source), scan,
                            {"harness_root_start_byte": 123, "harness_declaration_end_byte": 999}, 4)

    def test_prefix_auxiliary_roundtrip_and_syntax_failures_reject_entries(self):
        for key, value in (("prefix_safe", False), ("candidate_heuristic", False),
                           ("shape", "existing_local"), ("count", True), ("nodes", 2)):
            scan = self.scan(1);scan["analysis"]["records"][0][key] = value
            self.assertEqual([], g.proposals(self.source, self.row, g.target_site(self.row, self.source), scan,
                                             {"harness_root_start_byte": 123, "harness_declaration_end_byte": 999}, 4))
        for term in ("by exact existing", "sorry", "someTerm\nend", '"opaque"', "`(term)"):
            scan = self.scan(1);scan["analysis"]["records"][0]["roundtrip"]["value"] = term
            self.assertEqual([], g.proposals(self.source, self.row, g.target_site(self.row, self.source), scan,
                                             {"harness_root_start_byte": 123, "harness_declaration_end_byte": 999}, 4))

    def test_timed_out_entry_is_skipped_before_later_candidate_and_root_guards(self):
        scan = self.scan(2)
        scan["analysis"]["records"][0]["roundtrip"] = {
            "status": "failed", "max_heartbeat": True,
            "heartbeat_limit_scope": "dictionary_roundtrip"}
        binding = {"harness_root_start_byte": 123, "harness_declaration_end_byte": 999}
        site = g.target_site(self.row, self.source)
        row, = g.proposals(self.source, self.row, site, scan, binding, 4)
        self.assertEqual(1, row["census_record_index"])
        self.assertEqual("someDictionary1", row["dictionary_value"])
        self.assertEqual(g.digest(self.source), row["parent_sha256"])
        for key, value in (("target_absent_from_analysis_env", False),
                           ("root_context_kind", "closed_lambda_telescope"),
                           ("root_start_byte", 124), ("opened_proof_lambdas", True)):
            with self.subTest(key=key), self.assertRaises(g.DictionaryDiscoveryError):
                g.proposals(self.source, self.row, site, {**scan, key: value}, binding, 4)

    def test_native_failure_is_recorded_and_raised(self):
        with patch.object(g.arena, "load_task", return_value=(None, self.row)), \
             patch.object(g, "capture", side_effect=g.DictionaryDiscoveryError("native failure")), \
             self.assertRaises(g.DictionaryDiscoveryError):
            self.generate()
        receipt = json.loads((self.work / "dictionary-proposals.json").read_text())
        self.assertEqual("failed", receipt["status"])
        self.assertEqual(0, receipt["candidate_count"])

    def test_capture_mock_checks_one_compile_prefix_harness_and_output_binding(self):
        self.work.mkdir()
        prefix = SimpleNamespace(text="import Lean\n", sha256="b" * 64)
        site = g.target_site(self.row, self.source)
        def run(path, project, deadline, log):
            text = path.read_text(encoding="utf-8")
            self.assertTrue(text.endswith(self.source))
            self.assertIn("#e6_generic_dictionary_census", text)
            (self.work / "dictionary-census.json").write_text(json.dumps(self.scan()))
            return {"returncode": 0, "timed_out": False, "seconds": 1}
        with patch.object(g.lean_source, "exact_source_prefix", return_value=prefix), \
             patch.object(g.RuntimeContext, "resolve", return_value=SimpleNamespace(environment=lambda _: {})), \
             patch.object(g, "configure_native_environment", return_value={}), \
             patch.object(g.lean_launch, "workspace_guard", return_value={"toolchain": "mock"}), \
             patch.object(g.native, "_run", side_effect=run) as native:
            scan, binding = g.capture(self.config, self.source, self.row, site, self.work, 20)
        self.assertEqual(1, native.call_count)
        self.assertEqual("b" * 64, binding["prefix_sha256"])
        self.assertEqual(g.digest(self.source), binding["source_sha256"])
        self.assertEqual(g.digest((self.work / "DictionaryCapture.lean").read_bytes()), binding["harness_sha256"])
        self.assertEqual(g.digest((self.work / "dictionary-census.json").read_bytes()), binding["raw_census_sha256"])

    def test_capture_preserves_scoped_target_prefix_and_utf8_root_binding(self):
        declaration = "theorem scopedTarget (α : Type) : True := by\n  trivial\n"
        row = {"name": "scopedTarget", "signature": "theorem scopedTarget (α : Type) : True",
               "header": "-- β unchanged source\n", "contexts": [], "src": declaration}
        source = g.lean_source.render_candidate_scaffold(row)
        site = g.target_site(row, source)
        scope = ("\n-- α scoped prefix\nnamespace OriginalScope\nvariable (unused : Nat)\n"
                 "set_option maxHeartbeats 2000000 in\nomit unused in\n"
                 "open scoped OriginalScope in\nopen Nat in\n")
        for module in (False, True):
            with self.subTest(module=module):
                work = self.work / ("module" if module else "legacy")
                work.mkdir(parents=True)
                header = "module\n\npublic import Lean" if module else "import Lean"
                prefix = SimpleNamespace(text=header + scope, sha256=g.digest(header + scope))
                def run(path, project, deadline, log):
                    text = path.read_text(encoding="utf-8")
                    marker = text.rindex("#e6_generic_dictionary_census")
                    # Every original directive still wraps the census/target,
                    # and the helper is outside the original namespace.
                    self.assertTrue(text[:marker].endswith(scope))
                    self.assertLess(text.index("namespace E6GenericDictionaryCensus"), text.index("namespace OriginalScope"))
                    self.assertTrue(text.endswith(declaration))
                    imported = "public meta import Lean" if module else "import Lean"
                    self.assertIn(imported + "\n\nmeta section", text)
                    (work / "dictionary-census.json").write_text(json.dumps(self.scan()))
                    return {"returncode": 0, "timed_out": False, "seconds": 1}
                with patch.object(g.lean_source, "exact_source_prefix", return_value=prefix), \
                     patch.object(g.RuntimeContext, "resolve", return_value=SimpleNamespace(environment=lambda _: {})), \
                     patch.object(g, "configure_native_environment", return_value={}), \
                     patch.object(g.lean_launch, "workspace_guard", return_value={"toolchain": "mock"}), \
                     patch.object(g.native, "_run", side_effect=run):
                    _, binding = g.capture(self.config, source, row, site, work, 20)
                encoded = (work / "DictionaryCapture.lean").read_bytes()
                root = binding["harness_root_start_byte"]
                self.assertTrue(encoded[root:].startswith(b"by\n  trivial"))
                self.assertEqual(len(encoded.rstrip(b"\n")), binding["harness_declaration_end_byte"])
                self.assertEqual(source.encode().index(b"by\n"), binding["source_root_start_byte"])
                self.assertEqual(g.digest(prefix.text), binding["prefix_sha256"])

    def test_request_limits_and_literal_dependency_manifest(self):
        for changes in ({"timeout_seconds": float("inf")}, {"timeout_seconds": True},
                        {"max_candidates": True}, {"family": "arbitrary"}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                self.generate(**changes)
        import ast
        tree = ast.parse(Path(g.__file__).read_text(encoding="utf-8"))
        assignment = next(n for n in tree.body if isinstance(n, ast.Assign)
                          and any(isinstance(t, ast.Name) and t.id == "GENERATOR_FILES" for t in n.targets))
        self.assertEqual(g.GENERATOR_FILES, ast.literal_eval(assignment.value))
        self.assertTrue(all(not Path(p).is_absolute() for p in g.GENERATOR_FILES))
        helper = (g.SUPPORT / "DictionaryCensus.lean.inc").read_text(encoding="utf-8")
        self.assertNotIn("lambdaTelescope", helper)
        self.assertIn("root.withContext", helper)
        self.assertIn("Lean.Parser.Term.byTactic", helper)


if __name__ == "__main__":
    unittest.main()

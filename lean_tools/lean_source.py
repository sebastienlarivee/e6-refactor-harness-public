"""Frozen candidate and prefix construction shared by Lean workflow tools.

This boundary builds text; it never launches Lean, consults measurement caches,
or imports an already-completed project target module.
"""
from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, TYPE_CHECKING

from lean_tools.measurement_policy import (
    ARENA_POLICY, candidate_token_offset, resolve_scoring_policy,
)
from lean_tools.task import load_task
from lean_tools.workflow_errors import WorkflowError

if TYPE_CHECKING:
    from lean_tools.diagnostic_presentation import SourceMap

DEFAULT_HEADER = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\n\n"


TARGET_BEGIN = "-- ARENA TARGET BEGIN: edit only this declaration\n"


TARGET_END = "-- ARENA TARGET END\n"


FORBIDDEN_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b", re.IGNORECASE),
    "admit": re.compile(r"\badmit\b", re.IGNORECASE),
    "custom axiom": re.compile(r"\baxiom\b", re.IGNORECASE),
    "sorryAx": re.compile(r"\bsorryAx\b"),
    # Aesop's `add unsafe ...` describes its search phase, not an unsafe Lean
    # declaration. Restrict this guard to declaration/term introducers; Lean
    # compilation and the exact axiom audit remain the validity boundary.
    "unsafe": re.compile(
        r"\bunsafe\s+(?:(?:private|protected|public|noncomputable|partial|"
        r"nonrec|meta)\s+)*(?:def|fun|theorem|lemma|abbrev|opaque|instance|"
        r"axiom|example|structure|inductive|class)\b",
        re.IGNORECASE,
    ),
    "opaque": re.compile(r"\bopaque\b", re.IGNORECASE),
    "extern": re.compile(r"\bextern\b", re.IGNORECASE),
    "IO": re.compile(r"\bIO\."),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "reduction oracle": re.compile(r"\b(?:ofReduceBool|ofReduceNat)\b"),
    "elaboration command": re.compile(r"\b(?:run_cmd|run_elab)\b"),
    "custom elaborator": re.compile(
        r"(?m)^\s*(?:macro|macro_rules|elab|elab_rules|notation|syntax)\b"
    ),
    "implementation override": re.compile(r"@\[(?:implemented_by|extern)\b"),
    "kernel bypass": re.compile(
        r"(?:\bdebug|«debug»)\.(?:skipKernelTC\b|«skipKernelTC»)"
    ),
}


# `open ... in` and `set_option ... in` have term and tactic parsers as well
# as command parsers. Recognize only their complete local prefix; finding an
# unrelated `in` later in the body must not excuse a bare command. Comments are
# masked before matching, while string option values retain their delimiters.
_LEAN_LETTERLIKE = r"\u2100-\u214f\U0001d49c-\U0001d59f"
_SCOPED_IDENT_PART = (
    rf"(?:«[^»\r\n]+»|(?:[^\W\d]|[{_LEAN_LETTERLIKE}])[\w'!?{_LEAN_LETTERLIKE}]*)"
)
_SCOPED_RESERVED = (
    r"in|by|let|have|show|fun|forall|match|if|then|else|do|return|for|while|"
    r"unless|try|catch|finally|where|with|open|scoped|hiding|renaming|set_option|"
    r"theorem|lemma|def|abbrev|instance|example|axiom|opaque|structure|inductive|"
    r"class|initialize|namespace|section|end|attribute|mutual|export|import"
)
_SCOPED_IDENT = (
    rf"(?!(?:{_SCOPED_RESERVED})(?![\w.'!?{_LEAN_LETTERLIKE}]))"
    rf"{_SCOPED_IDENT_PART}(?:\.{_SCOPED_IDENT_PART})*"
)
_SCOPED_IDENTS = rf"{_SCOPED_IDENT}(?:\s+{_SCOPED_IDENT})*"
_SCOPED_OPEN = re.compile(
    rf"open\s+(?:scoped\s+{_SCOPED_IDENTS}"
    rf"|{_SCOPED_IDENT}\s+hiding\s+{_SCOPED_IDENTS}"
    rf"|{_SCOPED_IDENT}\s+renaming\s+{_SCOPED_IDENT}\s*(?:→|->)\s*{_SCOPED_IDENT}"
    rf"(?:\s*,\s*{_SCOPED_IDENT}\s*(?:→|->)\s*{_SCOPED_IDENT})*"
    rf"|{_SCOPED_IDENT}\s*\(\s*{_SCOPED_IDENTS}\s*\)"
    rf"|{_SCOPED_IDENTS})\s*\bin\b"
)
_SCOPED_OPTION = re.compile(
    rf"set_option\s+{_SCOPED_IDENT}\s+"
    r'(?:true|false|0[bB](?:_*[01])+|0[oO](?:_*[0-7])+|'
    r'0[xX](?:_*[0-9a-fA-F])+|[0-9](?:_*[0-9])*|"(?:[^"\\]|\\.)*"|'
    r'r(?P<raw_hashes>#*)".*?"(?P=raw_hashes))\s+in\b',
    re.DOTALL,
)
_COMMAND_TOKEN_START = re.compile(
    rf"(?<![\w.'`{_LEAN_LETTERLIKE}])"
    r"(?P<command>theorem|lemma|def|abbrev|instance|example|axiom|opaque|"
    r"structure|inductive|coinductive|class|initialize|builtin_initialize|"
    r"namespace|section|end|open|set_option|attribute|mutual|export|import|"
    r"prelude|universe|universes|variable|variables|include|omit|"
    r"unlock_limits|macro|macro_rules|elab|elab_rules|notation|syntax|deriving|"
    r"with_weak_namespace|end_local_scope|assert_not_exists|assert_not_imported|"
    r"deprecated_syntax|init_quot|docs_to_verso|deprecated_module|register_tactic_tag|"
    r"tactic_extension|recommended_spelling|gen_injective_theorems|"
    r"register_error_explanation|add_decl_doc)"
    rf"\b(?![.'!?{_LEAN_LETTERLIKE}])"
)
_LINE_HASH_COMMAND = re.compile(r"(?m)^[ \t]*#\b")
_HASH_COMMAND_TOKEN = re.compile(
    r"(?<![\w.'`])#(?:check|check_failure|check_tactic|eval|synth|exit|print|"
    r"reduce|guard|guard_msgs|time|count_heartbeats|find|lint|help|where|version|"
    r"import_path|check_assertions|with_exporting|dump_async_env_state|"
    r"show_deprecated_modules)(?![\w'])"
)
# `module` is also an ordinary Mathlib tactic. Lean only accepts a module
# header before imports, so it cannot be a successful appended command here.
_RAW_STRING_START = re.compile(r'r(#*)"')
_IDENT_CONTINUATION = re.compile(rf"[\w.'!?{_LEAN_LETTERLIKE}]")


LEAN_TOKEN_PATTERN = re.compile(
    r"[A-Za-z0-9_.'\u0080-\uffff]+|:=|=>|->|<-|<->|<=|>=|!=|==|&&|\|\||[^\s]"
)


ARENA_TOKEN_PATTERN = re.compile(
    r"[\w.']+|<;>|\?_|::|:=|=>|->|<-|<->|<=|>=|!=|==|&&|\|\||[^\s]"
)


PROJECT_MEASUREMENT_HELPER = """module

public meta import Lean.Elab.Command

public section

open Lean Elab Command

syntax (name := lrhMeasuredDecl) "lrh_measured_decl " command : command

@[command_elab lrhMeasuredDecl]
public meta def elabLrhMeasuredDecl : CommandElab := fun stx => do
  let start ← IO.getNumHeartbeats
  elabCommand
    (← `(command| set_option maxHeartbeats 0 in $(⟨stx[1]!⟩)))
  let finish ← IO.getNumHeartbeats
  logInfo m!"LRH_HEARTBEATS {(finish - start) / 1000}"
"""


def local_proof_tokens(proof_body: str, policy: str | None = None) -> list[str]:
    """Lex masked proof-body text using the selected versioned token rule.

    This returns body tokens only. Candidate scoring adds the policy's offset
    separately, so a submitted unchanged proof receives the same candidate
    treatment as every other submission.
    """
    pattern = (
        ARENA_TOKEN_PATTERN
        if resolve_scoring_policy(policy) == ARENA_POLICY else LEAN_TOKEN_PATTERN
    )
    return pattern.findall(lean_code_mask(proof_body))


def candidate_proof_token_count(proof_body: str, policy: str | None = None) -> int:
    resolved = resolve_scoring_policy(policy)
    return len(local_proof_tokens(proof_body, resolved)) + candidate_token_offset(resolved)


def ensure_section_gap(text: str) -> str:
    if text.endswith("\n\n"):
        return text
    if text.endswith("\n"):
        return text + "\n"
    return text + "\n\n"


def render_supplied_environment(row: dict[str, Any]) -> str:
    header = row.get("header")
    if header is None:
        header_text = DEFAULT_HEADER
    elif isinstance(header, str):
        header_text = header
    else:
        raise WorkflowError(f"{row['name']}: header is not a string")

    rendered = ensure_section_gap(header_text)
    contexts = row.get("contexts", [])
    if not isinstance(contexts, list):
        raise WorkflowError(f"{row['name']}: contexts is not a list")
    for index, context in enumerate(contexts):
        if not isinstance(context, dict) or not isinstance(context.get("src"), str):
            raise WorkflowError(f"{row['name']}: malformed context at index {index}")
        source = context["src"]
        occurrences = rendered.count(source)
        if occurrences > 1:
            raise WorkflowError(
                f"{row['name']}: context {index} occurs multiple times in environment"
            )
        if occurrences == 0:
            rendered = ensure_section_gap(rendered + source)
    return rendered


def render_environment(row: dict[str, Any]) -> str:
    return render_supplied_environment(row)


def lean_code_mask(
    text: str, *, mask_strings: bool = True, mask_raw_strings: bool = False
) -> str:
    """Mask comments/strings, preserving offsets and the frozen scoring lexer.

    Admission opts into raw-string masking. The default retains historical
    token-count behavior until a separately versioned scoring change.
    """
    masked: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    raw_string_end: str | None = None
    escaped = False
    while index < len(text):
        if block_depth:
            if text.startswith("/-", index):
                masked.extend((" ", " "))
                block_depth += 1
                index += 2
            elif text.startswith("-/", index):
                masked.extend((" ", " "))
                block_depth -= 1
                index += 2
            else:
                masked.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif in_line_comment:
            if text[index] == "\n":
                masked.append("\n")
                in_line_comment = False
            else:
                masked.append(" ")
            index += 1
        elif in_string and raw_string_end is not None:
            if text.startswith(raw_string_end, index):
                masked.extend(raw_string_end if not mask_strings else " " * len(raw_string_end))
                index += len(raw_string_end)
                raw_string_end = None
                in_string = False
            else:
                character = text[index]
                masked.append(character if not mask_strings or character == "\n" else " ")
                index += 1
        elif in_string:
            character = text[index]
            masked.append(character if not mask_strings or character == "\n" else " ")
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            index += 1
        elif text.startswith("--", index):
            masked.extend((" ", " "))
            in_line_comment = True
            index += 2
        elif text.startswith("/-", index):
            masked.extend((" ", " "))
            block_depth = 1
            index += 2
        elif (
            mask_raw_strings
            and text[index] == "r"
            and (index == 0 or _IDENT_CONTINUATION.fullmatch(text[index - 1]) is None)
            and (raw_start := _RAW_STRING_START.match(text, index)) is not None
        ):
            masked.extend(raw_start[0] if not mask_strings else " " * len(raw_start[0]))
            in_string = True
            raw_string_end = '"' + raw_start[1]
            index = raw_start.end()
        elif text[index] == '"':
            masked.append(" " if mask_strings else '"')
            in_string = True
            index += 1
        else:
            masked.append(text[index])
            index += 1
    return "".join(masked)


def import_header_end(prefix: str) -> tuple[int, bool]:
    """Locate the import header without consuming a scoped target command.

    Lean's module header has optional module/prelude and one identifier per
    import (Lean/Parser/Module.lean). Comments are masked without shifting
    offsets. Inserting helpers at the target boundary would consume a trailing
    `omit ... in`, `open ... in`, or scoped option instead of its declaration.
    """
    mask = lean_code_mask(prefix)
    pos = len(mask) - len(mask.lstrip())
    module = re.match(r"module\b", mask[pos:])
    if module:
        pos += module.end()
    prelude = re.match(r"\s*prelude\b", mask[pos:])
    if prelude:
        pos += prelude.end()
    identifier = r"(?:«[^»]+»|[^\W\d][\w']*)(?:\.(?:«[^»]+»|[^\W\d][\w']*))*\.?"
    pattern = re.compile(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?" + identifier)
    while match := pattern.match(mask, pos):
        pos = match.end()
    return pos, bool(module)


def has_extra_top_level_command(body: str, masked_body: str) -> bool:
    """Keep local scopes without excusing commands wrapped by `... in`.

    This is an admission guard, not a replacement for Lean's parser, compiler,
    or exact axiom audit. In particular, a local prefix must still be followed
    by a valid proof term/tactic when Lean checks the candidate.
    """
    comments_masked = lean_code_mask(body, mask_strings=False, mask_raw_strings=True)
    # Quoted identifiers can contain command keywords without introducing a
    # command. Qualified identifiers and name quotations are excluded by the
    # token boundary above. Lean accepts successive commands on the same line,
    # so a line/indentation boundary would leave a real declaration escape.
    command_mask = re.sub(
        r"«[^»]*»", lambda match: re.sub(r"[^\r\n]", "_", match[0]), masked_body
    )
    if _LINE_HASH_COMMAND.search(command_mask) or _HASH_COMMAND_TOKEN.search(command_mask):
        return True
    for command in _COMMAND_TOKEN_START.finditer(command_mask):
        start = command.start("command")
        if not (
            _SCOPED_OPEN.match(comments_masked, start)
            or _SCOPED_OPTION.match(comments_masked, start)
        ):
            return True
    return False


def candidate_text_from_bytes(source_bytes: bytes) -> str:
    """Match UTF-8 read_text newline handling without rereading a mutable path."""
    if type(source_bytes) is not bytes:
        raise WorkflowError("candidate admission requires immutable source bytes")
    try:
        return source_bytes.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
    except UnicodeDecodeError as error:
        raise WorkflowError("candidate source is not valid UTF-8") from error


def normalized_lean_code(text: str) -> str:
    return re.sub(r"\s+", " ", lean_code_mask(text)).strip()


def declaration_short_name(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def theorem_declaration_matches(text: str, name: str) -> list[re.Match[str]]:
    """Find theorem/lemma commands whose declared name has the benchmark suffix."""
    local_name = declaration_short_name(name)
    pattern = re.compile(r"\b(?:theorem|lemma)\s+([^\s({\[:]+)")
    return [
        match
        for match in pattern.finditer(lean_code_mask(text))
        if match.group(1) == local_name
        or match.group(1).endswith(f".{local_name}")
    ]


def theorem_declaration_match(text: str, name: str) -> re.Match[str] | None:
    matches = theorem_declaration_matches(text, name)
    return matches[0] if matches else None


def supported_supplied_prefix(text: str) -> bool:
    """Accept frozen attributes, scoped opens, and declaration visibility."""
    return (
        re.fullmatch(
            r"(?:(?:@\[[^\]]*\]|open\s+[^\r\n]+?\s+in)\s*)*"
            r"(?:(?:private|protected|public)\s*)?",
            lean_code_mask(text).strip(),
        )
        is not None
    )


def matching_prefixed_declaration_start(
    source: str, theorem_start: int, expected_prefix: str
) -> int:
    """Locate the frozen supplied prefix immediately before a structural match."""
    tokens = re.findall(r"\S+", lean_code_mask(expected_prefix))
    if not tokens:
        return theorem_start
    pattern = r"(?<!\S)" + r"\s+".join(re.escape(token) for token in tokens) + r"\s*$"
    match = re.search(pattern, lean_code_mask(source)[:theorem_start])
    if match is None:
        raise WorkflowError("structural source declaration changed its scoped prefix")
    return match.start()


def exact_signature_assignment_start(source: str, signature: str) -> int | None:
    """Find the assignment immediately after an exact frozen task signature."""
    if not signature:
        return None
    starts = [match.start() for match in re.finditer(re.escape(signature), source)]
    if len(starts) != 1:
        return None
    suffix_start = starts[0] + len(signature)
    assignment = re.match(
        r"[ \t\r\n]*(:=)",
        lean_code_mask(source)[suffix_start:],
    )
    if assignment is None:
        return None
    return suffix_start + assignment.start(1)


def declaration_assignment_start(
    source: str, name: str, *, signature: str | None = None
) -> int:
    """Locate a frozen signature's assignment independently of its proof term.

    Without a signature, retain the conservative supplied-source fallback for
    `by` proofs (including local scopes). A lexical delimiter scan alone cannot
    distinguish every term-local assignment in an arbitrary Lean statement.
    """
    theorem_match = theorem_declaration_match(source, name)
    if theorem_match is None:
        raise WorkflowError(f"{name}: declaration does not contain its theorem")
    masked = lean_code_mask(source)
    expected_statement = None
    if signature is not None:
        signature_match = theorem_declaration_match(signature, name)
        if signature_match is None:
            raise WorkflowError(f"{name}: frozen signature does not contain its theorem")
        expected_statement = normalized_lean_code(signature[signature_match.start() :])
    comments_masked = (
        lean_code_mask(source, mask_strings=False, mask_raw_strings=True)
        if expected_statement is None else ""
    )
    opener_to_closer = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
    closers = set(opener_to_closer.values())
    stack: list[str] = []
    index = theorem_match.end()
    while index < len(masked):
        character = masked[index]
        if character == "«":
            quoted_end = masked.find("»", index + 1)
            if quoted_end >= 0:
                index = quoted_end + 1
                continue
        elif character in opener_to_closer:
            stack.append(opener_to_closer[character])
        elif character in closers:
            if stack and stack[-1] == character:
                stack.pop()
        elif not stack and masked.startswith(":=", index):
            if expected_statement is not None:
                if normalized_lean_code(source[theorem_match.start() : index]) == expected_statement:
                    return index
            else:
                body_start = index + 2
                while True:
                    body_start += len(comments_masked[body_start:]) - len(
                        comments_masked[body_start:].lstrip()
                    )
                    scope = _SCOPED_OPTION.match(comments_masked, body_start) or _SCOPED_OPEN.match(
                        comments_masked, body_start
                    )
                    if scope is None:
                        break
                    body_start = scope.end()
                if re.match(r"by(?:[ \t\r\n]|$)", comments_masked[body_start:]):
                    return index
        index += 1
    raise WorkflowError(f"{name}: could not find the declaration-level ':='")


def supplied_assignment_start(row: dict[str, Any]) -> int:
    source = row["src"]
    if not isinstance(source, str):
        raise WorkflowError(f"{row['name']}: src is not a string")
    signature = row.get("signature")
    if not isinstance(signature, str):
        raise WorkflowError(f"{row['name']}: signature is not a string")
    theorem_match = theorem_declaration_match(source, row["name"])
    if theorem_match is None:
        raise WorkflowError(
            f"{row['name']}: supplied declaration does not contain its theorem"
        )
    leading_code = source[: theorem_match.start()]
    if not supported_supplied_prefix(leading_code):
        raise WorkflowError(
            f"{row['name']}: unsupported code precedes the supplied theorem"
        )
    exact_assignment = exact_signature_assignment_start(source, signature)
    if exact_assignment is not None:
        return exact_assignment
    return declaration_assignment_start(source, row["name"])


def validate_supplied_declaration(row: dict[str, Any], declaration: str) -> str:
    expected = row["src"].rstrip("\r\n")
    if declaration.rstrip("\r\n") != expected:
        raise WorkflowError(f"{row['name']}: supplied original declaration changed")
    body = expected[supplied_assignment_start(row) + 2 :].strip()
    if not body:
        raise WorkflowError(f"{row['name']}: supplied original proof body is empty")
    return body


def canonical_candidate_declaration(row: dict[str, Any]) -> str:
    source = row["src"]
    return f"{row['signature']} {source[supplied_assignment_start(row) :]}"


def render_candidate_scaffold(row: dict[str, Any]) -> str:
    candidate = (
        render_environment(row) + TARGET_BEGIN + canonical_candidate_declaration(row)
    )
    if not candidate.endswith("\n"):
        candidate += "\n"
    return candidate + TARGET_END


def metric_label(value: str) -> str:
    if re.fullmatch(r"[A-Za-z0-9._-]+", value) is None:
        raise WorkflowError(
            "metric label may contain only ASCII letters, digits, dot, underscore, and hyphen"
        )
    return value


def extract_candidate_declaration(
    row: dict[str, Any], candidate_text: str
) -> tuple[str, str]:
    expected_environment = render_environment(row)
    if not candidate_text.startswith(expected_environment):
        raise WorkflowError(
            f"{row['name']}: candidate changed the frozen header or ordered contexts"
        )

    remainder = candidate_text[len(expected_environment) :]
    if TARGET_BEGIN in remainder:
        if not remainder.startswith(TARGET_BEGIN):
            raise WorkflowError(
                f"{row['name']}: material appears before the target marker"
            )
        target_start = len(TARGET_BEGIN)
        target_end = remainder.find(TARGET_END, target_start)
        if target_end < 0:
            raise WorkflowError(f"{row['name']}: missing target end marker")
        declaration = remainder[target_start:target_end].rstrip("\r\n")
        if remainder[target_end + len(TARGET_END) :].strip():
            raise WorkflowError(
                f"{row['name']}: material appears after the target marker"
            )
    else:
        declaration = remainder.rstrip("\r\n")
    return declaration, validate_declaration(row, declaration)


def validate_declaration(row: dict[str, Any], declaration: str) -> str:
    signature = row["signature"]
    if not declaration.startswith(signature):
        raise WorkflowError(
            f"{row['name']}: declaration does not preserve the exact signature"
        )
    remainder = declaration[len(signature) :]
    assignment = re.match(r"^[ \t\r\n]*:=[ \t\r\n]*", remainder)
    if assignment is None:
        raise WorkflowError(f"{row['name']}: exact signature is not followed by :=")
    body = remainder[assignment.end() :].strip()
    if not body:
        raise WorkflowError(f"{row['name']}: proof body is empty")

    masked_body = lean_code_mask(body, mask_raw_strings=True)
    matches = [
        label
        for label, pattern in FORBIDDEN_PATTERNS.items()
        if pattern.search(masked_body) is not None
    ]
    if has_extra_top_level_command(body, masked_body):
        matches.append("extra top-level command")
    if matches:
        raise WorkflowError(
            f"{row['name']}: forbidden proof construct(s): {', '.join(matches)}"
        )
    return body


def normalized_signature_example(row: dict[str, Any]) -> str:
    signature = row["signature"]
    theorem_match = (
        theorem_declaration_match(signature, row["name"])
        if isinstance(signature, str)
        else None
    )
    if theorem_match is None:
        raise WorkflowError(
            f"{row['name']}: normalized signature does not contain its theorem declaration"
        )
    leading = signature[: theorem_match.start()]
    return (
        f"{leading}example{signature[theorem_match.end() :]} := by\n"
        f"  apply {row['name']} <;> assumption"
    )


def heartbeat_harness(row: dict[str, Any], declaration: str, cap: int) -> str:
    return (
        render_environment(row)
        + "set_option Elab.async false in\n"
        + f"set_option maxHeartbeats {cap} in\n"
        + declaration
        + "\n"
    )


def exact_heartbeat_audit_harness(
    row: dict[str, Any], declaration: str, cap: int = 1_000_000_000
) -> str:
    if cap <= 0:
        raise WorkflowError("exact heartbeat cap must be positive")
    return (
        render_environment(row)
        + "set_option Elab.async false in\n"
        + f"set_option maxHeartbeats {cap} in\n"
        + "#count_heartbeats in\n"
        + declaration
        + f"\n\n#print axioms {row['name']}\n"
    )


def is_project_resident(row: dict[str, Any]) -> bool:
    return bool(row.get("file_path"))


def quick_compile_harness(
    row: dict[str, Any], declaration: str, project_root: Path
) -> str:
    """Preserve the task's frozen environment without measurement commands."""
    if is_project_resident(row):
        return project_compile_harness(row, declaration, project_root, exact=False)
    return render_environment(row) + declaration.rstrip() + "\n"


def project_source_path(row: dict[str, Any], project_root: Path) -> Path:
    file_path = row.get("file_path")
    if not isinstance(file_path, str) or not file_path:
        raise WorkflowError(f"{row['name']}: no project source path is recorded")
    source_path = (project_root.resolve() / Path(file_path)).resolve()
    try:
        source_path.relative_to(project_root.resolve())
    except ValueError as error:
        raise WorkflowError(
            f"{row['name']}: project source escaped its environment root"
        ) from error
    if not source_path.is_file():
        raise WorkflowError(f"{row['name']}: project source is missing: {source_path}")
    return source_path


def project_source_has_module_header(
    row: dict[str, Any], project_root: Path
) -> bool:
    source = project_source_path(row, project_root).read_text(encoding="utf-8")
    return re.search(r"(?m)^module[^\r\n]*\r?$", source) is not None


def project_axiom_target_command(name: str) -> str:
    """Resolve the target in its original module scope after measurement."""
    return (
        "\nrun_cmd Lean.withoutExporting do\n"
        f"  let expected := `{name}\n"
        f"  let target \u2190 Lean.resolveGlobalConstNoOverload (Lean.mkIdent `_root_.{name})\n"
        "  unless Lean.privateToUserName target == expected &&\n"
        "      (target == expected || target == Lean.mkPrivateNameCore `ArenaProjectMeasured expected) do\n"
        '    throwError "axiom target resolution changed"\n'
        '  Lean.logInfo ("LRH_AUDIT_TARGET " ++ target.toString)\n'
    )


def project_axiom_audit_harness(name: str, target: str) -> str:
    # Construct Name.num components in Lean; private names do not round-trip
    # through the parser as textual identifiers. Keep #print in a non-module
    # root, where Lean imports complete transitive private proof data.
    constructor = (
        f"`{name}" if target == name
        else f"Lean.mkPrivateNameCore `ArenaProjectMeasured `{name}"
    )
    return (
        "import ArenaProjectMeasured\nimport Lean.Elab.Command\n\n"
        "run_cmd do\n"
        f"  let target := {constructor}\n"
        f"  unless target.toString == {json.dumps(target, ensure_ascii=False)} do\n"
        '    throwError "axiom target binding changed"\n'
        "  Lean.Elab.Command.elabCommand (\u2190 `(command| #print axioms $(Lean.mkIdent target)))\n"
    )


def project_compile_harness(
    row: dict[str, Any],
    declaration: str,
    project_root: Path,
    *,
    exact: bool,
    cap: int = 1_000_000_000,
) -> str:
    """Build a source prefix ending at the replaced public declaration."""
    source_path = project_source_path(row, project_root)
    source_text = source_path.read_text(encoding="utf-8")
    original = row["src"].rstrip("\r\n")
    occurrences = source_text.count(original)
    candidate = declaration.rstrip()
    if occurrences == 1:
        prefix, _ = source_text.split(original, 1)
    elif occurrences == 0:
        matches = theorem_declaration_matches(source_text, row["name"])
        if len(matches) != 1:
            raise WorkflowError(
                f"{row['name']}: expected one structural source declaration in "
                f"{source_path}, found {len(matches)}"
            )
        candidate_match = theorem_declaration_match(candidate, row["name"])
        assert candidate_match is not None
        candidate_assignment = declaration_assignment_start(
            candidate, row["name"], signature=row["signature"]
        )
        try:
            source_assignment = declaration_assignment_start(
                source_text, row["name"], signature=row["signature"]
            )
        except WorkflowError as error:
            raise WorkflowError(
                f"{row['name']}: theorem statement changed in compatibility source "
                f"{source_path}"
            ) from error
        candidate_prefix = candidate[: candidate_match.start()]
        if not supported_supplied_prefix(candidate_prefix):
            raise WorkflowError(
                f"{row['name']}: candidate has an unsupported scoped prefix"
            )
        source_start = matching_prefixed_declaration_start(
            source_text, matches[0].start(), candidate_prefix
        )
        candidate_start = 0 if candidate_prefix.strip() else candidate_match.start()
        source_signature = source_text[source_start:source_assignment]
        candidate_signature = candidate[candidate_start:candidate_assignment]
        if normalized_lean_code(source_signature) != normalized_lean_code(
            candidate_signature
        ):
            raise WorkflowError(
                f"{row['name']}: theorem statement changed in compatibility source "
                f"{source_path}"
            )
        prefix = source_text[:source_start]
    else:
        raise WorkflowError(
            f"{row['name']}: expected at most one exact source declaration in "
            f"{source_path}, found {occurrences}"
        )

    replacement = candidate
    has_module_header = re.search(r"(?m)^module[^\r\n]*\r?$", source_text) is not None
    if exact:
        if cap <= 0:
            raise WorkflowError("exact heartbeat cap must be positive")
        replacement = (
            "set_option Elab.async false in\n"
            "lrh_measured_decl " + replacement
        )
    block_docs = list(re.finditer(r"/--.*?-/", prefix, re.DOTALL))
    if block_docs and not prefix[block_docs[-1].end() :].strip():
        prefix = prefix[: block_docs[-1].start()]
    line_doc = re.search(r"(?m)(?:^[ \t]*///[^\r\n]*(?:\r?\n|$))+\s*$", prefix)
    if line_doc is not None:
        prefix = prefix[: line_doc.start()]
    harness = prefix + replacement + "\n"
    if exact:
        if has_module_header:
            module_header = re.compile(r"(?m)^(module[^\r\n]*\r?\n)")
            harness, replacements = module_header.subn(
                r"\1\nmeta import LrhMeasurement\n", harness, count=1
            )
            if replacements != 1:
                raise WorkflowError(
                    f"{row['name']}: project source has no module header for measurement"
                )
        else:
            masked_harness = lean_code_mask(harness)
            first_import = re.search(
                r"(?m)^[ \t]*(?:(?:public|meta)[ \t]+)*import\b",
                masked_harness,
            )
            if first_import is None:
                raise WorkflowError(
                    f"{row['name']}: legacy project source has no import for measurement"
                )
            insertion = first_import.start()
            harness = (
                harness[:insertion]
                + "import LrhMeasurement\n"
                + harness[insertion:]
            )
    return harness



class SourceDocumentError(WorkflowError):
    """A candidate-to-document location or target-prefix invariant failed."""


@dataclass(frozen=True)
class TaskSnapshot:
    """Immutable source inputs taken from one normalized task row."""

    name: str
    signature: str
    original_declaration: str
    supplied_environment: str
    project_relative_path: str | None


@dataclass(frozen=True)
class CandidateSnapshot:
    """Validated candidate text paired with its frozen task source inputs."""

    task: TaskSnapshot
    path: Path
    text: str
    declaration: str
    proof_body: str
    declaration_start: int

    @property
    def proof_body_start(self) -> int:
        """Code-point offset of the validated editable body in candidate text."""
        # Validation returns the stripped body as the declaration's final suffix.
        return self.declaration_start + len(self.declaration.rstrip()) - len(self.proof_body)


@dataclass(frozen=True)
class SourcePrefix:
    text: str
    kind: str
    source_path: Path | None

    @property
    def sha256(self) -> str:
        return hashlib.sha256(self.text.encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class SourceDocument:
    """Managed interactive text and the exact candidate declaration offsets."""

    task_name: str
    candidate_path: Path
    project_root: Path
    source: str
    document_kind: str
    candidate_text: str
    candidate_declaration_start: int
    declaration: str
    document_declaration_start: int

    def source_map(self) -> SourceMap:
        from lean_tools import diagnostic_presentation as presentation

        return presentation.SourceMap.for_declaration(
            self.candidate_text,
            self.source,
            self.declaration,
            candidate_start=self.candidate_declaration_start,
            generated_start=self.document_declaration_start,
        )


def snapshot_task(row: dict[str, Any]) -> TaskSnapshot:
    return TaskSnapshot(
        name=row["name"],
        signature=row["signature"],
        original_declaration=row["src"],
        supplied_environment=render_environment(row),
        project_relative_path=row.get("file_path") or None,
    )


def snapshot_candidate(
    row: dict[str, Any], candidate_text: str, candidate_path: Path
) -> CandidateSnapshot:
    declaration, body = extract_candidate_declaration(row, candidate_text)
    task = snapshot_task(row)
    start = len(task.supplied_environment)
    if candidate_text[start:].startswith(TARGET_BEGIN):
        start += len(TARGET_BEGIN)
    return CandidateSnapshot(
        task=task,
        path=candidate_path.resolve(),
        text=candidate_text,
        declaration=declaration,
        proof_body=body,
        declaration_start=start,
    )


def exact_source_prefix(row: dict[str, Any], project_root: Path) -> SourcePrefix:
    """Cut at the target position, excluding the target and later declarations."""
    project_root = project_root.resolve()
    if is_project_resident(row):
        declaration = canonical_candidate_declaration(row)
        harness = project_compile_harness(
            row, declaration, project_root, exact=False
        )
        suffix = declaration.rstrip() + "\n"
        if not harness.endswith(suffix):
            raise SourceDocumentError(
                f"{row['name']}: evaluator harness did not end at the target declaration"
            )
        prefix = harness[: -len(suffix)]
        source_path = project_source_path(row, project_root)
        kind = "project-source-prefix"
    else:
        prefix = render_environment(row)
        source_path = None
        kind = "supplied-environment-prefix"
    if row["src"].rstrip("\r\n") in prefix:
        raise SourceDocumentError(f"{row['name']}: completed target leaked into oracle prefix")
    # Earlier declarations with the same short name remain legitimate context.
    return SourcePrefix(prefix, kind, source_path)


def _find_unique(text: str, needle: str, *, after: int, label: str) -> int:
    first = text.find(needle, after)
    if first < 0:
        raise SourceDocumentError(f"could not locate the {label}")
    if text.find(needle, first + 1) >= 0:
        raise SourceDocumentError(f"the {label} occurs more than once")
    return first


def prepare_document(
    task_path: Path, candidate_path: Path, project_root: Path
) -> SourceDocument:
    candidate_path = candidate_path.resolve()
    project_root = project_root.resolve()
    if not candidate_path.is_file():
        raise SourceDocumentError(f"candidate is missing: {candidate_path}")
    _document, row = load_task(task_path.resolve())
    candidate = snapshot_candidate(
        row, candidate_path.read_text(encoding="utf-8"), candidate_path
    )
    candidate_start = _find_unique(
        candidate.text,
        candidate.declaration,
        after=len(candidate.task.supplied_environment),
        label="candidate declaration",
    )
    source = quick_compile_harness(row, candidate.declaration, project_root)
    generated_start = _find_unique(
        source, candidate.declaration.rstrip(), after=0, label="managed declaration"
    )
    return SourceDocument(
        task_name=candidate.task.name,
        candidate_path=candidate.path,
        project_root=project_root,
        source=source,
        document_kind=(
            "project_source_prefix" if is_project_resident(row)
            else "supplied_environment"
        ),
        candidate_text=candidate.text,
        candidate_declaration_start=candidate_start,
        declaration=candidate.declaration,
        document_declaration_start=generated_start,
    )

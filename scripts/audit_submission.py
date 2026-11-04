#!/usr/bin/env python3
"""Audit this source tree against the pre-port release, without third-party packages.

This lexical audit does not parse or typecheck Lean. It supplements the fresh
build and Comparator/kernel checks. Normalization ignores comments/whitespace
and only the module-port commands documented in NORMALIZATION below; string
literal contents remain significant.
"""

import argparse
from collections import defaultdict
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from typing import NamedTuple


BASELINE = "03a35c170b1135d8546c8d63ccadc7939389eff1"
NORMALIZATION = [
    "Ignore nested block comments, line comments, and whitespace outside strings.",
    "Remove a standalone initial module command.",
    "Change public import commands to import commands.",
    "Remove one standalone @[expose] public section after the import header.",
    "Retain all other tokens, including the exact contents of string literals.",
]
TRUST_MARKERS = {
    "sorry", "admit", "axiom", "constant", "opaque", "unsafe", "partial",
    "native_decide", "implemented_by", "extern", "initialize",
    "builtin_initialize", "elab", "macro", "syntax", "run_tac",
    "sorryAx", "ofReduceBool", "eval_expr", "run_meta",
}
STUB = (
    "/-- The closed headline challenge; all project proofs must discharge this statement. -/\n"
    "theorem main : MainStatement := by\n  sorry\n\n"
)


class Token(NamedTuple):
    value: str
    line: int
    kind: str


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])


def lex(source):
    """Keep exact strings; skip Lean's nested comments and outside whitespace."""
    tokens = []
    i, line, size = 0, 1, len(source)
    while i < size:
        c = source[i]
        if c.isspace():
            line += c == "\n"
            i += 1
            continue
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = size if end == -1 else end
            continue
        if source.startswith("/-", i):
            i += 2
            depth = 1
            while i < size and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    line += source[i] == "\n"
                    i += 1
            if depth:
                raise ValueError("unterminated block comment")
            continue
        start, first_line = i, line
        # Lean raw strings use r"...", r#"..."#, etc.
        raw = re.match(r'r(#+)?"', source[i:]) if c == "r" else None
        if raw:
            hashes = raw.group(1) or ""
            i += len(raw.group(0))
            end = source.find('"' + hashes, i)
            if end == -1:
                raise ValueError("unterminated raw string")
            i = end + 1 + len(hashes)
            line += source[start:i].count("\n")
            tokens.append(Token(source[start:i], first_line, "string"))
            continue
        if c == '"':
            i += 1
            while i < size:
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError("unterminated string")
            line += source[start:i].count("\n")
            tokens.append(Token(source[start:i], first_line, "string"))
            continue
        if c == "«":
            end = source.find("»", i + 1)
            if end == -1:
                raise ValueError("unterminated quoted identifier")
            i = end + 1
            line += source[start:i].count("\n")
            tokens.append(Token(source[start:i], first_line, "identifier"))
            continue
        if c.isalnum() or c in "_'":
            i += 1
            while i < size and (source[i].isalnum() or source[i] in "_'"):
                i += 1
            tokens.append(Token(source[start:i], first_line, "identifier"))
            continue
        tokens.append(Token(c, first_line, "symbol"))
        i += 1
    return tokens


def command_lines(tokens):
    grouped = defaultdict(list)
    for token in tokens:
        grouped[token.line].append(token)
    return list(grouped.items())


def normalized(tokens):
    result, errors = [], []
    counts = {"module": 0, "public_import": 0, "expose_public_section": 0}
    header = True
    for index, (line, group) in enumerate(command_lines(tokens)):
        values = [t.value for t in group]
        if values == ["module"]:
            if index == 0:
                counts["module"] += 1
                continue
            errors.append({"line": line, "error": "module is not the initial command"})
        if values[:2] == ["public", "import"]:
            if not header:
                errors.append({"line": line, "error": "public import outside module header"})
            counts["public_import"] += 1
            result.extend(values[1:])
            continue
        if values[0] == "import":
            result.extend(values)
            continue
        if values == ["@", "[", "expose", "]", "public", "section"]:
            if header and counts["expose_public_section"] == 0:
                counts["expose_public_section"] += 1
                header = False
                continue
            errors.append({"line": line, "error": "expose/public section outside module header"})
        header = False
        result.extend(values)
    return result, counts, errors


def token_hash(values):
    return sha256(json.dumps(values, ensure_ascii=False, separators=(",", ":")).encode())


def imports(tokens):
    found = []
    for line, group in command_lines(tokens):
        values = [t.value for t in group]
        if values[:2] == ["public", "import"]:
            values = values[1:]
        if values[0] != "import":
            continue
        i = 1
        while i < len(values):
            name = values[i]
            i += 1
            while i + 1 < len(values) and values[i] == ".":
                name += "." + values[i + 1]
                i += 2
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*", name):
                raise ValueError(f"unrecognized import {name!r} at line {line}")
            found.append(name)
    return found


def lean_paths(root):
    files, symlinks = [], []
    for directory, dirs, names in os.walk(root, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in {".git", ".lake"})
        for name in sorted(names):
            if not name.endswith(".lean"):
                continue
            path = Path(directory) / name
            relative = path.relative_to(root).as_posix()
            (symlinks if path.is_symlink() else files).append(relative)
    return sorted(files), sorted(symlinks)


def audit(root, baseline):
    baseline = git(root, "rev-parse", "--verify", baseline + "^{commit}").decode().strip()
    old_paths = sorted(p for p in git(root, "ls-tree", "-r", "--name-only", baseline).decode().splitlines()
                       if p.endswith(".lean") and not {".git", ".lake"}.intersection(Path(p).parts))
    paths, symlinks = lean_paths(root)
    records, failures, token_sets, import_graph = {}, [], {}, {}
    all_markers, all_options, external = [], [], set()
    added, removed = sorted(set(paths) - set(old_paths)), sorted(set(old_paths) - set(paths))
    if added or removed:
        failures.append("Lean source inventory differs from the baseline")
    if symlinks:
        failures.append("Lean source symlinks are not permitted")
    for relative in paths:
        data = (root / relative).read_bytes()
        text = data.decode("utf-8")
        tokens = lex(text)
        values, port, port_errors = normalized(tokens)
        token_sets[relative] = values
        physical_lines = data.count(b"\n") + (bool(data) and not data.endswith(b"\n"))
        record = {
            "bytes": len(data), "physical_lines": physical_lines,
            "sha256": sha256(data), "comment_stripped_token_sha256": token_hash([t.value for t in tokens]),
            "normalized_token_sha256": token_hash(values), "module_port_syntax": port,
            "module_header": bool(tokens and tokens[0].value == "module" and
                                  command_lines(tokens)[0][1] == [tokens[0]]),
            "imports": imports(tokens), "normalization_errors": port_errors,
        }
        if relative in old_paths:
            old_data = git(root, "show", baseline + ":" + relative)
            old_values, _, old_errors = normalized(lex(old_data.decode("utf-8")))
            record.update(baseline_sha256=sha256(old_data),
                          baseline_normalized_token_sha256=token_hash(old_values),
                          mathematical_tokens_unchanged=(values == old_values and not old_errors))
        else:
            record["mathematical_tokens_unchanged"] = False
        issues = []
        if not record["module_header"] and Path(relative).name != "lakefile.lean":
            issues.append("missing initial module header")
        if physical_lines > 10000:
            issues.append("source exceeds 10000 lines")
        if relative == "Challenge.lean" and (physical_lines > 1000 or len(data) > 100 * 1024):
            issues.append("Challenge exceeds 1000 lines or 100 KiB")
        if not record["mathematical_tokens_unchanged"]:
            issues.append("tokens differ beyond allowed comments/module port")
        if port_errors:
            issues.append("unexpected module-port syntax placement")
        for token in tokens:
            if token.kind != "string" and token.value in TRUST_MARKERS:
                all_markers.append({"path": relative, "line": token.line, "token": token.value})
        for line, group in command_lines(tokens):
            if any(t.value == "set_option" for t in group):
                all_options.append({"path": relative, "line": line,
                                    "tokens": [t.value for t in group]})
        record["issues"] = issues
        failures.extend(relative + ": " + issue for issue in issues)
        records[relative] = record
        local = []
        for name in record["imports"]:
            dependency = name.replace(".", "/") + ".lean"
            if dependency in paths:
                local.append(dependency)
            else:
                external.add(name)
        import_graph[relative] = local
    cycles, state = [], {}

    def visit(path, stack):
        if state.get(path) == 1:
            cycles.append(stack[stack.index(path):] + [path])
            return
        if state.get(path) == 2:
            return
        state[path] = 1
        for dependency in import_graph[path]:
            visit(dependency, stack + [path])
        state[path] = 2

    for path in paths:
        visit(path, [])
    closure, pending = set(), ["Solution.lean"]
    while pending:
        path = pending.pop()
        if path in closure or path not in import_graph:
            continue
        closure.add(path)
        pending.extend(import_graph[path])
    if cycles:
        failures.append("project-local imports contain a cycle")
    if "Challenge.lean" in closure:
        failures.append("Solution imports the Challenge theorem stub")
    if "Solution.lean" not in closure:
        failures.append("Solution.lean is missing")
    unexpected = [m for m in all_markers if not (m["path"] == "Challenge.lean" and m["token"] == "sorry")]
    challenge_holes = [m for m in all_markers if m["path"] == "Challenge.lean" and m["token"] == "sorry"]
    if unexpected or len(challenge_holes) != 1:
        failures.append("unexpected trust/hole marker or missing expected Challenge stub")
    dangerous_options = [o for o in all_options if any(
        marker in "".join(o["tokens"]) for marker in ("skipKernel", "trustLevel", "debug.skip"))]
    if dangerous_options:
        failures.append("potential kernel/trust override option")
    challenge = (root / "Challenge.lean").read_text()
    companion = (root / "ThLean/Challenge/MainDefinitions.lean").read_text()
    exact_companion = challenge.count(STUB) == 1 and challenge.replace(STUB, "", 1) == companion
    if not exact_companion:
        failures.append("definitions companion differs from Challenge without final theorem/docstring")
    return {
        "schema_version": 1, "scope": "Static source audit; not a Lean build or kernel check",
        "baseline_commit": baseline, "normalization": NORMALIZATION,
        "lean_file_count": len(paths), "added_lean_files": added, "removed_lean_files": removed,
        "lean_symlinks": symlinks,
        "all_mathematical_tokens_unchanged": all(r["mathematical_tokens_unchanged"] for r in records.values()),
        "all_required_module_headers_present": all(r["module_header"] or Path(p).name == "lakefile.lean"
                                                   for p, r in records.items()),
        "maximum_source_lines": max((r["physical_lines"] for r in records.values()), default=0),
        "solution_local_import_closure_count": len(closure),
        "excluded_from_solution": sorted(set(paths) - closure),
        "project_local_import_cycles": cycles, "external_imports": sorted(external),
        "trust_markers": all_markers, "unexpected_trust_markers": unexpected,
        "solution_closure_trust_markers": [m for m in all_markers if m["path"] in closure],
        "set_options": all_options, "dangerous_set_options": dangerous_options,
        "companion_exactly_challenge_without_stub": exact_companion,
        "files": records, "failures": failures, "status": "PASS" if not failures else "FAIL",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--baseline", default=BASELINE)
    parser.add_argument("--report", type=Path, default=Path("verification/submission/source-audit.json"))
    args = parser.parse_args()
    root = args.root.resolve()
    report = args.report if args.report.is_absolute() else root / args.report
    result = audit(root, args.baseline)
    report.parent.mkdir(parents=True, exist_ok=True)
    report.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(f"{result['status']}: {result['lean_file_count']} Lean files; "
          f"{result['solution_local_import_closure_count']} in Solution closure; "
          f"{len(result['failures'])} issues")
    for failure in result["failures"]:
        print(failure)
    return int(bool(result["failures"]))


if __name__ == "__main__":
    raise SystemExit(main())

"""Mechanical operations for the agent's upstream import plan.

All declaration cuts and renames come from the two pinned Lean oracles. The
agent supplies selection, scope/import changes and prose; Lean checks the result.
"""
import hashlib
import json
from pathlib import Path


def read_jsonl(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def apply_edits(source, edits):
    data = source.encode() if isinstance(source, str) else source
    previous = len(data)
    for start, end, replacement in sorted(set(edits), reverse=True):
        if not 0 <= start <= end <= previous:
            raise ValueError("Overlapping or out-of-bounds source edits")
        data = data[:start] + replacement.encode() + data[end:]
        previous = start
    return data.decode()


def declaration_fact(row, facts):
    matches = [fact for fact in facts if fact["kind"] == "decl" and fact["declStart"]["line"] <= row["startLine"] <= fact["declEnd"]["line"]]
    if len(matches) != 1:
        raise ValueError("Declaration has no unique source command; retain its enclosing bundle")
    return matches[0]


def reachable(rows, roots):
    by_name = {row["name"]: row for row in rows}
    pending = list(roots) + [row["name"] for row in rows if row["isInstance"]]
    seen = set()
    while pending:
        name = pending.pop()
        if name in seen or name not in by_name:
            continue
        seen.add(name)
        row = by_name[name]
        pending.extend(row["typeDeps"] + row["valueDeps"])
        if row["kind"] == "inductive":
            pending.extend(item["name"] for item in rows if item["kind"] == "ctor" and name in item["typeDeps"])
    # Compiler companions are needed during traversal, but cannot be source nodes.
    return [by_name[name] for name in sorted(seen) if by_name[name]["startLine"] > 0]


def suggest_nodes(rows, facts_by_module, roots):
    live = reachable(rows, roots)
    result = []
    for row in live:
        if row["kind"] != "theorem":
            continue
        fact = declaration_fact(row, facts_by_module[row["module"]])
        if fact["valStart"] is None:
            continue
        size = fact["declEnd"]["line"] - fact["valStart"]["line"]
        users = [other for other in live if row["name"] in other["valueDeps"]]
        signal = len(users) >= 2 or any(other["module"] != row["module"] for other in users) or fact["docstring"] is not None
        if row["name"] in roots or (not row["isPrivate"] and (size > 40 or (size > 10 and signal))):
            result.append(row["name"])
    return result


def skeleton(source, facts, keep):
    """Subtract whole declaration commands; keep notations and all scope commands."""
    keep_spans = {(fact["declStart"]["offset"], fact["declEnd"]["offset"]) for fact in keep}
    return apply_edits(source, [(fact["declStart"]["offset"], fact["declEnd"]["offset"], "") for fact in facts
                                if fact["kind"] == "decl" and (fact["declStart"]["offset"], fact["declEnd"]["offset"]) not in keep_spans])


def declaration(source, row, facts, *, name=None, stub=False, renames=None):
    """Exact bytes, including Unicode and nested type-level := expressions."""
    fact = declaration_fact(row, facts)
    start, end = fact["declStart"]["offset"], fact["declEnd"]["offset"]
    edits = []
    if stub:
        if fact["valStart"] is None:
            raise ValueError("No elaborated proof boundary")
        edits.append((fact["valStart"]["offset"], end, ":= by sorry"))
    for field in ("docstring", "privateTok"):
        if fact.get(field):
            edits.append((fact[field]["start"]["offset"], fact[field]["end"]["offset"], ""))
    refs = [ref for ref in facts if ref["kind"] == "ref" and start <= ref["start"]["offset"] < end]
    if name is not None:
        binding = [ref for ref in refs if ref["const"].endswith(row["userName"]) and ref["end"]["offset"] <= fact["valStart"]["offset"]]
        if len(binding) != 1:
            raise ValueError("No unique elaborated declaration binding")
        edits.append((binding[0]["start"]["offset"], binding[0]["end"]["offset"], name))
    for ref in refs:
        if stub and ref["start"]["offset"] >= fact["valStart"]["offset"]:
            continue
        replacement = (renames or {}).get(ref["const"])
        if replacement and not any(a <= ref["start"]["offset"] < b for a, b, _ in edits):
            edits.append((ref["start"]["offset"], ref["end"]["offset"], replacement))
    return apply_edits(source.encode()[start:end], [(a - start, b - start, value) for a, b, value in edits]).strip()


def statement_name(hint, preamble, statement_without_name, dependency_keys, env):
    """Conservative identity: changed statement/context gets another immutable name."""
    data = json.dumps([env, preamble, statement_without_name, sorted(dependency_keys)], separators=(",", ":"))
    key = hashlib.sha256(data.encode()).hexdigest()
    safe = "".join(character if character.isascii() and character.isalnum() else "_" for character in hint)
    return f"BC_{safe[:80]}_{key[:20]}"

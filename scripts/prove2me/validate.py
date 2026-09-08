"""Check a prepared bundle in a credential-free job before a separate uploader sees it."""
import copy
import json
import re
import subprocess
import time
import uuid
from pathlib import Path
from publish import digest

NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
SHA = re.compile(r"^[a-f0-9]{40}$")
HASH = re.compile(r"^[a-f0-9]{64}$")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def source_fields(value):
    expected = {"benchmarkId", "submissionId", "repository", "commit", "path", "line", "sha256", "toolchain", "manifestSha256"}
    if set(value) != expected:
        raise ValueError("Source mappings must contain only explicit public fields")
    for key in ("benchmarkId", "submissionId"): uuid.UUID(value[key])
    if not re.fullmatch(r"https://github\.com/[A-Za-z0-9_-]+/[A-Za-z0-9_.-]+", value["repository"]):
        raise ValueError("Source must be a public GitHub repository")
    if any(part in {"", ".", "..", ".git"} for part in value["path"].split("/")) or not value["path"].endswith(".lean"):
        raise ValueError("Unsafe source path")
    if not SHA.fullmatch(value["commit"]) or not HASH.fullmatch(value["sha256"]) or not HASH.fullmatch(value["manifestSha256"]):
        raise ValueError("Sources must use immutable commits and hashes")
    if not isinstance(value["line"], int) or value["line"] < 1:
        raise ValueError("Invalid source line")


def validate_bundle(bundle):
    from batch import CONFIG
    if bundle.get("version") != 1 or bundle.get("workspaceRevision") != CONFIG["workspaceRevision"] or bundle.get("mathlibRev") != CONFIG["mathlibRev"]:
        raise ValueError("Bundle is not bound to the configured workspace and environment")
    collections = [{"benchmarkId": track["benchmarkId"], "tag": CONFIG["tag"], "mathlibRev": CONFIG["mathlibRev"]} for track in CONFIG["tracks"]]
    if bundle.get("collections") != collections:
        raise ValueError("Bundle cannot choose a different public collection")
    if not isinstance(bundle.get("items"), list) or len(bundle["items"]) > 2000:
        raise ValueError("Invalid batch size")
    available, names = set(), set()
    for item in bundle["items"]:
        if item["kind"] not in {"problem", "definition"} or not NAME.fullmatch(item["name"]) or item["name"] in names or item["key"] in available:
            raise ValueError("Invalid or duplicate immutable identity")
        if item["tags"] != [CONFIG["tag"]] or any(key not in available for key in item["requires"]):
            raise ValueError("Imports must be in dependency order in this checked batch")
        if type(item["isRoot"]) is not bool: raise ValueError("Invalid root marker")
        names.add(item["name"]); available.add(item["key"])
        for key in ("title", "description", "body"):
            if not isinstance(item[key], str) or not item[key].strip(): raise ValueError("Missing publication text")
        if len(item["title"]) > 200 or len(item["body"].encode()) > 8 * 1024 * 1024:
            raise ValueError("Publication text exceeds its limit")
        if item["kind"] == "problem" and item.get("generatedName", item["name"]) != item["name"]:
            raise ValueError("The theorem binding must match its provider identity")
        if item["kind"] == "problem" and (not item.get("solution") or not item.get("explanation")):
            raise ValueError("A theorem needs both exact native proof work and an explanation")
        if not item["sources"]: raise ValueError("Missing source attribution")
        for source in item["sources"]:
            source_fields(source)
            if source["benchmarkId"] not in {entry["benchmarkId"] for entry in collections}:
                raise ValueError("Source is outside Better.codes")
    for work in bundle["work"]:
        if not work["items"] or any(key not in available for key in work["items"]):
            raise ValueError("Only published useful work can be marked complete")
    return bundle


def compare_types(native, generated, *, allow_stubs=False, native_module=None):
    if native_module is not None and native.get("module") != native_module:
        raise ValueError("Native declaration belongs to a different module than its source reference")
    if native["levels"] != generated["levels"] or native["type"] != generated["type"] or native.get("body") != generated.get("body") or native.get("shape") != generated.get("shape"):
        raise ValueError("Generated statement changed the native theorem's exact type or context")
    serialized = json.dumps(native["type"]) + json.dumps(generated["type"])
    if "UNRESOLVED_" in serialized:
        raise ValueError("Type contains unresolved terms or universes")
    if not set(native["axioms"]) <= ALLOWED_AXIOMS:
        raise ValueError("Native result contains an admission or unexpected axiom")
    if not allow_stubs and not set(generated["axioms"]) <= ALLOWED_AXIOMS:
        raise ValueError("Generated proof contains an admission or unexpected axiom")


def source_binding(item, mapping, work):
    if mapping["submissionId"] != work["submissionId"] or mapping["benchmarkId"] != work["benchmarkId"]:
        raise ValueError("Source attribution differs from the selected submission")
    if mapping["path"] != item["nativeModule"].replace(".", "/") + ".lean":
        raise ValueError("Source reference does not contain the selected native declaration")
    if mapping["repository"] == work["repository"] and mapping["commit"] != work["commit"]:
        raise ValueError("Original source must remain at the selected submission commit")


def check(directory, deadline):
    from batch import CONFIG, HERE, run
    source = directory / "source"
    work = json.loads((directory / "work.json").read_text())
    inventory = json.loads((directory / "inventory.json").read_text())
    if not any(all(work.get(key) == value for key, value in item.items()) for item in inventory["work"]):
        raise ValueError("Prepared work differs from the original inventory")
    if run(["git", "rev-parse", "HEAD"], source) != work["nativeCommit"]:
        raise ValueError("Native source commit changed during preparation")
    run(["git", "diff", "--exit-code", "HEAD", "--"], source)
    expected_native = CONFIG["maintenanceSources"].get(work["commit"], work["commit"])
    if work["nativeCommit"] != expected_native:
        raise ValueError("Native source is not the original or its explicit maintenance port")
    if (source / "lean-toolchain").read_text().strip() != CONFIG["toolchain"]:
        raise ValueError("Unexpected Lean toolchain")
    manifest = json.loads((source / "lake-manifest.json").read_text())
    if not any(package["name"] == "mathlib" and package["rev"] == CONFIG["mathlibRev"] for package in manifest["packages"]):
        raise ValueError("Unexpected Mathlib pin")
    bundle = validate_bundle(json.loads((directory / "prepared.json").read_text()))
    validation_digest = digest([work["nativeCommit"], bundle, (HERE / "inspect.lean").read_text(), (HERE / "validate.py").read_text(), manifest])
    if bundle["work"] != [{"id": work["id"], "items": [item["key"] for item in bundle["items"]]}]:
        raise ValueError("Only this prepared source may be completed")
    if work.get("winner") and not any(item["nativeName"] == work["root"] and item["isRoot"] for item in bundle["items"]):
        raise ValueError("The winning claim must remain a root in its import")
    from generate import read_jsonl
    rows = read_jsonl(directory / "facts/decl_graph.jsonl")
    source_names = {row["name"]: row for row in rows}
    by_key = {item["key"]: item for item in bundle["items"]}
    renames = []
    for item in bundle["items"]:
        if item["nativeName"] not in source_names:
            raise ValueError("Publication is not in the extracted native graph")
        if item["nativeModule"] != source_names[item["nativeName"]]["module"]:
            raise ValueError("Publication points at a different native module")
        renames.append((item.get("generatedName", item["name"]), item["nativeName"]))
        if item["kind"] != "definition" and item.get("definitionRenames"):
            raise ValueError("Only checked definition bundles can rename statement context")
        for generated, original in item.get("definitionRenames", []):
            if original not in source_names or source_names[original]["module"] != item["nativeModule"]:
                raise ValueError("Definition rename is not in its native module")
            renames.append((generated, original))
    renames.sort(key=lambda pair: -len(pair[0]))
    output = source / ".lake/build/lib/lean"
    (source / "Inspect.lean").write_bytes((HERE / "inspect.lean").read_bytes())

    def remaining():
        seconds = int(deadline - time.time())
        if seconds < 1: raise TimeoutError("Batch deadline reached; leave work unprocessed")
        return seconds

    def compile_module(module, text):
        file = source / (module.replace(".", "/") + ".lean")
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(text)
        compiled = output / (module.replace(".", "/") + ".olean")
        compiled.parent.mkdir(parents=True, exist_ok=True)
        run(["lake", "env", "lean", "-o", str(compiled), str(file)], source, timeout=remaining())

    def inspect(module, names, mappings=(), stubs=()):
        config = directory / "inspect.json"
        config.write_text(json.dumps({"module": module, "names": names, "renames": mappings, "allowedStubs": stubs}))
        text = run(["lake", "env", "lean", "--run", "Inspect.lean", str(config)], source, timeout=remaining())
        values = [json.loads(line) for line in text.splitlines() if line.strip()]
        if [value["name"] for value in values] != list(names):
            raise ValueError("Inspection output differs from the requested declarations")
        return values

    for item in bundle["items"]:
        for mapping in item["sources"]:
            source_binding(item, mapping, work)
            roots = [source, *(source / ".lake/packages").iterdir()]
            found = False
            for root in roots:
                try:
                    # These reads cannot execute source code, and the shell never interprets paths.
                    expected_repo = CONFIG["repository"] if root == source else run(["git", "remote", "get-url", "origin"], root).removesuffix(".git")
                    if mapping["repository"] != expected_repo:
                        continue
                    if root != source and mapping["commit"] != run(["git", "rev-parse", "HEAD"], root):
                        continue
                    toolchain = run(["git", "show", f'{mapping["commit"]}:lean-toolchain'], root)
                    # run() strips terminal whitespace; fetch raw bytes for source-hash fidelity.
                    raw = lambda name: subprocess.check_output(["git", "show", f'{mapping["commit"]}:{name}'], cwd=root)
                    if digest(raw(mapping["path"]).decode()) == mapping["sha256"] and digest(raw("lake-manifest.json").decode()) == mapping["manifestSha256"] and toolchain == mapping["toolchain"]:
                        found = True; break
                except subprocess.CalledProcessError:
                    continue
            if not found: raise ValueError("Original source or dependency hashes do not match Git")
        pairs = [(item.get("generatedName", item["name"]), item["nativeName"]), *item.get("definitionRenames", [])]
        # All declarations in a bundle share an environment; import it once per
        # side instead of restarting Lean for every supporting definition/proof.
        native_records = inspect(item["nativeModule"], [original for _, original in pairs])
        native = native_records[0]
        module = ("Definitions.Def_" if item["kind"] == "definition" else "Theorems.Thm_") + item["name"]
        compile_module(module, item["body"] if item["kind"] == "definition" else item["preamble"] + "\n" + item["body"])
        imported_records = inspect(module, [generated for generated, _ in pairs], renames)
        if any(name.startswith(("ProximityPrize", "ArkLib", "CompPoly")) for name in imported_records[0]["modules"]):
            raise ValueError("Platform files must use published definitions instead of native-only libraries")
        for original, imported in zip(native_records, imported_records):
            compare_types(original, imported, allow_stubs=item["kind"] == "problem", native_module=item["nativeModule"])
        if item["kind"] == "problem":
            # Only other checked theorem stubs can discharge tracked dependencies.
            allowed = [by_key[key]["name"] for key in item["requires"] if by_key[key]["kind"] == "problem"]
            solution_module = "Solutions.Sol_" + item["name"]
            compile_module(solution_module, item["solution"])
            proof = inspect(solution_module, ["solution"], renames, allowed)[0]
            if module in proof["modules"] or any(name.startswith(("ProximityPrize", "ArkLib", "CompPoly")) for name in proof["modules"]):
                raise ValueError("Solution imports its own unproved target or an unavailable native module")
            compare_types(native, proof)
        item["checkedDigest"] = digest([item["body"], item.get("preamble", ""), item.get("solution", "")])
    # This file is the only artifact passed to the credentialed publisher job.
    bundle["validationDigest"] = validation_digest
    (directory / "checked.json").write_text(json.dumps(bundle, indent=2) + "\n")

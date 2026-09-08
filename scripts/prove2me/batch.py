#!/usr/bin/env python3
"""Daily read -> prepare -> check -> publish, with each stage independently runnable."""
import argparse
import concurrent.futures
import json
import os
import re
import subprocess
import sys
import time
import urllib.request
from pathlib import Path
from generate import discovery_roots, read_jsonl, submission_modules, suggest_nodes
from provider import Provider
from publish import Publisher, digest
from storage import Storage, empty_state

RUN_DEADLINE = float("inf")
HERE = Path(__file__).resolve().parent
CONFIG = json.loads((HERE / "config.json").read_text())
SHA = re.compile(r"^[a-f0-9]{40}$")
MODULE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")


def run(args, cwd, timeout=600, output=None):
    # This subprocess boundary is for credential-free preparation/check jobs only.
    if any(os.environ.get(key) for key in ("PROVE2ME_API_KEY", "AWS_ACCESS_KEY_ID", "AWS_SECRET_ACCESS_KEY", "R2_ACCESS_KEY_ID")):
        raise ValueError("Never compile or retrieve submitted source with publication/storage credentials")
    timeout = min(timeout, int(RUN_DEADLINE - time.time())) if RUN_DEADLINE != float("inf") else timeout
    if timeout < 1: raise TimeoutError("Batch deadline reached")
    result = subprocess.run(args, cwd=cwd, timeout=timeout, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
                            env={key: value for key, value in os.environ.items() if key in {"PATH", "HOME", "ELAN_HOME", "LEAN_PATH", "TMPDIR"}})
    if output:
        Path(output).write_bytes(result.stdout)
    return result.stdout.decode().strip()


def inventory(state, fetch=None, limit=1):
    if fetch is None:
        def fetch(url):
            with urllib.request.urlopen(url, timeout=30) as response:
                return json.load(response)
    work = []
    for track in CONFIG["tracks"]:
        rows = fetch(f'{CONFIG["api"]}/api/benchmarks/{track["benchmarkId"]}/submissions')["submissions"]
        eligible = [row for row in rows if SHA.fullmatch(row.get("submissionCommitSha") or "") and row["status"] not in {"received", "validating", "cancelled"}]
        promoted = [row for row in eligible if row.get("promotionStatus") == "promoted" and isinstance(row.get("officialScore"), (int, float))]
        winner = (max if track["direction"] == "+" else min)(promoted, key=lambda row: row["officialScore"], default=None)
        for row in eligible:
            identity = digest([CONFIG["version"], track["benchmarkId"], row["submissionCommitSha"]])
            if identity in state["completed"] or identity in state["deferred"]:
                continue
            work.append({"id": identity, "submissionId": row["id"], "commit": row["submissionCommitSha"],
                         "repository": CONFIG["repository"], "benchmarkId": track["benchmarkId"],
                         "track": track["track"], "directory": track["directory"], "module": track["module"], "root": track["root"],
                         "winner": winner is not None and row["id"] == winner["id"], "createdAt": row["createdAt"]})
    # Resume queued provider work first. A source that cannot prepare must not
    # monopolize every later batch; try fresh work before retrying it.
    pending = set()
    for receipt in state.get("items", {}).values():
        if receipt["phase"] not in {"FAILED", "ERROR"} and (receipt["phase"] != "published" or
                (receipt["kind"] == "problem" and (not receipt["proofs"] or
                 any(proof["phase"] in {"posting", "PENDING"} for proof in receipt["proofs"].values())))):
            pending.update(source["submissionId"] for source in receipt["sources"])
    def priority(item):
        return (item["submissionId"] not in pending, state.get("attempted", {}).get(item["id"], 0),
                not item["winner"], item["createdAt"], item["submissionId"])
    # Both unattempted current winners lead the historical backlog.
    work.sort(key=priority)
    unique = {item["id"]: item for item in reversed(work)}
    return sorted(unique.values(), key=priority)[:limit]


def checkout(work, directory, repository=None):
    source = directory / "source"
    source.mkdir(parents=True, exist_ok=False)
    run(["git", "init", "-q", "--template="], source)
    remote = repository or work["repository"]
    run(["git", "remote", "add", "origin", remote], source)
    run(["git", "-c", "credential.helper=", "fetch", "--no-tags", "origin", work["commit"]], source)
    native = CONFIG["maintenanceSources"].get(work["commit"], work["commit"])
    if native != work["commit"]:
        run(["git", "-c", "credential.helper=", "fetch", "--no-tags", "origin", native], source)
    run(["git", "-c", "core.hooksPath=/dev/null", "checkout", "--detach", native], source)
    work = {**work, "nativeCommit": run(["git", "rev-parse", "HEAD"], source)}
    if (source / "lean-toolchain").read_text().strip() != CONFIG["toolchain"]:
        raise ValueError("Historical source needs an explicit compatible maintenance port; leave this work pending")
    (directory / "work.json").write_text(json.dumps(work, indent=2) + "\n")
    return source


def extract(source, upstream, directory, work, workers=1):
    if run(["git", "rev-parse", "HEAD"], upstream) != CONFIG["workspaceRevision"]:
        raise ValueError("Prove2Me workspace is not at the pinned revision")
    if not MODULE.fullmatch(work["module"]):
        raise ValueError("Invalid root module")
    facts = directory / "facts"
    facts.mkdir(exist_ok=True)
    paths = run(["git", "ls-tree", "-r", "--name-only", work["nativeCommit"], "--", work["directory"]], source).splitlines()
    modules = submission_modules(paths, work["directory"])
    built, failed = [], []
    # A failed final attempt must not hide independently compiling helper modules.
    # Helpers go first; Lake reuses their outputs when compiling the final claim.
    for module in sorted(modules, key=lambda name: (name == work["module"], name)):
        try:
            run(["lake", "build", module], source, timeout=10500)
            built.append(module)
        except subprocess.CalledProcessError:
            failed.append(module)
    (facts / "builds.json").write_text(json.dumps({"built": built, "failed": failed}, indent=2) + "\n")
    if not built:
        raise ValueError("No submission module compiled; retain this source for repair")
    if work.get("winner") and work["module"] not in built:
        raise ValueError("The winning claim did not compile; do not replace it with a partial import")
    script = (upstream / "scripts/extract_decl_graph.lean").read_text()
    script = script.replace("import SumSquares\n", "".join(f"import {module}\n" for module in built))
    script = script.replace("let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m", "let isProj : Name → Bool := fun m => projPrefix.isPrefixOf m || (`ArkLib).isPrefixOf m || (`CompPoly).isPrefixOf m")
    script = script.replace("let projPrefix := `SumSquares", "let projPrefix := `ProximityPrize")
    (source / "ExtractGraph.lean").write_text(script)
    run(["lake", "env", "lean", "ExtractGraph.lean"], source, timeout=1800)
    (facts / "decl_graph.jsonl").write_bytes((source / "decl_graph.jsonl").read_bytes())
    rows = read_jsonl(facts / "decl_graph.jsonl")
    from generate import reachable
    candidates = discovery_roots(rows, set(built))
    roots = [work["root"]] if any(row["name"] == work["root"] for row in rows) else []
    live = reachable(rows, [*roots, *candidates])
    modules = sorted({row["module"] for row in live})
    search = [source, *(source / ".lake/packages").iterdir()]
    oracle = upstream / "scripts/extract_sketch_info.lean"
    bindings = {}
    def one(module):
        relative = Path(*module.split(".")).with_suffix(".lean")
        candidates = [root / relative for root in search if (root / relative).is_file()]
        if len(candidates) != 1:
            raise ValueError("No unique native source for " + module)
        file = candidates[0]
        binding = {"file": str(file.relative_to(source)), "sha256": digest(file.read_bytes().decode()), "workspaceRevision": CONFIG["workspaceRevision"], "nativeCommit": work["nativeCommit"]}
        result = facts / f"{module}.jsonl"
        receipt = facts / f"{module}.binding.json"
        if not result.exists() or not receipt.exists() or json.loads(receipt.read_text()) != binding:
            run(["lake", "env", "lean", "--run", str(oracle), str(file)], source, timeout=3600, output=result)
            receipt.write_text(json.dumps(binding, sort_keys=True) + "\n")
        return module, binding
    # Optional bounded overlap; default is one because measured Lean contention can cost more.
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        for module, binding in pool.map(one, modules):
            bindings[module] = binding
    (facts / "sources.json").write_text(json.dumps(bindings, indent=2) + "\n")
    suggested = suggest_nodes(rows, {module: read_jsonl(facts / f"{module}.jsonl") for module in modules}, roots, candidates)
    (facts / "suggested.json").write_text(json.dumps({"roots": roots, "candidates": candidates, "nodes": suggested, "failedModules": failed}, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=["inventory", "prepare", "extract", "check", "publish"])
    parser.add_argument("--directory", type=Path, required=True)
    parser.add_argument("--state", default=".yukon/prove2me")
    parser.add_argument("--upstream", type=Path)
    parser.add_argument("--repository", help="Local repository override for local maintenance commits")
    parser.add_argument("--workers", type=int, choices=[1, 2], default=1)
    parser.add_argument("--publish", action="store_true", help="Explicitly permit provider writes (default: check only)")
    parser.add_argument("--deadline", type=float, default=time.time() + 4 * 3600)
    args = parser.parse_args()
    global RUN_DEADLINE
    RUN_DEADLINE = args.deadline
    directory = args.directory.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    if args.stage == "inventory":
        storage = Storage(args.state)
        state = storage.read("state.json", empty_state())
        # Starting a new checkpoint is explicit; do not manufacture success from absent state later.
        work = inventory(state)
        for item in work:
            state.setdefault("attempted", {})[item["id"]] = time.time()
        storage.write("state.json", state)
        (directory / "inventory.json").write_text(json.dumps({"version": 1, "deadline": args.deadline, "work": work}, indent=2) + "\n")
        (directory / "state.json").write_text(json.dumps(state, indent=2) + "\n")
    elif args.stage == "prepare":
        pending = json.loads((directory / "inventory.json").read_text())["work"]
        if pending:
            checkout(pending[0], directory, args.repository)
    elif args.stage == "extract":
        if (directory / "work.json").exists():
            if args.upstream is None: parser.error("--upstream is required")
            extract(directory / "source", args.upstream.resolve(), directory, json.loads((directory / "work.json").read_text()), args.workers)
    elif args.stage == "check":
        from validate import check
        check(directory, args.deadline)
    else:
        from validate import validate_bundle
        bundle = validate_bundle(json.loads((directory / "checked.json").read_text()))
        if any(item.get("checkedDigest") != digest([item["body"], item.get("preamble", ""), item.get("solution", "")]) for item in bundle["items"]):
            raise ValueError("Checked publication bytes changed")
        if not args.publish:
            print(f'Checked batch contains {len(bundle["items"])} items; publication is disabled.')
            return
        storage = Storage(args.state)
        publisher = Publisher(Provider(os.environ["PROVE2ME_API_KEY"]), storage, args.deadline)
        while time.time() < args.deadline:
            ready = publisher.run(bundle)
            if len(ready) == len(bundle["items"]): break
            time.sleep(min(10, max(0, args.deadline - time.time())))


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        # Logs remain in the credential-free check job; no provider secrets are present.
        print(error.stderr.decode(errors="replace")[-4000:], file=sys.stderr)
        raise SystemExit(1)

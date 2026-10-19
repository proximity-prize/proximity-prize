#!/usr/bin/env python3
"""Check that no challenge can reach another.

`check-submission-imports.sh` audits the import *lines* a submission writes.
That is a textual boundary on the submission only: it says a lower submission
may import `ProximityPrize.Benchmark.TargetLower` and nothing else, but says
nothing about what importing that module transitively brings into scope. A
submission needs no import of its own to name something its target module
already pulled in.

So this checks the other half, on the challenge side: that no track's import
closure reaches another track's target module or the other profile, that
cross-profile sharing stays on a small allowlist, and that `export` is absent
from the challenge modules -- which is what keeps import lines the only path a
name can travel, and so what makes reading them sufficient.

Pure Python over import lines, so it runs in the pull-request job alongside the
other cheap guards, with no Lean build.

    python3 scripts/check-track-isolation.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from benchmark_profiles import PROFILES

ROOT = Path(__file__).resolve().parents[1]

# Modules a track may share with a track of the *other* profile. All are
# deliberately profile-free: the two `TargetCore*` modules hold one certificate
# shape each over abstract index/field/alphabet types, `CodeBridge` one generic
# distance lemma. The shapes are split so a lower track never sees the upper
# shape, and vice versa -- co-locating them widened each track's visible
# surface past what the duplicated contracts exposed.
# Anything else appearing here would mean the two profiles had grown a common
# dependency that can see one of them, so the list is checked, not derived.
SHARED_ACROSS_PROFILES = {
    "ProximityPrize.Benchmark.TargetCoreLower",
    "ProximityPrize.Benchmark.TargetCoreUpper",
    "ProximityPrize.Benchmark.CodeBridge",
}


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def repo_closure(module: str, seen: set[str] | None = None) -> set[str]:
    """Every in-repo module reachable from `module` by import lines."""
    seen = set() if seen is None else seen
    if module in seen:
        return seen
    seen.add(module)
    path = module_path(module)
    if not path.exists():
        return seen
    for line in path.read_text().splitlines():
        match = re.match(r"^import\s+(\S+)", line)
        if match and match.group(1).startswith("ProximityPrize"):
            repo_closure(match.group(1), seen)
    return seen


def check_static() -> list[str]:
    """No track imports another; cross-profile sharing stays on the allowlist."""
    failures = []
    closures = {s: repo_closure(p.target) for s, p in PROFILES.items()}
    for selector, closure in closures.items():
        for other, profile in PROFILES.items():
            if other == selector:
                continue
            if profile.target in closure:
                failures.append(
                    f"{selector}: imports {other}'s target module "
                    f"{profile.target}; challenges must not import each other"
                )
        # A track must not reach the other profile at all.
        foreign = (
            "ProximityPrize.Benchmark.IRSProfile"
            if PROFILES[selector].binary
            else "ProximityPrize.Benchmark.BinaryIRSProfile"
        )
        if foreign in closure:
            failures.append(f"{selector}: imports the other profile {foreign}")

    for selector, closure in closures.items():
        for other, other_closure in closures.items():
            if PROFILES[selector].binary == PROFILES[other].binary:
                continue
            for shared in closure & other_closure:
                if shared not in SHARED_ACROSS_PROFILES:
                    failures.append(
                        f"{shared} is shared by {selector} and {other}, which "
                        f"are different profiles, and is not on the "
                        f"cross-profile allowlist"
                    )
    return failures

def check_no_reexport() -> list[str]:
    """Import lines must stay the only way a name reaches a track.

    `check_static` reads import lines, which is sound only while that is the
    whole story. `export` re-publishes a name under the importing namespace, so
    a module could hand a track something its own imports never mention and the
    import graph would still look clean.

    An earlier revision probed this the other way round, asking Lean whether
    each of a list of forbidden names resolved from each target module. That
    cost 314s, found nothing the import graph did not already show, and had a
    failure mode of its own: a renamed entry in the list looked unreachable from
    everywhere and passed while checking nothing. Forbidding the mechanism is
    cheaper and does not decay.
    """
    failures = []
    for path in sorted((ROOT / "ProximityPrize" / "Benchmark").glob("*.lean")):
        for number, line in enumerate(path.read_text().splitlines(), 1):
            if re.match(r"^\s*export\s", line):
                failures.append(
                    f"{path.relative_to(ROOT)}:{number}: `export` re-publishes a "
                    f"name under the importing namespace, so import lines would "
                    f"no longer be the only path into a track"
                )
    return failures


def main() -> int:
    failures = check_static() + check_no_reexport()
    if failures:
        for failure in failures:
            print(f"::error::{failure}", file=sys.stderr)
        print(f"track isolation broken ({len(failures)})", file=sys.stderr)
        return 1
    print(f"ok -- no challenge imports another ({len(PROFILES)} tracks)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

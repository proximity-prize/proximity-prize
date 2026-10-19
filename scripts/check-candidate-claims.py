#!/usr/bin/env python3
"""Check each track's committed claim files against what its proof actually proves.

A local pre-flight check, not a security boundary. The submission pipeline
already binds the two: `benchmark.sh` calls `render-benchmark-challenge.py`,
which writes the trusted statement `theorem candidate : ProtocolClaim <score>
<numerator> <denominator>` from `score.txt` and the claim file, and Comparator
checks the submission against exactly that. A score disagreeing with its proof
fails there, authoritatively.

What this adds is catching the same inconsistency in the repository before a
benchmark run -- `validate.sh` builds the submissions as committed and never
renders a challenge, so without it a mismatched `score.txt` sits green locally
until the benchmark surfaces it.

    lake env lean scripts/emit-candidate-claims.lean | python3 scripts/check-candidate-claims.py
"""

from __future__ import annotations

import sys

from benchmark_contract import parse_radius, read_scalar
from benchmark_profiles import PROFILES, get_profile


def expected(selector: str) -> list[str]:
    """The numerals the committed claim files say the proof should carry."""
    p = get_profile(selector)
    root = p.submission
    score = read_scalar(f"{root}/score.txt")
    if p.side == "lower":
        numerator, denominator = parse_radius(read_scalar(f"{root}/radius.txt"))
        return [score, str(numerator), str(denominator)]
    return [score, read_scalar(f"{root}/unsafe-index.txt")]


def main() -> int:
    proved: dict[str, list[str]] = {}
    for line in sys.stdin.read().splitlines():
        if not line.strip():
            continue
        label, *nums = line.split()
        proved[label] = nums

    if set(proved) != set(PROFILES):
        print(
            f"emitted claims cover {sorted(proved)}, expected {sorted(PROFILES)}",
            file=sys.stderr,
        )
        return 1

    failures = []
    for selector in sorted(PROFILES):
        want = expected(selector)
        got = proved[selector]
        if want != got:
            failures.append(
                f"{selector}: committed claim files say {want} but the proof proves {got}"
            )

    if failures:
        for failure in failures:
            print(f"::error::{failure}", file=sys.stderr)
        print(f"claim files disagree with the proofs ({len(failures)})", file=sys.stderr)
        return 1

    print(f"ok -- every proof matches its committed claim files ({len(PROFILES)} tracks)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

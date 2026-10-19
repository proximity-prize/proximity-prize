#!/usr/bin/env python3
"""Check the published profile metadata against the geometry Lean actually has.

`benchmark_profiles.py` hardcodes the code geometry that every score artifact
advertises -- field, total dimension, interleaving, scalar-row dimension, domain
size, repetitions. Nothing previously tied those numbers to the Lean profiles
they claim to describe, so a profile edit on either side could leave the released
metadata describing a geometry the formalisation does not have.

Reads `scripts/emit-profile-geometry.lean` output on stdin:

    lake env lean --run scripts/emit-profile-geometry.lean | python3 scripts/check-profile-geometry.py
"""

from __future__ import annotations

import json
import sys

from benchmark_profiles import get_profile

# The upper track of each pair shares its lower track's profile geometry, so
# Lean emits one entry per pair and both selectors are checked against it.
PAIRS = {"lower": ["lower", "upper"], "binary-lower": ["binary-lower", "binary-upper"]}

# `field` and `domainKind` are emitted as hardcoded strings, so for those two
# this compares Lean's copy against benchmark_profiles.py's -- it catches one
# side being edited alone, but says nothing about the type a profile is over.
# `ContractShape.Geometry.koala_field`/`binary_field` pin that in Lean instead.
# The six numerals below are read from the profile definitions themselves.
CHECKED = [
    "field",
    "totalDimension",
    "interleaving",
    "baseDimension",
    "domainSize",
    "repetitions",
    "domainKind",
]


def main() -> int:
    try:
        emitted = json.loads(sys.stdin.read())
    except json.JSONDecodeError as error:
        print(f"could not parse emitted geometry: {error}", file=sys.stderr)
        return 1

    if set(emitted) != set(PAIRS):
        print(
            f"emitted geometry covers {sorted(emitted)}, expected {sorted(PAIRS)}",
            file=sys.stderr,
        )
        return 1

    failures = []
    for emitted_selector, selectors in PAIRS.items():
        lean = emitted[emitted_selector]
        for selector in selectors:
            published = get_profile(selector).metadata()
            for key in CHECKED:
                if key not in lean:
                    failures.append(f"{selector}: Lean emitted no {key}")
                elif key not in published:
                    failures.append(f"{selector}: benchmark_profiles.py publishes no {key}")
                elif published[key] != lean[key]:
                    failures.append(
                        f"{selector}: {key} is {published[key]!r} in "
                        f"benchmark_profiles.py but {lean[key]!r} in Lean"
                    )

    if failures:
        for failure in failures:
            print(f"::error::{failure}", file=sys.stderr)
        print(
            f"published profile metadata disagrees with Lean ({len(failures)})",
            file=sys.stderr,
        )
        return 1

    checked = sum(len(s) for s in PAIRS.values())
    print(f"ok -- published geometry matches Lean for all {checked} tracks")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

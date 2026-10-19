#!/usr/bin/env python3
"""Guard the one invariant that generalizes across challenges: a served version
lives only in challenges.json.

A verifier-side change is a new immutable version name. No file but
challenges.json may name a version of a served series (a `<series>-v0`
negative-test fixture and comment mentions aside); everything else reads it back
through challenges.py, so a bump is a one-line edit and a partial one is loud.

Deliberately nothing challenge-specific -- no seed, score, radius or hardening
shape. Those differ per challenge and belong to each challenge's own checks.
Multi-challenge by construction: a new challenge is a new challenges.json entry.
"""

from __future__ import annotations

import json
import re
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import challenges  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
SCAN_SUFFIXES = {".yml", ".yaml", ".py", ".sh"}

# Dependency pins are authoritative in lakefile.toml and lake-manifest.json.
# docs/binary-profile.md restates them as provenance narrative, which is worth
# keeping but will drift silently on the next bump, so it is checked rather than
# trusted. CompPoly has no require block of its own and appears only in the
# manifest. Keyed by the exact prose prefix each doc line uses.
PIN_PROSE = {
    "Arklib": "- ArkLib main: `",
    "CompPoly": "- CompPoly: `",
}
PIN_DOC = ROOT / "docs" / "binary-profile.md"


def manifest_pins() -> dict[str, str]:
    packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    return {
        p["name"]: p["rev"]
        for p in packages
        if isinstance(p, dict) and p.get("name") in PIN_PROSE
    }


def check_pins() -> bool:
    """True on failure. Any pin restated in prose must match the manifest."""
    pins = manifest_pins()
    missing = set(PIN_PROSE) - set(pins)
    if missing:
        print(f"lake-manifest.json has no {sorted(missing)} package", file=sys.stderr)
        return True
    fail = False
    for n, line in enumerate(PIN_DOC.read_text().splitlines(), 1):
        for name, prefix in PIN_PROSE.items():
            if not line.startswith(prefix):
                continue
            stated = line[len(prefix):].split("`", 1)[0]
            if stated != pins[name]:
                print(
                    f"stale {name} pin in prose (lake-manifest.json is authoritative): "
                    f"{PIN_DOC.relative_to(ROOT)}:{n}: states {stated}, "
                    f"manifest has {pins[name]}",
                    file=sys.stderr,
                )
                fail = True
    return fail


def check_sole_require() -> bool:
    """True on failure. The record is only sufficient while ArkLib is alone.

    A score artifact names ArkLib, CompPoly (with its URL) and the toolchain,
    and that is the whole trusted base only because ArkLib's revision fixes
    every other package transitively through committed manifests. One direct
    require is what makes that true. A second one -- a forked VCVio, say --
    would leave `arklibRev` no longer determining VCVio, with no field
    recording it and nothing anywhere noticing.

    CompPoly is the standing exception, which is why its URL is recorded
    rather than derived: production's manifest names a zksecurity fork that
    ArkLib's lakefile never declares. Comparing the manifest against ArkLib's
    lakefile would catch that, but it cannot run here -- the pull-request job
    is a bare checkout with no `.lake` -- and the recorded URL makes the
    artifact faithful either way. This checks only what a checkout can see.
    """
    lakefile = tomllib.loads((ROOT / "lakefile.toml").read_text())
    requires = [r.get("name") for r in lakefile.get("require", [])]
    if requires != ["Arklib"]:
        print(
            f"lakefile.toml must require exactly Arklib and nothing else; "
            f"found {requires or 'no requires'}. Every score artifact's "
            f"provenance assumes ArkLib's revision fixes the rest of the "
            f"manifest; a second direct dependency breaks that and needs "
            f"recording in the score writers.",
            file=sys.stderr,
        )
        return True
    return False


def main() -> int:
    try:
        entries = challenges.load()
    except challenges.ConfigError as exc:
        print(f"invalid challenges.json: {exc}", file=sys.stderr)
        return 1

    print(f"== challenges: {len(entries)} ==")
    for c in entries:
        print(f"  {c['slug']}  {c['version']}  (series: {challenges.series(c['version'])})")

    series = sorted({challenges.series(c["version"]) for c in entries})
    literal = re.compile("(?:" + "|".join(re.escape(s) for s in series) + r")-v[0-9]+")
    source = (ROOT / "challenges.json").resolve()

    fail = False
    for path in ROOT.rglob("*"):
        if (
            not path.is_file()
            or path.suffix not in SCAN_SUFFIXES
            or ".git" in path.parts
            or path.resolve() == source
        ):
            continue
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except (OSError, UnicodeError):
            continue
        for n, line in enumerate(lines, 1):
            for m in literal.finditer(line):
                if "#" in line[: m.start()] or m.group().endswith("-v0"):
                    continue  # a comment mention, or the -v0 negative fixture
                print(
                    f"stray version literal (read challenges.json instead): "
                    f"{path.relative_to(ROOT)}:{n}: {m.group()}",
                    file=sys.stderr,
                )
                fail = True

    if check_pins():
        fail = True

    if check_sole_require():
        fail = True

    if fail:
        return 1
    print("ok -- every served version is single-sourced in challenges.json")
    print("ok -- dependency pins restated in prose match lake-manifest.json")
    print("ok -- ArkLib is the sole direct require, so its revision fixes the rest")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

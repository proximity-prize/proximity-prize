#!/usr/bin/env python3
"""The challenges this repository serves, and the one place they are parsed.

`challenges.json` is the single source of truth: each challenge's version (the
immutable name a release bump changes) and its submission root live here and
nowhere else. Versions are independent per slug; two slugs may share a version
number, but neither must follow the other's numbering. Allocate a new number
against the independent verifier's served history, which may be ahead of this
repository. The benchmark workflow and version guard read the selected versions
back through this module: one schema, one parser.

CLI (for the shell/YAML callers):

    challenges.py version SLUG   -> the challenge's version string
    challenges.py root SLUG      -> its submission root
    challenges.py slugs          -> one slug per line
    challenges.py validate       -> exit 0 iff the config is well-formed
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

CONFIG = Path(__file__).resolve().parents[1] / "challenges.json"

# A version is `<series>-v<N>`: the series (irs-provable, koala-frs12, ...) is
# derived from it, so nothing here is tied to a particular challenge.
VERSION_RE = re.compile(r"^[a-z0-9][a-z0-9-]*-v[0-9]+$")
_FIELDS = ("slug", "version", "submission_root")


class ConfigError(ValueError):
    """challenges.json is missing or malformed."""


def load() -> list[dict]:
    """Return the validated list of challenge entries, or raise ConfigError."""
    try:
        data = json.loads(CONFIG.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ConfigError(f"cannot read {CONFIG.name}: {exc}") from exc
    challenges = data.get("challenges") if isinstance(data, dict) else None
    if not isinstance(challenges, list) or not challenges:
        raise ConfigError("challenges.json must hold a non-empty 'challenges' array")
    seen: set[str] = set()
    for entry in challenges:
        if not isinstance(entry, dict):
            raise ConfigError(f"challenge entry is not an object: {entry!r}")
        for field in _FIELDS:
            if not isinstance(entry.get(field), str) or not entry[field]:
                raise ConfigError(f"challenge entry missing '{field}': {entry!r}")
        if VERSION_RE.match(entry["version"]) is None:
            raise ConfigError(
                f"{entry['slug']}: version '{entry['version']}' is not <series>-vN"
            )
        if entry["slug"] in seen:
            raise ConfigError(f"duplicate challenge slug: {entry['slug']}")
        seen.add(entry["slug"])
    return challenges


def series(version: str) -> str:
    """The series a version belongs to: "foo-bar-v4" -> "foo-bar"."""
    return version.rsplit("-v", 1)[0]


def get(slug: str) -> dict:
    for entry in load():
        if entry["slug"] == slug:
            return entry
    raise ConfigError(f"no challenge with slug {slug!r}")


def main(argv: list[str]) -> int:
    try:
        if len(argv) == 1 and argv[0] == "slugs":
            print("\n".join(c["slug"] for c in load()))
        elif len(argv) == 1 and argv[0] == "validate":
            load()
        elif len(argv) == 2 and argv[0] == "version":
            print(get(argv[1])["version"])
        elif len(argv) == 2 and argv[0] == "root":
            print(get(argv[1])["submission_root"])
        else:
            print(__doc__, file=sys.stderr)
            return 2
    except ConfigError as exc:
        print(f"challenges: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

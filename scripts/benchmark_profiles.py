#!/usr/bin/env python3
"""Fixed routing and code geometry for each Toy IOP benchmark track."""

from dataclasses import dataclass
import sys

REPETITIONS = 128


def render_size(value: int) -> str:
    """Render exact powers of two as `2^e`, matching the Lean profile numerals."""
    exponent = value.bit_length() - 1
    return f"2^{exponent}" if 1 << exponent == value else str(value)


@dataclass(frozen=True)
class Profile:
    selector: str
    side: str
    binary: bool = False

    @property
    def track(self) -> str:
        return ("binary-" if self.binary else "") + "irs-reduction-threshold-" + self.side

    @property
    def challenge(self) -> str:
        return "proximity-prize-" + ("binary-" if self.binary else "") + "reduction-" + self.side

    @property
    def submission(self) -> str:
        return (
            "ProximityPrize/Submission"
            + ("Binary" if self.binary else "")
            + self.side.title()
        )

    @property
    def target(self) -> str:
        return (
            "ProximityPrize.Benchmark."
            + ("Binary" if self.binary else "")
            + "Target"
            + self.side.title()
        )

    @property
    def namespace(self) -> str:
        return (
            "ProximityPrize.Benchmark"
            + (".Binary" if self.binary else "")
            + (".Upper" if self.side == "upper" else "")
        )

    @property
    def claim_file(self) -> str:
        return "radius.txt" if self.side == "lower" else "unsafe-index.txt"

    @property
    def challenge_module(self) -> str:
        return (
            "ProximityPrize.Benchmark."
            + ("Binary" if self.binary else "")
            + "Challenge"
            + ("Upper" if self.side == "upper" else "")
        )

    @property
    def comparator(self) -> str:
        return (
            "benchmark/comparator"
            + ("-binary" if self.binary else "")
            + ("-upper" if self.side == "upper" else "")
            + ".json"
        )

    @property
    def domain_size(self) -> int:
        return 2 ** (21 if self.binary else 18)

    @property
    def total_dimension(self) -> int:
        return 2 ** (26 if self.binary else 20)

    @property
    def interleaving(self) -> int:
        return 64 if self.binary else 8

    @property
    def base_dimension(self) -> int:
        """Scalar-row dimension, derived exactly as Lean's
        `totalDimension_div_interleaving` does rather than assuming rate 1/2."""
        return self.total_dimension // self.interleaving

    @property
    def field_name(self) -> str:
        return "BF64.Ext3" if self.binary else "KoalaBear^6"

    @property
    def max_unsafe_index(self) -> int:
        return self.domain_size // 2

    def metadata(self) -> dict[str, str | int]:
        return {
            "field": self.field_name,
            "code": "interleaved-Reed-Solomon",
            "totalDimension": self.total_dimension,
            "interleaving": self.interleaving,
            "domainSize": self.domain_size,
            "baseDimension": self.base_dimension,
            "repetitions": REPETITIONS,
            "domainKind": "additive-polynomial-basis" if self.binary else "multiplicative-NTT",
        }

    @property
    def summary_line(self) -> str:
        """Human-readable geometry for the released summary markdown."""
        return (
            f"`k={render_size(self.total_dimension)}`, `s={self.interleaving}`, "
            f"`n={render_size(self.domain_size)}`, `t={REPETITIONS}` "
            f"over `{self.field_name}`"
        )


PROFILES = {
    p.selector: p
    for p in [
        Profile("lower", "lower"),
        Profile("upper", "upper"),
        Profile("binary-lower", "lower", True),
        Profile("binary-upper", "upper", True),
    ]
}


def get_profile(selector: str) -> Profile:
    try:
        return PROFILES[selector]
    except KeyError:
        raise ValueError(f"unknown benchmark profile: {selector}") from None


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] not in {"shell", "imports", "challenge"}:
        raise SystemExit("usage: benchmark_profiles.py shell|imports|challenge PROFILE")
    try:
        p = get_profile(sys.argv[2])
    except ValueError as error:
        raise SystemExit(str(error)) from error
    if sys.argv[1] == "challenge":
        print(p.challenge)
    elif sys.argv[1] == "imports":
        print(p.submission.replace("/", ".") + ".")
        print(p.target)
        print(p.claim_file)
    else:
        for value in [
            p.track,
            p.submission,
            p.challenge_module.replace(".", "/") + ".lean",
            p.claim_file,
            p.comparator,
        ]:
            print(value)


if __name__ == "__main__":
    main()

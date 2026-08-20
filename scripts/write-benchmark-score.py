#!/usr/bin/env python3
"""Write a local Yukon score after Comparator accepts either claim."""

from __future__ import annotations

import sys

from benchmark_contract import (
    DOMAIN_SIZE,
    arklib_revision,
    atomic_write_json,
    atomic_write_text,
    parse_centibits,
    parse_radius,
    parse_unsafe_index,
    submission_revision,
)


def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit(
            "usage: write-benchmark-score.py lower|upper CENTIBITS CLAIM"
        )

    profile, raw_score, claim = sys.argv[1:]
    if profile not in {"lower", "upper"}:
        raise SystemExit(f"unknown benchmark profile: {profile}")
    try:
        centibits = parse_centibits(raw_score)
        revision = arklib_revision()
        submission = submission_revision()
        bits = centibits / 100

        common = {
            "centibits": centibits,
            "bits": bits,
            "field": "KoalaBear^6",
            "code": "interleaved-Reed-Solomon",
            "totalDimension": 2**20,
            "interleaving": 8,
            "domainSize": DOMAIN_SIZE,
            "baseDimension": 2**17,
            "repetitions": 128,
            "verified": False,
            "locallyKernelChecked": True,
            "independentVerified": False,
            "verificationAuthority": "local-comparator-diagnostic",
            "launchEligible": False,
            "arklibRev": revision,
            "submissionRev": submission,
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
        }

        if profile == "lower":
            numerator, denominator = parse_radius(claim)
            exact_radius = f"{numerator}/{denominator}"
            track = "irs-reduction-threshold-lower"
            metrics = common | {
                "track": track,
                "claimKind": "certified-extractor-error-safe-radius",
                "direction": "induced-spot-check-bit-floor",
                "metric": "threshold_spot_floor_centibits",
                "radiusExact": exact_radius,
                "radius": numerator / denominator,
                "reductionErrorTarget": "2^-128",
                "reductionQuantity": "ToyProblem.Impl.IRS.certifiedGammaError",
                "winningSetRelation": (
                    "certified extractor error upper-bounds winning-set soundness"
                ),
                "spotCheckExpression": "(1 - radius)^128",
                "theorem": "ProximityPrize.Benchmark.candidate",
            }
            summary = (
                "## Proximity Prize — IRS reduction-threshold lower bound\n\n"
                f"- Induced spot-check-bit floor: **{bits:.2f} bits**\n"
                f"- Exact safe radius: `{exact_radius}`\n"
                "- Certified extractor-error target: `2^-128`\n"
            )
        else:
            unsafe_index = parse_unsafe_index(claim)
            exact_radius = f"{unsafe_index}/{DOMAIN_SIZE}"
            track = "irs-reduction-threshold-upper"
            metrics = common | {
                "track": track,
                "claimKind": "winning-set-unsafe-point",
                "direction": "minimize-attack-point-spot-check-bit-upper-bound",
                "metric": "reduction_upper_centibits",
                "unsafeIndex": unsafe_index,
                "unsafeRadiusExact": exact_radius,
                "unsafeRadius": unsafe_index / DOMAIN_SIZE,
                "winningSetTarget": "2^-128",
                "reductionQuantity": "ToyProblem.winningSetDensity",
                "spotCheckExpression": "(1 - unsafeRadius)^128",
                "theorem": "ProximityPrize.Benchmark.Upper.candidate",
            }
            summary = (
                "## Proximity Prize — IRS reduction-threshold upper attack\n\n"
                f"- Attack-point spot-check-bit upper bound: **{bits:.2f} bits**\n"
                f"- Attacked grid index: **{unsafe_index}**\n"
                f"- Exact attacked radius: `{exact_radius}`\n"
                "- Winning-set target: `2^-128`\n"
            )
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error

    atomic_write_json(
        f".yukon/{track}-score.json", {"score": bits, "metrics": metrics}
    )
    summary += (
        "- Leaderboard-authoritative: **no — independent verification required**\n"
        f"- ArkLib: `{revision}`\n"
        "- Profile: `k=2^20`, `s=8`, `n=2^18`, `t=128` over `KoalaBear^6`\n"
        "- Axioms: `propext`, `Classical.choice`, `Quot.sound`\n"
    )
    atomic_write_text(f"benchmark-results/{track}-summary.md", summary)


if __name__ == "__main__":
    main()

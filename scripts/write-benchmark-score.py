#!/usr/bin/env python3
"""Write a local Yukon score after Comparator accepts either claim."""

from __future__ import annotations

import sys

from benchmark_profiles import get_profile

from benchmark_contract import (
    arklib_revision,
    comppoly_source,
    lean_toolchain,
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
            "usage: write-benchmark-score.py lower|upper|binary-lower|binary-upper CENTIBITS CLAIM"
        )

    profile, raw_score, claim = sys.argv[1:]
    try:
        policy = get_profile(profile)
        centibits = parse_centibits(raw_score)
        revision = arklib_revision()
        comppoly_url, comppoly = comppoly_source()
        # The repository, not just the commit: production pins a zksecurity
        # fork while ArkLib declares Verified-zkEVM, and a bare hash cannot
        # tell a reader which of the two a score was checked against.
        comppoly_slug = "/".join(comppoly_url.split("/")[-2:])
        toolchain = lean_toolchain()
        submission = submission_revision()
        bits = centibits / 100

        common = {
            "centibits": centibits,
            "bits": bits,
            **policy.metadata(),
            "verified": False,
            "locallyKernelChecked": True,
            "independentVerified": False,
            "verificationAuthority": "local-comparator-diagnostic",
            "launchEligible": False,
            "arklibRev": revision,
            "compPolyRev": comppoly,
            "compPolyUrl": comppoly_url,
            "leanToolchain": toolchain,
            "submissionRev": submission,
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
        }

        if policy.side == "lower":
            numerator, denominator = parse_radius(claim)
            exact_radius = f"{numerator}/{denominator}"
            track = policy.track
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
                "theorem": policy.namespace + ".candidate",
            }
            summary = (
                "## Proximity Prize — IRS reduction-threshold lower bound\n\n"
                f"- Induced spot-check-bit floor: **{bits:.2f} bits**\n"
                f"- Exact safe radius: `{exact_radius}`\n"
                "- Certified extractor-error target: `2^-128`\n"
            )
        else:
            unsafe_index = parse_unsafe_index(claim, maximum=policy.max_unsafe_index)
            exact_radius = f"{unsafe_index}/{policy.domain_size}"
            track = policy.track
            metrics = common | {
                "track": track,
                "claimKind": "winning-set-unsafe-suffix",
                "direction": "induced-spot-check-bit-ceiling",
                "metric": "threshold_spot_ceiling_centibits",
                "unsafeIndex": unsafe_index,
                "unsafeRadiusExact": exact_radius,
                "unsafeRadius": unsafe_index / policy.domain_size,
                "winningSetTarget": "2^-128",
                "reductionQuantity": "ToyProblem.winningSetDensity",
                "spotCheckExpression": "(1 - unsafeRadius)^128",
                "theorem": policy.namespace + ".candidate",
            }
            summary = (
                "## Proximity Prize — IRS reduction-threshold upper bound\n\n"
                f"- Induced spot-check-bit ceiling: **{bits:.2f} bits**\n"
                f"- Unsafe-from-here grid index: **{unsafe_index}**\n"
                f"- Exact unsafe-from-here radius: `{exact_radius}`\n"
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
        f"- CompPoly: `{comppoly_slug}@{comppoly}`\n"
        f"- Lean: `{toolchain}`\n"
        f"- Profile: {policy.summary_line}\n"
        "- Axioms: `propext`, `Classical.choice`, `Quot.sound`\n"
    )
    atomic_write_text(f"benchmark-results/{track}-summary.md", summary)


if __name__ == "__main__":
    main()

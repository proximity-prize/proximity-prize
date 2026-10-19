#!/usr/bin/env python3
"""Convert an independently verified claim to Yukon's score format."""

from __future__ import annotations

import os
from pathlib import Path
import sys

from benchmark_profiles import PROFILES

from benchmark_contract import (
    arklib_revision,
    comppoly_source,
    lean_toolchain,
    MAX_FRACTION_COMPONENT,
    atomic_write_json,
    load_json_object,
    parse_centibits,
    parse_commit,
    parse_json_nat,
    parse_radius,
    parse_unsafe_index,
    read_scalar,
)

EXPECTED_SCALE = 100
POLICIES = {
    key: {
        "challenge": p.challenge,
        "direction": "maximize" if p.side == "lower" else "minimize",
        "track": p.track,
        "root": Path(p.submission),
        "profile": p,
    }
    for key, p in PROFILES.items()
}


def require_object(value: object, *, label: str) -> dict:
    if not isinstance(value, dict):
        raise ValueError(f"{label} must be a JSON object")
    return value


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit(
            "usage: write-verifier-score.py lower|upper|binary-lower|binary-upper RESULT.json"
        )
    profile, result_path = sys.argv[1:]
    policy = POLICIES.get(profile)
    if policy is None:
        raise SystemExit(f"unknown benchmark profile: {profile}")

    expected_version = os.environ.get("CHALLENGE_VERSION", "")
    if not expected_version:
        raise SystemExit("CHALLENGE_VERSION is not set")

    try:
        status = load_json_object(result_path)
        if status.get("status") != "verified":
            failure = status.get("failure")
            detail = failure if isinstance(failure, dict) else {}
            where = f"{detail.get('stage', '')}/{detail.get('code', '')}".rstrip("/")
            reason = detail.get("message") or ""
            raise ValueError(
                f"submission {status.get('status')}: {where}"
                + (f": {reason}" if reason else "")
            )

        challenge = require_object(status.get("challenge"), label="challenge")
        challenge_slug = challenge.get("challenge")
        version = challenge.get("version")
        if challenge_slug != policy["challenge"]:
            raise ValueError(
                f"service verified {challenge_slug}, expected {policy['challenge']}"
            )
        if version != expected_version:
            raise ValueError(f"service verified {version}, expected {expected_version}")

        result = require_object(status.get("result"), label="result")
        score = require_object(result.get("score"), label="result.score")
        metric = score.get("metric")
        if not isinstance(metric, str) or not metric:
            raise ValueError("result.score.metric must be a non-empty string")
        if score.get("direction") != policy["direction"] or score.get("unit") != "bits":
            raise ValueError(f"service score policy does not match the {profile} track")
        raw_value = score.get("value")
        if not isinstance(raw_value, str):
            raise ValueError("verified score must be a decimal string")
        value = parse_centibits(raw_value, label="verified score")
        scale = parse_json_nat(
            score.get("scale"),
            label="verified score scale",
            minimum=EXPECTED_SCALE,
            maximum=EXPECTED_SCALE,
        )

        root = policy["root"]
        claimed = parse_centibits(
            read_scalar(root / "score.txt"), label="committed score"
        )
        if value != claimed or scale != EXPECTED_SCALE:
            raise ValueError("verified service score does not match the committed claim")

        proof_metrics = require_object(result.get("metrics"), label="result.metrics")
        if policy["profile"].side == "lower":
            numerator, denominator = parse_radius(read_scalar(root / "radius.txt"))
            verified_numerator = parse_json_nat(
                proof_metrics.get("radius_numerator"),
                label="verified radius numerator",
                minimum=1,
                maximum=MAX_FRACTION_COMPONENT,
            )
            verified_denominator = parse_json_nat(
                proof_metrics.get("radius_denominator"),
                label="verified radius denominator",
                minimum=1,
                maximum=MAX_FRACTION_COMPONENT,
            )
            if (verified_numerator, verified_denominator) != (numerator, denominator):
                raise ValueError(
                    "verified service radius does not match the committed claim"
                )
            exact_radius = f"{numerator}/{denominator}"
            claim_metrics = {
                "radiusExact": exact_radius,
                "radius": numerator / denominator,
            }
        else:
            unsafe_index = parse_unsafe_index(
                read_scalar(root / "unsafe-index.txt"),
                label="committed unsafe index",
                maximum=policy["profile"].max_unsafe_index,
            )
            verified_unsafe_index = parse_json_nat(
                proof_metrics.get("unsafe_index"),
                label="verified unsafe index",
                minimum=1,
                maximum=policy["profile"].max_unsafe_index,
            )
            if verified_unsafe_index != unsafe_index:
                raise ValueError(
                    "verified service unsafe index does not match the committed claim"
                )
            claim_metrics = {
                "unsafeIndex": unsafe_index,
                "unsafeRadiusExact": f"{unsafe_index}/{policy['profile'].domain_size}",
                "unsafeRadius": unsafe_index / policy["profile"].domain_size,
            }

        resolved_value = status.get("resolved_commit") or status.get("commit")
        resolved_commit = parse_commit(resolved_value, label="resolved commit")
        expected_commit = parse_commit(
            os.environ.get("GITHUB_SHA"), label="GITHUB_SHA"
        )
        if resolved_commit != expected_commit:
            raise ValueError(
                f"service verified commit {resolved_commit}, expected {expected_commit}"
            )
        submission_id = status.get("id")
        if not isinstance(submission_id, str) or not submission_id:
            raise ValueError("service result has no submission id")
        comppoly_url, comppoly_rev = comppoly_source()
    except (KeyError, OSError, TypeError, ValueError) as error:
        raise SystemExit(str(error)) from error

    output = {
        "score": value / scale,
        "metrics": {
            **policy["profile"].metadata(),
            "arklibRev": arklib_revision(),
            "compPolyRev": comppoly_rev,
            "compPolyUrl": comppoly_url,
            "leanToolchain": lean_toolchain(),
            "verified": True,
            "locallyKernelChecked": True,
            "independentVerified": True,
            "verificationAuthority": "independent-verifier",
            "launchEligible": True,
            "track": policy["track"],
            "centibits": value,
            "metric": metric,
            "unit": "bits",
            **claim_metrics,
            "challenge": challenge_slug,
            "challengeVersion": version,
            "submissionId": submission_id,
            "commit": resolved_commit,
            "proofMetrics": proof_metrics,
        },
    }
    atomic_write_json(f".yukon/{policy['track']}-score.json", output)


if __name__ == "__main__":
    main()

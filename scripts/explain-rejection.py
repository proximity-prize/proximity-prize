#!/usr/bin/env python3
"""Put the verifier's own reason where the submitter will actually read it.

On failure the run's PR gets Yukon's wrapper -- `benchmark_failed: workflow run
concluded failure at step "Write Yukon score"` and a link -- while the reason
sits in this job's log, several clicks away. A solver whose proof verifies is
handed a table; a solver whose proof does not is handed a link. This writes the
reason to the job summary, which is the first thing that link opens onto.

It reads the verifier's own response and reformats it. It invents nothing: if
the service did not say why, this says that, rather than guessing a cause.

    explain-rejection.py verifier-result.json >> "$GITHUB_STEP_SUMMARY"
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

# What a submitter should do next, per failure code. Only codes whose remedy is
# genuinely different are listed; anything else falls back to the service's own
# message, which is more specific than a generic sentence would be.
ADVICE = {
    "proof_rejected": (
        "The candidate reached the verifier and was refused. The Lean error below is "
        "the verifier's own; it is the same build you can reproduce locally."
    ),
    "candidate_invalid": (
        "The submission tree was rejected before the proof was judged -- usually a file "
        "the source policy does not admit, or a missing required file."
    ),
    "submission_capacity_exceeded": (
        "Nothing is wrong with this submission. The repository already had its maximum "
        "number of submissions in flight, so this one was refused rather than queued. "
        "Resubmit once an earlier one finishes."
    ),
    "verifier_timeout_cleanup_pending": (
        "The candidate exceeded the challenge's time limit and was stopped. This is a "
        "statement about how long the proof takes to check, not about whether it is "
        "correct."
    ),
    "source_transport_retry_exhausted": (
        "The source could not be fetched from GitHub. This is an infrastructure "
        "failure, not a problem with the proof; resubmitting is reasonable."
    ),
}


def main(path: str) -> int:
    try:
        result = json.loads(Path(path).read_text())
    except (OSError, ValueError) as exc:
        print(f"## Verifier result unavailable\n\n`{type(exc).__name__}`: {exc}\n")
        return 0

    status = result.get("status") or "unknown"
    failure = result.get("failure") or {}
    code = failure.get("code") or ""
    stage = failure.get("stage") or ""
    message = (failure.get("message") or "").strip()

    lines = [f"## Submission {status}", ""]
    if code:
        lines += [f"**{code}**" + (f" · during `{stage}`" if stage else ""), ""]
    if code in ADVICE:
        lines += [ADVICE[code], ""]

    if message:
        lines += ["The verifier's own words:", "", "```", message, "```", ""]
    else:
        lines += [
            "The service returned no message for this failure. That is itself worth "
            "reporting -- a rejection should say why.",
            "",
        ]

    challenge = result.get("challenge") or {}
    if challenge:
        lines += [
            "| | |",
            "| --- | --- |",
            f"| challenge | `{challenge.get('challenge', '?')}` |",
            f"| version | `{challenge.get('version', '?')}` |",
            f"| commit | `{(result.get('resolved_commit') or result.get('commit') or '?')[:12]}` |",
            f"| submission | `{result.get('id', '?')}` |",
            "",
        ]
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1] if len(sys.argv) > 1 else "verifier-result.json"))

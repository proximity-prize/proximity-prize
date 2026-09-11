#!/usr/bin/env python3
"""Withdraw this job's submission when the job itself is cancelled."""

from __future__ import annotations

import json
import os
import sys
import urllib.error
import urllib.request

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from submit import TokenSource  # noqa: E402

TIMEOUT_SECONDS = 20


def _report(submission_id: str, detail: str, *, fatal: bool) -> None:
    """Say it where somebody will see it.

    This step only runs on a cancelled job, and nobody reads the log of a run
    they just cancelled. For five days every withdrawal here failed with a 500
    and the only trace was a line on stderr in exactly those logs -- so the
    verifier kept working on submissions their authors had already abandoned,
    and the first anyone knew of it was a fleet with no free hosts.

    A workflow command puts it on the run's own summary as an annotation, which
    survives the cancellation and is visible without opening the log.

    The exit code stays zero on purpose. The job is already cancelled and its
    conclusion cannot be improved by failing here; a red step would only hide
    the reason it was cancelled behind a reason it could not be withdrawn.
    """

    level = "error" if fatal else "warning"
    print(
        f"::{level} title=Submission not withdrawn::"
        f"{submission_id} is still running on the verifier: {detail}",
        flush=True,
    )
    print(f"withdrawal of {submission_id} failed: {detail}", file=sys.stderr)


def main() -> int:
    submission_id = os.environ.get("SUBMISSION_ID", "").strip()
    if not submission_id:
        print("no submission to cancel", file=sys.stderr)
        return 0

    base = os.environ.get("BASE", "").rstrip("/")
    if not base:
        print("BASE is not set; cannot cancel", file=sys.stderr)
        return 0

    try:
        token = TokenSource(base).get()
    except (SystemExit, urllib.error.URLError, OSError) as exc:
        print(f"could not mint a token to cancel {submission_id}: {exc}", file=sys.stderr)
        return 0

    request = urllib.request.Request(
        f"{base}/v1/submissions/{submission_id}/cancel", data=b"", method="POST"
    )
    request.add_header("Authorization", f"Bearer {token}")
    request.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(request, timeout=TIMEOUT_SECONDS) as response:
            status = json.loads(response.read().decode()).get("status", "?")
    except urllib.error.HTTPError as exc:
        _report(
            submission_id,
            f"the verifier answered {exc.code}",
            # 5xx is the verifier failing, not this submission being unusual, and
            # it is the case worth waking someone for: every withdrawal is
            # failing, not just this one.
            fatal=exc.code >= 500,
        )
        return 0
    except (urllib.error.URLError, OSError, ValueError) as exc:
        _report(submission_id, f"the request did not complete: {exc}", fatal=False)
        return 0

    print(f"cancelled {submission_id}; it is now {status}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

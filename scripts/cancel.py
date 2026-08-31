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
        print(f"cancel for {submission_id} returned {exc.code}", file=sys.stderr)
        return 0
    except (urllib.error.URLError, OSError, ValueError) as exc:
        print(f"cancel for {submission_id} did not complete: {exc}", file=sys.stderr)
        return 0

    print(f"cancelled {submission_id}; it is now {status}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

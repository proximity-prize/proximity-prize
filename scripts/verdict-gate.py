#!/usr/bin/env python3
"""Stop the run at the verdict, and say which kind of verdict it was.

Yukon names the step that failed. When the only step that can fail is "Write
Yukon score", every refused proof is announced as
`benchmark_failed: workflow run concluded failure at step "Write Yukon score"`,
which reads as though the harness broke rather than as though the proof was
refused -- even when the refusal was immediate and exactly as intended.

The run still has to fail -- there is no score, and a passing run would be
merged -- so this does not change the outcome. It changes which step's name ends
up in that sentence, and it separates the two cases that were sharing one exit:

  rejected  the proof was checked and did not hold. The author's answer, and
            nothing is wrong with the service.
  failed    the proof was never checked. Ours, not theirs.
  timeout   the proof was not checked in the time allowed. Also ours, in the
            sense that the author cannot act on it.

`write-verifier-score.py` keeps its own gate. This is a clearer message in front
of it, not a replacement for it: a script that writes a score must refuse a
result it was not given, whatever ran before it.
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

VERDICTS = {
    "rejected": "The proof was checked and refused. This is a verdict on the "
    "submission, not a failure of the benchmark.",
    "failed": "The submission was never checked -- the verifier could not reach "
    "a verdict. This is an infrastructure fault, not a judgement on the proof.",
    "timeout": "The submission was not checked within the time limit. This is a "
    "resource outcome, not a judgement on the proof.",
}

# Some failures carry their cause in the code, and the status is too coarse to
# describe them. `failed` means "no verdict was reached", which is true of a
# broken verifier and equally true of a candidate that outgrew a published
# ceiling -- and only one of those is ours. Without this the headline told an
# author their submission was an infrastructure fault while the two lines under
# it named the ceiling they had exceeded.
#
# Keyed on the code rather than a new status because the status is what every
# caller, poller and terminal-state set already agrees on; this is a better
# sentence in front of it, not a new state to roll out.
CODE_VERDICTS = {
    # Points at AGENTS.md and nothing else. The manifest that sets the ceiling
    # lives in a private repository and no endpoint publishes it, so naming it
    # sent an author to a door they cannot open. The rule in their own checkout
    # carries the same number and says what to do about it.
    "candidate_out_of_memory": "The submission exceeded the memory the challenge "
    "allows. This is a resource outcome, not a judgement on the proof -- see the "
    "memory rule in AGENTS.md, which gives the budget and the usual cause.",
    "candidate_out_of_disk": "The build filled the disk the challenge allows and "
    "stopped partway. This is a resource outcome, not a judgement on the proof: "
    "nothing was checked, so a correct proof fails this way too -- see the disk "
    "rule in AGENTS.md, which gives the budget and the usual cause.",
}


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: verdict-gate.py RESULT.json", file=sys.stderr)
        return 2
    path = Path(sys.argv[1])
    try:
        status = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        print(f"cannot read {path}: {exc}", file=sys.stderr)
        return 2
    if not isinstance(status, dict):
        print(f"{path} is not a JSON object", file=sys.stderr)
        return 2

    state = status.get("status")
    if state == "verified":
        return 0

    failure = status.get("failure")
    detail = failure if isinstance(failure, dict) else {}
    code = detail.get("code") or "unknown"
    message = detail.get("message") or ""
    headline = CODE_VERDICTS.get(code) or VERDICTS.get(
        state, f"The submission ended in state {state!r}."
    )

    # stderr so it lands in the step's own log, where the link in Yukon's
    # comment points.
    print(f"{headline}", file=sys.stderr)
    print(f"  status: {state}", file=sys.stderr)
    print(f"  code:   {code}", file=sys.stderr)
    if message:
        print(f"  reason: {message[:2000]}", file=sys.stderr)

    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        if state == "rejected":
            title = "Proof refused"
        elif code in CODE_VERDICTS:
            title = "Submission exceeded a challenge limit"
        else:
            title = "Verification did not complete"
        with open(summary, "a", encoding="utf-8") as handle:
            handle.write(f"## {title}\n\n{headline}\n\n")
            handle.write(f"- **status**: `{state}`\n- **code**: `{code}`\n")
            if message:
                handle.write(f"\n```\n{message[:2000]}\n```\n")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())

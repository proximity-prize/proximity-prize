#!/usr/bin/env python3
"""Submit one commit for verification and print the terminal status as JSON.

The service fetches the commit itself, so nothing is uploaded and this script
needs no knowledge of the verifier or its sandbox.

Two things here are less obvious than they look, and both only bite on a slow
verification:

* **The token expires.** ``GET /v1/submissions/{id}`` is authenticated, and the
  service rejects an OIDC token older than 600 seconds while a verification may
  run to the challenge's own 1200-second timeout. So the token is minted here,
  from the runner's token service, and re-minted before it ages out, rather
  than passed in once and treated as an API key.
* **An idempotency key belongs to one run.** The service binds it to a request
  digest that includes the run id and attempt, so reusing a key across runs is
  a conflict rather than a replay.
* **There are more terminal states than the obvious three.** ``source_failed``
  and ``timeout`` end a submission as surely as ``verified``; waiting only for
  the familiar ones burns the whole deadline for nothing.

Exits non-zero only if the submission could not be resolved at all. A
``rejected`` verdict is a successful run of this script.
"""

from __future__ import annotations

import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

POLL_SECONDS = 10
SUBMIT_RETRY_SECONDS = 60
# There is deliberately no deadline here. The job's `timeout-minutes` is the one
# bound, so how long a submission may take is configured where every other limit
# on this workflow is, and cannot silently disagree with it -- which it did:
# a 2400s poll budget sized for v3's 1200s challenge sat inside a 50-minute job
# cap, and would have begun abandoning verdicts the moment v4 raised the
# challenge timeout to 1500s.
#
# The cost is that a submission which outlives the job ends as a cancelled run
# rather than a failed one, losing the "gave up waiting for <id>" line. That was
# the only thing the inner deadline bought: it raised `SystemExit` without
# writing the result, so the summary step had nothing to explain either way.
TOKEN_REFRESH_SECONDS = 240      # well inside the service's 600s ceiling

# Every state the service can stop in. `rejected` is a verdict about the proof;
# the others are failures of everything around it, and mean something different.
TERMINAL = {"verified", "rejected", "failed", "source_failed", "timeout"}


class Busy(Exception):
    """The service is at capacity: 429, and worth retrying rather than failing."""


class TokenSource:
    """Mints OIDC tokens from the Actions runner, and refreshes them on demand."""

    def __init__(self, audience: str) -> None:
        self._audience = audience
        self._url = os.environ.get("ACTIONS_ID_TOKEN_REQUEST_URL")
        self._runner_token = os.environ.get("ACTIONS_ID_TOKEN_REQUEST_TOKEN")
        # A token supplied by the caller is honoured but cannot be refreshed;
        # anything that might poll for long should let this script mint its own.
        self._static = os.environ.get("TOKEN")
        if not self._static and not (self._url and self._runner_token):
            raise SystemExit(
                "no OIDC token available: set TOKEN, or grant permissions "
                "id-token: write so the runner exposes its token service"
            )
        self._value = self._static or ""
        self._minted_at = 0.0

    def get(self) -> str:
        if self._static:
            return self._static
        if not self._value or time.monotonic() - self._minted_at > TOKEN_REFRESH_SECONDS:
            query = urllib.parse.urlencode({"audience": self._audience})
            request = urllib.request.Request(f"{self._url}&{query}")
            request.add_header("Authorization", f"bearer {self._runner_token}")
            with urllib.request.urlopen(request, timeout=30) as response:
                self._value = json.loads(response.read().decode())["value"]
            self._minted_at = time.monotonic()
        return self._value


def _call(url: str, tokens: TokenSource, payload: dict | None = None,
          idempotency_key: str | None = None) -> dict:
    data = json.dumps(payload).encode() if payload is not None else None
    request = urllib.request.Request(url, data=data, method="POST" if data else "GET")
    request.add_header("Authorization", f"Bearer {tokens.get()}")
    if data:
        request.add_header("Content-Type", "application/json")
    if idempotency_key:
        request.add_header("Idempotency-Key", idempotency_key)
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            return json.loads(response.read().decode())
    except urllib.error.HTTPError as exc:
        body = exc.read().decode("utf-8", "replace")[:500]
        if exc.code == 429:
            # Capacity, not a verdict. Verification is serialized, so a busy
            # service is a normal condition and worth waiting out rather than
            # failing a job over.
            raise Busy(body) from exc
        raise SystemExit(f"{url} -> HTTP {exc.code}: {body}") from exc


def main() -> None:
    base = os.environ["BASE"].rstrip("/")
    repository = os.environ["REPOSITORY"]
    commit = os.environ["COMMIT"]
    challenge = os.environ["CHALLENGE"]
    # Optional. Empty means the service picks the challenge's active version,
    # which is what every submission did before this existed.
    challenge_version = os.environ.get("CHALLENGE_VERSION", "").strip() or None
    tokens = TokenSource(base)

    # The key is required, and scoped to this run. The service binds a key to
    # one request including its run id and attempt, so a key reused across two
    # runs is `idempotency_conflict`, not a replay -- it exists to make HTTP
    # retries *within* an attempt safe, not to deduplicate attempts.
    run = os.environ.get("GITHUB_RUN_ID", "local")
    attempt = os.environ.get("GITHUB_RUN_ATTEMPT", "1")
    target = challenge if challenge_version is None else f"{challenge}@{challenge_version}"
    # The version belongs in the key because it is part of the request the key
    # is bound to: re-running an attempt after bumping the pin would otherwise
    # reuse a key that named the old version and get `idempotency_conflict`
    # instead of a submission.
    key = f"{target}:{commit[:12]}:{run}.{attempt}"[:200]

    created = _submit_when_there_is_room(
        base, tokens, repository=repository, commit=commit,
        challenge=challenge, challenge_version=challenge_version,
        idempotency_key=key,
    )
    submission_id = created["id"]
    if created.get("idempotent_replay"):
        print("replaying an earlier submission of these bytes", file=sys.stderr)
    print(f"submission {submission_id} for {commit[:12]}", file=sys.stderr)

    seen = ""
    while True:
        status = _call(f"{base}/v1/submissions/{submission_id}", tokens)
        if status["status"] != seen:
            seen = status["status"]
            print(f"  {seen}", file=sys.stderr)
        if seen in TERMINAL:
            break
        time.sleep(POLL_SECONDS)

    json.dump(status, sys.stdout, indent=2, sort_keys=True)
    print()


def _submit_when_there_is_room(
    base: str, tokens: TokenSource, *, repository: str, commit: str,
    challenge: str, challenge_version: str | None, idempotency_key: str,
) -> dict:
    """Submit, waiting out a full queue rather than failing the job over it.

    Verification is serialized, so `submission_capacity_exceeded` is a normal
    condition rather than a verdict, and worth waiting on.

    `challenge_version` is sent only when CHALLENGE_VERSION is set. Omitting it
    means the service resolves the challenge's active version, so an operator
    can move everyone forward without touching this repository. Sending it
    pins an exact version, which a commit whose source only builds against one
    statement needs -- and is answered with `challenge_version_not_accepting`
    once that version is retired, rather than being silently moved onto a
    successor whose score means something different.
    """

    request = {
        "schema_version": 1,
        "repository": repository,
        "commit": commit,
        "challenge": challenge,
    }
    if challenge_version is not None:
        # The API refuses a version without its challenge (`422
        # incomplete_challenge_selection`); versions are unique only within one.
        request["challenge_version"] = challenge_version

    while True:
        try:
            return _call(
                f"{base}/v1/submissions",
                tokens,
                request,
                idempotency_key=idempotency_key,
            )
        except Busy:
            # No deadline, for the same reason as the poll loop: the job's
            # `timeout-minutes` decides how long this may take. A capacity
            # refusal says the service is busy, not that the proof is wrong,
            # and a submission that fails for it is failed permanently --
            # Yukon records one verdict and never revisits.
            print(f"  at capacity, retrying in {SUBMIT_RETRY_SECONDS}s", file=sys.stderr)
            time.sleep(SUBMIT_RETRY_SECONDS)


if __name__ == "__main__":
    main()

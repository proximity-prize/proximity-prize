# Better.codes imports into Prove2Me

This integration is prepared locally. The schedule and publication are disabled
by default. No provider records, verifier profiles or deployments were changed.

Prove2Me stores definitions, statements, proof attempts and dependencies. This
repository only prepares and publishes Lean files. Yukon reads the provider and
keeps no proof database. Original submissions retain their commits, scores and
attribution. A confirmed publication catalog connects provider UUIDs to source.

## Local commands

Run the ordinary Python checks without provider credentials:

```sh
python3 -m unittest discover -s scripts/prove2me -p 'test_*.py'
python3 scripts/check-versions.py
```

The batch stages are independently runnable. `inventory` reads public Yukon
submissions, starts with the current winners and includes nonwinning attempts.
It selects one source commit per batch. The default state is local; R2 is optional.
Discovery builds all tracked Lean modules in that submission root, including
helpers the final claim does not import. Independently compiled public lemmas
and definitions are offered to the agent even when they are short or unused.
A failed nonwinning final attempt does not hide working helper modules. Only
selected results that pass the source-fidelity and admission checks can publish;
this does not turn a failed competition attempt into an accepted submission.

```sh
python3 scripts/prove2me/batch.py inventory --directory batch
python3 scripts/prove2me/batch.py prepare --directory batch --repository "$PWD"
python3 scripts/prove2me/batch.py extract --directory batch --upstream /path/to/prove2me_workspace
# The agent follows agent-prompt.md and writes batch/prepared.json.
python3 scripts/prove2me/batch.py check --directory batch
python3 scripts/prove2me/batch.py publish --directory batch
```

The final command checks the publication bundle and makes no provider requests.
Only the explicit `--publish` option permits writes. Do not set publication or
storage credentials during prepare, extract, or check; those stages reject them.
Run Lean work on an appropriate compute host. FarmShare execution and prior proof
reports remain outside this release.

The upstream checkout must be at
`6b46503a65c3a4252170ed5ca984a796b5a5b6b4`. We reuse its declaration graph and
sketch-position scripts, with the documented root/prefix customization. The
agent handles useful-node selection, scope/import adaptation and descriptions;
`generate.py` performs exact byte-range cuts and renames. It does not split Lean
proofs with regex. The checker compares elaborated types, definition bodies and
constructor shapes with native source and checks for untracked admissions.

A historical source whose toolchain differs needs an explicit maintenance port;
it remains unprocessed instead of being misrepresented as compatible. The batch
records attempt times, tries other fresh sources, then retries older attempts.
Queued provider publications take priority so checked work can resume directly.
One incompatible or failed source does not block every future submission. `config.json`
contains the two winning sources' local ports. The upper source at `224323f` has
identical submission bytes at `1b2ca03`. Future unported historical attempts may
need additional agent/maintainer work before they can pass this gate.

## Checkpoints and recovery

Only `state.json` and `catalog.json` live under an existing R2 prefix such as
`s3://<existing-bucket>/prove2me/better-codes`. State contains completed-work IDs,
upload/proof job receipts, hashes and original-source mappings. It contains no
second authoritative graph. The catalog contains confirmed public provider IDs,
root markers and source links; proof status always comes from Prove2Me.

A queued upload is not a publication. The publisher waits for a matching public
`PUBLISHED` receipt and verifies its environment and statement context before
recording its theorem ID. A reduction accepted with open dependencies remains
`SKETCH_ACCEPTED`, distinct from a fully accepted proof.

Before each POST the publisher saves its intent. After a lost response it searches
the owner's job history or exact proof source and resumes the unique matching job.
An uncertain or ambiguous request is never blindly repeated. Failed jobs remain
in state for explicit repair. Repeated unchanged statements reuse the same record;
another proof can be added without replacing the statement or its original source.

The workflow permits one batch at a time and has a combined 235-minute job budget
plus a shared four-hour deadline. GitHub caches hold native preparation progress
and checked bundles, while per-module source bindings allow extraction to resume.
Checked bundles are keyed by the source and checker version; pending publication
can resume without repeating Lean work. Cache eviction can require recomputation.
`--workers 2` permits bounded parallel extraction; one worker is the default
because the earlier two-worker Lean run was slower under contention.

## Local verification and the remaining external checks

Python tests cover source selection, exact byte edits, context identity,
credential separation, queueing, interrupted POSTs, duplicate prevention, private
records, failed jobs and accepted reductions. They use a simulated provider.
They do not establish that the authenticated hosted contract matches those fixtures.

The pinned upstream SumSquares example was also mechanically converted and checked
with Lean 4.33.1: native/staged definition bodies and theorem types matched, its
shared reduction dependency remained tracked, and the unproved stub was detected.
The completed compute check took 328.76 seconds. This is a real local Lean check,
separate from the simulated publication service and the competition verifier.

The Lean compatibility files at `8b7e6d422a8d7f4554e06ae2ed23eb12c1651ebf` are
byte-identical to the previously checked corrected port. They preserve the
current competition's newer source rules and workflow. The lower claim remains
`ProtocolClaim 6804 10341375 33554432` (68.04 bits); the upper claim remains
`ProtocolClaimUpper 11613 122369` (116.13 bits).

The public workflow still selects the service profiles in `challenges.json`.
Changing this repository's Lean version does not update the separate verifier
service. Before any future remote use, its maintainer must register matching
immutable profiles using this toolchain, dependency pins and comparator changes,
preserve the current limits and scoring, and run both winners plus the malformed
proof/import negative cases. Those actual competition checks have not run here.
Do not run Yukon benchmark reorganization; it would reset and replay results.

The CompPoly pin `9d36af56cd57a468ade1cbbc8fae324983d79708` is currently local.
`benchmark/comp-poly-lean4331.patch` carries that exact dependency fix and its
regression test for review. A remote clean checkout needs that commit made
available at its configured repository before dependency installation can succeed.
Likewise the configured maintenance source commits are local until a separately
approved push. The `--repository` override supports local Git preparation now.

For a future hosted test, the service account, actual authenticated graph
responses, matching verifier profiles and accessible dependency/maintenance pins
must be available first. Keep `PROVE2ME_SYNC_ENABLED` and
`PROVE2ME_PUBLICATION_READY` unset for local work. Enabling the daily schedule is
a separate decision after a hosted solver-A → import → independent-solver-B test
and its normal competition verification pass.

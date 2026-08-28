# Agent instructions

When changing or preparing submissions for the reduction-threshold benchmarks:

1. Treat each challenge as self-contained. A lower submission may import only
   `ProximityPrize.Benchmark.TargetLower` and modules in
   `ProximityPrize.SubmissionLower`; an upper submission may import only
   `ProximityPrize.Benchmark.TargetUpper` and modules in
   `ProximityPrize.SubmissionUpper`. Never cross-import between challenges.
   Ignore the umbrella `ProximityPrize.lean` when preparing a submission; do
   not import `ProximityPrize`.
2. Keep each submission root flat. Put `Solution.lean`, every helper `.lean`
   file, `score.txt`, and the track-specific claim file directly in that root.
   Subdirectories are not allowed.
3. Stay inside the verifier's size limits. Both tracks admit at most **1000
   files**, **4 MiB per file**, and **4 MiB across the whole submission root**.
   The total is the limit that bites first: it is the same 4 MiB as the
   per-file one, so a few large generated modules can exhaust it even though
   each is individually fine. Nothing in this repository enforces these — the
   submission is refused at the fetch stage, before anything is compiled, and
   the claim is not scored.
4. Do not use the submission as an archive. Only `.lean` files plus `score.txt`
   and the track claim file (`radius.txt` for lower, `unsafe-index.txt` for
   upper) are admitted at all, and files that no import reaches still count
   against every limit in rule 3.

Keep these rules aligned with `scripts/check-submission-imports.sh` and with
the independent verifier's source policy, which is the authority: `source:` in
the challenge manifest (`max_files`, `max_file_bytes`, `max_total_bytes`,
`max_depth`, `allowed_suffixes`, `allowed_files`). If they ever disagree, the
manifest wins and this file is stale.

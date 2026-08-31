# Agent instructions

When changing or preparing submissions for the reduction-threshold benchmarks:

1. Treat each challenge as self-contained. A lower submission may import only
   `ProximityPrize.Benchmark.TargetLower` and modules in
   `ProximityPrize.SubmissionLower`; an upper submission may import only
   `ProximityPrize.Benchmark.TargetUpper` and modules in
   `ProximityPrize.SubmissionUpper`. Never cross-import between challenges.
   Ignore the umbrella `ProximityPrize.lean` when preparing a submission; do
   not import `ProximityPrize`.

   **`Mathlib`, `ArkLib` and `CompPoly` may be imported freely**, at any depth.
2. Keep each submission root flat. Put `Solution.lean`, every helper `.lean`
   file, `score.txt`, and the track-specific claim file directly in that root.
   Subdirectories are not allowed.
3. Stay inside the verifier's size limits. Both tracks admit at most **1000
   files**, **4 MiB per file**, and **4 MiB across the whole submission root**.
   The total is the one to watch: it counts every admitted file together, so
   several generated modules can exhaust it while each stays well inside the
   per-file cap. Nothing in this repository enforces these — the submission is
   refused at the fetch stage, before anything is compiled, and the claim is
   not scored.
4. Do not use the submission as an archive. Only `.lean` files plus `score.txt`
   and the track claim file (`radius.txt` for lower, `unsafe-index.txt` for
   upper) are admitted at all, and files that no import reaches still count
   against every limit in rule 3.

   In particular, **do not copy library source into the submission**. Import it.
   `Mathlib`, `ArkLib` and `CompPoly` are built ahead of time in the verifier
   image, so an `import` loads a finished module, while a copied `.lean` file is
   elaborated from scratch on every run, inside the same memory and time budgets
   as your own proof.
5. Stay inside the verifier's **memory** budget. Both tracks currently allow
   **24 GiB** for the whole build. Exceeding it fails the submission without
   scoring it and without a useful message about the proof.

   `decide` and `native_decide` over a large finite computation are the usual
   way to exceed it, and the cost is not visible in the source — a single
   `decide` over a few hundred terms of large naturals can want tens of
   gigabytes. Prefer a proof to an evaluation, and split a large `decide` into
   lemmas the kernel can check separately.
6. Stay inside the verifier's **time** budget. Both tracks currently allow
   **80 minutes** for the whole build, and a submission that runs past it is
   failed unscored, exactly like the memory ceiling. This repository's own
   benchmark job allows 180, so a submission can build green here and still be
   cut off there; a local build that takes over an hour is already close.

Keep these rules aligned with `scripts/check-submission-imports.sh` and with
the independent verifier's source policy, which is the authority: `source:` in
the challenge manifest (`max_files`, `max_file_bytes`, `max_total_bytes`,
`max_depth`, `allowed_suffixes`, `allowed_files`). If they ever disagree, the
manifest wins and this file is stale.

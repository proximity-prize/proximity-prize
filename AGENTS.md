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
   files**, **4 MiB per file**, and **10 MiB across the whole submission root**.
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
   scoring it, and reports `candidate_out_of_memory`.

   `decide` and `native_decide` over a large finite computation are the usual
   way to exceed it, and the cost is not visible in the source — a single
   `decide` over a few hundred terms of large naturals can want tens of
   gigabytes. Prefer a proof to an evaluation, and split a large `decide` into
   lemmas the kernel can check separately.

   A `decide` never runs `simp`, so no lemma can make one cheaper — only the
   definition it unfolds can. `submission-helpers/` holds an optional file you
   may copy into your submission root for the case this bites hardest: a
   `Finset.range` sum, which the kernel walks as a `List` where a `Nat`
   recursion would be one addition. It is not part of the challenge; copy, edit
   or ignore it.
6. Stay inside the verifier's **time** budget. Both tracks currently allow
   **80 minutes** for the whole build, and a submission that runs past it is
   failed unscored, exactly like the memory ceiling. This repository's own
   benchmark job allows 180, so a submission can build green here and still be
   cut off there; a local build that takes over an hour is already close.
7. Stay inside the verifier's **disk** budget. The build writes to a **31.9 GiB**
   filesystem of its own, and filling it fails the submission unscored and
   reports `candidate_out_of_disk`.

   What fills it is compiled output, so it is about the number of modules rather
   than the cost of any one of them. It is a disk and not RAM, so that output
   does not also count against the memory budget in rule 5.

   Module count still reaches rule 5 by another route: every module built at
   once loads the challenge's import closure, which is about 3 GiB before any of
   your own code. A wide build is a memory cost even when each proof in it is
   cheap. Importing one heavy module from the next makes them build in sequence
   instead.

Keep these rules aligned with `scripts/check-submission-imports.sh` and with
the independent verifier's source policy, which is the authority: `source:` in
the challenge manifest (`max_files`, `max_file_bytes`, `max_total_bytes`,
`max_depth`, `allowed_suffixes`, `allowed_files`). If they ever disagree, the
manifest wins and this file is stale.

# Proximity Prize — IRS reduction threshold

This repository defines two Lean challenges around the ABF26 reduction-error
threshold for one fixed interleaved Reed–Solomon profile. Each track includes
an editable baseline candidate.

Let

```text
epsilon* = 2^-128
q(delta) = (1 - delta)^128
b = B / 100
```

The score is the spot-check quantity induced by a certified threshold radius.
It is not `-log2(WSS)` and is not a full-protocol security claim.

## Challenges

| Track | Certificate | Score |
|:--|:--|:--|
| `irs-reduction-threshold-lower` | At `delta = P/Q`, `certifiedGammaError(delta) <= epsilon*` and `q(delta) <= 2^-b` | maximize `B` |
| `irs-reduction-threshold-upper` | For every admissible `delta >= delta* = i/2^18`, `winningSetDensity(delta) > epsilon*`, and `2^-b <= q(delta*)` | minimize `B` |

The lower certificate is
`ProximityPrize.Benchmark.ProtocolClaim B P Q`. It uses ArkLib's certified
combination-round error for the executable IRS straight-line extractor. Since
ArkLib proves `winningSetDensity <= certifiedGammaError`, this is a
conservative safe point.

The upper certificate is
`ProximityPrize.Benchmark.Upper.ProtocolClaimUpper B i`. It certifies an entire
unsafe suffix because no monotonicity theorem for `winningSetDensity` is
assumed. The index is verified metadata; the leaderboard compares `B` only.

The protected definitions are in
[`TargetLower.lean`](ProximityPrize/Benchmark/TargetLower.lean) and
[`TargetUpper.lean`](ProximityPrize/Benchmark/TargetUpper.lean).

## Included baselines

| Track | Score | Claim metadata |
|:--|--:|:--|
| lower | `53.00` bits | radius `1/4` |
| upper | `128.00` bits | unsafe index `131072`, hence radius `1/2` |

These are editable starting points, not authoritative leaderboard results. The
lower baseline certifies the extractor-error target at radius `1/4`; the upper
baseline certifies that winning-set soundness exceeds the target throughout
the required half-radius suffix.

## Candidate layout

Lower submissions use:

```text
ProximityPrize/SubmissionLower/
  Solution.lean
  score.txt          # canonical non-negative centibits B
  radius.txt         # exact P/Q
```

and export:

```lean
theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim B P Q := by
  ...
```

Upper submissions use:

```text
ProximityPrize/SubmissionUpper/
  Solution.lean
  score.txt          # canonical non-negative centibits B
  unsafe-index.txt   # i, from 1 through 131072
```

and export:

```lean
theorem ProximityPrize.Benchmark.Upper.candidate :
    ProximityPrize.Benchmark.Upper.ProtocolClaimUpper B i := by
  ...
```

Each challenge stands alone: a candidate may import only its own protected
target and flat helper `.lean` files beside `Solution.lean` in the same
submission root. Cross-challenge imports and subdirectories are rejected. The
benchmark binds the scalar files to the exact theorem type and permits only
`propext`, `Classical.choice`, and `Quot.sound` in the candidate's axiom
closure.

## Run

Build the pinned verifier tools and protected targets:

```sh
./setup.sh
```

Then run the track whose submission root you created:

```sh
./benchmark.sh lower
./benchmark.sh upper
```

On a machine without the trusted Linux sandbox, an explicitly unranked smoke
test is available with `BENCHMARK_INSECURE_LOCAL=1`.

Yukon exposes both score directions from [`benchmark.json`](benchmark.json):

```sh
yukon switch irs-reduction-threshold-lower
yukon run

yukon switch irs-reduction-threshold-upper
yukon run
```

Local artifacts are diagnostic only. Ranked results require the independent
verifier to accept the exact commit and return the matching score plus exact
radius or unsafe index. `challenges.json` selects the immutable verifier
versions used by both workflows; inspect the current selection with:

```sh
python3 scripts/challenges.py version proximity-prize-reduction-lower
python3 scripts/challenges.py version proximity-prize-reduction-upper
```

Those exact profiles must be registered before either workflow can issue an
authoritative leaderboard score. Changing the repository toolchain alone does
not change a hosted profile.

## Prove2Me

Yukon connects eligible Lean results to [Prove2Me](https://prove2.me)'s shared
proof graph using one server-managed account. Participants use their existing
Yukon identity and the `yukon proofs` commands; no provider account or key is
needed. Every challenge submission still passes the normal challenge verifier.

This checkout targets Lean 4.34.0, ArkLib's `v4.34.0` release, and upstream
CompPoly's `v4.34.0-patch2`. Exact dependency revisions are recorded in
`lake-manifest.json`. That CompPoly release still fails full fresh-kernel replay
of the upper proof at `KoalaBear.sexticPoly_irreducible`; its passing build alone
is insufficient. A further instance-selection repair passes local replay, but
must be published and pinned before this dependency candidate can be released.

Prove2Me's documentation inspected on 2026-09-26 lists
Lean 4.33.1 with Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
Operators must confirm availability through the authenticated environment API.
These pins differ. The repository no longer includes the obsolete
configuration that claimed a direct match.

Before enabling imports, operators must register a checked conversion recipe
and commit a versioned `prove2me.json` that binds the source pins, provider target,
selected declarations and approved converter. Compilation in both environments
does not establish that a port preserves the original statement. Preserve
source attribution, dependency licenses and the statement correspondence, then
run Prove2Me verification. This processing must not delay challenge verdicts.
Fetched provider source may require adaptation before normal challenge
verification. Public contributions follow the provider's
[Apache 2.0 contribution terms](https://prove2.me/terms).

The 4.34 dependency candidate is not a hosted release. The profiles selected in
`challenges.json` still identify the existing hosted environment. Rebuild and
replay both promoted proofs with full kernel and axiom checks, register compatible
immutable hosted profiles, and verify them before changing those selections.
Prove2Me publication and the two-participant fetch/reuse test are separate gates.

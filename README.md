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

The lower score is a centibit lower bound on `-log2(q(delta))`; the upper score
is a centibit upper bound at the attacked radius. Neither is `-log2(WSS)` or a
full-protocol security claim.

## Challenges

| Track | Certificate | Score |
|:--|:--|:--|
| `irs-reduction-threshold-lower` | At `delta = P/Q`, `certifiedGammaError(delta) <= epsilon*` and `q(delta) <= 2^-b` | maximize `B` |
| `irs-reduction-threshold-upper` | At `delta* = i/2^18`, `winningSetDensity(delta*) > epsilon*` and `2^-b <= q(delta*)` | minimize `B` |

The lower certificate is
`ProximityPrize.Benchmark.ProtocolClaim B P Q`. It uses ArkLib's certified
combination-round error for the executable IRS straight-line extractor. Since
ArkLib proves `winningSetDensity <= certifiedGammaError`, this is a
conservative safe point.

The upper certificate is
`ProximityPrize.Benchmark.Upper.ProtocolClaimUpper B i`. It certifies one
attacked radius and says nothing about any other radius; it need not be the first
unsafe point and does not claim a global safe/unsafe frontier. The index is
verified metadata; the leaderboard compares `B` only.

Without a monotonicity theorem for `winningSetDensity`, the lower safe point and
upper attacked point do not by themselves certify a threshold interval.

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
baseline certifies that winning-set density exceeds the target at radius `1/2`.

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
radius or unsafe index. The repository-side identities are:

```text
proximity-prize-reduction-lower @ irs-reduction-threshold-v1
proximity-prize-reduction-upper @ irs-reduction-threshold-v3
```

The upper v3 verifier profile must be registered before its workflow can issue
an authoritative leaderboard score.

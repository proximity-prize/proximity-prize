# Proximity Prize — IRS reduction threshold

This repository defines lower and upper Lean challenges for two interleaved Reed-Solomon profiles: the original KoalaBear profile and a binary-field profile with leanVM code geometry. Both instantiate ArkLib's formally specified Toy IOP. Each track includes an editable baseline candidate.

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

## Binary profile

The binary tracks are `binary-irs-reduction-threshold-lower` and `binary-irs-reduction-threshold-upper`. Their protected targets are [BinaryTargetLower.lean](ProximityPrize/Benchmark/BinaryTargetLower.lean) and [BinaryTargetUpper.lean](ProximityPrize/Benchmark/BinaryTargetUpper.lean), with declarations `ProximityPrize.Benchmark.Binary.ProtocolClaim` and `ProximityPrize.Benchmark.Binary.Upper.ProtocolClaimUpper`.

| Parameter | Binary profile |
| --- | --- |
| Challenge field | `BF64.Ext3`: GF(2^64)[y]/(y^3+y+1), cardinality 2^192 |
| Base field | GF(2)[x]/(x^64+x^4+x^3+x+1) |
| Evaluation domain | First 2^21 polynomial-basis bit patterns in the base field, embedded into the challenge field |
| Total dimension / interleaving / row dimension | 2^26 / 64 / 2^20 |
| Rate / minimum column distance | 1/2 / 1048577 |
| Spot checks / combination certificate target | 128 / 2^-128 |

The shape matches leanVM's 2^18-compression Flock batch: 2^14 witness bits per compression packed 64 bits per base-field word give 2^26 words; 64 lanes and rate 1/2 give a 2^21-point domain. The Toy IOP uses arbitrary extension-field received words and its existing affine combination of two interleaved arrays. A formal WHIR specification is not a prerequisite, and this challenge does not assert full Flock or WHIR security.

The binary lower seed claims `53.00` bits at radius `1/4`. The binary upper seed claims `128.00` bits at unsafe index `1048576`, hence radius `1/2`. The upper index range is 1 through 1048576, with grid denominator 2097152. The corresponding original-profile limits remain 131072 and 262144.

Binary candidate roots are `ProximityPrize/SubmissionBinaryLower` and `ProximityPrize/SubmissionBinaryUpper`. They export `ProximityPrize.Benchmark.Binary.candidate` and `ProximityPrize.Benchmark.Binary.Upper.candidate`. The same flat layout, allowed artifacts, own-target import policy, and axiom restrictions apply to every track. Binary candidates may import only their own binary target and helpers, plus Mathlib/ArkLib/CompPoly.

The binary profile is fixed in [BinaryIRSProfile.lean](ProximityPrize/Benchmark/BinaryIRSProfile.lean). The naive Toy opening estimate is 282624 bytes for 128 full paths and 64 extension-field symbols per query; it is not leanVM's serialized proof size. Application source is pinned in [docs/binary-profile.md](docs/binary-profile.md).

Challenge sampling is executable: [BinarySampling.lean](ProximityPrize/Benchmark/BinarySampling.lean) uses CompPoly's word and coefficient maps with VCVio's uniform sampler transport. It draws three independent 64-bit limbs, with a proved uniform output measure. [BinaryCodegen.lean](ProximityPrize/Benchmark/BinaryCodegen.lean) checks compiler IR for the sampler and the Toy prover, verifier, and extractors specialized to the production profile.

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
./benchmark.sh binary-lower
./benchmark.sh binary-upper
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

```sh
python3 scripts/challenges.py slugs
```

`challenges.json` is the source of truth for all immutable versions. The binary slugs are `proximity-prize-binary-reduction-lower` and `proximity-prize-binary-reduction-upper`.

Version numbers are independent per slug and must be allocated against the independent verifier's served history. This migration selects Koala versions above the production history; dev `main` alone is insufficient to choose a fresh version. Existing Koala submissions need migration and fresh acceptance on Lean 4.34.0, including the leading proofs whose migration remains unresolved. See the [version policy and leaderboard migration requirements](docs/binary-profile.md#release-requirements) before registration.

The new binary profiles and the migrated Koala profiles must be registered with the independent verifier before their workflows can issue authoritative scores. Public repository routing alone does not register a service-side challenge.

## Development validation

```sh
./scripts/validate.sh
```

This builds all four protected targets and seeds, audits their transitive axioms, executes the binary Toy runtime checks, checks submission isolation and immutable-version routing, and runs the profile/score boundary regressions. It does not send submissions to the independent service. Run `./setup.sh` and the local Comparator benchmarks as an additional acceptance check before release.

To run only the binary runtime checks:

```sh
lake build ProximityPrize VCVio.OracleComp.RunIO
lake env lean --run scripts/BinaryToyRuntime.lean
```

These execute the production field and sampler with small code dimensions, testing honest proving, verifier acceptance/rejection, encoding/decoding, extraction, and the simplified reduction's virtual output. The production dimensions are checked for code generation; this command does not allocate or benchmark a 2^26-coordinate witness.

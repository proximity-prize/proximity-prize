/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.BinaryIRSProfile

/-!
# Lower challenge certificate for the ABF26 reduction threshold

The fixed extractor-error target is `2^(-128)`. The interface certifies one
admissible radius at which the executable IRS straight-line extractor's
combination-round error bound is at most that target, then scores the induced
spot-check error `(1 - δ)^t`, where `t = BinaryIRSProfile.repetitions = 128`.

This extractor certificate is the MCA-plus-list term from ABF26 Lemma 6.10. It
upper-bounds Definition 6.11's winning-set soundness, so the certificate also
establishes a conservative safe point for the exact combinatorial reduction
error; equality is not assumed.
-/

namespace ProximityPrize.Benchmark.Binary

open ToyProblem
open scoped NNReal

/-- Exact radius encoded in the trusted theorem type. -/
noncomputable def claimedRadius (numerator denominator : Nat) : ℝ≥0 :=
  (numerator : ℝ≥0) / (denominator : ℝ≥0)

/-- Error corresponding to a score in hundredths of a bit. -/
noncomputable def claimedError (centiBits : Nat) : ℝ≥0 :=
  (2 : ℝ≥0) ^ (-((centiBits : ℝ) / 100))

/-- The fixed ABF26 extractor-error target `2^(-128)`. -/
noncomputable def reductionTarget : ℝ≥0 :=
  (ProximityGap.prizeThreshold : ℝ≥0)

/-- A lower certificate for the ABF26 reduction threshold.

`reduction` bounds the executable IRS extractor's certified combination-round
error at one safe radius. This implies the corresponding Definition 6.11
winning-set bound. `score` converts that radius to the spot-check term
`(1 - δ)^t`. A larger `centiBits` value is stronger. -/
structure ProtocolClaim
    (centiBits radiusNumerator radiusDenominator : Nat) : Prop where
  admissible : claimedRadius radiusNumerator radiusDenominator ∈
    Set.Ioo (0 : ℝ≥0) BinaryIRSProfile.minRelativeDistance
  reduction :
    ToyProblem.Impl.IRS.certifiedGammaError BinaryIRSProfile.totalDimension
        BinaryIRSProfile.interleaving BinaryIRSProfile.domain
        (claimedRadius radiusNumerator radiusDenominator) ≤
      reductionTarget
  score :
    (1 - claimedRadius radiusNumerator radiusDenominator) ^
        BinaryIRSProfile.repetitions ≤
      claimedError centiBits

end ProximityPrize.Benchmark.Binary

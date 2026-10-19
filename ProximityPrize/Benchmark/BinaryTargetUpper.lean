/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.BinaryIRSProfile
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Set.PowersetCard

/-!
# Upper certificate for the ABF26 reduction threshold

The fixed winning-set target is `epsilonStar = 2^(-128)`. The interface
certifies an unsafe-from-here radius `δstar` for Definition 6.11's worst-case
winning-challenge density and is scored by the induced spot-check error
`(1 - δstar)^t`, where `t = BinaryIRSProfile.repetitions = 128`.

ABF26 identifies Definition 6.11's worst-case winning-set density with the
soundness error of the Construction 6.9 reduction. ArkLib formalizes that
density and its game-level upper coupling, but not the converse equality to the
minimal game error. The winning-set target and spot-check error remain separate
round-by-round quantities. The whole admissible suffix is certified because no
monotonicity theorem is assumed. This threshold certificate does not construct
an end-to-end attacking prover.
-/

namespace ProximityPrize.Benchmark.Binary.Upper

open ToyProblem
open scoped NNReal

/-- The fixed ABF26 winning-set target `2^(-128)`. -/
noncomputable def epsilonStar : ℝ≥0 :=
  (ProximityGap.prizeThreshold : ℝ≥0)

/-- The claimed unsafe radius is pinned to the code's meaningful `1/n` grid. -/
noncomputable def claimedUnsafeRadius (unsafeIndex : Nat) : ℝ≥0 :=
  ProximityGap.gridPt (ι := BinaryIRSProfile.Index) unsafeIndex

/-- An upper certificate for the ABF26 reduction threshold.

`unsafeAbove` certifies that Definition 6.11's winning-set quantity is above the
fixed target from `δstar` onward. `score` converts that radius to
`(1 - δstar)^t`. Smaller `centiBits` and `unsafeIndex` are stronger. -/
structure ProtocolClaimUpper (centiBits unsafeIndex : Nat) : Prop where
  admissible : claimedUnsafeRadius unsafeIndex ∈
    Set.Ioo (0 : ℝ≥0) BinaryIRSProfile.minRelativeDistance
  unsafeAbove : ∀ δ ∈ Set.Ico (claimedUnsafeRadius unsafeIndex)
      BinaryIRSProfile.minRelativeDistance,
    epsilonStar < winningSetDensity BinaryIRSProfile.encoder δ
  score :
    (2 : ℝ≥0) ^ (-((centiBits : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius unsafeIndex) ^ BinaryIRSProfile.repetitions

end ProximityPrize.Benchmark.Binary.Upper

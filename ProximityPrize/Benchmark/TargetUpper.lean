/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.IRSProfile
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Set.PowersetCard

/-!
# Upper attack certificate for the ABF26 reduction threshold

The fixed winning-set target is `epsilonStar = 2^(-128)`. The interface
certifies an attacked radius `δstar` for Definition 6.11's worst-case
winning-challenge density and is scored by the induced spot-check error
`(1 - δstar)^t`, where `t = IRSProfile.repetitions = 128`.

ABF26 identifies Definition 6.11's worst-case winning-set density with the
soundness error of the Construction 6.9 reduction. ArkLib formalizes that
density and its game-level upper coupling, but not the converse equality to the
minimal game error. The winning-set target and spot-check error remain separate
round-by-round quantities. This point certificate does not claim monotonicity,
locate a global safe/unsafe frontier, or construct an end-to-end attacking
prover.
-/

namespace ProximityPrize.Benchmark.Upper

open ToyProblem
open scoped NNReal

/-- The fixed ABF26 winning-set target `2^(-128)`. -/
noncomputable def epsilonStar : ℝ≥0 :=
  (ProximityGap.prizeThreshold : ℝ≥0)

/-- The claimed unsafe radius is pinned to the code's meaningful `1/n` grid. -/
noncomputable def claimedUnsafeRadius (unsafeIndex : Nat) : ℝ≥0 :=
  ProximityGap.gridPt (ι := IRSProfile.Index) unsafeIndex

/-- An upper attack certificate for the ABF26 reduction threshold.

`unsafeAt` certifies that Definition 6.11's winning-set quantity is above the
fixed target at `δstar`. `score` certifies a centibit upper bound on the induced
spot-check bits from `(1 - δstar)^t`. Smaller `centiBits` and `unsafeIndex` are
stronger. -/
structure ProtocolClaimUpper (centiBits unsafeIndex : Nat) : Prop where
  admissible : claimedUnsafeRadius unsafeIndex ∈
    Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance
  unsafeAt :
    epsilonStar < winningSetDensity IRSProfile.encoder
      (claimedUnsafeRadius unsafeIndex)
  score :
    (2 : ℝ≥0) ^ (-((centiBits : ℝ) / 100)) ≤
      (1 - claimedUnsafeRadius unsafeIndex) ^ IRSProfile.repetitions

end ProximityPrize.Benchmark.Upper

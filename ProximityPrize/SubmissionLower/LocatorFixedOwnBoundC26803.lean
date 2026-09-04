import ProximityPrize.SubmissionLower.LocatorHybridRealizeC26803

/-!
# C2 own-bound provider for the 68.03 row

Both halves of `OwnBoundC2` now use agreement `181363`: the padded half comes
from `LocatorFixed6803`, and the hybrid half from
`LocatorFixedHybridC26803`.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixedOwnBoundC26803

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN095 RCN130 RCN137 RCN140 RCN156 RCN159 RCN174 RCN198 RCN234 RCN238
  RCN243 RCN266 RCN275
open LocatorFactorAggregate LocatorHybridCostC2 LocatorFixed
  LocatorFixedHybridC26803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

theorem regular_factor_own_bound
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDhigh : D ≤ 17773574)
    (hS : P.s ≤ 29) (hY : P.ys ≤ 135) (hT : P.total ≤ 6676)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ : ResidualSupportData P Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (R : RegularIndex Q) (hreal : RealizationC2 D) :
    OwnBoundC2 (regularSeeds Q selected Gamma R).card
      (regularCumulativeFlag Q R) :=
  ⟨LocatorFixed6803.regular_factor_count D P hDlow hDhigh hS hY hT
      Q hQ hbox HQ selected Gamma u0 u1 hdegree hagreement hno R,
    fun hhyb ↦ regular_factor_count_hybridC2 D P hDlow hDhigh
      hS hY hT Q hQ hbox HQ selected Gamma u0 u1 hdegree hagreement hno
      R hhyb hreal⟩

end

end ProximityPrize.SubmissionLower.LocatorFixedOwnBoundC26803

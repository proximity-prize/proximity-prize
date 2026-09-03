import ProximityPrize.SubmissionLower.LocatorHybridRealizeC2

/-! Per-factor bounds on the fixed stage — C2 / 6786 row: padded always, the C2
hybrid one when the C2 branch applies (`3 ≤ p.all` and `p.all + 2 ≤ middle p`). -/

namespace ProximityPrize.SubmissionLower.LocatorFixedOwnBoundC2
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN174 RCN275 RCN238 RCN243 RCN266 RCN140 RCN130 RCN156 RCN234 RCN159 RCN137 RCN198 RCN095
open LocatorFactorAggregate LocatorHybridCostC2 LocatorFixed LocatorFixedHybridC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

/-- Both per-factor bounds: padded always, C2 hybrid when it applies. -/
theorem regular_factor_own_bound
    (D:ℕ) (P:ResidualSupportParameters)
    (hDlow:131072 ≤ D) (hDhigh:D ≤ 14885460)
    (hS:P.s ≤ 24) (hY:P.ys ≤ 113) (hT:P.total ≤ 3808)
    (Q:P4) (hQ:Q ≠ 0)
    (hbox:Q ∈ RCN174.globalCoefficientBox K D 131071 P.total P.s)
    (HQ:ResidualSupportData P Q)
    (selected:K → Polynomial K) (Gamma:Finset K) (u0 u1:I → K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181530 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80614)
    (R:RegularIndex Q) (hreal:RealizationC2 D) :
    OwnBoundC2 (regularSeeds Q selected Gamma R).card (regularCumulativeFlag Q R):=
  ⟨regular_factor_count D P hDlow hDhigh hS hY hT Q hQ hbox HQ selected Gamma u0 u1
      hdegree hagreement hno R,
    fun hhyb=> regular_factor_count_hybridC2 D P hDlow hDhigh hS hY hT Q hQ hbox HQ
      selected Gamma u0 u1 hdegree hagreement hno R hhyb hreal⟩
end
end ProximityPrize.SubmissionLower.LocatorFixedOwnBoundC2

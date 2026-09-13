import ProximityPrize.SubmissionLower.BoundaryTailCarrier6807
import ProximityPrize.SubmissionLower.BoundaryTailOrdinary6807

namespace ProximityPrize.SubmissionLower.BoundaryTailBase6807

open scoped Classical BigOperators
open MvPolynomial RCN135 RCN136 RCN319 RCN238 RCN243 RCN130 RCN234 RCN156
open RCN095 RCN174 RCN275 RCN327 RCN140 RCN266 RCN286
open LocatorHybridCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def Active (p : FlagDegree) : Prop :=
  BoundaryTailCarrier6807.Active p ∧ LocatorFactorAggregate.middle p ≤ 142 ∧
    LocatorFactorAggregate.total p ≤ 7501

instance (p : FlagDegree) : Decidable (Active p) := by
  unfold Active BoundaryTailCarrier6807.Active
  infer_instance

def cap (p : FlagDegree) : ℕ :=
  if Active p then min (BoundaryTailOrdinary6807.rawCost p) (BoundaryTailCarrier6807.ledgerCap p)
  else BoundaryTailOrdinary6807.rawCost p

theorem cap_le_raw (p : FlagDegree) : cap p ≤ BoundaryTailOrdinary6807.rawCost p := by
  unfold cap
  split_ifs
  · exact min_le_left _ _
  · rfl

section Benchmark
open ProximityPrize.Benchmark
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- The semantic base cap for every actual regular factor. Ordinary counting,
profile interpolation, retained geometry and exceptional events are supplied
by proved construction theorems, not assumptions on an external provider. -/
theorem regular_factor_count
    (D : ℕ) (P : ResidualSupportParameters)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hS : P.s ≤ 31) (hY : P.ys ≤ 146) (hT : P.total ≤ 7784)
    (Q : P4) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D 131071 P.total P.s)
    (HQ : ResidualSupportData P Q)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181324 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i+gamma*u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80820)
    (R : RegularIndex Q) :
    (regularSeeds Q selected Gamma R).card ≤ cap (regularCumulativeFlag Q R) := by
  have hold := BoundaryTailOrdinary6807.regular_factor_count_raw D P hDlow hDchar
    hS hY hT Q hQ hbox HQ selected Gamma u0 u1 hdegree hagreement hno R
  unfold cap
  split_ifs with ha
  · apply le_min hold
    have hRdata := directFactor_data Q R.1 hQ D 131071 P.total P.s hbox R.2
    have hRsupport := BoundaryTailOrdinary6807.factor_support Q hQ HQ R
    have hsub := regularSeeds_subset Q selected Gamma R
    have hcum := originalCumulativeFlag_cumulative R.1
    have hsmallT : wt residualTotalWeights R.1 ≤ 7501 := by
      simpa only [regularCumulativeFlag, LocatorFactorAggregate.total, hcum.2.2] using ha.2.2
    have hsmallY : wt residualYSWeights R.1 ≤ 142 := by
      simpa only [regularCumulativeFlag, LocatorFactorAggregate.middle, hcum.2.1] using ha.2.1
    exact BoundaryTailCarrier6807.carrier_count_le_ledger (nodes := IRSProfile.domain) (u0 := u0) (u1 := u1)
      D P.total P.s R.1 hDlow hDchar hRdata.1 hRdata.2.1 hRdata.2.2
      hsmallT hsmallY
      (hRsupport.s_weight.trans hS)
      selected (regularSeeds Q selected Gamma R)
      (fun gamma hg => hdegree gamma (hsub hg))
      (fun gamma hg => hagreement gamma (hsub hg))
      (fun gamma hg => (Finset.mem_filter.mp hg).2.1)
      (fun gamma hg => (Finset.mem_filter.mp hg).2.2)
      (noLargeSelectedPencil_mono selected Gamma _ 131071 80820 hsub hno)
      (by norm_num [I, IRSProfile.Index]) ha.1
  · exact hold

end Benchmark
end
end ProximityPrize.SubmissionLower.BoundaryTailBase6807

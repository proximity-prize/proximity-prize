import ProximityPrize.SubmissionLower.LocatorGenericSourceCount6783
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
import ProximityPrize.SubmissionLower.LocatorSourceCGap

namespace ProximityPrize.SubmissionLower.LocatorGenericSourceRoutes6783

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN130 RCN140 RCN180 RCN238 RCN266
open LocatorGenericSourceCountEngine LocatorReplacementGridData

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

private theorem sourceA_gap (u0 u1 : I → K) :
    44259914061 ≤ Module.finrank K
      (SourceKernel 12709130 130000 21 70 u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    12709130 131071 130000 21 70 IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact LocatorArithmetic.kernelA_nullity ▸ hlo'

private theorem sourceAux_gap (u0 u1 : I → K) :
    350071455602 ≤ Module.finrank K
      (SourceKernel 13072248 130000 21 72 u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    13072248 131071 130000 21 72 IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact LocatorAuxiliaryArithmetic.auxiliary72_nullity ▸ hlo'

theorem sourceA_count
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181559 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80585)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : SourceKernel 12709130 130000 21 70 u0 u1,
      F.1 ∣ reconstruct K 12709130 131071 130000 21 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceA 1 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceA (box c) 1 := by
  have hcapacity : ∀ j, 1 ≤ j → j ≤ 1 →
      12709130 - j * 50489 ≤
        (70 - j) * 181559 + j * (131071 - 1) := by
    intro j hj hj1
    have : j = 1 := by omega
    subst j
    decide
  have hlowpos : ∀ j, 1 ≤ j → j ≤ 1 →
      0 < 12709130 - j * 50489 := by
    intro j hj hj1
    have : j = 1 := by omega
    subst j
    decide
  have hgap : sourceA.gap ≤ Module.finrank K
      (SourceKernel 12709130 130000 21 70 u0 u1) := by
    simpa only [sourceA, SourceKernel] using sourceA_gap u0 u1
  exact source_count_of_divisor 12709130 130000 21 70 96 50489 1 sourceA
    rfl rfl rfl rfl (by decide) (by decide) hcapacity hlowpos
    u0 u1 H selected Gamma hdegree hagreement hno F hF hdiv hgap
    c hcell hfit

theorem sourceAux_count
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181559 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80585)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : SourceKernel 13072248 130000 21 72 u0 u1,
      F.1 ∣ reconstruct K 13072248 131071 130000 21 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceAux 1 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceAux (box c) 1 := by
  have hcapacity : ∀ j, 1 ≤ j → j ≤ 1 →
      13072248 - j * 50489 ≤
        (72 - j) * 181559 + j * (131071 - 1) := by
    intro j hj hj1
    have : j = 1 := by omega
    subst j
    exact LocatorAuxiliaryArithmetic.auxiliary72_capacity
  have hlowpos : ∀ j, 1 ≤ j → j ≤ 1 →
      0 < 13072248 - j * 50489 := by
    intro j hj hj1
    have : j = 1 := by omega
    subst j
    decide
  have hgap : sourceAux.gap ≤ Module.finrank K
      (SourceKernel 13072248 130000 21 72 u0 u1) := by
    simpa only [sourceAux, SourceKernel] using sourceAux_gap u0 u1
  exact source_count_of_divisor 13072248 130000 21 72 99 50489 1 sourceAux
    rfl rfl rfl rfl (by decide) LocatorAuxiliaryArithmetic.auxiliary72_shape
    hcapacity hlowpos u0 u1 H selected Gamma hdegree hagreement hno F hF
    hdiv hgap c hcell hfit

theorem sourceC_count
    (k : ℕ) (hk9 : k ≤ 9)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181559 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80585)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : SourceKernel 51744315 130000 85 285 u0 u1,
      F.1 ∣ reconstruct K 51744315 131071 130000 85 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceC k (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) k := by
  have hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      51744315 - j * 50489 ≤
        (285 - j) * 181559 + j * (131071 - 1) := by
    intro j _hj hjk
    exact LocatorAuxiliaryArithmetic.auxiliary176_stage_capacity j
      (hjk.trans (hk9.trans (by decide)))
  have hlowpos : ∀ j, 1 ≤ j → j ≤ k →
      0 < 51744315 - j * 50489 := by
    intro j _hj hjk
    have := hjk.trans hk9
    omega
  have hgap : sourceC.gap ≤ Module.finrank K
      (SourceKernel 51744315 130000 85 285 u0 u1) := by
    simpa only [sourceC, SourceKernel] using
      LocatorSourceCGap.finrank_lower_bound u0 u1
  exact source_count_of_divisor 51744315 130000 85 285 394 50489 k sourceC
    rfl rfl rfl rfl (by decide) LocatorAuxiliaryArithmetic.auxiliary176_shape
    hcapacity hlowpos u0 u1 H selected Gamma hdegree hagreement hno F hF
    hdiv hgap c hcell hfit

end

end ProximityPrize.SubmissionLower.LocatorGenericSourceRoutes6783

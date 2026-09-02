import ProximityPrize.SubmissionLower.LocatorGenericSourceCount6784
import ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
import ProximityPrize.SubmissionLower.LocatorSourceCGap

namespace ProximityPrize.SubmissionLower.LocatorGenericSourceRoutes6784

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

private theorem kernel_gap
    (D L s m value : ℕ)
    (hvalue : coefficientCount D 131071 L s -
      262144 * localRankBound m L s = value)
    (u0 u1 : I → K) : value ≤ Module.finrank K
      (SourceKernel D L s m u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    D 131071 L s m IRSProfile.domain u0 u1
  exact hvalue ▸ (hcard ▸ hlo)

theorem sourceA_count
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181550 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80594)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : SourceKernel 13071600 130000 21 72 u0 u1,
      F.1 ∣ reconstruct K 13071600 131071 130000 21 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceA 1 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceA (box c) 1 := by
  have hgap : sourceA.gap ≤ Module.finrank K
      (SourceKernel 13071600 130000 21 72 u0 u1) := by
    simpa only [sourceA, SourceKernel] using
      kernel_gap 13071600 130000 21 72 184271188970
        LocatorArithmetic.kernelA_nullity u0 u1
  have hcapacity : ∀ j, 1 ≤ j → j ≤ 1 →
      13071600 - j * 50480 ≤ (72 - j) * 181550 + j * 131070 := by
    intro j hj hj1
    have : j = 1 := by omega
    subst j
    decide
  have hlowpos : ∀ j, 1 ≤ j → j ≤ 1 →
      0 < 13071600 - j * 50480 := by
    intro j hj hj1
    have : j = 1 := by omega
    subst j
    decide
  exact source_count_of_divisor 13071600 130000 21 72 99 50480 1 sourceA
    rfl rfl rfl rfl (by decide) (by decide) hcapacity hlowpos
    u0 u1 H selected Gamma hdegree hagreement hno F hF hdiv hgap c hcell hfit

theorem sourceAux_count
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181550 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80594)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : SourceKernel 13253150 130000 22 73 u0 u1,
      F.1 ∣ reconstruct K 13253150 131071 130000 22 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceAux 1 (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceAux (box c) 1 := by
  have hgap : sourceAux.gap ≤ Module.finrank K
      (SourceKernel 13253150 130000 22 73 u0 u1) := by
    simpa only [sourceAux, SourceKernel] using
      kernel_gap 13253150 130000 22 73 441366390587
        LocatorAuxiliaryArithmetic.auxiliary72_nullity u0 u1
  have hcapacity : ∀ j, 1 ≤ j → j ≤ 1 →
      13253150 - j * 50480 ≤ (73 - j) * 181550 + j * 131070 := by
    intro j hj hj1
    have : j = 1 := by omega
    subst j
    exact LocatorAuxiliaryArithmetic.auxiliary72_capacity
  have hlowpos : ∀ j, 1 ≤ j → j ≤ 1 →
      0 < 13253150 - j * 50480 := by
    intro j hj hj1
    have : j = 1 := by omega
    subst j
    decide
  exact source_count_of_divisor 13253150 130000 22 73 101 50480 1 sourceAux
    rfl rfl rfl rfl (by decide) LocatorAuxiliaryArithmetic.auxiliary72_shape
    hcapacity hlowpos u0 u1 H selected Gamma hdegree hagreement hno F hF
    hdiv hgap c hcell hfit

theorem sourceC_count
    (k : ℕ) (hk14 : k ≤ 14)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181550 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80594)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : SourceKernel 51741750 130000 85 285 u0 u1,
      F.1 ∣ reconstruct K 51741750 131071 130000 85 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits sourceC k (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost sourceC (box c) k := by
  have hgap : sourceC.gap ≤ Module.finrank K
      (SourceKernel 51741750 130000 85 285 u0 u1) := by
    simpa only [sourceC, SourceKernel] using
      LocatorSourceCGap.finrank_lower_bound u0 u1
  have hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      51741750 - j * 50480 ≤ (285 - j) * 181550 + j * 131070 := by
    intro j _ hjk
    exact LocatorAuxiliaryArithmetic.auxiliary176_stage_capacity j
      (hjk.trans (hk14.trans (by decide)))
  have hlowpos : ∀ j, 1 ≤ j → j ≤ k →
      0 < 51741750 - j * 50480 := by
    intro j _ hjk
    have := hjk.trans hk14
    omega
  exact source_count_of_divisor 51741750 130000 85 285 394 50480 k sourceC
    rfl rfl rfl rfl (by decide) LocatorAuxiliaryArithmetic.auxiliary176_shape
    hcapacity hlowpos u0 u1 H selected Gamma hdegree hagreement hno F hF
    hdiv hgap c hcell hfit

private theorem routeDepthAux_bounds_local (src : Source) (b : Box) (n : ℕ) :
    ∀ k, routeDepthAux src b k n ≠ 0 →
      k ≤ routeDepthAux src b k n ∧ routeDepthAux src b k n < k + n := by
  induction n with
  | zero =>
      intro k h
      simp only [routeDepthAux, ne_eq, not_true_eq_false] at h
  | succ n ih =>
      intro k h
      simp only [routeDepthAux] at h ⊢
      by_cases hterm : terminalCoprime src b k
      · rw [if_pos hterm] at h ⊢
        by_cases hfit : FastRouteFits src k b
        · rw [if_pos hfit]
          omega
        · rw [if_neg hfit] at h
          exact absurd rfl h
      · rw [if_neg hterm] at h ⊢
        have hb := ih (k + 1) h
        omega

theorem routeDepth_le_fourteen (src : Source) (b : Box)
    (h : routeDepth src b ≠ 0) : routeDepth src b ≤ 14 := by
  have hb := routeDepthAux_bounds_local src b routeCap 1 h
  change routeDepthAux src b 1 routeCap ≤ 14
  have hcap : routeCap = 14 := rfl
  omega

end

end ProximityPrize.SubmissionLower.LocatorGenericSourceRoutes6784

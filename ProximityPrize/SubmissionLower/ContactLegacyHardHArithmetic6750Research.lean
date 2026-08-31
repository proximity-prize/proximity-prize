import ProximityPrize.SubmissionLower.ContactLegacyDirectArithmetic6750Research
import ProximityPrize.SubmissionLower.ContactLegacyNonbasicArithmetic6750Research

namespace ProximityPrize.SubmissionLower.ContactLegacyHardHArithmetic6750Research

open ProximityPrize.Benchmark
open ContactFactorCaps
open ContactKernelCommonGCD6750Research
open ContactResidualSupportParametersResearch
open ContactTwoTailParameters6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactRouterCellCosts6750Research
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHardCellSelector6750Research
open ContactOrdinaryHardShell6750Research
open ContactSelectedCount6750Research
open ContactSelectedOldCoreLowQuotients6750Research
open ContactLegacyTwoFactorEasy6750Research
open ContactPureTotalQuotientOrdinary6750Research
open ContactLegacyOldGCountProvider6750Research
open ContactLegacyDirectArithmetic6750Research
open ContactLegacyNonbasicArithmetic6750Research
open ContactTightSingularLedgerResearch
open ContactCanonicalHighSourceAnchoredCap6750Research

set_option autoImplicit false
set_option maxHeartbeats 50000000
set_option maxRecDepth 50000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

def hardQuotientD (y r : Nat) : Nat :=
  max 131072 (8729952 - (131071 * y - r))
def hardPureZeroCost (y r : Nat) : Nat :=
  cellRegularCost 3 3 2 +
    (cellTightProfile (hardQuotientD y r) 3 2).countCap
def hardPurePositiveBoundaryCost (y r : Nat) : Nat :=
  (cellTightProfile (hardQuotientD y r) (1699 - hardMinT y r) 1).countCap

theorem hardQuotientD_bound
    {u₀ u₁ : I → K} (S : SelectedInterpolants6750 u₀ u₁)
    (F : CanonicalOldCoreFactorization S) :
    factorD F.Q ≤ hardQuotientD
      (factorYS (canonicalOldCoreH S)) (factorS (canonicalOldCoreH S)) := by
  let H := canonicalOldCoreH S
  let y := factorYS H
  let r := factorS H
  have hrel := residualYS_mul_le_contact_add_slope H w (by norm_num [w])
  change w * y ≤ factorContact H + r at hrel
  norm_num [w] at hrel
  have hc := oldCommonCore_contact_le S
  have hadd := F.contact_add
  change factorContact (oldCommonCore S) =
    factorContact H + factorContact F.Q at hadd
  have hrem : 131071 * y - r ≤ factorContact H := by
    omega
  have hq : factorContact F.Q + 1 ≤ 8729952 - (131071 * y - r) := by
    change factorContact (oldCommonCore S) ≤ 8729951 at hc
    omega
  change max (w + 1) (factorContact F.Q + 1) ≤
    max 131072 (8729952 - (131071 * y - r))
  rw [show w + 1 = 131072 by norm_num [w]]
  apply max_le
  · exact Nat.le_max_left _ _
  · exact hq.trans (Nat.le_max_right _ _)

theorem hardPureAndThirdBoundaryReceipt :
    ∀ (y : Fin 67) (r : Fin 15),
      OrdinaryHardCell (hardMinT y.1 r.1) y.1 r.1 →
      hardPureZeroCost y.1 r.1 ≤
          ContactRouterUniformCaps6750Research.hardThirdCap ∧
        hardPurePositiveBoundaryCost y.1 r.1 ≤
          ContactRouterUniformCaps6750Research.hardThirdCap ∧
        nonBasicThirdCost (hardMinT y.1 r.1) y.1 r.1 ≤
          ContactRouterUniformCaps6750Research.hardThirdCap := by
  unfold OrdinaryHardCell
  decide

theorem factorEquationCost_pure_zero_le
    {u₀ u₁ : I → K} (S : SelectedInterpolants6750 u₀ u₁)
    (F : CanonicalOldCoreFactorization S)
    (hy : factorYS F.Q = 0) (hr : factorS F.Q = 0)
    (ht : factorTotal F.Q = 0) :
    factorEquationCost F.Q ≤ hardPureZeroCost
      (factorYS (canonicalOldCoreH S)) (factorS (canonicalOldCoreH S)) := by
  have hD := hardQuotientD_bound S F
  have hmono := tightCount_mono_D (t := 3) (r := 2) hD
  have hR : factorPaddedR F.Q = 2 := by
    simp only [factorPaddedR, hr]
    decide
  have hY : factorPaddedY F.Q = 3 := by
    simp only [factorPaddedY, hR, hy]
    decide
  have hT : factorPaddedT F.Q = 3 := by
    simp only [factorPaddedT, hY, ht]
    decide
  unfold factorEquationCost hardPureZeroCost
  rw [hR, hY, hT]
  exact Nat.add_le_add_left hmono (cellRegularCost 3 3 2)

theorem factorRFreeCost_pure_positive_le
    {u₀ u₁ : I → K} (S : SelectedInterpolants6750 u₀ u₁)
    (F : CanonicalOldCoreFactorization S)
    (gcell : OrdinaryHardCell (oldCoreTotal S) (oldCoreYS S) (oldCoreS S))
    (hcell : OrdinaryHardCell
      (factorTotal (canonicalOldCoreH S))
      (factorYS (canonicalOldCoreH S))
      (factorS (canonicalOldCoreH S)))
    (ht : factorTotal F.Q ≠ 0) :
    factorRFreeCost F.Q ≤ hardPurePositiveBoundaryCost
      (factorYS (canonicalOldCoreH S)) (factorS (canonicalOldCoreH S)) := by
  let t := factorTotal (canonicalOldCoreH S)
  let y := factorYS (canonicalOldCoreH S)
  let r := factorS (canonicalOldCoreH S)
  have hqpos : 1 ≤ factorTotal F.Q := Nat.one_le_iff_ne_zero.mpr ht
  have hqt : factorTotal F.Q ≤ 1699 - t := by
    have hadd := F.total_add
    have htop := gcell.2.2.2.2.2
    omega
  have htmin := hcell.2.2.2.2.1
  have hD := hardQuotientD_bound S F
  have hDmono := tightCount_mono_D
    (t := factorTotal F.Q) (r := 1) hD
  have htmono :=
    ContactCanonicalHighSourceAnchoredCap6750Research.tightCount_mono_total
      (D := hardQuotientD y r) (r := 1)
      (hqt.trans (Nat.sub_le_sub_left htmin 1699))
  unfold factorRFreeCost hardPurePositiveBoundaryCost
  simp only [max_eq_right hqpos]
  exact hDmono.trans htmono

theorem canonicalNonzeroCost_le_hardThirdCap
    {u₀ u₁ : I → K} (S : SelectedInterpolants6750 u₀ u₁)
    (F : CanonicalOldCoreFactorization S)
    (gcell : OrdinaryHardCell (oldCoreTotal S) (oldCoreYS S) (oldCoreS S))
    (hcell : OrdinaryHardCell
      (factorTotal (canonicalOldCoreH S))
      (factorYS (canonicalOldCoreH S))
      (factorS (canonicalOldCoreH S))) :
    canonicalNonzeroCost6750 S F ≤
      ContactRouterUniformCaps6750Research.hardThirdCap := by
  let t := factorTotal (canonicalOldCoreH S)
  let y := factorYS (canonicalOldCoreH S)
  let r := factorS (canonicalOldCoreH S)
  have hboundary : OrdinaryHardCell (hardMinT y r) y r :=
    ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
      Nat.le_refl _, hcell.2.2.2.2.1.trans hcell.2.2.2.2.2⟩
  have hreceipt := hardPureAndThirdBoundaryReceipt
    ⟨y, Nat.lt_succ_iff.mpr hcell.2.1⟩
    ⟨r, Nat.lt_succ_iff.mpr hcell.2.2.2.1⟩ hboundary
  have hreceipt' : hardPureZeroCost y r ≤
        ContactRouterUniformCaps6750Research.hardThirdCap ∧
      hardPurePositiveBoundaryCost y r ≤
        ContactRouterUniformCaps6750Research.hardThirdCap ∧
      nonBasicThirdCost (hardMinT y r) y r ≤
        ContactRouterUniformCaps6750Research.hardThirdCap := by
    simpa using hreceipt
  by_cases hpure : factorYS F.Q = 0 ∧ factorS F.Q = 0
  · by_cases htotal : factorTotal F.Q = 0
    · rw [canonicalNonzeroCost6750, if_pos hpure, if_pos htotal]
      exact (factorEquationCost_pure_zero_le S F hpure.1 hpure.2 htotal).trans
        hreceipt'.1
    · rw [canonicalNonzeroCost6750, if_pos hpure, if_neg htotal]
      exact (factorRFreeCost_pure_positive_le S F gcell hcell htotal).trans
        hreceipt'.2.1
  · rw [canonicalNonzeroCost6750, if_neg hpure]
    have hthird := nonBasicThirdCost_antitone_total
      (y := y) (r := r) hcell.2.2.2.2.1
    simpa only [canonicalThirdCost6750, nonBasicThirdCost, t, y, r,
      factorTotal, factorYS, factorS] using hthird.trans hreceipt'.2.2

private theorem shellAnchoredReceipt :
    ∀ (y : Fin 67) (r : Fin 15),
      OrdinaryHardCell 1699 y.1 r.1 →
      r.1 ≤ hardLastR1658 y.1 →
      canonicalAnchoredCost 1699 y.1 r.1 ≤
        ContactRouterUniformCaps6750Research.hardAnchoredCap := by
  unfold OrdinaryHardCell
  decide

theorem OrdinaryHardCell.canonicalAnchoredCost_le_hardAnchoredCap
    {t y r : Nat} (cell : OrdinaryHardCell t y r) :
    canonicalAnchoredCost t y r ≤
      ContactRouterUniformCaps6750Research.hardAnchoredCap := by
  rcases cell.hard_or_firstDerivativeShell with hhard | ⟨ht, hr⟩
  · exact
      ContactCanonicalHighSourceAnchoredCap6750Research.HardCell.canonicalAnchoredCost_le_hardAnchoredCap
        hhard
  · subst t
    exact shellAnchoredReceipt ⟨y, Nat.lt_succ_iff.mpr cell.2.1⟩
      ⟨r, Nat.lt_succ_iff.mpr cell.2.2.2.1⟩ cell hr

end ProximityPrize.SubmissionLower.ContactLegacyHardHArithmetic6750Research

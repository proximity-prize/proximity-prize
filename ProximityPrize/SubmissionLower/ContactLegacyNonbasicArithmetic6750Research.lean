import ProximityPrize.SubmissionLower.ContactOrdinaryHardShell6750Research
import ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research
import ProximityPrize.SubmissionLower.ContactMovingProtocol6750Research
import ProximityPrize.SubmissionLower.ContactLegacyMonotonicity6751Research
import ProximityPrize.SubmissionLower.ContactAnchoredThirdResidual6750Research
import ProximityPrize.SubmissionLower.ContactUpstreamTAnalytic6750Research

namespace ProximityPrize.SubmissionLower.ContactLegacyNonbasicArithmetic6750Research

open ContactTwoTailParameters6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactRouterCellCosts6750Research
open ContactRecursiveResidualStages6656Research
open ContactTightSingularLedgerResearch
open ContactOrdinaryHardShell6750Research
open ContactAnchoredHardCellSelector6750Research

set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 200000

def nonBasicD : Nat := 8598882
def nonBasicPaddedR (r : Nat) : Nat := max 2 r
def nonBasicPaddedY (y r : Nat) : Nat := max (nonBasicPaddedR r + 1) y
def nonBasicPaddedT (t y r : Nat) : Nat := max (nonBasicPaddedY y r) t
def nonBasicEquationCost (t y r : Nat) : Nat :=
  cellRegularCost (nonBasicPaddedT t y r) (nonBasicPaddedY y r)
      (nonBasicPaddedR r) +
    (cellTightProfile nonBasicD (nonBasicPaddedT t y r)
      (nonBasicPaddedR r)).countCap
def nonBasicThirdCost (t y r : Nat) : Nat :=
  (ContactAnchoredThirdResidual6750Research.thirdStage t y r).regularCountCap +
    (ContactAnchoredThirdResidual6750Research.thirdPivot t r).countCap

def nonBasicEquationCap : Nat := 71010384918972586
def nonBasicThirdCap : Nat := 208776440890990

theorem nonBasicEquationCost_mono_total
    {t₁ t₂ y r : Nat} (h : t₁ ≤ t₂) :
    nonBasicEquationCost t₁ y r ≤ nonBasicEquationCost t₂ y r := by
  have hp : nonBasicPaddedT t₁ y r ≤ nonBasicPaddedT t₂ y r :=
    max_le_max_left (nonBasicPaddedY y r) h
  unfold nonBasicEquationCost
  exact Nat.add_le_add
    (ContactLegacyMonotonicity6751Research.cellRegularCost_mono_total hp)
    (ContactLegacyMonotonicity6751Research.tightCount_mono_total hp)

theorem nonBasicThirdCost_antitone_total
    {t₁ t₂ y r : Nat} (h : t₁ ≤ t₂) :
    nonBasicThirdCost t₂ y r ≤ nonBasicThirdCost t₁ y r := by
  unfold nonBasicThirdCost ContactAnchoredThirdResidual6750Research.thirdStage
    ContactAnchoredThirdResidual6750Research.thirdPivot
  simp only [UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, UnequalParameters.errors,
    UnequalParameters.gap, TightParameters.countCap,
    TightParameters.tightNumerator, TightParameters.coreNumerator,
    TightParameters.agreement, TightParameters.aggregateCost,
    TightParameters.implicitYCap, TightParameters.algebraicCap,
    TightParameters.kappa, TightParameters.errors, TightParameters.gap,
    ContactSingularLedger6600Research.dot,
    ContactAnchoredThirdResidual6750Research.n,
    ContactAnchoredThirdResidual6750Research.w,
    ContactAnchoredThirdResidual6750Research.agreements]
  gcongr

theorem ordinaryHardUpstreamBoundaryReceipt :
    ∀ (y : Fin 66) (r : Fin 15),
      OrdinaryHardCell (hardMinT y.1 r.1) y.1 r.1 →
      upstreamCellCost (hardMinT y.1 r.1) y.1 r.1 ≤
        ContactRouterUniformCaps6750Research.upstreamCap := by
  unfold OrdinaryHardCell
  decide

theorem nonBasicEquationReceipt : ∀ (y : Fin 66) (r : Fin 15),
    r.1 ≤ y.1 → (r.1 < 2 ∨ y.1 ≤ r.1) →
    nonBasicEquationCost 1692 y.1 r.1 ≤ nonBasicEquationCap := by
  decide

theorem nonBasicThirdReceipt : ∀ (y : Fin 66) (r : Fin 15),
    r.1 ≤ y.1 → (r.1 < 2 ∨ y.1 ≤ r.1) →
    nonBasicThirdCost y.1 y.1 r.1 ≤ nonBasicThirdCap := by
  decide

theorem nonBasicLocalCost_le_budget
    {gt gy gr ht hy hr : Nat}
    (gcell : OrdinaryHardCell gt gy gr)
    (hrhy : hr ≤ hy) (hyht : hy ≤ ht)
    (hht : ht ≤ 1692) (hhy : hy ≤ 65) (hhr : hr ≤ 14)
    (hdeg : hr < 2 ∨ hy ≤ hr) :
    upstreamCellCost gt gy gr + nonBasicEquationCost ht hy hr +
        nonBasicThirdCost ht hy hr ≤
      ContactMovingProtocol6750Research.mcaBudget := by
  have hup0 := ContactUpstreamTAnalytic6750Research.upstreamCellCost_antitone_total
    (y := gy) (r := gr) gcell.2.2.2.2.1
  have hup1 := ordinaryHardUpstreamBoundaryReceipt
    ⟨gy, Nat.lt_succ_iff.mpr gcell.2.1⟩
    ⟨gr, Nat.lt_succ_iff.mpr gcell.2.2.2.1⟩
    ⟨gcell.1, gcell.2.1, gcell.2.2.1, gcell.2.2.2.1,
      Nat.le_refl _, gcell.2.2.2.2.1.trans gcell.2.2.2.2.2⟩
  have hup1' : upstreamCellCost (hardMinT gy gr) gy gr ≤
      ContactRouterUniformCaps6750Research.upstreamCap := by
    simpa using hup1
  have he0 := nonBasicEquationCost_mono_total (y := hy) (r := hr) hht
  have he1 := nonBasicEquationReceipt ⟨hy, by omega⟩ ⟨hr, by omega⟩
    hrhy hdeg
  have he1' : nonBasicEquationCost 1692 hy hr ≤ nonBasicEquationCap := by
    simpa using he1
  have h3₀ := nonBasicThirdCost_antitone_total (y := hy) (r := hr) hyht
  have h3₁ := nonBasicThirdReceipt ⟨hy, by omega⟩ ⟨hr, by omega⟩
    hrhy hdeg
  have h3₁' : nonBasicThirdCost hy hy hr ≤ nonBasicThirdCap := by
    simpa using h3₁
  have hsum : ContactRouterUniformCaps6750Research.upstreamCap +
      nonBasicEquationCap + nonBasicThirdCap ≤
        ContactMovingProtocol6750Research.mcaBudget := by
    decide
  omega

end ProximityPrize.SubmissionLower.ContactLegacyNonbasicArithmetic6750Research

#print axioms ProximityPrize.SubmissionLower.ContactLegacyNonbasicArithmetic6750Research.nonBasicLocalCost_le_budget

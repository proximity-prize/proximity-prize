import ProximityPrize.SubmissionLower.ContactLegacyPureBandReceipt6750Research
import ProximityPrize.SubmissionLower.ContactUpstreamTAnalytic6750Research

namespace ProximityPrize.SubmissionLower.ContactLegacyAdaptiveBasic6750Research

open ContactAnchoredHardCellSelector6750Research
open ContactAnchoredOneFamilySelector6750Research
open ContactOrdinaryHardShell6750Research
open ContactAnchoredThirdResidual6750Research
open ContactRecursiveResidualStages6656Research
open ContactTightSingularLedgerResearch
open ContactRouterCellCosts6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactLegacyPureBandReceipt6750Research

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 400000

def thirdCost (t y r : Nat) : Nat :=
  (thirdStage t y r).regularCountCap + (thirdPivot t r).countCap

def upstreamRMax (t y hr : Nat) : Nat :=
  (Finset.range 15).sup fun gr =>
    if hr ≤ gr then upstreamCellCost t (y + 1) gr else 0

def aCost (t y r : Nat) : Nat := upstreamRMax t y r + thirdCost t y r
def bCost (t y r : Nat) : Nat := coordinateCost 8417478 t y r

def hostilePair (y r : Nat) : Prop :=
  38 ≤ y ∧ y ≤ 65 ∧ hostileMinR y ≤ r ∧ r ≤ 14

def easyTop (y r : Nat) : Nat :=
  if 38 ≤ y ∧ y ≤ 65 ∧ hostileMinR y ≤ r ∧ r ≤ 14 then
    hardMinT y r - 1 else 1659

def tailMid (y r : Nat) : Nat := easyTop y r - 5
def tailCap (y r : Nat) : Nat :=
  max (aCost (y + 1) y r + bCost (tailMid y r) y r)
    (aCost (tailMid y r + 1) y r + bCost (easyTop y r) y r)

private theorem tailReceipt : ∀ (y : Fin 65) (r : Fin 15),
    hostilePair y.1 r.1 →
    tailCap y.1 r.1 ≤ ContactMovingSeedless6750Research.mcaBudget := by
  unfold hostilePair
  decide

def nonHostileMaxY (r : Nat) : Nat :=
  match r with
  | 8 => 59 | 9 => 53 | 10 => 48 | 11 => 44
  | 12 => 41 | 13 => 39 | 14 => 37 | _ => 64

def nonHostileCap (r : Nat) : Nat :=
  aCost (r + 2) (r + 1) r + bCost 1659 (nonHostileMaxY r) r

private theorem nonHostileReceipt : ∀ r : Fin 15, 2 ≤ r.1 →
    nonHostileCap r.1 ≤ ContactMovingSeedless6750Research.mcaBudget := by
  decide

private theorem nonHostileBReceipt : ∀ (y : Fin 65) (r : Fin 15),
    2 ≤ r.1 → r.1 < y.1 → ¬ hostilePair y.1 r.1 →
    bCost 1659 y.1 r.1 ≤ bCost 1659 (nonHostileMaxY r.1) r.1 := by
  unfold hostilePair
  decide

theorem upstreamCellCost_antitone_y {t y1 y2 r : Nat} (hy : y1 ≤ y2) :
    upstreamCellCost t y2 r ≤ upstreamCellCost t y1 r := by
  unfold upstreamCellCost residualCost6750 firstStage secondStage
    firstPivot secondPivot
  simp only [UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator, UnequalParameters.agreement,
    UnequalParameters.leftAgreement, UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost, UnequalParameters.errors,
    UnequalParameters.gap, TightParameters.countCap,
    TightParameters.tightNumerator, TightParameters.coreNumerator,
    TightParameters.agreement, TightParameters.aggregateCost,
    TightParameters.implicitYCap, TightParameters.algebraicCap,
    TightParameters.kappa, TightParameters.errors, TightParameters.gap,
    ContactSingularLedger6600Research.dot]
  gcongr <;> omega

theorem upstreamCellCost_le_upstreamRMax
    {gt gy gr ht hy hr : Nat} (hgt : ht ≤ gt) (hgy : hy + 1 ≤ gy)
    (hgr : hr ≤ gr) (hgrTop : gr ≤ 14) :
    upstreamCellCost gt gy gr ≤ upstreamRMax ht hy hr := by
  have htmono := ContactUpstreamTAnalytic6750Research.upstreamCellCost_antitone_total
    (y := gy) (r := gr) hgt
  have hy' := upstreamCellCost_antitone_y (t := ht) (r := gr) hgy
  have hs : upstreamCellCost ht (hy + 1) gr ≤ upstreamRMax ht hy hr := by
    unfold upstreamRMax
    simpa only [if_pos hgr] using
      (Finset.le_sup
        (s := Finset.range 15)
        (f := fun gr => if hr ≤ gr then
          upstreamCellCost ht (hy + 1) gr else 0)
        (Finset.mem_range.mpr (by omega : gr < 15)))
  exact htmono.trans (hy'.trans hs)

private theorem aCost_antitone_total {t1 t2 y r : Nat} (ht : t1 ≤ t2) :
    aCost t2 y r ≤ aCost t1 y r := by
  have hu : upstreamRMax t2 y r ≤ upstreamRMax t1 y r := by
    unfold upstreamRMax
    apply Finset.sup_le
    intro gr hmem
    by_cases hrg : r ≤ gr
    · simp only [if_pos hrg]
      exact (ContactUpstreamTAnalytic6750Research.upstreamCellCost_antitone_total
        (y := y + 1) (r := gr) ht).trans (by
          simpa only [if_pos hrg] using
            (Finset.le_sup
              (s := Finset.range 15)
              (f := fun gr => if r ≤ gr then
                upstreamCellCost t1 (y + 1) gr else 0) hmem))
    · simp only [if_neg hrg, Nat.zero_le]
  have hthird :=
    ContactCanonicalHighSourceUniformThirdCap6750Research.thirdCost_antitone_t
      (y := y) (r := r) ht
  unfold aCost thirdCost
  omega

private theorem bCost_mono_total {t1 t2 y r : Nat}
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t1) (ht : t1 ≤ t2) :
    bCost t1 y r ≤ bCost t2 y r := by
  simp only [bCost, coordinateCost, paddedT, paddedY, paddedR,
    max_eq_right hr2, max_eq_right (by omega : r + 1 ≤ y),
    max_eq_right hyt, max_eq_right (hyt.trans ht)]
  exact Nat.add_le_add
    (ContactCanonicalHighSourceAnchoredCap6750Research.cellRegularCost_mono_total ht)
    (ContactCanonicalHighSourceAnchoredCap6750Research.tightCount_mono_total ht)

private theorem thirdCost_diagonal_antitone_y {y1 y2 r : Nat}
    (hy : y1 ≤ y2) : thirdCost (y2 + 1) y2 r ≤
      thirdCost (y1 + 1) y1 r := by
  unfold thirdCost thirdStage thirdPivot
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
  gcongr <;> omega

private theorem aCost_diagonal_antitone_y {y1 y2 r : Nat} (hy : y1 ≤ y2) :
    aCost (y2 + 1) y2 r ≤ aCost (y1 + 1) y1 r := by
  have hu : upstreamRMax (y2 + 1) y2 r ≤ upstreamRMax (y1 + 1) y1 r := by
    unfold upstreamRMax
    apply Finset.sup_le
    intro gr hmem
    by_cases hrg : r ≤ gr
    · simp only [if_pos hrg]
      have h1 := upstreamCellCost_antitone_y (t := y2 + 1) (r := gr)
        (show y1 + 1 ≤ y2 + 1 by omega)
      have h2 := ContactUpstreamTAnalytic6750Research.upstreamCellCost_antitone_total
        (y := y1 + 1) (r := gr) (show y1 + 1 ≤ y2 + 1 by omega)
      exact (h1.trans h2).trans (by
        simpa only [if_pos hrg] using
          (Finset.le_sup
            (s := Finset.range 15)
            (f := fun gr => if r ≤ gr then
              upstreamCellCost (y1 + 1) (y1 + 1) gr else 0) hmem))
    · simp only [if_neg hrg, Nat.zero_le]
  have hthird := thirdCost_diagonal_antitone_y (r := r) hy
  unfold aCost
  omega

private theorem nonHostile_y_le_max {y r : Nat} (hy : y ≤ 64)
    (hr : r ≤ 14) (hnot : ¬ hostilePair y r) : y ≤ nonHostileMaxY r := by
  interval_cases r <;>
    simp only [nonHostileMaxY] <;>
    unfold hostilePair hostileMinR at hnot <;>
    split_ifs at hnot <;> omega

theorem basicNonPureCost_le_budget {t y r : Nat}
    (hr2 : 2 ≤ r) (hry : r < y) (hy1t : y + 1 ≤ t)
    (htop : t ≤ easyTop y r) (hyTop : y ≤ 64) (hrTop : r ≤ 14) :
    aCost t y r + bCost t y r ≤
      ContactMovingSeedless6750Research.mcaBudget := by
  by_cases hhost : hostilePair y r
  · have hwide : y + 1 ≤ tailMid y r := by
      have hcheck : ∀ (yy : Fin 65) (rr : Fin 15),
          hostilePair yy.1 rr.1 → yy.1 + 1 ≤ tailMid yy.1 rr.1 := by
        unfold hostilePair
        decide
      simpa using hcheck ⟨y, by omega⟩ ⟨r, by omega⟩ hhost
    have hEasyTop : easyTop y r ≤ 1659 := by
      have hcond : 38 ≤ y ∧ y ≤ 65 ∧ hostileMinR y ≤ r ∧ r ≤ 14 := by
        simpa only [hostilePair] using hhost
      simp only [easyTop, if_pos hcond]
      have hcheck : ∀ (yy : Fin 65) (rr : Fin 15),
          hostilePair yy.1 rr.1 → hardMinT yy.1 rr.1 ≤ 1659 := by
        unfold hostilePair
        decide
      have hm : hardMinT y r ≤ 1659 := by
        simpa using hcheck ⟨y, by omega⟩ ⟨r, by omega⟩ hhost
      omega
    have hcap : tailCap y r ≤ ContactMovingSeedless6750Research.mcaBudget := by
      simpa using tailReceipt ⟨y, by omega⟩ ⟨r, by omega⟩ hhost
    by_cases hleft : t ≤ tailMid y r
    · have ha := aCost_antitone_total (y := y) (r := r)
        (show y + 1 ≤ t by omega)
      have hb := bCost_mono_total hr2 hry (by omega) hleft
      unfold tailCap at hcap
      omega
    · have hm : tailMid y r + 1 ≤ t := by omega
      have ha := aCost_antitone_total (y := y) (r := r) hm
      have hb := bCost_mono_total hr2 hry (by omega) htop
      unfold tailCap at hcap
      omega
  · have hcond : ¬(38 ≤ y ∧ y ≤ 65 ∧ hostileMinR y ≤ r ∧ r ≤ 14) := by
      simpa only [hostilePair] using hhost
    have hEasyTop : easyTop y r = 1659 := by simp [easyTop, hcond]
    have hymax := nonHostile_y_le_max hyTop hrTop hhost
    have ha := aCost_antitone_total (y := y) (r := r)
      (show y + 1 ≤ t by omega)
    have hadiag : aCost (y + 1) y r ≤ aCost (r + 2) (r + 1) r := by
      simpa [Nat.add_assoc] using aCost_diagonal_antitone_y (r := r)
        (show r + 1 ≤ y by omega)
    have hb1 := bCost_mono_total hr2 hry (by omega) htop
    rw [hEasyTop] at hb1
    have hb2 : bCost 1659 y r ≤ bCost 1659 (nonHostileMaxY r) r := by
      simpa using nonHostileBReceipt
        ⟨y, by omega⟩ ⟨r, by omega⟩ hr2 hry hhost
    have hcap : nonHostileCap r ≤
        ContactMovingSeedless6750Research.mcaBudget := by
      simpa using nonHostileReceipt ⟨r, by omega⟩ hr2
    unfold nonHostileCap at hcap
    omega

end ProximityPrize.SubmissionLower.ContactLegacyAdaptiveBasic6750Research

#print axioms ProximityPrize.SubmissionLower.ContactLegacyAdaptiveBasic6750Research.basicNonPureCost_le_budget

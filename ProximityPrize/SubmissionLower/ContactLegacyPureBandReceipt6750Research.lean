import ProximityPrize.SubmissionLower.ContactOrdinaryHardShell6750Research
import ProximityPrize.SubmissionLower.ContactRouterCellCosts6750Research
import ProximityPrize.SubmissionLower.ContactLegacyMonotonicity6751Research

namespace ProximityPrize.SubmissionLower.ContactLegacyPureBandReceipt6750Research

open ContactAnchoredHardCellSelector6750Research
open ContactAnchoredOneFamilySelector6750Research
open ContactOrdinaryHardShell6750Research
open ContactRouterCellCosts6750Research
open ContactTwoTailResidualGeneric6750Research
open ContactTwoTailParameters6750Research

set_option autoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000

def paddedR (r : Nat) : Nat := max 2 r
def paddedY (y r : Nat) : Nat := max (paddedR r + 1) y
def paddedT (t y r : Nat) : Nat := max (paddedY y r) t
def coordinateCost (D t y r : Nat) : Nat :=
  cellRegularCost (paddedT t y r) (paddedY y r) (paddedR r) +
    (cellTightProfile D (paddedT t y r) (paddedR r)).countCap
def rfreeCost (D t : Nat) : Nat :=
  (cellTightProfile D (max 1 t) 1).countCap
def pureQD (y r : Nat) : Nat :=
  max (w + 1) (8729952 - (w * y - r))
def pureBandCap (y r : Nat) : Nat :=
  upstreamCellCost (hardMinT y r) y r +
    coordinateCost 8729952 (hardMinT y r - 1) y r +
    rfreeCost (pureQD y r) (1692 - y)

def pureBoundaryCost (ht y r : Nat) : Nat :=
  upstreamCellCost (hardMinT y r) y r +
    coordinateCost 8729952 ht y r +
    rfreeCost (pureQD y r) (1692 - ht)

private theorem row8 : ∀ y : Fin 66,
    OrdinaryHardCell (hardMinT y.1 8) y.1 8 →
    pureBandCap y.1 8 ≤ ContactMovingSeedless6750Research.mcaBudget := by
  unfold OrdinaryHardCell
  decide
private theorem row9 : ∀ y : Fin 66,
    OrdinaryHardCell (hardMinT y.1 9) y.1 9 →
    pureBandCap y.1 9 ≤ ContactMovingSeedless6750Research.mcaBudget := by
  unfold OrdinaryHardCell
  decide
private theorem row10 : ∀ y : Fin 66,
    OrdinaryHardCell (hardMinT y.1 10) y.1 10 →
    pureBandCap y.1 10 ≤ ContactMovingSeedless6750Research.mcaBudget := by
  unfold OrdinaryHardCell
  decide
private theorem row11 : ∀ y : Fin 66,
    OrdinaryHardCell (hardMinT y.1 11) y.1 11 →
    pureBandCap y.1 11 ≤ ContactMovingSeedless6750Research.mcaBudget := by
  unfold OrdinaryHardCell
  decide
private theorem row12 : ∀ y : Fin 66,
    OrdinaryHardCell (hardMinT y.1 12) y.1 12 →
    pureBandCap y.1 12 ≤ ContactMovingSeedless6750Research.mcaBudget := by
  unfold OrdinaryHardCell
  decide
private theorem row13 : ∀ y : Fin 66,
    OrdinaryHardCell (hardMinT y.1 13) y.1 13 →
    pureBandCap y.1 13 ≤ ContactMovingSeedless6750Research.mcaBudget := by
  unfold OrdinaryHardCell
  decide
private theorem row14 : ∀ y : Fin 66,
    OrdinaryHardCell (hardMinT y.1 14) y.1 14 →
    pureBandCap y.1 14 ≤ ContactMovingSeedless6750Research.mcaBudget := by
  unfold OrdinaryHardCell
  decide

theorem pureBandCap_le_budget
    (y r : Nat) (hy : y ≤ 65) (hr : r ≤ 14)
    (hcell : OrdinaryHardCell (hardMinT y r) y r) :
    pureBandCap y r ≤ ContactMovingSeedless6750Research.mcaBudget := by
  have hr8 : 8 ≤ r := by
    rcases hcell with ⟨_, _, hrlo, _, _, _⟩
    unfold ContactAnchoredOneFamilySelector6750Research.hostileMinR at hrlo
    split_ifs at hrlo <;> omega
  interval_cases r
  · simpa using row8 ⟨y, by omega⟩ hcell
  · simpa using row9 ⟨y, by omega⟩ hcell
  · simpa using row10 ⟨y, by omega⟩ hcell
  · simpa using row11 ⟨y, by omega⟩ hcell
  · simpa using row12 ⟨y, by omega⟩ hcell
  · simpa using row13 ⟨y, by omega⟩ hcell
  · simpa using row14 ⟨y, by omega⟩ hcell

private theorem coordinateCost_mono_total {D t1 t2 y r : Nat}
    (hr2 : 2 ≤ r) (hry : r < y) (hyt : y ≤ t1) (ht : t1 ≤ t2) :
    coordinateCost D t1 y r ≤ coordinateCost D t2 y r := by
  simp only [coordinateCost, paddedT, paddedY, paddedR,
    max_eq_right hr2, max_eq_right (by omega : r + 1 ≤ y),
    max_eq_right hyt, max_eq_right (hyt.trans ht)]
  exact Nat.add_le_add
    (ContactLegacyMonotonicity6751Research.cellRegularCost_mono_total ht)
    (ContactLegacyMonotonicity6751Research.tightCount_mono_total ht)

private theorem rfreeCost_mono_total {D t1 t2 : Nat} (ht : t1 ≤ t2) :
    rfreeCost D t1 ≤ rfreeCost D t2 := by
  unfold rfreeCost
  apply ContactLegacyMonotonicity6751Research.tightCount_mono_total
  omega

theorem pureBoundaryCost_le_budget {ht y r : Nat}
    (hcell : OrdinaryHardCell (hardMinT y r) y r)
    (hyht : y ≤ ht) (hnot : ¬ OrdinaryHardCell ht y r)
    (htop : ht ≤ 1692) :
    pureBoundaryCost ht y r ≤ ContactMovingSeedless6750Research.mcaBudget := by
  have hr2 : 2 ≤ r := by
    rcases hcell with ⟨_, _, hrlo, _, _, _⟩
    unfold hostileMinR at hrlo
    split_ifs at hrlo <;> omega
  have hry : r < y := by rcases hcell with ⟨_, _, _, _, _, _⟩; omega
  have hlt : ht < hardMinT y r := by
    by_contra hn
    apply hnot
    rcases hcell with ⟨hylo, hyhi, hrlo, hrhi, _, _⟩
    exact ⟨hylo, hyhi, hrlo, hrhi, by omega, htop⟩
  have hH := coordinateCost_mono_total (D := 8729952) hr2 hry hyht
    (show ht ≤ hardMinT y r - 1 by omega)
  have hQ := rfreeCost_mono_total (D := pureQD y r)
    (show 1692 - ht ≤ 1692 - y by omega)
  have hcap := pureBandCap_le_budget y r hcell.2.1 hcell.2.2.2.1 hcell
  unfold pureBoundaryCost pureBandCap at *
  omega

end ProximityPrize.SubmissionLower.ContactLegacyPureBandReceipt6750Research

#print axioms ProximityPrize.SubmissionLower.ContactLegacyPureBandReceipt6750Research.pureBandCap_le_budget

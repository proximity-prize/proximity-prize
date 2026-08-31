import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredHardCellSelector6750Research

 








namespace ProximityPrize.SubmissionLower.ContactOrdinaryHardShell6750Research

open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHardCellSelector6750Research

set_option autoImplicit false

 

def OrdinaryHardCell (t y r : Nat) : Prop :=
  38 ≤ y ∧ y ≤ 66 ∧
  hostileMinR y ≤ r ∧ r ≤ 14 ∧
  hardMinT y r ≤ t ∧ t ≤ 1699

 
def FirstDerivativeShell (t y r : Nat) : Prop :=
  OrdinaryHardCell t y r ∧ ¬ HardCell t y r

theorem HardCell.ordinaryHardCell {t y r : Nat} (h : HardCell t y r) :
    OrdinaryHardCell t y r := by
  refine ⟨h.y_lower, h.y_upper, h.r_lower, h.r_upper, h.t_lower, ?_⟩
  exact h.t_le_1659

theorem OrdinaryHardCell.hard_or_firstDerivativeShell
    {t y r : Nat} (h : OrdinaryHardCell t y r) :
    HardCell t y r ∨
      (t = 1699 ∧ r ≤ hardLastR1658 y) := by
  rcases h with ⟨hylo, hyhi, hrlo, hrhi, htlo, hthi⟩
  by_cases hr : r ≤ hardLastR1658 y
  · by_cases ht : t ≤ 1698
    · left
      refine ⟨hylo, hyhi, hrlo, hrhi, htlo, ?_⟩
      simp [hardMaxT, hr, ht]
    · right
      exact ⟨by omega, hr⟩
  · left
    refine ⟨hylo, hyhi, hrlo, hrhi, htlo, ?_⟩
    simp [hardMaxT, hr, hthi]

theorem FirstDerivativeShell.eq_1659_and_r_le
    {t y r : Nat} (h : FirstDerivativeShell t y r) :
    t = 1699 ∧ r ≤ hardLastR1658 y := by
  rcases h.1.hard_or_firstDerivativeShell with hhard | hshell
  · exact False.elim (h.2 hhard)
  · exact hshell

 
theorem hard_or_firstDerivativeShell_or_ordinaryEasy
    (t y r : Nat) :
    HardCell t y r ∨ FirstDerivativeShell t y r ∨
      ¬ OrdinaryHardCell t y r := by
  by_cases hord : OrdinaryHardCell t y r
  · by_cases hhard : HardCell t y r
    · exact Or.inl hhard
    · exact Or.inr (Or.inl ⟨hord, hhard⟩)
  · exact Or.inr (Or.inr hord)

end ProximityPrize.SubmissionLower.ContactOrdinaryHardShell6750Research

#print axioms ProximityPrize.SubmissionLower.ContactOrdinaryHardShell6750Research.OrdinaryHardCell.hard_or_firstDerivativeShell
#print axioms ProximityPrize.SubmissionLower.ContactOrdinaryHardShell6750Research.FirstDerivativeShell.eq_1659_and_r_le
#print axioms ProximityPrize.SubmissionLower.ContactOrdinaryHardShell6750Research.hard_or_firstDerivativeShell_or_ordinaryEasy

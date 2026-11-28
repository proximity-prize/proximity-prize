import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option Elab.async false

namespace R6970LayerMass
open Finset

/-- Sum the number of multiples that fit at each coefficient. -/
theorem layer_mass {ι : Type*} (sites : Finset ι) (w : ι → ℕ)
    (cap d copies : ℕ) :
    d * (∑ n ∈ range copies, (sites.filter (fun i => (n + 1) * d + w i ≤ cap)).card)
        ≤ ∑ i ∈ sites, (cap - w i) := by
  classical
  by_cases hpos : d = 0
  · simp [hpos]
  have hd : 0 < d := Nat.pos_of_ne_zero hpos
  calc
    _ = ∑ n ∈ range copies, ∑ i ∈ sites,
        if (n + 1) * d + w i ≤ cap then d else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [← Finset.sum_filter]
      simp [Nat.mul_comm]
    _ = ∑ i ∈ sites, ∑ n ∈ range copies,
        if (n + 1) * d + w i ≤ cap then d else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_filter, Finset.sum_const, Nat.nsmul_eq_mul]
      have sub : ((range copies).filter (fun n => (n + 1) * d + w i ≤ cap))
          ⊆ range ((cap - w i) / d) := by
        intro n hn
        have fit := (Finset.mem_filter.mp hn).2
        have hmul : (n + 1) * d ≤ cap - w i := by omega
        exact Finset.mem_range.mpr ((Nat.le_div_iff_mul_le hd).mpr hmul)
      exact (Nat.mul_le_mul_right d
        ((Finset.card_le_card sub).trans_eq (Finset.card_range _))).trans
        (Nat.div_mul_le_self _ _)

theorem degree_budget {ι : Type*} (sites : Finset ι) (w : ι → ℕ)
    (cap d copies step rank : ℕ)
    (fit : rank ≤ step * ∑ n ∈ range copies,
      (sites.filter (fun i => (n + 1) * d + w i ≤ cap)).card) :
    rank * d ≤ step * ∑ i ∈ sites, (cap - w i) := by
  exact (Nat.mul_le_mul_right d fit).trans (by
    rw [Nat.mul_assoc, Nat.mul_comm _ d]
    exact Nat.mul_le_mul_left step (layer_mass sites w cap d copies))

end R6970LayerMass

#print axioms R6970LayerMass.degree_budget

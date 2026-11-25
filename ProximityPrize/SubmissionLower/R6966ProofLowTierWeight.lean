import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option Elab.async false

namespace Research6966.LowTierWeight
open Finset

def weight (J j : ℕ) : ℕ := 4*j + if J < 2*j then J else 0

theorem mono (J : ℕ) {j k : ℕ} (h : j ≤ k) : weight J j ≤ weight J k := by
  unfold weight
  split <;> split <;> omega

theorem total {ι : Type*} (s : Finset ι) (f : ι → ℕ) {J : ℕ}
    (fits : ∑ i ∈ s, f i ≤ J) : ∑ i ∈ s, weight J (f i) ≤ 5*J := by
  classical
  let heavy := s.filter (fun i => J < 2*f i)
  have one : heavy.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨his, hi'⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjs, hj'⟩ := Finset.mem_filter.mp hj
    by_contra ne
    have sub : ({i,j} : Finset ι) ⊆ s := by
      intro a ha
      simp only [mem_insert,mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact his
      · exact hjs
    have h := (Finset.sum_le_sum_of_subset_of_nonneg sub (f:=f) (by intros; omega)).trans fits
    rw [Finset.sum_pair ne] at h
    omega
  have charged : (∑ i ∈ s, if J < 2*f i then J else 0) = heavy.card * J := by
    rw [← Finset.sum_filter]
    simp [heavy]
  simp only [weight,Finset.sum_add_distrib,← Finset.mul_sum,charged]
  have h := Nat.mul_le_mul_right J one
  omega

#print axioms total
end Research6966.LowTierWeight

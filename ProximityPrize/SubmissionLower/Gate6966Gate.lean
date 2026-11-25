import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
set_option Elab.async false

set_option autoImplicit false

namespace Gate6966Gate

open Module

section Overlap

variable {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]

theorem threshold_overlap (s : Finset ι) (V M : ι → Submodule 𝕜 E) (W : ι → ℕ)
    (h : (∑ i ∈ s, (finrank 𝕜 E - finrank 𝕜 (M i) + W i)) < ∑ i ∈ s, finrank 𝕜 (V i)) :
    ∃ i ∈ s, W i < finrank 𝕜 ↥(V i ⊓ M i) := by
  classical
  by_contra! hn
  apply Nat.not_lt_of_ge ?_ h
  refine Finset.sum_le_sum fun i hi => ?_
  have he := Submodule.finrank_sup_add_finrank_inf_eq (V i) (M i)
  have hsup := (V i ⊔ M i).finrank_le
  have hi' := hn i hi
  omega

end Overlap

section Gate

variable {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable {G : Type*}

theorem gate₂ (Target : Prop) (s : Finset ι) (V M : ι → Submodule 𝕜 E) (W : ι → ℕ)
    (Good : ι → G → Prop) (free : ι → G → ℕ)
    (hdich : ∀ i ∈ s, ∀ U : Submodule 𝕜 E, U ≤ V i ⊓ M i → U ≠ ⊥ →
      ∃ g : G, finrank 𝕜 U ≤ free i g ∧ (Good i g → Target))
    (hW : ∀ i ∈ s, ∀ g : G, ¬ Good i g → free i g ≤ W i)
    (hsum : (∑ i ∈ s, (finrank 𝕜 E - finrank 𝕜 (M i) + W i)) < ∑ i ∈ s, finrank 𝕜 (V i)) :
    Target := by
  obtain ⟨i, hi, hlt⟩ := threshold_overlap s V M W hsum
  have hne : (V i ⊓ M i) ≠ ⊥ := by
    intro hb
    rw [hb, _root_.finrank_bot] at hlt
    exact Nat.not_lt_zero _ hlt
  obtain ⟨g, hfin, hgood⟩ := hdich i hi (V i ⊓ M i) le_rfl hne
  by_cases hG : Good i g
  · exact hgood hG
  · exact absurd (hfin.trans (hW i hi g hG)) (Nat.not_le_of_lt hlt)

theorem gate₂_of_need (Target : Prop) (s : Finset ι) (V M : ι → Submodule 𝕜 E) (W : ι → ℕ)
    (Good : ι → G → Prop) (free : ι → G → ℕ) (need : ℕ)
    (hdich : ∀ i ∈ s, ∀ U : Submodule 𝕜 E, U ≤ V i ⊓ M i → U ≠ ⊥ →
      ∃ g : G, finrank 𝕜 U ≤ free i g ∧ (Good i g → Target))
    (hW : ∀ i ∈ s, ∀ g : G, ¬ Good i g → free i g ≤ W i)
    (hneed : need ≤ ∑ i ∈ s, finrank 𝕜 (V i))
    (hsum : (∑ i ∈ s, (finrank 𝕜 E - finrank 𝕜 (M i) + W i)) < need) :
    Target :=
  gate₂ Target s V M W Good free hdich hW (hsum.trans_le hneed)

end Gate

end Gate6966Gate

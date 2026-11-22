import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.Shared50Persistent -- serialize candidate build

open scoped BigOperators

namespace Shared50ShapeRankBase

variable {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A rank balance forces an element in one of the small support spaces. -/
theorem exists_nonzero_overlap (s : Finset ι) (V M : ι → Submodule 𝕜 E)
    (h : (∑ i ∈ s, (Module.finrank 𝕜 E - Module.finrank 𝕜 (M i))) <
      ∑ i ∈ s, Module.finrank 𝕜 (V i)) :
    ∃ i ∈ s, ∃ v : E, v ≠ 0 ∧ v ∈ V i ∧ v ∈ M i := by
  classical
  by_contra! hn
  apply (Nat.not_lt_of_ge ?_) h
  change (∑ i ∈ s, Module.finrank 𝕜 (V i)) ≤
    (∑ i ∈ s, (Module.finrank 𝕜 E - Module.finrank 𝕜 (M i)))
  refine Finset.sum_le_sum (s := s) (f := fun i => Module.finrank 𝕜 (V i))
    (g := fun i => Module.finrank 𝕜 E - Module.finrank 𝕜 (M i)) fun i hi => ?_
  have hmeet : V i ⊓ M i = ⊥ := by
    apply bot_unique
    intro v hv
    have hz : v = 0 := by
      by_contra hzero
      exact (hn i hi v hzero hv.1) hv.2
    rw [hz]
    exact Submodule.zero_mem _
  have he := (V i).finrank_sup_add_finrank_inf_eq (M i)
  rw [hmeet, finrank_bot, add_zero] at he
  have hsup := (V i ⊔ M i).finrank_le
  omega

theorem residual_order_pos {b f r k s : ℕ}
    (hr : 0 < r) (hf : s * b < f) (hG : k * f ≤ r * b) :
    0 < r - s*k := by
  by_contra! hs
  have hsr : r ≤ s*k := by omega
  have hk : 0 < k := by
    by_contra! hn
    interval_cases k
    simp at hsr
    omega
  have hprod := Nat.mul_lt_mul_of_pos_left hf hk
  have he : (s * k) * b = k * (s * b) := by ac_rfl
  rw [← he] at hprod
  exact (not_lt_of_ge hG) ((Nat.mul_le_mul_right b hsr).trans_lt hprod)

end Shared50ShapeRankBase

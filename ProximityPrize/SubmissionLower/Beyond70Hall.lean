import ProximityPrize.SubmissionLower.Pack_K1_14_3_2_7Proof

namespace Beyond70Hall

open scoped BigOperators

theorem rank_cut {F M N : Type*} [Field F] [Fintype M] [Fintype N]
    (A : Matrix M N F) (r : M → Prop) (c : N → Prop)
    [DecidablePred r] [DecidablePred c]
    (zero : ∀ i j, ¬ r i → ¬ c j → A i j = 0) :
    A.rank ≤ Fintype.card {i // r i} + Fintype.card {j // c j} := by
  classical
  let I := { i // r i } ⊕ { j // c j }
  let left : Matrix M I F := fun i k => Sum.elim
    (fun h : {i // r i} => if i = h.val then 1 else 0)
    (fun h : {j // c j} => if r i then 0 else A i h.val) k
  let right : Matrix I N F := fun k j => Sum.elim
    (fun h : {i // r i} => A h.val j)
    (fun h : {j // c j} => if h.val = j then 1 else 0) k
  have hprod : left * right = A := by
    ext i j
    change (left * right) i j = A i j
    rw [Matrix.mul_apply]
    dsimp only [I]
    rw [Fintype.sum_sum_type]
    simp only [left, right, Sum.elim_inl, Sum.elim_inr]
    have hrow : (∑ x : {i // r i}, if i = x.val then A x.val j else 0) =
        if r i then A i j else 0 := by
      split_ifs with hr
      · rw [Finset.sum_eq_single (⟨i, hr⟩ : {i // r i})]
        · simp
        · intro x _ hne
          have hx : i ≠ x.val := fun h => hne (Subtype.ext h.symm)
          simp [hx]
        · simp
      · apply Finset.sum_eq_zero
        intro x _
        have hx : i ≠ x.val := fun h => hr (h.symm ▸ x.property)
        simp [hx]
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
    rw [hrow]
    by_cases hr : r i
    · simp [hr]
    · by_cases hc : c j
      · simp only [hr, ite_false, zero_add]
        rw [Finset.sum_eq_single (⟨j, hc⟩ : {j // c j})]
        · simp
        · intro x _ hne
          have hx : x.val ≠ j := fun h => hne (Subtype.ext h)
          simp [hx]
        · simp
      · simp only [hr, ite_false, zero_add, zero i j hr hc]
        apply Finset.sum_eq_zero
        intro x _
        have hx : x.val ≠ j := fun h => hc (h ▸ x.property)
        simp [hx]
  rw [← hprod]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa [I] using left.rank_le_card_width)

local instance : Fact (Nat.Prime CJ0.p) := ⟨KoalaBear.is_prime⟩


end Beyond70Hall

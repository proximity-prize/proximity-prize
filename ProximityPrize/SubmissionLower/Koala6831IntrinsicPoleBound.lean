import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped BigOperators
open RCN187 RCN295

noncomputable section

set_option autoImplicit false

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

private theorem poleOrder_nonnegative (v : Valuation E (WithZero (Multiplicative ℤ))) (x : E) :
    0 ≤ poleOrder v x := le_max_left _ _

private theorem quotientExponentPoleWeight_le
    (i j k a b c : ℕ) (pY pZ₀ pZ₁ : ℤ)
    (hi : i ≤ a) (hij : i + j ≤ b) (hk : k ≤ c)
    (hZ₀ : 0 ≤ pZ₀) (hZ₁ : 0 ≤ pZ₁) :
    (i : ℤ) * pY + (j : ℤ) * pZ₀ + (k : ℤ) * pZ₁ ≤
      (a : ℤ) * max pY pZ₀ + ((b : ℤ) - a) * pZ₀ + (c : ℤ) * pZ₁ := by
  have hi' : (i : ℤ) ≤ a := by exact_mod_cast hi
  have hij' : (i : ℤ) + j ≤ b := by exact_mod_cast hij
  have hk' : (k : ℤ) ≤ c := by exact_mod_cast hk
  have hmax : 0 ≤ max pY pZ₀ - pZ₀ := sub_nonneg.mpr (le_max_right _ _)
  calc
    _ ≤ (i : ℤ) * max pY pZ₀ + (j : ℤ) * pZ₀ + (k : ℤ) * pZ₁ :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (Int.natCast_nonneg i)) le_rfl) le_rfl
    _ = (i : ℤ) * (max pY pZ₀ - pZ₀) + ((i : ℤ) + j) * pZ₀ + (k : ℤ) * pZ₁ := by ring
    _ ≤ (a : ℤ) * (max pY pZ₀ - pZ₀) + (b : ℤ) * pZ₀ + (c : ℤ) * pZ₁ :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hi' hmax)
        (mul_le_mul_of_nonneg_right hij' hZ₀)) (mul_le_mul_of_nonneg_right hk' hZ₁)
    _ = _ := by ring

theorem poleOrder_eval_le_quotient_caps
    (v : Valuation E (WithZero (Multiplicative ℤ)))
    (hcoeff : ∀ t : K, v (algebraMap K E t) ≤ 1)
    (order : Fin 3 ≃ Fin 3) (x : Fin 3 → E) (F : MvPolynomial (Fin 3) K)
    (a b c : ℕ) (hab : a ≤ b)
    (hcap : ∀ d ∈ F.support,
      d (order 0) ≤ a ∧ d (order 0) + d (order 1) ≤ b ∧ d (order 2) ≤ c) :
    poleOrder v (MvPolynomial.eval₂Hom (algebraMap K E) x F) ≤
      (a : ℤ) * max (poleOrder v (x (order 0))) (poleOrder v (x (order 1))) +
        ((b : ℤ) - a) * poleOrder v (x (order 1)) + (c : ℤ) * poleOrder v (x (order 2)) := by
  classical
  apply (poleOrder_eval_le_support v (algebraMap K E) hcoeff x F).trans
  unfold supportPoleWeight exponentSetPoleWeight
  apply Finset.max'_le
  intro m hm
  rcases Finset.mem_insert.mp hm with rfl | hm
  · have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
    exact add_nonneg (add_nonneg
      (mul_nonneg (Int.natCast_nonneg a) ((poleOrder_nonnegative v _).trans (le_max_left _ _)))
      (mul_nonneg (sub_nonneg.mpr hab') (poleOrder_nonnegative v _)))
      (mul_nonneg (Int.natCast_nonneg c) (poleOrder_nonnegative v _))
  · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hi, hij, hk⟩ := hcap d hd
    unfold exponentPoleWeight
    rw [← order.sum_comp (fun i => (d i : ℤ) * poleOrder v (x i)), Fin.sum_univ_three]
    exact quotientExponentPoleWeight_le _ _ _ a b c _ _ _ hi hij hk
      (poleOrder_nonnegative v _) (poleOrder_nonnegative v _)

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic

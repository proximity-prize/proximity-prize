import ProximityPrize.SubmissionBinaryLower.P64C6Uniform

/-!
# Integer profile identities for the positive-bias application

All agreement positions retained here lie on positive-order lines. Missing
positions will be charged separately by the incidence bound.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Geometry

variable {ι : Type*} [Fintype ι]

lemma sum_sub_one (μ : ι → ℕ) (A : Finset ι) (hμ : ∀ i ∈ A, 1 ≤ μ i) :
    (∑ i ∈ A, ((μ i - 1 : ℕ) : ℤ)) = (∑ i ∈ A, (μ i : ℤ)) - A.card := by
  have ht : ∀ i ∈ A, ((μ i - 1 : ℕ) : ℤ) = (μ i : ℤ) - 1 := by
    intro i hi
    rw [Nat.cast_sub (hμ i hi), Nat.cast_one]
  rw [Finset.sum_congr rfl ht, Finset.sum_sub_distrib]
  simp

lemma normal_le_excess (μ : ι → ℕ) (A : Finset ι) (w D N : ℕ)
    (hμ : ∀ i ∈ A, 1 ≤ μ i) (hA : D + N ≤ A.card) (hsupport : w < ∑ i ∈ A, μ i) :
    (w : ℤ) - D - (∑ i ∈ A, ((μ i - 1 : ℕ) : ℤ)) ≤
      N + ((A.card - (D + N) : ℕ) : ℤ) := by
  rw [sum_sub_one μ A hμ]
  have hsum : (w : ℤ) < ∑ i ∈ A, (μ i : ℤ) := by exact_mod_cast hsupport
  rw [Nat.cast_sub hA, Nat.cast_add]
  omega

lemma bias_leading (μ : ι → ℕ) (A : Finset ι) (h D N β : ℕ)
    (hA : D + N ≤ A.card) (hβ : (∑ i, μ i) + β = h * (D + N)) :
    (β : ℤ) + 4 * h * ((A.card - (D + N) : ℕ) : ℤ) ≤
      P64C6Bessel.bias (fun _ => 4 * h) A (4 * (∑ i, μ i) + β) := by
  have he : (∑ i, (μ i : ℤ)) + β = (h : ℤ) * (D + N) := by exact_mod_cast hβ
  unfold P64C6Bessel.bias
  rw [Nat.cast_sub hA]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sum]
  nlinarith

/-- A dangerous curve forces the total line order above the spatial weight. -/
lemma beta_lt (μ : ι → ℕ) (A : Finset ι) (h D N w β : ℕ)
    (hw : h * D ≤ w) (hsupport : w < ∑ i ∈ A, μ i)
    (hβ : (∑ i, μ i) + β = h * (D + N)) : β < h * N := by
  classical
  have hsum : (∑ i ∈ A, μ i) ≤ ∑ i, μ i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)
  nlinarith

end P64C6Geometry
end ProximityPrize.SubmissionBinaryLower

import ProximityPrize.SubmissionBinaryLower.P64C7Aggregate

/-!
# The mass identity and its lower bound

The profile hypothesis is homogeneous in the factor and line orders. This
allows the same statement to be retained through Frobenius descent.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Mass

open P64C7Aggregate

variable {ι : Type*} [Fintype ι]

theorem mass_identity (h : ℕ) (μ : ι → ℕ) (A : Finset ι) (hμ : ∀ i, μ i ≤ h) :
    (mass h μ A : ℤ) = (h : ℤ) ^ 2 * A.card - 2 * h * (∑ i ∈ A, (μ i : ℤ)) +
      ∑ i, (μ i : ℤ) ^ 2 := by
  classical
  have ht : ∀ i, ((if i ∈ A then (h - μ i) ^ 2 else μ i ^ 2 : ℕ) : ℤ) =
      (if i ∈ A then (h : ℤ) ^ 2 - 2 * h * μ i else 0) + (μ i : ℤ) ^ 2 := by
    intro i
    by_cases hi : i ∈ A
    · simp only [if_pos hi, Nat.cast_pow, Nat.cast_sub (hμ i)]
      ring
    · simp [hi]
  simp only [mass, Nat.cast_sum, ht, Finset.sum_add_distrib, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_const_zero, add_zero, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  ring

theorem defect_identity (μ : ι → ℕ) (A : Finset ι) (w D : ℕ)
    (hμ : ∀ i ∈ A, 1 ≤ μ i) :
    (w : ℤ) - D - ∑ i ∈ A, ((μ i - 1 : ℕ) : ℤ) =
      (w : ℤ) - D - (∑ i ∈ A, (μ i : ℤ)) + A.card := by
  have he : (∑ i ∈ A, ((μ i - 1 : ℕ) : ℤ)) = (∑ i ∈ A, (μ i : ℤ)) - A.card := by
    calc _ = ∑ i ∈ A, ((μ i : ℤ) - 1) := Finset.sum_congr rfl (fun i hi => by
          simp [Nat.cast_sub (hμ i hi)])
      _ = _ := by simp [Finset.sum_sub_distrib]
  rw [he]
  ring

/-- The protected profile bound leaves a factor of two in the mass per normal defect. -/
theorem mass_lower (h w N : ℕ) (μ : ι → ℕ) (A : Finset ι)
    (hh : 3 ≤ h) (hμh : ∀ i, μ i ≤ h) (hμ : ∀ i ∈ A, 1 ≤ μ i)
    (hcard : 1482911 ≤ A.card) (hsupport : w < ∑ i ∈ A, μ i)
    (hN : (N : ℤ) = (w : ℤ) - 1048575 - ∑ i ∈ A, ((μ i - 1 : ℕ) : ℤ))
    (hprofile : 2 * (h : ℤ) * w - h ^ 2 * 1048575 - (∑ i, (μ i : ℤ) ^ 2) ≤
      65536 * h ^ 2) :
    h ^ 2 * (2 * N) ≤ 4 * mass h μ A := by
  have hm := mass_identity h μ A hμh
  have hN' : (N : ℤ) = (w : ℤ) - 1048575 - (∑ i ∈ A, (μ i : ℤ)) + A.card :=
    hN.trans (by simpa only [Nat.cast_ofNat] using defect_identity μ A w 1048575 hμ)
  have hs : (w : ℤ) < ∑ i ∈ A, (μ i : ℤ) := by exact_mod_cast hsupport
  have ha : (1482911 : ℤ) ≤ A.card := by exact_mod_cast hcard
  have hh' : (3 : ℤ) ≤ h := by exact_mod_cast hh
  have hn : (N : ℤ) ≤ (A.card : ℤ) - 1048575 := by omega
  have hcoeff : (0 : ℤ) ≤ 3 * h ^ 2 - 8 * h := by nlinarith
  have h1 := mul_nonneg hcoeff (sub_nonneg.mpr hn)
  have h2 := mul_le_mul_of_nonneg_left (show (262144 : ℤ) ≤ (A.card : ℤ) - 1048575 by omega)
    (sq_nonneg (h : ℤ))
  have h3 : (0 : ℤ) ≤ h ^ 2 * N := by positivity
  have he : (mass h μ A : ℤ) =
      ((h : ℤ) ^ 2 - 2 * h) * ((A.card : ℤ) - 1048575) + 2 * h * N -
        (2 * h * w - h ^ 2 * 1048575 - (∑ i, (μ i : ℤ) ^ 2)) := by
    nlinarith only [hm, congrArg (fun t : ℤ => 2 * h * t) hN']
  have ht : (h : ℤ) ^ 2 * (2 * N) ≤ 4 * mass h μ A := by nlinarith only [he, h1, h2, h3, hprofile]
  exact_mod_cast ht

end P64C7Mass
end ProximityPrize.SubmissionBinaryLower

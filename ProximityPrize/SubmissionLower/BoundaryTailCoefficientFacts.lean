import ProximityPrize.SubmissionLower.BoundaryTailAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailCoefficientFacts

open BoundaryTailAlgebra RCN055 RCN313
variable {K : Type*} [Field K]
local notation "Poly4" => MvPolynomial (Fin 4) K
noncomputable section

def signedOddScalar : ℕ → K
  | 0 => 1
  | m + 1 => -(2 * m + 1 : K) * signedOddScalar m

@[simp] theorem signedOddScalar_zero : signedOddScalar (K := K) 0 = 1 := rfl

@[simp] theorem signedOddScalar_succ (m : ℕ) :
    signedOddScalar (K := K) (m + 1) = -(2 * m + 1 : K) * signedOddScalar m := by
  rfl

theorem signedOddScalar_ne_zero {p : ℕ} [CharP K p] (m : ℕ)
    (hm : 2 * m < p) : signedOddScalar (K := K) m ≠ 0 := by
  induction m with
  | zero => simp [signedOddScalar]
  | succ m ih =>
      rw [signedOddScalar_succ]
      apply mul_ne_zero
      · apply neg_ne_zero.mpr
        intro hz
        have hdvd : p ∣ 2 * m + 1 :=
          (CharP.cast_eq_zero_iff K p (2 * m + 1)).mp (by
            simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
              Nat.cast_one] using hz)
        exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
      · apply ih
        omega

theorem refinedCoefficientStep_support (F : Poly4) (m : ℕ)
    (C : ℕ → Poly4) (q : ℕ) (hq : m + 2 < q) :
    refinedCoefficientStep F m C q = 0 := by
  unfold refinedCoefficientStep
  apply Finset.sum_eq_zero
  intro i hi
  have hil : i ≤ m + 1 := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hqi : q ≠ i := by omega
  have hqi1 : q ≠ i + 1 := by omega
  have hqbranch : ¬(q = i + 2 ∧ i ≤ m) := by omega
  simp [hqi, hqi1, hqbranch]

theorem refinedCoefficients_support (F : Poly4) (m q : ℕ)
    (hq : m + 1 < q) : refinedCoefficients F m q = 0 := by
  induction m generalizing q with
  | zero =>
      have hq0 : q ≠ 0 := by omega
      simp [refinedCoefficients, hq0]
  | succ m ih =>
      simp only [refinedCoefficients]
      apply refinedCoefficientStep_support F m (refinedCoefficients F m) q
      omega

theorem refinedCoefficients_zero (F : Poly4) (m : ℕ) :
    refinedCoefficients F m 0 = MvPolynomial.C (signedOddScalar (K := K) m) := by
  induction m with
  | zero => simp [refinedCoefficients]
  | succ m ih =>
      have hC2 : MvPolynomial.C (2 : K) = (2 : Poly4) :=
        map_natCast (MvPolynomial.C : K →+* Poly4) 2
      simp [refinedCoefficients, refinedCoefficientStep, ih, signedOddScalar,
        contributionA, sExponent, Nat.cast_add, Nat.cast_mul, hC2]

theorem refinedCoefficients_zero_recurrence (F : Poly4) (m : ℕ) :
    refinedCoefficients F (m + 1) 0 =
      MvPolynomial.C (-(2 * m + 1 : K)) * refinedCoefficients F m 0 := by
  rw [refinedCoefficients_zero, refinedCoefficients_zero]
  simp [signedOddScalar, Nat.cast_add, Nat.cast_mul]

end
end ProximityPrize.SubmissionLower.BoundaryTailCoefficientFacts

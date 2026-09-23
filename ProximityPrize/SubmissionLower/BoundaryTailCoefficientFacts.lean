import ProximityPrize.SubmissionLower.BoundaryTailRepresentation
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

theorem refinedCoefficients_zero (F : Poly4) (m : ℕ) :
    refinedCoefficients F m 0 = MvPolynomial.C (signedOddScalar (K := K) m) := by
  induction m with
  | zero => simp [refinedCoefficients]
  | succ m ih =>
      have hC2 : MvPolynomial.C (2 : K) = (2 : Poly4) :=
        map_natCast (MvPolynomial.C : K →+* Poly4) 2
      simp [refinedCoefficients, refinedCoefficientStep, ih, signedOddScalar,
        contributionA, sExponent, Nat.cast_add, Nat.cast_mul, hC2]

end
end ProximityPrize.SubmissionLower.BoundaryTailCoefficientFacts

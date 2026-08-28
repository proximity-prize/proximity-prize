import ProximityPrize.SubmissionLower.BCHKSHilbert90GlobalGauge6400

/-!
# Primitive multiplier of a homogeneous semilinear solution

For a coprime pair `A,B`, every solution of

`A * H + B * sigma(H) = 0`

lies in the dual primitive direction.  Concretely, `H = B * R` and
`sigma(H) = -A * R` for one polynomial multiplier `R`.  This identifies the
actual degree object that a bounded Hilbert--90 gauge would have to control.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSHilbert90PrimitiveMultiplier6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSSemilinearPolynomialDescent6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Coprimality principalizes every homogeneous semilinear solution in the
dual direction `(B,-A)`. -/
theorem exists_primitiveMultiplier_of_semilinear_eq_zero6400
    (A B H : IRSProfile.Field[X])
    (hB : B ≠ 0) (hcoprime : IsCoprime A B)
    (hsemi : koalaPolynomialSemilinear6400 A B H = 0) :
    ∃ R : IRSProfile.Field[X],
      H = B * R ∧
      H.map koalaSexticFrobenius.toRingHom = -A * R := by
  have hcross :
      B * (-H.map koalaSexticFrobenius.toRingHom) = A * H := by
    rw [koalaPolynomialSemilinear6400] at hsemi
    linear_combination -hsemi
  obtain ⟨R, hH, hmap⟩ :=
    exists_polynomial_multiplier_of_coprime_cross
      B A H (-H.map koalaSexticFrobenius.toRingHom)
      hB hcoprime.symm hcross
  refine ⟨R, ?_, ?_⟩
  · simpa only [mul_comm] using hH
  · have hneg := congrArg Neg.neg hmap
    calc
      H.map koalaSexticFrobenius.toRingHom = -(R * A) := by
        simpa only [neg_neg] using hneg
      _ = -A * R := by ring

/-- For nonzero `H`, primitive factorization subtracts the degree of `B`
exactly rather than merely giving the five-factor adjugate upper bound. -/
theorem primitiveMultiplier_natDegree_add6400
    (B H R : IRSProfile.Field[X])
    (hB : B ≠ 0) (hH : H ≠ 0) (hfactor : H = B * R) :
    R.natDegree + B.natDegree = H.natDegree := by
  have hR : R ≠ 0 := by
    intro hzero
    apply hH
    rw [hfactor, hzero, mul_zero]
  rw [hfactor, Polynomial.natDegree_mul hB hR, Nat.add_comm]

/-- If `B` has degree `d` and a homogeneous gauge has the generic adjugate
bound `5*d`, its primitive multiplier has degree at most `4*d`. -/
theorem primitiveMultiplier_natDegree_le_four_mul6400
    (B H R : IRSProfile.Field[X]) (d : Nat)
    (hB : B ≠ 0) (hH : H ≠ 0)
    (hBdegree : B.natDegree = d) (hfactor : H = B * R)
    (hHdegree : H.natDegree ≤ 5 * d) :
    R.natDegree ≤ 4 * d := by
  have hsum := primitiveMultiplier_natDegree_add6400 B H R hB hH hfactor
  rw [hBdegree] at hsum
  omega

/-- Nodewise nonvanishing descends from the gauge to its primitive
multiplier whenever the primitive denominator lane is nonzero there. -/
theorem primitiveMultiplier_eval_ne_zero6400
    (B H R : IRSProfile.Field[X]) (x : IRSProfile.Field)
    (hfactor : H = B * R) (hH : H.eval x ≠ 0) :
    R.eval x ≠ 0 := by
  intro hzero
  apply hH
  rw [hfactor, Polynomial.eval_mul, hzero, mul_zero]

end BCHKSHilbert90PrimitiveMultiplier6400
end ProximityPrize.SubmissionLower

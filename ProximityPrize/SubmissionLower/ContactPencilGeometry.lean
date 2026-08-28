import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualCurveCoordinateField

import ProximityPrize.SubmissionLower.LocalMathlib_Algebra_MvPolynomial_NoZeroDivisors

/-!
# Actual pencil geometry inside prime-quotient coordinate fields

Model label: gpt-5.

An R-dependent principal prime cannot make Y affine in Z. On a genuine
non-point prime curve over an algebraically closed field, if Y and R are
both affine in Z, then Z is transcendental. These are proved on the actual
prime quotient and its fraction field, not assumed dimension properties.

Polynomial value/slope recovery transports an actual polynomial pencil
identity to these two coordinate relations. The contact Taylor and
identity-node theorems supply those inputs in the later counting assembly.
-/

namespace ProximityPrize.SubmissionLower.ContactPencilGeometry

open ActualCurveCoordinateField

noncomputable section

variable (K : Type) [Field K]

def graphEquation (a b : K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 0 - (MvPolynomial.C a + MvPolynomial.X 2 * MvPolynomial.C b)

theorem graphEquation_ne_zero (a b : K) : graphEquation K a b ≠ 0 := by
  intro h
  have hd := congrArg (MvPolynomial.pderiv (0 : Fin 3)) h
  simp [graphEquation] at hd

theorem graphEquation_r_degree (a b : K) :
    (graphEquation K a b).degreeOf (1 : Fin 3) = 0 := by
  have hm : (MvPolynomial.X 2 * MvPolynomial.C b : MvPolynomial (Fin 3) K).degreeOf 1 ≤ 0 := by
    simpa [MvPolynomial.degreeOf_X] using MvPolynomial.degreeOf_mul_le (1 : Fin 3)
      (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) (MvPolynomial.C b)
  have ha : (MvPolynomial.C a + MvPolynomial.X 2 * MvPolynomial.C b :
      MvPolynomial (Fin 3) K).degreeOf 1 ≤ 0 :=
    (MvPolynomial.degreeOf_add_le 1 _ _).trans (max_le (by simp) hm)
  apply Nat.eq_zero_of_le_zero
  exact (MvPolynomial.degreeOf_sub_le 1 _ _).trans
    (max_le (by simp [MvPolynomial.degreeOf_X]) ha)

variable (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]

theorem graphEquation_mem_of_affine_coordinate (a b : K)
    (hy : coordinate K P 0 = algebraMap K (CoordinateField K P) a +
      coordinate K P 2 * algebraMap K (CoordinateField K P) b) :
    graphEquation K a b ∈ P := by
  rw [← coordinateEvaluation_ker K P]
  change coordinateEvaluation K P (graphEquation K a b) = 0
  simp only [graphEquation, map_sub, map_add, map_mul]
  change coordinate K P 0 - (algebraMap K (CoordinateField K P) a +
    coordinate K P 2 * algebraMap K (CoordinateField K P) b) = 0
  exact sub_eq_zero.mpr hy

/-- An actual R-dependent hypersurface cannot be contained in a pencil
graph, already using only its Y-coordinate equation. -/
theorem not_y_affine_of_r_dependent_principal
    (g : MvPolynomial (Fin 3) K) (hP : P = Ideal.span {g})
    (hr : 0 < g.degreeOf (1 : Fin 3)) (a b : K) :
    coordinate K P 0 ≠ algebraMap K (CoordinateField K P) a +
      coordinate K P 2 * algebraMap K (CoordinateField K P) b := by
  intro hy
  have hmem := graphEquation_mem_of_affine_coordinate K P a b hy
  rw [hP, Ideal.mem_span_singleton] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hprod : g * q ≠ 0 := by
    rw [← hq]
    exact graphEquation_ne_zero K a b
  obtain ⟨hg0, hq0⟩ := mul_ne_zero_iff.mp hprod
  have hle : g.degreeOf 1 ≤ (graphEquation K a b).degreeOf 1 := by
    rw [hq, MvPolynomial.degreeOf_mul_eq hg0 hq0]
    exact Nat.le_add_right _ _
  rw [graphEquation_r_degree] at hle
  omega

theorem coordinate_algebraic_of_scalar (i : Fin 3) (c : K)
    (hc : coordinate K P i = algebraMap K (CoordinateField K P) c) :
    IsAlgebraic K (coordinate K P i) := by
  refine ⟨Polynomial.X - Polynomial.C c, Polynomial.X_sub_C_ne_zero c, ?_⟩
  simp [hc]

/-- Vertical polynomial-pencil curves would be points, contradicting the
actual component's already established non-point prime. -/
theorem seed_transcendental_of_affine_coordinates [IsAlgClosed K]
    (hnonpoint : ∀ v : Fin 3 → K,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (a b c d : K)
    (hy : coordinate K P 0 = algebraMap K (CoordinateField K P) a +
      coordinate K P 2 * algebraMap K (CoordinateField K P) b)
    (hr : coordinate K P 1 = algebraMap K (CoordinateField K P) c +
      coordinate K P 2 * algebraMap K (CoordinateField K P) d) :
    Transcendental K (coordinate K P 2) := by
  intro hz
  obtain ⟨z, hz⟩ := coordinate_eq_scalar_of_isAlgebraic K P 2 hz
  have hy' : coordinate K P 0 = algebraMap K (CoordinateField K P) (a + z * b) := by
    simpa only [map_add, map_mul, hz] using hy
  have hr' : coordinate K P 1 = algebraMap K (CoordinateField K P) (c + z * d) := by
    simpa only [map_add, map_mul, hz] using hr
  have hall : ∀ i : Fin 3, IsAlgebraic K (coordinate K P i) := by
    intro i
    fin_cases i
    · exact coordinate_algebraic_of_scalar K P 0 _ hy'
    · exact coordinate_algebraic_of_scalar K P 1 _ hr'
    · exact coordinate_algebraic_of_scalar K P 2 _ hz.symm
  obtain ⟨v, hv⟩ := eq_point_kernel_of_coordinates_algebraic K P hall
  exact hnonpoint v hv

/-- Actual value and slope recovery turn a polynomial pencil identity into
both affine coordinate identities in the original quotient field. -/
theorem affine_coordinates_of_polynomial_pencil
    (ξ : K) (Q : Polynomial (CoordinateField K P)) (Q₀ Q₁ : Polynomial K)
    (hQ : Q = Q₀.map (algebraMap K (CoordinateField K P)) +
      Polynomial.C (coordinate K P 2) * Q₁.map (algebraMap K (CoordinateField K P)))
    (hy : Q.eval (algebraMap K (CoordinateField K P) ξ) = coordinate K P 0)
    (hr : Q.derivative.eval (algebraMap K (CoordinateField K P) ξ) = coordinate K P 1) :
    coordinate K P 0 = algebraMap K (CoordinateField K P) (Q₀.eval ξ) +
        coordinate K P 2 * algebraMap K (CoordinateField K P) (Q₁.eval ξ) ∧
      coordinate K P 1 = algebraMap K (CoordinateField K P) (Q₀.derivative.eval ξ) +
        coordinate K P 2 * algebraMap K (CoordinateField K P) (Q₁.derivative.eval ξ) := by
  constructor
  · rw [← hy, hQ]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_map_apply]
  · rw [← hr, hQ, Polynomial.derivative_add, Polynomial.derivative_C_mul]
    simp only [Polynomial.derivative_map, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_map_apply]

end

end ProximityPrize.SubmissionLower.ContactPencilGeometry

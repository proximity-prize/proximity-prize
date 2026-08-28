import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.SmallCoordinateBoxZeroCount
import ProximityPrize.SubmissionLower.ActualCurveZeroCount

/-!
# Actual curve zero count for projections below twice the characteristic

The actual quotient curve uses one chosen finite/separable coordinate to
construct its common projective place space.  Every coordinate used in
the box estimate need only have finite degree below `2p`.
-/

namespace ProximityPrize.SubmissionLower.ActualCurveZeroCountSmall

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveScalarTowers ActualCurveZeroCount

noncomputable section

variable (K : Type) [Field K]
variable (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
variable (p : ℕ) [ExpChar K p]

def ProjectionsFiniteSmall : Prop :=
  ∀ (i : Fin 3) (hi : Transcendental K (coordinate K P i)),
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P i hi
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Module.finrank (RatFunc K) (CoordinateField K P) < 2 * p

variable [IsAlgClosed K]

def coordinateData (hproj : ProjectionsFiniteSmall K P p) (i : Fin 3) :
    SmallCoordinateBoxZeroCount.Coordinate K (CoordinateField K P) p :=
  if hi : Transcendental K (coordinate K P i) then
    Sum.inr {
      embedding := rationalBaseEmbedding K P i hi
      finite := (hproj i hi).1
      degree_lt_two := (hproj i hi).2 }
  else
    Sum.inl ((coordinate_eq_scalar_of_isAlgebraic K P i (not_not.mp hi)).choose)

theorem coordinateData_value (hproj : ProjectionsFiniteSmall K P p) (i : Fin 3) :
    SmallCoordinateBoxZeroCount.coordinateValue K (CoordinateField K P) p
      (coordinateData K P p hproj i) = coordinate K P i := by
  unfold coordinateData
  split_ifs with hi
  · exact rational_variable_image K P i hi
  · exact (coordinate_eq_scalar_of_isAlgebraic K P i (not_not.mp hi)).choose_spec

theorem coordinateData_degree (hproj : ProjectionsFiniteSmall K P p) (i : Fin 3) :
    SmallCoordinateBoxZeroCount.coordinateDegree K (CoordinateField K P) p
      (coordinateData K P p hproj i) = actualCoordinateDegree K P i := by
  unfold coordinateData actualCoordinateDegree
  split_ifs <;> rfl

/-- Actual affine point count with one explicit separable separator and
small (possibly inseparable) coordinate projections everywhere else. -/
theorem finite_zero_points_le_box_of_separator
    (hp : p.Prime) (hproj : ProjectionsFiniteSmall K P p)
    (i₀ : Fin 3) (hi₀ : Transcendental K (coordinate K P i₀))
    (hsep₀ : letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P i₀ hi₀
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P))
    (F : MvPolynomial (Fin 3) K) (hF : F ∉ P)
    (cap : Fin 3 → ℕ) (hcap : ∀ i, F.degreeOf i ≤ cap i)
    (S : Finset (Fin 3 → K))
    (hSP : ∀ v ∈ S, P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hSF : ∀ v ∈ S, MvPolynomial.aeval v F = 0) :
    (S.card : ℤ) ≤ ∑ i, (cap i : ℤ) * (actualCoordinateDegree K P i : ℤ) := by
  classical
  letI : Algebra (Polynomial K) (CoordinateRing K P) :=
    quotientPolynomialAlgebra K P i₀
  letI : Algebra (Polynomial K) (CoordinateField K P) :=
    polynomialBaseAlgebra K P i₀
  letI : Algebra (RatFunc K) (CoordinateField K P) :=
    rationalBaseAlgebra K P i₀ hi₀
  letI := quotientBaseScalarTower K P i₀
  letI := polynomialBaseScalarTower K P i₀
  letI := quotientFractionScalarTower K P i₀
  letI := polynomialRationalScalarTower K P i₀ hi₀
  letI := rationalBaseScalarTower K P i₀ hi₀
  letI : FiniteDimensional (RatFunc K) (CoordinateField K P) :=
    (hproj i₀ hi₀).1
  letI : Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := hsep₀
  let c := coordinateData K P p hproj
  have hc : ∀ i, SmallCoordinateBoxZeroCount.coordinateValue
      K (CoordinateField K P) p (c i) =
        algebraMap (CoordinateRing K P) (CoordinateField K P)
          (quotientCoordinate K P i) := by
    intro i
    rw [quotientCoordinate_fraction]
    exact coordinateData_value K P p hproj i
  let liftPoint : {v : Fin 3 → K // v ∈ S} → (CoordinateRing K P →ₐ[K] K) :=
    fun v ↦ pointHom K P ⟨v.1, hSP v.1 v.2⟩
  have hinj : Function.Injective liftPoint := by
    intro v w h
    have hvw := pointHom_injective K P h
    apply Subtype.ext
    exact congrArg (fun z : PointOn K P ↦ z.val) hvw
  let points := S.attach.image liftPoint
  have hpoints : ∀ φ ∈ points, φ (MvPolynomial.eval₂Hom
      (algebraMap K (CoordinateRing K P)) (quotientCoordinate K P) F) = 0 := by
    intro φ hφ
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hφ
    rw [quotient_eval_eq_mk]
    exact hSF v.1 v.2
  have hcount := SmallCoordinateBoxZeroCount.finite_model_zero_points_le_box
    K (CoordinateField K P) (CoordinateRing K P) hp
    (quotientCoordinate K P) c hc cap F hcap
    (quotient_eval_ne_zero_of_not_mem K P F hF) points hpoints
  have hcard : points.card = S.card := by
    change (S.attach.image liftPoint).card = S.card
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  rw [hcard] at hcount
  simpa only [c, coordinateData_degree] using hcount

end

end ProximityPrize.SubmissionLower.ActualCurveZeroCountSmall

#print axioms ProximityPrize.SubmissionLower.ActualCurveZeroCountSmall.finite_zero_points_le_box_of_separator

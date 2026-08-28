import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.CoordinateBoxZeroCount
import ProximityPrize.SubmissionLower.ActualCurveScalarTowers

/-!
# Box zero counts on the actual prime-component coordinate ring

Model label: gpt-5.

The ring is the literal quotient of K[Y,R,Z] by the actual prime, and
the field is its literal fraction ring. Original affine points descend
to actual quotient algebra homomorphisms, injectively. A proper test
polynomial is proved nonzero in this quotient and its coordinate field.

Algebraic coordinates are proved constant over algebraically closed K;
each transcendental coordinate uses its canonical actual RatFunc
embedding. The only projection inputs are finite-dimensionality and
separability for these actual induced extensions, supplied by the
separate proper-cut degree pipeline. No field presentation, point map,
height, pole, or zero-count inequality is assumed.
-/

namespace ProximityPrize.SubmissionLower.ActualCurveZeroCount

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveScalarTowers

noncomputable section

variable (K : Type) [Field K]
variable (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]

abbrev PointOn :=
  {v : Fin 3 → K // P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom}

/-- Actual descent of the original point evaluation through the quotient. -/
def pointHom (v : PointOn K P) : CoordinateRing K P →ₐ[K] K :=
  Ideal.Quotient.liftₐ P (MvPolynomial.aeval v.1) (fun F hF ↦ v.2 hF)

theorem pointHom_mk (v : PointOn K P) (F : MvPolynomial (Fin 3) K) :
    pointHom K P v (Ideal.Quotient.mk P F) = MvPolynomial.aeval v.1 F := rfl

theorem pointHom_coordinate (v : PointOn K P) (i : Fin 3) :
    pointHom K P v (quotientCoordinate K P i) = v.1 i := by
  rw [quotientCoordinate, pointHom_mk, MvPolynomial.aeval_X]

/-- Different original coordinate triples give different actual quotient
K-points; this is proved on the three coordinate functions. -/
theorem pointHom_injective : Function.Injective (pointHom K P) := by
  intro v w h
  apply Subtype.ext
  funext i
  have hi := DFunLike.congr_fun h (quotientCoordinate K P i)
  simpa only [pointHom_coordinate] using hi

theorem quotient_eval_eq_mk (F : MvPolynomial (Fin 3) K) :
    MvPolynomial.eval₂Hom (algebraMap K (CoordinateRing K P))
      (quotientCoordinate K P) F = Ideal.Quotient.mk P F := by
  have hhom : MvPolynomial.aeval (quotientCoordinate K P) = Ideal.Quotient.mkₐ K P := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X]
    rfl
  exact AlgHom.congr_fun hhom F

theorem quotient_eval_ne_zero_of_not_mem (F : MvPolynomial (Fin 3) K) (hF : F ∉ P) :
    MvPolynomial.eval₂Hom (algebraMap K (CoordinateRing K P))
      (quotientCoordinate K P) F ≠ 0 := by
  rw [quotient_eval_eq_mk]
  intro hzero
  exact hF (Ideal.Quotient.eq_zero_iff_mem.mp hzero)

/-- The previously proved literal evaluation kernel also gives the
proper-test nonvanishing in the actual component field. -/
theorem field_eval_ne_zero_iff (F : MvPolynomial (Fin 3) K) :
    MvPolynomial.aeval (coordinate K P) F ≠ 0 ↔ F ∉ P := by
  change ¬ F ∈ RingHom.ker (MvPolynomial.aeval (coordinate K P)).toRingHom ↔ F ∉ P
  rw [aeval_coordinate_ker]

/-- These are the actual canonical projection extensions. This property
does not contain a field-degree, height, or point-count inequality. -/
def ProjectionsFiniteSeparable : Prop :=
  ∀ (i : Fin 3) (hi : Transcendental K (coordinate K P i)),
    letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P)

/-- Degree of the actual coordinate projection; constant coordinates
have degree zero. Finrank is taken for the canonical rational embedding. -/
def actualCoordinateDegree (i : Fin 3) : ℕ :=
  if hi : Transcendental K (coordinate K P i) then
    letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
    Module.finrank (RatFunc K) (CoordinateField K P)
  else 0

theorem actualCoordinateDegree_of_transcendental (i : Fin 3)
    (hi : Transcendental K (coordinate K P i)) :
    actualCoordinateDegree K P i =
      (letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
       Module.finrank (RatFunc K) (CoordinateField K P)) := by
  simp only [actualCoordinateDegree, dif_pos hi]

theorem actualCoordinateDegree_of_isAlgebraic (i : Fin 3)
    (hi : IsAlgebraic K (coordinate K P i)) : actualCoordinateDegree K P i = 0 := by
  exact dif_neg (not_not.mpr hi)

variable [IsAlgClosed K]

/-- Construct the coordinate data required by the proved global bound
from the actual coordinates, with no arbitrary embedding choice. -/
def coordinateData (hproj : ProjectionsFiniteSeparable K P) (i : Fin 3) :
    CoordinateBoxZeroCount.Coordinate K (CoordinateField K P) :=
  if hi : Transcendental K (coordinate K P i) then
    Sum.inr {
      embedding := rationalBaseEmbedding K P i hi
      finite := (hproj i hi).1
      separable := (hproj i hi).2 }
  else
    Sum.inl ((coordinate_eq_scalar_of_isAlgebraic K P i (not_not.mp hi)).choose)

theorem coordinateData_value (hproj : ProjectionsFiniteSeparable K P) (i : Fin 3) :
    CoordinateBoxZeroCount.coordinateValue K (CoordinateField K P)
      (coordinateData K P hproj i) = coordinate K P i := by
  unfold coordinateData
  split_ifs with hi
  · exact rational_variable_image K P i hi
  · exact (coordinate_eq_scalar_of_isAlgebraic K P i (not_not.mp hi)).choose_spec

theorem coordinateData_degree (hproj : ProjectionsFiniteSeparable K P) (i : Fin 3) :
    CoordinateBoxZeroCount.coordinateDegree K (CoordinateField K P)
      (coordinateData K P hproj i) = actualCoordinateDegree K P i := by
  unfold coordinateData actualCoordinateDegree
  split_ifs <;> rfl

/-- The actual original affine point count after choosing one actual
transcendental coordinate as the separator. Every scalar tower, point
homomorphism, and proper-test nonvanishing is derived. -/
theorem finite_zero_points_le_box_of_separator
    (hproj : ProjectionsFiniteSeparable K P)
    (i₀ : Fin 3) (hi₀ : Transcendental K (coordinate K P i₀))
    (F : MvPolynomial (Fin 3) K) (hF : F ∉ P)
    (cap : Fin 3 → ℕ) (hcap : ∀ i, F.degreeOf i ≤ cap i)
    (S : Finset (Fin 3 → K))
    (hSP : ∀ v ∈ S, P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hSF : ∀ v ∈ S, MvPolynomial.aeval v F = 0) :
    (S.card : ℤ) ≤ ∑ i, (cap i : ℤ) * (actualCoordinateDegree K P i : ℤ) := by
  classical
  letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i₀
  letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i₀
  letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i₀ hi₀
  letI := quotientBaseScalarTower K P i₀
  letI := polynomialBaseScalarTower K P i₀
  letI := quotientFractionScalarTower K P i₀
  letI := polynomialRationalScalarTower K P i₀ hi₀
  letI := rationalBaseScalarTower K P i₀ hi₀
  letI : FiniteDimensional (RatFunc K) (CoordinateField K P) := (hproj i₀ hi₀).1
  letI : Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := (hproj i₀ hi₀).2
  let c := coordinateData K P hproj
  have hc : ∀ i, CoordinateBoxZeroCount.coordinateValue K (CoordinateField K P) (c i) =
      algebraMap (CoordinateRing K P) (CoordinateField K P) (quotientCoordinate K P i) := by
    intro i
    rw [quotientCoordinate_fraction]
    exact coordinateData_value K P hproj i
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
  have hcount := CoordinateBoxZeroCount.finite_model_zero_points_le_box
    K (CoordinateField K P) (CoordinateRing K P) (quotientCoordinate K P)
    c hc cap F hcap (quotient_eval_ne_zero_of_not_mem K P F hF) points hpoints
  have hcard : points.card = S.card := by
    change (S.attach.image liftPoint).card = S.card
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  rw [hcard] at hcount
  simpa only [c, coordinateData_degree] using hcount

/-- An actual non-point prime supplies its own separating coordinate
via the proved quotient-field theorem; no coordinate is supplied here. -/
theorem finite_zero_points_le_box
    (hproj : ProjectionsFiniteSeparable K P)
    (hnonpoint : ∀ v : Fin 3 → K,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (F : MvPolynomial (Fin 3) K) (hF : F ∉ P)
    (cap : Fin 3 → ℕ) (hcap : ∀ i, F.degreeOf i ≤ cap i)
    (S : Finset (Fin 3 → K))
    (hSP : ∀ v ∈ S, P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hSF : ∀ v ∈ S, MvPolynomial.aeval v F = 0) :
    (S.card : ℤ) ≤ ∑ i, (cap i : ℤ) * (actualCoordinateDegree K P i : ℤ) := by
  obtain ⟨i, hi⟩ := exists_transcendental_coordinate_of_ne_point_kernel K P hnonpoint
  exact finite_zero_points_le_box_of_separator K P hproj i hi F hF cap hcap S hSP hSF

end

end ProximityPrize.SubmissionLower.ActualCurveZeroCount

#print axioms ProximityPrize.SubmissionLower.ActualCurveZeroCount.pointHom
#print axioms ProximityPrize.SubmissionLower.ActualCurveZeroCount.pointHom_injective
#print axioms ProximityPrize.SubmissionLower.ActualCurveZeroCount.quotient_eval_ne_zero_of_not_mem
#print axioms ProximityPrize.SubmissionLower.ActualCurveZeroCount.field_eval_ne_zero_iff
#print axioms ProximityPrize.SubmissionLower.ActualCurveZeroCount.actualCoordinateDegree_of_transcendental
#print axioms ProximityPrize.SubmissionLower.ActualCurveZeroCount.coordinateData_value
#print axioms ProximityPrize.SubmissionLower.ActualCurveZeroCount.coordinateData_degree
#print axioms ProximityPrize.SubmissionLower.ActualCurveZeroCount.finite_zero_points_le_box_of_separator
#print axioms ProximityPrize.SubmissionLower.ActualCurveZeroCount.finite_zero_points_le_box

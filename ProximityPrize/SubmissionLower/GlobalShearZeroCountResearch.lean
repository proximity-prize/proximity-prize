import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualCurveArbitraryProjectionZeroCountResearch
import ProximityPrize.SubmissionLower.ActualCurveZeroCount
import ProximityPrize.SubmissionLower.TrivariateShearResearch
import ProximityPrize.SubmissionLower.ArbitraryRationalProjectionResearch
import ProximityPrize.SubmissionLower.CharacteristicFreeInseparableDichotomyResearch

/-!
# Actual affine zero count after one scalar triangular shear

This research adapter keeps the original prime quotient and its original
affine points.  It substitutes `R = S - a Z` in the test polynomial, uses
`S = R + a Z` as the common finite separable parameter, and applies the
existing affine-model place theorem.  Thus no prime-ideal transport or
point-bijection theorem is needed for the fibre count.
-/

namespace ProximityPrize.SubmissionLower.GlobalShearZeroCountResearch

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveScalarTowers
  ActualCurveZeroCount CoordinateBoxZeroCount
open ActualCurveArbitraryProjectionZeroCountResearch
open TrivariateShearResearch ArbitraryRationalProjectionResearch
open CharacteristicFreeInseparableDichotomyResearch

noncomputable section

set_option maxHeartbeats 1000000

variable (K : Type) [Field K]
variable (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]

local instance : DecidableEq K := Classical.decEq K

/-- A proof-irrelevance-stable three-entry function.  Unlike nested vector
notation, this reduces cleanly after case splitting on `Fin 3`. -/
def triple {A : Type} (x₀ x₁ x₂ : A) : Fin 3 → A :=
  Fin.cases x₀ (Fin.cases x₁ (Fin.cases x₂ Fin.elim0))

/-- Literal coordinates of the unchanged quotient model after declaring
the middle variable to be `S = R + a Z`. -/
def shearedModelCoordinates (a : K) : Fin 3 → CoordinateRing K P :=
  triple (quotientCoordinate K P 0)
    (quotientCoordinate K P 1 +
      algebraMap K (CoordinateRing K P) a * quotientCoordinate K P 2)
    (quotientCoordinate K P 2)

/-- Evaluation transport in an arbitrary coefficient algebra.  This is the
ring-valued form of `aeval_shear_at_add`; it is what lets the quotient-ring
nonvanishing proof avoid any transported prime. -/
theorem eval₂Hom_shear_at_add
    {A : Type} [CommRing A] [Algebra K A]
    (F : MvPolynomial (Fin 3) K) (y r z : A) (a : K) :
    MvPolynomial.eval₂Hom (algebraMap K A)
        ![y, r + algebraMap K A a * z, z] (shearAlgHom a F) =
      MvPolynomial.eval₂Hom (algebraMap K A) ![y, r, z] F := by
  have hhom :
      (MvPolynomial.eval₂Hom (algebraMap K A)
          ![y, r + algebraMap K A a * z, z]).comp
          (shearAlgHom a).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap K A) ![y, r, z] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [RingHom.comp_apply, shearAlgHom]
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, shearAlgHom, shearImage] <;> ring
  exact RingHom.congr_fun hhom F

/-- Shearing and evaluating in the original quotient gives the original
quotient class. -/
theorem sheared_quotient_eval_eq_mk (a : K)
    (F : MvPolynomial (Fin 3) K) :
    MvPolynomial.eval₂Hom (algebraMap K (CoordinateRing K P))
        (shearedModelCoordinates K P a) (shearAlgHom a F) =
      Ideal.Quotient.mk P F := by
  rw [show shearedModelCoordinates K P a =
      ![quotientCoordinate K P 0,
        quotientCoordinate K P 1 +
          algebraMap K (CoordinateRing K P) a * quotientCoordinate K P 2,
        quotientCoordinate K P 2] by
          funext i
          fin_cases i <;> rfl,
    eval₂Hom_shear_at_add]
  have hx : (![quotientCoordinate K P 0, quotientCoordinate K P 1,
      quotientCoordinate K P 2] : Fin 3 → CoordinateRing K P) =
        quotientCoordinate K P := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact quotient_eval_eq_mk K P F

/-- Rectangular support after the shear. -/
def shearedCap (cap : Fin 3 → ℕ) : Fin 3 → ℕ :=
  ![cap 0, cap 1, cap 2 + cap 1]

theorem shear_degree_caps (a : K) (F : MvPolynomial (Fin 3) K)
    (cap : Fin 3 → ℕ) (hcap : ∀ i, F.degreeOf i ≤ cap i) :
    ∀ i, (shearAlgHom a F).degreeOf i ≤ shearedCap cap i := by
  intro i
  fin_cases i
  · exact (shear_degreeOf_zero_le a F).trans (hcap 0)
  · exact (shear_degreeOf_one_le a F).trans (hcap 1)
  · exact (shear_degreeOf_two_le a F).trans
      (Nat.add_le_add (hcap 2) (hcap 1))

variable [IsAlgClosed K]

/-- One unchanged literal coordinate, packaged using only finiteness of all
projections and separability of this particular projection.  This avoids
assuming that the discarded `R` projection is separable. -/
def literalCoordinateDataAt
    (hfinite : ProjectionsFinite K P) (i : Fin 3)
    (hsep : ∀ hi : Transcendental K (coordinate K P i),
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P i hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P)) :
    Coordinate K (CoordinateField K P) :=
  if hi : Transcendental K (coordinate K P i) then
    Sum.inr {
      embedding := rationalBaseEmbedding K P i hi
      finite := hfinite i hi
      separable := hsep hi }
  else
    Sum.inl ((coordinate_eq_scalar_of_isAlgebraic K P i (not_not.mp hi)).choose)

theorem literalCoordinateDataAt_value
    (hfinite : ProjectionsFinite K P) (i : Fin 3)
    (hsep : ∀ hi : Transcendental K (coordinate K P i),
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P i hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P)) :
    coordinateValue K (CoordinateField K P)
      (literalCoordinateDataAt K P hfinite i hsep) = coordinate K P i := by
  unfold literalCoordinateDataAt
  split_ifs with hi
  · exact rational_variable_image K P i hi
  · exact (coordinate_eq_scalar_of_isAlgebraic K P i
      (not_not.mp hi)).choose_spec

theorem literalCoordinateDataAt_degree
    (hfinite : ProjectionsFinite K P) (i : Fin 3)
    (hsep : ∀ hi : Transcendental K (coordinate K P i),
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P i hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P)) :
    coordinateDegree K (CoordinateField K P)
      (literalCoordinateDataAt K P hfinite i hsep) =
        actualCoordinateDegree K P i := by
  unfold literalCoordinateDataAt actualCoordinateDegree
  split_ifs <;> rfl

/-- The literal sheared coordinate in the fraction field.  Scalar notation
matches the global Kähler-shear theorem definitionally. -/
def shearedFieldCoordinate (a : K) : CoordinateField K P :=
  coordinate K P 1 + a • coordinate K P 2

/-- The literal S projection in the unchanged affine quotient. -/
def shearProjection
    (a : K)
    (hS : Transcendental K (shearedFieldCoordinate K P a))
    (hfiniteS :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        (elementEmbedding K (CoordinateField K P)
          (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) (CoordinateField K P))
    (hsepS :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        (elementEmbedding K (CoordinateField K P)
          (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P)) :
    AffineSeparableProjection K (CoordinateRing K P) (CoordinateField K P) where
  modelValue := quotientCoordinate K P 1 +
    algebraMap K (CoordinateRing K P) a * quotientCoordinate K P 2
  embedding := elementEmbedding K (CoordinateField K P)
    (shearedFieldCoordinate K P a) hS
  value_eq := by
    rw [elementEmbedding_variable]
    simp only [shearedFieldCoordinate, Algebra.smul_def, map_add, map_mul,
      quotientCoordinate_fraction, quotientCoordinate_fraction]
    exact congrArg (fun t : CoordinateField K P ↦
      coordinate K P 1 + t * coordinate K P 2)
        (IsScalarTower.algebraMap_apply K (CoordinateRing K P)
          (CoordinateField K P) a)
  finite := hfiniteS
  separable := hsepS

/-- All three pole-count coordinates, with S in the middle. -/
def shearedCoordinateData
    (hfinite : ProjectionsFinite K P)
    (hsepY : ∀ hi : Transcendental K (coordinate K P 0),
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P 0 hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P))
    (hsepZ : ∀ hi : Transcendental K (coordinate K P 2),
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P 2 hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P))
    (a : K)
    (hS : Transcendental K (shearedFieldCoordinate K P a))
    (hfiniteS :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        (elementEmbedding K (CoordinateField K P)
          (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) (CoordinateField K P))
    (hsepS :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        (elementEmbedding K (CoordinateField K P)
          (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P)) :
    Fin 3 → Coordinate K (CoordinateField K P) :=
  triple (literalCoordinateDataAt K P hfinite 0 hsepY)
    (Sum.inr {
      embedding := elementEmbedding K (CoordinateField K P)
        (shearedFieldCoordinate K P a) hS
      finite := hfiniteS
      separable := hsepS })
    (literalCoordinateDataAt K P hfinite 2 hsepZ)

theorem shearedCoordinateData_value
    (hfinite : ProjectionsFinite K P)
    (hsepY : ∀ hi : Transcendental K (coordinate K P 0),
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P 0 hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P))
    (hsepZ : ∀ hi : Transcendental K (coordinate K P 2),
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P 2 hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P))
    (a : K)
    (hS : Transcendental K (shearedFieldCoordinate K P a))
    (hfiniteS :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        (elementEmbedding K (CoordinateField K P)
          (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) (CoordinateField K P))
    (hsepS :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        (elementEmbedding K (CoordinateField K P)
          (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P)) :
    ∀ i, coordinateValue K (CoordinateField K P)
        (shearedCoordinateData K P hfinite hsepY hsepZ a hS hfiniteS hsepS i) =
      algebraMap (CoordinateRing K P) (CoordinateField K P)
        (shearedModelCoordinates K P a i) := by
  intro i
  refine Fin.cases ?_ (fun i₁ ↦ ?_) i
  · change coordinateValue K (CoordinateField K P)
      (literalCoordinateDataAt K P hfinite 0 hsepY) =
        algebraMap (CoordinateRing K P) (CoordinateField K P)
          (quotientCoordinate K P 0)
    rw [literalCoordinateDataAt_value, quotientCoordinate_fraction]
  · refine Fin.cases ?_ (fun i₂ ↦ ?_) i₁
    · change
      (elementEmbedding K (CoordinateField K P)
        (shearedFieldCoordinate K P a) hS)
          (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) =
        algebraMap (CoordinateRing K P) (CoordinateField K P)
          (quotientCoordinate K P 1 +
            algebraMap K (CoordinateRing K P) a * quotientCoordinate K P 2)
      rw [elementEmbedding_variable]
      simp only [shearedFieldCoordinate, Algebra.smul_def, map_add, map_mul,
        quotientCoordinate_fraction, quotientCoordinate_fraction]
      exact congrArg (fun t : CoordinateField K P ↦
        coordinate K P 1 + t * coordinate K P 2)
          (IsScalarTower.algebraMap_apply K (CoordinateRing K P)
            (CoordinateField K P) a)
    · refine Fin.cases ?_ (fun i₃ ↦ Fin.elim0 i₃) i₂
      change coordinateValue K (CoordinateField K P)
        (literalCoordinateDataAt K P hfinite 2 hsepZ) =
          algebraMap (CoordinateRing K P) (CoordinateField K P)
            (quotientCoordinate K P 2)
      rw [literalCoordinateDataAt_value, quotientCoordinate_fraction]

theorem shearedCoordinateData_degree
    (hfinite : ProjectionsFinite K P)
    (hsepY : ∀ hi : Transcendental K (coordinate K P 0),
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P 0 hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P))
    (hsepZ : ∀ hi : Transcendental K (coordinate K P 2),
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P 2 hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P))
    (a : K)
    (hS : Transcendental K (shearedFieldCoordinate K P a))
    (hfiniteS :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        (elementEmbedding K (CoordinateField K P)
          (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) (CoordinateField K P))
    (hsepS :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        (elementEmbedding K (CoordinateField K P)
          (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P)) :
    coordinateDegree K (CoordinateField K P)
        (shearedCoordinateData K P hfinite hsepY hsepZ a hS hfiniteS hsepS 0) =
          actualCoordinateDegree K P 0 ∧
      coordinateDegree K (CoordinateField K P)
        (shearedCoordinateData K P hfinite hsepY hsepZ a hS hfiniteS hsepS 1) =
          (letI : Algebra (RatFunc K) (CoordinateField K P) :=
            (elementEmbedding K (CoordinateField K P)
              (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
           Module.finrank (RatFunc K) (CoordinateField K P)) ∧
      coordinateDegree K (CoordinateField K P)
        (shearedCoordinateData K P hfinite hsepY hsepZ a hS hfiniteS hsepS 2) =
          actualCoordinateDegree K P 2 := by
  constructor
  · exact literalCoordinateDataAt_degree K P hfinite 0 hsepY
  constructor
  · rfl
  · exact literalCoordinateDataAt_degree K P hfinite 2 hsepZ

/-- Actual original affine points satisfy the exact sheared rectangular
zero count. -/
theorem finite_zero_points_le_global_sheared_box
    (hfinite : ProjectionsFinite K P)
    (hsepY : ∀ hi : Transcendental K (coordinate K P 0),
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P 0 hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P))
    (hsepZ : ∀ hi : Transcendental K (coordinate K P 2),
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P 2 hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P))
    (a : K)
    (hS : Transcendental K (shearedFieldCoordinate K P a))
    (hfiniteS :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        (elementEmbedding K (CoordinateField K P)
          (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) (CoordinateField K P))
    (hsepS :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        (elementEmbedding K (CoordinateField K P)
          (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P))
    (F : MvPolynomial (Fin 3) K) (hF : F ∉ P)
    (cap : Fin 3 → ℕ) (hcap : ∀ i, F.degreeOf i ≤ cap i)
    (S : Finset (Fin 3 → K))
    (hSP : ∀ v ∈ S, P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hSF : ∀ v ∈ S, MvPolynomial.aeval v F = 0) :
    S.card ≤ cap 0 * actualCoordinateDegree K P 0 +
      cap 1 *
        (letI : Algebra (RatFunc K) (CoordinateField K P) :=
          (elementEmbedding K (CoordinateField K P)
            (shearedFieldCoordinate K P a) hS).toRingHom.toAlgebra
         Module.finrank (RatFunc K) (CoordinateField K P)) +
      (cap 2 + cap 1) * actualCoordinateDegree K P 2 := by
  classical
  let q := shearProjection K P a hS hfiniteS hsepS
  let c := shearedCoordinateData K P hfinite hsepY hsepZ a hS hfiniteS hsepS
  let x := shearedModelCoordinates K P a
  let B := shearAlgHom a F
  have hc : ∀ i, coordinateValue K (CoordinateField K P) (c i) =
      algebraMap (CoordinateRing K P) (CoordinateField K P) (x i) :=
    shearedCoordinateData_value K P hfinite hsepY hsepZ a hS hfiniteS hsepS
  have hBcap : ∀ i, B.degreeOf i ≤ shearedCap cap i :=
    shear_degree_caps K a F cap hcap
  have hBne : MvPolynomial.eval₂Hom (algebraMap K (CoordinateRing K P)) x B ≠ 0 := by
    rw [show MvPolynomial.eval₂Hom (algebraMap K (CoordinateRing K P)) x B =
      Ideal.Quotient.mk P F from sheared_quotient_eval_eq_mk K P a F]
    intro hzero
    exact hF (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  let liftPoint : {v : Fin 3 → K // v ∈ S} → (CoordinateRing K P →ₐ[K] K) :=
    fun v ↦ pointHom K P ⟨v.1, hSP v.1 v.2⟩
  have hinj : Function.Injective liftPoint := by
    intro v w hvw
    have h := pointHom_injective K P hvw
    apply Subtype.ext
    exact congrArg (fun z : PointOn K P ↦ z.val) h
  let points := S.attach.image liftPoint
  have hpoints : ∀ ψ ∈ points,
      ψ (MvPolynomial.eval₂Hom (algebraMap K (CoordinateRing K P)) x B) = 0 := by
    intro ψ hψ
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hψ
    rw [show MvPolynomial.eval₂Hom (algebraMap K (CoordinateRing K P)) x B =
      Ideal.Quotient.mk P F from sheared_quotient_eval_eq_mk K P a F,
      pointHom_mk]
    exact hSF v.1 v.2
  have hcount :=
    AffineSeparableProjection.finite_model_zero_points_le_box
      K (CoordinateRing K P) (CoordinateField K P)
        q x c hc (shearedCap cap) B hBcap hBne points hpoints
  have hcard : points.card = S.card := by
    change (S.attach.image liftPoint).card = S.card
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  rw [hcard] at hcount
  have hdegrees := shearedCoordinateData_degree K P hfinite hsepY hsepZ
    a hS hfiniteS hsepS
  simp only [c, shearedCap, Fin.sum_univ_three] at hcount
  rw [hdegrees.1, hdegrees.2.1, hdegrees.2.2] at hcount
  norm_num at hcount
  exact_mod_cast hcount

end

end ProximityPrize.SubmissionLower.GlobalShearZeroCountResearch

#print axioms ProximityPrize.SubmissionLower.GlobalShearZeroCountResearch.eval₂Hom_shear_at_add
#print axioms ProximityPrize.SubmissionLower.GlobalShearZeroCountResearch.sheared_quotient_eval_eq_mk
#print axioms ProximityPrize.SubmissionLower.GlobalShearZeroCountResearch.finite_zero_points_le_global_sheared_box

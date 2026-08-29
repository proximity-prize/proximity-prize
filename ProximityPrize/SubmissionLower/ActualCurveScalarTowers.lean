import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualCurveRationalProjection

/-! .









 -/

namespace ProximityPrize.SubmissionLower.ActualCurveScalarTowers

open ActualCurveCoordinateField ActualCurveRationalProjection

noncomputable section

variable (K : Type) [Field K] (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]

abbrev polynomialBaseAlgebra (i : Fin 3) :
    Algebra (Polynomial K) (CoordinateField K P) :=
  (Polynomial.aeval (coordinate K P i)).toRingHom.toAlgebra

theorem polynomial_algebraMap_eq (i : Fin 3) (f : Polynomial K) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    algebraMap (Polynomial K) (CoordinateField K P) f =
      Polynomial.aeval (coordinate K P i) f := rfl

theorem polynomialBaseScalarTower (i : Fin 3) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    IsScalarTower K (Polynomial K) (CoordinateField K P) := by
  letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
  exact IsScalarTower.of_algebraMap_eq fun c =>
    ((Polynomial.aeval (coordinate K P i)).commutes c).symm

theorem polynomialBase_injective (i : Fin 3)
    (hi : Transcendental K (coordinate K P i)) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    Function.Injective (algebraMap (Polynomial K) (CoordinateField K P)) :=
  transcendental_iff_injective.mp hi

theorem polynomial_variable_image (i : Fin 3) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    algebraMap (Polynomial K) (CoordinateField K P) Polynomial.X = coordinate K P i := by
  exact Polynomial.aeval_X _

theorem polynomialRationalScalarTower (i : Fin 3)
    (hi : Transcendental K (coordinate K P i)) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
    IsScalarTower (Polynomial K) (RatFunc K) (CoordinateField K P) := by
  letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
  letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
  exact IsScalarTower.of_algebraMap_eq fun f =>
    (rationalBaseEmbedding_polynomial K P i hi f).symm

/-- .
 -/
theorem actual_scalar_towers (i : Fin 3)
    (hi : Transcendental K (coordinate K P i)) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
    IsScalarTower K (Polynomial K) (CoordinateField K P) ∧
      IsScalarTower (Polynomial K) (RatFunc K) (CoordinateField K P) ∧
      IsScalarTower K (RatFunc K) (CoordinateField K P) := by
  exact ⟨polynomialBaseScalarTower K P i,
    polynomialRationalScalarTower K P i hi, rationalBaseScalarTower K P i hi⟩

/-- . -/
def quotientCoordinate (i : Fin 3) : CoordinateRing K P :=
  Ideal.Quotient.mk P (MvPolynomial.X i)

abbrev quotientPolynomialAlgebra (i : Fin 3) :
    Algebra (Polynomial K) (CoordinateRing K P) :=
  (Polynomial.aeval (quotientCoordinate K P i)).toRingHom.toAlgebra

theorem quotientBaseScalarTower (i : Fin 3) :
    letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
    IsScalarTower K (Polynomial K) (CoordinateRing K P) := by
  letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
  exact IsScalarTower.of_algebraMap_eq fun c =>
    ((Polynomial.aeval (quotientCoordinate K P i)).commutes c).symm

theorem quotientCoordinate_fraction (i : Fin 3) :
    algebraMap (CoordinateRing K P) (CoordinateField K P) (quotientCoordinate K P i) =
      coordinate K P i := rfl

theorem quotient_polynomial_fraction (i : Fin 3) (f : Polynomial K) :
    algebraMap (CoordinateRing K P) (CoordinateField K P)
        (Polynomial.aeval (quotientCoordinate K P i) f) =
      Polynomial.aeval (coordinate K P i) f := by
  have hhom :
      (IsScalarTower.toAlgHom K (CoordinateRing K P) (CoordinateField K P)).comp
          (Polynomial.aeval (quotientCoordinate K P i)) =
        Polynomial.aeval (coordinate K P i) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X]
    rfl
  exact AlgHom.congr_fun hhom f

theorem quotientFractionScalarTower (i : Fin 3) :
    @IsScalarTower (Polynomial K) (CoordinateRing K P) (CoordinateField K P)
      (quotientPolynomialAlgebra K P i).toSMul
      (inferInstance : Algebra (CoordinateRing K P) (CoordinateField K P)).toSMul
      (polynomialBaseAlgebra K P i).toSMul := by
  letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
  letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
  exact IsScalarTower.of_algebraMap_eq fun f =>
    (quotient_polynomial_fraction K P i f).symm

theorem quotientBase_injective (i : Fin 3)
    (hi : Transcendental K (coordinate K P i)) :
    letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
    Function.Injective (algebraMap (Polynomial K) (CoordinateRing K P)) := by
  letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
  intro f g hfg
  apply transcendental_iff_injective.mp hi
  rw [← quotient_polynomial_fraction K P i f, ← quotient_polynomial_fraction K P i g]
  exact congrArg (algebraMap (CoordinateRing K P) (CoordinateField K P)) hfg

end


end ProximityPrize.SubmissionLower.ActualCurveScalarTowers

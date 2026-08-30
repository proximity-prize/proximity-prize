import ProximityPrize.SubmissionLower.ActualCurveRationalProjection

namespace ProximityPrize.SubmissionLower.ActualCurveScalarTowers

open ActualCurveCoordinateField ActualCurveRationalProjection

noncomputable section

variable (K : Type) [Field K] (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]

abbrev polynomialBaseAlgebra (i : Fin 3) :
    Algebra (Polynomial K) (CoordinateField K P) :=
  (Polynomial.aeval (coordinate K P i)).toRingHom.toAlgebra

omit [P.IsPrime] in
theorem polynomialBaseScalarTower (i : Fin 3) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    IsScalarTower K (Polynomial K) (CoordinateField K P) := by
  letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
  exact IsScalarTower.of_algebraMap_eq fun c =>
    ((Polynomial.aeval (coordinate K P i)).commutes c).symm

theorem polynomialRationalScalarTower (i : Fin 3)
    (hi : Transcendental K (coordinate K P i)) :
    letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
    letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
    IsScalarTower (Polynomial K) (RatFunc K) (CoordinateField K P) := by
  letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
  letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
  exact IsScalarTower.of_algebraMap_eq fun f =>
    (rationalBaseEmbedding_polynomial K P i hi f).symm

def quotientCoordinate (i : Fin 3) : CoordinateRing K P :=
  Ideal.Quotient.mk P (MvPolynomial.X i)

abbrev quotientPolynomialAlgebra (i : Fin 3) :
    Algebra (Polynomial K) (CoordinateRing K P) :=
  (Polynomial.aeval (quotientCoordinate K P i)).toRingHom.toAlgebra

omit [P.IsPrime] in
theorem quotientBaseScalarTower (i : Fin 3) :
    letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
    IsScalarTower K (Polynomial K) (CoordinateRing K P) := by
  letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
  exact IsScalarTower.of_algebraMap_eq fun c =>
    ((Polynomial.aeval (quotientCoordinate K P i)).commutes c).symm

omit [P.IsPrime] in
theorem quotientCoordinate_fraction (i : Fin 3) :
    algebraMap (CoordinateRing K P) (CoordinateField K P) (quotientCoordinate K P i) =
      coordinate K P i := rfl

omit [P.IsPrime] in
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

omit [P.IsPrime] in
theorem quotientFractionScalarTower (i : Fin 3) :
    @IsScalarTower (Polynomial K) (CoordinateRing K P) (CoordinateField K P)
      (quotientPolynomialAlgebra K P i).toSMul
      (inferInstance : Algebra (CoordinateRing K P) (CoordinateField K P)).toSMul
      (polynomialBaseAlgebra K P i).toSMul := by
  letI : Algebra (Polynomial K) (CoordinateRing K P) := quotientPolynomialAlgebra K P i
  letI : Algebra (Polynomial K) (CoordinateField K P) := polynomialBaseAlgebra K P i
  exact IsScalarTower.of_algebraMap_eq fun f =>
    (quotient_polynomial_fraction K P i f).symm

end

end ProximityPrize.SubmissionLower.ActualCurveScalarTowers

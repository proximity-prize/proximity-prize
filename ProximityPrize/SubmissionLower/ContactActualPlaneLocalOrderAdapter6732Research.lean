import ProximityPrize.SubmissionLower.ActualPlaneRelationMaximal6732Research
namespace ProximityPrize.SubmissionLower.ContactActualPlaneLocalOrderAdapter6732Research
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualPlaneCoordinateKernel ActualPlaneCoordinateDegree
open TrivariateRationalCollection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K:Type) [Field K]
def planeDenominators (order:Fin 3 ≃ Fin 3):Submonoid (Original K):=
  (coefficientDenominators K).comap (collect K order).toMonoidHom
@[reducible] def rationalPolynomialAlgebra (order:Fin 3 ≃ Fin 3):
    Algebra (Original K) (RationalPolynomials K):=
  (rationalMap K order).toAlgebra
@[reducible] def planeAlgebra (order:Fin 3 ≃ Fin 3):
    Algebra (Original K) (PlaneRing K):=
  (planeMap K order).toAlgebra
theorem rationalPolynomialLocalization (order:Fin 3 ≃ Fin 3):
    letI:=rationalPolynomialAlgebra K order
    IsLocalization (planeDenominators K order) (RationalPolynomials K):=by
  letI:=rationalPolynomialAlgebra K order
  letI:Algebra (Collected K) (RationalPolynomials K):=
    MvPolynomial.algebraMvPolynomial
  letI:IsLocalization (coefficientDenominators K) (RationalPolynomials K):=
    MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)
  apply IsLocalization.of_ringEquiv_left
    (R:=Original K) (S:=Collected K) (K:=RationalPolynomials K)
    (M₁:=coefficientDenominators K) (M₂:=planeDenominators K order)
    (collect K order).toRingEquiv
  · exact Submonoid.map_comap_eq_of_surjective
      (collect K order).surjective (coefficientDenominators K)
  · intro F
    rfl
theorem planeRingLocalization (order:Fin 3 ≃ Fin 3):
    letI:=planeAlgebra K order
    IsLocalization (planeDenominators K order) (PlaneRing K):=by
  letI:=rationalPolynomialAlgebra K order
  let aPlane:=planeAlgebra K order
  letI:Algebra (Original K) (PlaneRing K):=aPlane
  letI:SMul (Original K) (PlaneRing K):=aPlane.toSMul
  letI:IsLocalization (planeDenominators K order) (RationalPolynomials K):=
    rationalPolynomialLocalization K order
  let e:RationalPolynomials K ≃ₐ[Original K] PlaneRing K:={
    bivariateEquiv (RatFunc K) with
    commutes':=fun F => rfl}
  exact IsLocalization.isLocalization_of_algEquiv
    (planeDenominators K order) e
end
end ProximityPrize.SubmissionLower.ContactActualPlaneLocalOrderAdapter6732Research

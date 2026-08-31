import ProximityPrize.SubmissionLower.ActualPlaneRelationMaximal6732Research
import ProximityPrize.SubmissionLower.ArbitraryPlaneEvaluationFamilyResearch
namespace ProximityPrize.SubmissionLower.ContactPlaneRelationCoefficientFiber6733Research
open ActualPlaneCoordinateKernel ArbitraryPlaneEvaluationFamilyResearch
open ArbitraryRationalProjectionResearch
open ActualPlaneRelationMaximal6732Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
variable (order:Fin 3 ≃ Fin 3)
variable (e:MvPolynomial (Fin 3) K →ₐ[K] L)
variable (ht:Transcendental K (e (MvPolynomial.X (order 0))))
abbrev CoefficientRing:=Polynomial (RatFunc K)
def projectedFactor:Polynomial (RatFunc K):=
  letI:Algebra (RatFunc K) L:=
    (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
  minpoly (RatFunc K) (e (MvPolynomial.X (order 2)))
theorem planeEvaluation_comp_C:
    (planeEvaluation K L order e ht).comp
      (Polynomial.C:CoefficientRing K →+*PlaneRing K)=
        Polynomial.eval₂RingHom
          (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom
          (e (MvPolynomial.X (order 2))):=by
  letI:Algebra (RatFunc K) L:=
    (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
  apply Polynomial.ringHom_ext
  · intro c
    change planeEvaluation K L order e ht
        (Polynomial.C (Polynomial.C c))=
      Polynomial.aeval (e (MvPolynomial.X (order 2))) (Polynomial.C c)
    rw [planeEvaluation_C_C,Polynomial.aeval_C]
    rfl
  · change planeEvaluation K L order e ht (Polynomial.C Polynomial.X)=
      Polynomial.aeval (e (MvPolynomial.X (order 2))) Polynomial.X
    rw [planeEvaluation_C_X,Polynomial.aeval_X]
theorem relationKernel_comap_C:
    (relationKernel K L order e ht).comap
      (Polynomial.C:CoefficientRing K →+*PlaneRing K)=
        Ideal.span {projectedFactor K L order e ht}:=by
  letI:Algebra (RatFunc K) L:=
    (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
  rw [relationKernel,RingHom.comap_ker,planeEvaluation_comp_C,
    show Polynomial.eval₂RingHom
      (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom
      (e (MvPolynomial.X (order 2)))=
        (Polynomial.aeval (e (MvPolynomial.X (order 2)))).toRingHom from rfl]
  change RingHom.ker (Polynomial.aeval (e (MvPolynomial.X (order 2))))=
    Ideal.span {minpoly (RatFunc K) (e (MvPolynomial.X (order 2)))}
  rw [minpoly.ker_aeval_eq_span_minpoly]
theorem projectedFactor_monic
    (hfinite:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L):
    (projectedFactor K L order e ht).Monic:=by
  letI:Algebra (RatFunc K) L:=
    (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
  letI:FiniteDimensional (RatFunc K) L:=hfinite
  exact minpoly.monic (IsIntegral.of_finite _ _)
theorem projectedFactor_irreducible
    (hfinite:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L):
    Irreducible (projectedFactor K L order e ht):=
  by
    letI:Algebra (RatFunc K) L:=
      (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
    letI:FiniteDimensional (RatFunc K) L:=hfinite
    exact minpoly.irreducible (IsIntegral.of_finite _ _)
theorem relationKernel_isMaximal
    (hfinite:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L)
    (hgen:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
    (relationKernel K L order e ht).IsMaximal:=by
  letI:Algebra (RatFunc K) L:=
    (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
  letI:FiniteDimensional (RatFunc K) L:=hfinite
  apply RingHom.ker_isMaximal_of_surjective
  exact planeEvaluation_surjective_of_finite_generatingPair
    (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) hgen
end
end ProximityPrize.SubmissionLower.ContactPlaneRelationCoefficientFiber6733Research

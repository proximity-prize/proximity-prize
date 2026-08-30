import ProximityPrize.SubmissionLower.O
namespace ProximityPrize.SubmissionLower.ContactFlagPlaneIndexedCost6733Research
open ActualCurveCoordinateField ActualPlaneCoordinateKernel ContactRegularComponentCover
open ContactFlagAffineFamilyDegree6543Research
open ContactFlagResidueDegreeCostAdapter6732Research
open ContactAdaptiveProjectionCoordinateResearch CoordinateBoxZeroCount
open ContactFlagPlaneIndexedFiber6733Research
open ContactFlagPlaneIndexedResidueWeight6733Research
open ContactPlaneRelationCoefficientFiber6733Research
open ContactFlagPlaneSurfaceLocalAdapter6732Research
open ArbitraryPlaneEvaluationFamilyResearch
open ActualPlaneRelationMaximal6732Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
variable {A:Type}
variable (component:A → RegularComponent Omega G T H)
variable (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hgen in
theorem indexed_coordinateDegree_eq_factorDegree_mul_planeWeight
   (hgate:∀ a:A,∀ hx:Transcendental Omega
       (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))),
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))∧
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega (component a).1)))
   (a:A):
   coordinateDegree Omega (CoordinateField Omega (component a).1)
     (coordinateOfGate
       (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0)))
       (hgate a))=
     (indexedComponentFactor component lam mu nu order ht a).natDegree*
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a:=by
 rw [coordinateOfGate_degree_of_transcendental _ (hgate a) (ht a)]
 let F:=RatFunc Omega
 let L:=CoordinateField Omega (component a).1
 let e:=flagEvaluation Omega (component a).1 lam mu nu
 let q:=projectedFactor Omega L order e (ht a)
 let J:=relationKernel Omega L order e (ht a)
 letI:Algebra F L:=flagBaseAlgebra Omega (component a).1
   lam mu nu order (ht a)
 letI:FiniteDimensional F L:=hfinite a
 letI:J.IsMaximal:=relationKernel_isMaximal Omega L order e (ht a)
   (hfinite a) (hgen a)
 let aResidue:=residueAlgebra q J
   (relationKernel_comap_C Omega L order e (ht a))
 letI:Algebra (AdjoinRoot q) (PlaneRing Omega ⧸ J):=aResidue
 letI:SMul (AdjoinRoot q) (PlaneRing Omega ⧸ J):=aResidue.toSMul
 let targetSemiring:Semiring (PlaneRing Omega ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing Omega ⧸ J):=targetSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing Omega ⧸ J):=Algebra.toModule
 have hq:Irreducible q:=projectedFactor_irreducible Omega L order e
   (ht a) (hfinite a)
 let phi:PlaneRing Omega →ₐ[F] L:={
   toRingHom:=planeEvaluation Omega L order e (ht a)
   commutes':=fun c => by
     change planeEvaluation Omega L order e (ht a)
       (Polynomial.C (Polynomial.C c))=algebraMap F L c
     rw [planeEvaluation_C_C]
     rfl}
 have hsurj:Function.Surjective phi:=by
   change Function.Surjective
     (PlaneFunctionFieldDegree.planeEval F L
       (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))))
   exact planeEvaluation_surjective_of_finite_generatingPair
     (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) (hgen a)
 let eqv:(PlaneRing Omega ⧸ J) ≃ₐ[F] L:=by
   change (PlaneRing Omega ⧸ RingHom.ker phi) ≃ₐ[F] L
   exact Ideal.quotientKerAlgEquivOfSurjective hsurj
 have hquot:Module.finrank F (PlaneRing Omega ⧸ J)=
     Module.finrank F L:=eqv.toLinearEquiv.finrank_eq
 change Module.finrank F L=q.natDegree*
   indexedPlaneResidueWeight component lam mu nu order ht hfinite a
 rw [show indexedPlaneResidueWeight component lam mu nu order ht hfinite a=
     Module.finrank (AdjoinRoot q) (PlaneRing Omega ⧸ J) by rfl]
 calc
   Module.finrank F L=Module.finrank F (PlaneRing Omega ⧸ J):=hquot.symm
   _=q.natDegree*Module.finrank (AdjoinRoot q) (PlaneRing Omega ⧸ J):=
     quotient_finrank_eq_natDegree_mul_residue_finrank q hq J
       (relationKernel_comap_C Omega L order e (ht a))
end
end ProximityPrize.SubmissionLower.ContactFlagPlaneIndexedCost6733Research

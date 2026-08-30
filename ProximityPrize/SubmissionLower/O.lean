import ProximityPrize.SubmissionLower.Y9
namespace ProximityPrize.SubmissionLower.ContactFlagPlaneIndexedResidueWeight6733Research
open ActualPlaneCoordinateKernel ArbitraryPlaneEvaluationFamilyResearch
open ActualCurveCoordinateField ContactRegularComponentCover
open ContactFlagAffineFamilyDegree6543Research ContactFlagResidueDegreeCostAdapter6732Research
open ContactPlaneRelationCoefficientFiber6733Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega:Type} [Field Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
variable {A:Type} (component:A → RegularComponent Omega G T H)
variable (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
noncomputable def indexedPlaneResidueWeight (a:A):ℕ:=by
 let L:=CoordinateField Omega (component a).1
 let e:=flagEvaluation Omega (component a).1 lam mu nu
 let q:=projectedFactor Omega L order e (ht a)
 let J:=relationKernel Omega L order e (ht a)
 letI:Fact (Irreducible q):=
   ⟨projectedFactor_irreducible Omega L order e (ht a) (hfinite a)⟩
 let a0:=residueAlgebra q J (relationKernel_comap_C Omega L order e (ht a))
 letI:Algebra (AdjoinRoot q) (PlaneRing Omega ⧸ J):=a0
 letI:SMul (AdjoinRoot q) (PlaneRing Omega ⧸ J):=a0.toSMul
 let targetSemiring:Semiring (PlaneRing Omega ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing Omega ⧸ J):=targetSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing Omega ⧸ J):=Algebra.toModule
 exact Module.finrank (AdjoinRoot q) (PlaneRing Omega ⧸ J)
end
end ProximityPrize.SubmissionLower.ContactFlagPlaneIndexedResidueWeight6733Research

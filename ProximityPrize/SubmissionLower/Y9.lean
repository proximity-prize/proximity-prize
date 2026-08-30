import ProximityPrize.SubmissionLower.N
namespace ProximityPrize.SubmissionLower.ContactFlagPlaneIndexedFiber6733Research
open scoped Classical BigOperators
open ActualPlaneCoordinateKernel ArbitraryPlaneEvaluationFamilyResearch
open ActualCurveCoordinateField ArbitraryRationalProjectionResearch
open ContactRegularComponentCover
open ContactFlagTriangularProjectionResearch ContactFlagAffineFamilyDegree6543Research
open ContactFlagResidueDegreeCostAdapter6732Research
open ContactFlagPlaneFiberPrimary6733Research
open ActualPlaneRelationMaximal6732Research
open ContactPlaneRelationCoefficientFiber6733Research
open ContactPlaneLocalOrderPrimary6732Research
open ContactLocalizedPlaneRelation6733Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
variable {A:Type} [Fintype A]
variable (component:A → RegularComponent Omega G T H)
variable (hcomponent:Function.Injective component)
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
def indexedComponentFactor (a:A):Polynomial (RatFunc Omega):=
 projectedFactor Omega (CoordinateField Omega (component a).1) order
   (flagEvaluation Omega (component a).1 lam mu nu) (ht a)
abbrev IndexedFactorFiber (q:Polynomial (RatFunc Omega)):=
 {a:A//q=indexedComponentFactor component lam mu nu order ht a}
def indexedFiberRelation
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   Ideal (Polynomial (FiberCoefficient q hq)):=
 Ideal.map (fiberLocalizePlane q hq)
   (relationKernel Omega (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
def indexedFiberRelationBar
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   Ideal (SurfaceQuotient (fiberLocalizePlane q hq surface)):=
 Ideal.map (Ideal.Quotient.mk
   (Ideal.span {fiberLocalizePlane q hq surface}))
     (indexedFiberRelation component lam mu nu order ht q hq a)
theorem indexedFiberRelation_under
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelation component lam mu nu order ht q hq a).comap
     (fiberLocalizePlane q hq)=
       relationKernel Omega (CoordinateField Omega (component a.1).1) order
         (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1):=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let J:=relationKernel Omega (CoordinateField Omega (component a.1).1) order
   (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
 let f:=fiberLocalizePlane q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hJprime:J.IsPrime:=RingHom.ker_isPrime _
 have hcomap:J.comap c=p:=by
   rw [relationKernel_comap_C]
   exact congrArg (fun r => Ideal.span {r}) a.property.symm
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing Omega))
       (J:Set (PlaneRing Omega)):=by
   rw [Set.disjoint_left]
   intro x hx hxJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp hx
   exact hr (hcomap ▸ hxJ)
 change (Ideal.map f J).comap f=J
 change (Ideal.map (algebraMap (PlaneRing Omega) (Polynomial R)) J).comap
   (algebraMap (PlaneRing Omega) (Polynomial R))=J
 exact IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R) hJprime hdisjoint
include hfinite hgen in
theorem indexedFiberRelation_isMaximal
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let J:=relationKernel Omega (CoordinateField Omega (component a.1).1) order
   (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 have hJmax:J.IsMaximal:=relationKernel_isMaximal Omega
   (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
       (hfinite a.1) (hgen a.1)
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hunder:=indexedFiberRelation_under component lam mu nu order ht q hq a
 letI:((indexedFiberRelation component lam mu nu order ht q hq a).under
     (PlaneRing Omega)).IsMaximal:=by
   change ((indexedFiberRelation component lam mu nu order ht q hq a).comap
     (algebraMap (PlaneRing Omega) (Polynomial R))).IsMaximal
   simpa only [fiberLocalizePlane] using hunder ▸ hJmax
 exact Ideal.IsMaximal.of_isLocalization_of_disjoint
   (p.primeCompl.map c.toMonoidHom)
include hcomponent in
theorem indexedFiberRelation_injective
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Function.Injective
     (indexedFiberRelation component lam mu nu order ht q hq):=by
 intro a b hab
 have hunder:=congrArg (Ideal.comap (fiberLocalizePlane q hq)) hab
 rw [indexedFiberRelation_under component lam mu nu order ht q hq a,
   indexedFiberRelation_under component lam mu nu order ht q hq b] at hunder
 have heval:=congrArg (Ideal.comap (planeMap Omega order)) hunder
 rw [relationKernel_contract,relationKernel_contract] at heval
 have hprime:=congrArg (Ideal.comap (flagAlgHom lam mu nu).toRingHom) heval
 rw [flagEvaluation_kernel_contract,flagEvaluation_kernel_contract] at hprime
 have hcomp:component a.1=component b.1:=Subtype.ext hprime
 exact Subtype.ext (hcomponent hcomp)
include hcomponent hfinite hgen in
theorem indexedFiberRelation_pairwise_coprime
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Pairwise fun a b:IndexedFactorFiber component lam mu nu order ht q =>
     IsCoprime (indexedFiberRelation component lam mu nu order ht q hq a)
       (indexedFiberRelation component lam mu nu order ht q hq b):=by
 intro a b hab
 apply Ideal.isCoprime_iff_sup_eq.mpr
 exact (indexedFiberRelation_isMaximal component lam mu nu order ht hfinite hgen
   q hq a).coprime_of_ne
     (indexedFiberRelation_isMaximal component lam mu nu order ht hfinite hgen
       q hq b)
     (fun heq => hab (indexedFiberRelation_injective
       component hcomponent lam mu nu order ht q hq heq))
end
end ProximityPrize.SubmissionLower.ContactFlagPlaneIndexedFiber6733Research

import ProximityPrize.SubmissionLower.J9
import ProximityPrize.SubmissionLower.C5
namespace ProximityPrize.SubmissionLower.ContactFlagPlaneFiberSurface6733Research
open ActualCurveCoordinateField ActualPlaneCoordinateKernel
open ArbitraryPlaneEvaluationFamilyResearch ContactRegularComponentCover
open ContactFlagTriangularProjectionResearch ContactFlagAffineFamilyDegree6543Research
open ContactFlagResidueDegreeCostAdapter6732Research
open ContactFlagPlaneFiberPrimary6733Research
open ContactPlaneRelationCoefficientFiber6733Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
variable (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ C:RegularComponent Omega G T H,
 Transcendental Omega
   (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
theorem fiber_denominators_disjoint_surface
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   letI:(Ideal.span {q}).IsPrime:=
     (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
   Disjoint
     (((Ideal.span {q}).primeCompl.map
       (Polynomial.C:Polynomial (RatFunc Omega) →+*PlaneRing Omega).toMonoidHom):
       Set (PlaneRing Omega))
     (Ideal.span {planeMap Omega order (flagAlgHom lam mu nu G)}:
       Set (PlaneRing Omega)):=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let J:=relationKernel Omega (CoordinateField Omega C.1.1) order
   (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1)
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 have hcomap:J.comap c=p:=by
   rw [relationKernel_comap_C]
   exact congrArg (fun r => Ideal.span {r}) C.property.symm
 have hsurface:planeMap Omega order (flagAlgHom lam mu nu G)∈J:=by
   change planeEvaluation Omega (CoordinateField Omega C.1.1) order
     (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1)
       (planeMap Omega order (flagAlgHom lam mu nu G))=0
   rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
   change flagEvaluation Omega C.1.1 lam mu nu (flagAlgHom lam mu nu G)=0
   rw [flagEvaluation_flag]
   change G∈RingHom.ker (coordinateEvaluation Omega C.1.1).toRingHom
   rw [coordinateEvaluation_ker]
   exact regularComponent_G_mem Omega G T H C.1
 rw [Set.disjoint_left]
 intro a ha haSurface
 obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp ha
 apply hr
 have hJ:c r∈J:=J.mem_of_dvd
   (Ideal.mem_span_singleton.mp haSurface) hsurface
 have hrJ:r∈J.comap c:=hJ
 rw [hcomap] at hrJ
 exact hrJ
theorem fiberSurface_span_isPrime
   (hG:Irreducible G)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   (Ideal.span {fiberLocalizePlane q hq
     (planeMap Omega order (flagAlgHom lam mu nu G))}).IsPrime:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hglobal:(Ideal.span {planeMap Omega order
     (flagAlgHom lam mu nu G)}).IsPrime:=
   Ideal.isPrime_span_singleton_of_prime
     (transformedSurface_irreducible lam mu nu order hG C.1 (ht C.1)).prime
 have hmapped:=IsLocalization.isPrime_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R)
     (Ideal.span {planeMap Omega order (flagAlgHom lam mu nu G)})
     hglobal (fiber_denominators_disjoint_surface lam mu nu order ht q hq C)
 change (@Ideal.span (Polynomial R) Polynomial.commSemiring.toSemiring
   {algebraMap (PlaneRing Omega) (Polynomial R)
     (planeMap Omega order (flagAlgHom lam mu nu G))}).IsPrime
 simpa only [Ideal.map_span,Set.image_singleton] using hmapped
theorem fiberTail_not_mem_surface
   (hG:Irreducible G) (hproper:¬ G∣T)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   fiberLocalizePlane q hq (planeMap Omega order (flagAlgHom lam mu nu T))∉
     Ideal.span {fiberLocalizePlane q hq
       (planeMap Omega order (flagAlgHom lam mu nu G))}:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 let f:PlaneRing Omega →+*Polynomial R:=fiberLocalizePlane q hq
 let P:=planeMap Omega order (flagAlgHom lam mu nu G)
 let Q:=planeMap Omega order (flagAlgHom lam mu nu T)
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 intro hmem
 have hunder:=IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R)
     (Ideal.isPrime_span_singleton_of_prime
       (transformedSurface_irreducible lam mu nu order hG C.1 (ht C.1)).prime)
     (fiber_denominators_disjoint_surface lam mu nu order ht q hq C)
 have hspanEq:Ideal.map f (Ideal.span {P})=Ideal.span {f P}:=by
   rw [Ideal.map_span]
   simp only [Set.image_singleton]
 have hmem':f Q∈Ideal.map f (Ideal.span {P}):=by
   rwa [hspanEq]
 have hglobal:Q∈Ideal.span {P}:=by
   have hx:Q∈(Ideal.map f (Ideal.span {P})).comap f:=hmem'
   change Q∈(Ideal.map (algebraMap (PlaneRing Omega) (Polynomial R))
     (Ideal.span {P})).under (PlaneRing Omega) at hx
   rwa [hunder] at hx
 exact transformedSurface_not_dvd_tail lam mu nu order hG hproper C.1 (ht C.1)
   (Ideal.mem_span_singleton.mp hglobal)
end
end ProximityPrize.SubmissionLower.ContactFlagPlaneFiberSurface6733Research

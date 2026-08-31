import ProximityPrize.SubmissionLower.N
namespace ProximityPrize.SubmissionLower.RCN102
open scoped Classical BigOperators
open RCN011 RCN021
open RCN002 RCN022
open RCN264
open RCN125 RCN093
open RCN226
open RCN191
open RCN120
open RCN113
open RCN225
open RCN014
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
variable (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ C:RegularComponent Omega G T H,
 Transcendental Omega
   (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
def componentFactor (C:RegularComponent Omega G T H):
   Polynomial (RatFunc Omega):=
 projectedFactor Omega (CoordinateField Omega C.1) order
   (flagEvaluation Omega C.1 lam mu nu) (ht C)
abbrev FactorFiber (q:Polynomial (RatFunc Omega)):=
 {C:RegularComponent Omega G T H//q=componentFactor lam mu nu order ht C}
def fiberRelation
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   Ideal (Polynomial (FiberCoefficient q hq)):=
 Ideal.map (fiberLocalizePlane q hq)
   (relationKernel Omega (CoordinateField Omega C.1.1) order
     (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1))
def fiberRelationBar
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (C:FactorFiber lam mu nu order ht q):
   Ideal (SurfaceQuotient (fiberLocalizePlane q hq surface)):=
 Ideal.map (Ideal.Quotient.mk
   (Ideal.span {fiberLocalizePlane q hq surface}))
     (fiberRelation lam mu nu order ht q hq C)
theorem fiberRelation_under
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   (fiberRelation lam mu nu order ht q hq C).comap
     (fiberLocalizePlane q hq)=
       relationKernel Omega (CoordinateField Omega C.1.1) order
         (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1):=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let J:=relationKernel Omega (CoordinateField Omega C.1.1) order
   (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1)
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
   exact congrArg (fun r => Ideal.span {r}) C.property.symm
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing Omega))
       (J:Set (PlaneRing Omega)):=by
   rw [Set.disjoint_left]
   intro a ha haJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp ha
   exact hr (hcomap ▸ haJ)
 change (Ideal.map f J).comap f=J
 change (Ideal.map (algebraMap (PlaneRing Omega) (Polynomial R)) J).comap
   (algebraMap (PlaneRing Omega) (Polynomial R))=J
 exact IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R) hJprime hdisjoint
theorem fiberRelation_isMaximal
   (hfinite:∀ C:RegularComponent Omega G T H,
     letI:=flagBaseAlgebra Omega C.1 lam mu nu order (ht C)
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))
   (hgen:∀ C:RegularComponent Omega G T H,
     letI:=flagBaseAlgebra Omega C.1 lam mu nu order (ht C)
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 2)),
         flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 1))}:
         Set (CoordinateField Omega C.1))=⊤)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   (fiberRelation lam mu nu order ht q hq C).IsMaximal:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let J:=relationKernel Omega (CoordinateField Omega C.1.1) order
   (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1)
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 have hJmax:J.IsMaximal:=relationKernel_isMaximal Omega
   (CoordinateField Omega C.1.1) order
     (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1)
       (hfinite C.1) (hgen C.1)
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hunder:=fiberRelation_under lam mu nu order ht q hq C
 letI:((fiberRelation lam mu nu order ht q hq C).under
     (PlaneRing Omega)).IsMaximal:=by
   change ((fiberRelation lam mu nu order ht q hq C).comap
     (algebraMap (PlaneRing Omega) (Polynomial R))).IsMaximal
   simpa only [fiberLocalizePlane] using hunder ▸ hJmax
 exact Ideal.IsMaximal.of_isLocalization_of_disjoint
   (p.primeCompl.map c.toMonoidHom)
theorem fiberRelation_injective
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Function.Injective (fiberRelation lam mu nu order ht q hq):=by
 intro C D hCD
 have hunder:=congrArg
   (Ideal.comap (fiberLocalizePlane q hq)) hCD
 rw [fiberRelation_under lam mu nu order ht q hq C,
   fiberRelation_under lam mu nu order ht q hq D] at hunder
 have heval:=congrArg (Ideal.comap (planeMap Omega order)) hunder
 rw [relationKernel_contract,relationKernel_contract] at heval
 have hprime:=congrArg
   (Ideal.comap (flagAlgHom lam mu nu).toRingHom) heval
 rw [flagEvaluation_kernel_contract,flagEvaluation_kernel_contract] at hprime
 apply Subtype.ext
 apply Subtype.ext
 exact hprime
theorem fiberRelation_pairwise_coprime
   (hfinite:∀ C:RegularComponent Omega G T H,
     letI:=flagBaseAlgebra Omega C.1 lam mu nu order (ht C)
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))
   (hgen:∀ C:RegularComponent Omega G T H,
     letI:=flagBaseAlgebra Omega C.1 lam mu nu order (ht C)
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 2)),
         flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 1))}:
         Set (CoordinateField Omega C.1))=⊤)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Pairwise fun C D:FactorFiber lam mu nu order ht q =>
     IsCoprime (fiberRelation lam mu nu order ht q hq C)
       (fiberRelation lam mu nu order ht q hq D):=by
 intro C D hne
 apply Ideal.isCoprime_iff_sup_eq.mpr
 exact (fiberRelation_isMaximal lam mu nu order ht hfinite hgen q hq C).coprime_of_ne
   (fiberRelation_isMaximal lam mu nu order ht hfinite hgen q hq D)
   (fun heq => hne (fiberRelation_injective lam mu nu order ht q hq heq))
end
end ProximityPrize.SubmissionLower.RCN102

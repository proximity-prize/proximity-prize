import ProximityPrize.SubmissionLower.FJ
namespace ProximityPrize.SubmissionLower.RCN191
open RCN011 RCN021
open RCN022
open RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
variable (order:Fin 3 ≃ Fin 3)
variable (e:MvPolynomial (Fin 3) K →ₐ[K] L)
variable (ht:Transcendental K (e (MvPolynomial.X (order 0))))
abbrev CoeffPrime:Ideal (Polynomial (RatFunc K)):=
 Ideal.span {projectedFactor K L order e ht}
theorem coeffPrime_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (CoeffPrime K L order e ht).IsMaximal:=
 PrincipalIdealRing.isMaximal_of_irreducible
   (projectedFactor_irreducible K L order e ht hfinite)
abbrev LocalCoefficient
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):=
 @Localization.AtPrime (Polynomial (RatFunc K)) _
   (CoeffPrime K L order e ht)
   (coeffPrime_isMaximal K L order e ht hfinite).isPrime
local instance localCoefficientSemiring
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Semiring (LocalCoefficient K L order e ht hfinite):=
 (inferInstance:CommRing
   (LocalCoefficient K L order e ht hfinite)).toSemiring
local instance localizedPlaneSemiring
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Semiring (Polynomial (LocalCoefficient K L order e ht hfinite)):=
 (inferInstance:CommRing
   (Polynomial (LocalCoefficient K L order e ht hfinite))).toSemiring
def localizePlane
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   PlaneRing K →+*Polynomial (LocalCoefficient K L order e ht hfinite):=
 Polynomial.mapRingHom
   (algebraMap (Polynomial (RatFunc K))
     (LocalCoefficient K L order e ht hfinite))
def localizedRelation
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Ideal (Polynomial (LocalCoefficient K L order e ht hfinite)):=
 Ideal.map (localizePlane K L order e ht hfinite)
   (relationKernel K L order e ht)
theorem localizedRelation_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   (localizedRelation K L order e ht hfinite).IsMaximal:=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let f:=localizePlane K L order e ht hfinite
 let c:Polynomial (RatFunc K) →+*PlaneRing K:=Polynomial.C
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 have hJmax:J.IsMaximal:=
   relationKernel_isMaximal K L order e ht hfinite hgen
 letI:J.IsPrime:=hJmax.isPrime
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing K))
       (J:Set (PlaneRing K)):=by
   rw [Set.disjoint_left]
   intro a ha haJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp ha
   apply hr
   have hrJ:r∈J.comap c:=haJ
   have hcomap:J.comap c=p:=by
     simpa only [J,c,p] using
       relationKernel_comap_C K L order e ht
   rwa [hcomap] at hrJ
 letI:Algebra (Polynomial (RatFunc K)) Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 letI:Algebra (PlaneRing K) (Polynomial Rp):=
   Polynomial.algebra (Polynomial (RatFunc K)) Rp
 have hf:f=algebraMap (PlaneRing K) (Polynomial Rp):=rfl
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom)
     (Polynomial Rp):=by
   exact Polynomial.isLocalization p.primeCompl Rp
 have hunder:(localizedRelation K L order e ht hfinite).under
     (PlaneRing K)=J:=by
   change (Ideal.map f J).under (PlaneRing K)=J
   rw [hf]
   exact IsLocalization.under_map_of_isPrime_disjoint
     (I:=J) (p.primeCompl.map c.toMonoidHom) (Polynomial Rp)
       hJmax.isPrime hdisjoint
 letI:((localizedRelation K L order e ht hfinite).under
     (PlaneRing K)).IsMaximal:=
   hunder ▸ hJmax
 have hunder':(Ideal.map
     (algebraMap (PlaneRing K) (Polynomial Rp)) J).under (PlaneRing K)=J:=by
   rw [←hf]
   exact hunder
 letI:((Ideal.map (algebraMap (PlaneRing K) (Polynomial Rp)) J).under
     (PlaneRing K)).IsMaximal:=hunder'.symm ▸ hJmax
 change (Ideal.map f J).IsMaximal
 rw [hf]
 exact Ideal.IsMaximal.of_isLocalization_of_disjoint
   (p.primeCompl.map c.toMonoidHom)
abbrev LocalizedPlane
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):=
 Polynomial (LocalCoefficient K L order e ht hfinite)
abbrev LocalizedSurfaceQuotient
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (surface:PlaneRing K):=
 Polynomial (LocalCoefficient K L order e ht hfinite) ⧸
   Ideal.span {localizePlane K L order e ht hfinite surface}
def localizedRelationBar
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (surface:PlaneRing K):
   Ideal (LocalizedSurfaceQuotient K L order e ht hfinite surface):=
 Ideal.map (Ideal.Quotient.mk
   (Ideal.span {localizePlane K L order e ht hfinite surface}))
     (localizedRelation K L order e ht hfinite)
theorem localizedRelationBar_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤)
   (surface:PlaneRing K)
   (hsurface:surface∈relationKernel K L order e ht):
   (localizedRelationBar K L order e ht hfinite surface).IsMaximal:=by
 let J:=localizedRelation K L order e ht hfinite
 let q:=Ideal.Quotient.mk
   (Ideal.span {localizePlane K L order e ht hfinite surface})
 have hJmax:J.IsMaximal:=
   localizedRelation_isMaximal K L order e ht hfinite hgen
 letI:J.IsMaximal:=hJmax
 apply Ideal.IsMaximal.map_of_surjective_of_ker_le
   (f:=q) Ideal.Quotient.mk_surjective
 rw [Ideal.mk_ker,Ideal.span_le]
 intro x hx
 rw [Set.mem_singleton_iff] at hx
 subst x
 exact Ideal.mem_map_of_mem (localizePlane K L order e ht hfinite) hsurface
theorem localizedRelationBar_ne_bot
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (surface tail:PlaneRing K)
   (htail:tail∈relationKernel K L order e ht)
   (hproper:localizePlane K L order e ht hfinite tail∉
     Ideal.span {localizePlane K L order e ht hfinite surface}):
   localizedRelationBar K L order e ht hfinite surface≠⊥:=by
 intro hbot
 have hbar:Ideal.Quotient.mk
     (Ideal.span {localizePlane K L order e ht hfinite surface})
     (localizePlane K L order e ht hfinite tail)∈
       localizedRelationBar K L order e ht hfinite surface:=
   Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ htail)
 rw [hbot,Ideal.mem_bot] at hbar
 exact hproper (Ideal.Quotient.eq_zero_iff_mem.mp hbar)
end
end ProximityPrize.SubmissionLower.RCN191

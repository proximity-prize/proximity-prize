import ProximityPrize.SubmissionLower.FN
import ProximityPrize.SubmissionLower.O
import ProximityPrize.SubmissionLower.C3
namespace ProximityPrize.SubmissionLower.RCN110
open RCN011 RCN021
open RCN002 RCN264
open RCN093 RCN120
open RCN102
open RCN106
open RCN107
open RCN232
open RCN197
open RCN192
open RCN111
open RCN191
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {Omega:Type} [Field Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
variable {A:Type} [Fintype A]
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
include hfinite in
theorem indexedNaturalSurfaceLocal_isLocalHom
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q)
   [hbarMax:(indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal]:
   IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=by
 letI:(polynomialRelationBar (indexedFiberSurface q hq surface)
     (indexedFiberRelation component lam mu nu order ht q hq a)).IsMaximal:=by
   change (indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal
   exact hbarMax
 exact polynomialSurfaceAtPrimeNatural_isLocalHom
   (indexedFiberSurface q hq surface)
   (indexedFiberRelation component lam mu nu order ht q hq a)
   (indexedFiberRelation_comap_C_eq_maximalIdeal
     component lam mu nu order ht hfinite q hq a)
include hfinite hgen in
theorem indexedNaturalSurfaceResidue_finite
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q)
   (hsurface:surface∈relationKernel Omega
     (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   [hbarMax:(indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal]:
   letI:IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
     indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht hfinite
       q hq surface a
   FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
     (IsLocalRing.ResidueField (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=by
 cases a with
 | mk a hqeq =>
   subst q
   let L:=CoordinateField Omega (component a).1
   let e:=flagEvaluation Omega (component a).1 lam mu nu
   let P:=localizePlane Omega L order e (ht a) (hfinite a) surface
   let J:=localizedRelation Omega L order e (ht a) (hfinite a)
   have hcontract:=localizedRelation_comap_C_eq_maximalIdeal Omega L
     order e (ht a) (hfinite a)
   have hsurfaceJ:P∈J:=Ideal.mem_map_of_mem _ hsurface
   letI:(polynomialRelationBar P J).IsMaximal:=by
     change (indexedFiberRelationBar component lam mu nu order ht
       (indexedComponentFactor component lam mu nu order ht a) hq surface
         ⟨a,rfl⟩).IsMaximal
     exact hbarMax
   have hrelFinite:=localizedRelationResidue_finite Omega L order e
     (ht a) (hfinite a) (hgen a)
   exact polynomialSurfaceResidue_finite P J hcontract hsurfaceJ hrelFinite
include hfinite hgen in
theorem indexedNaturalSurfaceResidue_finrank_eq_plane
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q)
   (hsurface:surface∈relationKernel Omega
     (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   [hbarMax:(indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal]:
   letI:IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
     indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht hfinite
       q hq surface a
   Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))=
     indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1:=by
 cases a with
 | mk a hqeq =>
   subst q
   let L:=CoordinateField Omega (component a).1
   let e:=flagEvaluation Omega (component a).1 lam mu nu
   let R:=LocalCoefficient Omega L order e (ht a) (hfinite a)
   let P:=localizePlane Omega L order e (ht a) (hfinite a) surface
   let J:=localizedRelation Omega L order e (ht a) (hfinite a)
   have hcontract:=localizedRelation_comap_C_eq_maximalIdeal Omega L
     order e (ht a) (hfinite a)
   have hsurfaceJ:P∈J:=Ideal.mem_map_of_mem _ hsurface
   letI:(polynomialRelationBar P J).IsMaximal:=by
     change (indexedFiberRelationBar component lam mu nu order ht
       (indexedComponentFactor component lam mu nu order ht a) hq surface
         ⟨a,rfl⟩).IsMaximal
     exact hbarMax
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar P J))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom P J hcontract
   let aRelation:=relationResidueAlgebra J hcontract
   letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=aRelation
   letI:SMul (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=aRelation.toSMul
   let targetSemiring:Semiring (Polynomial R ⧸ J):=inferInstance
   letI:AddCommMonoid (Polynomial R ⧸ J):=targetSemiring.toAddCommMonoid
   letI:Module (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=Algebra.toModule
   calc
     Module.finrank (IsLocalRing.ResidueField R)
         (IsLocalRing.ResidueField (Localization.AtPrime
           (polynomialRelationBar P J)))=
       Module.finrank (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=
         polynomialSurfaceResidue_finrank_eq_relation P J hcontract hsurfaceJ
     _=indexedPlaneResidueWeight component lam mu nu order ht hfinite a:=by
       simpa [indexedPlaneResidueWeight] using
         localizedRelationResidue_finrank_eq_unlocalized Omega L order e
           (ht a) (hfinite a) (hgen a)
end
end ProximityPrize.SubmissionLower.RCN110

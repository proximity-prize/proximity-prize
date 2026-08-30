import ProximityPrize.SubmissionLower.EP
import ProximityPrize.SubmissionLower.EB
namespace ProximityPrize.SubmissionLower.RCN109
open scoped Classical BigOperators
open RCN011 RCN021
open RCN002 RCN264
open RCN093
open RCN102
open RCN106
open RCN107
open RCN143
open RCN307
open RCN014
open RCN120
open RCN236
open RCN110
open RCN111
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
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
include hcomponent hfinite hgen in
theorem indexedFixedFactor_grouped_resultant_power_dvd
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q) (hqMonic:q.Monic)
   (surface tail:PlaneRing Omega) (m n:ℕ)
   [hSurfacePrime:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime]
   [hbarMax:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal]
   [hlocal:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   [hresfinite:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   (hbarne:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥)
   (multiplicity:IndexedFactorFiber component lam mu nu order ht q → ℕ)
   (htail:∀ a,indexedFiberTail q hq tail∈
     Ideal.span {indexedFiberSurface q hq surface} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   (hPcap:(indexedFiberSurface q hq surface).natDegree ≤ m)
   (hQcap:(indexedFiberTail q hq tail).natDegree ≤ n)
   (hresultant:Polynomial.resultant surface tail m n≠0)
   (hPbar:(indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq))≠0):
   q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
     multiplicity a*Module.finrank
       (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a))))∣
     Polynomial.resultant surface tail m n:=by
 letI:DecidableEq (RatFunc Omega):=Classical.decEq _
 letI:(Ideal.span {q}).IsPrime:=
   (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 let weight:IndexedFactorFiber component lam mu nu order ht q → ℕ:=fun a =>
   Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
     (IsLocalRing.ResidueField (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))
 let cert:=indexedWeightedFiberPrimaryPieces component hcomponent lam mu nu
   order ht hfinite hgen q hq surface tail hbarne multiplicity htail
     (hlocal:=hlocal) (hresfinite:=hresfinite)
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     Module.Finite (FiberCoefficient q hq)
       (Polynomial (FiberCoefficient q hq) ⧸ cert.pieces a):=fun a => by
   obtain ⟨M,hMmonic,hMmem⟩:=exists_monic_mem_indexedFiberRelation
     component lam mu nu order ht hfinite hgen q hq a
   apply RCN309.moduleFinite_quotient_of_monic_mem
     (cert.pieces a) (M^multiplicity a) (hMmonic.pow _)
   have hpow:M^multiplicity a∈
       Ideal.span {indexedFiberSurface q hq surface} ⊔
         indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a:=
     (show indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a ≤
         Ideal.span {indexedFiberSurface q hq surface} ⊔
           indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a
       from le_sup_right) (Ideal.pow_mem_pow hMmem (multiplicity a))
   simpa [cert,indexedWeightedFiberPrimaryPieces,
     primaryPiecesCertificateOfMembershipWeighted,mappedPrimaryPiece] using hpow
 letI:Module.Finite (FiberCoefficient q hq)
     (∀ a,Polynomial (FiberCoefficient q hq) ⧸ cert.pieces a):=inferInstance
 exact grouped_resultant_power_dvd_of_primary_pieces_of_surface_mod_ne_zero
   (Ideal.span {q}) q (fun a => multiplicity a*weight a)
     rfl hq hqMonic surface tail m n
     (indexedFiberSurface q hq surface) (indexedFiberTail q hq tail)
     rfl rfl hPcap hQcap hresultant hPbar cert
include hcomponent hfinite hgen in
theorem indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q) (hqMonic:q.Monic)
   (surface tail:PlaneRing Omega) (m n:ℕ)
   [hSurfacePrime:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime]
   (hsurface:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     surface∈relationKernel Omega (CoordinateField Omega (component a.1).1) order
       (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   (hbarne:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥)
   (multiplicity:IndexedFactorFiber component lam mu nu order ht q → ℕ)
   (htail:∀ a,indexedFiberTail q hq tail∈
     Ideal.span {indexedFiberSurface q hq surface} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   (hPcap:(indexedFiberSurface q hq surface).natDegree ≤ m)
   (hQcap:(indexedFiberTail q hq tail).natDegree ≤ n)
   (hresultant:Polynomial.resultant surface tail m n≠0)
   (hPbar:(indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq))≠0):
   q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
     multiplicity a*indexedPlaneResidueWeight component lam mu nu order
       ht hfinite a.1)∣Polynomial.resultant surface tail m n:=by
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal:=
   fun a => indexedFiberRelationBar_isMaximal component lam mu nu order ht
     hfinite hgen q hq surface hsurface a
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
   fun a => indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht
     hfinite q hq surface a
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
   fun a => indexedNaturalSurfaceResidue_finite component lam mu nu order ht
     hfinite hgen q hq surface a (hsurface a)
 have hpow:=indexedFixedFactor_grouped_resultant_power_dvd component hcomponent
   lam mu nu order ht hfinite hgen q hq hqMonic surface tail m n hbarne
     multiplicity htail hPcap hQcap hresultant hPbar
 have hweight:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))=
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1:=
   fun a => indexedNaturalSurfaceResidue_finrank_eq_plane component lam mu nu
     order ht hfinite hgen q hq surface a (hsurface a)
 simpa only [hweight] using hpow
end
end ProximityPrize.SubmissionLower.RCN109

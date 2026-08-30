import ProximityPrize.SubmissionLower.Y9
import ProximityPrize.SubmissionLower.L9
import ProximityPrize.SubmissionLower.FP
namespace ProximityPrize.SubmissionLower.RCN107
open scoped Classical BigOperators
open RCN011 RCN021
open RCN002 RCN022
open RCN264
open RCN125 RCN093
open RCN120
open RCN102
open RCN106
open RCN192
open RCN197
open RCN236
open RCN307
open RCN225
open RCN191
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
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
abbrev indexedFiberSurface
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega):Polynomial (FiberCoefficient q hq):=
 fiberLocalizePlane q hq surface
abbrev indexedFiberTail
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (tail:PlaneRing Omega):Polynomial (FiberCoefficient q hq):=
 fiberLocalizePlane q hq tail
include hfinite hgen in
theorem indexedFiberRelationBar_isMaximal
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (hsurface:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     surface∈relationKernel Omega (CoordinateField Omega (component a.1).1) order
       (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal:=by
 let J:=indexedFiberRelation component lam mu nu order ht q hq a
 let quotientMap:=Ideal.Quotient.mk
   (Ideal.span {indexedFiberSurface q hq surface})
 letI:J.IsMaximal:=indexedFiberRelation_isMaximal
   component lam mu nu order ht hfinite hgen q hq a
 apply Ideal.IsMaximal.map_of_surjective_of_ker_le
   (f:=quotientMap) Ideal.Quotient.mk_surjective
 rw [Ideal.mk_ker,Ideal.span_le]
 intro x hx
 rw [Set.mem_singleton_iff] at hx
 subst x
 exact Ideal.mem_map_of_mem (fiberLocalizePlane q hq) (hsurface a)
theorem indexedFiberRelationBar_ne_bot
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface tail:PlaneRing Omega)
   (htailRoot:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     tail∈relationKernel Omega (CoordinateField Omega (component a.1).1) order
       (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   (hproper:indexedFiberTail q hq tail∉
     Ideal.span {indexedFiberSurface q hq surface})
   (a:IndexedFactorFiber component lam mu nu order ht q):
   indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥:=by
 let quotientMap:Polynomial (FiberCoefficient q hq) →+*
     SurfaceQuotient (indexedFiberSurface q hq surface):=
   Ideal.Quotient.mk (Ideal.span {indexedFiberSurface q hq surface})
 intro hbot
 have hmem:quotientMap (indexedFiberTail q hq tail)∈
     indexedFiberRelationBar component lam mu nu order ht q hq surface a:=
   Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (htailRoot a))
 have hzero:quotientMap (indexedFiberTail q hq tail)=0:=by
   apply Ideal.mem_bot.mp
   rw [←hbot]
   exact hmem
 exact hproper (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
include hfinite in
theorem indexedFiberRelation_comap_C_eq_maximalIdeal
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelation component lam mu nu order ht q hq a).comap
       Polynomial.C=IsLocalRing.maximalIdeal (FiberCoefficient q hq):=by
 cases a with
 | mk a hqeq =>
   subst q
   exact localizedRelation_comap_C_eq_maximalIdeal Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
include hfinite hgen in
theorem exists_monic_mem_indexedFiberRelation
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   ∃ M:Polynomial (FiberCoefficient q hq),M.Monic∧
     M∈indexedFiberRelation component lam mu nu order ht q hq a:=by
 cases a with
 | mk a hqeq =>
   subst q
   let J:=localizedRelation Omega (CoordinateField Omega (component a).1) order
     (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   letI:J.IsMaximal:=localizedRelation_isMaximal Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a)
         (hfinite a) (hgen a)
   have hcontract:=localizedRelation_comap_C_eq_maximalIdeal Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   have hfin:=localizedRelationResidue_finite Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a)
         (hfinite a) (hgen a)
   exact exists_monic_mem_maximal_relation J hcontract hfin
noncomputable def indexedWeightedFiberPrimaryPieces
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface tail:PlaneRing Omega)
   [hSurfacePrime:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime]
   [hbarMax:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal]
   (hbarne:∀ a,indexedFiberRelationBar component lam mu nu order ht
     q hq surface a≠⊥)
   (multiplicity:IndexedFactorFiber component lam mu nu order ht q → ℕ)
   (htail:∀ a,indexedFiberTail q hq tail∈
     Ideal.span {indexedFiberSurface q hq surface} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   [hlocal:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   [hresfinite:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]:
   PrimaryPiecesCertificate (indexedFiberSurface q hq surface)
     (indexedFiberTail q hq tail) (fun a => multiplicity a*
       Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
         (IsLocalRing.ResidueField (Localization.AtPrime
           (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))):=by
 exact primaryPiecesCertificateOfMembershipWeighted
   (indexedFiberSurface q hq surface) (indexedFiberTail q hq tail)
   (indexedFiberRelation component lam mu nu order ht q hq)
   (indexedFiberRelationBar component lam mu nu order ht q hq surface)
   (fun _ => rfl) hbarne multiplicity htail
   (indexedFiberRelation_pairwise_coprime component hcomponent lam mu nu order
     ht hfinite hgen q hq)
end
end ProximityPrize.SubmissionLower.RCN107

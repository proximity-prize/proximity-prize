import ProximityPrize.SubmissionLower.FW
import ProximityPrize.SubmissionLower.O
namespace ProximityPrize.SubmissionLower.RCN249
open scoped Classical BigOperators
open RCN135 RCN086 RCN244 RCN074 RCN245 RCN106 RCN111 RCN095 RCN120 RCN093 RCN002
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) (A:Type) [Fintype A]
structure StageIndexedFlagFamily where
 component:A → StageComponent S
 injective:Function.Injective component
 lam:GenericField K
 mu:GenericField K
 nu:GenericField K
 order:Fin 3 ≃ Fin 3
 ht:∀ a,Transcendental (GenericField K)
   (flagEvaluation (GenericField K) (component a).1 lam mu nu
     (MvPolynomial.X (order 0)))
 finite:∀ a,
   letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
   FiniteDimensional (RatFunc (GenericField K))
     (CoordinateField (GenericField K) (component a).1)
 generates:∀ a,
   letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
   IntermediateField.adjoin (RatFunc (GenericField K))
     ({flagEvaluation (GenericField K) (component a).1 lam mu nu
         (MvPolynomial.X (order 2)),
       flagEvaluation (GenericField K) (component a).1 lam mu nu
         (MvPolynomial.X (order 1))}:
       Set (CoordinateField (GenericField K) (component a).1))=⊤
 positive:0 < (stageSurfacePlane S lam mu nu order).natDegree
structure StageIndexedFactor (F:StageIndexedFlagFamily S A) where
 q:Polynomial (RatFunc (GenericField K))
 irreducible:Irreducible q
 monic:q.Monic
 witness:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q
noncomputable def stageFamilyGroupedExponent
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A)
   (q:Polynomial (RatFunc (GenericField K))):ℕ:=
 ∑ a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q,
   localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (F.component a.1)*
     indexedPlaneResidueWeight F.component F.lam F.mu F.nu F.order
       F.ht F.finite a.1
noncomputable def stageFamilyResultant (F:StageIndexedFlagFamily S A):
   Polynomial (RatFunc (GenericField K)):=
 Polynomial.resultant (stageSurfacePlane S F.lam F.mu F.nu F.order)
   (stageTailPlane S F.lam F.mu F.nu F.order)
   (stageSurfacePlane S F.lam F.mu F.nu F.order).natDegree
   (stageTailPlane S F.lam F.mu F.nu F.order).natDegree
@[simp] theorem stageFamilyGroupedExponent_eq
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (q):
   stageFamilyGroupedExponent S A hfirstProper F q=
     ∑ a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q,
       localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (F.component a.1)*
         indexedPlaneResidueWeight F.component F.lam F.mu F.nu F.order
           F.ht F.finite a.1:=rfl
end
end ProximityPrize.SubmissionLower.RCN249

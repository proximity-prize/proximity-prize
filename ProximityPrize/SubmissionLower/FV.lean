import ProximityPrize.SubmissionLower.C3
import ProximityPrize.SubmissionLower.FU
namespace ProximityPrize.SubmissionLower.RCN246
open RCN244 RCN248
open RCN135 RCN136 RCN095
open RCN074
open RCN106
open RCN107
open RCN102
open RCN245
open RCN113
open RCN120
open RCN086 RCN264
open RCN218 RCN313
open RCN002 RCN011
open RCN021 RCN125
open RCN093
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {errorCap : ℕ}
variable {stageSupport : RCN275.ResidualSupportParameters}
variable {A:Type} [Fintype A]
theorem indexedStageSurface_mem_relation
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0)))) (a:A):
   stageSurfacePlane S lam mu nu order∈
     relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a).1) order
       (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a):=by
 change planeEvaluation (GenericField K)
   (CoordinateField (GenericField K) (component a).1) order
     (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a)
       (planeMap (GenericField K) order (flagAlgHom lam mu nu S.G))=0
 rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
 change flagEvaluation (GenericField K) (component a).1 lam mu nu
   (flagAlgHom lam mu nu S.G)=0
 rw [flagEvaluation_flag]
 change S.G∈RingHom.ker
   (coordinateEvaluation (GenericField K) (component a).1).toRingHom
 rw [coordinateEvaluation_ker]
 exact regularComponent_G_mem (GenericField K) S.G _ _ (component a)
theorem indexedStageTail_mem_relation
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0)))) (a:A):
   stageTailPlane S lam mu nu order∈
     relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a).1) order
       (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a):=by
 let tail:=globalTailCut (polynomialEmbedding K) S.F
   (RCN326.w+1)
 change planeEvaluation (GenericField K)
   (CoordinateField (GenericField K) (component a).1) order
     (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a)
       (planeMap (GenericField K) order (flagAlgHom lam mu nu tail))=0
 rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
 change flagEvaluation (GenericField K) (component a).1 lam mu nu
   (flagAlgHom lam mu nu tail)=0
 rw [flagEvaluation_flag]
 change tail∈RingHom.ker
   (coordinateEvaluation (GenericField K) (component a).1).toRingHom
 rw [coordinateEvaluation_ker]
 exact regularComponent_T_mem (GenericField K) S.G tail _ (component a)
structure IndexedFiberProjectionData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):Prop where
 relationMax:(indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal
 factor_mem:stageFiberTargetMap S lam mu nu order q hq
   (originalData S (component a.1)).factor∈
     Ideal.span {indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)}
 surface_mem:indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)∈
   indexedFiberRelation component lam mu nu order ht q hq a
 contract:(indexedFiberRelation component lam mu nu order ht q hq a).comap
   (stageFiberTargetMap S lam mu nu order q hq)=componentPrime S (component a.1)
 tail_eq:indexedFiberTail q hq (stageTailPlane S lam mu nu order)=
   stageFiberTargetMap S lam mu nu order q hq
     (numerator K S.F (RCN326.w+1))*
       stageFiberScalar S lam mu nu order q hq
theorem indexedFiberProjectionData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (component a).1))
   (hgen:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))}:
         Set (CoordinateField (GenericField K) (component a).1))=⊤)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   IndexedFiberProjectionData S component lam mu nu order ht q hq a:=by
 let phi:=polynomialEmbedding K
 let plane:=flagPlaneMap (GenericField K) lam mu nu order
 let localize:=fiberLocalizePlane q hq
 let J:=indexedFiberRelation component lam mu nu order ht q hq a
 refine ⟨indexedFiberRelation_isMaximal component lam mu nu order ht
   hfinite hgen q hq a,?_,?_,?_,?_⟩
 · rw [Ideal.mem_span_singleton]
   exact map_dvd (localize.comp plane) (originalData S (component a.1)).factor_dvd
 · exact Ideal.mem_map_of_mem localize
     (indexedStageSurface_mem_relation S component lam mu nu order ht a.1)
 · have hplane:(relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu)
         (ht a.1)).comap plane=(component a.1).1:=by
     change (relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu)
         (ht a.1)).comap
       ((planeMap (GenericField K) order).comp (flagAlgHom lam mu nu).toRingHom)=_
     rw [←Ideal.comap_comap,relationKernel_contract,
       flagEvaluation_kernel_contract]
   change J.comap ((localize.comp plane).comp (surfaceMap phi))=
     componentPrime S (component a.1)
   rw [←Ideal.comap_comap, ←Ideal.comap_comap,
     indexedFiberRelation_under,hplane]
   rfl
 · change localize (plane (globalTailCut phi S.F
     (RCN326.w+1)))=
     localize (plane (surfaceMap phi (numerator K S.F
       (RCN326.w+1))))*
       localize (plane (MvPolynomial.C
         ((-phi Polynomial.X)^(RCN326.w+1))))
   rw [globalTailCut_eq,map_mul,map_mul]
end
end ProximityPrize.SubmissionLower.RCN246

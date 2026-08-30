import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.X2
import ProximityPrize.SubmissionLower.Z
namespace ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel
open ActualCurveCoordinateField ActualCurveRationalProjection TrivariateRationalCollection
noncomputable section
def bivariateEquiv (A:Type) [Field A]:
   MvPolynomial (Fin 2) A ≃ₐ[A] Polynomial (Polynomial A):=
 (MvPolynomial.finSuccEquiv A 1).trans
   (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv A (Fin 1)))
@[simp] theorem bivariateEquiv_C (A:Type) [Field A] (a:A):
   bivariateEquiv A (MvPolynomial.C a)=Polynomial.C (Polynomial.C a):=by
 simp [bivariateEquiv,MvPolynomial.finSuccEquiv_apply]
@[simp] theorem bivariateEquiv_X_zero (A:Type) [Field A]:
   bivariateEquiv A (MvPolynomial.X (0:Fin 2))=Polynomial.X:=by
 simp [bivariateEquiv,MvPolynomial.finSuccEquiv_apply]
@[simp] theorem bivariateEquiv_X_one (A:Type) [Field A]:
   bivariateEquiv A (MvPolynomial.X (1:Fin 2))=Polynomial.C Polynomial.X:=by
 change Polynomial.map (MvPolynomial.uniqueAlgEquiv A (Fin 1)).toRingHom
   ((MvPolynomial.finSuccEquiv A 1) (MvPolynomial.X (0:Fin 1).succ))=
     Polynomial.C Polynomial.X
 rw [MvPolynomial.finSuccEquiv_X_succ,Polynomial.map_C]
 simp [MvPolynomial.uniqueAlgEquiv]
variable (K:Type) [Field K]
abbrev PlaneRing:=Polynomial (Polynomial (RatFunc K))
def planeMap (order:Fin 3 ≃ Fin 3):Original K →+*PlaneRing K:=
 (bivariateEquiv (RatFunc K)).toRingHom.comp (rationalMap K order)
@[simp] theorem planeMap_C (order:Fin 3 ≃ Fin 3) (a:K):
   planeMap K order (MvPolynomial.C a)=
     Polynomial.C (Polynomial.C
       (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a))):=by
 simp [planeMap,rationalMap]
@[simp] theorem planeMap_X_first (order:Fin 3 ≃ Fin 3):
   planeMap K order (MvPolynomial.X (order 0))=
     Polynomial.C (Polynomial.C
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)):=by
 simp [planeMap,rationalMap]
@[simp] theorem planeMap_X_outer (order:Fin 3 ≃ Fin 3):
   planeMap K order (MvPolynomial.X (order 1))=Polynomial.X:=by
 have h:=collect_X_other K order (0:Fin 2)
 change collect K order (MvPolynomial.X (order 1))=MvPolynomial.X 0 at h
 simp [planeMap,rationalMap,h]
@[simp] theorem planeMap_X_inner (order:Fin 3 ≃ Fin 3):
   planeMap K order (MvPolynomial.X (order 2))=Polynomial.C Polynomial.X:=by
 have h:=collect_X_other K order (1:Fin 2)
 change collect K order (MvPolynomial.X (order 2))=MvPolynomial.X 1 at h
 simp [planeMap,rationalMap,h]
theorem planeMap_injective (order:Fin 3 ≃ Fin 3):
   Function.Injective (planeMap K order):=
 (bivariateEquiv (RatFunc K)).injective.comp (rationalMap_injective K order)
section Component
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
variable (ht:Transcendental K (coordinate K P (order 0)))
include ht in
theorem planeMap_irreducible_of_component
   (G:Original K) (hG:Irreducible G) (hmem:G∈P):
   Irreducible (planeMap K order G):=by
 exact (MulEquiv.irreducible_iff (bivariateEquiv (RatFunc K))).mpr
   (rationalMap_irreducible_of_component K order P G hG hmem ht)
include ht in
theorem planeMap_dvd_iff_of_component
   (G H:Original K) (hG:Irreducible G) (hmem:G∈P):
   planeMap K order G∣planeMap K order H ↔ G∣H:=by
 constructor
 · rintro ⟨U,hU⟩
   have hrat:rationalMap K order G∣rationalMap K order H:=by
     refine ⟨(bivariateEquiv (RatFunc K)).symm U,?_⟩
     apply (bivariateEquiv (RatFunc K)).injective
     change bivariateEquiv (RatFunc K) (rationalMap K order H)=
       bivariateEquiv (RatFunc K) (rationalMap K order G)*U at hU
     simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
   exact (rationalMap_dvd_iff_of_component K order P G H hG hmem ht).mp hrat
 · intro hdiv
   exact map_dvd (planeMap K order) hdiv
def actualPlaneEvaluation:PlaneRing K →+*CoordinateField K P:=
 (Polynomial.evalRingHom (coordinate K P (order 1))).comp
   (Polynomial.mapRingHom
     (Polynomial.eval₂RingHom (rationalBaseEmbedding K P (order 0) ht).toRingHom
       (coordinate K P (order 2))))
@[simp] theorem actualPlaneEvaluation_C_C (a:RatFunc K):
   actualPlaneEvaluation K order P ht (Polynomial.C (Polynomial.C a))=
     rationalBaseEmbedding K P (order 0) ht a:=by
 simp [actualPlaneEvaluation]
@[simp] theorem actualPlaneEvaluation_X:
   actualPlaneEvaluation K order P ht Polynomial.X=coordinate K P (order 1):=by
 simp [actualPlaneEvaluation]
@[simp] theorem actualPlaneEvaluation_C_X:
   actualPlaneEvaluation K order P ht (Polynomial.C Polynomial.X)=
     coordinate K P (order 2):=by
 simp [actualPlaneEvaluation]
theorem actualPlaneEvaluation_comp_planeMap:
   (actualPlaneEvaluation K order P ht).comp (planeMap K order)=
     (coordinateEvaluation K P).toRingHom:=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp only [RingHom.comp_apply]
   rw [planeMap_C,actualPlaneEvaluation_C_C,
     rationalBaseEmbedding_polynomial,Polynomial.aeval_C]
   exact (MvPolynomial.algHom_C (coordinateEvaluation K P) a).symm
 · intro i
   obtain ⟨j,rfl⟩:=order.surjective i
   by_cases hj:j=0
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_first,actualPlaneEvaluation_C_C,
       rationalBaseEmbedding_polynomial,Polynomial.aeval_X]
     rfl
   by_cases hj':j=1
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_outer,actualPlaneEvaluation_X]
     rfl
   have hjtwo:j=2:=by
     apply Fin.ext
     have hjlt:=j.isLt
     have hjzero:j.val≠0:=fun h => hj (Fin.ext h)
     have hjone:j.val≠1:=fun h => hj' (Fin.ext h)
     omega
   subst j
   simp only [RingHom.comp_apply]
   rw [planeMap_X_inner,actualPlaneEvaluation_C_X]
   rfl
def actualRelationKernel:Ideal (PlaneRing K):=
 RingHom.ker (actualPlaneEvaluation K order P ht)
theorem actualRelationKernel_contract:
   (actualRelationKernel K order P ht).comap (planeMap K order)=P:=by
 rw [actualRelationKernel,RingHom.comap_ker,actualPlaneEvaluation_comp_planeMap]
 exact coordinateEvaluation_ker K P
theorem actualPlane_root_iff (F:Original K):
   actualPlaneEvaluation K order P ht (planeMap K order F)=0 ↔ F∈P:=by
 change ((actualPlaneEvaluation K order P ht).comp (planeMap K order)) F=0 ↔ F∈P
 rw [actualPlaneEvaluation_comp_planeMap]
 change F∈RingHom.ker (coordinateEvaluation K P).toRingHom ↔ F∈P
 rw [coordinateEvaluation_ker]
end Component
theorem prime_eq_of_actualRelationKernel_eq
   (order:Fin 3 ≃ Fin 3) (P Q:Ideal (Original K)) [P.IsPrime] [Q.IsPrime]
   (hP:Transcendental K (coordinate K P (order 0)))
   (hQ:Transcendental K (coordinate K Q (order 0)))
   (heq:actualRelationKernel K order P hP=actualRelationKernel K order Q hQ):
   P=Q:=by
 have h:=congrArg (Ideal.comap (planeMap K order)) heq
 simpa only [actualRelationKernel_contract] using h
theorem actualRelationKernel_family_injective
   (order:Fin 3 ≃ Fin 3) {I:Type} (P:I → Ideal (Original K))
   [∀ i,(P i).IsPrime]
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P):
   Function.Injective (fun i => actualRelationKernel K order (P i) (ht i)):=by
 intro i j hij
 apply hinj
 exact prime_eq_of_actualRelationKernel_eq K order (P i) (P j) (ht i) (ht j) hij
end
end ProximityPrize.SubmissionLower.ActualPlaneCoordinateKernel

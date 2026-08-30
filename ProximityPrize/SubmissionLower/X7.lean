import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AW
import ProximityPrize.SubmissionLower.G
namespace ProximityPrize.SubmissionLower.RCN021
open scoped Classical BigOperators
open RCN371 RCN011
 RCN009 RCN013
 RCN008
 RCN024
 RCN025 RCN022
noncomputable section
set_option maxHeartbeats 1000000
variable (K:Type) [Field K]
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance:IsLocalization (coefficientDenominators K)
   (RationalPolynomials K):=
 MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)
section OneEvaluation
variable (L:Type) [Field L] [Algebra K L]
variable (order:Fin 3 ≃ Fin 3) (e:Original K →ₐ[K] L)
def collectedEvaluation:Collected K →+*L:=
 e.toRingHom.comp (collect K order).symm.toRingHom
@[simp] theorem collectedEvaluation_collect (F:Original K):
   collectedEvaluation K L order e (collect K order F)=e F:=by
 simp [collectedEvaluation]
@[simp] theorem collectedEvaluation_C (H:Polynomial K):
   collectedEvaluation K L order e (MvPolynomial.C H)=
     Polynomial.aeval (e (MvPolynomial.X (order 0))) H:=by
 have hhom:e.toRingHom.comp (coefficientLift K order)=
     (Polynomial.aeval (e (MvPolynomial.X (order 0)))).toRingHom:=by
   apply Polynomial.ringHom_ext
   · intro a
     change e (coefficientLift K order (Polynomial.C a))=
       Polynomial.aeval (e (MvPolynomial.X (order 0))) (Polynomial.C a)
     rw [coefficientLift_C,Polynomial.aeval_C]
     exact e.commutes a
   · change e (coefficientLift K order Polynomial.X)=
       Polynomial.aeval (e (MvPolynomial.X (order 0))) Polynomial.X
     rw [coefficientLift_X,Polynomial.aeval_X]
 exact RingHom.congr_fun hhom H
theorem coefficientDenominators_disjoint_of_evaluation
   (G:Original K) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Disjoint (coefficientDenominators K:Set (Collected K))
     (Ideal.span ({collect K order G}:Set (Collected K)):Set (Collected K)):=by
 rw [Set.disjoint_left]
 intro a ha hI
 obtain ⟨H,hH,rfl⟩:=Submonoid.mem_map.mp ha
 have hH0:H≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hH
 obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hI
 have hzero:Polynomial.aeval (e (MvPolynomial.X (order 0))) H=0:=by
   have heval:=congrArg (collectedEvaluation K L order e) hU
   simpa only [map_mul,collectedEvaluation_collect,collectedEvaluation_C,
     hroot,zero_mul] using heval
 exact hH0 (transcendental_iff.mp ht H hzero)
theorem rationalMap_irreducible_of_evaluation
   (G:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Irreducible (rationalMap K order G):=by
 have hp:=IsLocalization.isPrime_of_isPrime_disjoint
   (coefficientDenominators K) (RationalPolynomials K)
   (Ideal.span ({collect K order G}:Set (Collected K)))
   (collected_principal_isPrime K order G hG)
   (coefficientDenominators_disjoint_of_evaluation K L order e G hroot ht)
 have hp':
     (Ideal.span ({rationalMap K order G}:Set (RationalPolynomials K))).IsPrime:=by
   simpa only [Ideal.map_span,Set.image_singleton, ←rationalMap_eq] using hp
 exact ((Ideal.span_singleton_prime
   (rationalMap_ne_zero K order G hG.ne_zero)).mp hp').irreducible
theorem rationalMap_dvd_iff_of_evaluation
   (G H:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   rationalMap K order G∣rationalMap K order H ↔ G∣H:=by
 constructor
 · intro hdiv
   have hm:algebraMap (Collected K) (RationalPolynomials K) (collect K order H)∈
       Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collect K order G}:Set (Collected K))):=by
     simpa only [Ideal.map_span,Set.image_singleton,Ideal.mem_span_singleton,
       ←rationalMap_eq] using hdiv
   have hu:collect K order H∈
       (Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collect K order G}:Set (Collected K)))).under (Collected K):=hm
   rw [IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K)
     (RationalPolynomials K) (collected_principal_isPrime K order G hG)
     (coefficientDenominators_disjoint_of_evaluation K L order e G hroot ht)] at hu
   obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hu
   refine ⟨(collect K order).symm U,?_⟩
   apply (collect K order).injective
   simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
 · exact fun hdiv↦map_dvd (rationalMap K order) hdiv
theorem planeMap_irreducible_of_evaluation
   (G:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Irreducible (planeMap K order G):=
 (MulEquiv.irreducible_iff (bivariateEquiv (RatFunc K))).mpr
   (rationalMap_irreducible_of_evaluation K L order e G hG hroot ht)
theorem planeMap_dvd_iff_of_evaluation
   (G H:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   planeMap K order G∣planeMap K order H ↔ G∣H:=by
 constructor
 · rintro ⟨U,hU⟩
   have hrat:rationalMap K order G∣rationalMap K order H:=by
     refine ⟨(bivariateEquiv (RatFunc K)).symm U,?_⟩
     apply (bivariateEquiv (RatFunc K)).injective
     change bivariateEquiv (RatFunc K) (rationalMap K order H)=
       bivariateEquiv (RatFunc K) (rationalMap K order G)*U at hU
     simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
   exact (rationalMap_dvd_iff_of_evaluation K L order e G H hG hroot ht).mp hrat
 · exact fun hdiv↦map_dvd (planeMap K order) hdiv
def planeEvaluation
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   PlaneRing K →+*L:=
 (Polynomial.evalRingHom (e (MvPolynomial.X (order 1)))).comp
   (Polynomial.mapRingHom
     (Polynomial.eval₂RingHom
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom
       (e (MvPolynomial.X (order 2)))))
@[simp] theorem planeEvaluation_C_C
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))) (a:RatFunc K):
   planeEvaluation K L order e ht (Polynomial.C (Polynomial.C a))=
     elementEmbedding K L (e (MvPolynomial.X (order 0))) ht a:=by
 simp [planeEvaluation]
@[simp] theorem planeEvaluation_X
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   planeEvaluation K L order e ht Polynomial.X=
     e (MvPolynomial.X (order 1)):=by
 simp [planeEvaluation]
@[simp] theorem planeEvaluation_C_X
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   planeEvaluation K L order e ht (Polynomial.C Polynomial.X)=
     e (MvPolynomial.X (order 2)):=by
 simp [planeEvaluation]
theorem elementEmbedding_polynomial (s:L) (hs:Transcendental K s)
   (f:Polynomial K):
   elementEmbedding K L s hs (algebraMap (Polynomial K) (RatFunc K) f)=
     Polynomial.aeval s f:=
 RatFunc.liftRingHom_algebraMap _ _ f
theorem planeEvaluation_comp_planeMap
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   (planeEvaluation K L order e ht).comp (planeMap K order)=e.toRingHom:=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp only [RingHom.comp_apply]
   rw [planeMap_C,planeEvaluation_C_C,
     elementEmbedding_polynomial,Polynomial.aeval_C]
   exact (e.commutes a).symm
 · intro i
   obtain ⟨j,rfl⟩:=order.surjective i
   by_cases hj:j=0
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_first,planeEvaluation_C_C,
       elementEmbedding_variable]
     rfl
   by_cases hj':j=1
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_outer,planeEvaluation_X]
     rfl
   have hjtwo:j=2:=by
     apply Fin.ext
     have hjlt:=j.isLt
     have hjzero:j.val≠0:=fun h↦hj (Fin.ext h)
     have hjone:j.val≠1:=fun h↦hj' (Fin.ext h)
     omega
   subst j
   simp only [RingHom.comp_apply]
   rw [planeMap_X_inner,planeEvaluation_C_X]
   rfl
def relationKernel
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Ideal (PlaneRing K):=RingHom.ker (planeEvaluation K L order e ht)
theorem relationKernel_contract
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   (relationKernel K L order e ht).comap (planeMap K order)=
     RingHom.ker e.toRingHom:=by
 rw [relationKernel,RingHom.comap_ker,planeEvaluation_comp_planeMap]
end OneEvaluation
section FixedFamily
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
variable (E:I → Type)
variable [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
variable (e:∀ i,Original K →ₐ[K] E i)
theorem finite_sum_finrank_bound
   (ht:∀ i,Transcendental K (e i (MvPolynomial.X (order 0))))
   (hgen:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))}:
         Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦RingHom.ker (e i).toRingHom))
   (G H:Original K) (hG:Irreducible G)
   (hGroot:∀ i,e i G=0) (hHroot:∀ i,e i H=0)
   (hproper:¬ G∣H) (hpositive:0 < (planeMap K order G).natDegree):
   letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
     (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
   (∀ i,FiniteDimensional (RatFunc K) (E i))∧
     (∑ i,Module.finrank (RatFunc K) (E i)) ≤
       (planeMap K order H).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order H):=by
 classical
 letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
   (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   have hirr:Irreducible (planeMap K order G):=
     planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
       G hG (hGroot i₀) (ht i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro hdiv
     exact hproper ((planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
       G H hG (hGroot i₀) (ht i₀)).mp hdiv)
   have hGroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i) (planeMap K order G)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hGroot i
   have hHroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i) (planeMap K order H)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hHroot i
   have hfinite:∀ i,FiniteDimensional (RatFunc K) (E i):=by
     intro i
     have hGeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom (algebraMap (RatFunc K) (E i))
           (e i (MvPolynomial.X (order 2))))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hGroots i
     have hHeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom (algebraMap (RatFunc K) (E i))
           (e i (MvPolynomial.X (order 2))))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hHroots i
     exact finite_of_proper_plane_roots (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))
       hGeval hHeval (hgen i)
   letI:∀ i,FiniteDimensional (RatFunc K) (E i):=hfinite
   have hrelation:Function.Injective (fun i↦
       RCN361.relationIdeal (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1)))):=by
     intro i j hij
     apply hkernels
     change relationKernel K (E i) order (e i) (ht i)=
       relationKernel K (E j) order (e j) (ht j) at hij
     have hc:=congrArg (Ideal.comap (planeMap K order)) hij
     simpa only [relationKernel_contract] using hc
   exact ⟨hfinite,
     sum_finrank_le_planar_bound_without_separability
       (K:=RatFunc K) (I:=I) E
       (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (fun i↦e i (MvPolynomial.X (order 2)))
       (fun i↦e i (MvPolynomial.X (order 1))) hgen
       hrelation hGroots hHroots⟩
 · letI:IsEmpty I:=⟨fun i↦hI ⟨i⟩⟩
   exact ⟨fun i↦isEmptyElim i,by simp⟩
end FixedFamily
end
end ProximityPrize.SubmissionLower.RCN021

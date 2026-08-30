import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.JA
import ProximityPrize.SubmissionLower.R8
import ProximityPrize.SubmissionLower.R1
namespace ProximityPrize.SubmissionLower.RCN358
open scoped Classical BigOperators WithZero
open IsDedekindDomain
noncomputable section
variable (K:Type*) [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev InfinityBase:=RCN349.InfinityBase K
local instance:Algebra K (InfinityBase K):=
 (RCN352.constantMap K).toAlgebra
def infinityBasePoint:InfinityBase K →ₐ[K] K where
 toRingHom:=(RCN352.residueEquiv K).symm.toRingHom.comp
   (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityBase K)))
 commutes' c:=by
   change (RCN352.residueEquiv K).symm
     (RCN352.residueConstant K c)=c
   rw [←RCN352.residueEquiv_apply,RingEquiv.symm_apply_apply]
theorem infinityBasePoint_kernel:
   RingHom.ker (infinityBasePoint K).toRingHom=
     (RCN349.infinityPlace K).asIdeal:=by
 ext r
 change (RCN352.residueEquiv K).symm
     (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityBase K)) r)=0 ↔
   r∈IsLocalRing.maximalIdeal (InfinityBase K)
 constructor
 · intro h
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   apply (RCN352.residueEquiv K).symm.injective
   simpa only [map_zero] using h
 · intro h
   rw [Ideal.Quotient.eq_zero_iff_mem.mpr h,map_zero]
variable [IsAlgClosed K]
theorem finiteBase_natDegree_eq_one (f:Polynomial K) (hf:Irreducible f):
   f.natDegree=1:=
 Polynomial.natDegree_eq_of_degree_eq_some
   (IsAlgClosed.degree_eq_one_of_irreducible K hf)
theorem finiteBase_exists_point (p:HeightOneSpectrum (Polynomial K)):
   ∃ phi:Polynomial K →ₐ[K] K,RingHom.ker phi.toRingHom=p.asIdeal:=by
 obtain ⟨f,hf,hm,hplace⟩:=RCN366.exists_monic_primePlace K p
 obtain ⟨alpha,hroot⟩:=IsAlgClosed.exists_root f (by
   rw [IsAlgClosed.degree_eq_one_of_irreducible K hf]
   exact one_ne_zero)
 let phi:Polynomial K →ₐ[K] K:=Polynomial.aeval alpha
 have hkermax:(RingHom.ker phi.toRingHom).IsMaximal:=
   RCN354.pointKernel_isMaximal phi
 have hle:p.asIdeal ≤ RingHom.ker phi.toRingHom:=by
   rw [←hplace]
   change Ideal.span {f} ≤ RingHom.ker phi.toRingHom
   apply (Ideal.span_singleton_le_iff_mem (I:=RingHom.ker phi.toRingHom)).mpr
   change f.eval alpha=0
   exact hroot
 refine ⟨phi,?_⟩
 exact ((p.isPrime.isMaximal p.ne_bot).eq_of_le hkermax.ne_top hle).symm
variable (L:Type*) [Field L]
variable [Algebra K L] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
abbrev FiniteNormalization:=RCN349.FiniteNormalization K L
local instance:IsFractionRing (InfinityBase K) (RatFunc K):=
 RCN353.infinityRing_isFractionRing K
local instance (priority:=100):Algebra (InfinityBase K) L:=
 ((algebraMap (RatFunc K) L).comp
   (algebraMap (InfinityBase K) (RatFunc K))).toAlgebra
local instance:IsScalarTower (InfinityBase K) (RatFunc K) L:=
 IsScalarTower.of_algebraMap_eq' rfl
abbrev InfiniteNormalization:=RCN349.InfiniteNormalization K L
theorem finitePlace_inertia_one
   (q:HeightOneSpectrum (FiniteNormalization K L)):
   q.asIdeal.inertiaDeg (Polynomial K)=1:=by
 letI:Algebra K (FiniteNormalization K L):=
   ((algebraMap (Polynomial K) (FiniteNormalization K L)).comp Polynomial.C).toAlgebra
 letI:IsScalarTower K (Polynomial K) (FiniteNormalization K L):=
   IsScalarTower.of_algebraMap_eq' rfl
 letI:q.asIdeal.IsMaximal:=q.isPrime.isMaximal q.ne_bot
 obtain ⟨phi,hphi⟩:=finiteBase_exists_point K
   (HeightOneSpectrum.under (Polynomial K) q)
 apply RCN373.inertiaDeg_eq_one_of_point_fiber phi q.asIdeal
 exact hphi.symm
theorem infinitePlace_inertia_one
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   q.asIdeal.inertiaDeg (InfinityBase K)=1:=by
 letI:Algebra K (InfiniteNormalization K L):=
   ((algebraMap (InfinityBase K) (InfiniteNormalization K L)).comp
     (algebraMap K (InfinityBase K))).toAlgebra
 letI:IsScalarTower K (InfinityBase K) (InfiniteNormalization K L):=
   IsScalarTower.of_algebraMap_eq' rfl
 letI:q.asIdeal.IsMaximal:=q.isPrime.isMaximal q.ne_bot
 letI:=RCN345.infinitePlace_liesOver K L q
 apply RCN373.inertiaDeg_eq_one_of_point_fiber
   (infinityBasePoint K) q.asIdeal
 rw [infinityBasePoint_kernel]
 exact (Ideal.over_def q.asIdeal (RCN349.infinityPlace K).asIdeal).symm
theorem infinitePlace_inertia'_one
   (q:HeightOneSpectrum (InfiniteNormalization K L)):
   (RCN349.infinityPlace K).asIdeal.inertiaDeg' q.asIdeal=1:=by
 letI:q.asIdeal.IsMaximal:=q.isPrime.isMaximal q.ne_bot
 letI:=RCN345.infinitePlace_liesOver K L q
 rw [Ideal.inertiaDeg'_eq_inertiaDeg]
 exact infinitePlace_inertia_one K L q
theorem finiteFiber_weight_one (f:Polynomial K) (hf:Irreducible f)
   (Q:{Q:Ideal (FiniteNormalization K L)//
     Q∈IsDedekindDomain.primesOverFinset
       (RCN366.primePlace K f hf).asIdeal (FiniteNormalization K L)}):
   (f.natDegree:ℤ)*(Q.1.inertiaDeg (Polynomial K):ℤ)=1:=by
 have hQ:=finitePlace_inertia_one K L
   (RCN357.placeAbove (Polynomial K) (FiniteNormalization K L)
     (RCN366.primePlace K f hf) Q)
 change Q.1.inertiaDeg (Polynomial K)=1 at hQ
 rw [finiteBase_natDegree_eq_one K f hf,hQ]
 norm_num
theorem infiniteFiber_weight_one
   (Q:{Q:Ideal (InfiniteNormalization K L)//
     Q∈IsDedekindDomain.primesOverFinset
       (RCN349.infinityPlace K).asIdeal (InfiniteNormalization K L)}):
   (Q.1.inertiaDeg (InfinityBase K):ℤ)=1:=by
 have hQ:=infinitePlace_inertia_one K L
   (RCN357.placeAbove (InfinityBase K) (InfiniteNormalization K L)
     (RCN349.infinityPlace K) Q)
 exact_mod_cast hQ
end
end ProximityPrize.SubmissionLower.RCN358

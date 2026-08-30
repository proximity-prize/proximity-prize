import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.G1
namespace ProximityPrize.SubmissionLower.RCN353
open scoped Classical
noncomputable section
variable (K:Type*) [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev InfinityRing:=(RatFunc.inftyValuation K).valuationSubring
instance infinity_isRankOneDiscrete:
   Valuation.IsRankOneDiscrete (RatFunc.inftyValuation K):=inferInstance
instance infinityRing_isDiscreteValuationRing:
   IsDiscreteValuationRing (InfinityRing K):=inferInstance
theorem infinityRing_isFractionRing:
   IsFractionRing (InfinityRing K) (RatFunc K):=inferInstance
def infinityUniformizer:InfinityRing K:=by
 refine ⟨(RatFunc.X:RatFunc K)⁻¹,?_⟩
 change RatFunc.inftyValuation K (RatFunc.X:RatFunc K)⁻¹ ≤ 1
 rw [show RatFunc.inftyValuation K (RatFunc.X:RatFunc K)⁻¹=
     WithZero.exp (-1:ℤ) by
   simpa only [one_div] using RatFunc.inftyValuation.X_inv K]
 rw [←WithZero.exp_zero,WithZero.exp_le_exp]
 norm_num
theorem infinityUniformizer_value:
   RatFunc.inftyValuation K
     (algebraMap (InfinityRing K) (RatFunc K) (infinityUniformizer K))=
     WithZero.exp (-1:ℤ):=by
 change RatFunc.inftyValuation K (RatFunc.X:RatFunc K)⁻¹=_
 simpa only [one_div] using RatFunc.inftyValuation.X_inv K
theorem infinityUniformizer_isUniformizer:
   (RatFunc.inftyValuation K).IsUniformizer
     (algebraMap (InfinityRing K) (RatFunc K) (infinityUniformizer K)):=by
 unfold Valuation.IsUniformizer
 rw [Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
   (v:=RatFunc.inftyValuation K)
   ⟨algebraMap (InfinityRing K) (RatFunc K) (infinityUniformizer K),
     infinityUniformizer_value K⟩]
 exact infinityUniformizer_value K
theorem infinityUniformizer_ne_zero:infinityUniformizer K≠0:=by
 intro hzero
 have h:=(infinityUniformizer_isUniformizer K).ne_zero
 exact h (by rw [hzero,map_zero])
theorem infinity_maximalIdeal_eq_span:
   (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).asIdeal=
     Ideal.span {infinityUniformizer K}:=
 (infinityUniformizer_isUniformizer K).is_generator
theorem infinityUniformizer_irreducible:Irreducible (infinityUniformizer K):=
 (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
   (infinity_maximalIdeal_eq_span K)
theorem infinity_intValuation_eq (x:InfinityRing K):
   (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).intValuation x=
     RatFunc.inftyValuation K (algebraMap (InfinityRing K) (RatFunc K) x):=by
 by_cases hx:x=0
 · simp [hx]
 obtain ⟨n,u,rfl⟩:=IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
   hx (infinityUniformizer_irreducible K)
 have hunit:
     (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).intValuation
       (u:InfinityRing K)=1:=by
   simp [IsDiscreteValuationRing.maximalIdeal]
 have hunit':
     RatFunc.inftyValuation K
       (algebraMap (InfinityRing K) (RatFunc K) (u:InfinityRing K))=1:=
   Valuation.Integers.one_of_isUnit
     (Valuation.valuationSubring.integers (RatFunc.inftyValuation K)) u.isUnit
 have hparameter:
     (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).intValuation
       (infinityUniformizer K)=WithZero.exp (-1:ℤ):=
   (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).intValuation_singleton
     (infinityUniformizer_ne_zero K) (infinity_maximalIdeal_eq_span K)
 simp only [map_mul,map_pow,hunit,hunit',hparameter,
   infinityUniformizer_value,one_mul]
theorem infinity_valuation_eq (x:RatFunc K):
   (IsDiscreteValuationRing.maximalIdeal (InfinityRing K)).valuation (RatFunc K) x=
     RatFunc.inftyValuation K x:=by
 obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (A:=InfinityRing K) x
 simp only [map_div₀,
   IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
   infinity_intValuation_eq]
end
end ProximityPrize.SubmissionLower.RCN353

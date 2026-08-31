import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.InfinityValuationRing
namespace ProximityPrize.SubmissionLower.InfinityResidueField
open scoped Classical WithZero
noncomputable section
variable (K:Type*) [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev InfinityRing:=InfinityValuationRing.InfinityRing K
def constantMap:K →+*InfinityRing K where
  toFun c:=⟨RatFunc.C c,by
    change RatFunc.inftyValuation K (RatFunc.C c) ≤ 1
    by_cases hc:c=0
    · simp [hc]
    · exact le_of_eq (RatFunc.inftyValuation.C K hc)⟩
  map_zero':=Subtype.ext (map_zero RatFunc.C)
  map_one':=Subtype.ext (map_one RatFunc.C)
  map_add' c d:=Subtype.ext (map_add RatFunc.C c d)
  map_mul' c d:=Subtype.ext (map_mul RatFunc.C c d)
theorem constantMap_value (c:K):
    (constantMap K c).val=RatFunc.C c:=rfl
theorem polynomial_quotient_value_lt_one
    (f g:Polynomial K) (hg:g≠0) (hdeg:f.degree < g.degree):
    RatFunc.inftyValuation K
      (algebraMap (Polynomial K) (RatFunc K) f/
        algebraMap (Polynomial K) (RatFunc K) g) < 1:=by
  by_cases hf:f=0
  · simp [hf]
  have hfmap:algebraMap (Polynomial K) (RatFunc K) f≠0:=by
    simpa using hf
  have hgmap:algebraMap (Polynomial K) (RatFunc K) g≠0:=by
    simpa using hg
  have hquot:=div_ne_zero hfmap hgmap
  have hnat:f.natDegree < g.natDegree:=by
    rw [Polynomial.degree_eq_natDegree hf,Polynomial.degree_eq_natDegree hg] at hdeg
    exact_mod_cast hdeg
  rw [RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero K hquot,
    RatFunc.intDegree_div hfmap hgmap,
    RatFunc.intDegree_polynomial,RatFunc.intDegree_polynomial,
    ←WithZero.exp_zero,WithZero.exp_lt_exp]
  exact sub_neg.mpr (Int.ofNat_lt.mpr hnat)
theorem exists_constant_difference_lt_one (r:InfinityRing K):
    ∃ c:K,RatFunc.inftyValuation K (r.val-RatFunc.C c) < 1:=by
  by_cases hr:r.val=0
  · exact ⟨0,by simp [hr]⟩
  have hf:r.val.num≠0:=RatFunc.num_ne_zero hr
  have hg:r.val.denom≠0:=r.val.denom_ne_zero
  have hdegree:r.val.num.natDegree ≤ r.val.denom.natDegree:=by
    have hmem:RatFunc.inftyValuation K r.val ≤ 1:=r.property
    rw [RatFunc.inftyValuation_apply,
      RatFunc.inftyValuation_of_nonzero K hr,
      ←WithZero.exp_zero,WithZero.exp_le_exp] at hmem
    dsimp [RatFunc.intDegree] at hmem
    omega
  by_cases hstrict:r.val.num.natDegree < r.val.denom.natDegree
  · refine ⟨0,?_⟩
    have hd:r.val.num.degree < r.val.denom.degree:=by
      rw [Polynomial.degree_eq_natDegree hf,Polynomial.degree_eq_natDegree hg]
      exact_mod_cast hstrict
    have h:=polynomial_quotient_value_lt_one K r.val.num r.val.denom hg hd
    simpa only [RatFunc.num_div_denom,map_zero,sub_zero] using h
  · have hsame:r.val.num.natDegree=r.val.denom.natDegree:=by omega
    have hdegfg:r.val.num.degree=r.val.denom.degree:=by
      rw [Polynomial.degree_eq_natDegree hf,Polynomial.degree_eq_natDegree hg,hsame]
    let c:K:=r.val.num.leadingCoeff
    have hc:c≠0:=Polynomial.leadingCoeff_ne_zero.mpr hf
    have hpc:r.val.num.degree=(Polynomial.C c*r.val.denom).degree:=by
      rw [Polynomial.degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hc)]
      exact hdegfg
    have hlc:r.val.num.leadingCoeff=
        (Polynomial.C c*r.val.denom).leadingCoeff:=by
      rw [(RatFunc.monic_denom r.val).leadingCoeff_C_mul]
    have hcancel:
        (r.val.num-Polynomial.C c*r.val.denom).degree < r.val.denom.degree:=
      (Polynomial.degree_sub_lt hpc hf hlc).trans_eq hdegfg
    have hgmap:algebraMap (Polynomial K) (RatFunc K) r.val.denom≠0:=by
      simpa using hg
    have hquot:r.val-RatFunc.C c=
        algebraMap (Polynomial K) (RatFunc K)
          (r.val.num-Polynomial.C c*r.val.denom)/
        algebraMap (Polynomial K) (RatFunc K) r.val.denom:=by
      calc
        r.val-RatFunc.C c=
            algebraMap (Polynomial K) (RatFunc K) r.val.num/
              algebraMap (Polynomial K) (RatFunc K) r.val.denom-RatFunc.C c:=by
          rw [RatFunc.num_div_denom]
        _=(algebraMap (Polynomial K) (RatFunc K) r.val.num-
              RatFunc.C c*algebraMap (Polynomial K) (RatFunc K) r.val.denom)/
              algebraMap (Polynomial K) (RatFunc K) r.val.denom:=by
          rw [sub_div,mul_div_cancel_right₀ _ hgmap]
        _=_:=by rw [map_sub,map_mul,RatFunc.algebraMap_C]
    refine ⟨c,?_⟩
    rw [hquot]
    exact polynomial_quotient_value_lt_one K
      (r.val.num-Polynomial.C c*r.val.denom) r.val.denom hg hcancel
theorem exists_constant_difference_mem_maximalIdeal (r:InfinityRing K):
    ∃ c:K,r-constantMap K c∈IsLocalRing.maximalIdeal (InfinityRing K):=by
  obtain ⟨c,hc⟩:=exists_constant_difference_lt_one K r
  refine ⟨c,?_⟩
  apply (Valuation.mem_maximalIdeal_iff (RatFunc K) (RatFunc.inftyValuation K)).mpr
  exact hc
abbrev ResidueField:=InfinityRing K ⧸ IsLocalRing.maximalIdeal (InfinityRing K)
def residueConstant:K →+*ResidueField K:=
  (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityRing K))).comp (constantMap K)
theorem residueConstant_injective:Function.Injective (residueConstant K):=
  (residueConstant K).injective
theorem residueConstant_surjective:Function.Surjective (residueConstant K):=by
  intro y
  obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective y
  obtain ⟨c,hc⟩:=exists_constant_difference_mem_maximalIdeal K r
  refine ⟨c,?_⟩
  have hz:=Ideal.Quotient.eq_zero_iff_mem.mpr hc
  have heq:Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityRing K)) r=
      residueConstant K c:=by
    apply sub_eq_zero.mp
    simpa only [map_sub,residueConstant,RingHom.comp_apply] using hz
  exact heq.symm
def residueEquiv:K ≃+*ResidueField K:=
  RingEquiv.ofBijective (residueConstant K)
    ⟨residueConstant_injective K,residueConstant_surjective K⟩
theorem residueEquiv_apply (c:K):residueEquiv K c=residueConstant K c:=rfl
end
end ProximityPrize.SubmissionLower.InfinityResidueField

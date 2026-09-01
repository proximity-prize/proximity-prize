import ProximityPrize.SubmissionLower.D7
namespace ProximityPrize.SubmissionLower.RCN227
open UniqueFactorizationMonoid
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K:Type} [Field K] [DecidableEq K]
theorem ord_algebraMap_eq_normalizedFactors_count
   (p:Ideal (Polynomial K)) [p.IsPrime]
   (q r:Polynomial K) (hp:p=Ideal.span {q})
   (hq:Irreducible q) (hqMonic:q.Monic)
   (hr:r≠0):
   Ring.ord (Localization.AtPrime p)
     (algebraMap (Polynomial K) (Localization.AtPrime p) r)=
       ((normalizedFactors r).count q:ℕ∞):=by
 let R:=Localization.AtPrime p
 have hp0:p≠⊥:=by
   rw [hp,ne_eq,Ideal.span_singleton_eq_bot]
   exact hq.ne_zero
 letI:IsDiscreteValuationRing R:=
   IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
     (Polynomial K) hp0 R
 have hem:emultiplicity q r=((normalizedFactors r).count q:ℕ∞):=by
   rw [emultiplicity_eq_count_normalizedFactors hq hr,
     hqMonic.normalize_eq_self]
 have hfinite:FiniteMultiplicity q r:=
   finiteMultiplicity_of_emultiplicity_eq_natCast hem
 let e:ℕ:=(normalizedFactors r).count q
 have hmult:multiplicity q r=e:=by
   rw [multiplicity_eq_count_normalizedFactors hq hr,
     hqMonic.normalize_eq_self]
 obtain ⟨s,hrs,hqNotDvd⟩:=hfinite.exists_eq_pow_mul_and_not_dvd
 rw [hmult] at hrs
 have hsNotMem:s∉p:=by
   simpa only [hp,Ideal.mem_span_singleton] using hqNotDvd
 have hsUnit:IsUnit (algebraMap (Polynomial K) R s):=
   (IsLocalization.AtPrime.isUnit_to_map_iff R p s).mpr hsNotMem
 have hqMapNe:algebraMap (Polynomial K) R q≠0:=
   by
     simpa only [map_zero] using
       (FaithfulSMul.algebraMap_injective (Polynomial K) R).ne hq.ne_zero
 have hmax:IsLocalRing.maximalIdeal R=
     Ideal.span {algebraMap (Polynomial K) R q}:=by
   calc
     IsLocalRing.maximalIdeal R=
         Ideal.map (algebraMap (Polynomial K) R) p:=by
       simpa only [R] using
         (Localization.AtPrime.map_eq_maximalIdeal (I:=p)).symm
     _=Ideal.map (algebraMap (Polynomial K) R) (Ideal.span {q}):=
       congrArg (Ideal.map (algebraMap (Polynomial K) R)) hp
     _=Ideal.span {algebraMap (Polynomial K) R q}:=by
       rw [Ideal.map_span]
       simp only [Set.image_singleton]
 have hqMapIrr:Irreducible (algebraMap (Polynomial K) R q):=
   IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
     _ hqMapNe hmax
 have hsNe:algebraMap (Polynomial K) R s≠0:=hsUnit.ne_zero
 have hrsMap:algebraMap (Polynomial K) R r=
     (algebraMap (Polynomial K) R q)^e*
       algebraMap (Polynomial K) R s:=by
   rw [hrs,map_mul,map_pow]
 change Ring.ord R (algebraMap (Polynomial K) R r)=_
 rw [hrsMap,
   Ring.ord_mul R (mem_nonZeroDivisors_iff_ne_zero.mpr hsNe),
   Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.mpr hqMapNe),
   Ring.ord_of_irreducible hqMapIrr,Ring.ord_of_isUnit hsUnit]
 simp [e]
theorem pow_sum_dvd_of_sum_le_localized_ord
   {I:Type*} [Fintype I]
   (p:Ideal (Polynomial K)) [p.IsPrime]
   (q r:Polynomial K) (hp:p=Ideal.span {q})
   (hq:Irreducible q) (hqMonic:q.Monic) (hr:r≠0)
   (multiplicity:I → ℕ)
   (hle:((∑ i,multiplicity i:ℕ):ℕ∞) ≤
     Ring.ord (Localization.AtPrime p)
       (algebraMap (Polynomial K) (Localization.AtPrime p) r)):
   q^(∑ i,multiplicity i)∣r:=by
 rw [ord_algebraMap_eq_normalizedFactors_count p q r hp hq hqMonic hr] at hle
 have hcount:(∑ i,multiplicity i) ≤ (normalizedFactors r).count q:=by
   exact_mod_cast hle
 have hem:emultiplicity q r=
     ((normalizedFactors r).count q:ℕ∞):=by
   rw [emultiplicity_eq_count_normalizedFactors hq hr,
     hqMonic.normalize_eq_self]
 apply pow_dvd_of_le_emultiplicity
 rw [hem]
 exact_mod_cast hcount
end
end ProximityPrize.SubmissionLower.RCN227

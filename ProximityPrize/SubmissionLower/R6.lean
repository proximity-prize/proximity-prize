import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.GeometricFactorContraction
noncomputable section
section FlatPrincipal
variable {A B:Type*} [CommRing A] [IsDomain A]
 [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra A B]
 [Module.Flat A B]
theorem prime_eq_span_of_le (g:B) (hg:Prime g)
   (Q:Ideal B) [Q.IsPrime] (hQ:Q≠⊥)
   (hle:Q ≤ Ideal.span {g}):Q=Ideal.span {g}:=by
 let P:Ideal B:=Ideal.span {g}
 haveI:P.IsPrime:=(Ideal.span_singleton_prime hg.ne_zero).mpr hg
 have hheight:P.height ≤ 1:=Ideal.height_span_singleton_le_one hg.not_unit
 by_contra hne
 have hlt:Q < P:=lt_of_le_of_ne hle hne
 have hsmall:=(Ideal.height_le_iff (p:=P) (n:=1)).mp hheight Q
   inferInstance hlt
 have hzero:Q.height=0:=Order.lt_one_iff.mp hsmall
 exact hQ (Ideal.height_eq_zero_iff_eq_bot.mp hzero)
theorem under_prime_factor_eq
   (hinjective:Function.Injective (algebraMap A B))
   (F:A) (hF:Prime F) (g:B) (hg:Prime g)
   (hdiv:g∣algebraMap A B F):
   (Ideal.span {g}).under A=Ideal.span {F}:=by
 let P:Ideal B:=Ideal.span {g}
 let p:Ideal A:=Ideal.span {F}
 haveI:P.IsPrime:=(Ideal.span_singleton_prime hg.ne_zero).mpr hg
 haveI:p.IsPrime:=(Ideal.span_singleton_prime hF.ne_zero).mpr hF
 have hp:p ≤ P.under A:=by
   apply Ideal.span_le.mpr
   intro x hx
   obtain rfl:=Set.mem_singleton_iff.mp hx
   exact Ideal.mem_span_singleton.mpr hdiv
 obtain ⟨Q,hQP,hQprime,hQover⟩:=
   P.exists_ideal_le_liesOver_of_le (p:=p) (q:=P.under A) hp
 letI:Q.IsPrime:=hQprime
 letI:Q.LiesOver p:=hQover
 have hFQ:algebraMap A B F∈Q:=by
   change F∈Q.under A
   rw [←Q.over_def p]
   exact Ideal.subset_span (Set.mem_singleton F)
 have hQ:Q≠⊥:=by
   intro hbot
   rw [hbot,Ideal.mem_bot] at hFQ
   exact hF.ne_zero (hinjective (by simpa only [map_zero] using hFQ))
 have heq:Q=P:=prime_eq_span_of_le g hg Q hQ hQP
 have hover:Q.under A=p:=(Q.over_def p).symm
 simpa only [heq] using hover
theorem dvd_of_prime_factor_dvd
   (hinjective:Function.Injective (algebraMap A B))
   (F M:A) (hF:Prime F) (g:B) (hg:Prime g)
   (hdivF:g∣algebraMap A B F) (hdivM:g∣algebraMap A B M):
   F∣M:=by
 have hm:M∈(Ideal.span {g}).under A:=
   Ideal.mem_span_singleton.mpr hdivM
 rw [under_prime_factor_eq hinjective F hF g hg hdivF] at hm
 exact Ideal.mem_span_singleton.mp hm
end FlatPrincipal
section CoefficientExtension
variable {K L σ:Type*} [Field K] [Field L] [Algebra K L]
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem coefficient_extension_flat:
   Module.Flat (MvPolynomial σ K) (MvPolynomial σ L):=by
 exact Module.Flat.of_linearEquiv
   (Algebra.IsPushout.equiv K (MvPolynomial σ K) L
     (MvPolynomial σ L)).symm.toLinearEquiv
variable [Finite σ]
theorem geometric_factor_contraction
   (F:MvPolynomial σ K) (hF:Irreducible F)
   (g:MvPolynomial σ L) (hg:Irreducible g)
   (hdiv:g∣MvPolynomial.map (algebraMap K L) F):
   Ideal.comap (MvPolynomial.map (algebraMap K L)) (Ideal.span {g})=
     Ideal.span {F}:=by
 letI:=coefficient_extension_flat (K:=K) (L:=L) (σ:=σ)
 have hinj:Function.Injective
     (algebraMap (MvPolynomial σ K) (MvPolynomial σ L)):=
   MvPolynomial.map_injective _ (algebraMap K L).injective
 exact under_prime_factor_eq hinj F hF.prime g hg.prime hdiv
theorem original_dvd_of_geometric_factor_dvd
   (F M:MvPolynomial σ K) (hF:Irreducible F)
   (g:MvPolynomial σ L) (hg:Irreducible g)
   (hdivF:g∣MvPolynomial.map (algebraMap K L) F)
   (hdivM:g∣MvPolynomial.map (algebraMap K L) M):
   F∣M:=by
 have hm:M∈Ideal.comap (MvPolynomial.map (algebraMap K L))
     (Ideal.span {g}):=Ideal.mem_span_singleton.mpr hdivM
 rw [geometric_factor_contraction F hF g hg hdivF] at hm
 exact Ideal.mem_span_singleton.mp hm
theorem geometric_factor_not_dvd_of_original_not_dvd
   (F M:MvPolynomial σ K) (hF:Irreducible F) (hnot:¬ F∣M)
   (g:MvPolynomial σ L) (hg:Irreducible g)
   (hdivF:g∣MvPolynomial.map (algebraMap K L) F):
   ¬ g∣MvPolynomial.map (algebraMap K L) M:=by
 intro hdivM
 exact hnot (original_dvd_of_geometric_factor_dvd F M hF g hg hdivF hdivM)
end CoefficientExtension
end
end ProximityPrize.SubmissionLower.GeometricFactorContraction

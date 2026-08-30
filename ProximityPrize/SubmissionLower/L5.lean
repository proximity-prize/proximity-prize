import ProximityPrize.SubmissionLower.O2
namespace ProximityPrize.SubmissionLower.RCN186
variable {A:Type*} [CommRing A]
noncomputable def quotientPrime (I p:Ideal A):Ideal (A ⧸ I):=
 p.map (Ideal.Quotient.mk I)
theorem quotientPrime_isPrime (I p:Ideal A) [p.IsPrime]
   (hIp:I ≤ p):(quotientPrime I p).IsPrime:=by
 apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
 simpa only [Ideal.mk_ker] using hIp
noncomputable abbrev LocalizedQuotient (I p:Ideal A) [p.IsPrime]
   (hIp:I ≤ p):Type _:=
 @Localization.AtPrime (A ⧸ I) _ (quotientPrime I p)
   (quotientPrime_isPrime I p hIp)
theorem quotientPrime_comap_quotientMk (I p:Ideal A) [p.IsPrime]
   (hIp:I ≤ p):
   (quotientPrime I p).comap (Ideal.Quotient.mk I)=p:=by
 rw [quotientPrime,Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
 change p ⊔ RingHom.ker (Ideal.Quotient.mk I)=p
 rw [Ideal.mk_ker,sup_eq_left]
 exact hIp
theorem quotientMk_map_primeCompl (I p:Ideal A) [p.IsPrime]
   [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   Submonoid.map (Ideal.Quotient.mk I) p.primeCompl=
     (quotientPrime I p).primeCompl:=by
 apply SetLike.ext
 intro x
 constructor
 · rintro ⟨s,hs,rfl⟩
   intro hmem
   exact hs ((quotientPrime_comap_quotientMk I p hIp).symm ▸ hmem)
 · intro hx
   obtain ⟨s,rfl⟩:=Ideal.Quotient.mk_surjective x
   refine ⟨s,?_,rfl⟩
   intro hs
   apply hx
   change s∈(quotientPrime I p).comap (Ideal.Quotient.mk I)
   rw [quotientPrime_comap_quotientMk I p hIp]
   exact hs
noncomputable def ambientToLocalizedQuotient
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   Localization.AtPrime p →+*LocalizedQuotient I p hIp:=by
 have hM:=quotientMk_map_primeCompl I p hIp
 letI:IsLocalization (Submonoid.map (Ideal.Quotient.mk I) p.primeCompl)
     (LocalizedQuotient I p hIp):=hM.symm ▸ inferInstance
 exact IsLocalization.map (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I)
   p.primeCompl.le_comap_map
theorem ambientToLocalizedQuotient_surjective
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   Function.Surjective (ambientToLocalizedQuotient I p hIp):=by
 have hM:=quotientMk_map_primeCompl I p hIp
 letI:IsLocalization (Submonoid.map (Ideal.Quotient.mk I) p.primeCompl)
     (LocalizedQuotient I p hIp):=hM.symm ▸ inferInstance
 simpa only [ambientToLocalizedQuotient] using
   (IsLocalization.map_surjective_of_surjective p.primeCompl (Localization.AtPrime p)
     (LocalizedQuotient I p hIp) Ideal.Quotient.mk_surjective)
theorem ambientToLocalizedQuotient_ker
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   RingHom.ker (ambientToLocalizedQuotient I p hIp)=
     I.map (algebraMap A (Localization.AtPrime p)):=by
 have hM:=quotientMk_map_primeCompl I p hIp
 have hk:=IsLocalization.ker_map (S:=Localization.AtPrime p)
   (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I) hM
 let canonicalMap:Localization.AtPrime p →+*LocalizedQuotient I p hIp:=
   IsLocalization.map (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I)
     (hM.symm ▸ p.primeCompl.le_comap_map)
 have hmaps:ambientToLocalizedQuotient I p hIp=canonicalMap:=by
   apply IsLocalization.ringHom_ext p.primeCompl
   simp only [ambientToLocalizedQuotient,canonicalMap,IsLocalization.map_comp]
 rw [hmaps]
 change RingHom.ker canonicalMap=_
 calc
   RingHom.ker canonicalMap=RingHom.ker
       (IsLocalization.map (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I)
         (hM.symm ▸ p.primeCompl.le_comap_map)):=by
     congr 1
   _=I.map (algebraMap A (Localization.AtPrime p)):=by
     simpa only [Ideal.mk_ker] using hk
noncomputable def quotientAmbientEquivLocalizedQuotient
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) ≃+*
     LocalizedQuotient I p hIp:=
 (Ideal.quotEquivOfEq (ambientToLocalizedQuotient_ker I p hIp).symm).trans
   (RingHom.quotientKerEquivOfSurjective
     (ambientToLocalizedQuotient_surjective I p hIp))
end ProximityPrize.SubmissionLower.RCN186

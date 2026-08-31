import ProximityPrize.SubmissionLower.S
namespace ProximityPrize.SubmissionLower.RCN310
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {A:Type*} [CommRing A]
theorem exists_multiplier_mem_sup_pow_of_localized_mem
   (I p:Ideal A) (hIp:I ≤ p)
   (pbar:Ideal (A ⧸ I)) [pbar.IsPrime]
   (hpbar:pbar=Ideal.map (Ideal.Quotient.mk I) p)
   (x:A) (n:ℕ)
   (hx:algebraMap (A ⧸ I) (Localization.AtPrime pbar)
     (Ideal.Quotient.mk I x)∈
       IsLocalRing.maximalIdeal (Localization.AtPrime pbar)^n):
   ∃ s:A,s∉p∧s*x∈I ⊔ p^n:=by
 let S:=A ⧸ I
 let L:=Localization.AtPrime pbar
 let q:A →+*S:=Ideal.Quotient.mk I
 have hxMap:algebraMap S L (q x)∈
     Ideal.map (algebraMap S L) (pbar^n):=by
   rw [Ideal.map_pow,IsLocalization.AtPrime.map_eq_maximalIdeal pbar L]
   exact hx
 rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
   pbar.primeCompl L] at hxMap
 obtain ⟨m,hmM,hmprod⟩:=hxMap
 obtain ⟨s,hs⟩:=Ideal.Quotient.mk_surjective m
 have hcomap:Ideal.comap q pbar=p:=by
   rw [hpbar,Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
     ←RingHom.ker_eq_comap_bot,Ideal.mk_ker,sup_eq_left.mpr hIp]
 have hsnot:s∉p:=by
   intro hsp
   have hqsp:q s∈pbar:=by
     change s∈Ideal.comap q pbar
     rwa [hcomap]
   exact hmM (hs ▸ hqsp)
 have hmprod':q (s*x)∈pbar^n:=by
   simpa only [q,map_mul,hs] using hmprod
 have hmapped:q (s*x)∈Ideal.map q (p^n):=by
   rw [Ideal.map_pow, ←hpbar]
   exact hmprod'
 have hcomapPow:s*x∈Ideal.comap q (Ideal.map q (p^n)):=hmapped
 rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
   ←RingHom.ker_eq_comap_bot,Ideal.mk_ker] at hcomapPow
 exact ⟨s,hsnot,by simpa only [sup_comm] using hcomapPow⟩
theorem isPrimary_of_maximal_power_le_le
   (J Q:Ideal A) [J.IsMaximal] (n:ℕ) (hn:1 ≤ n)
   (hpow:J^n ≤ Q) (hle:Q ≤ J):Q.IsPrimary:=by
 apply Ideal.isPrimary_of_isMaximal_radical
 have hrad:Ideal.radical Q=J:=by
   apply le_antisymm
   · exact (inferInstance:J.IsPrime).radical_le_iff.mpr hle
   · intro x hx
     exact ⟨n,hpow (Ideal.pow_mem_pow hx n)⟩
 rw [hrad]
 exact inferInstance
theorem mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
   (surface x s:A) (J:Ideal A) [J.IsMaximal]
   (hsurface:surface∈J) (n:ℕ) (hn:1 ≤ n)
   (hs:s∉J)
   (hmul:s*x∈Ideal.span {surface} ⊔ J^n):
   x∈Ideal.span {surface} ⊔ J^n:=by
 let Q:=Ideal.span {surface} ⊔ J^n
 have hpow:J^n ≤ Q:=le_sup_right
 have hle:Q ≤ J:=by
   exact sup_le (Ideal.span_le.mpr (by simpa))
     (Ideal.pow_le_self (Nat.ne_of_gt hn))
 have hprimary:Q.IsPrimary:=
   isPrimary_of_maximal_power_le_le J Q n hn hpow hle
 have hcases:=(Ideal.isPrimary_iff.mp hprimary).2
   (by simpa only [mul_comm] using hmul)
 rcases hcases with hxQ | hsrad
 · exact hxQ
 · have hrad:Ideal.radical Q=J:=by
     apply le_antisymm
     · exact (inferInstance:J.IsPrime).radical_le_iff.mpr hle
     · intro y hy
       exact ⟨n,hpow (Ideal.pow_mem_pow hy n)⟩
   exact False.elim (hs (hrad ▸ hsrad))
theorem mapped_mem_span_sup_pow_of_localized_mem
   {B:Type*} [CommRing B]
   (I p:Ideal A) (hIp:I ≤ p)
   (pbar:Ideal (A ⧸ I)) [pbar.IsPrime]
   (hpbar:pbar=Ideal.map (Ideal.Quotient.mk I) p)
   (x:A) (n:ℕ) (hn:1 ≤ n)
   (hx:algebraMap (A ⧸ I) (Localization.AtPrime pbar)
     (Ideal.Quotient.mk I x)∈
       IsLocalRing.maximalIdeal (Localization.AtPrime pbar)^n)
   (f:A →+*B) (surface:B) (J:Ideal B) [J.IsMaximal]
   (hmapI:Ideal.map f I ≤ Ideal.span {surface})
   (hsurface:surface∈J)
   (hcontract:Ideal.comap f J=p):
   f x∈Ideal.span {surface} ⊔ J^n:=by
 obtain ⟨s,hsnot,hsx⟩:=
   exists_multiplier_mem_sup_pow_of_localized_mem
     I p hIp pbar hpbar x n hx
 have hmapP:Ideal.map f p ≤ J:=by
   rw [Ideal.map_le_iff_le_comap,hcontract]
 have hmapPow:Ideal.map f (p^n) ≤ J^n:=by
   rw [Ideal.map_pow]
   exact pow_le_pow_left' hmapP n
 have htarget:Ideal.map f (I ⊔ p^n) ≤
     Ideal.span {surface} ⊔ J^n:=by
   rw [Ideal.map_sup]
   exact sup_le (hmapI.trans le_sup_left) (hmapPow.trans le_sup_right)
 have hmul:f s*f x∈Ideal.span {surface} ⊔ J^n:=by
   rw [←map_mul]
   exact htarget (Ideal.mem_map_of_mem f hsx)
 have hfs:f s∉J:=by
   intro h
   apply hsnot
   rw [←hcontract]
   exact h
 exact mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
   surface (f x) (f s) J hsurface n hn hfs hmul
end
end ProximityPrize.SubmissionLower.RCN310

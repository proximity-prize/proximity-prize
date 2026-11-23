import ProximityPrize.SubmissionLower.ZsE91Ed
set_option Elab.async false
set_option maxRecDepth 4000
namespace q97A7gc
open Polynomial

open q7kdBxd qqi5QRb


section am5
variable {R K:Type*} [CommRing R] [Field K] [Algebra R K]
private abbrev Ek (u:K) :Ideal R :=
 (Algebra.linearMap R K).range.colon {u}
private theorem bsA {x :R} {u:K} :
  x∈Ek u ↔ ∃ y :R,algebraMap R K x*u=algebraMap R K y := by
 rw [Submodule.mem_colon_singleton,LinearMap.mem_range,Algebra.smul_def]
 exact exists_congr fun _=>eq_comm
private theorem prime_denominator_height [IsNoetherianRing R] [IsDomain R]
    [IsIntegrallyClosedIn R K] (P:Ideal R) [P.IsPrime] (v :K)
    (hP:P=Ek v) (hne :P ≠ ⊥) :P.height = 1 := by
  have hclosed:=(isIntegrallyClosedIn_iff (R:=R) (A:=K)).mp inferInstance
  have hmem {x :R} : x∈P ↔ ∃ y :R,algebraMap R K x*v=algebraMap R K y :=
    hP ▸ bsA
  let N :=Submodule.map (Algebra.linearMap R K) P
  have hN :N ≠ ⊥ := by
    obtain ⟨x,hx,hx0⟩:=(Submodule.ne_bot_iff P).mp hne
    exact (Submodule.ne_bot_iff N).mpr ⟨algebraMap R K x,⟨x,hx,rfl⟩,
      fun e=>hx0 (hclosed.1 (e.trans (map_zero _).symm))⟩
  have hex : ∃ x∈P,∃ y∉P,algebraMap R K x*v=algebraMap R K y := by
    by_contra! h
    have hstable : ∀ z∈N,v•z∈N := by
      rintro _ ⟨x,hx,rfl⟩
      obtain ⟨y,hy⟩:=hmem.mp hx
      have hyP:y∈P:= by
        by_contra hyP
        exact h x hx y hyP hy
      exact ⟨y,hyP,hy.symm.trans (mul_comm _ _)⟩
    have hint :=isIntegral_of_smul_mem_submodule N hN
      ((IsNoetherian.noetherian P).map _) v hstable
    obtain ⟨y,hy⟩:=hclosed.2 hint
    exact ‹P.IsPrime›.one_notMem (hmem.mpr ⟨y,by simpa only [map_one,one_mul] using hy.symm⟩)
  obtain ⟨x,hx,y,hy,hxy⟩:=hex
  have hmin:P∈(Ideal.span {x}).minimalPrimes := by
    refine ⟨⟨inferInstance,(Ideal.span_singleton_le_iff_mem _).mpr hx⟩,?_⟩
    rintro Q ⟨hQ,hxQ⟩ hQP b hb
    obtain ⟨c,hbc⟩:=hmem.mp hb
    have he :y*b=x*c:=hclosed.1 (by
      rw [map_mul,map_mul,← hxy,← hbc]
      ring)
    have hmul :y*b∈Q :=
      he ▸ Q.mul_mem_right c (hxQ (Ideal.mem_span_singleton_self x))
    exact (hQ.mem_or_mem hmul).resolve_left fun hyQ=>hy (hQP hyQ)
  exact le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin)
    (Order.one_le_iff_ne_zero.mpr fun e=>hne (Ideal.height_eq_zero_iff_eq_bot.mp e))
private theorem detect_denominator {A:Type*} [CommRing A] [IsNoetherianRing R]
  [IsDomain R] [IsIntegrallyClosedIn R K] (f :A →+* R) (M:Ideal A) [M.IsPrime] (u:K)
  (hM: (Ek u).comap f≤M) (hne :Ek (R:=R) u ≠ ⊥) :
  ∃ P:Ideal R,P.IsPrime∧P.height = 1∧P.comap f≤M∧Ek u≤P:= by
 let D:Ideal R:=Ek u
 obtain ⟨Q,hDQ,hQ,hQM⟩:=Ideal.exists_ideal_comap_le_prime M D hM
 have :Q.IsPrime :=hQ
 obtain ⟨P,hP,hPQ⟩:=Ideal.exists_minimalPrimes_le hDQ
 have :P.IsPrime :=hP.isPrime
 obtain ⟨v,hv⟩:=Submodule.exists_eq_colon_of_mem_minimalPrimes
  (N :=(Algebra.linearMap R K).range) (x :=u) hP
 have hDP:D ≤P:=hP.le
 have hpne :P ≠ ⊥ := fun e=>hne (bot_unique (hDP.trans_eq e))
 exact ⟨P,hP.isPrime,prime_denominator_height P v hv hpne,
  (Ideal.comap_mono hPQ).trans hQM,hDP⟩
end am5
private theorem detect_normal {A K:Type*} [CommRing A] [Field K] [Algebra A K]
   [IsNoetherianRing A] [Module.Finite A (integralClosure A K)]
   (M:Ideal A) [M.IsPrime] (u:K)
   (hu : ∀ a :A,a∉M → ¬ IsIntegral A (algebraMap A K a*u))
   (hden : ∃ b:A,algebraMap A K b≠0∧IsIntegral A (algebraMap A K b*u)) :
   ∃ P:Ideal (integralClosure A K),P.IsPrime∧P.height = 1 ∧
     P.comap (algebraMap A (integralClosure A K))≤M ∧
     ¬ (∃ a :integralClosure A K,a∉P ∧ ∃ b:integralClosure A K,(a :K)*u=b) := by
 let R:Type _:=integralClosure A K
 let f :A →+* R:=algebraMap A R
 have :IsNoetherianRing R:=IsNoetherianRing.of_finite A R
 let D:Ideal R:=Ek (R:=R) (K:=K) u
 have hmem (a :R) :a∈D↔IsIntegral A (algebraMap R K a*u) := by
   rw [show D =Ek (R:=R) (K:=K) u from rfl,bsA]
   constructor
   · rintro ⟨b,hb⟩
     rw [hb]
     exact b.property
   · intro h
     exact ⟨⟨_,h⟩,rfl⟩
 have hcomap :D.comap f≤M:= by
   intro a ha
   by_contra h
   exact hu a h ((hmem (f a)).mp ha)
 obtain ⟨b,hb,hint⟩:=hden
 have hne :D ≠ ⊥ := by
   intro e
   have hd:f b∈D:=(hmem (f b)).mpr hint
   have hz :f b=0:=Ideal.mem_bot.mp (e ▸ hd)
   exact hb (congrArg (algebraMap R K) hz |>.trans (map_zero _))
 obtain ⟨P,hP,hh,hPM,hDP⟩:=detect_denominator (R:=R) (K:=K) f M u hcomap hne
 refine ⟨P,hP,hh,hPM,?_⟩
 rintro ⟨s,hs,t,ht⟩
 have hsD:s∈D:=(bsA (R:=R) (K:=K)).mpr ⟨t,ht⟩
 exact hs (hDP hsD)
end q97A7gc

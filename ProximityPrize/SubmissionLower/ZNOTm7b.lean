import ProximityPrize.SubmissionLower.ZSYEDJb
import ProximityPrize.SubmissionLower.ZAcMpba
set_option Elab.async false
namespace q1vkLGd
noncomputable section
open Finset MvPolynomial
open P5 (K)
open cu (L)
open qQ9yWTb (Curve Usable)
open scoped Classical Polynomial
open qe6nVeb (immersedAt)
open private bad_count from ProximityPrize.SubmissionLower.ZTV7u3a
open private ps_algMap from ProximityPrize.SubmissionLower.ZSYEDJb
def c1 :Prop :=
  ∀ (T:Finset K) (s :K→Fin 2→L),Set.InjOn s (T:Set K) → ∀ d:ℕ,
    (∃ f :Curve,f≠0∧f.totalDegree≤d ∧ ∀ γ∈T,eval (s γ) f=0) ∨
      ∃ U⊆T,(d+1)*(d+2)≤2*U.card ∧
        ∃ f :Curve,f≠0∧f.totalDegree≤d+1 ∧ ∀ γ∈U,Smooth f (s γ)
def c2 :Prop :=FormalLift
private theorem smooth_usable (hl:FormalLift) {q:Curve} {z :Fin 2→L}
  (h:Smooth q z) :Usable q z := by
 obtain ⟨hz,i,hi⟩:=h
 obtain ⟨a,hc,ha,hfree⟩:=hl q z i hz hi
 obtain ⟨j,hji⟩:=exists_ne i
 refine ⟨a,hc,ha,j,?_⟩
 rw [hfree j hji]
 simp
private theorem usable_eval {q:Curve} {z :Fin 2→L} (h:Usable q z) :
  eval z q=0:= by
 obtain ⟨a,hc,ha,_⟩:=h
 have he :=MvPolynomial.hom_eval₂ q PowerSeries.C PowerSeries.constantCoeff a
 have hC: (PowerSeries.constantCoeff (R:=L)).comp PowerSeries.C=RingHom.id L:= by
  ext r
  exact PowerSeries.constantCoeff_C r
 rw [ha,map_zero,hC,show (fun i=>PowerSeries.constantCoeff (a i))=z from funext hc] at he
 exact he.symm
private theorem usable_mul {q r :Curve} {z :Fin 2→L} (h:Usable (q*r) z) :
  Usable q z∨Usable r z := by
 obtain ⟨a,hc,ha,ht⟩:=h
 rw [eval₂_mul] at ha
 exact (mul_eq_zero.mp ha).imp (fun hq=>⟨a,hc,hq,ht⟩) (fun hr=>⟨a,hc,hr,ht⟩)
private theorem usable_iff_immersed (q:Curve) (z :Fin 2→L) :
   Usable q z↔immersedAt q z := by
 constructor
 · rintro ⟨a,hc,he,ht⟩
   exact ⟨a,hc,ht,by simpa only [ps_algMap] using he⟩
 · rintro ⟨a,hc,ht,he⟩
   exact ⟨a,hc,by simpa only [ps_algMap] using he,ht⟩
private theorem loss {U:Finset K} {s :K→Fin 2→L} (hinj:Set.InjOn s (U:Set K))
  {q:Curve} (hq:Irreducible q) (hz : ∀ γ∈U,eval (s γ) q=0)
  (hn : ∀ γ∈U,¬ Usable q (s γ)) :3*U.card≤q.totalDegree*(q.totalDegree-1) := by
 simpa only [← usable_iff_immersed,filter_true_of_mem hn] using
  bad_count qYzLClc.proof qGzrWfb.proof hinj hq hz
private theorem count_factors (p:Curve→(Fin 2→L)→Prop)
   (at_root : ∀ q z,p q z→eval z q=0)
   (on_mul : ∀ q r z,p (q*r) z→p q z∨p r z)
   {T:Finset K} {s :K→Fin 2→L} {b c:ℚ} (hc:0≤ c)
   (jX : ∀ q:Curve,Irreducible q → ∀ U⊆T,(∀ γ∈U,p q (s γ)) →
     (U.card:ℚ)≤b*q.totalDegree+c*(q.totalDegree :ℚ)^2)
   (f :Curve) :f≠0 → ∀ U⊆T,(∀ γ∈U,p f (s γ)) →
     (U.card:ℚ)≤b*f.totalDegree+c*(f.totalDegree :ℚ)^2 := by
 let:UniqueFactorizationMonoid Curve :=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
 refine WfDvdMonoid.induction_on_irreducible f (fun h=>(h rfl).elim) ?_ ?_
 · intro q hq _ U _ hp
   have he :U = ∅ := eq_empty_iff_forall_notMem.mpr fun γ hγ =>
     (hq.map (eval (s γ))).ne_zero (at_root q (s γ) (hp γ hγ))
   have hd:q.totalDegree=0:= by
     have h:=totalDegree_le_of_dvd_of_isDomain (isUnit_iff_dvd_one.mp hq) (one_ne_zero)
     simpa using h
   simp [he,hd]
 · intro r q hr hq ih _ U hU hp
   let A:=U.filter fun γ=>p q (s γ)
   let B:=U.filter fun γ => ¬ p q (s γ)
   have hA:=jX q hq A (filter_subset _ _ |>.trans hU)
     (fun γ hγ=>(mem_filter.mp hγ).2)
   have hB:=ih hr B (filter_subset _ _ |>.trans hU) fun γ hγ=> by
     obtain ⟨hg,hn⟩:=mem_filter.mp hγ
     exact (on_mul q r (s γ) (hp γ hg)).resolve_left hn
   have hpart: (U.card:ℚ)=(A.card:ℚ)+(B.card:ℚ) := by
     exact_mod_cast (card_filter_add_card_filter_not (s :=U) (p:= fun γ=>p q (s γ))).symm
   rw [hpart,totalDegree_mul_of_isDomain hq.ne_zero hr,Nat.cast_add]
   apply (add_le_add hA hB).trans
   have hcross :0≤ c*((q.totalDegree :ℚ)*r.totalDegree) :=
     mul_nonneg hc (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
   nlinarith only [hcross]
private theorem filter_count {T U:Finset K} {s :K→Fin 2→L} {q:Curve} {b:ℚ}
  (hU:U⊆T) (h: ((T.filter fun γ=>Usable q (s γ)).card:ℚ)≤b*q.totalDegree) :
  ((U.filter fun γ=>Usable q (s γ)).card:ℚ)≤b*q.totalDegree :=
 le_trans (by exact_mod_cast card_le_card (filter_subset_filter _ hU)) h
end
end q1vkLGd

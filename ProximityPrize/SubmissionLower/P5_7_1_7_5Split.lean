import ProximityPrize.SubmissionLower.ZL8vffb
import ProximityPrize.SubmissionLower.ZNOTm7b
set_option Elab.async false
set_option autoImplicit true
namespace q1vkLGd
noncomputable section
open Finset MvPolynomial
open P5 (K)
open cu (L)
open qQ9yWTb (Curve Usable)
open scoped Classical Polynomial
def c3:Prop :=
  ∀ (T:Finset K) (s :K→Fin 2→L),Set.InjOn s (T:Set K) →
    ∀ q:Curve,Irreducible q→(∀ γ∈T,eval (s γ) q=0) →
      Nonempty (Projection T s q)
def c4 :Prop :=
  FormalLift →
    ∀ (f :nC) (z :Fin 2→L),f.Monic→Transverse f (z 0) (z 1) →
      ¬ Usable (u7 f) z→(Polynomial.X-Polynomial.C (z 0))^3∣discr f
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
private theorem loss (h3:c3) (h4 :c4) (h2 :FormalLift)
    {U:Finset K} {s :K→Fin 2→L} (hinj:Set.InjOn s (U:Set K))
    {q:Curve} (hq:Irreducible q) (hz : ∀ γ∈U,eval (s γ) q=0)
    (hn : ∀ γ∈U,¬ Usable q (s γ)) :3*U.card≤q.totalDegree*(q.totalDegree-1) := by
  obtain ⟨P⟩:=h3 U s hinj q hq hz
  let l (γ:K) :L[X] :=Polynomial.X-Polynomial.C (P.point γ 0)
  have hdvd: (∏ γ∈U,l γ^3)∣discr P.equation := by
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero_of_ne fun he=>hij (P.separates hi hj he)).isUnit).pow
    · intro γ hγ
      exact h4 h2 P.equation (P.point γ) P.monic (P.ct4 γ hγ)
        (fun h=>hn γ hγ (P.pullback γ hγ h))
  have hd (γ:K) : (l γ^3).natDegree=3:= by
    rw [(Polynomial.monic_X_sub_C _).natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one]
  have hp: (∏ γ∈U,l γ^3).natDegree=3*U.card:= by
    rw [Polynomial.natDegree_prod U (fun γ=>l γ^3) (fun γ _ =>
      pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))]
    simp [hd,Nat.mul_comm]
  exact (hp ▸ Polynomial.natDegree_le_of_dvd hdvd P.nonzero).trans P.degree
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
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :qQ9yWTb.c5:= by
  intro T s hinj b hb cap
  let d := ⌊2*b⌋₊
  have hdb: (d:ℚ)≤2*b:=Nat.floor_le (by positivity)
  rcases h1 T s hinj d with ⟨f,hf,hd,hz⟩ | ⟨U,hU,hcard,f,hf,hd,hs⟩
  · have hp (q:Curve) (hq:Irreducible q) (U:Finset K) (hU:U⊆T)
        (hu : ∀ γ∈U,eval (s γ) q=0) :
        (U.card:ℚ)≤b*q.totalDegree+(1/3:ℚ)*(q.totalDegree :ℚ)^2 := by
      let V:=U.filter fun γ => ¬ Usable q (s γ)
      have hV:V⊆U:=filter_subset _ _
      have hbad:=loss h3 h4 h2 (hinj.mono (show (V:Set K)⊆T from hV.trans hU))
        hq (fun γ hγ=>hu γ (hV hγ)) (fun γ hγ=>(mem_filter.mp hγ).2)
      have hbad' : 3*(V.card:ℚ)≤(q.totalDegree :ℚ)^2 := by
        rw [pow_two]
        exact_mod_cast hbad.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      have hgood:=filter_count hU (cap q hq)
      have hpart: (U.card:ℚ)=((U.filter fun γ=>Usable q (s γ)).card:ℚ)+V.card:= by
        exact_mod_cast (card_filter_add_card_filter_not
          (s :=U) (p:= fun γ=>Usable q (s γ))).symm
      linarith only [hbad',hgood,hpart]
    have H :=count_factors (fun q z=>eval z q=0) (fun _ _ h=>h)
      (fun _ _ _ h=>mul_eq_zero.mp (by simpa only [map_mul] using h))
      (by norm_num : (0:ℚ)≤1/3) hp f hf T (Subset.rfl) hz
    have hdeg: (f.totalDegree :ℚ)≤2*b:=(by exact_mod_cast hd: (f.totalDegree :ℚ)≤d).trans hdb
    have hlin:=mul_le_mul_of_nonneg_left hdeg hb
    have hsq:=pow_le_pow_left₀ (Nat.cast_nonneg f.totalDegree : (0:ℚ)≤_) hdeg 2
    linarith only [H,hlin,hsq]
  · have hp (q:Curve) (hq:Irreducible q) (V:Finset K) (hV:V⊆T)
        (hv : ∀ γ∈V,Usable q (s γ)) :
        (V.card:ℚ)≤b*q.totalDegree+0*(q.totalDegree :ℚ)^2 := by
      have he :V.filter (fun γ=>Usable q (s γ))=V:=filter_true_of_mem hv
      simpa only [he,zero_mul,add_zero] using filter_count hV (cap q hq)
    have H :=count_factors Usable (fun _ _=>usable_eval) (fun _ _ _=>usable_mul)
      (le_refl (0:ℚ)) hp f hf U hU (fun γ hγ=>smooth_usable h2 (hs γ hγ))
    have hdeg: (f.totalDegree :ℚ)≤(d:ℚ)+1 := by exact_mod_cast hd
    have hmul :=mul_le_mul_of_nonneg_left hdeg hb
    have hb' : 2*b<(d:ℚ)+2 :=(Nat.lt_floor_add_one _).trans (by linarith)
    have hlt:=mul_lt_mul_of_pos_left hb' (by positivity :0<(d:ℚ)+1)
    have hcard' : ((d:ℚ)+1)*((d:ℚ)+2)≤2*(U.card:ℚ) := by exact_mod_cast hcard
    exfalso
    simp only [zero_mul,add_zero] at H
    linarith only [H,hmul,hlt,hcard']
end
end q1vkLGd

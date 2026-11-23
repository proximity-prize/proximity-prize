import ProximityPrize.SubmissionLower.ZYfUQxc
import ProximityPrize.SubmissionLower.ZwEplQa
set_option Elab.async false
open _root_ renaming Ideal.Quotient.factorₐ→ oj,Irreducible→nq,Module.Finite→nI,Module.finrank→lJ,MvPolynomial.X→nX,MvPolynomial.affineHilbertPolynomial→lI,Nat.add_le_add→mD,Nat.mul_add→lV,Nat.mul_le_mul_left→lz,WfDvdMonoid.induction_on_irreducible→ oq,le_sup_left→n5,qe6nVeb.SeedPlane→aU,qe6nVeb.immersedAt→cy,qe6nVeb.immersedMarks→c9
set_option autoImplicit true
namespace q7YMR4d
noncomputable section
open P5 (K)
open cu (L)
open qe6nVeb (SeedPlane immersedAt immersedMarks)
open MvPolynomial Finset
open scoped Classical
def c1 :Prop :=
  (∀ (q:aU) a,SmoothAt q a→cy q a) ∧
  (∀ (q:aU) a,eval a q=0→(∀ i,eval a (pderiv i q)=0) →
    simpleQuadratic q a→cy q a)
def c2 :Prop :=
  ∀ (z :K→Fin 2→L) (T:Finset K) (d:ℕ),Set.InjOn z (T:Set K) →
    (∀ q:aU,q.totalDegree≤d→(∀ γ∈T,eval (z γ) q=0)→q=0) →
    ∃ q:aU,q≠0∧q.totalDegree≤d+1 ∧
      (d+1)*(d+2)≤2*(smoothMarks q z T).card
def c3:Prop :=
  ∀ (q:aU) (a :Fin 2→L) (i:Fin 2),
    eval a q=0→(∀ j,eval a (pderiv j q)=0) → ¬ simpleQuadratic q a →
      3≤lJ L (aU ⧸ (ke q (pderiv i q) ⊔ oF a^3))
private theorem degree_pos {q:aU} (hq:nq q) :0<q.totalDegree := by
 apply Nat.pos_of_ne_zero
 intro h
 have he :=totalDegree_eq_zero_iff_eq_C.mp h
 apply hq.not_isUnit
 exact isUnit_iff_totalDegree_of_isReduced.mpr
  ⟨isUnit_iff_ne_zero.mpr (fun hz=>hq.ne_zero (by rw [he,hz,map_zero])),h⟩
private theorem cut_upper {q g:aU} (hq:nq q) (hg:g≠0)
   (hd:g.totalDegree<q.totalDegree) :
   nI L (aU ⧸ ke q g) ∧
     lJ L (aU ⧸ ke q g)≤g.totalDegree*q.totalDegree := by
 let P:Ideal SeedPlane :=Ideal.span {q}
 let J:=ke q g
 let:UniqueFactorizationMonoid SeedPlane :=MvPolynomial.uniqueFactorizationMonoid (Fin 2)
 have hP:P.IsPrime :=
   (Ideal.span_singleton_prime hq.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hq)
 have hgp:g∉P:= fun hm=>(not_le_of_gt hd)
   (totalDegree_le_of_dvd_of_isDomain (Ideal.mem_span_singleton.mp hm) hg)
 have hp: (lI P).natDegree=1 := by
   have h:=natDegree_affineHilbertPolynomial_span_singleton_add_one hq.ne_zero hP.ne_top
   change (lI P).natDegree+1=Nat.card (Fin 2) at h
   rw [Nat.card_eq_fintype_card,Fintype.card_fin] at h
   omega
 have hl: (lI P).leadingCoeff=(q.totalDegree :ℚ) := by
   have h:=affineDegree_span_singleton hq.ne_zero
   change affineDegree P= _ at h
   simpa only [affineDegree,hp,Nat.factorial_one,Nat.cast_one,one_mul] using h
 have hcut:=principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
   hP hgp (le_refl g.totalDegree)
 have hJ: (lI J).natDegree=0:= by
   change (lI (P ⊔ Ideal.span {g})).natDegree=0
   exact Nat.eq_zero_of_le_zero (by simpa only [hp,Nat.sub_self] using hcut.1)
 have hfin:nI L (aU ⧸ J) :=
   moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hJ
 refine ⟨hfin,?_⟩
 have h:=hcut.2
 change (lI J).coeff _≤_ at h
 rw [affineHilbertPolynomial_eq_C_finrank,hp,Nat.sub_self,Polynomial.coeff_C_zero,
   Nat.cast_one,mul_one,hl] at h
 exact_mod_cast h
private theorem pointIdeals_ne {a b:Fin 2→L} (h:a≠b) :
  oF a≠oF b:= by
 intro e
 apply h
 funext i
 have ha :nX i - C (a i)∈oF a := by
  change eval a (nX i - C (a i))=0
  simp
 rw [e] at ha
 change eval b (nX i - C (a i))=0 at ha
 simpa only [map_sub,eval_X,eval_C,sub_eq_zero,eq_comm] using ha
private theorem pointIdeal_maximal (a :Fin 2→L) : (oF a).IsMaximal :=
 RingHom.ker_isMaximal_of_surjective (eval a) fun x=>⟨C x,eval_C x⟩
private theorem cut_lower {q g:aU} [nI L (aU ⧸ ke q g)]
   {z :K→Fin 2→L} {T:Finset K} (hz :Set.InjOn z (T:Set K))
   (hl : ∀ γ∈T,3≤lJ L
     (aU ⧸ (ke q g ⊔ oF (z γ)^3))) :
   3*T.card≤lJ L (aU ⧸ ke q g) := by
 classical
 let J:=ke q g
 let D (γ:T) :=oF (z γ)
 let P (γ:T) :=J ⊔ D γ^3
 have hc:Pairwise (fun γ η:T=>IsCoprime (P γ) (P η)) := by
   intro γ η hne
   let: (D γ).IsMaximal:=pointIdeal_maximal _
   let: (D η).IsMaximal:=pointIdeal_maximal _
   have hd:D γ≠D η :=
     pointIdeals_ne fun h=>hne (Subtype.ext (hz γ.prop η.prop h))
   have hp:D γ^3 ⊔ D η^3 = ⊤ :=
     Ideal.pow_sup_pow_eq_top (Ideal.isCoprime_iff_sup_eq.mp (Ideal.isCoprime_of_isMaximal hd))
   apply Ideal.isCoprime_iff_sup_eq.mpr
   apply top_unique
   rw [← hp]
   exact sup_le_sup le_sup_right le_sup_right
 let F: (aU ⧸ J) →ₗ[L] (∀ γ:T,aU ⧸ P γ) :=
   LinearMap.pi fun γ=>(oj L (I:=J) (J:=P γ) n5).toLinearMap
 have hF:Function.Surjective F:= by
   intro t
   obtain ⟨r,hr⟩:=Ideal.pi_quotient_surjective hc t
   exact ⟨Ideal.Quotient.mk J r,funext hr⟩
 let (γ:T) :nI L (aU ⧸ P γ) :=
   Module.Finite.of_surjective (oj L n5).toLinearMap
     (Ideal.Quotient.factor_surjective n5)
 let (γ:T) :Module.Free L (aU ⧸ P γ) :=Module.Free.of_divisionRing L _
 have h:=LinearMap.finrank_le_finrank_of_surjective (f :=F) hF
 rw [Module.finrank_pi_fintype L] at h
 calc
   3*T.card = ∑ _:T,3:= by simp [Nat.mul_comm]
   _ ≤ ∑ γ:T,lJ L (aU ⧸ P γ) :=sum_le_sum fun γ _=>hl γ γ.prop
   _≤_:=h
private theorem immersed_product {q r :aU} {a :Fin 2→L}
  (h:cy (q*r) a) :cy q a∨cy r a := by
 obtain ⟨t,h₀,h₁,h₂⟩:=h
 rw [← coe_eval₂Hom,map_mul,mul_eq_zero] at h₂
 exact h₂.imp (fun hq=>⟨t,h₀,h₁,hq⟩) (fun hr=>⟨t,h₀,h₁,hr⟩)
private theorem immersed_unit {q:aU} (hq:IsUnit q) {a :Fin 2→L}
  (h:cy q a) :False := by
 obtain ⟨t,_,_,ht⟩:=h
 exact (hq.map (eval₂Hom (algebraMap L (PowerSeries L)) t)).ne_zero ht
private theorem immersed_count {z :K→Fin 2→L} {T:Finset K} {B:ℕ}
    (h : ∀ q:aU,nq q→(c9 q z T).card≤B*q.totalDegree)
    {q:aU} (hq:q≠0) : (c9 q z T).card≤B*q.totalDegree := by
  classical
  revert hq
  induction q using oq with
  | zero=>intro hq; exact (hq rfl).elim
  | unit q hu =>
    intro _
    have he :c9 q z T = ∅ := eq_empty_iff_forall_notMem.mpr
      fun _ hγ=>immersed_unit hu (mem_filter.mp hγ).2
    simp [he]
  | mul a q ha hq ih =>
    intro _
    rw [totalDegree_mul_of_isDomain hq.ne_zero ha,lV]
    calc
      _≤(c9 q z T∪c9 a z T).card :=
        card_le_card fun γ hγ=> by
          obtain ⟨hm,hs⟩:=mem_filter.mp hγ
          exact mem_union.mpr ((immersed_product hs).imp
            (fun hs=>mem_filter.mpr ⟨hm,hs⟩) (fun hs=>mem_filter.mpr ⟨hm,hs⟩))
      _≤_:=card_union_le _ _
      _≤_:=mD (h q hq) (ih ha)
private theorem bad_count (h₁:c1) (h₃:c3)
   {z :K→Fin 2→L} {T:Finset K} (hz :Set.InjOn z (T:Set K))
   {q:aU} (hq:nq q) (hr : ∀ γ∈T,eval (z γ) q=0) :
   3*(T.filter fun γ => ¬ cy q (z γ)).card≤q.totalDegree*(q.totalDegree-1) := by
 classical
 let U:=T.filter fun γ => ¬ cy q (z γ)
 obtain ⟨i,hi⟩:=polar_exists q hq
 have hd: (pderiv i q).totalDegree≤q.totalDegree-1 := by
   simpa only [weightedTotalDegree_one,Pi.one_apply] using
     weightedTotalDegree_pderiv_le_sub (1 :Fin 2→ℕ) i q
 obtain ⟨hfin,hu⟩:=cut_upper hq hi (hd.trans_lt (by have :=degree_pos hq; omega))
 let:=hfin
 have hl : ∀ γ∈U,3≤lJ L
     (aU ⧸ (ke q (pderiv i q) ⊔ oF (z γ)^3)) := by
   intro γ hγ
   obtain ⟨hm,hn⟩:=mem_filter.mp hγ
   have ha :=hr γ hm
   have hgrad : ∀ j,eval (z γ) (pderiv j q)=0 :=
     fun j=>not_not.mp fun hj=>hn (h₁.1 q _ ⟨ha,j,hj⟩)
   exact h₃ q _ i ha hgrad (fun hs=>hn (h₁.2 q _ ha hgrad hs))
 exact (cut_lower (hz.mono (filter_subset _ _)) hl).trans
   (hu.trans ((Nat.mul_le_mul_right _ hd).trans_eq (Nat.mul_comm _ _)))
private theorem reserve_add (a b:ℕ) :
  a*(a-1)+b*(b-1)≤(a+b)*(a+b-1) := by
 rw [Nat.add_mul]
 exact mD (lz _ (by omega)) (lz _ (by omega))
theorem of_children (h₁:c1) (h₂:c2) (h₃:c3) :qe6nVeb.c4 := by
  classical
  intro z T hz B hB hImm
  let d:=2*B-1
  have hd:d+1=2*B:= by dsimp [d]; omega
  have hex : ∃ q:aU,q≠0∧q.totalDegree≤d ∧ ∀ γ∈T,eval (z γ) q=0:= by
    by_contra hn
    obtain ⟨q,hq,hdeg,hs⟩:=h₂ z T d hz (fun r hr hvan=> by
      by_contra hne
      exact hn ⟨r,hne,hr,hvan⟩)
    have hm: (smoothMarks q z T).card≤(c9 q z T).card :=
      card_le_card fun γ hγ =>
        let ⟨hT,hs⟩:=mem_filter.mp hγ
        mem_filter.mpr ⟨hT,h₁.1 q _ hs⟩
    have hs' := hs.trans (lz _ (hm.trans ((immersed_count hImm hq).trans
      (lz _ hdeg))))
    have he :d+2=2*B+1 := by omega
    rw [he] at hs'
    rw [lV,Nat.mul_one] at hs'
    have hh:2*(B*(d+1))=(d+1)*(2*B) := by ring
    rw [hh] at hs'
    omega
  obtain ⟨q,hq,hdeg,hvan⟩:=hex
  have count (q:aU) (hq:q≠0) (U:Finset K) (hU:U⊆T)
      (hv : ∀ γ∈U,eval (z γ) q=0) :
      3*U.card≤3*(B*q.totalDegree)+q.totalDegree*(q.totalDegree-1) := by
    revert hq U hU hv
    induction q using oq with
    | zero=>intro hn; exact (hn rfl).elim
    | unit q hu =>
      intro _ U _ hv
      have he :U = ∅ := eq_empty_iff_forall_notMem.mpr
        fun γ hγ=>(hu.map (eval (z γ))).ne_zero (hv γ hγ)
      simp [he]
    | mul a q ha hq ih =>
      intro _ U hU hv
      let V:=U.filter fun γ=>eval (z γ) q=0
      let W:=U \ V
      have hV:V⊆U:=filter_subset _ _
      have hW:W⊆U:=sdiff_subset
      have hvV (γ:K) (hγ:γ∈V) :eval (z γ) q=0:=(mem_filter.mp hγ).2
      have hvW (γ:K) (hγ:γ∈W) :eval (z γ) a=0:= by
        have h:=hv γ (hW hγ)
        rw [map_mul] at h
        exact (mul_eq_zero.mp h).resolve_left
          (fun hz' => (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨hW hγ,hz'⟩))
      have hbad:=bad_count h₁ h₃ (hz.mono (hV.trans hU)) hq hvV
      have hgood: (c9 q z V).card≤B*q.totalDegree :=
        (card_le_card (filter_subset_filter _ (hV.trans hU))).trans (hImm q hq)
      have hpart:=card_filter_add_card_filter_not (s :=V) (fun γ=>cy q (z γ))
      change (c9 q z V).card+_=V.card at hpart
      have hcap:3*V.card≤3*(B*q.totalDegree)+q.totalDegree*(q.totalDegree-1) := by
        rw [← hpart,lV]
        exact mD (lz _ hgood) hbad
      rw [← card_sdiff_add_card_eq_card hV,totalDegree_mul_of_isDomain hq.ne_zero ha]
      change 3*(W.card+V.card)≤_
      have hsum:=mD (ih ha W (hW.trans hU) hvW) hcap
      rw [lV]
      have hs :=reserve_add q.totalDegree a.totalDegree
      rw [lV,lV]
      omega
  have htot:=count q hq T (Subset.refl _) hvan
  have hqB:q.totalDegree≤2*B:=hdeg.trans (by omega)
  calc
    _≤_:=htot
    _≤3*(B*(2*B))+(2*B)*(2*B) :=
      mD (lz _ (lz _ hqB))
        (Nat.mul_le_mul hqB ((Nat.sub_le _ _).trans hqB))
    _ = _:= by ring
end
end q7YMR4d

import ProximityPrize.SubmissionLower.ZucFfdd
import ProximityPrize.SubmissionLower.ZXxMpWa
set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
namespace q6t08kb
noncomputable section
open P6_6 P6_6_7 MvPolynomial
open aR (af ao shape qE cK extend jet ceilDiv)
open oR (qg)
open aeA (view gLc gLd cvh)
open BO (bfW)
open agL (BV a4A EY)
open scoped BigOperators Polynomial
open private Ka aYc from ProximityPrize.SubmissionLower.AH
open private orderAt_ord from ProximityPrize.SubmissionLower.ZfVU1Oc
private theorem cSn (R:af 4) (i:Fin 4) :
    BV (Finsupp.single i 1) R=pderiv i R:= by
  classical
  conv_rhs=>rw [R.as_sum]
  simp only [BV,map_sum,pderiv_monomial]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Finsupp.single_eq_of_ne hji]
  · simp
private theorem regular_linear (f :af 2) (hf :Irreducible f) (hd:f.degreeOf 1=1)
    (S:ao[X]) (hz :cK f S=0) :qg 1 f S:= by
  refine ⟨hz,?_⟩
  intro hsep
  let A:=view f
  have hA:A.natDegree=1 :=(gLc f).trans hd
  have hexp:=Polynomial.eq_X_add_C_of_natDegree_le_one hA.le
  have hdA:A.derivative=Polynomial.C (A.coeff 1) := by
    conv_lhs=>rw [hexp]
    simp
  have hsep' : cK (A.coeff 1) S=0:= by
    change cK (pderiv (Fin.last 1) f) S=0 at hsep
    rw [cvh,gLd,hdA,Polynomial.map_C,Polynomial.eval_C] at hsep
    exact hsep
  have hz' : cK (A.coeff 0) S=0:= by
    rw [cvh] at hz
    change (A.map (eval (jet S))).eval (jet S (1 :Fin 2))=0 at hz
    conv_lhs at hz=>rw [hexp]
    change eval (jet S) (A.coeff 1)=0 at hsep'
    simpa [cK,hsep'] using hz
  let L:=Ka.symm (Polynomial.X-Polynomial.C S)
  have hdvd (j:ℕ) (h:cK (A.coeff j) S=0) :L∣A.coeff j:= by
    have hroot : (Ka (A.coeff j)).eval S=0:=(aYc _ _).trans h
    simpa only [L,AlgEquiv.symm_apply_apply] using
      map_dvd Ka.symm (Polynomial.dvd_iff_isRoot.mpr hroot)
  have hD:Polynomial.C L∣A:=(Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun j=> by
    by_cases h:j=0
    · subst j
      exact hdvd 0 hz'
    by_cases h' : j=1
    · subst j
      exact hdvd 1 hsep'
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega :A.natDegree<j)]
    exact dvd_zero _
  have hprim:A.IsPrimitive :=(hf.map view).isPrimitive (hA.trans_ne (by decide))
  have hu:IsUnit L:=hprim _ hD
  exact Polynomial.not_isUnit_X_sub_C S (by simpa only [L,AlgEquiv.apply_symm_apply] using hu.map Ka)
private theorem index_one_row {R:af 4} (hR:Irreducible R) (hj: (shape R).j=1) :
    ∃ (f :af 2) (e :Fin 2→Fin 4),Function.Injective e∧e 1=1 ∧
      (∀ S (i:Fin 2),jet S (e i)=jet S i)∧rename e f=R ∧
      Irreducible f∧f.totalDegree=(shape R).b∧f.degreeOf 1=1 := by
  classical
  let e :Fin 2→Fin 4 :=Fin.castLE (by decide)
  have he :Function.Injective e :=Fin.castLE_injective _
  have hv : (R.vars :Set (Fin 4))⊆Set.range e := by
    intro i hi
    obtain ⟨m,hm,hi⟩:=(mem_vars_iff_mem_support i).mp hi
    have hidx :m.sum (fun j a=>j.val*a)≤(shape R).j :=
      Finset.le_sup (f := fun m=>m.sum (fun j a=>j.val*a)) hm
    have hmul :=Finset.single_le_sum (f := fun j:Fin 4=>j.val*m j) (fun _ _=>Nat.zero_le _) hi
    have hmpos :=Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    have hi' : i.val<2 := by
      have h:=(Nat.le_mul_of_pos_right _ hmpos).trans (hmul.trans hidx)
      omega
    exact ⟨⟨i.val,hi'⟩,Fin.ext rfl⟩
  obtain ⟨f,hr⟩:=exists_rename_eq_of_vars_subset_range R e he hv
  let back :af 4 →ₐ[ao[X]] af 2 :=rename (fun i:Fin 4=>Fin.ofNat 2 i.val)
  have hback (g:af 2) :back (rename e g)=g:= by
    change rename _ (rename e g)=g
    rw [rename_rename]
    have h: (fun i:Fin 4=>Fin.ofNat 2 i.val) ∘ e=id := by
      funext i
      fin_cases i <;> rfl
    rw [h,rename_id_apply]
  have hf :Irreducible f := by
    refine ⟨fun h=>hR.not_isUnit (hr ▸ h.map (rename e)),?_⟩
    intro g q h
    have h' : R=rename e g*rename e q:= by rw [← hr,h,map_mul]
    rcases hR.isUnit_or_isUnit h' with hu | hu
    · exact Or.inl (hback g ▸ hu.map back)
    · exact Or.inr (hback q ▸ hu.map back)
  refine ⟨f,e,he,rfl,fun _ _=>rfl,hr,hf,?_,?_⟩
  · change f.totalDegree=R.totalDegree
    rw [← hr,← weightedTotalDegree_one,← weightedTotalDegree_one,
      weightedTotalDegree_rename_of_injective he]
    rfl
  · have h:=hj
    change qE R=1 at h
    rw [← hr,Ex.C6,weightedTotalDegree_rename_of_injective he] at h
    have hw: (Fin.val :Fin 4→ℕ) ∘ e=Pi.single 1 1 := by
      funext i
      fin_cases i <;> decide
    rwa [hw,weightedTotalDegree_piSingle] at h
private theorem ebF {n x b:ℕ} (h:46402*n≤82317*x+46402) (hb:1≤b^2) :
    n≤ ceilDiv (82317*x) 46402+b^2 := by
  unfold ceilDiv
  omega
private theorem first_marks (C:Context) (R:af 4) (hf :Irreducible R) (hj: (shape R).j=1) :
    ∃ f :af 2,Irreducible f∧f.totalDegree=(shape R).b∧f.degreeOf 1=1 ∧
      (∀ γ∈roots C R,qg 1 f (extend (C.s γ))) ∧
      markedWeight C.Δ C.s R=(roots C R).card:= by
  classical
  obtain ⟨f,e,he,he1,heval,hr,hfi,hb,hd⟩:=index_one_row hf hj
  have he' (g:af 2) (S:ao[X]) :cK (rename e g) S=cK g S:= by
    rw [cK,eval_rename,cK]
    exact congrArg (fun x=>eval x g) (funext (heval S))
  have hreg (γ:P6.K) (hγ:γ∈roots C R) :qg 1 f (extend (C.s γ)) := by
    apply regular_linear f hfi hd
    rw [← he' f,hr]
    exact bfW (Finset.mem_filter.mp hγ).2 (orderAt_ord C R γ)
  have hweight:markedWeight C.Δ C.s R=(roots C R).card:= by
    unfold markedWeight roots
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro γ hΓ
    change ord C R γ=if 0<ord C R γ then 1 else 0
    by_cases ho:0<ord C R γ
    · rw [ite_eq_left ho]
      apply le_antisymm _ ho
      by_contra! hbig
      have hi:EY (Finsupp.single (1 :Fin 4) 1)=1 := by simp [EY]
      have hp:EY (Finsupp.single (1 :Fin 4) 1)<ord C R γ:= by
        rw [hi]
        exact hbig
      have hz :=a4A
        hp
        (orderAt_ord C R γ)
      rw [cSn,← hr,← he1,pderiv_rename he,he'] at hz
      exact (hreg γ (Finset.mem_filter.mpr ⟨hΓ,ho⟩)).2 hz
    · rw [ite_eq_right ho]
      exact Nat.eq_zero_of_not_pos ho
  exact ⟨f,hfi,hb,hd,hreg,hweight⟩
private theorem first_regular_count {w Γ s} (hmsg :Messages w Γ s)
    (f :af 2) (hfi:Irreducible f) (hd:f.degreeOf 1=1) {b:ℕ}
    (hB:f.totalDegree≤b) (hreg : ∀ γ∈Γ,qg 1 f (extend (s γ))) :
    46402*Γ.card≤82317*firstMixed b 1+46402 := by
  let d:=gZ
  obtain ⟨T⟩:=czH.proof f d b 1 (by decide) (by decide) (by decide) hB hd.le
  let a :=aF0.BJ d b
  let v :=aF0.YM d b 1
  have ha :0<a := by simp [a,aF0.BJ]
  have hv :0<v :=lt_min ha (by decide :0<d)
  change 46402*Γ.card≤82317*(b*v+1*(a - v))+46402
  apply P6_6_5.bv5 hmsg
  intro i hi
  apply (cz7.a8m hmsg.distinct f hfi (by rw [hd]; decide) hreg ha hv i hi
    (T.cut (P6.node i) (w i)) (ana.aVQ _ (T.ags _ _) (T.top_bound _ _))
    (fun γ hγ=>T.agrees _ (hmsg.degree γ hγ) (hreg γ hγ) _ _)).trans
  unfold cappedDegreeMixedVolume
  rw [hd]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hB) _
theorem first_order (C:Context) (R:af 4) (hf :Irreducible R) (hj: (shape R).j=1) :
    markedWeight C.Δ C.s R≤eyA (lowerBody (shape R)).b 1 := by
  obtain ⟨f,hfi,hb,hd,hreg,hweight⟩:=first_marks C R hf hj
  let b:=(lowerBody (shape R)).b
  have hB:f.totalDegree≤b:=hb.le.trans (le_max_left _ _)
  have hmsg :=C.messages.mono (Δ:=roots C R) (Finset.filter_subset _ _)
  have hc:=first_regular_count hmsg f hfi hd hB hreg
  have hpos :0<b:=(Nat.succ_pos _).trans_le (le_max_right (shape R).b ((shape R).j+3))
  have hone :1≤b^2 :=Nat.one_le_pow _ _ hpos
  rw [hweight]
  simpa only [firstMixed_eq,eyA,ite_eq_right (by decide : (1 :ℕ)≠0),
    d1C,ee8,b] using ebF hc hone
end
end q6t08kb

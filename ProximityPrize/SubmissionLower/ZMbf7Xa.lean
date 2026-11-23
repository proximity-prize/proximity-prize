import ProximityPrize.SubmissionLower.ZLCmwJc
import ProximityPrize.SubmissionLower.ZwDGfQd
import ProximityPrize.SubmissionLower.ZuY7OPe
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
namespace qxwYnxa
noncomputable section
open Polynomial
open qaJ7jxd (sylvesterNumer sylvesterNumer_eval₂)
open private specialized_coprime from ProximityPrize.SubmissionLower.ZLCmwJc
open private resultant_product from ProximityPrize.SubmissionLower.ZwDGfQd
open scoped BigOperators Classical
variable {R F E :Type} [CommRing R] [Field F] [IsAlgClosed F] [Infinite F]
 [Field E] [IsAlgClosed E] [Infinite E]
omit [IsAlgClosed F] in
theorem sample (n:ℕ) : ∃ p:F[X],p.Monic∧p.natDegree=n∧p.Separable := by
 let a (i:Fin n) :=Infinite.natEmbedding F i.val
 refine ⟨∏ i,(Polynomial.X - C (a i)),monic_prod_X_sub_C _ _,?_,?_⟩
 · simp [natDegree_finsetProd_X_sub_C_eq_card]
 · exact separable_prod_X_sub_C_iff.mpr
     ((Infinite.natEmbedding F).injective.comp Fin.val_injective)
omit [IsAlgClosed F] [Infinite F] [IsAlgClosed E] [Infinite E] in
theorem good_roots (i:R →+* E) (hi:Function.Injective i) (v :R →+* F)
   (p h:R[X]) {n:ℕ} (hn:0<n) (hp:p.natDegree≤n)
   (hv : (p.map v).natDegree=n) (hs : (p.map v).Separable) (hh:h.map v=1) :
   (p.map i).natDegree=n∧(p.map i).Separable ∧
     ∀ x∈(p.map i).roots,(p.map i).derivative.eval x≠0∧(h.map i).eval x≠0:= by
 have hc:IsCoprime (p.map v) ((p.derivative*h).map v) := by
   simpa only [Polynomial.map_mul,← derivative_map,hh,mul_one,Separable] using hs
 obtain ⟨hd,hc⟩:=specialized_coprime i hi v p (p.derivative*h) n hn hp hv hc
 rw [Polynomial.map_mul,← derivative_map] at hc
 refine ⟨hd,(IsCoprime.mul_right_iff.mp hc).1,?_⟩
 intro x hx
 have hp₀:p.map i≠0:=ne_zero_of_natDegree_gt (hd.symm ▸ hn)
 have hroot :=(mem_roots hp₀).mp hx
 have he :=(aeval_ne_zero_of_isCoprime hc x).resolve_left (by simpa using hroot)
 simpa only [coe_aeval_eq_eval,eval_mul,mul_ne_zero_iff] using he
private theorem sample_numerator (v :R →+* F) (p r q:R[X]) {n:ℕ}
   (hn:0<n) (hv : (p.map v).natDegree=n) (hm: (p.map v).Monic)
   (hr :r.map v=1) (hq:q.map v=Polynomial.X) :
   (sylvesterNumer p r q n).map v=p.map v := by
 apply Polynomial.funext
 intro x
 rw [eval_map,sylvesterNumer_eval₂,hr,hq,mul_one]
 have hdeg: (C x-Polynomial.X).natDegree≤n :=
   (natDegree_sub_le_of_le (by simp : (C x).natDegree≤1) natDegree_X.le).trans
     (Nat.succ_le_of_lt hn)
 have hs : (p.map v).Splits :=IsAlgClosed.splits _
 have hprod:=resultant_eq_prod_eval (p.map v) (C x-Polynomial.X) n hdeg hs
 rw [hv] at hprod
 rw [hprod,hm.leadingCoeff,one_pow,one_mul,hs.eval_eq_prod_roots_of_monic hm]
 congr 1
 apply Multiset.map_congr rfl
 intro y _
 simp
theorem bwk (i:R →+* E) (hi:Function.Injective i) (v :R →+* F)
   (p r q:R[X]) {n:ℕ} (hn:0<n) (hp: (p.map i).natDegree=n)
   (hr :r.natDegree≤n) (hq:q.natDegree≤n)
   (hv : (p.map v).natDegree=n) (hm: (p.map v).Monic) (hs : (p.map v).Separable)
   (hvr :r.map v=1) (hvq:q.map v=Polynomial.X) :
   ∀ x∈(p.map i).roots,∀ y∈(p.map i).roots,
     (q.map i).eval x/(r.map i).eval x=(q.map i).eval y/(r.map i).eval y→x=y := by
 have hden:i (p.resultant r n n)≠0:=(map_ne_zero_iff i hi).mpr fun hz=> by
   have he :=congrArg v hz
   rw [map_zero,← resultant_map_map,hvr,resultant_one_right,← hv,coeff_natDegree,
     hm.leadingCoeff,one_pow] at he
   exact one_ne_zero he
 let Q:=sylvesterNumer p r q n
 have hQv :Q.map v=p.map v :=sample_numerator v p r q hn hv hm hvr hvq
 have hp' : p.natDegree=n:=(natDegree_map_eq_of_injective hi p).symm.trans hp
 have hfac:=resultant_product i hi p r q n hp' hr hq hden
 change Q.map i= _ at hfac
 let values :=(p.map i).roots.map fun x=>(q.map i).eval x/(r.map i).eval x
 have hfac' : Q.map i=C (i (p.resultant r n n)) *
     (values.map fun a=>Polynomial.X - C a).prod:= by
   rw [hfac,Multiset.map_map]
   rfl
 have hQdeg:Q.natDegree=n:= by
   rw [← natDegree_map_eq_of_injective hi Q,hfac',natDegree_C_mul hden,
     natDegree_multiset_prod_X_sub_C_eq_card,Multiset.card_map,
     IsAlgClosed.card_roots_eq_natDegree,hp]
 have hcop:IsCoprime (Q.map v) (Q.derivative.map v) := by
   rw [← derivative_map,hQv]
   exact hs
 obtain ⟨_,hc⟩:=specialized_coprime i hi v Q Q.derivative n hn hQdeg.le
   ((congrArg Polynomial.natDegree hQv).trans hv) hcop
 rw [← derivative_map,← Separable,hfac'] at hc
 exact Multiset.inj_on_of_nodup_map (nodup_of_separable_prod hc.of_mul_right)
end
end qxwYnxa
end
section
set_option backward.isDefEq.respectTransparency false
namespace qxwYnxa
noncomputable section
open Polynomial
open cu (L)
open q2tSkEc (bzm caps orders)
open qEAs6me (topSlot topPoly topPoly_map topPoly_degree coeff_topPoly)
open qVAMdHe (first tu kB Ext emb ek jet delta)
open scoped BigOperators Classical
variable {s b d:ℕ}
private def lP (d:ℕ) (t:Fin 3) :Fin (orders d t+1) :=
 ⟨orders d t-1,by omega⟩
private theorem jet_diff {t:Fin 3} (h:1≤orders d t) :
  orders d t - (lP d t).val=1 := by
 change orders d t - (orders d t-1)=1
 omega
private abbrev width (s b d:ℕ) (t:Fin 3) :=
 caps b s t+(orders d t - (lP d t).val)*s+1
private def jetPoly {M:Type} [CommSemiring M] (a :bzm s b d→M) (t:Fin 3) :M[X] :=
 ofFn (width s b d t) (fun j=>a ⟨t,lP d t,j⟩)
private theorem jetPoly_eval {M:Type} [CommSemiring M] (a :bzm s b d→M)
   (t:Fin 3) (ht:1≤orders d t) (x :M) :
   (jetPoly a t).eval x=jet a t x := by
 rw [jet,Fintype.sum_sigma,Finset.sum_eq_single (lP d t)]
 · simp only [jet_diff ht,ite_true,jetPoly,ofFn_eq_sum_monomial,eval_finsetSum,eval_monomial]
 · intro i _ hi
   have he :orders d t - i.val≠1 := by
     intro h
     apply hi
     apply Fin.ext
     have :=i.isLt
     change i.val=orders d t-1
     omega
   simp [he]
 · simp
private theorem jetPoly_map {M N :Type} [CommSemiring M] [CommSemiring N]
  (e :M →+* N) (a :bzm s b d→M) (t:Fin 3) :
  (jetPoly a t).map e=jetPoly (e ∘ a) t:= by
 simp only [jetPoly,ofFn_eq_sum_monomial,Polynomial.map_sum,map_monomial,Function.comp_apply]
private theorem jetPoly_degree {M:Type} [CommSemiring M]
  (a :bzm s b d→M) (t:Fin 3) (ht:1≤orders d t) :
  (jetPoly a t).natDegree≤ caps b s t+s := by
 have hh:=ofFn_natDegree_lt (R:=M) (n:=width s b d t) (Nat.zero_lt_succ _)
  (fun j=>a ⟨t,lP d t,j⟩)
 change (jetPoly a t).natDegree<width s b d t at hh
 simp only [width,jet_diff ht,one_mul] at hh
 omega
private theorem jet_fill {M:Type} [CommSemiring M]
  (a :bzm s b d→M) (t:Fin 3) (p:M[X]) (hp:p.natDegree<width s b d t)
  (h : ∀ j:Fin (width s b d t),a ⟨t,lP d t,j⟩=p.coeff j) :
  jetPoly a t=p:= by
 rw [jetPoly,show (fun j:Fin (width s b d t)=>a ⟨t,lP d t,j⟩) =
  toFn _ p from funext h]
 exact ofFn_comp_toFn_eq_id_of_natDegree_lt hp
private theorem top_fill (a :bzm s b d→L) (t:Fin 3) (p:L[X])
   (hp:p.natDegree≤ caps b s t)
   (h : ∀ j,a ⟨t,topSlot s b d t j⟩=p.coeff j) :topPoly a t=p:= by
 ext j
 rw [coeff_topPoly]
 split_ifs with hj
 · exact h ⟨j,hj⟩
 · exact (coeff_eq_zero_of_natDegree_lt (by omega :p.natDegree<j)).symm
private def vars (s b d:ℕ) (r :bzm s b d) :tu s b d :=
 if h:r≠first s b d then MvPolynomial.X ⟨r,h⟩ else 0
private def specialize (a :bzm s b d→L) :tu s b d →+* L :=
 MvPolynomial.eval₂Hom (RingHom.id L) (a ∘ Subtype.val)
private theorem vars_spec (a :bzm s b d→L) (ha :a (first s b d)=0) :
   specialize a ∘ vars s b d=a := by
 funext r
 by_cases hr :r=first s b d
 · subst r
   simp [vars,ha]
 · simp [vars,specialize,hr,Function.comp_def]
private theorem vars_generic :
  emb s b d ∘ vars s b d=ek s b d:= by
 funext r
 by_cases hr :r=first s b d <;> simp [vars,ek,hr]
private def sampleArg (p u j k :L[X]) (r :bzm s b d) :L :=
 if r.1=0 then
  (if orders d 0 - r.2.1.val=1 then j else u).coeff r.2.2.val
 else if r.1=1 then p.coeff r.2.2.val else k.coeff r.2.2.val
private theorem sample_top₀ (p u j k :L[X]) (hu:u.natDegree≤b) :
  topPoly (sampleArg (s :=s) (b:=b) (d:=d) p u j k) 0=u:= by
 apply top_fill _ _ _ hu
 intro i
 simp [sampleArg,topSlot]
private theorem sample_top₁ (p u j k :L[X]) (hp:p.natDegree≤b+s+1) :
  topPoly (sampleArg (s :=s) (b:=b) (d:=d) p u j k) 1=p:= by
 apply top_fill _ _ _ hp
 intro i
 simp [sampleArg,topSlot,show (1 :Fin 3)≠0 by decide]
private theorem sample_jets (p u j k :L[X]) (hd:2≤d)
   (hj:j.natDegree≤b+s) (hk :k.natDegree≤b+s) :
   let a :=sampleArg (s :=s) (b:=b) (d:=d) p u j k
   jetPoly a 0=j∧jetPoly a 2=k := by
 have h0:1≤orders d 0:= by change 1≤d; omega
 have h2 :1≤orders d 2 := by change 1≤d-1; omega
 dsimp only
 constructor
 · apply jet_fill
   · change j.natDegree<b+(orders d 0-(lP d 0).val)*s+1
     simpa only [jet_diff h0,one_mul,Nat.lt_succ_iff] using hj
   · intro i
     have h:d-(lP d 0).val=1 :=jet_diff h0
     simp [sampleArg,h]
 · apply jet_fill
   · change k.natDegree<b+(orders d 2 - (lP d 2).val)*s+1
     simpa only [jet_diff h2,one_mul,Nat.lt_succ_iff] using hk
   · intro i
     simp [sampleArg,show (2 :Fin 3)≠0 by decide,show (2 :Fin 3)≠1 by decide]
theorem proof :qVAMdHe.c1 := by
  intro s b d hd
  let n:=b+s+1
  have hn:0<n:=Nat.zero_lt_succ _
  obtain ⟨p,hmonic,hp,hsep⟩:=sample (F:=L) n
  let u:L[X] :=if 0<b then Polynomial.X else 0
  let j:L[X] :=if b=0∧0<s then Polynomial.X else 0
  let k :L[X] :=1+C (d:L)*j
  have hu:u.natDegree≤b:= by
    by_cases hb:0<b <;> simp [u,hb,Nat.succ_le_of_lt]
  have hj:j.natDegree≤b+s := by
    by_cases h:b=0∧0<s
    · simpa [j,h] using (show 1≤b+s by omega)
    · simp [j,h]
  have hk :k.natDegree≤b+s := by
    apply (natDegree_add_le _ _).trans
    exact max_le (by simp) ((natDegree_C_mul_le _ _).trans hj)
  let a₀:bzm s b d→L:=sampleArg p u j k
  let v :=specialize a₀
  have ha₀:a₀ (first s b d)=0:= by
    simp only [a₀,sampleArg,first,topSlot,Nat.sub_self,ite_eq_right Nat.zero_ne_one]
    by_cases hb:0<b <;> simp [u,hb]
  have hv :=vars_spec a₀ ha₀
  let i:=emb s b d
  have hi:Function.Injective i :=
    (RingHom.injective (algebraMap (kB s b d) (Ext s b d))).comp
      (IsFractionRing.injective (tu s b d) (kB s b d))
  let A:=vars s b d
  let P:=topPoly A 1
  let U:=topPoly A 0
  let J:=jetPoly A 0
  let D:=jetPoly A 2 - C (d:tu s b d)*J
  have h0:1≤orders d 0:= by change 1≤d; omega
  have h2 :1≤orders d 2 := by change 1≤d-1; omega
  have hPv :P.map v=p:= by
    rw [topPoly_map,hv]
    exact sample_top₁ p u j k hp.le
  have hUv :U.map v=u:= by
    rw [topPoly_map,hv]
    exact sample_top₀ p u j k hu
  obtain ⟨hj₀,hk₀⟩:=sample_jets (s :=s) (b:=b) p u j k hd hj hk
  have hJv :J.map v=j:= by rw [jetPoly_map,hv,hj₀]
  have hDv :D.map v=1 := by
    simp only [D,Polynomial.map_sub,Polynomial.map_mul,hJv]
    rw [jetPoly_map,hv,hk₀]
    simp [k]
  have hPi:P.map i=topPoly (ek s b d) 1 := by rw [topPoly_map,vars_generic]
  have hUi:U.map i=topPoly (ek s b d) 0:= by rw [topPoly_map,vars_generic]
  have hJi (x :Ext s b d) : (J.map i).eval x=jet (ek s b d) 0 x := by
    rw [jetPoly_map,vars_generic,jetPoly_eval _ _ h0]
  have hDi (x :Ext s b d) : (D.map i).eval x=delta (ek s b d) x := by
    simp only [D,Polynomial.map_sub,Polynomial.map_mul,eval_sub,eval_mul,hJi,delta]
    rw [jetPoly_map,vars_generic,jetPoly_eval _ _ h2,Polynomial.map_C,eval_C,map_natCast]
  have hPdeg:P.natDegree≤n:=topPoly_degree A 1
  have hUdeg:U.natDegree≤n:=(topPoly_degree A 0).trans (by change b≤n; omega)
  have hJdeg:J.natDegree≤b+s :=jetPoly_degree A 0 h0
  have hDdeg:D.natDegree≤b+s := by
    apply (natDegree_sub_le _ _).trans
    exact max_le (jetPoly_degree A 2 h2) ((natDegree_C_mul_le _ _).trans hJdeg)
  have hdv : (P.map v).natDegree=n:=hPv ▸ hp
  have hmv : (P.map v).Monic:=hPv ▸ hmonic
  have hsv : (P.map v).Separable :=hPv ▸ hsep
  obtain ⟨hdeg,hsepi,hgood⟩:=good_roots i hi v P D hn hPdeg hdv hsv hDv
  let S:=(P.map i).roots.toFinset
  have hcard:S.card=n:= by
    change (P.map i).roots.toFinset.card=n
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hsepi),IsAlgClosed.card_roots_eq_natDegree,hdeg]
  let e :Fin n ≃ S:=(Fintype.equivFinOfCardEq ((Fintype.card_coe S).trans hcard)).symm
  let a :Fin n→Ext s b d:=Subtype.val ∘ e
  have ha :Function.Injective a :=Subtype.val_injective.comp e.injective
  have hr (x :Fin n) :a x∈(P.map i).roots :=Multiset.mem_toFinset.mp (e x).property
  have hPne :P.map i≠0:=ne_zero_of_natDegree_gt (hdeg.symm ▸ hn)
  refine ⟨a,ha,hPi ▸ hdeg,?_,?_,?_⟩
  · intro x
    have hroot :=(mem_roots hPne).mp (hr x)
    have h:=hgood (a x) (hr x)
    exact ⟨hPi ▸ hroot,hPi ▸ h.1,hDi (a x) ▸ h.2⟩
  · intro hb x y hxy
    have hU:U.map v=Polynomial.X:= by simp [hUv,u,hb]
    have he :=bwk i hi v P 1 U hn hdeg (by simp) hUdeg hdv hmv hsv
      (Polynomial.map_one v) hU
    apply ha (he _ (hr x) _ (hr y) ?_)
    simpa only [Polynomial.map_one,eval_one,div_one,hUi] using hxy
  · intro hb
    by_cases hs :s=0
    · intro x y _
      apply Fin.ext
      have hx :x.val<b+s+1 :=x.isLt
      have hy :y.val<b+s+1 :=y.isLt
      omega
    · have hJ:J.map v=Polynomial.X:= by simp [hJv,j,hb,Nat.pos_of_ne_zero hs]
      have he :=bwk i hi v P D J hn hdeg (hDdeg.trans (Nat.le_succ _))
        (hJdeg.trans (Nat.le_succ _)) hdv hmv hsv hDv hJ
      intro x y hxy
      apply ha (he _ (hr x) _ (hr y) ?_)
      simpa only [hJi,hDi] using hxy
end
end qxwYnxa
end

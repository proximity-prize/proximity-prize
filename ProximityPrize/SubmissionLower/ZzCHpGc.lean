import ProximityPrize.SubmissionLower.ZK7Ye0a
import ProximityPrize.SubmissionLower.ZTbuynb
set_option Elab.async false
open _root_ renaming FaithfulSMul.algebraMap_injective→nI,Lagrange.nodal→cy,Lagrange.nodal_ne_zero→nq,MulZeroClass.mul_zero→lz,Nat.add_le_add_left→mD,P5_7.farAgreement→lI,P5_7_7.sites→aU,congrArg→c9,mul_ne_zero→lV,q20JTGa.nodal_eq_locator→lJ
set_option autoImplicit true
set_option maxHeartbeats 500000
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace q20JTGa
noncomputable section
open Polynomial Finset P5_7_7
open P5 (I K node blockLength)
open P5_7 (farAgreement)
open cu (L j9)
open scoped Classical
private def output {w:I→K} (r :WordRow w) (f :K[X]) :L[X] :=
 r.a*j9 f+r.b
private theorem row_eval {ι F:Type*} [Field F] {x y :ι→F}
  (r :InterpolationRow x y) (f :F[X]) (i:ι) :
  (r.a*f+r.b).eval (x i)=r.a.eval (x i)*(f.eval (x i)-y i) := by
 rw [eval_add,eval_mul,mul_sub,eq_sub_iff_add_eq]
 rw [add_assoc,add_comm (r.b.eval _),r.Ju,add_zero]
private theorem lift_eval (f :K[X]) (i:I) :
  (j9 f).eval (base i)=algebraMap K L (f.eval (node i)) :=
 eval_map_apply _ _
private theorem output_degree {D d:ℕ} {w:I→K} (r :WordRow w)
   (hr :ic D r.a r.b d) {f :K[X]} (hf :f.natDegree≤D) :
   (output r f).natDegree≤d:= by
 rcases hr with ⟨ha,hb⟩
 unfold output
 rcases ha with ha | ha
 · simpa only [ha,zero_mul,zero_add] using hb
 · exact (natDegree_add_le _ _).trans
     (max_le (natDegree_mul_le.trans ((mD (natDegree_map_le.trans hf) _).trans ha)) hb)
private theorem output_dvd {w:I→K} (r :WordRow w) (S:K→K[X]) (γ:K) :
  mL (aU w S γ)∣output r (S γ) :=
 ex4 fun i hi=> by
  have he : (S γ).eval (node i)=w i:=mem_sites.mp hi
  rw [output,row_eval,lift_eval,he,sub_self,lz]
private theorem quotient_degree {A:Finset I} {q N :L[X]} {d:ℕ}
   (hq:mL A*q=N) (hd:N.natDegree≤d) :q.natDegree≤d-A.card:= by
 by_cases h:q=0
 · simp only [h,natDegree_zero,Nat.zero_le]
 have hh:=natDegree_mul (locator_ne A) h
 rw [hq,locator_degree] at hh
 omega
private theorem hit_width {A:Finset I} {q N :L[X]} {d:ℕ}
  (hq:mL A*q=N) (hd:N.natDegree≤d) (hn:N≠0) :A.card≤d:= by
 have he :q≠0:= fun hz=>hn (by rw [← hq,hz,lz])
 have hh:=natDegree_mul (locator_ne A) he
 rw [hq,locator_degree] at hh
 omega
private theorem reduced {ι F:Type*} [Fintype ι] [Field F] [IsAlgClosed F]
   {x y :ι→F} (hx :Function.Injective x) (r s :InterpolationRow x y)
   (htarget : ∀ i,r.a.eval (x i)≠0∨s.a.eval (x i)≠0)
   (hdet : ∃ c:F,c≠0∧det r s=C c*cy univ x)
   (f :F[X]) (A:Finset ι) (hA : ∀ i,i∈A↔f.eval (x i)=y i)
   {P Q:F[X]} (hP:cy A x*P=s.a*f+s.b)
   (hQ:cy A x*Q=r.a*f+r.b) :
   IsCoprime P Q ∧ ∀ i,P.eval (x i)*r.a.eval (x i)= Q.eval (x i)*s.a.eval (x i)↔i∉A:= by
 let B:=univ \ A
 obtain ⟨c,hc,hd⟩:=hdet
 have hprod:cy A x*cy B x=cy univ x :=
   prod_mul_prod_compl _ _
 have hclear :r.a*P-s.a*Q=C c*cy B x := by
   apply mul_left_cancel₀ (nq (s :=A) (v :=x))
   calc
     _=r.a*(cy A x*P)-s.a*(cy A x*Q) := by ring
     _=det r s := by rw [hP,hQ]; unfold det; ring
     _ = _:= by rw [hd,← hprod]; ring
 have atMiss (i:ι) (hi:i∈B) : ¬ (P.eval (x i)=0∧Q.eval (x i)=0) := by
   rintro ⟨hp,hq⟩
   have hh:f.eval (x i)-y i≠0:=sub_ne_zero.mpr fun he=>(mem_sdiff.mp hi).2 ((hA i).mpr he)
   have hp' := c9 (eval (x i)) hP
   have hq' := c9 (eval (x i)) hQ
   simp only [eval_mul,row_eval s,hp,lz] at hp'
   simp only [eval_mul,row_eval r,hq,lz] at hq'
   exact (htarget i).elim
     (fun h=>lV h hh hq'.symm) (fun h=>lV h hh hp'.symm)
 constructor
 · apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed F F P Q).mpr
   intro t
   simp only [coe_aeval_eq_eval]
   by_contra hn
   obtain ⟨hp,hq⟩:=not_or.mp hn
   have hp' := not_not.mp hp
   have hq' := not_not.mp hq
   have he :=c9 (eval t) hclear
   simp only [eval_mul,eval_sub,eval_C,hp',hq',lz ,sub_self] at he
   have hB:=(mul_eq_zero.mp he.symm).resolve_left hc
   rw [Lagrange.eval_nodal,Finset.prod_eq_zero_iff] at hB
   obtain ⟨i,hi,hz⟩:=hB
   have ht:=sub_eq_zero.mp hz
   subst t
   exact atMiss i hi ⟨hp',hq'⟩
 · intro i
   have he :=c9 (eval (x i)) hclear
   simp only [eval_mul,eval_sub,eval_C] at he
   rw [← sub_eq_zero,mul_comm (P.eval _),mul_comm (Q.eval _),he,mul_eq_zero,or_iff_right hc]
   have hB:i∈B↔i∉A:= by simp only [B,mem_sdiff,mem_univ,true_and]
   rw [← hB]
   refine ⟨fun hz=>not_not.mp fun hn => ?_,Lagrange.eval_nodal_at_node⟩
   apply (Lagrange.eval_nodal_not_at_node (s :=B) (v :=x) (x :=x i) ?_) hz
   intro j hj he
   have hj' : j=i:=(hx he).symm
   exact hn (hj' ▸ hj)
private theorem det_ne {ι F:Type*} [Fintype ι] [Field F] {x y :ι→F}
  {D:ℕ} (J:InterpolationRows D x y) :det J.r J.s≠0:= by
 obtain ⟨c,hc,hd⟩:=J.determinant
 rw [hd]
 exact lV (C_ne_zero.mpr hc) nq
private theorem gMz {A d₀ d₁ n:ℕ} (h₀:A≤d₀) (h₁:A≤d₁) (h:d₀+d₁=n) :
 2*A+((d₀-A)+(d₁-A))=n:= by omega
private theorem shifted_width {A d:ℕ} (h:A≤d) :A+(d-A)=d :=
 (Nat.add_comm _ _).trans (Nat.sub_add_cancel h)
private theorem rwG {D:ℕ} {w:I→K} (J:WordRows D w) {g:K[X]} {A:Finset I} {P Q:L[X]}
    (hA : ∀ i,i∈A↔(j9 g).eval (base i)=algebraMap K L (w i))
    (hP:mL A*P=output J.s g) (hQ:mL A*Q=output J.r g) :
    IsCoprime P Q ∧ ∀ i,P.eval (base i)*J.r.a.eval (base i)=Q.eval (base i)*J.s.a.eval (base i) ↔ i∉A :=
  reduced base_injective J.r J.s (wordRows_target J) J.determinant (j9 g) A hA
    (by rw [lJ]; exact hP) (by rw [lJ]; exact hQ)
private theorem reduced_word {D:ℕ} {w:I→K} (J:WordRows D w)
    {S:K→K[X]} {γ:K} {P Q:L[X]}
    (hP:mL (aU w S γ)*P=output J.s (S γ))
    (hQ:mL (aU w S γ)*Q=output J.r (S γ)) :
    IsCoprime P Q ∧ ∀ i,
      P.eval (base i)*J.r.a.eval (base i)= Q.eval (base i)*J.s.a.eval (base i) ↔
        ¬ hit w S γ i:= by
  have hsites (i:I) :i∈aU w S γ ↔
      (j9 (S γ)).eval (base i)=algebraMap K L (w i) := by
    rw [lift_eval,(nI K L).eq_iff]
    exact mem_sites
  have hred:=rwG J hsites hP hQ
  exact ⟨hred.1,fun i=>(hred.2 i).trans mem_sites.not⟩
private theorem word_determinant {D:ℕ} {w:I→K} (J:WordRows D w) :
  ∃ c:L,c≠0∧J.r.a*J.s.b-J.s.a*J.r.b=C c*mL univ := by
 obtain ⟨c,hc,he⟩:=J.determinant
 exact ⟨c,hc,he.trans (c9 (fun t=>C c*t) (lJ univ))⟩
private theorem degree_transfer {a b d e h p q:ℕ} (e₀:a=d) (e₁:b=e)
  (hb:h≤d∧q≤d-h∧p≤e-h) :h≤a∧q≤a-h∧p≤b-h:= by
 rw [e₀,e₁]
 exact hb
private theorem chart_pack {D:ℕ} {w:I→K} {U:Finset K} {S:K→K[X]}
  (J:WordRows D w) {u₀ u₁:ℕ} (ho:u₀≤u₁)
  (hw:2*lI+(u₀+u₁)=blockLength+D)
  (e₀:lI+u₀=J.d₀) (e₁:lI+u₁=J.d₁) (P Q:K→ L[X])
  (hQne : ∀ γ∈U,Q γ≠0)
  (hP : ∀ γ,mL (aU w S γ)*P γ=output J.s (S γ))
  (hQ : ∀ γ,mL (aU w S γ)*Q γ=output J.r (S γ))
  (degree : ∀ γ∈U,(aU w S γ).card≤J.d₀ ∧
    (Q γ).natDegree≤J.d₀-(aU w S γ).card∧(P γ).natDegree≤J.d₁-(aU w S γ).card) :
  Nonempty (DualWord D w U S) := by
 have hred γ:=reduced_word J (hP γ) (hQ γ)
 refine ⟨{
  a₀:=J.r.a,a₁:=J.s.a,b₀:=J.r.b,b₁:=J.s.b
  u₀:=u₀,u₁:=u₁
  order :=ho
  gMz :=hw
  row₀:=Eq.mpr (c9 (ic D J.r.a J.r.b) e₀) J.bound₀
  row₁:=Eq.mpr (c9 (ic D J.s.a J.s.b) e₁) J.bound₁
  determinant:=word_determinant J
  rows_hit := fun i=>⟨J.r.Ju i,J.s.Ju i⟩
  target :=wordRows_target J
  P:=P,Q:= Q
  denominator :=hQne
  coprime := fun γ _=>(hred γ).1
  numerator_ix := fun γ _=>hP γ
  denominator_ix := fun γ _=>hQ γ
  degree := fun γ hγ=>degree_transfer e₀ e₁ (degree γ hγ)
  dual_hits := fun γ _=>(hred γ).2 }⟩
private theorem pickG {w:I→K} (A:K→Finset I) (r :WordRow w) (S:K→K[X])
    (h : ∀ γ,mL (A γ)∣output r (S γ)) : ∃ P:K→ L[X], ∀ γ,mL (A γ)*P γ=output r (S γ) :=
 ⟨fun γ=>Classical.choose (h γ),fun γ=>(Classical.choose_spec (h γ)).symm⟩
private theorem neG {m q N:L[X]} (h:m*q=N) (hN:N≠0) :q≠0:= fun hz=>hN (by rw [← h,hz,lz])
private theorem bY {D:ℕ} {w:I→K} {U:Finset K} {S:K→K[X]}
  (J:WordRows D w) (hU:U.Nonempty)
  (ha : ∀ γ∈U,lI≤(aU w S γ).card)
  (hd : ∀ γ∈U,(S γ).natDegree≤D)
  (hn : ∀ γ∈U,output J.r (S γ)≠0) :Nonempty (DualWord D w U S) := by
 obtain ⟨P,hP'⟩:=pickG (aU w S) J.s S (output_dvd J.s S)
 obtain ⟨Q,hQ'⟩:=pickG (aU w S) J.r S (output_dvd J.r S)
 have hdeg₀ γ (hγ:γ∈U) :=output_degree J.r J.bound₀ (hd γ hγ)
 have hdeg₁ γ (hγ:γ∈U) :=output_degree J.s J.bound₁ (hd γ hγ)
 have hwidth γ (hγ:γ∈U) :=hit_width (hQ' γ) (hdeg₀ γ hγ) (hn γ hγ)
 have hA:lI≤J.d₀:= by
  obtain ⟨γ,hγ⟩:=hU
  exact (ha γ hγ).trans (hwidth γ hγ)
 have hQne γ (hγ:γ∈U) :Q γ≠0:=neG (hQ' γ) (hn γ hγ)
 have hA' := hA.trans J.order
 exact chart_pack J (Nat.sub_le_sub_right J.order lI)
  (gMz hA hA' (J.width.trans (c9 (· + D) index_card)))
  (shifted_width hA) (shifted_width hA') P Q hQne hP' hQ' fun γ hγ =>
  ⟨hwidth γ hγ,quotient_degree (hQ' γ) (hdeg₀ γ hγ),quotient_degree (hP' γ) (hdeg₁ γ hγ)⟩
theorem proof :P5_7_7.c2 := by
 intro D w T z S M
 by_cases hsmall:T.card≤1
 · exact Or.inl hsmall
 obtain ⟨J⟩:=wordRows D w
 let U:=T.filter fun γ=>output J.r (S γ)≠0
 have hU:U⊆T:=filter_subset _ _
 have hn : ∀ γ∈U,output J.r (S γ)≠0:= fun _ h=>(mem_filter.mp h).2
 have hbad: (T.filter fun γ=>output J.r (S γ)=0).card≤1 := by
   refine Finset.card_le_one.mpr fun α ha β hb=>M.sections
     (mem_filter.mp ha).1 (mem_filter.mp hb).1 ?_
   have ha' := (mem_filter.mp ha).2
   have hb' := (mem_filter.mp hb).2
   have hra :J.r.a≠0:= by
     intro hz
     have hrb:J.r.b=0:= by simpa only [output,hz,zero_mul,zero_add] using ha'
     exact det_ne J (by simp only [det,hz,hrb,zero_mul,lz ,sub_self])
   have he :=ha'.trans hb'.symm
   unfold output at he
   exact Polynomial.map_injective _ (nI K L)
     (mul_left_cancel₀ hra (add_right_cancel he))
 have hsize :T.card≤U.card+1 := by
   have hs :=card_filter_add_card_filter_not (s :=T) (fun γ=>output J.r (S γ)≠0)
   simp only [not_not] at hs
   exact hs.symm.le.trans (mD hbad _)
 have hpos :0<U.card:=Nat.pos_of_ne_zero fun hz =>
   hsmall (by simpa only [hz,zero_add] using hsize)
 exact Or.inr ⟨U,hU,hsize,bY J (card_pos.mp hpos)
   (fun γ hγ=>M.dw γ (hU hγ)) (fun γ hγ=>M.degree γ (hU hγ)) hn⟩
end
end q20JTGa

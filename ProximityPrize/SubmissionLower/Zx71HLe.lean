import ProximityPrize.SubmissionLower.ZyrUiId
import ProximityPrize.SubmissionLower.Z6ykYva
import ProximityPrize.SubmissionLower.ZIbuJkc
set_option Elab.async false
section
set_option autoImplicit true
namespace quj0Mle
noncomputable section
open qkgz7gb (PlaneCurve)
open cu (L)
open MvPolynomial Finset
open scoped BigOperators Classical
private def linear (x :aax) (i:Fin 2) :PlaneCurve :=MvPolynomial.X i - C (x i)
private theorem cYh (x :aax) (i:Fin 2) : (linear x i).totalDegree≤1 := by
 exact (totalDegree_sub _ _).trans (by rw [totalDegree_X,totalDegree_C,Nat.max_zero])
private theorem separator (V:Finset aax) (x :V) :
   ∃ f :PlaneCurve,f.totalDegree≤2*V.card∧f.eval x.val=1 ∧
     ∀ y∈V,y≠x.val→f.eval y=0 ∧ ∀ i:Fin 2,(pderiv i f).eval y=0:= by
 classical
 have coord (y :aax) :y≠x.val → ∃ i,x.val i≠y i:= by
   intro hy
   by_contra! h
   exact hy (funext fun i=>(h i).symm)
 let j (y :aax) :Fin 2 :=if h:y≠x.val then (coord y h).choose else 0
 let A (y :aax) :=linear y (j y)
 let W:=V.erase x.val
 let B := ∏ y∈W,A y ^2
 have hB:B.eval x.val≠0:= by
   rw [show B.eval x.val = ∏ y∈W,(A y).eval x.val^2 by simp [B,map_prod]]
   apply prod_ne_zero_iff.mpr
   intro y hy
   have hne :=(mem_erase.mp hy).1
   exact pow_ne_zero _ (by
     simpa [A,linear,j,hne,sub_ne_zero] using (coord y hne).choose_spec)
 let f :=C (B.eval x.val)⁻¹*B
 refine ⟨f,?_,?_,?_⟩
 · have hW:W.card≤V.card:=card_le_card (erase_subset x.val V)
   have hd:B.totalDegree ≤ ∑ y∈W,(A y ^2).totalDegree :=
     totalDegree_finsetProd _ _
   have hs : (∑ y∈W,(A y ^2).totalDegree) ≤ ∑ _y∈W,(2 :ℕ) :=
     sum_le_sum fun y _=>(totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (cYh y _))
   have h' := (totalDegree_mul (C (B.eval x.val)⁻¹) B).trans
     (Nat.add_le_add (totalDegree_C _).le (hd.trans hs))
   exact h'.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hW)
 · simp [f,hB]
 · intro y hy hne
   have hyW:y∈W:=mem_erase.mpr ⟨hne,hy⟩
   have ha : (A y).eval y=0:= by simp [A,linear]
   have hp:B=A y ^2 * ∏ z∈W.erase y,A z^2 :=
     (mul_prod_erase W (fun z=>A z^2) hyW).symm
   constructor
   · simp [f,hp,ha]
   · intro i
     simp [f,hp,ha]
private def deriv (x v :aax) :PlaneCurve →ₗ[L] L :=
 ∑ i:Fin 2,v i•((aeval x).toLinearMap.comp (pderiv i).toLinearMap)
private theorem deriv_apply (x v :aax) (f :PlaneCurve) :
  deriv x v f=v 0*(pderiv 0 f).eval x+v 1*(pderiv 1 f).eval x := by
 simp [deriv,Fin.sum_univ_two,aeval_eq_eval,smul_eq_mul]
private theorem deriv_mul (x v :aax) (f g:PlaneCurve) :
  deriv x v (f*g)=deriv x v f * g.eval x+f.eval x*deriv x v g:= by
 simp only [deriv_apply,pderiv_mul,map_add,map_mul]
 ring
private theorem deriv_linear (x v :aax) (i:Fin 2) :
  deriv x v (linear x i)=v i:= by
 fin_cases i <;> simp [deriv_apply,linear,pderiv_X]
private theorem deriv_C (x v :aax) (a :L) :deriv x v (C a)=0:= by
 simp [deriv_apply]
private theorem linear_eval (x :aax) (i:Fin 2) : (linear x i).eval x=0:= by
 simp [linear]
private theorem tangent_direction (x :aax) (r :PlaneCurve) :
   ∃ v :aax,(∃ j,v j≠0)∧deriv x v r=0:= by
 let a :=(pderiv 0 r).eval x
 let b:=(pderiv 1 r).eval x
 by_cases hb:b=0
 · exact ⟨![0,1],⟨1,by simp⟩,by simpa [deriv_apply,b] using hb⟩
 · refine ⟨![b,-a],⟨0,hb⟩,?_⟩
   simp only [deriv_apply,Matrix.cons_val_zero,Matrix.cons_val_one,a,b]
   ring
private def jet (V S:Finset aax) (v :S→aax) :
   PlaneCurve →ₗ[L] (V→L)×(S→L) :=
 (LinearMap.pi fun x :V=>(aeval x.val).toLinearMap).prod
   (LinearMap.pi fun x :S=>deriv x.val (v x))
private theorem jet_surj (V S:Finset aax) (hS:S⊆V) (v :S→aax)
    (hv : ∀ x,∃ j,v x j≠0) (n:ℕ) (hn:2*V.card+1≤n) :
    Function.Surjective ((jet V S v).comp (Space n).subtype) := by
  classical
  choose F hFdeg hFx hFy using separator V
  choose j hj using hv
  let inc (x :S) :V:=⟨x.val,hS x.property⟩
  let H (x :S) :=F (inc x)*(C ((v x (j x))⁻¹)*linear x.val (j x))
  have hHdeg (x :S) : (H x).totalDegree≤n:= by
    have hm:=totalDegree_mul (C (v x (j x))⁻¹) (linear x.val (j x))
    rw [totalDegree_C,zero_add] at hm
    exact (totalDegree_mul _ _).trans
      ((Nat.add_le_add (hFdeg _) (hm.trans (cYh _ _))).trans hn)
  have hVal (x y :V) : (F x).eval y.val=if x=y then 1 else 0:= by
    split_ifs with h
    · subst y; exact hFx _
    · exact (hFy x _ y.property (fun he=>h (Subtype.ext he.symm))).1
  have hH0 (x :S) (y :V) : (H x).eval y.val=0:= by
    by_cases h:inc x=y
    · subst y
      simp [H,inc,linear]
    · simp [H,hVal,h]
  have hD (x y :S) :deriv y.val (v y) (H x)=if x=y then 1 else 0:= by
    by_cases h:x=y
    · subst y
      have he : (F (inc x)).eval x.val=1 :=hFx (inc x)
      simp [H,deriv_mul,deriv_linear,deriv_C,linear_eval,he,hj]
    · have he :inc x≠inc y := fun he=>h (Subtype.ext (congrArg (fun w:V=>w.val) he))
      have hzero : (F (inc x)).eval y.val=0:= by simpa [he] using hVal (inc x) (inc y)
      have hz : ∀ i,(pderiv i (F (inc x))).eval y.val=0 :=
        (hFy (inc x) _ (inc y).property (fun he=>h (Subtype.ext he.symm))).2
      simp [H,deriv_mul,deriv_apply y.val (v y) (F (inc x)),hz,hzero,h]
  rintro ⟨a,b⟩
  let P:Space n := ∑ x :V,a x•⟨F x,(mem_restrictTotalDegree _ _ _).mpr
    ((hFdeg x).trans (by omega))⟩
  let Q:Space n := ∑ x :S,(b x - deriv x.val (v x) P.val) •
    ⟨H x,(mem_restrictTotalDegree _ _ _).mpr (hHdeg x)⟩
  refine ⟨P+Q,Prod.ext (funext fun y => ?_) (funext fun y => ?_)⟩
  · let E :=(aeval y.val).toLinearMap.comp (Space n).subtype
    change E (P+Q)=a y
    simp [P,Q,E,aeval_eq_eval,hVal,hH0,Finset.sum_ite_eq',mul_ite]
  · let E :=(deriv y.val (v y)).comp (Space n).subtype
    change E (P+Q)=b y
    simp only [Q,E,map_add,map_sum,map_smul,LinearMap.comp_apply,Submodule.subtype_apply,
      hD,smul_eq_mul,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',mem_univ,ite_true]
    abel
theorem dlW {q r :PlaneCurve} (hq:Irreducible q) (hr :r≠0)
   (hd:r.totalDegree<q.totalDegree) (S U:Finset aax) (hdisj:Disjoint S U)
   (hqS : ∀ x∈S,∀ i:Fin 2,(pderiv i q).eval x=0)
   (hqV : ∀ x∈S∪U,q.eval x=0) (hrV : ∀ x∈S∪U,r.eval x=0) :
   2*S.card+U.card≤q.totalDegree*r.totalDegree := by
 classical
 let V:=S∪U
 choose v hv hv0 using fun x :S=>tangent_direction x.val r
 let J:=Ib q r
 let F:=jet V S v
 have hker :J.restrictScalars L≤LinearMap.ker F:= by
   intro f hf
   change f∈J at hf
   obtain ⟨a,b,rfl⟩:=Ideal.mem_span_pair.mp hf
   apply LinearMap.mem_ker.mpr
   refine Prod.ext (funext fun x => ?_) (funext fun x => ?_)
   · change (a*q+b*r).eval x.val=0
     simp [hqV _ x.property,hrV _ x.property]
   · have hx :x.val∈V:=mem_union_left U x.property
     have hq0:deriv x.val (v x) q=0:= by simp [deriv_apply,hqS _ x.property]
     change deriv x.val (v x) (a*q+b*r)=0
     simp [deriv_mul,hq0,hv0 x,hqV _ hx,hrV _ hx]
 let n:=max (2*V.card+1) (q.totalDegree+r.totalDegree)
 let G:quotientDegreeLE J n →ₗ[L] (V→L)×(S→L) :=
   ((J.restrictScalars L).liftQ F hker).comp (quotientDegreeLE J n).subtype
 have hs :Function.Surjective G:= by
   intro y
   obtain ⟨f,hf⟩:=jet_surj V S (subset_union_left) v hv n (le_max_left _ _) y
   exact ⟨⟨Ideal.Quotient.mk J f.val,mk_mem_quotientDegreeLE
     ((mem_restrictTotalDegree _ _ _).mp f.property)⟩,hf⟩
 have hlow:=LinearMap.finrank_le_finrank_of_surjective hs
 rw [Module.finrank_prod,Module.finrank_fintype_fun_eq_card,Module.finrank_fintype_fun_eq_card,
   Fintype.card_coe,Fintype.card_coe] at hlow
 have hcard:V.card=S.card+U.card:=card_union_of_disjoint hdisj
 have hup:=pair_rank hq hr hd n (le_max_right _ _)
 change _≤affineHilbertFunction J n at hlow
 exact (show 2*S.card+U.card≤affineHilbertFunction J n by omega).trans hup
end
end quj0Mle
end
section
set_option autoImplicit true
namespace quj0Mle
noncomputable section
open P5 (K)
open qkgz7gb (PlaneCurve rV SmoothAt)
open cu (L triangle)
open MvPolynomial Finset
private theorem affine_linear (q:PlaneCurve) (hd:q.totalDegree≤1) (i:Fin 2) :
   pderiv i q=C (q.coeff (Finsupp.single i 1)) := by
 classical
 ext m
 by_cases hm:m=0
 · subst m
   simp [coeff_pderiv,coeff_C]
 · have hdeg:0< m.degree :=Nat.pos_of_ne_zero fun hz =>
     hm ((Finsupp.degree_eq_zero_iff _).mp hz)
   have ha :q.totalDegree<(m+Finsupp.single i 1).degree := by
     rw [map_add,Finsupp.degree_single]
     omega
   rw [coeff_pderiv,coeff_eq_zero_of_totalDegree_lt ha,zero_mul,coeff_C,ite_eq_right (Ne.symm hm)]
private theorem linear_smooth {q:PlaneCurve} (hq:Irreducible q)
  (hd:q.totalDegree≤1) {x :aax} (hx :q.eval x=0) :SmoothAt q x := by
 classical
 by_contra hs
 have hdeg:q.totalDegree=0:= by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro m hm
  have hb:m.degree≤1 :=(le_totalDegree hm).trans hd
  change m.degree≤0
  by_contra! hn
  have h₁:m.degree=1 := by omega
  obtain ⟨i,rfl⟩:=(Finsupp.sum_eq_one_iff m).mp h₁
  apply hs
  refine ⟨hx,i,?_⟩
  rw [affine_linear q hd,eval_C]
  exact mem_support_iff.mp hm
 exact (totalDegree_pos_of_span_singleton_ne_top hq.ne_zero
  (mt Ideal.span_singleton_eq_top.mp hq.not_isUnit)).ne' hdeg
private theorem extra_points {q:PlaneCurve} (hq:Irreducible q) (S:Finset aax) (m:ℕ) :
  ∃ U:Finset aax,U.card=m∧Disjoint S U ∧ ∀ x∈U,q.eval x=0:= by
 let I:Ideal PlaneCurve :=Ideal.span {q}
 have hI:I ≠ ⊤ := mt Ideal.span_singleton_eq_top.mp hq.not_isUnit
 have hinf : (zeroLocus L I).Infinite := by
  intro hfin
  have hz :=(finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero I).mp hfin
  have hd:=natDegree_affineHilbertPolynomial_span_singleton_add_one hq.ne_zero hI
  rw [hz,Nat.card_fin] at hd
  omega
 obtain ⟨U,hU,hcard⟩:=(hinf.sdiff S.finite_toSet).exists_subset_card_eq m
 refine ⟨U,hcard,disjoint_left.mpr fun x hx hy=>(hU hy).2 hx,?_⟩
 exact fun x hx=>(hU hx).1 q (Ideal.mem_span_singleton_self q)
private theorem auxiliary_budget {d:ℕ} (hd:2≤d) :
   ∃ e m:ℕ,e<d∧(d-1)*(d-2)/2+1+m<triangle e ∧
     d*e<2*((d-1)*(d-2)/2+1)+m:= by
 by_cases h:d = 2
 · subst d
   exact ⟨1,1,by decide⟩
 obtain ⟨t,rfl⟩ : ∃ t,d=t+3:=⟨d-3,by omega⟩
 rw [show t+3-1=t+2 by omega,show t+3-2=t+1 by omega,Nat.mul_comm (t+2) (t+1)]
 have hA:2*((t+1)*(t+2)/2)=(t+1)*(t+2) :=XK (t+1)
 have hT:2*triangle (t+1)=(t+2)*(t+3) :=bye (t+1)
 have ha : (t+2)*(t+3)=(t+1)*(t+2)+2*(t+2) := by ring
 have hb: (t+3)*(t+1)+1=(t+1)*(t+2)+2+t:= by ring
 refine ⟨t+1,t,by omega,?_,?_⟩ <;> omega
private theorem mark_inj {T:Finset K} {z :K→K} (hz :Set.InjOn z (T:Set K)) :
  Set.InjOn (rV z) (T:Set K) := by
 intro x hx y hy h
 apply hz hx hy
 exact (algebraMap K L).injective (congrFun h 0)
theorem proof :qkgz7gb.c4 := by
 classical
 intro T z hz q hq _
 let B:=T.filter fun γ=>q.eval (rV z γ)=0 ∧ ¬ SmoothAt q (rV z γ)
 let C:=B.image (rV z)
 have hc:C.card=B.card :=
   card_image_of_injOn ((mark_inj hz).mono (filter_subset _ _))
 change B.card≤_
 rw [← hc]
 have hsing (x :aax) (hx :x∈C) :q.eval x=0 ∧ ¬ SmoothAt q x := by
   obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hx
   exact (mem_filter.mp hγ).2
 by_cases hsmall:q.totalDegree≤1
 · have hem:C = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx =>
     (hsing x hx).2 (linear_smooth hq hsmall (hsing x hx).1)
   simp [hem]
 by_contra! hbad
 obtain ⟨S,hS,hcard⟩:=exists_subset_card_eq (Nat.succ_le_of_lt hbad)
 obtain ⟨e,m,he,hdim,hcount⟩:=auxiliary_budget (d:=q.totalDegree) (by omega)
 obtain ⟨U,hU,hdisj,hqU⟩:=extra_points hq S m
 have hsize : (S∪U).card<triangle e := by
   rw [card_union_of_disjoint hdisj,hcard,hU]
   exact hdim
 obtain ⟨r,hr,hre,hrV⟩:=interpolate (S∪U) e hsize
 have hqV : ∀ x∈S∪U,q.eval x=0:= by
   intro x hx
   exact (mem_union.mp hx).elim (fun hs=>(hsing x (hS hs)).1) (hqU x)
 have hgrad : ∀ x∈S,∀ i:Fin 2,(pderiv i q).eval x=0:= by
   intro x hx i
   by_contra hi
   have hh:=hsing x (hS hx)
   exact hh.2 ⟨hh.1,i,hi⟩
 have hb:=dlW hq hr (hre.trans_lt he) S U hdisj hgrad hqV hrV
 rw [hcard,hU] at hb
 exact hcount.not_ge (hb.trans (Nat.mul_le_mul_left _ hre))
end
end quj0Mle
end

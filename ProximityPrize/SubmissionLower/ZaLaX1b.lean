import ProximityPrize.SubmissionLower.L
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.Zw2ME7d
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.Z6jV1pb
import ProximityPrize.SubmissionLower.ZK7Ye0a
set_option Elab.async false
set_option maxHeartbeats 12000000
section
set_option autoImplicit true
namespace bat
noncomputable section
open Polynomial aR dN Rl
private theorem c7d (g:af 4) (n:ℕ) :raw false g n=su g n:= by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [raw,ih,step,Bool.false_eq_true,↓reduceIte,Fy,su]
@[simp] private theorem ajn (P:af 4) (m:Fin 4 →₀ ℕ) :
    (lX P).coeff m=derivative (P.coeff m) := by
  classical
  rw [lX,MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial,Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm,map_zero]
private theorem a2H (P Q:af 4) :
    lX (P*Q)=lX P*Q+P*lX Q:= by
  classical
  ext m
  simp only [ajn,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,
    MvPolynomial.coeff_mul,map_sum,derivative_mul,Finset.sum_add_distrib]
private theorem a6r (P Q:af 4) :
    pK (P*Q)=pK P*Q+P*pK Q:= by
  simp only [pK,a2H,MvPolynomial.pderiv_mul,
    add_mul,mul_add,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  have h (i:Fin 3) :
      MvPolynomial.C (C ((i.val+1 :ℕ) :ao))*MvPolynomial.X i.succ *
        (P*MvPolynomial.pderiv i.castSucc Q) =
      P*(MvPolynomial.C (C ((i.val+1 :ℕ) :ao))*MvPolynomial.X i.succ *
        MvPolynomial.pderiv i.castSucc Q) := by ac_rfl
  simp only [← mul_assoc,← Finset.sum_mul] at h ⊢
  simp only [h]
  ring
private theorem ZF (g P Q:af 4) :
    u6 g (P*Q)=u6 g P*Q+P*u6 g Q:= by
  simp only [u6,a6r,separant,MvPolynomial.pderiv_mul]
  ring
private theorem c7g (g:af 4) (h:separant (separant g)=0) (n:ℕ) :
    su g n=separant g^n*raw true g n:= by
  have hD:u6 g (separant g)=separant g*pK (separant g) := by
    simp [u6,h]
  have hOne :u6 g 1=0:= by
    have hm:=ZF g 1 1
    simp only [mul_one,one_mul] at hm
    linear_combination -hm
  have hp (a :ℕ) :
      u6 g (separant g^a)=(a :af 4)*separant g^a*pK (separant g) := by
    induction a with
    | zero=>simp [hOne]
    | succ a ih =>
      rw [pow_succ,ZF,ih,hD,Nat.cast_succ]
      ring
  induction n with
  | zero=>simp [su,raw]
  | succ n ih =>
    simp only [su,raw,step,Fy,↓reduceIte,one_mul,ih,aqZ,
      ZF,hp,hD,pow_succ,Nat.cast_mul,Nat.cast_ofNat]
    ring
theorem gBe (linear :Bool) (g:af 4)
    (hl:linear=true→separant (separant g)=0)
    (aI:Ideal GeoJets) (hp:aI.IsPrime) (hr :bC (separant g)∉aI) :
    bC (raw linear g bf)∈aI↔bC (vU g)∈aI:= by
  cases linear with
  | false=>rw [c7d,vU]
  | true =>
    have hn:bC (separant g)^bf∉aI :=
      fun h=>hr (hp.mem_of_pow_mem _ h)
    unfold vU
    rw [c7g g (hl rfl)]
    simp only [bC,map_mul,map_pow] at hn ⊢
    exact ⟨fun h=>aI.mul_mem_left _ h,fun h=>(hp.mem_or_mem h).resolve_left hn⟩
end
end bat
end
section
open _root_ renaming MvPolynomial.weightedTotalDegree_mul_le→c9,MvPolynomial.weightedTotalDegree_pderiv_le_sub→lI,Nat.add_le_add→cy,Nat.add_le_add_left→mD,Nat.le_add_right→nq,Nat.mul_add→nX,Nat.mul_le_mul_left→lV,Nat.mul_le_mul_right→nI,Nat.sub_le_sub_right→lz,Submodule.sub_mem→lJ,aR.shape→aU
set_option autoImplicit true
namespace bat
noncomputable section
open Polynomial MvPolynomial aR Ex dN wH lB
open Sr.Weight
local notation "W" => MvPolynomial.weightedTotalDegree
private theorem al0 (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
    {g P:af 4} {B d:ℕ} (hB:w 3≤B) (hg:W w g≤B) (hP:W w P≤d) :
    W w (u6 g P)≤d+(B - w 3)+Δ:= by
  have hsep:=(lI w 3 g).trans (lz hg (w 3))
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply lJ
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    exact (c9 _ _ _).trans
      ((cy hsep (aa5 w Δ hshift P hP)).trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    by_cases h:w 3≤d
    · have hp:=(lI w 3 P).trans (lz hP (w 3))
      exact (c9 _ _ _).trans
        ((cy (aa5 w Δ hshift g hg) hp).trans (by omega))
    · rw [separant,arU w _ P (hP.trans_lt (Nat.lt_of_not_ge h)),
        mul_zero,weightedTotalDegree_zero]
      exact Nat.zero_le _
private theorem dlS (w:Fin 4→ℕ) (a :ℕ) (P:af 4) :
  W w ((a :af 4)*P)≤W w P:= by
 rw [← map_natCast (MvPolynomial.C:ao[X] →+* af 4)]
 exact Po w _ _
private theorem step_bound (linear :Bool) (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
    {g P:af 4} {B d:ℕ} (hB:w 3≤B) (hg:W w g≤B) (hP:W w P≤d) (a :ℕ) :
    W w (step linear g a P)≤d+(Fy linear*(B - w 3)+Δ) := by
  have hsep:W w (separant g)≤B - w 3 :=
    (lI w 3 g).trans (lz hg (w 3))
  cases linear
  · simp only [step,Bool.false_eq_true,↓reduceIte,Fy,aqZ]
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply lJ <;> apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    · exact (c9 _ _ _).trans
        ((cy hsep (al0 w Δ hshift hB hg hP)).trans (by omega))
    · exact (c9 _ _ _).trans (cy
        ((dlS _ _ _).trans (al0 w Δ hshift hB hg hsep)) hP |>.trans (by omega))
  · simp only [step,Fy,↓reduceIte,one_mul]
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply lJ <;> apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    · exact (al0 w Δ hshift hB hg hP).trans (by omega)
    · exact (c9 _ _ _).trans (cy
        ((dlS _ _ _).trans (aa5 w Δ hshift _ hsep)) hP |>.trans (by omega))
private theorem ceI (linear :Bool) (w:Fin 4→ℕ) (Δ:ℕ)
   (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) {g:af 4} {B:ℕ}
   (hB:w 3≤B) (hg:W w g≤B) (n:ℕ) :
   W w (raw linear g n)≤w 0+n*(Fy linear*(B - w 3)+Δ) := by
 induction n with
 | zero=>simpa only [raw,zero_mul,add_zero] using abx (R:=ao[X]) w 0
 | succ n ih =>
   simpa only [raw,Nat.add_mul,one_mul,Nat.add_assoc] using
     step_bound linear w Δ hshift hB hg ih (Fy linear*n)
private theorem cpc (g:af 4) (w:Fin 4→ℕ) (a :ℕ) {B:ℕ} (hg:W w g≤B) :
   W w (separant g^a)≤a*(B - w 3) :=
 (weightedTotalDegree_pow_le _ _ _).trans (lV _
   ((lI w 3 g).trans (lz hg _)))
private theorem Vi (w:Fin 4→ℕ) (Δ:ℕ)
    (hshift : ∀ i:Fin 3,w i.succ≤w i.castSucc+Δ)
    {g:af 4} {B:ℕ} (hB:w 3≤B) (hg:W w g≤B) (i:Fin bf) :
    W w (numerator g i)≤w 0+bf*(Fy (ail g)*(B - w 3)+Δ) := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sum_mem
  intro j _
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
  apply (Po _ _ _).trans
  unfold bqQ
  apply (Po _ _ _).trans
  apply (c9 _ _ _).trans
  let k :=Fy (ail g)
  calc
    _≤k*(bf - j.val)*(B - w 3) +
        (w 0+j.val*(k*(B - w 3)+Δ)) :=
      cy (cpc g w _ hg) (ceI _ w Δ hshift hB hg _)
    _=w 0+(bf - j.val+j.val)*(k*(B - w 3))+j.val*Δ:= by ring
    _≤_:= by
      rw [Nat.sub_add_cancel j.isLt.le,nX ,← Nat.add_assoc]
      exact mD (nI Δ j.isLt.le) _
private theorem b2V {g Q:af 4} (hg:0<(aU g).t)
   (h : ∀ (w:Fin 4→ℕ) (Δ B:ℕ),(∀ i:Fin 3,w i.succ≤w i.castSucc+Δ) →
     w 3≤B→W w g≤B →
     W w Q≤w 0+bf*(Fy (ail g)*(B - w 3)+Δ)) :
   aO (aU Q) (rH (aU g)) := by
 let p:=(aU g).iU
 let k :=Fy (ail g)
 have hch:bF p:=Tn g
 have hj:3≤p.j:= by
   have htop:3*p.t≤p.j:=hch.2
   have hpos :0<p.t:=hg
   omega
 have hb:1≤p.b:= by have hb:p.j≤p.b:=hch.1; omega
 let w:Fin 4→ℕ:=Pi.single 3 1
 have hbQ:Q.totalDegree≤1+bf*(k*(p.b - 1)) := by
   have hbg:W (1 :Fin 4→ℕ) g≤p.b:= by
     rw [weightedTotalDegree_one]
     change g.totalDegree≤ max g.totalDegree (qE g)
     exact le_max_left _ _
   have h' := h 1 0 p.b (fun _=> by simp) hb hbg
   simpa only [weightedTotalDegree_one,Pi.one_apply,add_zero] using h'
 have hjQ:W Fin.val Q≤bf*(k*(p.j-3)+1) := by
   have h' := h Fin.val 1 p.j (fun _=> by rfl) hj (by rw [← C6]; rfl)
   change W Fin.val Q≤0+bf*(k*(p.j-3)+1) at h'
   rwa [zero_add] at h'
 have htQ:Q.degreeOf 3≤bf*(k*(p.t - 1)+1) := by
   have h' := h w 1 p.t (fun i=> by fin_cases i <;> decide)
     (by change 1≤p.t; exact hg)
     (by simp only [w,weightedTotalDegree_piSingle]; exact le_rfl)
   simpa only [w,weightedTotalDegree_piSingle,show w 0=0 by decide,
     show w 3=1 by decide,zero_add] using h'
 unfold rH
 change aO (aU Q) (if (aU g).t=1 then ajN p else bY (bf+4) p)
 have hbox (b j t:ℕ) (hB:Q.totalDegree≤b) (hJ:W Fin.val Q≤j)
     (hT:Q.degreeOf 3≤t) :aO (aU Q) ⟨max b j,j,min t (j/3)⟩:= by
   refine ⟨hB.trans (le_max_left _ _),?_,le_min hT ?_⟩
   · change qE Q≤j
     rwa [C6]
   · change Q.degreeOf 3≤j/3
     have htj:=(a9d Q).trans hJ
     omega
 split_ifs with hlin
 · have hk :k=1 := by simp [k,ail,hlin,Fy]
   have ht:p.t=1 :=hlin
   apply hbox
   · simpa only [hk,one_mul] using hbQ
   · rw [hk,one_mul,show p.j-3+1=p.j - 2 by omega] at hjQ
     exact hjQ.trans (Nat.le_add_left _ _)
   · simp only [hk,ht,Nat.sub_self,mul_zero,zero_add,mul_one] at htQ
     exact htQ.trans (Nat.le_succ _)
 · have hk :k=2 := by simp [k,ail,hlin,Fy]
   have hw:bf≤bf+4 :=nq  _ _
   have hscale (n:ℕ) :bf*(2*n)≤2*(bf+4)*n:= by
     rw [← Nat.mul_assoc,Nat.mul_comm bf 2]
     exact nI  n (lV  2 hw)
   apply hbox
   · rw [hk] at hbQ
     exact hbQ.trans (mD  (hscale _) 1)
   · simp only [hk,nX ,mul_one] at hjQ
     exact hjQ.trans ((cy  (hscale _) hw).trans (nq  _ _))
   · simp only [hk,nX ,mul_one] at htQ
     exact htQ.trans ((cy  (hscale _) hw).trans (nq  _ _))
theorem b0q {g:af 4} (hg:0<(aU g).t) :
  aO (aU (denominator g bf)) (rH (aU g)) := by
 apply b2V hg
 intro w Δ B _ _ hB
 have hp:=cpc g w (Fy (ail g)*bf) hB
 refine hp.trans ?_
 calc
  _=bf*(Fy (ail g)*(B - w 3)) := by ring
  _≤_:=Nat.le_add_left_of_le (lV _ (nq _ _))
theorem eFD {g:af 4} (hg:0<(aU g).t) (i:Fin bf) :
  aO (aU (numerator g i)) (rH (aU g)) :=
 b2V hg (fun w Δ _ hs h3 hB=>Vi w Δ hs h3 hB i)
theorem aX4 {g:af 4} (hg:0<(aU g).t) :
  aO (aU (raw (ail g) g bf)) (rH (aU g)) :=
 b2V hg (fun w Δ _ hs h3 hB=>ceI _ w Δ hs h3 hB _)
end
end bat
end
section
section
set_option autoImplicit true
set_option maxRecDepth 20000
namespace qJrKOKe
open qMHqmcc (GG receipt appendGrades)
set_option quotPrecheck false in
local notation "az" => (receipt 2565 rfl (by decide +kernel) (by decide +kernel))
private theorem r1 :GG b10 52 4 :=⟨az,az,az,az,True.intro⟩
private theorem r2 :GG b10 56 4 :=⟨az,az,az,az,True.intro⟩
private theorem r3:GG b10 60 4 :=⟨az,az,az,az,True.intro⟩
private theorem r4 :GG b10 64 4 :=⟨az,az,az,az,True.intro⟩
private theorem r5:GG b10 68 4 :=⟨az,az,az,az,True.intro⟩
private theorem r6:GG b10 72 1 :=⟨az,True.intro⟩
theorem d:GG b10 52 21 :=
 appendGrades (appendGrades (appendGrades (appendGrades (appendGrades r1 r2) r3) r4) r5) r6
end qJrKOKe
end
section
set_option autoImplicit true
namespace qQ9yWTb
noncomputable section
open Polynomial Finset
open P5 (K p)
open cu (Equation FX qD)
open P5_7_7 (seedEmbedding_injective)
private theorem c8H (i:Fin 2) {f g:Equation} {u v :ℕ}
    (hf : ∀ j,(f.coeff j).degreeOf i≤u) (hg : ∀ j,(g.coeff j).degreeOf i≤v) :
    (f.resultant g).degreeOf i≤f.natDegree*v+g.natDegree*u:= by
  classical
  let m:=f.natDegree
  let n:=g.natDegree
  let A:=sylvester f g m n
  let cap:Fin (m+n)→ℕ:= fun j=>j.addCases (fun _=>v) (fun _=>u)
  have hentry (a b:Fin (m+n)) : (A a b).degreeOf i≤ cap b:= by
    refine Fin.addCases ?_ ?_ b
    · intro j
      simp only [A,cap,sylvester,Matrix.of_apply,Fin.addCases_left]
      split
      · exact hg _
      · simp
    · intro j
      simp only [A,cap,sylvester,Matrix.of_apply,Fin.addCases_right]
      split
      · exact hf _
      · simp
  change A.det.degreeOf i≤ m*v+n*u
  rw [Matrix.det_apply]
  exact (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun π _=> by
    have hp: (∏ j,A (π j) j).degreeOf i≤ m*v+n*u :=
      (MvPolynomial.degreeOf_prod_le _ _ _).trans (calc
        _ ≤ ∑ j,cap j:=sum_le_sum fun j _=>hentry (π j) j
        _ = _:= by rw [Fin.sum_univ_add]; simp [cap])
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;>
      simpa [h,MvPolynomial.degreeOf_neg] using hp)
private theorem common_root {f g:Equation} (hpos :0<f.natDegree)
  (z :K) (y :FX) (hf :f.eval₂ (qD z) y=0)
  (hg:g.eval₂ (qD z) y=0) :qD z (f.resultant g)=0:= by
 obtain ⟨a,b,_,_,hab⟩:=exists_mul_add_mul_eq_C_resultant f g
  (le_refl _) (le_refl _) (Or.inl hpos.ne')
 have he :=congrArg (eval₂RingHom (qD z) y) hab
 simpa only [coe_eval₂RingHom,eval₂_add,eval₂_mul,eval₂_C,hf,hg,zero_mul,add_zero]
  using he.symm
theorem count_resultant {f g:Equation} {T:Finset K} {z :K→K} {y :K→FX}
    {e E h cz ct :ℕ} (hf :0<f.natDegree) (he :f.natDegree≤e)
    (hE :g.natDegree≤E) (hF:cu.vm f h)
    (hG : ∀ (j:ℕ) (i:Fin 2),(g.coeff j).degreeOf i ≤
      (if i=0 then cz+1 else ct+1)*h)
    (hproper :f.resultant g≠0) (hp: (e*(cz+1)+E)*h<p)
    (hz :Set.InjOn z (T:Set K)) (hfr : ∀ γ∈T,f.eval₂ (qD (z γ)) (y γ)=0)
    (hgr : ∀ γ∈T,g.eval₂ (qD (z γ)) (y γ)=0) :
    T.card≤(e*(cz+1)+E)*h+p*((e*(ct+1)+E)*h) := by
  let R:=f.resultant g
  have hb (i:Fin 2) (c:ℕ) (hc: (if i=0 then cz+1 else ct+1)=c+1) :
      R.degreeOf i≤(e*(c+1)+E)*h:= by
    have hd:=c8H i (fun j=>((f.coeff j).degreeOf_le_totalDegree i).trans (hF j))
      (fun j=> by simpa only [hc] using hG j i)
    refine hd.trans ?_
    calc
      _≤e*((c+1)*h)+E*h :=
        Nat.add_le_add (Nat.mul_le_mul_right _ he) (Nat.mul_le_mul_right _ hE)
      _ = _:= by ring
  have ha :=hb 0 cz (ite_eq_left rfl)
  have hc:=hb 1 ct (ite_eq_right (by decide))
  classical
  rw [← card_image_of_injOn (seedEmbedding_injective.comp_injOn hz)]
  apply cu.bqt p _ _ (by decide) R hproper ha hp hc
  intro t ht
  obtain ⟨γ,hγ,rfl⟩:=mem_image.mp ht
  exact common_root hf (z γ) (y γ) (hfr γ hγ) (hgr γ hγ)
end
end qQ9yWTb
end
section
namespace q1vkLGd
noncomputable section

open cu (L)
open qQ9yWTb (Curve)
open scoped Polynomial
def Smooth (q:Curve) (z :Fin 2→L) :Prop :=
  MvPolynomial.eval z q=0 ∧
    ∃ i,MvPolynomial.eval z (MvPolynomial.pderiv i q)≠0
def FormalLift:Prop :=
  ∀ (q:Curve) (z :Fin 2→L) (i:Fin 2),MvPolynomial.eval z q=0 →
    MvPolynomial.eval z (MvPolynomial.pderiv i q)≠0 →
    ∃ a :Fin 2→PowerSeries L,
      (∀ j,PowerSeries.constantCoeff (a j)=z j) ∧
      MvPolynomial.eval₂ PowerSeries.C a q=0 ∧
      ∀ j,j≠i→a j=PowerSeries.C (z j)+PowerSeries.X
end
end q1vkLGd
end
end

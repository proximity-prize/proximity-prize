import ProximityPrize.SubmissionLower.Z0sgnhc
import ProximityPrize.SubmissionLower.ZPahZ1a
import ProximityPrize.SubmissionLower.ZLWPQ5c
import ProximityPrize.SubmissionLower.ZnTmQ9b
import ProximityPrize.SubmissionLower.Zx4lLde
set_option Elab.async false
open _root_ renaming Finset.sum_le_sum → zQk, Nat.add_le_add → z9f, Nat.add_le_add_right → zlr, Nat.cast_le → z9h, Nat.cast_nonneg → zqJ, Nat.mul_le_mul → zcp, Nat.mul_le_mul_left → zBI, Nat.sub_le_sub_right → zIu, Nat.succ_pos → ztH
section
set_option autoImplicit true
namespace qWYz30a
theorem proof :qpDASwe.c1 :=
  q6CrDDe.of_children q978Lma.proof P5_7_1_5_4_2_1_2.proof
end qWYz30a
end
section
set_option autoImplicit true
namespace qnUAN9d
theorem proof :q49VXnc.c1 :=
  qnyP9Da.of_children q3zqDZc.proof qJQ0Sxd.proof
    qDhaEec.proof
end qnUAN9d
end
section
set_option autoImplicit true
namespace qq81JAd
theorem proof :qvCjzac.c3 :=
  qziIa4d.of_children qOj34lc.proof qJ69aaa.proof
    (qnyP9Da.of_children q3zqDZc.proof qJQ0Sxd.proof
      qDhaEec.proof) qU1uHGd.proof
end qq81JAd
end
section
set_option autoImplicit true
namespace qtqUEwc
open cu (Shape)
open P6_7_3 (lineFee)
open qehP9ee (asShape kK mixedCols)
open qUrGXob (lastOrigin originShape)
open Finset
open TD (FP a3x)
open scoped BigOperators
private abbrev bw:ℕ:=0xd4fbef3ee3031
private theorem line_cap {b j u:ℕ} (hb:b≤12) (hj:j≤2) (hu:u≤130) :
    lineFee b j u≤bw:= by
  let a :=1+267207*(b - 1)
  let z :=min a (267207*(j - 1)+133605)
  let t:=267207*u
  let m:=u*(2*a*z-z*z)+2*t*(b*z+j*(a-z))
  let n:=u*(2*a+z)+t*(2*b+j)+b*z+j*a+u+b+j
  have ha :a≤2939278 :=
    Nat.add_le_add_left (zBI _ (zIu hb 1)) 1
  have hz :z≤400812 :=(min_le_right _ _).trans
    (zlr (zBI _ (zIu hj 1)) 133605)
  have ht:t≤34736910 :=zBI 267207 hu
  have hm:m≤0x3b9ef53b2be70 :=
    z9f
      (zcp hu ((Nat.sub_le _ _).trans (zcp (zBI 2 ha) hz)))
      (zcp (zBI 2 ht)
        (z9f (zcp hb hz) (zcp hj ((Nat.sub_le _ _).trans ha))))
  have hn₁:=zcp hu (z9f (zBI 2 ha) hz)
  have hn₂:=zcp ht (z9f (zBI 2 hb) hj)
  have hn₃:=z9f (z9f hn₁ hn₂) (zcp hb hz)
  have hn:n≤0x67203cb8:=z9f
    (z9f (z9f (z9f hn₃ (zcp hj ha)) hu) hb) hj
  change (164808*(m+n)+46135-1)/46135+b+u+1≤_
  calc
    _≤(164808*(0x3b9ef53b2be70+0x67203cb8)+46135-1)/46135+12+130+1 := by
      refine zlr (z9f (z9f (Nat.div_le_div_right ?_) hb) hu) 1
      exact zIu (zlr (zBI 164808
        (z9f hm hn)) 46135) 1
    _=bw:=rfl
private def upper :Shape :=⟨0,14,2,130⟩
private theorem cols_le {v :Fin 3→ℕ} (hb:v 0≤12) (hj:v 1≤2) (hu:v 2≤130)
    (k :Fin 4) (j:Fin 3) :mixedCols (asShape v) k j≤ mixedCols upper k j:= by
  fin_cases k <;> fin_cases j <;> first
    | exact Nat.zero_le _
    | exact hb.trans (by decide :12≤14)
    | exact hj
    | exact hu
    | exact (Nat.sub_le _ _).trans hb
private theorem fWE (k :Fin 4) :0≤ residual lastOrigin k :=
  div_nonneg (zqJ _) (zqJ _)
private theorem line_margin: (bw:ℚ)≤ residual lastOrigin 0*292 := by
  change (bw:ℚ)≤(((0x257e21f8b06375:ℕ) :ℚ)/((500:ℕ) :ℚ))*292
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by decide : (0:ℚ)<500)).2
  exact_mod_cast (show bw*500≤0x257e21f8b06375*292 by decide)
private theorem iL (j:Fin 3) :
    (∑ k :Fin 4,residual lastOrigin k*(mixedCols upper k j:ℚ)) +
      (if j=1 then (bw:ℚ) else 0)≤unit lastOrigin j:= by
  have hcols (k :Fin 4) :mixedCols upper k j≤ mixedCols (originShape lastOrigin) k j:= by
    fin_cases k <;> fin_cases j <;> decide
  have hn (k :Fin 4) :
      0≤ residual lastOrigin k*((mixedCols (originShape lastOrigin) k j:ℚ) - mixedCols upper k j) :=
    mul_nonneg (fWE k) (sub_nonneg.mpr (Nat.cast_le.mpr (hcols k)))
  have h: (if j=1 then (bw:ℚ) else 0) ≤
      ∑ k :Fin 4,residual lastOrigin k *
        ((mixedCols (originShape lastOrigin) k j:ℚ) - mixedCols upper k j) := by
    by_cases hj:j=1
    · subst j
      rw [ite_eq_left rfl]
      have hdiff : (mixedCols (originShape lastOrigin) 0 1 :ℚ) - mixedCols upper 0 1=292 := by
        change (304 :ℚ) - 12=292
        norm_num
      have hsingle :=single_le_sum (fun k _=>hn k) (mem_univ (0:Fin 4))
      rw [hdiff] at hsingle
      exact line_margin.trans hsingle
    · rw [ite_eq_right hj]
      exact sum_nonneg fun k _=>hn k
  simp only [mul_sub,sum_sub_distrib] at h
  rw [unit]
  linarith only [h]
theorem line_absorbed:absorbs := by
  intro v hv _ hj _
  have hb:v 0≤12 :=(hv 0).trans_eq (by with_unfolding_all rfl)
  have hj' : v 1≤2 :=(hv 1).trans_eq (by with_unfolding_all rfl)
  have hu:v 2≤130:=(hv 2).trans_eq (by with_unfolding_all rfl)
  have hf :=(z9h (α:=ℚ)).mpr (line_cap hb hj' hu)
  have hjQ: (1 :ℚ)≤(v 1 :ℚ) :=Nat.cast_le.mpr (show 1≤v 1 from hj)
  have hm:FP (residual lastOrigin) (kK v (asShape v)) ≤
      FP (residual lastOrigin) (kK v upper) :=
    a3x (fWE) fun k =>
      zQk fun j _=>mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (cols_le hb hj' hu k j)) (zqJ (v j))
  calc
    _≤(bw:ℚ)*(v 1 :ℚ)+FP (residual lastOrigin) (kK v upper) :=
      add_le_add (hf.trans (le_mul_of_one_le_right (zqJ bw) hjQ)) hm
    _ = ∑ j:Fin 3,((∑ k :Fin 4,residual lastOrigin k*(mixedCols upper k j:ℚ)) +
        (if j=1 then (bw:ℚ) else 0))*(v j:ℚ) := by
      rw [dot_mixed]
      simp only [add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,Finset.sum_ite_eq',
        Finset.mem_univ,ite_true,add_comm]
    _≤_:=zQk fun j _=>mul_le_mul_of_nonneg_right (iL j) (zqJ _)
end qtqUEwc
end
section
set_option autoImplicit true
namespace qtqUEwc
open P6_7_3 (IntroIndex bgK introCap)
open qUrGXob
open qehP9ee (kK mixedCols)
open TD (FP a3x)
open cu (Shape)
open pI (weight)
open scoped Classical
def mixedNat (v :Fin 3→ℕ) (s :Shape) (k :Fin 4) :ℕ :=
  v 0*mixedCols s k 0+v 1*mixedCols s k 1+v 2*mixedCols s k 2
theorem mixedNat_cast (v :Fin 3→ℕ) (s :Shape) (k :Fin 4) :
    (mixedNat v s k :ℚ)=kK v s k := by
  simp only [mixedNat,kK,Fin.sum_univ_three,Nat.cast_add,Nat.cast_mul]
private def freeTrial (i:Fin 7) :Trial:=i.castLE (by decide)
private theorem trial_free (i:Fin 7) :trialKind (freeTrial i) = .free i.succ:= by
  fin_cases i <;> rfl
def freeIds (t:Trial) :List (Fin 7) :=
  (List.finRange 7).filter fun i=>decide (i.val<t.val)
def freeCap (o:IntroIndex) (i:Fin 7) (k :Fin 4) :ℕ :=
  mixedNat (bgK (stage i.succ).free) (refShape o) k/((stage i.succ).dI+1)
def baseCap (o:IntroIndex) (t:Trial) (k :Fin 4) :ℕ :=
  (freeIds t).foldl (fun a i=>min a (freeCap o i k))
    (min (mixedNat (introCap o.val) (originShape o) k) (base k))
private theorem le_fold_min {α:Type} (xs :List α) (f :α→ℕ) {a v :ℕ}
    (ha :v≤a) (hx : ∀ x∈xs,v≤f x) :
    v≤xs.foldl (fun z i=>min z (f i)) a := by
  induction xs generalizing a with
  | nil=>exact ha
  | cons x xs ih =>
    exact ih (le_min ha (hx x (List.mem_cons_self ..)))
      (fun y hy=>hx y (List.mem_cons_of_mem _ hy))
theorem base_le {o:IntroIndex} {t:Trial} {v :Fin 4→ℕ}
    (hv :MemberFits o t v) (k :Fin 4) :v k≤baseCap o t k := by
  apply le_fold_min
  · apply le_min
    · apply (z9h (α:=ℚ)).mp
      rw [mixedNat_cast]
      exact (hv.1 k).trans (min_le_left _ _)
    · apply (z9h (α:=ℚ)).mp
      rw [← initial_values]
      have hh:=bHK t.isLt k
      rw [historyAt,dite_eq_left t.isLt] at hh
      exact ((hv.1 k).trans (min_le_right _ _)).trans hh
  · intro i hi
    have hj:i.val<t.val :=of_decide_eq_true (List.mem_filter.mp hi).2
    have hf :=hv.2 (freeTrial i) hj
    rw [trial_free] at hf
    have hfk :=hf k
    let s :=stage i.succ
    change (v k :ℚ)≤kK (bgK s.free) (refShape o) k/(s.dI+1 :ℚ) at hfk
    rw [← mixedNat_cast,← Nat.cast_succ] at hfk
    have hp:=(le_div_iff₀ (Nat.cast_pos.mpr (ztH s.dI))).mp hfk
    exact (Nat.le_div_iff_mul_le (ztH s.dI)).mpr (by exact_mod_cast hp)
private def jX (o:IntroIndex) (t:Trial) :ℕ :=
  let w:=weight (aHp t) 0
  w 0*baseCap o t 0+w 1*baseCap o t 1 +
    w 2*baseCap o t 2+w 3*baseCap o t 3
private theorem price_cast (o:IntroIndex) (t:Trial) :
    (jX o t:ℚ)=FP (SS 0 t) (fun k=>baseCap o t k) := by
  simp only [jX,FP,SS,Fin.sum_univ_four,Nat.cast_add,Nat.cast_mul]
private def toTrial (i:Fin 8) :Trial:=i.castLE (by decide)
set_option maxHeartbeats 4000000 in
private theorem price_check (o:IntroIndex) (i:Fin 8) :
    jX o (toTrial i)*(dD o (toTrial i)+1)≤dN o (toTrial i) := by
  fin_cases o <;> fin_cases i <;> exact Nat.le_of_ble_eq_true (by with_unfolding_all rfl)
theorem directional_early {o:IntroIndex} {t:Trial} {v :Fin 4→ℕ}
    (ht:t.val<8) (hv :MemberFits o t v) :
    min projectionBound (FP (SS 0 t) (fun k=>v k))≤d o t:= by
  apply (min_le_right _ _).trans
  have hp:jX o t*(dD o t+1)≤dN o t:=price_check o ⟨t.val,ht⟩
  calc
    _≤FP (SS 0 t) (fun k=>(baseCap o t k :ℚ)) :=
      a3x (fun _=>zqJ _) (fun k=>Nat.cast_le.mpr (base_le hv k))
    _=(jX o t:ℚ) :=(price_cast o t).symm
    _≤d o t:=(le_div_iff₀ (Nat.cast_pos.mpr (ztH _))).mpr (by exact_mod_cast hp)
end qtqUEwc
end
section
set_option autoImplicit true
namespace qtqUEwc
open qUrGXob
open qJeTDGe (bbD)
def c1 :Prop :=
  ∀ o t (v :Fin 4→ℕ),8≤t.val→0<v 0→MemberFits o t v →
    min projectionBound (TD.FP (SS 0 t) (fun k=>v k))≤d o t
def c2 :Prop := ∀ o t,aSz (d o t) (a o t) (b o t)
def c3:Prop :=
  (∀ o s k,stopPrice a b o s k≤envelopePrice o s k) ∧
  (∀ o j,unit o j≤bbD factorJump o j)
def c4 :Prop :=stageBook+freeBook+factorBook≤(dualFee :ℚ)
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) :qUrGXob.c4 := by
  refine ⟨⟨d,a,b,h2,?_,projection_le,
    fun B=>⟨cut_bill B 0,(cut_bill B 2).trans points_le,
      (dual_bound B line_absorbed h3.2 h3.1).trans h4⟩⟩⟩
  intro o t v hv hf
  by_cases ht:t.val<8
  · exact directional_early ht hf
  · exact h1 o t v (Nat.le_of_not_gt ht) hv hf
end qtqUEwc
end

import ProximityPrize.SubmissionLower.CmpCSum
import ProximityPrize.SubmissionLower.Z9Rfpte
import ProximityPrize.SubmissionLower.ZdBkMOd
import ProximityPrize.SubmissionLower.ZjZ6ihd
set_option Elab.async false
section
namespace qCgnalc
open Polynomial
open scoped BigOperators Polynomial
def reciprocalCoeff {F:Type} [Field F] (Q v j q:ℕ) :F :=
 (-1 :F)^(q-j)*((Q-v).choose (q-j) :F)
theorem reciprocal_sum {F:Type} [Field F] {Q v j:ℕ} (hjv :j≤v) (hvQ:v≤Q)
    (r :ℕ) :
    (if r≤v∧j≤ r then ((v-j).choose (r-j) :F) else 0) =
    ∑ q:Fin (Q+1),if j≤q.val∧q.val≤ r then
      reciprocalCoeff Q v j q.val*((Q-q.val).choose (r-q.val) :F) else 0:= by
  let x :F[X] :=Polynomial.X
  let y :=1 + x
  let p (q:ℕ) :=C (reciprocalCoeff (F:=F) Q v j q)*(x^q*y^(Q-q))
  have hy :y + -x = 1 := by simp [y]
  have hpoly :x^j*y^(v-j) = ∑ q∈Finset.Ico j (j+(Q-v+1)),p q:= by
    calc
      _=x^j*y^(v-j)*(y + -x)^(Q-v) := by rw [hy,one_pow,mul_one]
      _ = _:= by
        have hshift:=Finset.sum_Ico_add p 0 (Q-v+1) j
        rw [Nat.Ico_zero_eq_range,zero_add] at hshift
        rw [add_comm y (-x),add_pow (-x) y (Q-v),Finset.mul_sum,
          show j+(Q-v+1)=(Q-v+1)+j by omega,← hshift]
        apply Finset.sum_congr rfl
        intro e he
        have he' := Finset.mem_range.mp he
        have hq:j+e - j=e := by omega
        have hn:v-j+(Q-v-e)= Q-(j+e) := by omega
        dsimp [p,reciprocalCoeff]
        rw [hq,show -x=(-1 :F[X])*x by simp,mul_pow,pow_add x j e,
          ← hn,pow_add y]
        simp only [map_mul,map_pow,map_neg,map_one,C_eq_natCast]
        ring
  have hcoeff (n q:ℕ) : (x^q*y^n).coeff r =
      if q≤ r then (n.choose (r-q) :F) else 0:= by
    dsimp [x,y]
    rw [coeff_X_pow_mul',coeff_one_add_X_pow]
  have hp:=congrArg (fun f :F[X]=>f.coeff r) hpoly
  change (x^j*y^(v-j)).coeff r= _ at hp
  rw [hcoeff,finsetSum_coeff] at hp
  rw [Fin.sum_univ_eq_sum_range (fun q=>if j≤q∧q≤ r then
    reciprocalCoeff (F:=F) Q v j q*((Q-q).choose (r-q) :F) else 0)]
  rw [← Finset.sum_subset (show Finset.Ico j (j+(Q-v+1))⊆Finset.range (Q+1) from by
    intro q hq
    simp only [Finset.mem_Ico,Finset.mem_range] at hq ⊢
    omega)]
  · calc
      _=(if j≤ r then ((v-j).choose (r-j) :F) else 0) := by
        by_cases hr :j≤ r
        · by_cases hrv :r≤v
          · simp [hr,hrv]
          · simp [hr,hrv,Nat.choose_eq_zero_of_lt (show v-j< r-j by omega)]
        · simp [hr]
      _ = _:=hp
      _ = _:= by
        apply Finset.sum_congr rfl
        intro q hq
        change (C (reciprocalCoeff Q v j q)*(x^q*y^(Q-q))).coeff r= _
        rw [coeff_C_mul,hcoeff]
        simp only [(Finset.mem_Ico.mp hq).1,true_and]
        split_ifs <;> simp
  · intro q hq hout
    by_cases hjq:j≤q∧q≤ r
    · have he :Q-v<q-j:= by
        have hn:j+(Q-v+1)≤q :=
          Nat.le_of_not_gt fun h=>hout (Finset.mem_Ico.mpr ⟨hjq.1,h⟩)
        omega
      simp [hjq,reciprocalCoeff,Nat.choose_eq_zero_of_lt he]
    · simp [hjq]
end qCgnalc
end
section
set_option backward.isDefEq.respectTransparency false
namespace qCgnalc
noncomputable section
open Matrix
open cu (Shape)
open Ge (jJ)

open aeL (Offset Pivot Gv a2N beO eKM btx Pa)
open qQCEOid (WindowCol windowMatrix windowBudget)
open scoped BigOperators Matrix
private def Dj (s :Shape) (k :ℕ) :=min s.B k
private def valueCap (s :Shape) (u k :ℕ) :=min u (s.B+u-k)
private def lower (s :Shape) (t:Offset s) (u k q:ℕ) :=
 max (Gv s t) (q-valueCap s u k)
private def cols (s :Shape) (t:Offset s) (u k q:ℕ) :=
 min q s.J+1-lower s t u k q
private def rows (s :Shape) (t:Offset s) (q:ℕ) :=s.B+2*s.J-t.val-q
private abbrev ax0 (s :Shape) (t:Offset s) (u k :ℕ) :=
 Σ q:Fin (Dj s k+1),Fin (min (cols s t u k q.val) (rows s t q.val))
private abbrev eligible (s :Shape) (t:Offset s) (u k q j:ℕ) :Prop :=
 s.J-j≤t.val∧t.val<s.B+2*s.J-(q+min q s.J)+j ∧
  q-j≤u∧q≤k∧k≤ s.B+u-(q-j)
private theorem slots_le_budget (s :Shape) (t:Offset s) (u k :ℕ) (hk :k≤ s.B+u) :
    Fintype.card (ax0 s t u k)≤windowBudget s t u k := by
  classical
  let Target := {z :Σ q:jJ s,Fin (min q.val s.J+1) //
    eligible s t u k z.1.val z.2.val}
  have hc:Fintype.card Target=windowBudget s t u k := by
    let f (q j:ℕ) :=if eligible s t u k q j then (1 :ℕ) else 0
    calc
      Fintype.card Target = ∑ z :Σ q:jJ s,Fin (min q.val s.J+1),
          f z.1.val z.2.val := by
        rw [Fintype.card_subtype]
        exact (Finset.sum_boole (R:=ℕ) (fun z :Σ q:jJ s,Fin (min q.val s.J+1) =>
          eligible s t u k z.1.val z.2.val) Finset.univ).symm
      _ = ∑ q:jJ s,∑ j∈Finset.range (min q.val s.J+1),f q.val j:= by
        rw [Fintype.sum_sigma]
        exact Finset.sum_congr rfl fun q _=>Fin.sum_univ_eq_sum_range (f q.val) _
      _ = _:=Fin.sum_univ_eq_sum_range (fun q =>
        ∑ j∈Finset.range (min q s.J+1),f q j) _
  let f (x :ax0 s t u k) :Target := by
    let q:=x.1.val
    let d:=min q s.J
    let j:=d-x.2.val
    have hq:=Nat.lt_succ_iff.mp x.1.isLt
    have hqB:=hq.trans (min_le_left s.B k)
    have hqk :=hq.trans (min_le_right s.B k)
    have ha :=x.2.isLt.trans_le (min_le_left ..)
    have hb:=x.2.isLt.trans_le (min_le_right ..)
    have hl:lower s t u k q≤j:= by
      change x.2.val<d+1-lower s t u k q at ha
      dsimp [j]
      omega
    have hjJet:=(le_max_left (Gv s t) (q-valueCap s u k)).trans hl
    have hjValue :=(le_max_right (Gv s t) (q-valueCap s u k)).trans hl
    have hvU:=min_le_left u (s.B+u-k)
    have hvB:=min_le_right u (s.B+u-k)
    have hdq:=min_le_left q s.J
    have hdJ:=min_le_right q s.J
    change x.2.val< rows s t q at hb
    unfold rows Gv at *
    refine ⟨⟨⟨q,by omega⟩,⟨j,by dsimp [j]; omega⟩⟩,?_⟩
    change eligible s t u k q j
    unfold eligible
    have hqj:q-j≤valueCap s u k := by omega
    have hspend:=hqj.trans hvB
    dsimp [j] at *
    exact ⟨by omega,by omega,hqj.trans hvU,hqk,by omega⟩
  rw [← hc]
  apply Fintype.card_le_of_injective f
  rintro ⟨q,a⟩ ⟨q',b⟩ h
  have hq:q=q' := Fin.ext (congrArg (fun z :Target=>z.val.1.val) h)
  subst q'
  have hj:min q.val s.J-a.val=min q.val s.J-b.val :=
    congrArg (fun z :Target=>z.val.2.val) h
  have ha :=a.isLt.trans_le (min_le_left ..)
  have hb:=b.isLt.trans_le (min_le_left ..)
  change a.val< min q.val s.J+1-lower s t u k q.val at ha
  change b.val< min q.val s.J+1-lower s t u k q.val at hb
  have :a=b:=Fin.ext (by omega)
  subst b
  rfl
private theorem row_lt {s :Shape} {t:Offset s} (r :Pivot s t) {q:ℕ}
  (hq:q≤ r.1.val) :r.2.val< rows s t q:= by
 have hi:r.2.val<s.B+2*s.J-(t.val+r.1.val) :=
  r.2.isLt.trans_le (min_le_right ..)
 unfold rows
 omega
private def weights (F:Type) [Field F] (s :Shape) (t:Offset s) (u k q:ℕ)
   (i:Fin (rows s t q)) :Fin (min (cols s t u k q) (rows s t q))→F :=
 (eKM F (lower s t u k q) (cols s t u k q) (rows s t q) i.val i.isLt).choose
private def left (F:Type) [Field F] (s :Shape) (t:Offset s) (u k :ℕ) :
   Matrix (Pivot s t) (ax0 s t u k) F :=
 fun r x=>if h:x.1.val≤ r.1.val then
   ((Dj s k-x.1.val).choose (r.1.val-x.1.val) :F) *
     weights F s t u k x.1.val ⟨r.2.val,row_lt r h⟩ x.2
   else 0
private def right (F:Type) [Field F] (s :Shape) (t:Offset s) (u k :ℕ) :
   Matrix (ax0 s t u k) (WindowCol s t u k) F :=
 fun x v=>if a2N v.val≤x.1.val then
   reciprocalCoeff (Dj s k) v.val.1.val (a2N v.val) x.1.val *
     ((a2N v.val).choose x.2.val :F) else 0
private theorem block (F:Type) [Field F] (s :Shape) (t:Offset s) (u k :ℕ)
    (r :Pivot s t) (v :WindowCol s t u k) (q:Fin (Dj s k+1)) :
    (∑ a,left F s t u k r ⟨q,a⟩*right F s t u k ⟨q,a⟩ v) =
    if a2N v.val≤q.val∧q.val≤ r.1.val then
      ((a2N v.val).choose r.2.val :F) *
        (reciprocalCoeff (Dj s k) v.val.1.val (a2N v.val) q.val *
          ((Dj s k-q.val).choose (r.1.val-q.val) :F))
    else 0:= by
  let j:=a2N v.val
  let g:=v.val.1.val
  let Q:=Dj s k
  by_cases hq:q.val≤ r.1.val
  · by_cases hj:j≤q.val
    · by_cases he :q.val-j≤Q-g
      · have hgj:=(beO s t v.val.1 _ v.val.2.isLt).1
        change j≤ min g s.J at hgj
        have hjJ:=hgj.trans (min_le_right _ _)
        have hfirst:Gv s t≤j:=Nat.le_add_right ..
        have hgk :g≤k :=v.property.1
        have hgu:k≤g+u:=v.property.2
        have hgB:g≤ s.B:=Nat.lt_succ_iff.mp v.val.1.isLt
        have hQB:Q≤ s.B:=min_le_left _ _
        have hQk :Q≤k :=min_le_right _ _
        have hh:q.val-j≤valueCap s u k := by
          unfold valueCap
          exact le_min (by omega) (by omega)
        have hl:lower s t u k q.val≤j:=max_le hfirst (by omega)
        have hd:j≤ min q.val s.J:=le_min hj hjJ
        let b:Fin (cols s t u k q.val) :=⟨j-lower s t u k q.val,by
          unfold cols
          omega⟩
        have hb:lower s t u k q.val+b.val=j:= by dsimp [b]; omega
        have hw:=(eKM F (lower s t u k q.val) (cols s t u k q.val)
          (rows s t q.val) r.2.val (row_lt r hq)).choose_spec b
        simp only [btx,hb] at hw
        change (j.choose r.2.val :F) = ∑ a,
          weights F s t u k q.val ⟨r.2.val,row_lt r hq⟩ a*(j.choose a.val :F) at hw
        simp only [left,right,hq,show a2N v.val≤q.val from hj,
          dite_eq_left,ite_true,and_self]
        rw [hw,Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _=> by ring
      · have hz :reciprocalCoeff (F:=F) Q g j q.val=0:= by
          simp [reciprocalCoeff,Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge he)]
        change reciprocalCoeff (F:=F) (Dj s k) v.val.1.val (a2N v.val) q.val=0 at hz
        simp [left,right,hq,show a2N v.val≤q.val from hj,hz]
    · simp [left,right,hq,show ¬ a2N v.val≤q.val from hj]
  · simp [left,hq]
private theorem factor (F:Type) [Field F] (s :Shape) (t:Offset s) (u k :ℕ) :
  windowMatrix F s t u k=left F s t u k*right F s t u k := by
 ext r v
 have hj:a2N v.val≤v.val.1.val :=
  (beO s t v.val.1 _ v.val.2.isLt).1.trans (min_le_left _ _)
 have hv :v.val.1.val≤Dj s k :=le_min
  (Nat.lt_succ_iff.mp v.val.1.isLt) v.property.1
 rw [Matrix.mul_apply,Fintype.sum_sigma]
 simp_rw [block]
 have he :=congrArg (fun z :F=>((a2N v.val).choose r.2.val :F)*z)
  (reciprocal_sum (F:=F) hj hv r.1.val)
 simp only [Finset.mul_sum,mul_ite,mul_zero] at he
 simpa only [windowMatrix,Matrix.submatrix_apply,id_eq,Pa,one_pow,mul_one] using he
theorem proof :qQCEOid.c2 := by
 intro F _ _ s t u k _ _
 by_cases hk :k≤ s.B+u
 · rw [factor]
   exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans (slots_le_budget s t u k hk))
 · have :IsEmpty (WindowCol s t u k) :=⟨fun v=>hk
    (v.property.2.trans (Nat.add_le_add_right (Nat.lt_succ_iff.mp v.val.1.isLt) u))⟩
   exact (Matrix.rank_le_card_width _).trans (by simp)
end
end qCgnalc
end

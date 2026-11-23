import ProximityPrize.SubmissionLower.ZnaMqIa
import ProximityPrize.SubmissionLower.ZUURnQa
set_option Elab.async false
open _root_ renaming Nat.add_assoc→lJ,Nat.cast_add→c9,Nat.cast_mul→lI,Nat.cast_ofNat→lV,Nat.cast_sub→nq,Nat.le_of_lt_succ→nI,Nat.lt_irrefl→mD,Nat.succ_pos→lz,P5_7_2.threshold→cy,cu.Shape→aU,of_decide_eq_true→nX
section
set_option autoImplicit true
namespace qMHqmcc
open Finset cu P5_7_2
open P5_7_6 (O3 phase)
open Y2 (aOy Tb bg5 aJq aYm)
open aZD (Core aT)
open private bfq co2 biQ from ProximityPrize.SubmissionLower.D9
open private bid from ProximityPrize.SubmissionLower.CN
def width (s :aU) (h q j t:ℕ) :ℤ :=
 (s.m*A:ℕ)+(j:ℤ)-(131071-(h:ℤ))*q - 2*(h:ℤ)*t
private theorem biL (s :aU) (h q j t:ℕ) (hh:h≤131071) :
   (↑(s.m*A+j-q*(131071-h)-2*h*t:ℕ) :ℤ)=max 0 (width s h q j t) := by
 rw [Nat.sub_sub]
 have hd: (↑(131071-h:ℕ) :ℤ)=131071 - h:=nq hh
 have he : (↑(s.m*A+j:ℕ) :ℤ)-(↑(q*(131071-h)+2*h*t:ℕ) :ℤ) =
     width s h q j t:= by
   simp only [width,c9,lI,lV,hd]
   ring
 generalize s.m*A+j=x at *
 generalize q*(131071-h)+2*h*t=y at *
 by_cases hxy :y≤x
 · rw [Int.ofNat_sub hxy,he,max_eq_right (by omega)]
 · have hz :x-y=0:=Nat.sub_eq_zero_of_le (by omega)
   rw [hz,Int.ofNat_zero,max_eq_left (by omega)]
theorem gain_eq (s :aU) (h E v :ℕ) (hh:h≤131071) :
  (ZN h s E v :ℤ)=O3 s E v (fun q j t=>max 0 (width s h q j t)) := by
 simp only [ZN,ku,O3,Nat.cast_sum,c9,lI,biL _ _ _ _ _ hh]
abbrev stop (s :aU) (E v :ℕ) :=s.J+Tb s E v
def column (s :aU) (pin t:ℕ) :ℕ :=
 aOy (2*pin*t) (131071-pin) (s.m*A+s.J/2) (s.B+1)
def masked (s :aU) (pin h q j t:ℕ) :ℤ :=
 if q<column s pin t then width s h q j t else 0
theorem column_le (s :aU) (pin t:ℕ) :column s pin t≤ s.B+1 := by
 simp only [column,aOy]
 split_ifs <;> omega
private def core (s :aU) (h E v d k :ℕ) :Core :=
 let D:ℤ:=131071-(h:ℤ)
 let p:ℤ:=(E-1 :ℕ)
 let w:ℤ:=(E*d:ℕ)
 ⟨k,E*d,E-1,bg5 s v d (Tb s E v),aJq s v d,
   ⟨(k :ℤ)-w,-p⟩,⟨2*(s.m*A:ℕ)-D*(w+k-1),-2-D*p⟩,
   2-4*(h:ℤ)-D⟩
private theorem core_term (s :aU) (h E v d k t a :ℕ)
   (he :0<E) (hat :a≤t) (hk :t-a+E*(a+d)≤k) :
   (core s h E v d k).term a t =
     2*(∑ q∈Ico (t-a+E*(a+d)) k,width s h q (t-a) t) := by
 let l:=t-a+E*(a+d)
 let D:ℤ:=131071-(h:ℤ)
 have hk' : l≤k :=hk
 have hl: (l:ℤ)=(t:ℤ)+(E*d:ℕ)+((E-1 :ℕ) :ℤ)*a := by
   rw [show l=aYm E d t+(E-1)*a from biQ E d t a he hat]
   push_cast [aYm]
   ring
 change _=2*(∑ q∈Ico l k,width s h q (t-a) t)
 rw [sum_Ico_eq_sum_range]
 have hw (i:ℕ) :width s h (l+i) (t-a) t=width s h l (t-a) t+(-D)*(i:ℤ) := by
   simp only [width,D,c9]
   ring
 simp_rw [hw]
 rw [bid]
 simp only [core,Core.term,aT.at,width,D,nq hat,nq hk']
 rw [hl]
 ring
private theorem order_pos (s :aU) (E v :ℕ) :0<Tb s E v := by
 unfold Tb
 split
 · exact lz _
 · exact lt_min (lz _) (lz _)
private def diag (s :aU) (h E v d t k :ℕ) :ℤ :=
 ∑ a∈Ico (t-s.J) (min t (Tb s E v-1)+1),
   (slots s.U ((a+d)*v) :ℤ) * ∑ q∈Ico (t-a+E*(a+d)) k,width s h q (t-a) t
private theorem diag_eq (s :aU) (h E v d k t:ℕ) (he :0<E) :
    let C:=core s h E v d k
    (∑ a∈range C.cap,
      if a≤t∧t<a+(s.J+1)∧t+(C.offset+C.step*a)<C.column
      then C.seed.eval a*C.term a t else 0)=4*diag s h E v d t k := by
  dsimp only
  let C:=core s h E v d k
  let S:=(range C.cap).filter (fun a=>a≤t∧t<a+(s.J+1)∧t+(C.offset+C.step*a)<C.column)
  let T:=Ico (t-s.J) (min t (Tb s E v-1)+1)
  have hn:=order_pos s E v
  have hm (a :ℕ) :a∈S↔a∈T∧(a+d)*v≤ s.U∧t-a+E*(a+d)<k := by
    simp only [S,T,C,core,mem_filter,mem_range,mem_Ico,bfq,Nat.lt_succ_iff,le_min_iff]
    constructor
    · rintro ⟨⟨ha,hv⟩,ht,hj,hk⟩
      rw [biQ E d t a he ht]
      exact ⟨⟨by omega,ht,by omega⟩,hv,by simpa [aYm,lJ] using hk⟩
    · rintro ⟨⟨hj,ht,ha⟩,hv,hk⟩
      rw [biQ E d t a he ht] at hk
      exact ⟨⟨by omega,hv⟩,ht,by omega,by simpa [aYm,lJ] using hk⟩
  rw [← sum_filter,diag,mul_sum]
  change (∑ a∈S,C.seed.eval a*C.term a t)= _
  calc
    _ = ∑ a∈S,4*((slots s.U ((a+d)*v) :ℤ) *
          ∑ q∈Ico (t-a+E*(a+d)) k,width s h q (t-a) t) := by
      apply sum_congr rfl
      intro a ha
      obtain ⟨ht,hv,hk⟩:=(hm a).mp ha
      have hat :a≤t:=(le_min_iff.mp (nI (mem_Ico.mp ht).2)).1
      change (aJq s v d).eval a*(core s h E v d k).term a t= _
      rw [co2 _ _ _ _ hv,core_term s h E v d k t a he hat hk.le]
      ring
    _ = _:= by
      apply sum_subset (fun a ha=>((hm a).mp ha).1)
      intro a ha hn
      by_cases hv : (a+d)*v≤ s.U
      · have hz :k≤t-a+E*(a+d) :=
          Nat.le_of_not_gt (fun hk=>hn ((hm a).mpr ⟨ha,hv,hk⟩))
        simp [Ico_eq_empty_of_le hz]
      · simp [slots,hv]
private def group (s :aU) (h E v d l r k :ℕ) :ℤ :=
 let C:=core s h E v d k
 (C.vo r 0 - C.vo r (s.J+1))-(C.vo l 0 - C.vo l (s.J+1))
private theorem group_eq (s :aU) (h E v d l r k :ℕ) (he :0<E) (hl:l≤ r) :
  group s h E v d l r k=1440*(∑ t∈Ico l r,diag s h E v d t k) := by
 rw [group,Core.azU,Core.azU,← mul_sub,← sum_Ico_eq_sub _ hl]
 simp_rw [diag_eq s h E v d k _ he]
 rw [← mul_sum]
 ring
open bjU (scan)
open Y2 (aIy)
open private coM from ProximityPrize.SubmissionLower.B4
def boundary (s :aU) (pin n i:ℕ) :ℕ :=
 if i=0 then 0
 else aOy ((131071-pin)*(s.B+1-i)) (2*pin) (s.m*A+s.J/2) n
def reaches (s :aU) (pin n:ℕ) :Bool :=
 (((131071-pin)*(s.B+1-24))+2*pin*(n-1)).blt (s.m*A+s.J/2)
theorem boundary_full (s :aU) (pin n:ℕ) (h:reaches s pin n=true) :
   boundary s pin n 24=n:= by
 let B:=(131071-pin)*(s.B+1-24)
 let x :=aOy B (2*pin) (s.m*A+s.J/2) n
 change x=n
 have hpos :B+2*pin*(n-1)<s.m*A+s.J/2 :=Nat.blt_eq.mp h
 apply Nat.le_antisymm
 · by_contra! hn
   exact (mD _) ((aIy _ _ _ _ _).mp hn).1
 · by_contra! hn
   have hm:=Nat.mul_le_mul_left (2*pin) (show x≤n-1 by omega)
   have hx :B+2*pin*x<s.m*A+s.J/2 := by omega
   exact (mD _) ((aIy B (2*pin) (s.m*A+s.J/2) n x).mpr ⟨hn,hx⟩)
private theorem lt_boundary (s :aU) (pin n i t:ℕ) (hi:0< i) (hB:i≤ s.B+1) :
  t<boundary s pin n i↔t<n∧s.B+1-i<column s pin t:= by
 have hb:s.B+1-i<s.B+1 := by omega
 simp only [boundary,ite_eq_right (Nat.ne_of_gt hi),column,aIy,hb,true_and,add_comm]
private theorem dz1 (s :aU) (pin n i:ℕ) (hi:i+1≤ s.B+1) :
   boundary s pin n i≤boundary s pin n (i+1) := by
 by_cases hz :i=0
 · simp [hz,boundary]
 by_contra! hn
 let t:=boundary s pin n (i+1)
 obtain ⟨ht,hk⟩:=(lt_boundary s pin n i t (by omega) (by omega)).mp hn
 exact (mD _) ((lt_boundary s pin n (i+1) t (by omega) hi).mpr ⟨ht,by omega⟩)
private theorem ekI (s :aU) (pin n i t:ℕ) (hi:i+1≤ s.B+1)
  (ht:t∈Ico (boundary s pin n i) (boundary s pin n (i+1))) :
  column s pin t=s.B+1-i:= by
 obtain ⟨hl,hr⟩:=mem_Ico.mp ht
 obtain ⟨htn,hq⟩:=(lt_boundary s pin n (i+1) t (by omega) hi).mp hr
 have hu:column s pin t≤ s.B+1-i:= by
  by_contra! hh
  by_cases hz :i=0
  · subst i
    exact (Nat.not_lt_of_ge (column_le _ _ _)) (by simpa using hh)
  · exact (not_lt_of_ge hl) ((lt_boundary s pin n i t (by omega) (by omega)).mpr ⟨htn,hh⟩)
 omega
private theorem gwO (s :aU) (pin n count:ℕ) (hc:count≤ s.B+1) (f :ℕ→ℤ) :
   (∑ i∈range count,∑ t∈Ico (boundary s pin n i) (boundary s pin n (i+1)),f t) =
     ∑ t∈range (boundary s pin n count),f t:= by
 induction count with
 | zero=>simp [boundary]
 | succ i ih =>
   rw [sum_range_succ,ih (by omega :i≤ s.B+1),sum_range_add_sum_Ico f (dz1 s pin n i hc)]
private theorem masked_diag (s :aU) (pin h E v d t:ℕ) :
    (∑ a∈Ico (t-s.J) (min t (Tb s E v-1)+1),
      (slots s.U ((a+d)*v) :ℤ) *
        ∑ q∈Ico (t-a+E*(a+d)) (s.B+1),masked s pin h q (t-a) t) =
      diag s h E v d t (column s pin t) := by
  unfold diag
  apply sum_congr rfl
  intro a _
  congr 1
  simp only [masked]
  rw [← sum_filter]
  congr 1
  ext q
  simp only [mem_Ico,mem_filter]
  have hc:=column_le s pin t
  omega
private def groupAt (s :aU) (pin h E v d i:ℕ) :ℤ :=
 let l:=boundary s pin (stop s E v) i
 let r :=boundary s pin (stop s E v) (i+1)
 if l< r then group s h E v d l r (s.B+1-i) else 0
private theorem groupAt_eq (s :aU) (pin h E v d i:ℕ) (he :0<E) (hi:i+1≤ s.B+1) :
    groupAt s pin h E v d i=1440 *
      ∑ t∈Ico (boundary s pin (stop s E v) i) (boundary s pin (stop s E v) (i+1)),
        diag s h E v d t (column s pin t) := by
  unfold groupAt
  dsimp only
  split
  · rw [group_eq _ _ _ _ _ _ _ _ he (dz1 s pin (stop s E v) i hi)]
    congr 1
    exact sum_congr rfl (fun t ht=> by rw [ekI s pin (stop s E v) i t hi ht])
  · rw [Ico_eq_empty_of_le (by omega),sum_empty,mul_zero]
private theorem sum_groupAt (s :aU) (pin h E v d count:ℕ) (he :0<E)
  (hc:count≤ s.B+1) (hn:boundary s pin (stop s E v) count=stop s E v) :
  (∑ i∈range count,groupAt s pin h E v d i) =
    1440*phase s E v d (masked s pin h) := by
 conv_rhs =>
  rw [phase]
  simp only [masked_diag]
  change 1440*(∑ t∈range (stop s E v),diag s h E v d t (column s pin t))
  rw [← hn,← gwO s pin (stop s E v) count hc,mul_sum]
 exact sum_congr rfl (fun i hi=>groupAt_eq s pin h E v d i he ((mem_range.mp hi).trans_le hc))
def block (s :aU) (pin h E v i:ℕ) :ℤ :=
 groupAt s pin h E v 0 i - groupAt s pin h E v 1 i
def scanBlock (s :aU) (pin h E v count:ℕ) :ℤ :=
 (scan (fun i=>⟨true,block s pin h E v i,0⟩) 0 count).base
theorem scanBlock_eq (s :aU) (pin h E v count:ℕ) (he :0<E)
  (hc:count≤ s.B+1) (hn:boundary s pin (stop s E v) count=stop s E v) :
  scanBlock s pin h E v count=1440*P5_7_6.O3 s E v (masked s pin h) := by
 have hs :=coM (fun i=>⟨true,block s pin h E v i,0⟩) 0 count false
 simp only [Bool.false_eq_true,ite_false,Nat.zero_add] at hs
 rw [scanBlock,hs,P5_7_6.gain_phases _ _ _ _ he]
 simp only [block,sum_sub_distrib]
 rw [sum_groupAt s pin h E v 0 count he hc hn,sum_groupAt s pin h E v 1 count he hc hn,mul_sub]
end qMHqmcc
end
section
set_option autoImplicit true
namespace qMHqmcc
open P5_7_2
open P5_7 (Bank)
def nY (t:Bank) (pin E v h:ℕ) :ℤ :=
 scanBlock t.shape pin h E v 24 - 1440*(j3 h t:ℤ)
def signs (t:Bank) (pin E v :ℕ) :Bool :=
 let a :=nY t pin E v pin
 let b:=nY t pin E v (pin+1)
 decide (0<a) && decide (a≤b)
structure cL (b:fO) (x :Test b) :Prop where
 reach:reaches (Lc b x).shape (jX b).lo
  (stop (Lc b x).shape (cy x) (apo x))=true
 sign:signs (Lc b x) (jX b).lo (cy x) (apo x)=true
def test (b:fO) :ℕ→Test b
 | 0=>none
 | i+1=>if hi:i<(row b).bDZ then some ⟨i,hi⟩ else none
def GG (b:fO) (start:ℕ) :ℕ→Prop
 | 0=>True
 | n+1=>cL b (test b (start+n))∧GG b start n
end qMHqmcc
end
section
set_option autoImplicit true
namespace qMHqmcc

open P5_7_2
open P5_7 (Bank)
open P5_7_6 (O3 gain_le gain_add)
open private c8O from ProximityPrize.SubmissionLower.D9
private def x5 (b:Bank) (pin E v h:ℕ) :ℤ :=
 O3 b.shape E v (masked b.shape pin h)-(j3 h b:ℤ)
private theorem scaled_eq (b:Bank) (pin E v h:ℕ) (he :0<E) (hc:24≤b.shape.B+1)
  (hn:boundary b.shape pin (stop b.shape E v) 24=stop b.shape E v) :
  nY b pin E v h=1440*x5 b pin E v h:= by
 rw [nY,scanBlock_eq _ _ _ _ _ _ he hc hn,x5,mul_sub]
private theorem masked_step (s :aU) (pin n q j t:ℕ) :
   masked s pin (n+1) q j t+masked s pin (n+1) q j t =
    masked s pin n q j t+masked s pin (n+2) q j t:= by
 by_cases ht:q<column s pin t
 · have hw (h:ℕ) :masked s pin h q j t=width s h q j t:=ite_eq_left ht
   rw [hw (n+1),hw n,hw (n+2)]
   simp only [width,c9,Nat.cast_one,lV]
   ring
 · have hz (h:ℕ) :masked s pin h q j t=0:=ite_eq_right ht
   rw [hz (n+1),hz n,hz (n+2)]
private theorem surplus_step (b:Bank) (pin E v n:ℕ) :
    x5 b pin E v (n+1) + x5 b pin E v (n+1) =
      x5 b pin E v n + x5 b pin E v (n+2) := by
  have hg :
      O3 b.shape E v (masked b.shape pin (n+1)) +
        O3 b.shape E v (masked b.shape pin (n+1)) =
      O3 b.shape E v (masked b.shape pin n) +
        O3 b.shape E v (masked b.shape pin (n+2)) := by
    rw [← gain_add b.shape E v _ (masked b.shape pin (n+1)),
      ← gain_add b.shape E v _ (masked b.shape pin (n+2))]
    exact congrArg (O3 b.shape E v) (funext fun q=>funext fun j=>funext fun t =>
      masked_step b.shape pin n q j t)
  have hd: (j3 (n+1) b:ℤ)+(j3 (n+1) b:ℤ) =
      (j3 n b:ℤ)+(j3 (n+2) b:ℤ) := by
    simp only [j3,c9,lI,Nat.cast_one,lV]
    ring
  unfold x5
  omega
private theorem strict {b:Bank} {pin E v h:ℕ} (hl:pin≤h) (hh:h≤131071)
   (he :0<E) (hc:24≤b.shape.B+1)
   (hn:boundary b.shape pin (stop b.shape E v) 24=stop b.shape E v)
   (hp:0<nY b pin E v pin) (hd:nY b pin E v pin≤nY b pin E v (pin+1)) :
   j3 h b<ZN h b.shape E v := by
 rw [scaled_eq _ _ _ _ _ he hc hn] at hp
 rw [scaled_eq _ _ _ _ _ he hc hn,scaled_eq _ _ _ _ _ he hc hn] at hd
 have hr :=c8O (f :=x5 b pin E v)
   (fun n _=>(surplus_step b pin E v n).le) hl (by omega)
 have hpos :0<x5 b pin E v h:= by omega
 have hg:=gain_le b.shape E v (f :=masked b.shape pin h)
   (g:= fun q j t=>max 0 (width b.shape h q j t)) (by
     intro q j t
     unfold masked
     split
     · exact le_max_right _ _
     · exact le_max_left _ _)
 rw [← gain_eq b.shape h E v hh] at hg
 unfold x5 at hpos
 omega
theorem receipt {b:fO} {x :Test b} (pin:ℕ) (hpin: (jX b).lo=pin)
  (hn:reaches (Lc b x).shape pin (stop (Lc b x).shape (cy x) (apo x))=true)
  (hs :signs (Lc b x) pin (cy x) (apo x)=true) :cL b x := by
 subst pin
 exact ⟨hn,hs⟩
private theorem band_width (b:fO) :24≤(row b).shape.B+1 := by
 fin_cases b <;> decide
theorem checked {b:fO} {x :Test b} {h:ℕ}
  (hl: (jX b).lo≤h) (hh:h≤131071) (hr :cL b x) :
  j3 h (Lc b x)<ZN h (Lc b x).shape (cy x) (apo x) := by
 have he :0<cy x := by cases x <;> exact lz _
 have hB: (Lc b x).shape.B=(row b).shape.B:= by cases x <;> rfl
 have hc:24≤(Lc b x).shape.B+1 := by
  rw [hB]
  exact band_width b
 obtain ⟨hn,hs⟩:=hr
 unfold signs at hs
 obtain ⟨hp,hd⟩:=Bool.and_eq_true_iff.mp hs
 exact strict hl hh he hc (boundary_full _ _ _ hn)
  (nX hp) (nX hd)
theorem appendGrades {b:fO} {start n m:ℕ}
   (hn:GG b start n) (hm:GG b (start+n) m) :GG b start (n+m) := by
 induction m with
 | zero=>exact hn
 | succ m ih =>
   have ht:cL b (test b ((start+n)+m)) :=hm.1
   rw [lJ] at ht
   rw [Nat.add_succ]
   exact ⟨ht,ih hm.2⟩
private theorem egi (b:fO) (start:ℕ) {n:ℕ}
   (hs :GG b start n) {j:ℕ} (hj:j<n) :cL b (test b (start+j)) := by
 induction n with
 | zero=>omega
 | succ n ih =>
   rcases Nat.lt_or_eq_of_le (nI hj) with hlt | rfl
   · exact ih hs.2 hlt
   · exact hs.1
theorem receipts (b:fO) (hg:GG b 0 ((row b).bDZ+1)) (x :Test b) :cL b x := by
 cases x with
 | none=>exact egi b 0 hg (j:=0) (Nat.succ_pos _)
 | some i =>
   rcases i with ⟨j,hj⟩
   have ht:=egi b 0 hg (Nat.succ_lt_succ hj)
   rw [Nat.zero_add] at ht
   simpa only [test,hj,dite_true] using ht
end qMHqmcc
end

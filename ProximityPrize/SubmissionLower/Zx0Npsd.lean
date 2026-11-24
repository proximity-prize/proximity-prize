import ProximityPrize.SubmissionLower.D9
import ProximityPrize.SubmissionLower.ZEXyWMe
import ProximityPrize.SubmissionLower.AY
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.AS
import ProximityPrize.SubmissionLower.ZITfVad
import ProximityPrize.SubmissionLower.ZZBDV9b
import ProximityPrize.SubmissionLower.ZedfuCc
import ProximityPrize.SubmissionLower.ZV1UoEe
set_option Elab.async false
section
open _root_ renaming Finset.range→cy,Finset.sum_congr→lz,Finset.sum_range_succ→nI,Finset.sum_sub_distrib→lJ,Int.natCast_nonneg→ oy,Nat.cast_add→nq,Nat.cast_mul→mD,Nat.cast_sub→ oq,Nat.le_div_iff_mul_le→ ov,Nat.lt_succ_iff→ oj,Nat.sub_add_cancel→ oz,Nat.succ_pos→lV,P5_7.midAgreement→lI,cu.Shape→aU,cu.slots→c9,ite_eq_left→n5,ite_eq_right→nX,mul_le_mul_of_nonneg_left→ ox
section
set_option autoImplicit true
namespace qqf9uAa
open Finset
open cu (slots)
open Dt (Bank jJ)
open Y2 (aOy)

open P5_7_3 (fO j3 terminal)
def Xa (s :aU) (lo t:ℕ) :ℕ :=
 aOy (2*lo*t) (131071-lo) (s.m*lI) (s.B+1)
def width (s :aU) (h:ℤ) (q j t:ℕ) :ℤ :=
 (s.m*lI:ℕ)+(j:ℤ)-(131071-h)*q - 2*h*t
def Bp (s :aU) (lo:ℕ) (h:ℤ) (q j t:ℕ) :ℤ :=
 if q<Xa s lo t then width s h q j t else 0
def weight (s :aU) (v g a :ℕ) :ℕ :=
 c9 s.U (a*v) - if a<g then c9 s.U ((a+1)*v) else 0
def total (s :aU) (E v :ℕ) (w:ℕ→ℕ→ℕ→ℤ) :ℤ :=
  ∑ q∈cy (s.B+1),∑ j∈cy (min q s.J+1),∑ a∈cy ((q-j)/E+1),
    (weight s v ((q-j)/E) a :ℤ)*w q j (j+a)
def Signs (t:Bank) (h E v :ℕ) :Prop :=
  let left:=total t.shape E v (Bp t.shape h h)
  (j3 h t:ℤ)<left ∧
    left+2*((t.shape.U:ℤ)+1)*t.poleMoment≤total t.shape E v (Bp t.shape h ((h:ℤ)+1))
def GradeSigns (t:Bank) (h:ℕ) :ℕ→List jJ→Prop
 | _,[]=>True
 | e,g :: gs=>Signs {t with shape := {t.shape with U:=g.slots}} h e (g.seedCap+1) ∧
     GradeSigns t h (e+1) gs
def BandSigns (b:fO) :Prop :=
  Signs (terminal b) b.jX.lo (b.schedule.gw.length+1) 0 ∧
    GradeSigns (terminal b) b.jX.lo 1 b.schedule.gw
def RangeSigns (lo hi:ℕ) :Prop :=
 ∀ b:fO,lo≤b.jX.lo→b.jX.lo<hi→BandSigns b
end qqf9uAa
end
section
set_option autoImplicit true
namespace qqf9uAa
open Finset
open cu (ku)

open P5_7_3 (ZN j3)
open Dt (Bank)
open Y2 (Tb)
open private deJ crN diagonal from ProximityPrize.SubmissionLower.D9
theorem total_le (s :aU) (lo h E v :ℕ) (hh:h≤131071) :
    total s E v (Bp s lo h)≤(ZN h s E v :ℤ) := by
  simp only [total,ZN,ku,Nat.cast_sum]
  apply sum_le_sum; intro q _
  apply sum_le_sum; intro j _
  let g:=(q-j)/E
  let raw:= fun a=>s.m*lI+j-q*(131071-h)-2*h*(j+a)
  have raw_ge (a :ℕ) :Bp s lo h q j (j+a)≤(raw a :ℤ) := by
    unfold Bp
    split
    · have hx :width s h q j (j+a)=((s.m*lI+j:ℕ) :ℤ) -
          (↑(q*(131071-h)+2*h*(j+a) :ℕ) :ℤ) := by
        unfold width
        push_cast [oq hh]
        ring
      rw [hx]
      dsimp only [raw]
      rw [Nat.sub_sub]
      omega
    · exact oy _
  calc
    _ ≤ ∑ a∈cy (g+1),(weight s v g a :ℤ)*(raw a :ℤ) :=
      sum_le_sum fun a _=>ox (raw_ge a) (oy _)
    _ = _:= by
      rw [nI,nq,Nat.cast_sum,mD]
      congr 1
      · exact lz rfl (fun a ha=> by simp only [weight,n5 (mem_range.mp ha),mD,raw,g])
      · simp only [weight,lt_irrefl,ite_false,Nat.sub_zero,raw,g]
private theorem total_affine (s :aU) (lo E v :ℕ) (d:ℤ) :
    total s E v (Bp s lo ((lo:ℤ)+d)) =
      total s E v (Bp s lo lo)+d*(total s E v (Bp s lo ((lo:ℤ)+1)) -
        total s E v (Bp s lo lo)) := by
  simp only [total,← lJ,mul_sum,← sum_add_distrib]
  apply lz rfl; intro q _
  apply lz rfl; intro j _
  apply lz rfl; intro a _
  unfold Bp
  split <;> (try simp only [width]) <;> ring
theorem strict_of_support {t:Bank} {lo h E v :ℕ} (hl:lo≤h) (hh:h≤131071)
   (hp: (j3 lo t:ℤ)<total t.shape E v (Bp t.shape lo lo))
   (hs :total t.shape E v (Bp t.shape lo lo)+(2 :ℤ)*(t.shape.U+1)*t.poleMoment ≤
     total t.shape E v (Bp t.shape lo ((lo:ℤ)+1))) :
   j3 h t<ZN h t.shape E v := by
 let d:ℤ:=(h:ℤ)-lo
 have hd:0≤d:= by dsimp [d]; omega
 have he : (h:ℤ)=(lo:ℤ)+d:= by dsimp [d]; ring
 have ha :=total_affine t.shape lo E v d
 rw [← he] at ha
 have hb: (j3 h t:ℤ)=(j3 lo t:ℤ)+d*(2*(t.shape.U+1)*t.poleMoment) := by
   simp only [j3,nq,mD,Nat.cast_one,Nat.cast_ofNat]
   dsimp [d]
   ring
 have hm:=ox (show (2 :ℤ)*(t.shape.U+1)*t.poleMoment ≤
   total t.shape E v (Bp t.shape lo ((lo:ℤ)+1)) - total t.shape E v (Bp t.shape lo lo)
   by omega) hd
 have hg:=total_le t.shape lo h E v hh
 omega
def phase (s :aU) (E v d:ℕ) (w:ℕ→ℕ→ℕ→ℤ) :ℤ :=
  ∑ t∈cy (s.J+Tb s E v),∑ a∈Ico (t-s.J) (min t (Tb s E v-1)+1),
    (c9 s.U ((a+d)*v) :ℤ) * ∑ q∈Ico (t-a+E*(a+d)) (s.B+1),w q (t-a) t
private theorem eNa (s :aU) (E v q j:ℕ) (he :0<E)
    (hq:q≤ s.B) (hj:j≤q) (w:ℕ→ℤ) :
    (∑ a∈cy ((q-j)/E+1),(weight s v ((q-j)/E) a :ℤ)*w a) =
      (∑ a∈cy (Tb s E v),if j+E*(a+0)≤q then (c9 s.U ((a+0)*v) :ℤ)*w a else 0) -
      (∑ a∈cy (Tb s E v),if j+E*(a+1)≤q then (c9 s.U ((a+1)*v) :ℤ)*w a else 0) := by
  let g:=(q-j)/E
  let f := fun d a=>(c9 s.U ((a+d)*v) :ℤ)*w a
  have step (a :ℕ) :c9 s.U ((a+1)*v)≤ c9 s.U (a*v) :=
    deJ _ (Nat.mul_le_mul_right v (by omega))
  have hdiff :
      (∑ a∈cy (g+1),(weight s v g a :ℤ)*w a) =
        (∑ a∈cy (g+1),f 0 a) - ∑ a∈cy g,f 1 a := by
    rw [nI,nI (f 0),add_sub_right_comm,← lJ]
    congr 1
    · apply lz rfl
      intro a ha
      simp only [f,weight,n5 (mem_range.mp ha),Nat.add_zero,Int.ofNat_sub (step a),sub_mul]
    · simp [f,weight]
  rw [hdiff]
  have hz (d a :ℕ) (ha :Tb s E v≤a) (hg:a+d≤g) :f d a=0:= by
    have hcap:g≤ s.B/E :=Nat.div_le_div_right (by omega)
    unfold Tb at ha
    split at ha
    · omega
    · rename_i hv
      have hlarge :s.U/v<a+d:= by omega
      have hout:s.U<(a+d)*v := by
        by_contra! hm
        exact (Nat.not_le_of_lt hlarge) ((ov (Nat.pos_of_ne_zero hv)).2 hm)
      simp [f,c9,Nat.not_le_of_lt hout]
  have hdiv (a d:ℕ) :j+E*(a+d)≤q↔a+d≤g:= by
    rw [ov he,Nat.mul_comm (a+d) E]
    omega
  rw [crN (g+1) _ (fun a ha hb=>hz 0 a ha (by omega)),
    crN g _ (fun a ha hb=>hz 1 a ha (by omega))]
  have hz₀ (a :ℕ) :j+E*a≤q↔a≤g:= by simpa using hdiv a 0
  simp only [hdiv,hz₀,Nat.add_zero,oj,Nat.add_one_le_iff,f]
private def bty (s :aU) (E v d:ℕ) (w:ℕ→ℕ→ℕ→ℤ) :ℤ :=
 ∑ q∈cy (s.B+1),∑ j∈cy (s.J+1),∑ a∈cy (Tb s E v),
   if j+E*(a+d)≤q then (c9 s.U ((a+d)*v) :ℤ)*w q j (j+a) else 0
private theorem c30 (s :aU) (E v d q:ℕ) (w:ℕ→ℕ→ℕ→ℤ) :
  (∑ j∈cy (min q s.J+1),∑ a∈cy (Tb s E v),
    if j+E*(a+d)≤q then (c9 s.U ((a+d)*v) :ℤ)*w q j (j+a) else 0) =
  ∑ j∈cy (s.J+1),∑ a∈cy (Tb s E v),
    if j+E*(a+d)≤q then (c9 s.U ((a+d)*v) :ℤ)*w q j (j+a) else 0:= by
 apply sum_subset (range_mono (Nat.succ_le_succ (min_le_right _ _)))
 intro j hj hn
 simp only [mem_range,oj,le_min_iff] at hj hn
 exact sum_eq_zero fun a _=>nX (by omega)
private theorem c3Z (s :aU) (E v d:ℕ) (w:ℕ→ℕ→ℕ→ℤ) :
   bty s E v d w=phase s E v d w:= by
 have hR:Tb s E v-1+1=Tb s E v := by
   apply oz
   unfold Tb
   split
   · exact lV _
   · exact le_min (lV _) (lV _)
 unfold bty phase
 rw [sum_comm]
 conv_lhs =>
   enter [2,j]
   rw [sum_comm]
 conv_lhs =>
   rw [← hR]
   rw [diagonal]
 rw [Nat.add_assoc,hR]
 apply lz rfl; intro t _
 apply lz rfl; intro a ha
 have hta :t-a+a=t:=oz (by have :=(mem_Ico.mp ha).2; omega)
 rw [mul_sum,← sum_filter]
 have hf : (cy (s.B+1)).filter (fun q=>t-a+E*(a+d)≤q) =
     Ico (t-a+E*(a+d)) (s.B+1) := by
   ext q
   simp only [mem_range,mem_filter,mem_Ico]
   tauto
 rw [hf,hta]
theorem total_eq_phases (s :aU) (E v :ℕ) (w:ℕ→ℕ→ℕ→ℤ) (he :0<E) :
  total s E v w=phase s E v 0 w - phase s E v 1 w:= by
 rw [← c3Z,← c3Z]
 unfold total bty
 rw [← lJ]
 apply lz rfl; intro q hq
 rw [← c30 s E v 0 q,← c30 s E v 1 q,← lJ]
 apply lz rfl; intro j hj
 rw [mem_range,oj] at hq hj
 exact eNa _ _ _ _ _ he hq (hj.trans (min_le_left _ _)) _
end qqf9uAa
end
section
set_option autoImplicit true
namespace qqf9uAa
open Finset


open Y2 (Tb aOy aIy bg5 aJq aYm)
open aZD (Core)
open private bfq co2 biQ from ProximityPrize.SubmissionLower.D9
open private bid from ProximityPrize.SubmissionLower.CN
private def bb1 (s :aU) (h:ℤ) (E v d k :ℕ) :Core :=
 let D:ℤ:=131071-h
 let p:ℤ:=(E-1 :ℕ)
 let w:ℤ:=(E*d:ℕ)
 ⟨k,E*d,E-1,bg5 s v d (Tb s E v),aJq s v d,
   ⟨(k :ℤ)-w,-p⟩,⟨2*(s.m*lI:ℕ)-D*(w+k-1),-2-D*p⟩,
   2-4*h-D⟩
private theorem cutSum (s :aU) (lo t a l:ℕ) (h:ℤ) :
   (∑ q∈Ico l (s.B+1),Bp s lo h q (t-a) t) =
     ∑ q∈Ico l (Xa s lo t),width s h q (t-a) t:= by
 have hc:Xa s lo t≤ s.B+1 := by
   by_contra! he
   exact (lt_irrefl _ ((aIy _ _ _ _ _).mp he).1)
 unfold Bp
 rw [← sum_filter]
 have hf : (Ico l (s.B+1)).filter (fun q=>q<Xa s lo t)=Ico l (Xa s lo t) := by
   ext q
   simp only [mem_filter,mem_Ico]
   omega
 rw [hf]
private theorem coreTerm (s :aU) (h:ℤ) (E v d t a k :ℕ) (he :0<E)
   (ha :a≤t) (hl:t-a+E*(a+d)≤k) :
   2*(∑ q∈Ico (t-a+E*(a+d)) k,width s h q (t-a) t) =
     (bb1 s h E v d k).term a t:= by
 let l:=t-a+E*(a+d)
 have hle :l≤k :=hl
 have hx :=biQ E d t a he ha
 change 2*(∑ q∈Ico l k,width s h q (t-a) t)= _
 rw [sum_Ico_eq_sum_range]
 have hf (i:ℕ) :width s h (l+i) (t-a) t =
     width s h l (t-a) t+(h-131071)*(i:ℤ) := by
   simp only [width,nq]
   ring
 simp_rw [hf]
 rw [bid]
 simp only [oq hle,width,bb1,Core.term,aZD.aT.at,oq ha]
 change l=aYm E d t+(E-1)*a at hx
 rw [hx]
 simp only [aYm,nq,mD]
 ring
private def diag (s :aU) (lo:ℕ) (h:ℤ) (E v d t:ℕ) :ℤ :=
 ∑ a∈Ico (t-s.J) (min t (Tb s E v-1)+1),
   (c9 s.U ((a+d)*v) :ℤ) *
     ∑ q∈Ico (t-a+E*(a+d)) (s.B+1),Bp s lo h q (t-a) t
private theorem diag_eq (s :aU) (lo:ℕ) (h:ℤ) (E v d t k :ℕ)
    (he :0<E) (hk :Xa s lo t=k) :
    4*diag s lo h E v d t =
      ∑ a∈cy (bb1 s h E v d k).cap,
        if a≤t∧t<a+(s.J+1)∧t+((bb1 s h E v d k).offset+
          (bb1 s h E v d k).step*a)<k
        then (bb1 s h E v d k).seed.eval a*(bb1 s h E v d k).term a t else 0:= by
  let C:=bb1 s h E v d k
  let R:=min t (Tb s E v-1)+1
  let l:= fun a=>t-a+E*(a+d)
  let f := fun a=>(c9 s.U ((a+d)*v) :ℤ) * ∑ q∈Ico (l a) k,width s h q (t-a) t
  let p:= fun a=>a≤t∧t<a+(s.J+1)∧t+(C.offset+C.step*a)<k
  have hend:0<Tb s E v := by
    unfold Tb
    split
    · exact lV _
    · exact lt_min (lV _) (lV _)
  have hdiag:diag s lo h E v d t = ∑ a∈Ico (t-s.J) R,f a :=
    lz rfl fun a _=> by simp only [f,l,cutSum,hk]
  have hmem (a :ℕ) :
      a∈(cy C.cap).filter p↔a∈Ico (t-s.J) R∧(a+d)*v≤ s.U∧l a<k := by
    simp only [mem_filter,mem_range,C,bb1,bfq,p,mem_Ico,R]
    by_cases hat :a≤t
    · rw [show l a=t+(E*d+(E-1)*a) by
        dsimp [l]; rw [biQ E d t a he hat,aYm,Nat.add_assoc]]
      omega
    · omega
  change _ = ∑ a∈cy C.cap,if p a then C.seed.eval a*C.term a t else 0
  rw [hdiag,← sum_filter,mul_sum]
  symm
  calc
    _ = ∑ a∈(cy C.cap).filter p,4*f a := by
      apply lz rfl; intro a ha
      obtain ⟨ha,hv,hl⟩:=(hmem a).mp ha
      have hat :a≤t:=(Nat.le_of_lt_succ (mem_Ico.mp ha).2).trans (min_le_left _ _)
      change (aJq s v d).eval a*_ = _
      rw [co2 s v d a hv,← coreTerm s h E v d t a k he hat hl.le]
      dsimp only [f,l]
      ring
    _ = _:= by
      apply sum_subset (fun a ha=>((hmem a).mp ha).1)
      intro a ha hn
      by_cases hv : (a+d)*v≤ s.U
      · have hk' : k≤l a := by
          by_contra! ht
          exact hn ((hmem a).mpr ⟨ha,hv,ht⟩)
        simp [f,Ico_eq_empty_of_le hk']
      · simp [f,c9,hv]
def boundary (s :aU) (lo n i:ℕ) :ℕ :=
 if i=0 then 0
 else aOy ((131071-lo)*(s.B+1-i)) (2*lo) (s.m*lI) n
def stop (s :aU) (E v :ℕ) :=s.J+Tb s E v
def bcR (C:Core) (J x :ℕ) :ℤ:=C.vo x 0 - C.vo x (J+1)
private def group (s :aU) (h:ℤ) (E v d l r k :ℕ) :ℤ :=
 if l< r then
  let C:=bb1 s h E v d k
  bcR C s.J r - bcR C s.J l
 else 0
private theorem group_eq (s :aU) (lo:ℕ) (h:ℤ) (E v d l r k :ℕ)
   (he :0<E) (hk : ∀ t∈Ico l r,Xa s lo t=k) :
   group s h E v d l r k=1440*(∑ t∈Ico l r,diag s lo h E v d t) := by
 unfold group
 by_cases hl:l< r
 · rw [n5 hl]
   simp only [bcR,Core.azU,← mul_sub,← sum_Ico_eq_sub _ hl.le]
   have hd:=lz (f := fun t=>4*diag s lo h E v d t) rfl
     (fun t ht=>diag_eq s lo h E v d t k he (hk t ht))
   have hcol: (bb1 s h E v d k).column=k :=rfl
   rw [hcol,← hd,← mul_sum]
   ring
 · rw [nX hl,Ico_eq_empty_of_le (Nat.le_of_not_gt hl),sum_empty,mul_zero]
def IK (s :aU) (lo:ℕ) (h:ℤ) (E v i:ℕ) :ℤ :=
 let l:=boundary s lo (stop s E v) i
 let r :=boundary s lo (stop s E v) (i+1)
 let k :=s.B+1-i
 group s h E v 0 l r k - group s h E v 1 l r k
private theorem lt_boundary (s :aU) (h n i t:ℕ) (hi:0< i) (hB:i≤ s.B+1) :
  t<boundary s h n i↔t<n∧s.B+1-i<Xa s h t:= by
 have hb:s.B+1-i<s.B+1 := by omega
 simp only [boundary,nX (Nat.ne_of_gt hi),Xa,aIy,hb,true_and,add_comm]
private theorem dz1 (s :aU) (h n i:ℕ) (hi:i+1≤ s.B+1) :
   boundary s h n i≤boundary s h n (i+1) := by
 by_cases hz :i=0
 · simp [hz,boundary]
 by_contra! hn
 let t:=boundary s h n (i+1)
 obtain ⟨ht,hk⟩:=(lt_boundary s h n i t (by omega) (by omega)).mp hn
 exact (Nat.lt_irrefl _) ((lt_boundary s h n (i+1) t (by omega) hi).mpr ⟨ht,by omega⟩)
private theorem ekI (s :aU) (h n i t:ℕ) (hi:i+1≤ s.B+1)
  (ht:t∈Ico (boundary s h n i) (boundary s h n (i+1))) :
  Xa s h t=s.B+1-i:= by
 obtain ⟨hl,hr⟩:=mem_Ico.mp ht
 obtain ⟨htn,hq⟩:=(lt_boundary s h n (i+1) t (by omega) hi).mp hr
 have hu:Xa s h t≤ s.B+1-i:= by
  by_contra! hh
  by_cases hz :i=0
  · subst i
    have he :s.B+1<Xa s h t:= by simpa using hh
    exact (Nat.lt_irrefl _) ((aIy _ _ _ _ _).mp he).1
  · exact (not_lt_of_ge hl) ((lt_boundary s h n i t (by omega) (by omega)).mpr ⟨htn,hh⟩)
 omega
private theorem gwO (s :aU) (h n count:ℕ) (hc:count≤ s.B+1) (f :ℕ→ℤ) :
   (∑ i∈cy count,∑ t∈Ico (boundary s h n i) (boundary s h n (i+1)),f t) =
     ∑ t∈cy (boundary s h n count),f t:= by
 induction count with
 | zero=>simp [boundary]
 | succ i ih =>
   rw [nI,ih (by omega :i≤ s.B+1),sum_range_add_sum_Ico f (dz1 s h n i hc)]
theorem dbW (s :aU) (lo count E v :ℕ) (h:ℤ) (he :0<E)
  (hc:count≤ s.B+1) (hb:boundary s lo (stop s E v) count=stop s E v) :
  (∑ i∈cy count,IK s lo h E v i)=1440*total s E v (Bp s lo h) := by
 rw [total_eq_phases _ _ _ _ he,phase,phase,← lJ]
 change _=1440*(∑ t∈cy (stop s E v),
  (diag s lo h E v 0 t - diag s lo h E v 1 t))
 rw [← hb,← gwO s lo (stop s E v) count hc,mul_sum]
 apply lz rfl; intro i hi
 have hc' : i+1≤ s.B+1 :=Nat.le_trans (mem_range.mp hi) hc
 have hk := fun t ht=>ekI s lo (stop s E v) i t hc' ht
 rw [IK,group_eq _ _ _ _ _ _ _ _ _ he hk,
  group_eq _ _ _ _ _ _ _ _ _ he hk,lJ]
 ring
end qqf9uAa
end
end
section
set_option autoImplicit true
namespace P6_3
noncomputable section
open P6 Polynomial
open Rv (Bank an0)
def afT {u T R D} (B:KJ u T R D) (l:Fin 2) :K[X] :=
  B.a*(B.β l).map twist
def aeb {u T R D} (B:KJ u T R D) (j:Fin 2) :K[X] :=
  -(B.b*B.α j)
abbrev EJ:ℕ:=4*dw - 1
def aPB (aV:Bank) (n h:ℕ) :Prop :=
  n*(BN.adQ 4 aV.first aV.second -
      BN.adQ 3 (aV.first - 1) (aV.second - 1)) <
    BN.acN EJ 5 aV.first aV.second -
      BN.acN (EJ-(k - 1) - h) 4
        (aV.first - 1) (aV.second - 1)
def arz :ℚ :=
  (((blockLength-(k - 1))*an0:ℕ) :ℚ)/((dw-(k - 1) :ℕ) :ℚ)
def aPP:ℕ := ⌈((210 :ℕ) :ℚ)*arz^2⌉₊
end
end P6_3
end
section
set_option autoImplicit true
namespace qK9H6va
open P6_6_1 (FF DV)
open aR MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open fP (Form GS Ew lP m9 L4 Jx)
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
open private Local T brP be8 a5k aDF bIp cXS aIu djp cXT aWA bH2 deP cSR merge c0l from ProximityPrize.SubmissionLower.AS
private def postprocess (s :ℕ) (g:ℤ) :Form →ₗ[ao] Local :=
  (projectLowContact 155).comp
    ((LinearMap.mulLeft ao (T^(g+56).toNat *
      (aDF L4)^(s - iO s))).comp aDF.toLinearMap)
private theorem eNg (s :ℕ) (g:ℤ) (hg : -56≤g) {P:Form}
    (hP:P.IsWeightedHomogeneous (fun _=>(1 :ℕ)) (iO s)) :
    postprocess s g (weightedTruncation m9 (Vm s g).toNat P) =
      postprocess s g P:= by
  let d:=iO s
  let cutoff :=(Vm s g).toNat
  let H :=filterSupport (fun e :Fin 4 →₀ ℕ => ¬ e.weight m9<cutoff) P
  have hsplit :weightedTruncation m9 cutoff P+H=P :=
    filterSupport_add_filterSupport_not _ _
  have hH :H∈restrictWeightedOrder (fun j=>1+m9 j) (d+cutoff) := by
    refine mem_restrictWeightedOrder.mpr fun e he => ?_
    have hc:=mem_support_iff.mp he
    change (filterSupport _ P).coeff e≠0 at hc
    rw [coeff_filterSupport] at hc
    by_cases hl:e.weight m9<cutoff
    · simp [hl] at hc
    · have hd:=hP (d:=e) (by simpa [hl] using hc)
      rw [← Finsupp.degree_eq_weight_one] at hd
      have hw:e.weight (fun j=>1+m9 j)=e.degree+e.weight m9:= by
        rw [Finsupp.degree_eq_sum,Finsupp.weight_eq_sum,Finsupp.weight_eq_sum,
          ← Finset.sum_add_distrib]
        simp [Nat.mul_add]
      rw [hw,hd]
      exact Nat.add_le_add_left (Nat.le_of_not_lt hl) d
  have ht: (T^(g+56).toNat) ∈
      restrictWeightedOrder (localContactWeight 3) ((g+56).toNat*1) :=
    pow_mem_restrictWeightedOrder (X_mem_restrictWeightedOrder _ _ (localContactWeight_T 3).ge) _
  have hf :=pow_mem_restrictWeightedOrder cXT (s - d)
  have hh:=mul_mem_restrictWeightedOrder (mul_mem_restrictWeightedOrder ht hf)
    (bind₁_mem_restrictWeightedOrder aIu hH)
  have hc:155≤((g+56).toNat*1+(s-d)*1)+(d+cutoff) := by
    have hd:d≤ s :=min_le_left _ _
    dsimp [cutoff,Vm]
    omega
  have hz :postprocess s g H=0 :=
    (weightedTruncation_eq_zero_iff _ _ _).mpr (restrictWeightedOrder_anti _ hc hh)
  calc
    postprocess s g (weightedTruncation m9 cutoff P) =
        postprocess s g (weightedTruncation m9 cutoff P+H) := by rw [map_add,hz,add_zero]
    _=postprocess s g P:= by rw [hsplit]
private theorem gql (P:Local) :
    T^56*projectLowContact 99 P=projectLowContact 155 (T^56*P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial e a =>
      have hmul :T^56*monomial e a=monomial (Finsupp.single (localT 3) 56+e) a := by
        rw [MvPolynomial.X_pow_eq_monomial,monomial_mul_monomial,one_mul]
      rw [aWA,hmul,aWA]
      have ho:localContactOrder 3 (Finsupp.single (localT 3) 56+e) =
          56+localContactOrder 3 e := by
        simp [localContactOrder,Finsupp.weight_single]
      have hlt:localContactOrder 3 (Finsupp.single (localT 3) 56+e)<155 ↔
          localContactOrder 3 e<99:= by rw [ho]; omega
      by_cases he :localContactOrder 3 e<99
      · simp [he,hlt.mpr he,hmul]
      · have hnot : ¬ localContactOrder 3 (Finsupp.single (localT 3) 56+e)<155 :=
          fun h=>he (hlt.mp h)
        simp [he,hnot]
  | add P Q hP hQ=>simp only [map_add,mul_add,hP,hQ]
private def trimmed (u:JetVariable 3 →₀ ℕ) :Fin 4 →₀ ℕ :=
  u.some-Finsupp.single 0 (u.some.degree - iO u.some.degree)
private theorem aJT (u:JetVariable 3 →₀ ℕ) (j:Fin 4) (h:j≠0) :
    trimmed u j=u (some j) := by
  simp [trimmed,Ne.symm h]
private theorem dh6 (u:JetVariable 3 →₀ ℕ) :
    (trimmed u).weight lP=u.some.weight lP:= by
  rw [bH2,bH2]
  rw [aJT u 1 (by decide),aJT u 2 (by decide),aJT u 3 (by decide)]
  simp
private theorem cuh (u:JetVariable 3 →₀ ℕ) (hu:FF u) :
    trimmed u 0+(u.some.degree - iO u.some.degree)=u (some 0) ∧
      (trimmed u).degree=iO u.some.degree := by
  have htotal:u.some.degree=u (some 0)+u (some 1)+u (some 2)+u (some 3) := by
    simp [Finsupp.degree_eq_sum,Fin.sum_univ_four]
  have hcap:=hu.2.2.2.1
  have htrim:trimmed u 0 =
      u (some 0)-(u.some.degree - iO u.some.degree) := by
    simp [trimmed]
  have hnew : (trimmed u).degree =
      trimmed u 0+u (some 1)+u (some 2)+u (some 3) := by
    simp [Finsupp.degree_eq_sum,Fin.sum_univ_four,aJT u 1 (by decide),
      aJT u 2 (by decide),aJT u 3 (by decide)]
  simp only [iO] at *
  omega
private theorem dh7 (u:JetVariable 3 →₀ ℕ) (hu:FF u) :
    Ew (iO u.some.degree) (-((u none :ℤ) - u.some.weight lP))
      56 16 (trimmed u) := by
  refine ⟨(cuh u hu).2,?_,?_,?_⟩
  · rw [dh6]
    omega
  · rw [dh6]
    exact_mod_cast hu.2.1
  · rw [aJT u 3 (by decide)]
    exact hu.2.2.1
private theorem dxL (u:JetVariable 3 →₀ ℕ) (hu:FF u) (a :ao) :
    (Jx (monomial (trimmed u) a)).IsWeightedHomogeneous
      (fun _=>(1 :ℕ)) (iO u.some.degree) := by
  have h:=isWeightedHomogeneous_monomial (fun _:Fin 4=>(1 :ℕ)) (trimmed u) a
    (m:=iO u.some.degree)
    (by rw [← Finsupp.degree_eq_weight_one,(cuh u hu).2])
  apply h.bind₁
  intro j
  split_ifs
  · exact djp
  · exact isWeightedHomogeneous_X _ _ _
private theorem gqI (u:JetVariable 3 →₀ ℕ) (hu:FF u) (a :ao) :
    T^56*unscaledLocalSubstitution 3 0 0 (monomial u a) =
      T^(((u none :ℤ) - u.some.weight lP)+56).toNat *
        (aDF L4)^(u.some.degree - iO u.some.degree) *
        aDF (Jx (monomial (trimmed u) a)) := by
  have hi:=hu.2.1
  change u.some.weight lP≤56 at hi
  let r :=(((u none :ℤ) - u.some.weight lP)+56).toNat
  have ht:r+u.some.weight lP=u none+56:= by dsimp [r]; omega
  rw [bH2] at ht
  simp only [Finsupp.some_apply] at ht
  have hv :=(cuh u hu).1
  have h1 :unscaledLocalSubstitution (R:=ao) 3 0 0 (MvPolynomial.X (some 1)) =
      MvPolynomial.X (localY (0:Fin 3)) :=unscaledLocalSubstitution_Y_succ 3 0 0 0
  have h2 :unscaledLocalSubstitution (R:=ao) 3 0 0 (MvPolynomial.X (some 2)) =
      MvPolynomial.X (localY (1 :Fin 3)) :=unscaledLocalSubstitution_Y_succ 3 0 0 1
  have h3:unscaledLocalSubstitution (R:=ao) 3 0 0 (MvPolynomial.X (some 3)) =
      MvPolynomial.X (localY (2 :Fin 3)) :=unscaledLocalSubstitution_Y_succ 3 0 0 2
  have b0:Jx (MvPolynomial.X 0)=L4 := by simp [Jx]
  have b (j:Fin 4) (hj:j≠0) :Jx (MvPolynomial.X j)=MvPolynomial.X j:= by
    simp [Jx,hj]
  rw [deP,cSR]
  simp only [map_mul,map_pow,algHom_C,algebraMap_eq,unscaledLocalSubstitution_X,map_zero,
    zero_add,← cXS,h1,h2,h3,b0,b 1 (by decide),b 2 (by decide),b 3 (by decide),
    aJT u 1 (by decide),aJT u 2 (by decide),aJT u 3 (by decide),
    bIp]
  have hpow:T^r*T^u (some 1)*(T^2)^u (some 2)*(T^3)^u (some 3) =
      T^(u none+56) := by
    rw [← pow_mul,← pow_mul,← pow_add,← pow_add,← pow_add]
    congr 1
    omega
  calc
    _=T^(u none+56)*MvPolynomial.C a*aDF L4^u (some 0) *
        MvPolynomial.X (localY (0:Fin 3))^u (some 1) *
        MvPolynomial.X (localY (1 :Fin 3))^u (some 2) *
        MvPolynomial.X (localY (2 :Fin 3))^u (some 3) := by rw [pow_add]; ring
    _ = _:= by
      rw [← hpow,← hv,pow_add]
      simp [a5k,be8,brP,mul_pow]
      ring
private theorem gqw (u:JetVariable 3 →₀ ℕ) (hu:FF u)
    (a :ao) :
    let s :=u.some.degree
    let g:=(u none :ℤ) - u.some.weight lP
    T^56*localConstraintAt 99 0 0 (monomial u a) =
      postprocess s g (auo s g ⟨monomial (trimmed u) a,
        (monomial_mem_restrictSupport (R:=ao)).mpr (Or.inl (dh7 u hu))⟩) := by
  dsimp only [localConstraintAt,LinearMap.comp_apply,AlgHom.toLinearMap_apply]
  rw [gql,gqI u hu]
  have hi:=hu.2.1
  change u.some.weight lP≤56 at hi
  let s :=u.some.degree
  let g:ℤ:=(u none :ℤ) - u.some.weight lP
  let P:=Jx (monomial (trimmed u) a)
  change postprocess s g P=postprocess s g
    (weightedTruncation m9 (Vm s g).toNat P)
  exact (eNg s g (by dsimp [g]; omega) (dxL u hu a)).symm
theorem dzd (s :ℕ) (g:ℤ) (h:99-(s :ℤ)≤g) :
    auo s g=0:= by
  apply LinearMap.ext
  intro q
  change weightedTruncation m9 (Vm s g).toNat (Jx q)=0
  have hcut: (Vm s g).toNat=0:= by unfold Vm; omega
  rw [hcut,weightedTruncation_eq_zero_iff,restrictWeightedOrder_zero]
  trivial
private abbrev Block :=Fin 134×Fin 155
private abbrev Image (b:Block) :=LinearMap.range (auo b.1 (offset b.2))
private def assemble : (∀ b:Block,Image b) →ₗ[ao] Local :=
  merge (fun b=>postprocess b.1 (offset b.2))
private theorem eNf (b:Block) (s :ℕ) (g:ℤ)
    (hs : (b.1 :ℕ)=s) (hg:offset b.2=g)
    (q:GS (iO s) (-g) 56 16) :
    postprocess s g (auo s g q)∈LinearMap.range assemble := by
  subst s
  subst g
  let v :Image b:=⟨auo b.1 (offset b.2) q,LinearMap.mem_range_self _ q⟩
  exact ⟨Pi.single b v,c0l (fun j:Block=>postprocess j.1 (offset j.2)) b v⟩
private theorem gqC (u:JetVariable 3 →₀ ℕ)
    (hu:FF u) (a :ao) :
    T^56*localConstraintAt 99 0 0 (monomial u a)∈LinearMap.range assemble := by
  classical
  let s :=u.some.degree
  let g:ℤ:=(u none :ℤ) - u.some.weight lP
  let q:GS (iO s) (-g) 56 16 :=
    ⟨monomial (trimmed u) a,(monomial_mem_restrictSupport (R:=ao)).mpr (Or.inl (dh7 u hu))⟩
  have hmono:T^56*localConstraintAt 99 0 0 (monomial u a) =
      postprocess s g (auo s g q) :=gqw u hu a
  rw [hmono]
  by_cases hg:g<99
  · have hJ:=hu.2.1
    change u.some.weight lP≤56 at hJ
    have hs :s<134 := by exact Nat.lt_succ_of_le hu.1
    have hr : (g+56).toNat<155:= by dsimp [g] at *; omega
    let b:Block :=(⟨s,hs⟩,⟨(g+56).toNat,hr⟩)
    have ho:offset b.2=g:= by dsimp [b,offset,g]; omega
    exact eNf b s g rfl ho q
  · rw [dzd s g (by omega),LinearMap.zero_apply,map_zero]
    exact Submodule.zero_mem _
theorem fTq :
    Module.finrank ao (LinearMap.range (DV 0 0)) ≤
      ∑ s :Fin 134,b5w s := by
  classical
  let shift:=LinearMap.mulLeft ao (T^56)
  have hshift:Function.Injective shift :=
    fun _ _ h=>mul_left_cancel₀ (pow_ne_zero _ (MvPolynomial.X_ne_zero _)) h
  let ic:=shift.comp (DV 0 0)
  have hdim:Module.finrank ao (LinearMap.range ic) =
      Module.finrank ao (LinearMap.range (DV 0 0)) := by
    rw [LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective shift hshift _).finrank_eq.symm
  have hsub:LinearMap.range ic≤LinearMap.range assemble := by
    rintro _ ⟨Q,rfl⟩
    change shift (localConstraintAt 99 0 0 (Q:DifferentialPolynomial ao 3))∈_
    rw [(Q:DifferentialPolynomial ao 3).as_sum,map_sum,map_sum]
    exact Submodule.sum_mem _ fun u hu=>gqC u (Q.property hu) _
  have (b:Block) :Module.Finite ao (Image b) := by
    have :Module.Finite ao (GS (iO b.1) (-offset b.2) 56 16) :=
      restrictSupport_finite ((Finsupp.finite_of_degree_le _).subset fun _ he =>
        Nat.le_of_eq he.1)
    infer_instance
  calc
    _=Module.finrank ao (LinearMap.range ic) :=hdim.symm
    _≤Module.finrank ao (LinearMap.range assemble) :=Submodule.finrank_mono hsub
    _≤Module.finrank ao (∀ b:Block,Image b) :=LinearMap.finrank_range_le assemble
    _ = _ := by rw [Module.finrank_pi_fintype, Fintype.sum_prod_type]
                rfl
end
end qK9H6va
end
section
set_option autoImplicit true
namespace qK9H6va
open fP (cF xH oG)
open scoped BigOperators
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
open private r0 r1 r2 r3 r4 r5 r6 r7 from ProximityPrize.SubmissionLower.ZITfVad
private theorem eWA:r0.sum=417639:= by decide
private theorem fgW:r1.sum=3600562 := by decide
private theorem fpX:r2.sum=5233908:= by decide
private theorem fvo:r3.sum=3978883:= by decide
private theorem fzQ:r4.sum=2449302 := by decide
private theorem fDM:r5.sum=1249733:= by decide
private theorem fHk :r6.sum=468902 := by decide
private theorem fKZ:r7.sum=67696:= by decide
private theorem ehQ: (∑ q:Fin 134,Ni q)=17466625:= by
  have hlen:aPJ.length=134 := by rfl
  calc
    _ = ∑ q:Fin aPJ.length,aPJ[q.val]! := by rw [hlen]; rfl
    _ = ∑ q:Fin aPJ.length,aPJ[q.val] :=
      Finset.sum_congr rfl fun q _=> by rw [getElem!_pos]
    _=aPJ.sum:=Fin.sum_univ_getElem aPJ
    _ = _:= by
      simp only [aPJ,List.sum_append,eWA,fgW,fpX,fvo,
        fzQ,fDM,fHk,fKZ]
private theorem gA5 (q:ℕ) (hlo:132≤q) (hhi:q≤133) :
    Oi q≤Ni q:= by
  have hd:iO q=33:= by
    unfold iO P6_6_1.asu
    split <;> (try split) <;> omega
  have hz (g:ℤ) :Gy q g=0:= by
    ext e m
    have he :=e.property.1
    have hrow:=e.property.2
    have hcol:=m.property.2.1
    rw [cF] at he
    have he33:=he.trans hd
    rw [oG] at hrow
    rw [xH] at hcol
    unfold Vm at hrow
    have hlt:e.val 1< m.val 1∨e.val 2< m.val 2∨e.val 3< m.val 3:= by
      by_contra! h
      omega
    rcases hlt with h | h | h <;> simp [Gy,prefixMatrix,Nat.choose_eq_zero_of_lt h]
  simp [Oi,hz]
def c1 :Prop := ∀ q≤46,Oi q≤Ni q
def c2 :Prop :=RankBand 33 46
def c3:Prop :=RankBand 47 50
def c4 :Prop :=RankBand 51 55
def c5:Prop :=RankBand 56 56
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) :P6_6_1.c1 := by
  have gw (q:ℕ) (hq:q≤133) :Oi q≤Ni q:= by
    by_cases h46q:q≤46
    · exact h1 q h46q
    by_cases h131 :q≤131
    · have hdlo:33≤ iO q:= by
        unfold iO P6_6_1.asu
        split <;> (try split) <;> omega
      have hdhi:iO q≤56:=(min_le_right _ _).trans (gAv q)
      by_cases h46:iO q≤46
      · exact h2 q (by omega) h131 hdlo h46
      by_cases h50:iO q≤50
      · exact h3 q (by omega) h131 (by omega) h50
      by_cases h55:iO q≤55
      · exact h4 q (by omega) h131 (by omega) h55
      exact h5 q (by omega) h131 (by omega) hdhi
    · exact gA5 q (by omega) hq
  calc
    _ ≤ ∑ q:Fin 134,b5w q:=fTq
    _ ≤ ∑ q:Fin 134,Ni q:=Finset.sum_le_sum fun q _ =>
      (eiE q).trans (gw q (Nat.le_of_lt_succ q.isLt))
    _ = _:=ehQ
end qK9H6va
end

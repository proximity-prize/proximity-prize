import ProximityPrize.SubmissionLower.CH
import ProximityPrize.SubmissionLower.CI
set_option Elab.async false
open _root_ renaming Finset.range → z4x, Finset.range_mono → znF, Finset.sum_congr → zUo, Finset.sum_eq_zero → zYF, Finset.sum_le_sum → zQk, Nat.add_sub_cancel_left → z7K, Nat.div_le_div_right → zf6, Nat.le_add_right → z8K, Nat.sub_le_sub_left → zTu, Nat.sub_le_sub_right → zIu, Nat.succ_le_succ → zLT
set_option autoImplicit true
section
namespace wV
open aR (Shape)
open gW (Bank)
open scoped BigOperators
abbrev a9P:=Bank→Shape→ℕ
def HY (degree index top:ℕ) :ℕ :=
 if degree=0 then 0 else AJ.bmI ⟨degree - 1,index,top⟩
def bgn:List (ℕ×ℕ×ℕ) :=
 [(0,3400,1650),(3400,3438,1600),(3438,3603,1550),(3603,3634,1500),
  (3634,3663,1450),(3663,3711,1400),(3711,3770,1350),(3770,3817,1300),
  (3817,3866,1250),(3866,3914,1200),(3914,3962,1150),(3962,4010,1100),
  (4010,4021,1050)]
def aWp (used limit index top:ℕ) (kA:ℕ×ℕ×ℕ) :ℕ :=
  let (lo,hi,cap) :=kA
  let first:=lo - used
  let endGrade :=min limit hi - used
  let aJm:=min endGrade (cap+1)
  (HY aJm index top - HY (min first aJm) index top) +
    (endGrade - max first (cap+1)) *
      (HY (cap+1) index top - HY cap index top)
def pS (b:Bank) (used :Shape) :ℕ :=
  let q:=b.box
  if used.b≤q.b∧used.j≤q.j∧used.t≤q.t then
    (bgn.map (aWp used.b (q.b+1) (q.j - used.j) (q.t - used.t))).sum
  else 0
def zN (count:a9P) (b:Bank) (x :Shape) :ℕ :=
 ∑ r∈z4x (b.box.t/x.t),count b (x.scale (r+1))
def C8 (l bw fallback :ℕ) :ℕ:=if 0<l then min bw fallback else fallback
end wV
end
section
namespace wV
open aR (ceilDiv)

open scoped BigOperators
private theorem cEr {a d k :ℕ} (h:a≤d*k) :ceilDiv a d≤k := by
 by_cases hd:0<d
 · rw [ceilDiv,← Nat.lt_succ_iff,Nat.div_lt_iff_lt_mul hd,Nat.succ_mul]
   rw [Nat.mul_comm k d]
   omega
 · have he :d=0:= by omega
   simp [ceilDiv,he]
end wV
end
section
namespace aGb


open wV (HY)
open scoped BigOperators
private def slots (j t:ℕ) (f :ℕ→ℕ) :ℕ :=
 ∑ z∈z4x (min t (j/3)+1),
   ∑ y∈z4x ((j-3*z)/2+1),
     ∑ x∈z4x (j-3*z - 2*y+1),f (z+y + x)
private theorem crJ {n m:ℕ} (h:n≤ m) {f g:ℕ→ℕ}
  (same : ∀ i<n,f i=g i) (zero : ∀ i< m,n≤ i→ g i=0) :
  (∑ i∈z4x n,f i) = ∑ i∈z4x m,g i:= by
 calc
  _ = ∑ i∈z4x n,g i :=
    zUo rfl (fun i hi=>same i (Finset.mem_range.mp hi))
  _ = _:=Finset.sum_subset (znF h) (fun i hi hn =>
    zero i (Finset.mem_range.mp hi) (Nat.le_of_not_gt (hn ∘ Finset.mem_range.mpr)))
private theorem aTY (d j t:ℕ) :
    HY d j t=slots j t (fun w=>d - w) := by
  cases d with
  | zero=>simp [HY,slots]
  | succ d =>
    change AJ.bmI ⟨d,j,t⟩= _
    rw [← AJ.cr5]
    unfold Ds.symbols slots
    dsimp only
    apply crJ (by omega)
    · intro z hz
      apply crJ (zLT (min_le_right _ _))
      · intro y hy
        apply crJ (zLT (min_le_right _ _))
        · intro x hx
          omega
        · intro x hx hnx
          omega
      · intro y hy hny
        exact zYF fun x _=> by omega
    · intro z hz hnz
      refine zYF fun y _=>zYF fun x _ => ?_
      omega
private theorem increment (d j t:ℕ) :
  HY (d+1) j t =
   HY d j t+slots j t (fun w=>if w≤d then 1 else 0) := by
 simp only [aTY,slots,← Finset.sum_add_distrib]
 refine zUo rfl fun z _=>zUo rfl fun y _ =>
  zUo rfl fun x _ => ?_
 split <;> omega
private theorem boa (j t:ℕ) :Monotone (fun d=>HY d j t) :=
 monotone_nat_of_le_succ fun d=> by rw [increment]; exact z8K _ _
private theorem en0 {c d:ℕ} (h:c≤d) (j t:ℕ) :
  slots j t (fun w=>if w≤ c then 1 else 0) ≤
   slots j t (fun w=>if w≤d then 1 else 0) := by
 refine zQk fun z _=>zQk fun y _ =>
  zQk fun x _ => ?_
 change (if z+y + x≤ c then 1 else 0)≤(if z+y + x≤d then 1 else 0)
 split <;> split <;> omega
private theorem cUr {cap start:ℕ} (h:cap≤ start) (n j t:ℕ) :
   n*(HY (cap+1) j t - HY cap j t) ≤
     HY (start+n) j t - HY start j t:= by
 rw [increment cap,z7K]
 induction n with
 | zero=>simp
 | succ n ih =>
   have hm:=en0 (h.trans (z8K start n)) j t
   have hs :HY start j t≤HY (start+n) j t :=
     boa j t (z8K start n)
   rw [Nat.succ_mul,← Nat.add_assoc,increment]
   omega
end aGb
end
section
namespace wV
open gW (Gq)
open scoped BigOperators
def c1 :Prop :=pS=Gq
end wV
end
section
namespace bSj
open Finset
open gW (Gq Dj V7)
open wV (HY pS aWp bgn)
open scoped BigOperators
private def total (j t:ℕ) (f :ℕ→ℕ) :ℕ :=
 ∑ z∈range (min t (j/3)+1),
   ∑ y∈range ((j-3*z)/2+1),
     ∑ x∈range (j-3*z - 2*y+1),f (z+y + x)
private theorem bw7 (d b:ℕ) (f :ℕ→ℕ) (h : ∀ i,d< i→f i=0) :
  (∑ i∈range (min d b+1),f i) = ∑ i∈range (b+1),f i:= by
 apply sum_subset (range_mono (zLT (min_le_right d b)))
 intro i hi hn
 simp only [mem_range] at hi hn
 exact h i (by omega)
private theorem cD9 (d j t:ℕ) (f :ℕ→ℕ) (h : ∀ n,d<n→f n=0) :
    (∑ z∈range (min d (min t (j/3))+1),
      ∑ y∈range (min (d - z) ((j-3*z)/2)+1),
        ∑ x∈range (min (d - z - y) (j-3*z - 2*y)+1),f (z+y + x)) =
      total j t f := by
  unfold total
  rw [bw7 d (min t (j/3))]
  · refine sum_congr rfl fun z _ => ?_
    rw [bw7 (d - z) ((j-3*z)/2)]
    · exact sum_congr rfl fun y _ =>
        bw7 _ _ _ fun x hx=>h _ (by omega)
    · exact fun y hy=>sum_eq_zero fun x _=>h _ (by omega)
  · exact fun z hz=>sum_eq_zero fun y _=>sum_eq_zero fun x _=>h _ (by omega)
private theorem ay9 (d j t:ℕ) :
   V7 d j t=total j t (fun w=>if w≤d then 1 else 0) := by
 unfold V7
 rw [← cD9 d j t _ (fun n hn=>ite_eq_right (Nat.not_le_of_gt hn))]
 refine sum_congr rfl fun z hz=>sum_congr rfl fun y hy => ?_
 let count:=min (d - z - y) (j-3*z - 2*y)+1
 change count = ∑ x∈range count,if z+y + x≤d then 1 else 0
 calc
   count = ∑ _∈range count,(1 :ℕ) := by
     simp only [sum_const,Nat.nsmul_eq_mul,card_range,mul_one]
   _ = _:= by
     refine sum_congr rfl fun x hx => ?_
     simp only [count,mem_range] at hz hy hx
     rw [ite_eq_left (by omega)]
private theorem crI (d j t:ℕ) :
   (∑ r∈range d,V7 r j t)=total j t (fun w=>d - w) := by
 induction d with
 | zero=>simp [total]
 | succ d ih =>
   rw [sum_range_succ,ih,ay9]
   simp only [total,← sum_add_distrib]
   refine sum_congr rfl fun z _=>sum_congr rfl fun y _=>sum_congr rfl fun x _ => ?_
   split <;> omega
private theorem aTY (d j t:ℕ) :
   HY d j t = ∑ r∈range d,V7 r j t:= by
 rw [crI]
 cases d with
 | zero=>simp [HY,total]
 | succ d =>
   rw [HY,ite_eq_right (Nat.succ_ne_zero _),Nat.succ_sub_one,
     ← AJ.cr5,
     ← cD9 d j t (fun w=>d+1 - w) (fun n hn=> by omega)]
   simp only [Ds.symbols,min_left_comm t d (j/3)]
   refine sum_congr rfl fun z hz=>sum_congr rfl fun y hy=>sum_congr rfl fun x hx => ?_
   simp only [mem_range] at hz hy hx
   omega
private theorem eNO (f :ℕ→ℕ) {a b:ℕ} (h:a≤b) :
  (∑ r∈range b,f r)-(∑ r∈range a,f r) = ∑ r∈Ico a b,f r := by
 rw [← sum_range_add_sum_Ico f h,z7K]
private theorem cHX (j t:ℕ) {a b c:ℕ} (h:c≤a) :
  (∑ r∈Ico a b,V7 (min r c) j t)=(b-a)*V7 c j t:= by
 calc
  _ = ∑ _∈Ico a b,V7 c j t:=sum_congr rfl fun r hr=> by
    rw [min_eq_right (h.trans (mem_Ico.mp hr).1)]
  _ = _:= by simp only [sum_const,Nat.nsmul_eq_mul,Nat.card_Ico]
private theorem eL4 (a b c j t:ℕ) :
    (HY (min b (c+1)) j t -
        HY (min a (min b (c+1))) j t) +
      (b - max a (c+1))*(HY (c+1) j t - HY c j t) =
    ∑ r∈Ico a b,V7 (min r c) j t:= by
  have hs :HY (c+1) j t - HY c j t=V7 c j t:= by
    simp only [aTY,sum_range_succ,z7K]
  let m:=min b (c+1)
  change HY m j t - HY (min a m) j t+_ = _
  rw [hs,aTY m,aTY (min a m),eNO _ (min_le_right a m)]
  by_cases ha :a≤ m
  · rw [min_eq_left ha,← sum_Ico_consecutive (fun r=>V7 (min r c) j t) ha
      (min_le_left b (c+1))]
    refine congrArg₂ (· + ·) (sum_congr rfl fun r hr => ?_) ?_
    · have hrm:=(mem_Ico.mp hr).2
      rw [min_eq_left (by dsimp [m] at hrm; omega)]
    · by_cases hb:c+1≤b
      · have hm:m=c+1 :=min_eq_right hb
        rw [hm] at ha ⊢
        rw [max_eq_right ha,cHX j t (Nat.le_succ c)]
      · have hm:m=b:=min_eq_left (by omega)
        rw [hm,Ico_self,sum_empty,Nat.sub_eq_zero_of_le (by omega :b≤ max a (c+1)),
          zero_mul]
  · rw [min_eq_right (by omega :m≤a),Ico_self,sum_empty,zero_add]
    by_cases hab:a≤b
    · have hc:c+1≤a := by dsimp [m] at ha; omega
      rw [max_eq_left hc,cHX j t (by omega :c≤a)]
    · have hba :b≤a := by omega
      rw [Ico_eq_empty_of_le hba,sum_empty,
        Nat.sub_eq_zero_of_le (hba.trans (le_max_left a (c+1))),zero_mul]
private def clip (used limit q:ℕ) :ℕ:=min limit q - used
private theorem eL3 (used limit j t lo hi c:ℕ) (h:lo≤hi) :
   aWp used limit j t (lo,hi,c) =
     ∑ r∈Ico (clip used limit lo) (clip used limit hi),V7 (min r c) j t:= by
 have he :Ico (lo - used) (clip used limit hi) =
     Ico (clip used limit lo) (clip used limit hi) := by
   ext r
   simp only [clip,mem_Ico]
   omega
 unfold aWp
 dsimp only
 rw [eL4]
 exact congrArg (fun s => ∑ r∈s,V7 (min r c) j t) he
private def ow (start stop:ℕ) :List (ℕ×ℕ×ℕ)→Prop
  | []=>start=stop
  | (lo,hi,cap) :: rest =>
    start=lo∧lo≤hi ∧
      (∀ r used :ℕ,lo≤ r+used→ r+used<hi →
        min r (Dj (r+used))=min r cap)∧ow hi stop rest
private theorem eO4 :ow 0 4021 bgn:= by
 simp only [bgn,ow,true_and,and_true]
 refine ⟨by decide,?_,by decide,?_,by decide,?_,
  by decide,?_,by decide,?_,by decide,?_,
  by decide,?_,by decide,?_,by decide,?_,
  by decide,?_,by decide,?_,by decide,?_,by decide,?_⟩
 all_goals
  intro r used hlo hhi
  simp (disch:=omega) only [Dj,ite_eq_left,ite_eq_right] <;> omega
private theorem eoK (used limit j t stop:ℕ) (bands :List (ℕ×ℕ×ℕ))
    (start:ℕ) (h:ow start stop bands) :
    start≤ stop ∧
      (bands.map (aWp used limit j t)).sum =
        ∑ r∈Ico (clip used limit start) (clip used limit stop),
          V7 (min r (Dj (r+used))) j t:= by
  induction bands generalizing start with
  | nil =>
    change start=stop at h
    subst start
    simp
  | cons kA rest ih =>
    rcases kA with ⟨lo,hi,cap⟩
    obtain ⟨hstart,hle,hcap,htail⟩:=h
    subst start
    obtain ⟨hstop,hsum⟩:=ih hi htail
    refine ⟨hle.trans hstop,?_⟩
    rw [List.map_cons,List.sum_cons,hsum,eL3 _ _ _ _ _ _ _ hle]
    have hlocal :
        (∑ r∈Ico (clip used limit lo) (clip used limit hi),V7 (min r cap) j t) =
          ∑ r∈Ico (clip used limit lo) (clip used limit hi),
            V7 (min r (Dj (r+used))) j t:= by
      refine sum_congr rfl fun r hr => ?_
      have hr' := mem_Ico.mp hr
      simp only [clip] at hr'
      rw [hcap r used (by omega) (by omega)]
    rw [hlocal]
    exact sum_Ico_consecutive _
      (zIu (min_le_min_left limit hle) used)
      (zIu (min_le_min_left limit hstop) used)
theorem proof :wV.c1 := by
 change pS=Gq
 funext b used
 unfold pS Gq
 by_cases h:used.b≤b.box.b∧used.j≤b.box.j∧used.t≤b.box.t
 · simp only [ite_eq_left h]
   rw [(eoK used.b (b.box.b+1) (b.box.j - used.j) (b.box.t - used.t)
    4021 bgn 0 eO4).2]
   have hlimit :b.box.b+1≤4021 := by cases b <;> decide
   have hb:=h.1
   have hend:clip used.b (b.box.b+1) 4021=b.box.b - used.b+1 := by
    unfold clip
    rw [min_eq_left hlimit]
    omega
   rw [show clip used.b (b.box.b+1) 0=0 by simp [clip],hend,Nat.Ico_zero_eq_range]
 · simp only [ite_eq_right h]
end bSj
end
section
namespace WO
open aR (Shape aO)
open gW (Bank Gq Dj V7)
open wV (pS)
open scoped BigOperators
private theorem aQC {f g:ℕ→ℕ} {m n:ℕ} (hmn:m≤n)
   (h : ∀ i,f i≤g i) : (∑ i∈z4x m,f i) ≤ ∑ i∈z4x n,g i :=
 (zQk fun i _=>h i).trans (Finset.sum_le_sum_of_subset (znF hmn))
private theorem eiI {a b j k t u:ℕ} (hab:a≤b) (hjk :j≤k) (htu:t≤u) :
  V7 a j t≤V7 b k u:= by
 unfold V7
 apply aQC (zLT (min_le_min hab (min_le_min htu (zf6 hjk))))
 intro z
 have hb:=zIu hab z
 have hj:=zIu hjk (3*z)
 apply aQC (zLT (min_le_min hb (zf6 hj)))
 intro y
 exact zLT (min_le_min (zIu hb y) (zIu hj (2*y)))
private def fH (q:ℕ) :List (ℕ×ℕ)→ℕ
 | []=>1050
 | (k,cap) :: rest=>if q<k then cap else min cap (fH q rest)
private theorem dLQ (bs :List (ℕ×ℕ)) {x y :ℕ} (h:x≤y) :
    fH y bs≤fH x bs := by
  induction bs with
  | nil=>exact le_rfl
  | cons a bs ih =>
    obtain ⟨k,cap⟩:=a
    simp only [fH]
    by_cases hy :y<k
    · rw [ite_eq_left hy,ite_eq_left (h.trans_lt hy)]
    · rw [ite_eq_right hy]
      by_cases hx :x<k
      · rw [ite_eq_left hx]
        exact min_le_left _ _
      · rw [ite_eq_right hx]
        exact min_le_min le_rfl ih
private def cuts :List (ℕ×ℕ) :=
 [(3400,1650),(3438,1600),(3603,1550),(3634,1500),
  (3663,1450),(3711,1400),(3770,1350),(3817,1300),
  (3866,1250),(3914,1200),(3962,1150),(4010,1100)]
private theorem ay9 (q:ℕ) :Dj q=min q (fH q cuts) := by
 simp only [Dj,cuts,fH]
 by_cases h0:q<3400
 · simp only [*,↓reduceIte]
 by_cases h1 :q<3438
 · simp only [*,↓reduceIte]
   change 1600=min q 1600
   exact (min_eq_right (by omega)).symm
 by_cases h2 :q<3603
 · simp only [*,↓reduceIte]
   change 1550=min q 1550
   exact (min_eq_right (by omega)).symm
 by_cases h3:q<3634
 · simp only [*,↓reduceIte]
   change 1500=min q 1500
   exact (min_eq_right (by omega)).symm
 by_cases h4 :q<3663
 · simp only [*,↓reduceIte]
   change 1450=min q 1450
   exact (min_eq_right (by omega)).symm
 by_cases h5:q<3711
 · simp only [*,↓reduceIte]
   change 1400=min q 1400
   exact (min_eq_right (by omega)).symm
 by_cases h6:q<3770
 · simp only [*,↓reduceIte]
   change 1350=min q 1350
   exact (min_eq_right (by omega)).symm
 by_cases h7:q<3817
 · simp only [*,↓reduceIte]
   change 1300=min q 1300
   exact (min_eq_right (by omega)).symm
 by_cases h8:q<3866
 · simp only [*,↓reduceIte]
   change 1250=min q 1250
   exact (min_eq_right (by omega)).symm
 by_cases h9:q<3914
 · simp only [*,↓reduceIte]
   change 1200=min q 1200
   exact (min_eq_right (by omega)).symm
 by_cases Kr :q<3962
 · simp only [*,↓reduceIte]
   change 1150=min q 1150
   exact (min_eq_right (by omega)).symm
 by_cases h11 :q<4010
 · simp only [*,↓reduceIte]
   change 1100=min q 1100
   exact (min_eq_right (by omega)).symm
 simp only [*,↓reduceIte]
 change 1050=min q 1050
 exact (min_eq_right (by omega)).symm
private theorem eiJ {r x y :ℕ} (h:x≤y) :
  min r (Dj (r+y))≤ min r (Dj (r + x)) := by
 simp only [ay9,← min_assoc,min_eq_left (z8K r y),
  min_eq_left (z8K r x)]
 exact min_le_min le_rfl (dLQ _ (Nat.add_le_add_left h r))
private theorem dNb (b:Bank) {x y :Shape} (h:aO x y) :
   Gq b y≤Gq b x := by
 by_cases hy :y.b≤b.box.b∧y.j≤b.box.j∧y.t≤b.box.t
 · have hx :x.b≤b.box.b∧x.j≤b.box.j∧x.t≤b.box.t :=
    ⟨h.1.trans hy.1,h.2.1.trans hy.2.1,h.2.2.trans hy.2.2⟩
   simp only [Gq,ite_eq_left hy,ite_eq_left hx]
   apply aQC (zLT (zTu h.1 _))
   intro r
   exact eiI (eiJ h.1) (zTu h.2.1 _)
    (zTu h.2.2 _)
 · simp only [Gq,ite_eq_right hy,Nat.zero_le]
theorem aaQ (b:Bank) {x y :Shape} (h:aO x y) :
  pS b y≤pS b x := by
 have heq :pS=Gq:=bSj.proof
 rw [heq]
 exact dNb b h
end WO
end
section
namespace EN
open aR (Shape)
open gW (Bank)
open wV (pS)
open scoped BigOperators
private def WC (f :ℕ→ℕ) (start len:ℕ) :ℕ :=
 ∑ i∈z4x len,f (start+i)
private theorem bP5 (f :ℕ→ℕ) (start m n:ℕ) :
  WC f start (m+n)=WC f start m+WC f (start+m) n:= by
 simp only [WC,Finset.sum_range_add,Nat.add_assoc]
private def aEH (f :ℕ→ℕ) (start:ℕ) :List ℕ→ℕ
 | []=>0
 | width :: rest=>width*f start+aEH f (start+width) rest
private theorem byM {f :ℕ→ℕ} (hf :Antitone f) (xF:List ℕ) (start:ℕ) :
    WC f start xF.sum≤aEH f start xF:= by
  induction xF generalizing start with
  | nil=>simp [WC,aEH]
  | cons width rest ih =>
    rw [List.sum_cons,bP5,aEH]
    apply Nat.add_le_add _ (ih (start+width))
    calc
      _ ≤ ∑ _i∈z4x width,f start :=
        zQk fun i _=>hf (z8K _ i)
      _ = _:= by simp
def Ap (b:Bank) (x :Shape) (i:ℕ) :ℕ :=
 pS b (x.scale (i+1))
private def bvV (b:Bank) (x :Shape) (exactPrefix i:ℕ) :ℕ :=
 if i<exactPrefix then Ap b x i else AJ.ahC b.box (x.scale (i+1))
private theorem bvX {f g:ℕ→ℕ} (h : ∀ i,f i≤g i)
   (xF:List ℕ) (start:ℕ) :aEH f start xF≤aEH g start xF:= by
 induction xF generalizing start with
 | nil=>exact le_rfl
 | cons width rest ih =>
   exact Nat.add_le_add (Nat.mul_le_mul_left width (h start)) (ih (start+width))
abbrev Chunk :=List ℕ×ℕ
def vQ (b:Bank) (x :Shape) (exactPrefix start:ℕ) :List Chunk→Prop
  | []=>True
  | (xF,value) :: rest =>
    aEH (bvV b x exactPrefix) start xF=value ∧
      vQ b x exactPrefix (start + xF.sum) rest
def Fe :List Chunk→ℕ
 | []=>0
 | (xF,_) :: rest=>xF.sum+Fe rest
def Jz :List Chunk→ℕ
 | []=>0
 | (_,value) :: rest=>value+Jz rest
end EN
end
section
namespace Py
set_option maxHeartbeats 60000
set_option maxRecDepth 128
open aR (ceilDiv)
theorem LI {a b:ℕ} (h:a≤b) (d:ℕ) :ceilDiv a d≤ ceilDiv b d :=
 zf6 (zIu (Nat.add_le_add_right h d) 1)
end Py
end

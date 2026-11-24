import ProximityPrize.SubmissionLower.ZL8vffb
set_option Elab.async false
namespace qL60u
open jQ
def a6Ur (n a b:ℕ) :ℕ:=Nat.add (Nat.add (Nat.mul (Nat.mul (Nat.mul 6 n) a) b) (Nat.mul (Nat.mul (Nat.mul 3 (Nat.add a b)) n) (Nat.sub n 1))) (Nat.mul (Nat.mul n (Nat.sub n 1)) (Nat.add (Nat.mul 2 (Nat.sub n 1)) 1))
def buFr (N a:ℕ) :ℕ:=Nat.mul (Nat.mul 3 (Nat.sub N a)) (Nat.add (Nat.sub N a) 1)
def bK1r (N a:ℕ) :ℕ:=a6Ur (Nat.sub N a) a 1
private theorem cb (a b x y:ℕ) :cond (Nat.ble a b) x y=if a≤b then x else y:= by
  by_cases h:a≤b
  · rw [Nat.ble_eq_true_of_le h,if_pos h]; rfl
  · rw [Bool.eq_false_iff.mpr (fun e=>h (Nat.le_of_ble_eq_true e)),if_neg h]; rfl
def mx (a b:ℕ) :ℕ:=cond (Nat.ble a b) b a
def mn (a b:ℕ) :ℕ:=cond (Nat.ble a b) a b
theorem mx_eq (a b:ℕ) :mx a b=max a b:= by
  unfold mx; rw [cb,max_def]
theorem mn_eq (a b:ℕ) :mn a b=min a b:= by
  unfold mn; rw [cb,min_def]
def cemr (N k a:ℕ) :ℕ:=a6Ur (Nat.sub N (mx (Nat.add k 1) a)) (Nat.sub (mx (Nat.add k 1) a) k) (Nat.sub (Nat.add (mx (Nat.add k 1) a) 1) a)
theorem cemr_eq (N k a:ℕ) :cemr N k a=cem N k a:= by
  unfold cemr; rw [mx_eq]; rfl
def highr (B J t:ℕ) :ℕ:=mn J (Nat.sub (Nat.sub (Nat.add B (Nat.mul 2 J)) 1) t)
theorem highr_eq (B J t:ℕ) :highr B J t=high B J t:= by
  unfold highr; rw [mn_eq]; rfl
def widthr (B J t:ℕ) :ℕ:=Nat.sub (Nat.add (highr B J t) 1) (Nat.sub J t)
theorem widthr_eq (B J t:ℕ) :widthr B J t=width B J t:= by
  unfold widthr; rw [highr_eq]; rfl
def aoFr (B J t:ℕ) :ℕ:=mn (widthr B J t) (Nat.div (Nat.add (Nat.sub (Nat.sub (Nat.add B (Nat.mul 2 J)) t) (Nat.sub J t)) 1) 2)
theorem aoFr_eq (B J t:ℕ) :aoFr B J t=aoF B J t:= by
  unfold aoFr; rw [mn_eq,widthr_eq]; rfl
def bKtr (B J t:ℕ) (stat:ℕ→ℕ) :ℕ:=
  Nat.sub (Nat.add (stat (Nat.sub J t)) (stat (Nat.add (Nat.sub (Nat.add B (Nat.mul 2 J)) t) 1)))
    (Nat.add (stat (Nat.add (Nat.sub J t) (aoFr B J t))) (stat (Nat.sub (Nat.add (Nat.sub (Nat.add B (Nat.mul 2 J)) t) 1) (aoFr B J t))))
theorem bKtr_eq (B J t:ℕ) (stat:ℕ→ℕ) :bKtr B J t stat=bKt B J t stat:= by
  unfold bKtr; rw [aoFr_eq]; rfl
def bC6r (B J t:ℕ) (stat:ℕ→ℕ) :ℕ:=Nat.sub (stat (Nat.sub J t)) (stat (Nat.add (Nat.sub J t) (widthr B J t)))
theorem bC6r_eq (B J t:ℕ) (stat:ℕ→ℕ) :bC6r B J t stat=bC6 B J t stat:= by
  unfold bC6r; rw [widthr_eq]; rfl
def cudr (om:ℕ) (fuel:ℕ) :ℕ→ℕ→ℕ:=
  Nat.rec (motive:=fun _=>ℕ→ℕ→ℕ) (fun lo _=>lo)
    (fun _ r lo hi=>cond (Nat.ble (Nat.add (Nat.add lo 1) 1) hi)
      (cond (Nat.ble (Nat.mul (Nat.div (Nat.add lo hi) 2) (Nat.add (Nat.div (Nat.add lo hi) 2) 1)) (Nat.mul 2 om))
        (r (Nat.div (Nat.add lo hi) 2) hi) (r lo (Nat.div (Nat.add lo hi) 2))) lo) fuel
theorem cudr_eq (om:ℕ) :∀ f lo hi,cudr om f lo hi=cud om f lo hi
  | 0,lo,hi=>rfl
  | f+1,lo,hi=> by
    show cond (Nat.ble (Nat.add (Nat.add lo 1) 1) hi)
      (cond (Nat.ble (Nat.mul (Nat.div (Nat.add lo hi) 2) (Nat.add (Nat.div (Nat.add lo hi) 2) 1)) (Nat.mul 2 om))
        (cudr om f (Nat.div (Nat.add lo hi) 2) hi) (cudr om f lo (Nat.div (Nat.add lo hi) 2))) lo=_
    rw [cudr_eq om f,cudr_eq om f,cb,cb]
    simp only [cud]
    rfl
def thrr (B J t:ℕ) :ℕ:=
  cond (Nat.ble (Nat.div (bKtr B J t (buFr (Nat.add B 1))) 6) (Nat.mul (widthr B J t) (Nat.sub (Nat.add B 1) (highr B J t))))
    (Nat.sub B (Nat.div (Nat.sub (Nat.div (bKtr B J t (buFr (Nat.add B 1))) 6) 1) (widthr B J t)))
    (mn B (Nat.add (Nat.sub J t) (cudr (Nat.sub (Nat.div (bC6r B J t (buFr (Nat.add B 1))) 6) (Nat.div (bKtr B J t (buFr (Nat.add B 1))) 6)) 16 0 (Nat.add (widthr B J t) 1))))
theorem thrr_eq (B J t:ℕ) :thrr B J t=threshold B J t:= by
  unfold thrr; rw [mn_eq,cudr_eq,cb,bKtr_eq,bC6r_eq,widthr_eq,highr_eq]; rfl
def c2br (B J t:ℕ) :ℕ:=
  Nat.div (Nat.sub (Nat.add (Nat.mul (bKtr B J t (buFr (Nat.add B 1))) (thrr B J t)) (bC6r B J t (cemr (Nat.add B 1) (thrr B J t)))) (bKtr B J t (bK1r (Nat.add B 1)))) 6
theorem c2br_eq (B J t:ℕ) :c2br B J t=c2b B J t:= by
  unfold c2br; rw [thrr_eq,bKtr_eq,bKtr_eq,bC6r_eq]
  have e:cemr (Nat.add B 1) (threshold B J t)=cem (B+1) (threshold B J t):=funext fun a=>cemr_eq _ _ a
  rw [e]; rfl
def lTr (B J s n:ℕ) :ℕ:=Nat.rec (motive:=fun _=>ℕ) 0 (fun i r=>Nat.add r (c2br B J (Nat.add s i))) n
theorem lTr_eq (B J s:ℕ) :∀ n,lTr B J s n=lT B J s n
  | 0=>rfl
  | n+1=> by
    show Nat.add (lTr B J s n) (c2br B J (Nat.add s n))=m8 (fun i=>c2b B J (s+i)) (n+1)
    rw [lTr_eq B J s n,c2br_eq]
    rfl
theorem lT_of {B J s n t:ℕ} (h:lTr B J s n=t) :lT B J s n=t:=(lTr_eq B J s n).symm.trans h
end qL60u
namespace qpECY2d
set_option quotPrecheck false in
scoped notation "kV" => (by
 repeat' apply And.intro
 all_goals first | exact True.intro | (refine qL60u.lT_of ?_; decide +kernel) | decide +kernel)
set_option quotPrecheck false in
scoped notation "m2!" b:arg j:arg t:arg=>(aqm.ofEq
 (show jQ.lT b j j (b+j)=t from qL60u.lT_of (by decide +kernel)))
set_option quotPrecheck false in
scoped notation "p2!" b:arg j:arg t:arg w:arg n:arg x:arg =>
 checkedMoment b j t w n x kV rfl rfl
set_option quotPrecheck false in
scoped notation "s2!" b:arg j:arg a:arg w:arg n:arg x:arg =>
 segment b j a w n x kV
set_option quotPrecheck false in
scoped notation "j2!" b:arg j:arg t:arg xs:arg=>join b j t xs kV rfl rfl
end qpECY2d

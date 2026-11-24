import ProximityPrize.SubmissionLower.ZMwIPwd
set_option Elab.async false
namespace qL60s
open aFM (avC aM3 a7s)
open qs7wmAa (saveSum rowSave saving valPow topPow)
open private core countN from ProximityPrize.SubmissionLower.ZQpU10d
private theorem cb {α:Type} (a b:ℕ) (x y:α) :cond (Nat.ble a b) x y=if a≤b then x else y:= by
  by_cases h:a≤b
  · rw [Nat.ble_eq_true_of_le h,if_pos h]; rfl
  · rw [Bool.eq_false_iff.mpr (fun e=>h (Nat.le_of_ble_eq_true e)),if_neg h]; rfl
private theorem cbt {α:Type} (a b:ℕ) (x y:α) :cond (Nat.blt a b) x y=if a<b then x else y:=cb (a+1) b x y
private theorem cbe {α:Type} (a:ℕ) (x y:α) :cond (Nat.beq a 0) x y=if a=0 then x else y:= by
  by_cases h:a=0
  · subst h; rfl
  · rw [Bool.eq_false_iff.mpr (fun e=>h (Nat.eq_of_beq_eq_true e)),if_neg h]; rfl
def mnr (a b:ℕ) :ℕ:=cond (Nat.ble a b) a b
theorem mnr_eq (a b:ℕ) :mnr a b=min a b:= by unfold mnr; rw [cb,min_def]
theorem mnr_eq' (a b:ℕ) :mnr a b=Nat.min a b:= by
  first | (rw [mnr_eq]; done) | (rw [mnr_eq]; rfl) | (unfold mnr Nat.min; rw [cb]; rfl) | (rw [mnr_eq]; exact (Nat.min_def a b).symm)
def aM3r (d n:ℕ) :ℕ×ℕ:=
  cond (Nat.ble (mnr n (Nat.add (Nat.mul 3 d) 1)) (Nat.add d 1)) (avC (mnr n (Nat.add (Nat.mul 3 d) 1)),0)
   (cond (Nat.ble (mnr n (Nat.add (Nat.mul 3 d) 1)) (Nat.add (Nat.mul 2 d) 3))
     (avC (mnr n (Nat.add (Nat.mul 3 d) 1)),Nat.add (Nat.add (avC (Nat.sub (Nat.sub (mnr n (Nat.add (Nat.mul 3 d) 1)) d) 1)) (avC (Nat.sub (Nat.sub (mnr n (Nat.add (Nat.mul 3 d) 1)) d) 2))) (avC (Nat.sub (Nat.sub (mnr n (Nat.add (Nat.mul 3 d) 1)) d) 3)))
     (Nat.add (Nat.add (Nat.add (avC (mnr n (Nat.add (Nat.mul 3 d) 1))) (avC (Nat.sub (Nat.sub (mnr n (Nat.add (Nat.mul 3 d) 1)) (Nat.mul 2 d)) 3))) (avC (Nat.sub (Nat.sub (mnr n (Nat.add (Nat.mul 3 d) 1)) (Nat.mul 2 d)) 4))) (avC (Nat.sub (Nat.sub (mnr n (Nat.add (Nat.mul 3 d) 1)) (Nat.mul 2 d)) 5)),
      Nat.add (Nat.add (avC (Nat.sub (Nat.sub (mnr n (Nat.add (Nat.mul 3 d) 1)) d) 1)) (avC (Nat.sub (Nat.sub (mnr n (Nat.add (Nat.mul 3 d) 1)) d) 2))) (avC (Nat.sub (Nat.sub (mnr n (Nat.add (Nat.mul 3 d) 1)) d) 3))))
theorem aM3r_eq (d n:ℕ) :aM3r d n=aM3 d n:= by
  unfold aM3r; rw [mnr_eq',cb,cb]; rfl
def countNr (d n:ℕ) :ℕ:=Nat.sub (aM3r d n).1 (aM3r d n).2
theorem countNr_eq (d n:ℕ) :countNr d n=countN d n:= by
  unfold countNr countN; rw [aM3r_eq]; generalize aM3 d n=p; cases p; rfl
def Bpr (d m n:ℕ) :ℕ:=cond (Nat.blt d m) 0 (countNr (Nat.sub d m) n)
theorem Bpr_eq (d m n:ℕ) :Bpr d m n=if d<m then 0 else countN (d-m) n:= by
  unfold Bpr; rw [cbt,countNr_eq]; rfl
def corer (d u l o m:ℕ) :ℕ:=
  cond (Nat.beq m 0) (Nat.sub (countNr d u) (countNr d (mnr u l)))
   (cond (Nat.ble l u) (Nat.sub (Nat.add (countNr d u) (Bpr d m (Nat.sub o (Nat.mul 3 m)))) (Nat.add (countNr d o) (Bpr d m l)))
     (Nat.sub (Nat.add (Bpr d m (Nat.sub o (Nat.mul 3 m))) (countNr d l)) (Nat.add (countNr d o) (Bpr d m l))))
theorem corer_eq (d u l o m:ℕ) :corer d u l o m=core d u l o m:= by
  unfold corer core; simp only [cbe,cb,countNr_eq,Bpr_eq,mnr_eq]; rfl
def topPowr (d q r:ℕ) :ℕ:=mnr (mnr 570 (Nat.div (Nat.sub (Nat.sub (Nat.mul 4 (Nat.sub 4710 q)) 3422) (Nat.mul 9 r)) 2)) (Nat.sub d (Nat.sub (Nat.sub (Nat.add 3000 d) q) (Nat.mul 4 r)))
theorem topPowr_eq (d q r:ℕ) :topPowr d q r=topPow d q r:= by
  unfold topPowr; rw [mnr_eq,mnr_eq]; rfl
def savingr (d q r:ℕ) :ℕ:=
  corer (Nat.sub (Nat.sub d (Nat.sub (Nat.sub (Nat.add 3000 d) q) (Nat.mul 4 r))) (topPowr d q r)) (Nat.sub 1711 (Nat.mul 3 (topPowr d q r)))
    (Nat.sub (Nat.sub 1710 r) (Nat.mul 3 (topPowr d q r))) (Nat.sub (Nat.sub (Nat.sub 4710 q) r) (Nat.mul 2 (topPowr d q r)))
    (mnr (Nat.add (Nat.sub (Nat.sub d (Nat.sub (Nat.sub (Nat.add 3000 d) q) (Nat.mul 4 r))) (topPowr d q r)) 1) (Nat.div (Nat.sub (Nat.sub (Nat.add 3003 d) q) (Nat.sub (Nat.sub (Nat.add 3000 d) q) (Nat.mul 4 r))) 4))
theorem savingr_eq (d q r:ℕ) :savingr d q r=saving d q r:= by
  unfold savingr; rw [corer_eq,mnr_eq,topPowr_eq]; rfl
def a7r (f:ℕ→ℕ) (n:ℕ) :ℕ:=Nat.rec (motive:=fun _=>ℕ) 0 (fun i r=>Nat.add r (f i)) n
theorem a7r_eq (f:ℕ→ℕ) :∀ n,a7r f n=a7s f n
  | 0=>rfl
  | n+1=> by
    show Nat.add (a7r f n) (f n)=a7s f (n+1)
    rw [a7r_eq f n]; rfl
def rowSaver (d q:ℕ) :ℕ:=a7r (fun i=>a7r (fun j=>savingr d q (Nat.add (Nat.add 40 (Nat.mul 18 i)) j)) 18) 15
theorem rowSaver_eq (d q:ℕ) :rowSaver d q=rowSave d q:= by
  unfold rowSaver rowSave
  rw [a7r_eq]; congr 1; funext i; rw [a7r_eq]; congr 1; funext j; rw [savingr_eq]; rfl
def saveSumr (d lo n:ℕ) :ℕ:=Nat.rec (motive:=fun _=>ℕ) 0 (fun i r=>Nat.add r (rowSaver d (Nat.add lo i))) n
theorem saveSumr_eq (d lo:ℕ) :∀ n,saveSumr d lo n=saveSum d lo n
  | 0=>rfl
  | n+1=> by
    show Nat.add (saveSumr d lo n) (rowSaver d (Nat.add lo n))=saveSum d lo (n+1)
    rw [saveSumr_eq d lo n,rowSaver_eq]; rfl
theorem saveSum_of {d lo n t:ℕ} (h:saveSumr d lo n=t) :saveSum d lo n=t:=(saveSumr_eq d lo n).symm.trans h
end qL60s

import ProximityPrize.SubmissionLower.E7
import ProximityPrize.SubmissionLower.ZTqYzLd
import ProximityPrize.SubmissionLower.ZgEngac
set_option Elab.async false
set_option autoImplicit true
namespace qpjPzMc
open Finset
open P5_7_2 (A Aux)
open qMNIwTb (aL4 Mq capSum O3 fullCap)
open cu (Shape ku triangle)
open DP (bga azS)
open P5_7_4 (poleRank)
open qZyoMPc (aP4 scaledDebit_eq)
open agU (arY ad1)
open czX (a8x dei)
open private bid from ProximityPrize.SubmissionLower.CN
open private row aJm level df7 df3 bhM dgC cck from ProximityPrize.SubmissionLower.E7
private def amv (h r :ℕ) (s :Shape) (q j:ℕ) :ℕ :=
 Mq h ⟨r,s⟩+j - q*(131071-h)
private theorem cA5: (A:ℤ)=179740:=rfl
private def cut (s :Shape) (r lo mode :ℕ) :ℕ :=
 min (s.B+1) ((Mq lo ⟨r,s⟩ - 1-(2*mode*lo-1)*s.J)/(131071-lo)+1)
private def csU (s :Shape) (r lo mode q:ℕ) :ℕ :=
 min (min q s.J+1) ((amv lo r s q 0 - 1)/(2*mode*lo-1)+1)
private def support (s :Shape) (r lo mode q:ℕ) :ℕ :=
 if q<cut s r lo mode then min q s.J+1 else csU s r lo mode q
private def total (s :Shape) (r lo mode :ℕ) (x y z :ℤ) :ℤ :=
 let k :=cut s r lo mode
 aJm x y z s.J+level x y z s.J (k-s.J) +
  6*bhM (fun q=>row x y z q (csU s r lo mode q)) k (s.B+1-k)
private theorem asB (s :Shape) (r lo mode :ℕ) (x y z :ℤ)
   (hj:s.J≤ cut s r lo mode) :
   total s r lo mode x y z=6*(∑ q∈range (s.B+1),row x y z q (support s r lo mode q)) := by
 let k :=cut s r lo mode
 let f := fun q=>row x y z q (support s r lo mode q)
 have hk :k≤ s.B+1 :=min_le_left _ _
 have hsplit :=sum_range_add f k (s.B+1-k)
 have hprefix :=sum_range_add f s.J (k-s.J)
 rw [Nat.add_sub_of_le hk] at hsplit
 rw [Nat.add_sub_of_le hj] at hprefix
 change _=6*(∑ q∈range (s.B+1),f q)
 rw [hsplit,hprefix,mul_add,mul_add]
 have hfirst: (∑ q∈range s.J,f q) = ∑ q∈range s.J,row x y z q (q+1) := by
   apply sum_congr rfl
   intro q hq
   have hq' := mem_range.mp hq
   simp only [f,support,ite_eq_left (hq'.trans_le hj),min_eq_left hq'.le]
 have hmiddle : (∑ i∈range (k-s.J),f (s.J+i)) =
     ∑ i∈range (k-s.J),row x y z (s.J+i) (s.J+1) := by
   apply sum_congr rfl
   intro i hi
   have hi' := mem_range.mp hi
   have hlt:s.J+i<cut s r lo mode := by change s.J+i<k; omega
   simp only [f,support,ite_eq_left hlt,min_eq_right (Nat.le_add_right _ _)]
 have hlast : (∑ i∈range (s.B+1-k),f (k+i)) =
     ∑ i∈range (s.B+1-k),row x y z (k+i) (csU s r lo mode (k+i)) := by
   apply sum_congr rfl
   intro i _
   have hge :cut s r lo mode≤k+i:=Nat.le_add_right k i
   simp only [f,support,ite_eq_right (not_lt_of_ge hge)]
 rw [hfirst,hmiddle,hlast,df7,df3]
 dsimp only [total]
 rw [dgC]
private def origin (s :Shape) (r :ℕ) (h:ℤ) :ℤ:=(s.m:ℤ)*A - 2*h*r
private def aso (s :Shape) (r :ℕ) (h:ℤ) (mode q j:ℕ) :ℤ :=
 origin s r h-(131071-h)*q+(1-2*mode*h)*j
private def b7r (s :Shape) (r lo mode :ℕ) :ℤ :=
 total s r lo mode (2*origin s r lo) (-2*(131071-(lo:ℤ))) (1-2*(mode :ℤ)*lo)
private def cpY (s :Shape) (r lo mode :ℕ) :ℤ :=
 total s r lo mode (-4*(r :ℤ)) 2 (-2*(mode :ℤ))
private theorem gq1 (s :Shape) (r h mode q j:ℕ) (hh:h≤131071) :
  aso s r h mode q j≤((amv h r s q j - mode*(2*h*j) :ℕ) :ℤ) := by
 have cast_sub_le (a b:ℕ) : (a :ℤ)-b≤((a-b:ℕ) :ℤ) := by omega
 have hcut:=cast_sub_le (s.m*A) (2*h*r)
 have hraw:=cast_sub_le (Mq h ⟨r,s⟩+j) (q*(131071-h))
 have hloss :=cast_sub_le (amv h r s q j) (mode*(2*h*j))
 change _≤(Mq h ⟨r,s⟩:ℤ) at hcut
 change _≤(amv h r s q j:ℤ) at hraw
 push_cast [Nat.cast_sub hh] at hcut hraw hloss
 unfold aso origin
 rw [cA5]
 nlinarith only [hcut,hraw,hloss]
private theorem fZn (s :Shape) (r lo h mode q n:ℕ) :
   row (2*origin s r lo) (-2*(131071-(lo:ℤ))) (1-2*(mode :ℤ)*lo) q n +
     ((h:ℤ)-lo)*row (-4*(r :ℤ)) 2 (-2*(mode :ℤ)) q n =
   2*(∑ j∈range n,aso s r h mode q j) := by
 change _=2*(∑ j∈range n,(origin s r h-(131071-(h:ℤ))*q+(1-2*(mode :ℤ)*h)*j))
 rw [bid]
 unfold row origin
 ring
private theorem gxx (s :Shape) (r lo h mode :ℕ) (hh:h≤131071)
    (hj:s.J≤ cut s r lo mode) :
    b7r s r lo mode+((h:ℤ)-lo)*cpY s r lo mode ≤
      12*(ku s (fun q j=>amv h r s q j - mode*(2*h*j)) :ℤ) := by
  let f := fun q=>row (2*origin s r lo) (-2*(131071-(lo:ℤ))) (1-2*(mode :ℤ)*lo) q
    (support s r lo mode q)
  let g:= fun q=>row (-4*(r :ℤ)) 2 (-2*(mode :ℤ)) q (support s r lo mode q)
  have hsum: (∑ q∈range (s.B+1),f q)+((h:ℤ)-lo)*(∑ q∈range (s.B+1),g q) ≤
      2*(ku s (fun q j=>amv h r s q j - mode*(2*h*j)) :ℤ) := by
    unfold ku
    push_cast [Nat.cast_sum]
    rw [mul_sum,← sum_add_distrib,mul_sum]
    apply sum_le_sum
    intro q _
    rw [show f q+((h:ℤ)-lo)*g q= _ from fZn s r lo h mode q (support s r lo mode q)]
    have hsub:range (support s r lo mode q)⊆range (min q s.J+1) := by
      apply range_mono
      unfold support
      split
      · rfl
      · exact min_le_left _ _
    apply mul_le_mul_of_nonneg_left _ (by decide : (0:ℤ)≤2)
    calc
      _ ≤ ∑ j∈range (support s r lo mode q),((amv h r s q j - mode*(2*h*j) :ℕ) :ℤ) :=
        sum_le_sum fun j _=>gq1 s r h mode q j hh
      _≤_:=sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>Int.natCast_nonneg _)
  unfold b7r cpY
  rw [asB _ _ _ _ _ _ _ hj,asB _ _ _ _ _ _ _ hj]
  have hz :=mul_le_mul_of_nonneg_left hsum (by decide : (0:ℤ)≤6)
  dsimp only [f,g] at hz
  nlinarith only [hz]
private def biN (s :Shape) (r :ℕ) (h:ℤ) :ℤ :=
 origin s r h-(131071-h)*s.B
private theorem gMy (s :Shape) (r h:ℕ) (hh:h≤131071)
  (hw:0<biN s r h) :aL4 h ⟨r,s⟩:= by
 have hn:0≤(131071-(h:ℤ))*(s.B:ℤ) := by
  exact mul_nonneg (sub_nonneg.mpr (Int.ofNat_le.mpr hh)) (Int.natCast_nonneg _)
 unfold biN origin at hw
 have hbuf :2*h*r≤ s.m*A:= by
  have hz :2*(h:ℤ)*r≤(s.m:ℤ)*A:= by nlinarith only [hn,hw]
  exact_mod_cast hz
 unfold aL4 Mq
 apply Int.ofNat_lt.mp
 push_cast [Nat.cast_sub hh,Nat.cast_sub hbuf]
 rw [cA5] at hw
 nlinarith only [hw]
private def mode (moving:Bool) :ℕ:=if moving then 1 else 0
private def nodes (s :Shape) :ℤ:=262144*a8x (s.m-2*s.J) s.J
private theorem physical_eq (s :Shape) (hm:2*s.J≤ s.m) (hb:s.m+s.J≤ s.B+1) :
    6*(bga s :ℤ)=(triangle s.U:ℤ)*nodes s := by
  have e :6*bga s=triangle s.U*(262144*a8x (s.m-2*s.J) s.J) :=
    calc
      _=triangle s.U*(6*ad1 s) := by
        change 6*(triangle s.U*262144*_)=triangle s.U*(6*(262144*_))
        ring
      _ = _:= by rw [dei s hm hb]
  unfold nodes
  exact_mod_cast e
private theorem credit_eq (h:ℕ) (s :Shape) :
  (azS h s :ℤ)=2*(h:ℤ)*((triangle s.U:ℤ)*(arY s :ℤ)) := by
 change (↑(triangle s.U*(2*h)*arY s) :ℤ)= _
 push_cast
 ring
private theorem gain_eq (h:ℕ) (a :Aux) (moving:Bool) :
    (O3 h a (fullCap a.shape) moving:ℤ) =
      (triangle a.shape.U:ℤ) *
        (ku a.shape (fun q j=>amv h a.dI a.shape q j - mode moving*(2*h*j)) :ℤ) := by
  cases moving <;> simp [O3,capSum,ku,amv,mode]
private def cXb (s :Shape) (r lo m:ℕ) :ℤ :=
 240*(triangle s.U:ℤ)*(b7r s r lo m - 2*nodes s) - 2*lo*aP4 s.B s.J s.U
private def deC (s :Shape) (r lo m:ℕ) :ℤ :=
 240*(triangle s.U:ℤ)*cpY s r lo m - 2*aP4 s.B s.J s.U
def check (lo hi:ℕ) (a :Aux) (moving:Bool) :Bool :=
  let s :=a.shape
  let r :=a.dI
  let m:=mode moving
  let w:=biN s r lo
  let d:=(hi:ℤ)-lo
  let z :=cXb s r lo m
  decide (hi≤131071) && decide (s.J≤ s.B) && decide (s.B≤ s.U) &&
    decide (2*s.J≤ s.m) && decide (s.m+s.J≤ s.B+1) && decide (s.J≤ cut s r lo m) &&
    decide (0<w) && decide (0<w+d*((s.B:ℤ)-2*r)) &&
    decide (0<z) && decide (0<z+d*deC s r lo m)
theorem test {lo hi h:ℕ} {a :Aux} {moving:Bool} (hl:lo≤h) (hu:h≤hi)
    (hc:check lo hi a moving=true) :
    aL4 h a∧bga a.shape+2*h*poleRank a.shape <
      azS h a.shape+O3 h a (fullCap a.shape) moving:= by
  rcases a with ⟨r,s⟩
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hk,hj⟩,hu'⟩,hm⟩,hB⟩,hcut⟩,hw₀⟩,hw₁⟩,hz₀⟩,hz₁⟩:=hc
  have hh:=hu.trans hk
  have hlz :=Int.ofNat_le.mpr hl
  have huz :=Int.ofNat_le.mpr hu
  have hw:=cck hlz huz hw₀ hw₁
  have he :biN s r h=biN s r lo+((h:ℤ)-lo)*((s.B:ℤ)-2*r) := by
    unfold biN origin
    ring
  refine ⟨gMy s r h hh (he.symm ▸ hw),?_⟩
  have hz :=cck hlz huz hz₀ hz₁
  let m:=mode moving
  change 0<cXb s r lo m+((h:ℤ)-lo)*deC s r lo m at hz
  have hp:=physical_eq s hm hB
  have heq :cXb s r lo m+((h:ℤ)-lo)*deC s r lo m =
      240*(triangle s.U:ℤ)*(b7r s r lo m+((h:ℤ)-lo)*cpY s r lo m) -
        2880*(bga s :ℤ) - 2*(h:ℤ)*aP4 s.B s.J s.U:= by
    unfold cXb deC
    linear_combination 480*hp
  rw [heq,scaledDebit_eq s hj hu'] at hz
  have hs :=mul_le_mul_of_nonneg_left (gxx s r lo h m hh hcut)
    (show 0≤240*(triangle s.U:ℤ) by positivity)
  apply Int.ofNat_lt.mp
  push_cast only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
  change (bga s :ℤ)+2*(h:ℤ)*(poleRank s :ℤ) <
    (azS h s :ℤ)+(O3 h ⟨r,s⟩ (fullCap s) moving:ℤ)
  rw [credit_eq,gain_eq]
  change _<_+(triangle s.U:ℤ) *
    (ku s (fun q j=>amv h r s q j - m*(2*h*j)) :ℤ)
  nlinarith only [hz,hs]
end qpjPzMc

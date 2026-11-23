import ProximityPrize.SubmissionLower.E7
import ProximityPrize.SubmissionLower.ZL8vffb
set_option Elab.async false
set_option autoImplicit true
namespace P5_7_4
open Finset
open P5 (p)
open P5_7 (Bank Ls FarBand j3 farAgreement)
open cu (Shape ku triangle)
open private bid from ProximityPrize.SubmissionLower.CN
open private row aJm level df7 df3 cck from ProximityPrize.SubmissionLower.E7
private theorem cA5: (farAgreement:ℤ)=179779:=rfl
private def total (s :Shape) (x y z :ℤ) :ℤ :=
 aJm x y z s.J+level x y z s.J (s.B+1-s.J)
private theorem asB (s :Shape) (x y z :ℤ) (hj:s.J≤ s.B+1) :
   total s x y z=6*(∑ q∈range (s.B+1),row x y z q (min q s.J+1)) := by
 let f := fun q=>row x y z q (min q s.J+1)
 have hsplit :=sum_range_add f s.J (s.B+1-s.J)
 rw [Nat.add_sub_of_le hj] at hsplit
 change _=6*(∑ q∈range (s.B+1),f q)
 rw [hsplit,mul_add]
 have hfirst: (∑ q∈range s.J,f q) = ∑ q∈range s.J,row x y z q (q+1) := by
   apply sum_congr rfl
   intro q hq
   simp only [f,min_eq_left (mem_range.mp hq).le]
 have hlast : (∑ i∈range (s.B+1-s.J),f (s.J+i)) =
     ∑ i∈range (s.B+1-s.J),row x y z (s.J+i) (s.J+1) := by
   apply sum_congr rfl
   intro i _
   simp only [f,min_eq_right (Nat.le_add_right _ _)]
 rw [total,hfirst,hlast,df7,df3]
private def origin (s :Shape) (r :ℕ) (h:ℤ) :ℤ:=(s.m:ℤ)*farAgreement - 2*h*r
private def aso (s :Shape) (r :ℕ) (h:ℤ) (mode q j:ℕ) :ℤ :=
 origin s r h-(131071-h)*q+(1-2*mode*h)*j
private def b7r (s :Shape) (r lo mode :ℕ) :ℤ :=
 total s (2*origin s r lo) (-2*(131071-(lo:ℤ))) (1-2*(mode :ℤ)*lo)
private def cpY (s :Shape) (r _lo mode :ℕ) :ℤ :=
 total s (-4*(r :ℤ)) 2 (-2*(mode :ℤ))
private theorem gq1 (s :Shape) (r h mode q j:ℕ) (hh:h≤131071) :
  aso s r h mode q j≤((amv h r s q j - mode*(2*h*j) :ℕ) :ℤ) := by
 have cast_sub_le (a b:ℕ) : (a :ℤ)-b≤((a-b:ℕ) :ℤ) := by omega
 have hcut:=cast_sub_le (s.m*farAgreement) (2*h*r)
 have hraw:=cast_sub_le (Mq h r s+j) (q*(131071-h))
 have hloss :=cast_sub_le (amv h r s q j) (mode*(2*h*j))
 change _≤(Mq h r s :ℤ) at hcut
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
   (hj:s.J≤ s.B+1) :
   b7r s r lo mode+((h:ℤ)-lo)*cpY s r lo mode ≤
     12*(ku s (fun q j=>amv h r s q j - mode*(2*h*j)) :ℤ) := by
 let f := fun q=>row (2*origin s r lo) (-2*(131071-(lo:ℤ))) (1-2*(mode :ℤ)*lo) q
   (min q s.J+1)
 let g:= fun q=>row (-4*(r :ℤ)) 2 (-2*(mode :ℤ)) q (min q s.J+1)
 have hsum: (∑ q∈range (s.B+1),f q)+((h:ℤ)-lo)*(∑ q∈range (s.B+1),g q) ≤
     2*(ku s (fun q j=>amv h r s q j - mode*(2*h*j)) :ℤ) := by
   unfold ku
   push_cast [Nat.cast_sum]
   rw [mul_sum,← sum_add_distrib,mul_sum]
   apply sum_le_sum
   intro q _
   rw [show f q+((h:ℤ)-lo)*g q= _ from fZn s r lo h mode q (min q s.J+1)]
   exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _=>gq1 s r h mode q j hh)
     (by decide : (0:ℤ)≤2)
 unfold b7r cpY
 rw [asB _ _ _ _ hj,asB _ _ _ _ hj]
 have hz :=mul_le_mul_of_nonneg_left hsum (by decide : (0:ℤ)≤6)
 dsimp only [f,g] at hz
 nlinarith only [hz]
private def biN (s :Shape) (r :ℕ) (h:ℤ) :ℤ :=
 origin s r h-(131071-h)*s.B
private theorem gMy (s :Shape) (r h:ℕ) (hh:h≤131071)
  (hw:0<biN s r h) :aL4 h r s := by
 have hn:0≤(131071-(h:ℤ))*(s.B:ℤ) := by
  exact mul_nonneg (sub_nonneg.mpr (Int.ofNat_le.mpr hh)) (Int.natCast_nonneg _)
 unfold biN origin at hw
 have hbuf :2*h*r≤ s.m*farAgreement:= by
  have hz :2*(h:ℤ)*r≤(s.m:ℤ)*farAgreement:= by nlinarith only [hn,hw]
  exact_mod_cast hz
 unfold aL4 Mq
 apply Int.ofNat_lt.mp
 push_cast [Nat.cast_sub hh,Nat.cast_sub hbuf]
 rw [cA5] at hw
 nlinarith only [hw]
private def cXb (t:Bank) (r lo mode :ℕ) :ℤ :=
 (triangle t.shape.U:ℤ)*b7r t.shape r lo mode - 12*(j3 lo t:ℤ)
private def deC (t:Bank) (r lo mode :ℕ) :ℤ :=
 (triangle t.shape.U:ℤ)*cpY t.shape r lo mode - 24*(t.arY:ℤ)
private def check (lo hi:ℕ) (t:Bank) (r mode :ℕ) :Bool :=
 let w:=biN t.shape r lo
 let d:=(hi:ℤ)-lo
 let z :=cXb t r lo mode
 decide (hi≤131071) && decide (t.shape.J≤t.shape.B+1) &&
  decide (0<w) && decide (0<w+d*((t.shape.B:ℤ)-2*r)) &&
  decide (0<z) && decide (0<z+d*deC t r lo mode)
private theorem test {lo hi h:ℕ} {t:Bank} {r mode :ℕ} (hl:lo≤h) (hu:h≤hi)
  (hc:check lo hi t r mode=true) :
  aL4 h r t.shape∧j3 h t<O3 h r t.shape mode := by
 simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
 obtain ⟨⟨⟨⟨⟨hk,hj⟩,hw₀⟩,hw₁⟩,hz₀⟩,hz₁⟩:=hc
 have hl' : (lo:ℤ)≤h:=Int.ofNat_le.mpr hl
 have hu' : (h:ℤ)≤hi:=Int.ofNat_le.mpr hu
 have hh:=hu.trans hk
 have hw:=cck hl' hu' hw₀ hw₁
 have he :biN t.shape r h =
    biN t.shape r lo+((h:ℤ)-lo)*((t.shape.B:ℤ)-2*r) := by
  unfold biN origin
  ring
 refine ⟨gMy _ _ _ hh (he.symm ▸ hw),?_⟩
 have hz :=cck hl' hu' hz₀ hz₁
 have hs :=mul_le_mul_of_nonneg_left (gxx t.shape r lo h mode hh hj)
  (Int.natCast_nonneg (triangle t.shape.U))
 unfold cXb deC j3 at hz
 unfold O3 j3
 apply Int.ofNat_lt.mp
 push_cast at hz ⊢
 nlinarith only [hz,hs]
private def jf (lo hi:ℕ) (ss :List Ls) :Prop :=
 ∀ s∈ss,check lo hi s.free s.dI 0=true ∧
   check lo hi s.moving s.dI 1=true∧s.free.shape.U<p
private theorem dLg {lo hi:ℕ} {s :Ls} {ss :List Ls}
  (hf :check lo hi s.free s.dI 0=true)
  (hm:check lo hi s.moving s.dI 1=true)
  (hp:s.free.shape.U<p) (ht:jf lo hi ss) :jf lo hi (s :: ss) :=
 List.forall_mem_cons.mpr ⟨⟨hf,hm,hp⟩,ht⟩
private theorem dLh {lo hi:ℕ} : jf lo hi [] := by simp [jf]
set_option maxHeartbeats 5000000 in
private theorem dsU (b:FarBand) :jf b.row.lo b.row.hi b.row.stages := by
 cases b <;> simp only [FarBand.row]
 all_goals repeat' first
  | exact dLh
  | refine dLg rfl rfl (by decide) ?_
theorem stage_tests {b:FarBand} {h:ℕ} (hl:b.row.lo≤h) (hu:h≤b.row.hi)
  {s :Ls} (hs :s∈b.row.stages) :
  aL4 h s.dI s.free.shape∧j3 h s.free<O3 h s.dI s.free.shape 0 ∧
  s.free.shape.U<p∧aL4 h s.dI s.moving.shape ∧
  j3 h s.moving<O3 h s.dI s.moving.shape 1 := by
 obtain ⟨hf,hm,hc⟩:=dsU b s hs
 obtain ⟨hw,hd⟩:=test hl hu hf
 obtain ⟨hw',hd'⟩:=test hl hu hm
 exact ⟨hw,hd,hc,hw',hd'⟩
end P5_7_4

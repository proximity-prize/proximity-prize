import ProximityPrize.SubmissionLower.R6966ProofHelperWindowIntervals

set_option Elab.async false

namespace Research6966.HelperWindowCertificate
open Finset
open K1_14 (Shape shapeSum triangle)
open HelperAvoidance (debitAt rectSlots triSlots)
open HelperWindowIntervals (cutoff bound slotLimit triangle_tail rectangle_tail box axis)
open HelperWindowPrefix (volume)
set_option maxHeartbeats 850000

structure Witness where
  degree : ℕ
  rect : Bool
  lower : ℕ
  reserve : ℕ
  m : ℕ
  B : ℕ
  J : ℕ
  v : ℕ
  nodes : ℕ
  pole : ℕ

def agreement : ℕ := 179769
def firstHeight : ℕ := 2330
def lastHeight : ℕ := 2499
def seedCap : ℕ := 510000

def Witness.shape (b : Witness) : Shape :=
  ⟨b.m,b.B,b.J,if b.rect then seedCap else b.v⟩

def Witness.bank (b : Witness) : P1_7.Bank := ⟨b.shape,b.nodes,b.pole⟩

def Witness.weight (b : Witness) : ℕ := b.degree*(131071-lastHeight)-1

def Witness.width (b : Witness) : ℕ :=
  if b.rect then KoalaRect.area (box seedCap b.v) else triangle b.v

def Witness.rate (b : Witness) : ℕ :=
  if b.rect then box seedCap b.v 0+box seedCap b.v 1+2 else 2*(b.v+1)

def Witness.slots (b : Witness) (k : ℕ) : ℕ :=
  if b.rect then rectSlots (box seedCap b.v) (axis b.lower) k else triSlots b.v b.lower k

def Witness.top (b : Witness) (h : ℕ) : ℕ := cutoff b.shape agreement h b.reserve

def Witness.loop (b : Witness) (lo hi : ℕ) : ℕ :=
  bound b.shape agreement b.reserve lo hi b.degree 1 b.weight
    (slotLimit b.shape b.v b.lower) b.slots

def Positive (b : Witness) (lo hi : ℕ) : Prop :=
  b.width*b.nodes+hi*b.rate*b.pole+b.loop lo hi <
    b.width*volume (b.top hi) b.B b.J (131071-lo)

instance (b : Witness) (lo hi : ℕ) : Decidable (Positive b lo hi) := by
  unfold Positive
  infer_instance

def Cover (b : Witness) (lo : ℕ) : List ℕ → Prop
  | [] => lo = lastHeight+1
  | hi :: rest => lo ≤ hi ∧ hi ≤ lastHeight ∧ Positive b lo hi ∧ Cover b (hi+1) rest

theorem cover_height {b : Witness} {endpoints : List ℕ} {lo h : ℕ}
    (cover : Cover b lo endpoints) (low : lo ≤ h) (high : h ≤ lastHeight) :
    ∃ lo hi, lo ≤ h ∧ h ≤ hi ∧ hi ≤ lastHeight ∧ Positive b lo hi := by
  induction endpoints generalizing lo with
  | nil =>
    change lo=lastHeight+1 at cover
    omega
  | cons hi ends ih =>
    obtain ⟨_, hh, pos, tail⟩ := cover
    by_cases first : h ≤ hi
    · exact ⟨lo, hi, low, first, hh, pos⟩
    · exact ih tail (by omega)

theorem node_check (b : Witness) (hm : 2*b.J ≤ b.m) (hb : b.m+b.J ≤ b.B+1)
    (h : 262144*P1_7_1_2.sixPerNode (b.m-2*b.J) b.J = 6*b.nodes) :
    P1_7_1.nodeRows b.shape = b.nodes := by
  have eq := P1_7_1_2.six_nodeRows b.shape hm hb
  change 6*P1_7_1.nodeRows b.shape = 262144*P1_7_1_2.sixPerNode (b.m-2*b.J) b.J at eq
  rw [h] at eq
  omega

theorem weight_room (b : Witness) {h : ℕ} (lo : firstHeight ≤ h) (hi : h ≤ lastHeight)
    (hs : 2*b.reserve ≤ b.B) (hw : b.B*(131071-firstHeight) ≤ b.top firstHeight) :
    b.B*(131071-h) ≤ b.top h := by
  have delta : 131071-firstHeight = (131071-h)+(h-firstHeight) := by
    have last : lastHeight ≤ 131071 := by decide
    omega
  have res : 2*h*b.reserve = 2*firstHeight*b.reserve+(h-firstHeight)*(2*b.reserve) := by
    conv_lhs => rw [show h = firstHeight+(h-firstHeight) by omega]
    ring
  have more := Nat.mul_le_mul_left (h-firstHeight) hs
  have pre : b.B*(131071-firstHeight)+2*firstHeight*b.reserve ≤ b.m*agreement := by
    change b.B*(131071-firstHeight) ≤ b.m*agreement-2*firstHeight*b.reserve at hw
    by_cases nz : b.B*(131071-firstHeight) = 0
    · have bp : 0 < 131071-firstHeight := by decide
      have bz : b.B = 0 := (Nat.mul_eq_zero.mp nz).resolve_right bp.ne'
      have : b.reserve=0 := by omega
      rw [this, Nat.mul_zero, Nat.add_zero, nz]
      exact Nat.zero_le _
    · omega
  change b.B*(131071-h) ≤ b.m*agreement-2*h*b.reserve
  rw [res]
  rw [delta, Nat.mul_add] at pre
  rw [Nat.mul_comm (h-firstHeight) b.B] at more
  omega

theorem cutoff_order (b : Witness) {h : ℕ} (pos : 0 < b.top h) :
    b.top h-1+2*h*b.reserve < b.shape.m*agreement := by
  change 0 < b.m*agreement-2*h*b.reserve at pos
  change b.m*agreement-2*h*b.reserve-1+2*h*b.reserve < b.m*agreement
  omega

structure Verified (b : Witness) : Prop where
  node_eq : P1_7_1.nodeRows b.shape = b.nodes
  pole_ge : P1_7_1.groupedPoleMoment b.B b.J ≤ b.pole
  caps : b.B ≤ 5585 ∧ b.J ≤ 1200 ∧ b.v ≤ seedCap ∧ 0 < b.m ∧ 2*b.reserve ≤ b.B
  width_at_first : b.B*(131071-firstHeight) ≤ b.top firstHeight
  endpoints : ∃ endpoints : List ℕ, Cover b firstHeight endpoints

theorem Verified.raw_positive {b : Witness} (checked : Verified b) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    b.width*b.nodes+h*b.rate*b.pole+
        (∑ W ∈ range (b.top h), debitAt b.shape h (b.top h) W b.degree 1 b.weight b.slots) <
      b.width*shapeSum b.shape (fun q j => b.top h+j-q*(131071-h)) := by
  obtain ⟨ends, cover⟩ := checked.endpoints
  obtain ⟨bot, top, hb, ht, htop, cert⟩ := cover_height cover lo hi
  have tail : ∀ k > slotLimit b.shape b.v b.lower,
      b.slots k = 0 ∨ b.shape.B < k*b.degree ∨ b.shape.J < k*1 := by
    intro k big
    cases tag : b.rect
    · simpa only [Witness.slots,tag,Bool.false_eq_true,ite_false] using
        triangle_tail b.shape b.degree b.v b.lower k big
    · simpa only [Witness.slots,tag,ite_true] using
        rectangle_tail b.shape b.degree seedCap b.v b.lower k big
  have pos : 0 < h := (show 0 < firstHeight by decide).trans_le lo
  have narrow : b.shape.J < 131071-top := by
    change b.J < 131071-top
    have small := checked.caps.2.1
    have last : lastHeight = 2499 := rfl
    omega
  exact HelperWindowIntervals.positive b.shape agreement b.reserve bot top h b.degree 1 b.weight _
    b.width b.rate b.nodes b.pole b.slots pos hb ht narrow tail cert

theorem Verified.rectangle {b : Witness} (checked : Verified b) (rect : b.rect = true) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    KoalaRect.rectDebit h b.nodes b.pole (box seedCap b.v)+
        (∑ W ∈ range (b.top h),
          debitAt b.shape h (b.top h) W b.degree 1 b.weight (rectSlots (box seedCap b.v) (axis b.lower))) <
      KoalaRect.area (box seedCap b.v)*shapeSum b.shape (fun q j => b.top h+j-q*(131071-h)) := by
  have slots : b.slots = rectSlots (box seedCap b.v) (axis b.lower) := by
    funext k
    simp only [Witness.slots,rect,ite_true]
  simpa only [Witness.width,Witness.rate,slots,rect,ite_true,KoalaRect.rectDebit]
    using checked.raw_positive lo hi

theorem Verified.triangle {b : Witness} (checked : Verified b) (tri : b.rect = false) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    P1_7.debit h b.bank+
        (∑ W ∈ range (b.top h), debitAt b.shape h (b.top h) W b.degree 1 b.weight (triSlots b.v b.lower)) <
      triangle b.v*shapeSum b.shape (fun q j => b.top h+j-q*(131071-h)) := by
  have pos := checked.raw_positive lo hi
  have slots : b.slots = triSlots b.v b.lower := by
    funext k
    simp only [Witness.slots,tri,Bool.false_eq_true,ite_false]
  simpa only [Witness.width,Witness.rate,slots,tri,Bool.false_eq_true,ite_false,Nat.mul_left_comm h 2,
    Nat.mul_assoc,P1_7.debit,Witness.bank,Witness.shape] using pos

#print axioms Verified.rectangle
#print axioms Verified.triangle
end Research6966.HelperWindowCertificate

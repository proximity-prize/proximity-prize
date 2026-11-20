import ProximityPrize.SubmissionLower.Fast063
import ProximityPrize.SubmissionLower.C14BandsAt180255
set_option Elab.async false

/-! `K1_14_At.c5At`: the strict dimension test for the new 6916 band table (A = 180255).
Mechanical port of `Fast063` `K1_14_5` (support line at each band start) with 180265 -> 180255,
seeds 151/101/49/37, and regenerated moment data and support totals
(research/proximity-6916/c5at_support_cert.py; the port reproduces all eight official 69.15 totals,
and the unchanged high-band data blob equals the official one). UNBUILT. -/

section PackSource_K1_14_5AuxAt180255
set_option autoImplicit true
namespace K1_14_5At

open K1 K1_14 K1_14_At Finset
open scoped BigOperators

private theorem sum_arithmetic (n : ℕ) (a d : ℤ) :
    (∑ t ∈ range n, (a - 2*d*(t : ℤ))) = (n : ℤ)*(a - d*((n : ℤ)-1)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring

/-- For fixed derivative grade j and layer r, the positions used by the
left-endpoint support form the consecutive block j, ..., j+n-1. -/
private def supportCount (s : Shape) (lo j r : ℕ) : ℕ :=
  let offset := j*(131071-lo) + 2*lo*(j+r)
  let top := s.m*180255 + j
  min (s.B+1-j) (if offset < top then (top-offset-1)/(131071-lo)+1 else 0)

/-- Twice the sum of the signed widths in that block. -/
private def blockValue (s : Shape) (j r n : ℕ) (h : ℤ) : ℤ :=
  (n : ℤ) * (2*((s.m : ℤ)*180255+j) - (2*(j : ℤ)+n-1)*(131071-h) -
    4*((j : ℤ)+r)*h)

private def blockSlope (j r n : ℕ) : ℤ :=
  (n : ℤ) * ((2*(j : ℤ)+n-1) - 4*((j : ℤ)+r))

private def signedWidth (s : Shape) (h : ℤ) (q j r : ℕ) : ℤ :=
  (s.m : ℤ)*180255 + j - q*(131071-h) - 2*h*((j : ℤ)+r)

private def width (s : Shape) (h q j r : ℕ) : ℕ :=
  s.m*180255 + j - q*(131071-h) - 2*h*(j+r)

private def weight (s : Shape) (v r : ℕ) : ℕ :=
  slots s.U (r*v) - slots s.U ((r+1)*v)

private theorem width_ge_signed (s : Shape) {h : ℕ} (hh : h ≤ 131071) (q j r : ℕ) :
    signedWidth s h q j r ≤ (width s h q j r : ℤ) := by
  have cast_sub_le (a b : ℕ) : (a : ℤ) - b ≤ ((a-b : ℕ) : ℤ) := by omega
  have h₁ := cast_sub_le (s.m*180255+j) (q*(131071-h))
  have h₂ := cast_sub_le (s.m*180255+j-q*(131071-h)) (2*h*(j+r))
  unfold signedWidth width
  push_cast [Nat.cast_sub hh] at h₁ h₂
  linarith only [h₁, h₂]

private theorem blockValue_eq_sum (s : Shape) (h : ℤ) (j r n : ℕ) :
    blockValue s j r n h = ∑ t ∈ range n, 2 * signedWidth s h (j+t) j r := by
  calc
    _ = ∑ t ∈ range n,
        (2 * signedWidth s h j j r - 2*(131071-h)*(t : ℤ)) := by
      rw [sum_arithmetic]
      unfold blockValue signedWidth
      ring
    _ = _ := by
      apply sum_congr rfl
      intro t _
      unfold signedWidth
      push_cast
      ring

/-- Reorder the triangular (total grade, derivative grade) indexing. -/
private theorem shape_sum_flip {M : Type} [AddCommMonoid M]
    (s : Shape) (f : ℕ → ℕ → M) :
    (∑ q ∈ range (s.B+1), ∑ j ∈ range (min q s.J+1), f q j) =
      ∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1), f q j := by
  calc
    _ = ∑ q ∈ range (s.B+1), ∑ j ∈ range (s.J+1),
        if j ≤ q then f q j else 0 := by
      apply sum_congr rfl
      intro q _
      rw [← sum_filter]
      congr 1
      ext j
      simp only [mem_range, mem_filter, Nat.lt_succ_iff, le_min_iff]
      tauto
    _ = ∑ j ∈ range (s.J+1), ∑ q ∈ range (s.B+1),
        if j ≤ q then f q j else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [← sum_filter]
      congr 1
      ext q
      simp only [mem_filter, mem_range, mem_Ico]
      tauto

private theorem block_le (s : Shape) (v lo j r : ℕ) {h : ℕ} (hh : h ≤ 131071) :
    (weight s v r : ℤ) * blockValue s j r (supportCount s lo j r) h ≤
      ∑ q ∈ Ico j (s.B+1), 2 * (weight s v r : ℤ) * (width s h q j r : ℤ) := by
  let n := supportCount s lo j r
  let term (q : ℕ) := 2 * (weight s v r : ℤ) * (width s h q j r : ℤ)
  have hn : n ≤ s.B+1-j := Nat.min_le_left _ _
  rw [blockValue_eq_sum, mul_sum]
  calc
    _ ≤ ∑ t ∈ range n, term (j+t) := by
      apply sum_le_sum
      intro t _
      have ht := width_ge_signed s hh (j+t) j r
      unfold term
      rw [← mul_assoc, mul_comm (weight s v r : ℤ) 2]
      exact mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ ∑ t ∈ range (s.B+1-j), term (j+t) :=
      sum_le_sum_of_subset_of_nonneg (range_mono hn) (by intros; positivity)
    _ = _ := (sum_Ico_eq_sum_range term j (s.B+1)).symm

private def weightedSum (s : Shape) (v : ℕ) (f : ℕ → ℕ → ℤ) : ℤ :=
  ∑ j ∈ range (s.J+1), ∑ r ∈ range (s.U/v+1), (weight s v r : ℤ) * f j r

/-- Value of the doubled supporting line at the left endpoint. -/
def supportBase (s : Shape) (v lo : ℕ) : ℤ :=
  weightedSum s v fun j r => blockValue s j r (supportCount s lo j r) lo

/-- Slope of the doubled supporting line. -/
def supportSlope (s : Shape) (v lo : ℕ) : ℤ :=
  weightedSum s v fun j r => blockSlope j r (supportCount s lo j r)

private def gain (s : Shape) (v h : ℕ) : ℕ :=
  shapeSum s fun q j => ∑ r ∈ range (s.U/v+1), weight s v r * width s h q j r

private theorem support_le_gain (s : Shape) (v lo : ℕ) {h : ℕ} (hh : h ≤ 131071) :
    supportBase s v lo + ((h : ℤ)-lo) * supportSlope s v lo ≤ 2 * (gain s v h : ℤ) := by
  have hline : supportBase s v lo + ((h : ℤ)-lo) * supportSlope s v lo =
      weightedSum s v (fun j r => blockValue s j r (supportCount s lo j r) h) := by
    unfold supportBase supportSlope weightedSum
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro r _
    unfold blockValue blockSlope
    ring
  rw [hline]
  unfold gain shapeSum weightedSum
  push_cast
  simp only [mul_sum, ← mul_assoc]
  rw [shape_sum_flip]
  apply sum_le_sum
  intro j _
  rw [sum_comm]
  exact sum_le_sum fun r _ => block_le s v lo j r hh

private def nodeRow (k d : ℕ) : ℕ :=
  let n := min k ((d+1)/2)
  n*(d+1-n)

private theorem nodeRow_eq_sum (k d : ℕ) :
    (∑ i ∈ range k, (d-2*i)) = nodeRow k d := by
  let n := min k ((d+1)/2)
  have hnk : n ≤ k := Nat.min_le_left _ _
  have hnd : n ≤ (d+1)/2 := Nat.min_le_right _ _
  have hreduce : (∑ i ∈ range k, (d-2*i)) = ∑ i ∈ range n, (d-2*i) := by
    symm
    apply sum_subset (range_mono hnk)
    intro i hi hni
    simp only [mem_range, not_lt] at hi hni
    have hi' : (d+1)/2 ≤ i := by unfold n at hni; omega
    omega
  have hcast : ((∑ i ∈ range n, (d-2*i) : ℕ) : ℤ) =
      ∑ i ∈ range n, ((d : ℤ)-2*(i : ℤ)) := by
    rw [Nat.cast_sum]
    apply sum_congr rfl
    intro i hi
    have hit := mem_range.mp hi
    rw [Nat.cast_sub (by omega : 2*i ≤ d)]
    push_cast
    rfl
  have hclosed := sum_arithmetic n (d : ℤ) 1
  simp only [mul_one, one_mul] at hclosed
  have hn : n ≤ d+1 := by omega
  apply Int.ofNat_inj.mp
  rw [hreduce, hcast, hclosed]
  change _ = (↑(n*(d+1-n)) : ℤ)
  push_cast [Nat.cast_sub hn]
  ring

/-- Constant node debit, with an arithmetic progression summed at each q. -/
def nodeCost (s : Shape) : ℕ :=
  triangle s.U * 262144 *
    ∑ q ∈ range (s.B+1), nodeRow (min q s.J+1) (s.m+min q s.J-q)

/-- Coefficient of height in the two primary pole debits. -/
def poleSlope (s : Shape) : ℕ :=
  2*(s.U+1) * ∑ q ∈ range (s.B+1), (min q s.J+1)*((s.B+s.J-q)*(s.B-q))

private theorem debit_eq (s : Shape) (h : ℕ) :
    sourceDebit h s = nodeCost s + h * poleSlope s := by
  have hnode : shapeSum s (fun q i => s.m+min q s.J-(q+2*i)) =
      ∑ q ∈ range (s.B+1), nodeRow (min q s.J+1) (s.m+min q s.J-q) := by
    unfold shapeSum
    apply sum_congr rfl
    intro q _
    simpa only [Nat.sub_sub] using nodeRow_eq_sum (min q s.J+1) (s.m+min q s.J-q)
  have hpole : shapeSum s (fun q _ => (s.B+s.J-q)*(s.B-q)) =
      ∑ q ∈ range (s.B+1), (min q s.J+1)*((s.B+s.J-q)*(s.B-q)) := by
    unfold shapeSum
    simp only [sum_const, card_range, Nat.nsmul_eq_mul]
  unfold sourceDebit nodeCost poleSlope
  rw [hnode, hpole]
  ring

/-- Checking the starting slack and the slope suffices throughout a band
with this fixed terminal shape and tested seed degree. -/
theorem test_of_support (w : ℤ) {s : Shape} {v lo : ℕ}
    (hshape : terminalShapeNew w = s) (hv : (bandNew w).seedBound+1 = v)
    (hlo : (lo : ℤ) ≤ w) (hhi : w ≤ 131071)
    (hbase : 2 * ((nodeCost s : ℤ) + lo * (poleSlope s : ℤ)) < supportBase s v lo)
    (hslope : 2 * (poleSlope s : ℤ) ≤ supportSlope s v lo) :
    subbankDebitNew w < seedGainAt 180255 w := by
  have hw : w.toNat ≤ 131071 := by omega
  have hlo' : 0 ≤ (w.toNat : ℤ) - lo := by omega
  have hg : seedGainAt 180255 w = gain s v w.toNat := by
    have hU : (bandNew w).subbankSeeds = s.U := congrArg Shape.U hshape
    have hm : (bandNew w).multiplicity = s.m := congrArg Shape.m hshape
    simp only [seedGainAt, gain, weight, width, rawWidthAt, hshape, hv, hU, hm]
  have hplane := support_le_gain s v lo hw
  have hinc := mul_le_mul_of_nonneg_left hslope hlo'
  rw [hg, subbankDebitNew, hshape, debit_eq]
  have hcast : ((nodeCost s + w.toNat * poleSlope s : ℕ) : ℤ) < (gain s v w.toNat : ℤ) := by
    push_cast
    nlinarith only [hplane, hinc, hbase]
  exact_mod_cast hcast

end K1_14_5At
end PackSource_K1_14_5AuxAt180255

section PackSource_K1_14_5ProofAt180255
set_option autoImplicit true
namespace K1_14_5At

open K1 K1_14 K1_14_At

private def bridgeShape : Shape := ⟨836, 1164, 247, 19371⟩
private def pairedLowShape : Shape := ⟨358, 500, 105, 6798⟩
private def pairedMidShape : Shape := ⟨358, 500, 105, 4860⟩
private def pairedHighShape : Shape := ⟨358, 500, 105, 3913⟩

private def PositiveSupport (s : Shape) (v lo : ℕ) : Prop :=
  2 * ((nodeCost s : ℤ) + lo * (poleSlope s : ℤ)) < supportBase s v lo ∧
  2 * (poleSlope s : ℤ) ≤ supportSlope s v lo

open Finset
open scoped BigOperators

-- A recursive range sum for small closed checks, connected to the original Finset sums.
private def k145Sum {α : Type} [AddMonoid α] (f : ℕ → α) : ℕ → α
  | 0 => 0
  | n + 1 => k145Sum f n + f n

private theorem k145Sum_eq {α : Type} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    k145Sum f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp [k145Sum]
  | succ n ih => rw [k145Sum, Finset.sum_range_succ, ih]

private def k145SupportCount (s : Shape) (lo j r : ℕ) : ℕ :=
  let offset := j * (131071 - lo) + 2 * lo * (j + r)
  let top := s.m * 180255 + j
  min (s.B + 1 - j) (if offset < top then (top - offset - 1) / (131071 - lo) + 1 else 0)

private def k145NodeTerm (s : Shape) (q : ℕ) : ℕ :=
  let k := min q s.J + 1
  let d := s.m + min q s.J - q
  let n := min k ((d + 1) / 2)
  n * (d + 1 - n)

private def k145PoleTerm (s : Shape) (q : ℕ) : ℕ :=
  (min q s.J + 1) * ((s.B + s.J - q) * (s.B - q))

private theorem k145Node_eq (s : Shape) :
    nodeCost s = triangle s.U * 262144 * k145Sum (k145NodeTerm s) (s.B + 1) := by
  simp only [k145Sum_eq]
  rfl

private theorem k145Pole_eq (s : Shape) :
    poleSlope s = 2 * (s.U + 1) * k145Sum (k145PoleTerm s) (s.B + 1) := by
  simp only [k145Sum_eq]
  rfl

section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

-- On a diagonal t = j + r, j ranges backwards as r increases. Reindex
-- the rectangle so its two finite bounds can certify a single cutoff.
private theorem k145Diagonal (J R : ℕ) (f : ℕ → ℕ → ℤ) :
    (∑ j ∈ range (J+1), ∑ r ∈ range (R+1), f j r) =
      ∑ t ∈ range (J+R+1), ∑ r ∈ Ico (t-J) (min t R+1), f (t-r) r := by
  calc
    _ = ∑ r ∈ range (R+1), ∑ j ∈ range (J+1), f j r := sum_comm
    _ = ∑ r ∈ range (R+1), ∑ t ∈ Ico r (r+(J+1)), f (t-r) r := by
      apply sum_congr rfl
      intro r _
      rw [sum_Ico_eq_sum_range]
      simp
    _ = ∑ r ∈ range (R+1), ∑ t ∈ range (J+R+1),
        if r ≤ t ∧ t-r ≤ J then f (t-r) r else 0 := by
      apply sum_congr rfl
      intro r hr
      have hr' := mem_range.mp hr
      rw [← sum_filter]
      congr 1
      ext t
      simp only [mem_Ico, mem_filter, mem_range]
      omega
    _ = ∑ t ∈ range (J+R+1), ∑ r ∈ range (R+1),
        if r ≤ t ∧ t-r ≤ J then f (t-r) r else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro t _
      rw [← sum_filter]
      congr 1
      ext r
      simp only [mem_Ico, mem_filter, mem_range, Nat.lt_succ_iff, le_min_iff]
      omega

-- These two inequalities bracket the quotient in the original support
-- count. At the physical cap B only the lower inequality is necessary.
private theorem k145Quotient {B j D z T k : ℕ} (hd : 0 < D) (hj : j < k)
    (hb : k ≤ B) (hl : (k-1)*D+z < T) (hh : k=B ∨ T ≤ k*D+z) :
    min (B-j) (if j*D+z < T then (T-(j*D+z)-1)/D+1 else 0) = k-j := by
  have hjD : j*D ≤ (k-1)*D := Nat.mul_le_mul_right D (by omega)
  rw [ite_eq_left (by omega)]
  have hlow : k-1-j ≤ (T-(j*D+z)-1)/D := (Nat.le_div_iff_mul_le hd).2 (by
    rw [Nat.sub_mul]
    omega)
  rcases hh with rfl | hh
  · omega
  · have hupp : (T-(j*D+z)-1)/D < k-j := (Nat.div_lt_iff_lt_mul hd).2 (by
      rw [Nat.sub_mul]
      omega)
    omega

private def k145W (s : Shape) (v r : ℕ) : ℕ :=
  slots s.U (r*v) - slots s.U ((r+1)*v)

private def k145A (s : Shape) (lo t : ℕ) (slope : Bool) : ℤ :=
  if slope then -4*(t : ℤ) else 2*((s.m : ℤ)*180255) - 4*(t : ℤ)*lo
private def k145B (slope : Bool) : ℤ := if slope then 0 else 2
private def k145C (lo : ℕ) (slope : Bool) : ℤ := if slope then 1 else -(131071-(lo : ℤ))

private def k145Cell (s : Shape) (v lo : ℕ) (slope : Bool) (j r : ℕ) : ℤ :=
  let n : ℤ := k145SupportCount s lo j r
  (k145W s v r : ℤ) * (n * (k145A s lo (j+r) slope + k145B slope*j +
    k145C lo slope*(2*(j : ℤ)+n-1)))

private theorem k145Cells (s : Shape) (v lo : ℕ) (slope : Bool) :
    (if slope then supportSlope s v lo else supportBase s v lo) =
      ∑ j ∈ range (s.J+1), ∑ r ∈ range (s.U/v+1), k145Cell s v lo slope j r := by
  cases slope
  · change (∑ j ∈ range (s.J+1), ∑ r ∈ range (s.U/v+1), (k145W s v r : ℤ) * ((k145SupportCount s lo j r : ℤ) *
      (2*((s.m : ℤ)*180255+j) - (2*(j : ℤ)+k145SupportCount s lo j r-1)*(131071-lo) -
        4*((j : ℤ)+r)*lo))) = _
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro r _
    simp only [k145Cell, k145A, k145B, k145C, Bool.false_eq_true, ite_false, Nat.cast_add]
    ring
  · change (∑ j ∈ range (s.J+1), ∑ r ∈ range (s.U/v+1), (k145W s v r : ℤ) * ((k145SupportCount s lo j r : ℤ) *
      ((2*(j : ℤ)+k145SupportCount s lo j r-1)-4*((j : ℤ)+r)))) = _
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro r _
    simp only [k145Cell, k145A, k145B, k145C, ite_true, Nat.cast_add]
    ring

private def k145Cut (s : Shape) (lo t : ℕ) : ℕ :=
  min (s.B+1) ((s.m*180255+(t-(t-s.J))-2*lo*t-1)/(131071-lo)+1)

private def k145GoodCut (s : Shape) (v lo t : ℕ) : Prop :=
  let k := k145Cut s lo t
  let D := 131071-lo
  let jmax := t-(t-s.J)
  let jmin := t-min t (s.U/v)
  jmax < k ∧ k ≤ s.B+1 ∧ (k-1)*D + 2*lo*t < s.m*180255+jmin ∧
    (k=s.B+1 ∨ s.m*180255+jmax ≤ k*D+2*lo*t)

private instance (s : Shape) (v lo t : ℕ) : Decidable (k145GoodCut s v lo t) := by
  unfold k145GoodCut
  infer_instance

private theorem k145AtCut (s : Shape) (v lo t r : ℕ) (hd : lo < 131071)
    (h : k145GoodCut s v lo t) (hr : r ∈ Ico (t-s.J) (min t (s.U/v)+1)) :
    t-r ≤ k145Cut s lo t ∧ k145SupportCount s lo (t-r) r = k145Cut s lo t - (t-r) := by
  obtain ⟨hk, hb, hl, hh⟩ := h
  obtain ⟨ha, he⟩ := mem_Ico.mp hr
  have hrle : r ≤ t := by omega
  have hj : t-r < k145Cut s lo t := by omega
  refine ⟨by omega, ?_⟩
  unfold k145SupportCount
  rw [Nat.sub_add_cancel hrle]
  apply k145Quotient (by omega) hj hb (by omega)
  rcases hh with hcap | htop
  · exact Or.inl hcap
  · exact Or.inr (by omega)

-- Packed base-2^48 digits store the three weighted prefix moments at each
-- index. Their successive differences are verified against the slot counts.
private def k145Digit (data i r : ℕ) : ℕ :=
  (data >>> (48*(3*r+i))) % 281474976710656

private def k145MomStep (s : Shape) (v data r : ℕ) : Prop :=
  let w := k145W s v r
  k145Digit data 0 (r+1) = k145Digit data 0 r + w ∧
  k145Digit data 1 (r+1) = k145Digit data 1 r + w*r ∧
  k145Digit data 2 (r+1) = k145Digit data 2 r + w*r*r

private instance (s : Shape) (v data r : ℕ) : Decidable (k145MomStep s v data r) := by
  unfold k145MomStep
  infer_instance

private def k145All (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => k145All p n && p n

private theorem k145All_sound (p : ℕ → Prop) [DecidablePred p] (n : ℕ)
    (h : k145All (fun i => decide (p i)) n = true) : ∀ i < n, p i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    obtain ⟨h0,h1⟩ := Bool.and_eq_true_iff.mp h
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
    · exact ih h0 i hlt
    · exact of_decide_eq_true h1

private def k145Primitive (data i : ℕ) (x y z : ℤ) : ℤ :=
  x*k145Digit data 0 i + y*k145Digit data 1 i + z*k145Digit data 2 i

private theorem k145PrimStep (s : Shape) (v data r : ℕ) (x y z : ℤ)
    (h : k145MomStep s v data r) :
    k145Primitive data (r+1) x y z = k145Primitive data r x y z +
      (k145W s v r : ℤ)*(x+y*r+z*r*r) := by
  obtain ⟨h0,h1,h2⟩ := h
  simp only [k145Primitive, h0,h1,h2,Nat.cast_add,Nat.cast_mul]
  ring

private theorem k145Tel (f p : ℕ → ℤ) (a n : ℕ)
    (h : ∀ i < n, p (a+i+1) = p (a+i)+f (a+i)) :
    (∑ i ∈ range n, f (a+i)) = p (a+n)-p a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih (fun i hi => h i (by omega))]
    rw [← Nat.add_assoc, h n (by omega)]
    ring

-- If n=k-j and j=t-r, each weighted cell is w(r) times a quadratic in r.
private def k145PrimitiveAt (s : Shape) (lo data t : ℕ) (slope : Bool) (r : ℕ) : ℤ :=
  let k : ℤ := k145Cut s lo t
  let u := k-(t : ℤ)
  let a := k145A s lo t slope
  let b := k145B slope
  let c := k145C lo slope
  let e := a + b*t + c*((t : ℤ)+k-1)
  k145Primitive data r (u*e) (e-u*(b+c)) (-(b+c))

private def k145DiagValue (s : Shape) (v lo data t : ℕ) (slope : Bool) : ℤ :=
  k145PrimitiveAt s lo data t slope (min t (s.U/v)+1) -
    k145PrimitiveAt s lo data t slope (t-s.J)

private theorem k145OneDiag (s : Shape) (v lo data t : ℕ) (slope : Bool)
    (hd : lo < 131071) (ht : t < s.J+s.U/v+1) (hc : k145GoodCut s v lo t)
    (hm : ∀ r < s.U/v+1, k145MomStep s v data r) :
    (∑ r ∈ Ico (t-s.J) (min t (s.U/v)+1), k145Cell s v lo slope (t-r) r) =
      k145DiagValue s v lo data t slope := by
  let a := t-s.J
  let b := min t (s.U/v)+1
  have hab : a ≤ b := by
    change t-s.J ≤ min t (s.U/v)+1
    exact Nat.le.step (le_min (Nat.sub_le ..) (Nat.sub_le_iff_le_add'.2 (Nat.le_of_lt_succ ht)))
  change (∑ r ∈ Ico a b, _) = k145PrimitiveAt s lo data t slope b -
    k145PrimitiveAt s lo data t slope a
  rw [sum_Ico_eq_sum_range]
  conv_rhs => rw [← Nat.add_sub_of_le hab]
  apply k145Tel (fun r => k145Cell s v lo slope (t-r) r) (k145PrimitiveAt s lo data t slope) a (b-a)
  intro i hi
  let r := a+i
  have hmem : r ∈ Ico (t-s.J) (min t (s.U/v)+1) := by
    change r ∈ Ico a b
    exact mem_Ico.mpr ⟨by dsimp [r]; omega, by dsimp [r]; omega⟩
  obtain ⟨_, he⟩ := mem_Ico.mp hmem
  have hr : r ≤ t := by omega
  obtain ⟨hjk, hn⟩ := k145AtCut s v lo t r hd hc hmem
  change k145PrimitiveAt s lo data t slope (r+1) =
    k145PrimitiveAt s lo data t slope r + k145Cell s v lo slope (t-r) r
  simp only [k145PrimitiveAt, k145PrimStep _ _ _ r _ _ _ (hm r (by omega))]
  congr 1
  simp only [k145Cell, hn, Nat.cast_sub hjk, Nat.sub_add_cancel hr, Nat.cast_sub hr]
  ring

private theorem k145Eval (s : Shape) (v lo data : ℕ) (slope : Bool)
    (hd : lo < 131071)
    (hc : k145All (fun t => decide (k145GoodCut s v lo t)) (s.J+s.U/v+1) = true)
    (hm : k145All (fun r => decide (k145MomStep s v data r)) (s.U/v+1) = true) :
    (if slope then supportSlope s v lo else supportBase s v lo) =
      k145Sum (fun t => k145DiagValue s v lo data t slope) (s.J+s.U/v+1) := by
  rw [k145Cells, k145Diagonal, k145Sum_eq]
  apply sum_congr rfl
  intro t ht
  have hlt := mem_range.mp ht
  exact k145OneDiag s v lo data t slope hd hlt (k145All_sound _ _ hc t hlt)
    (k145All_sound _ _ hm)

private theorem k145BridgeNodeTotal :
    k145Sum (k145NodeTerm bridgeShape) 1165 = 66215380 := by decide +kernel

private theorem k145BridgePoleTotal :
    k145Sum (k145PoleTerm bridgeShape) 1165 = 127928356332 := by decide +kernel

private def k145BridgeData : ℕ :=
  0x75ffaebf400001d8bb4a8000000b2f439e0075feb73f400001d8b95b8000000b2f3fc00075ed4bc0780001d8963e4800000b2ef8f80075c692b3140001d847917a00000b2e591f00758b3a30da0001d7ce073800000b2d603500753bee3d2a0001d72a51a400000b2c0e3a0074d958c4fe0001d65d22e000000b2a632e007464219eea0001d5672d0e00000b285f110073dcee8b1c0001d449225000000b2601e300734463335c0001d303b4c800000b234ba400729b212b0c0001d197969800000b203c540071e1c7ef280001d00579e200000b1cd3f3007118f4e6460001ce4e10c800000b1912810070414360960001cc720d6c00000b14f7fe006f5b4c97e20001ca7221f000000b10846a006e67a7af8e0001c84f007600000b0bb7c5006d66e9b4980001c6095b2000000b06920f006c59a59d980001c3a1e41000000b011348006b406c4ac00001c1194d6800000afb3b70006a1bcc85dc0001be70494a00000af50a870068ec5302520001bba789d800000aee808d0067b28a5d220001b8bfc13400000ae79d8200666efb1ce60001b5b9a18000000ae061660065222bb1d20001b295dcde00000ad8cc390063cca075b40001af55257000000ad0ddfb00626edbabf40001abf82d5800000ac896ac0061095d81940001a87fa6b800000abff64c005f9ca40d300001a4ec43b200000ab6fcdb005e292b4efe0001a13eb66800000aadaa59005caf6d30ce00019d77b0fc00000aa3fec6005b2fe1860a00019997e59000000a99fa220059aafe0bb6000195a0064600000a8f9c6d00582136687000019190c54000000a84e5a7005692fc2c7000018d6ad4a000000a79d5d0005500bed1880001892ee68800000a6e6ce800536aebbb24000184ddad1a00000a62aaef0051d1ee364a00018077da7800000a568fe50050362f799a00017bfe20c400000a4a1bca004e9816a54e00017771322000000a3d4e9e004cf808c33a000172d1c0ae00000a302861004b5668c6cc00016e207e9000000a22a9130049b3978d0c0001695e1de800000a14d0b400480ff3dc9c0001648b50d800000a069f4400466bda65b800015fa8c982000009f814c30044c7a5c23600015ab73a08000009e93131004323ae7586000155b7548c000009d9f48e0041804aecb2000150a9cb30000009ca5eda003fddcf7e5e00014b8f5016000009ba7015003e3c8e6ac8000146689560000009aa283f003c9cd7dbc8000141364d30000009998758003afef9e4d000013bf929a8000009888d600039634082ec000136b1dcea000009773a570037c9f59cc2000131611918000009658e3d00363361029200012c07905400000953891200349fc86e36000126a5f4c0000009412ad600330f6f83220001213cf87e0000092e738900318297ce6400011bcd4db00000091b632b002ff980c6a400011657a67800000907f9bc002e7467cc24000110dcb4f8000008f4373c002cf38828c000010b5d2b52000008e01bab002b771b0fee000105d9bba8000008cba7090029ff579ebe00010053181c000008b6d95600288c72dbda0000fac9f2d0000008a1b29200271e9fb7860000f53efde60000088c32bd0025b60f0ba00000efb2eb800000087659d7002452ef9ba00000ea266dc00000086027e00022f56e14980000e49a36c8000008499cd800219db50d340000df0ef8ba00000832b8bf00204bed05ba0000d98565b80000081b7b95001f003c680a0000d3fe2fe400000803e55a001dbac7879e0000ce7a0960000007ebf60e001c7bb0a18a0000c8f9a44e000007d3adb1001b4317dc7c0000c37db2d0000007bb0c43001a111b48bc0000be06e708000007a211c40018e5d6e02c0000b895f31800000788be340017c16486480000b32b89220000076f11930016a3dc08260000adc85b48000007550be100158d531c760000a86d1bac0000073aad1e00147ddd63820000a31a7c700000071ff54a0013758c672e00009dd12fb600000704e4650012746f9af800009891e7a0000006e97a6f00117a945bf80000935d5650000006cdb76800108805f0e000008e342de8000006b19b50000f9ccd89fc00008917208a000006952627000eb8f2413200008406e0580000067857ed000ddc791a0200007f041f740000065b30a2000d0765018600007a0f90000000063db046000c39b6ce7200007529e41e0000061fd6d9000b736d411400007053cdf000000601a45b000ab485035400006b8dff98000005e318cc0009fcf8a8b4000066d92b38000005c4342c00094cc0ae500000623602f2000005a4f67b0008a3d37ade00005da538e8000005855fb9000802255eae000059277f3c000005656fe6000767a893aa000054bd88100000054527020006d44d3d5600005068058600000524850d0006480168d000004c27a9c0000005038a070005c2b10cd0000047fd26e0000004e235f00005444609a8000043e92f08000004c088c80004cca8294400003fec745a0000049e828f00045bbd1f2a00003c07a8f80000047c23450003f168887a0000383b7f04000004596aea00038d8bebee00003488a8a000000436597e00033006b9da000030efd7ee00000412ef010002d8b64c2c00002d71bf10000003ef2b7300028775e66c00002a0f1028000003cb0ed400023c1eb5bc000026c87d58000003a699240001f687d0d80000239eb8c200000381ca630001b68638160000209274880000035ca29100017becd56600001da462cc0000033721ae0001468c7c5200001ad535b00000031147ba00011633e9fe000018259f56000002eb14b50000eaafc5280000159651e0000002c4889f0000c3ca9e2800001327ff700000029da3780000a14ceef0000010db5a28000002766540000082fd1b0c00000eb1142a0000024ecdf70000689f6fa200000ca9df9800000226dd9d000051f6237200000ac66e94000001fe943200003ec156d6000009077340000001d5f1b600002ebf13c20000076d9fbe000001acf629000021ab4dc4000005f9a63000000183a18b0000173fe204000004ac38b800000159f3dc00000f3497440000038609780000012fed1c0000093f1de000000287ca92000001058d4b000005130fce000001b22e28000000dad46900000261f09e00000105e65c000000afc276000000db2d7a00000083a5500000008457720000002c1d260000002c1d2600000058935d0000000000000000000000000000002c7637000000000000000000000000000000000000

private theorem k145BridgeCuts :
    k145All (fun t => decide (k145GoodCut bridgeShape 151 2601 t)) 376 = true := by decide +kernel

private theorem k145BridgeMoments :
    k145All (fun r => decide (k145MomStep bridgeShape 145 k145BridgeData r)) 129 = true := by decide +kernel

private theorem k145BridgeBaseTotal : supportBase bridgeShape 151 2601 = 6540251279315699956328 := by
  have h := k145Eval bridgeShape 151 2601 k145BridgeData false (by decide) k145BridgeCuts k145BridgeMoments
  exact h.trans (by decide +kernel)

private theorem k145BridgeSlopeTotal : supportSlope bridgeShape 151 2601 = 30946677033297212 := by
  have h := k145Eval bridgeShape 151 2601 k145BridgeData true (by decide) k145BridgeCuts k145BridgeMoments
  exact h.trans (by decide +kernel)

private theorem bridge_test : PositiveSupport bridgeShape 151 2601 := by
  have hB : bridgeShape.B + 1 = 1165 := rfl
  rw [PositiveSupport, k145BridgeBaseTotal, k145BridgeSlopeTotal, k145Node_eq, k145Pole_eq, hB]
  have hn : k145Sum (k145NodeTerm bridgeShape) 1165 = 66215380 := k145BridgeNodeTotal
  have hp : k145Sum (k145PoleTerm bridgeShape) 1165 = 127928356332 := k145BridgePoleTotal
  rw [hn, hp]
  decide +kernel

private theorem k145LowNodeTotal :
    k145Sum (k145NodeTerm pairedLowShape) 501 = 5210801 := by decide +kernel

private theorem k145LowPoleTotal :
    k145Sum (k145PoleTerm pairedLowShape) 501 = 4343593800 := by decide +kernel

private def k145LowData : ℕ :=
  0x3f253dc8400001e3c01c600000160bb380003f22fb1f400001e3b779600000160b9280003f0027ff800001e3306580000016098690003eb546b6000001e2097c0000001604fd10003e44d5b6000001e047b800000015fdf600003db14481600001ddf014a0000015f47160003cfcf3a8a00001db078d00000015e86f30003c2a34cae00001d7931c40000015d9ef70003b3b4a95e00001d397bd80000015c8f220003a3268c6000001cf1a6be0000015b57740003911b426400001ca2022800000159f7ed00037db4290400001c4addc800000158708d00036911aec400001bec895000000156c15400035353531200001b87547200000154ea4200033c97a64600001b1b8ee000000152eb57000324fc49a200001aa9884c00000150c49300030c9def5200001a3190680000014e75f60002f3985a6c000019b3f6e60000014bff800002da065ef0000019310b780000014961310002c001e1c8000018a91dd0000001469b090002a5a3d8c80000181c7da000000143ad0800028b044aae0000178b7a9a00000140972e0002703a4f22000016f664700000013d597b0002555c0eb60000165d8ad400000139f3ef00023a7ec2e6000015c13d7800000136668a00021fb6b61800001521cc0e00000132b14c00020517439c0000147f86480000012ed4350001eab2d7ac000013dabbd80000012acf450001d09aef6c00001333bc7000000126a27c0001b6e018ea0000128ad7c2000001224dda00019d91f31e000011e05d800000011dd15f000184bf2dea000011349d5c000001192d0b00016c758a1a00001087e7080000011460de000154c1d96400000fda8a360000010f6cd800013daffe6800000f2cd6980000010a50f90001274aecb000000e7f1be0000001050d410001119ca8b000000dd1a9c0000000ffa1b00000fcae47c600000d24cfea000000fa0e460000e887f03a00000c78de10000000f453030000d530d93e00000bce23e4000000ee6fe70000c2af4aee00000b24f118000000e864f20000b1089e5000000a7d955e000000e232240000a0413d54000009d86068000000dbd77d0000905ca2d400000935a1e8000000d554fd0000815d5a9400000895a990000000ceaaa4000073450142000007f8c712000000c7d8720000661444760000075f4a20000000c0de67000059cae2b2000006c9826c000000b9bc8300004e67ab6200000637bfa8000000b272c6000043e87edc000005aa5186000000ab013000003a4a4e600000052187b8000000a367c1000031891c180000049db1f00000009ba6790000299ffb180000041f1fe000000093bd58000022890f5e000003a6213a0000008bac5e00001c3d8dd20000033305b000000083738b000016b5bc46000002c61cf40000007b12df000011e8f1760000025fb6b8000000728a5a00000dcd95080000020022ae00000069d9fc00000a591f8c000001a7b0880000006101c5000007801a7c00000156aff80000005801b500000536203c0000010d70b00000004ed9cc0000036ddc1a000000cc4262000000458a0a000002190a4e0000009374c00000003c126f0000012877fa00000063577c0000003272fb0000008c032a0000003c3a4800000028abae000000329ad40000001e6cd60000001ebc880000000a3ed80000000a3ed800000014a5890000000000000000000000000000000a66b1000000000000000000000000000000000000

private theorem k145LowCuts :
    k145All (fun t => decide (k145GoodCut pairedLowShape 101 3555 t)) 173 = true := by decide +kernel

private theorem k145LowMoments :
    k145All (fun r => decide (k145MomStep pairedLowShape 99 k145LowData r)) 68 = true := by decide +kernel

private theorem k145LowBaseTotal : supportBase pairedLowShape 101 3555 = 63573612244988680784 := by
  have h := k145Eval pairedLowShape 101 3555 k145LowData false (by decide) k145LowCuts k145LowMoments
  exact h.trans (by decide +kernel)

private theorem k145LowSlopeTotal : supportSlope pairedLowShape 101 3555 = 286515012517476 := by
  have h := k145Eval pairedLowShape 101 3555 k145LowData true (by decide) k145LowCuts k145LowMoments
  exact h.trans (by decide +kernel)

private theorem paired_low_test : PositiveSupport pairedLowShape 101 3555 := by
  have hB : pairedLowShape.B + 1 = 501 := rfl
  rw [PositiveSupport, k145LowBaseTotal, k145LowSlopeTotal, k145Node_eq, k145Pole_eq, hB]
  have hn : k145Sum (k145NodeTerm pairedLowShape) 501 = 5210801 := k145LowNodeTotal
  have hp : k145Sum (k145PoleTerm pairedLowShape) 501 = 4343593800 := k145LowPoleTotal
  rw [hn, hp]
  decide +kernel

private def k145MidData : ℕ :=
  0x46c7caa5f000016f1673f000000b4508300046c7470b0000016f151fa000000b4504c00046b791d64000016eec174000000b449990004692a2e50000016e8a9e0000000b4398500046595ba50000016df1e00000000b42010000460c99ffa000016d23096000000b3fd3a00045ad3859e000016c1f464000000b3d103000453c0d946000016ae7c2c000000b39b6b00044b9ed0b600001697dab0000000b35c720004427a696c0000167e22b2000000b314180004386068a00000166166f4000000b2c25d00042d5d5b4400001641ba38000000b267410004217d96040000161f2f40000000b202c4000414cd3546000015f9d8ce000000b194e6000407581d2a000015d1c9a4000000b11da70003f929f98a000015a71484000000b09d070003ea4e3dfa00001579cc30000000b013060003dad025c80000154a036a000000af7fa40003cabab3fc00001517ccf4000000aee2e10003ba18b358000014e33b90000000ae3cbd0003a8f4b658000014ac6200000000ad8d38000397591732000014735306000000acd4520003854ff7d6000014382164000000ac120b000372e341ee000013fadfdc000000ab46630003601ca6de000013bba130000000aa715a00034d059fc40000137a7822000000a992f0000339a76d78000013377774000000a8ab250003260b188c000012f2b1e8000000a7b9f900031239714c000012ac3a40000000a6bf6c0002fe3b0fbe00001264233e000000a5bb7e0002ea1853a20000121a7fa4000000a4ae2f0002d5d96472000011cf6234000000a3977f0002c186316200001182ddb0000000a2776e0002ad2671600000113504da000000a14dfc000298c1a314000010e5ea74000000a01b290002845f0ce000001095a1400000009edef500027005bce0000010443c000000009d996000025bbc88ea00000ff1cd760000009c4a6a0002478a0e8e00000f9e68640000009af21300023374b31600000f4a1f8c00000099905b00021f82a38600000ef505b000000098254200020bb9d49c00000e9f2d9200000096b0c80001f82002d000000e48a9f40000009532ed0001e4bab25400000df18d9800000093abb10001d18f2f1400000d99eb40000000921b140001bea28cb600000d41d5ae0000009081160001abf9a69a00000ce95fa40000008eddb7000199991fda00000c909be40000008d30f700018785634a00000c379d300000008b7ad6000175c2a37800000bde764a00000089bb5400016454daac00000b8539f400000087f2710001533fcae800000b2bfaf000000086202d00014286fde800000ad2cc000000008444880001322dc52200000a79bfe6000000825f820001223739c600000a20e96400000080711b000112a63cbe000009c85b3c0000007e79530001037d76ae0000097028300000007c782a0000f4bf57f40000091863020000007a6da00000e66e18a8000008c11e740000007859b50000d88bb89c0000086a6d48000000763c690000cb19ff5c0000081462400000007415bc0000be1a7c2e000007bf101e00000071e5ae0000b18e86120000076a89a40000006fac3f0000a5773bc200000716e1940000006d696f000099d583b2000006c42ab00000006b1d3e00008eaa0c100000067277ba00000068c7ac000083f54ac400000621db740000006668b9000079b77d70000005d268a000000064006500006ff0a970000005843200000000618eb0000066a09bda000005374a560000005f139a00005dc6e97e000004ebc4640000005c8f2300005562eee6000004a1b2ec0000005a014b00004d73d0560000045928b0000000576a12000045f879cc00000412387200000054c97800003eef9f00000003ccf4f4000000521f7d00003857bb640000038970f80000004f6c210000322f122400000347bf400000004caf6400002c73ae2600000307f28e00000049e94600002723620a000002ca1da40000004719c70000223bc82a0000028e53440000004440e700001dba429a00000254a630000000415ea60000199bfb280000021d292a0000003e7304000015dde35c000001e7eef40000003b7e010000127cb478000001b50a50000000387f9d00000f74ef78000001848e000000003577d800000cc2dd12000001568cc60000003266b200000a628db60000012b19640000002f4c2b0000084fd98e00000102469c0000002c284300000686607e000000dc273000000028fafa000005018a24000000b8cde200000025c450000003bc85d8000000984d74000000228445000002b24aac0000007ab8a80000001f3ad9000001dd976c0000006022400000001be80c00000138f29e000000489cfe000000188bde000000beaa82000000343ba400000015264f00000068d5120000002310f400000011b75f000000315002000000152fb00000000e3f0e00000011c0c00000000aaa9a0000000abd5c000000039474000000039474000000073249000000000000000000000000000000039dd5000000000000000000000000000000000000

private theorem k145MidCuts :
    k145All (fun t => decide (k145GoodCut pairedMidShape 49 8250 t)) 205 = true := by decide +kernel

private theorem k145MidMoments :
    k145All (fun r => decide (k145MomStep pairedMidShape 48 k145MidData r)) 100 = true := by decide +kernel

private theorem k145MidBaseTotal : supportBase pairedMidShape 49 8250 = 32989772600197692408 := by
  have h := k145Eval pairedMidShape 49 8250 k145MidData false (by decide) k145MidCuts k145MidMoments
  exact h.trans (by decide +kernel)

private theorem k145MidSlopeTotal : supportSlope pairedMidShape 49 8250 = 122735381981344 := by
  have h := k145Eval pairedMidShape 49 8250 k145MidData true (by decide) k145MidCuts k145MidMoments
  exact h.trans (by decide +kernel)

private theorem paired_mid_test : PositiveSupport pairedMidShape 49 8250 := by
  have hB : pairedMidShape.B + 1 = 501 := rfl
  rw [PositiveSupport, k145MidBaseTotal, k145MidSlopeTotal, k145Node_eq, k145Pole_eq, hB]
  have hn : k145Sum (k145NodeTerm pairedMidShape) 501 = 5210801 := k145LowNodeTotal
  have hp : k145Sum (k145PoleTerm pairedMidShape) 501 = 4343593800 := k145LowPoleTotal
  rw [hn, hp]
  decide +kernel

private def k145HighData : ℕ :=
  0x343f8617300000fe090cf00000074e857000343af339000000fdfde6400000074e6a40003428a179000000fdd0ce400000074dfb40003408cfa5700000fd81b8500000074d36b00033dc05e8f00000fd114f900000074c1c900033a2ca6cc00000fc803f200000074aace000335da158c00000fbcf322000000748e7a000330d0cd3700000fafed3b000000746ccd00032b18d01f00000fa0fcef0000007445c7000324ba008000000f902cf000000074196800031dbc208000000f7d87f000000073e7b000031626d22f00000f6918a100000073b09f00030e01978700000f52e9b500000073743500030553d26c00000f3b05de0000007332720002fc24c4ac00000f2177ce00000072eb560002f27b8fff00000f064a37000000729ee10002e85f360700000ee987cb000000724d130002ddd6985000000ecb3b3c00000071f5ec0002d2e8785000000eab6f3c00000071996c0002c79b776700000e8a2e7d0000007137930002bbf616df00000e6783b100000070d0610002affeb7ec00000e43798a0000007063d60002a3bb9bac00000e1e1aba0000006ff1f200029732e32700000df771f30000006f7ab500028a6a8f4f00000dcf89e70000006efe1f00027d68810000000da66d480000006e7c3000027032790000000d7c26c80000006df4e8000262ce17ff00000d50c1190000006d684700025540de9700000d2446ed0000006cd64d000247902d4c00000cf6c2f60000006c3efa000239c1448c00000cc83fe60000006ba24e00022bd944af00000c98c86f0000006b004900021ddd2df700000c6867430000006a58eb00020fd1e09000000c37271400000069ac34000201bc1c9000000c05129400000068fa240001f3a081f700000bd234750000006842bb0001e58390af00000b9e97690000006785f90001d769a88c00000b6a462200000066c3de0001c957094c00000b354b5200000065fc6a0001bb4fd29700000affb1ab000000652f9d0001ad5803ff00000ac983df000000645d7700019f737d0000000a92cca00000006385f8000191a5fd0000000a5b96a000000062a920000183f3234f00000a23ec9100000061c6ef0001765e6f27000009ebd92500000060df65000168eb3fac000009b3670e0000005ff28200015b9cd3ec0000097aa0fe0000005f004600014e764adf0000094191a70000005e08b10001417aa3670000090843bb0000005d0bc3000134acbc50000008cec1ec0000005c097c0001280f54500000089516ec0000005b01dc00011ba50a070000085b4d6d00000059f4e300010f705bff00000821702100000058e29100010373a8ac000007e789ba00000057cae60000f7b12e6c000007ada4ea00000056ade20000ec2b0b8700000773cc63000000558b850000e0e33e2f0000073a0ad70000005463cf0000d5dba480000007006af80000005336c00000cb15fc80000006c6f7780000005204580000c093e41f0000068dbb0900000050cc970000b656d93700000654c05d0000004f8f7d0000ac60398c0000061c12260000004e4d0a0000a2b142cc000005e3bb160000004d053e0000994b128f000005abc5df0000004bb8190000902ea657000005743d330000004a659b0000875cdb900000053d2bc4000000490dc400007ed66f90000005069c4400000047b0940000769bff97000004d09965000000464e0b00006eae08cf0000049b2dd900000044e6290000670ce84c0000046664520000004378ee00005fb8db0c00000432478200000042065a000058b1fdf7000003fee21b000000408e6d000051f84ddf000003cc3ecf0000003f112700004b8ba7800000039a68500000003d8e880000456bc7800000036969500000003c069000003f984a6f000003394c810000003a793f00003a10acc70000030a1c9500000038e695000034d44aec000002dbe43e000000374e9200002fe2612c000002aeae2e00000035b13600002b3a0bbf000002828517000000340e81000026da46c70000025773ab000000326673000022c1ee500000022d849c00000030b90c00001eefbe5000000204c29c0000002f064c00001b6252a7000001dd385d0000002d4e3300001818271f000001b6f0910000002b90c10000150f976c00000191f5ea00000029cdf600001246df2c0000016e531a0000002805d200000fbc19e70000014c12d300000026385500000d6d430f0000012b3fc700000024657f00000b5836000000010be4a8000000228d500000097aae00000000ee0c2800000020afc8000007d2463f000000d1c0f90000001ecce70000065c79d7000000b70dcd0000001ce4ad00000516a3cc0000009dfd560000001af71a000003fdff0c000000869a4600000019042e0000030fa66f00000070ef4f000000170be90000024894b70000005d0723000000150e4b000001a5a4900000004aec74000000130b540000012390900000003aa9f4000000110304000000bef3370000002c4a550000000ef55b0000007446ef0000001fd8490000000ce2590000003fe60c000000155e820000000ac9fe0000001e0acc0000000ce7b200000008ac4a0000000acf57000000067e8b00000006893d000000022dbf000000022dbf0000000460d7000000000000000000000000000000023318000000000000000000000000000000000000

private theorem k145HighCuts :
    k145All (fun t => decide (k145GoodCut pairedHighShape 37 24000 t)) 211 = true := by decide +kernel

private theorem k145HighMoments :
    k145All (fun r => decide (k145MomStep pairedHighShape 37 k145HighData r)) 106 = true := by decide +kernel

private theorem k145HighBaseTotal : supportBase pairedHighShape 37 24000 = 22565639861695424700 := by
  have h := k145Eval pairedHighShape 37 24000 k145HighData false (by decide) k145HighCuts k145HighMoments
  exact h.trans (by decide +kernel)

private theorem k145HighSlopeTotal : supportSlope pairedHighShape 37 24000 = 76379217149100 := by
  have h := k145Eval pairedHighShape 37 24000 k145HighData true (by decide) k145HighCuts k145HighMoments
  exact h.trans (by decide +kernel)

private theorem paired_high_test : PositiveSupport pairedHighShape 37 24000 := by
  have hB : pairedHighShape.B + 1 = 501 := rfl
  rw [PositiveSupport, k145HighBaseTotal, k145HighSlopeTotal, k145Node_eq, k145Pole_eq, hB]
  have hn : k145Sum (k145NodeTerm pairedHighShape) 501 = 5210801 := k145LowNodeTotal
  have hp : k145Sum (k145PoleTerm pairedHighShape) 501 = 4343593800 := k145LowPoleTotal
  rw [hn, hp]
  decide +kernel

end

/-- The strict inequality (T) for all four native terminal subbanks. -/
theorem proof : K1_14_At.c5At := by
  intro w hlo hhi
  have hw : w ≤ 131071 := by omega
  by_cases hb : w ≤ 3554
  · exact test_of_support w
      (by simp [terminalShapeNew, bandNew, hb, bridgeShape])
      (by simp [bandNew, hb]) hlo hw bridge_test.1 bridge_test.2
  by_cases hl : w ≤ 8249
  · exact test_of_support w
      (by simp [terminalShapeNew, bandNew, hb, hl, pairedLowShape])
      (by simp [bandNew, hb, hl]) (by omega) hw paired_low_test.1 paired_low_test.2
  by_cases hm : w ≤ 23999
  · exact test_of_support w
      (by simp [terminalShapeNew, bandNew, hb, hl, hm, pairedMidShape])
      (by simp [bandNew, hb, hl, hm]) (by omega) hw paired_mid_test.1 paired_mid_test.2
  · exact test_of_support w
      (by simp [terminalShapeNew, bandNew, hb, hl, hm, pairedHighShape])
      (by simp [bandNew, hb, hl, hm]) (by omega) hw paired_high_test.1 paired_high_test.2

end K1_14_5At
end PackSource_K1_14_5ProofAt180255

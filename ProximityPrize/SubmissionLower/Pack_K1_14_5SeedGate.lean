import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast023
set_option Elab.async false

section PackSource_K1_14_5Aux
set_option autoImplicit true
namespace K1_14_5

open K1_14 Finset
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
  let top := s.m*180236 + j
  min (s.B+1-j) (if offset < top then (top-offset-1)/(131071-lo)+1 else 0)

/-- Twice the sum of the signed widths in that block. -/
private def blockValue (s : Shape) (j r n : ℕ) (h : ℤ) : ℤ :=
  (n : ℤ) * (2*((s.m : ℤ)*180236+j) - (2*(j : ℤ)+n-1)*(131071-h) -
    4*((j : ℤ)+r)*h)

private def blockSlope (j r n : ℕ) : ℤ :=
  (n : ℤ) * ((2*(j : ℤ)+n-1) - 4*((j : ℤ)+r))

private def signedWidth (s : Shape) (h : ℤ) (q j r : ℕ) : ℤ :=
  (s.m : ℤ)*180236 + j - q*(131071-h) - 2*h*((j : ℤ)+r)

private def width (s : Shape) (h q j r : ℕ) : ℕ :=
  s.m*180236 + j - q*(131071-h) - 2*h*(j+r)

private def weight (s : Shape) (v r : ℕ) : ℕ :=
  slots s.U (r*v) - slots s.U ((r+1)*v)

private theorem width_ge_signed (s : Shape) {h : ℕ} (hh : h ≤ 131071) (q j r : ℕ) :
    signedWidth s h q j r ≤ (width s h q j r : ℤ) := by
  have cast_sub_le (a b : ℕ) : (a : ℤ) - b ≤ ((a-b : ℕ) : ℤ) := by omega
  have h₁ := cast_sub_le (s.m*180236+j) (q*(131071-h))
  have h₂ := cast_sub_le (s.m*180236+j-q*(131071-h)) (2*h*(j+r))
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
    (hshape : terminalShape w = s) (hv : (band w).seedBound+1 = v)
    (hlo : (lo : ℤ) ≤ w) (hhi : w ≤ 131071)
    (hbase : 2 * ((nodeCost s : ℤ) + lo * (poleSlope s : ℤ)) < supportBase s v lo)
    (hslope : 2 * (poleSlope s : ℤ) ≤ supportSlope s v lo) :
    subbankDebit w < seedGain w := by
  have hw : w.toNat ≤ 131071 := by omega
  have hlo' : 0 ≤ (w.toNat : ℤ) - lo := by omega
  have hg : seedGain w = gain s v w.toNat := by
    have hU : (band w).subbankSeeds = s.U := congrArg Shape.U hshape
    have hm : (band w).multiplicity = s.m := congrArg Shape.m hshape
    simp only [seedGain, gain, weight, width, rawWidth, hshape, hv, hU, hm]
  have hplane := support_le_gain s v lo hw
  have hinc := mul_le_mul_of_nonneg_left hslope hlo'
  rw [hg, subbankDebit, hshape, debit_eq]
  have hcast : ((nodeCost s + w.toNat * poleSlope s : ℕ) : ℤ) < (gain s v w.toNat : ℤ) := by
    push_cast
    nlinarith only [hplane, hinc, hbase]
  exact_mod_cast hcast

end K1_14_5
end PackSource_K1_14_5Aux

section PackSource_K1_14_5Proof
set_option autoImplicit true
namespace K1_14_5

open K1_14

private def band0Shape : Shape := ⟨836, 1164, 247, 22171⟩
private def bridgeShape : Shape := ⟨836, 1164, 247, 21937⟩
private def pairedLowShape : Shape := ⟨358, 500, 105, 7650⟩
private def pairedMidShape : Shape := ⟨358, 500, 105, 5202⟩
private def pairedHighShape : Shape := ⟨358, 500, 105, 4581⟩

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
  let top := s.m * 180236 + j
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
  if slope then -4*(t : ℤ) else 2*((s.m : ℤ)*180236) - 4*(t : ℤ)*lo
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
      (2*((s.m : ℤ)*180236+j) - (2*(j : ℤ)+k145SupportCount s lo j r-1)*(131071-lo) -
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
  min (s.B+1) ((s.m*180236+(t-(t-s.J))-2*lo*t-1)/(131071-lo)+1)

private def k145GoodCut (s : Shape) (v lo t : ℕ) : Prop :=
  let k := k145Cut s lo t
  let D := 131071-lo
  let jmax := t-(t-s.J)
  let jmin := t-min t (s.U/v)
  jmax < k ∧ k ≤ s.B+1 ∧ (k-1)*D + 2*lo*t < s.m*180236+jmin ∧
    (k=s.B+1 ∨ s.m*180236+jmax ≤ k*D+2*lo*t)

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

private theorem k145Band0NodeTotal :
    k145Sum (k145NodeTerm band0Shape) 1165 = 66215380 := by decide +kernel

private theorem k145Band0PoleTotal :
    k145Sum (k145PoleTerm band0Shape) 1165 = 127928356332 := by decide +kernel

private def k145Band0Data : ℕ :=
  0xa9b39caaa9000288f8d85500000ea6c2d600a9b1859205000288f4da0f00000ea6bb3500a9984be898000288c44c4600000ea65dc000a9632cb3b80002885d460e00000ea595f200a91301bb59000287c09c1900000ea463cb00a8a8a24959000286ef231900000ea2c74b00a824e32980000285e9afc000000ea0c07200a78896a980000284b116c000000e9e4f4000a6d48c98f5000283462ccb00000e9b73b500a609924965000281a9c69300000e982dd100a528728e4000027fdcb8ca00000e947d9400a431f5bce000027ddfd82200000e9062fe00a326e1ac8900027bb3f94d00000e8bde0f00a207f9b66900027959f0fd00000e86eec700a0d5feb598000276d293e400000e819526009f91af07180002741eb6b400000e7bd12c009e3bc689d50002713f2e1f00000e75a2d9009cd4fe9ea500026e34ced700000e6f0a2d009b5e0e284800026b006d8e00000e6807280099d7a98b68000267a2def600000e6099ca00984282ae990002641cf7c100000e58c21300969f48fa590002606f8ca100000e5080030094eea9591000025c9b724800000e47d39a0093314e3710000258a17d6800000e3ebcd8009167df82950002548282b300000e353bbd008f9302abc50002503f56db00000e2b5049008db35aa4b000024bd8ce9200000e20fa7c008bc987e1500002474fbe8a00000e163a560089d6285789000242a4fb7500000e0b0fd70087d9d77f2900023dd95a0500000dff7aff0085d52e51e8000238edaeec00000df37bce0083c8c34b68000233e2cedc00000de712440081b52a693500022eb98e8700000dda3e61007f9af52ac500022972c29f00000dcd0025007d7ab291780002240f3fd600000dbf5790007b54ef209800021e8fdade00000db144a200792a34dd59000218f5686900000da2c75b0076fb0b4ed900021340bd2900000d93dfbb0074c7f77e2000020d72add000000d848dc20072917bf6200002078c0f1000000d74d17000705818c3b50002018db59b00000d64aac5006e1c4b75a50001fb78762300000d5419c1006bde8f1ca00001f54d255a00000d431e6400699f5c4b400001ef0c97f200000d31b8ae00675f2916090001e8b7a29d00000d1fe89f00651e6913690001e24f1a0d00000d0dae370062dd8d5bb80001dbd3d2f400000cfb097600609d0489380001d546a20400000ce7fa5c005e5d3ab8150001cea85bef00000cd480e9005c1e9986650001c7f9d56700000cc09d1d0059e18814280001c13be31e00000cac4ef80057a66b03480001ba6f59c600000c97967a00556da477990001b3950e1100000c8273a30053379416d90001acadd4b100000c6ce6730051049708b00001a5ba825800000c56eeea004ed507f6b000019ebbebb800000c408d08004ca93f0c55000197b2e58300000c29c0cd004a8191f705000190a0446b00000c128a3900485e53e61000018984dd2200000bfae94c00463fd58ab000018261845a00000be2de0600442665180900017b370ec500000bca68670042124e432900017406511500000bb1886f004003da430800016cd01ffc00000b983e1e003dfb4fd08800016595502c00000b7e8974003bf8f3267500015e56b65700000b646a710039fd06018500015715272f00000b49e115003807c7a05800014fd1776600000b2eed6000361974c3780001488c7bae00000b138f5200343247ad590001414708b900000af7c6eb00325278225900013a01f33900000adb942b00307a3b68c0000132be0fe000000abef712002ea9c448c000012b7c336000000aa1efa0002ce1430c750001243d326b00000a847dd5002b20e57fe500011d01e1b300000a66a1b1002968d6f100000115cb15ea00000a485b340027b9402fa000010e99a3c200000a29aa5e002612478d890001076e5fed00000a0a8f2f00247410de690001004a1f1d000009eb09a70022debd77d80000f92db604000009cb19c60021526c31580000f219f954000009aabf8c001fcf3964550000eb0fbdbf00000989faf9001e553eec250000e40fd7f700000968cc0d001ce49426080000dd1b1cae0000094732c8001b7d4df1280000d6326096000009252f2a001a1f7eae990000cf56786100000902c1330018cb3641590000c88838c1000008dfe8e3001780820e500000c1c87668000008bca63a00163f6cfc500000bb18060800000898f938001507ff74150000b477bc5300000874e1dd0013da3f60450000ade86dfb0000085060290012b6302d700000a76aefb20000082b741c00119bd2ca100000a100162a000008061db600108b25a68900009aa8b615000007e05cf7000f8424b52900009465a425000007ba31df000e86c96a2800008e37b50c000007939c6e000d930abba80000881fbd7c0000076c9ca4000ca8dd21b50000821e9227000007453281000bc832964500007c3507bf0000071d5e05000af0fa953800007663f2f6000006f51f30000a23221c58000070ac287e000006cc760200095e93ab5900006b0e7d09000006a3627b0008a33743d90000658bc54900000679e49b0007f0f2696000006024d5f00000064ffc62000747a8216000005ada83b000000625a9d00006a738f335000055ada33b000005faece500060f82e8250000509f0943000005cfc5a1000580618b6000004baf8a7a000005a434040004f9adea00000046dffb9200000578380e00047b3e930900004231313d0000054bd1bf000404e7976900003da4002d0000051f01170003967a89f8000039393d14000004f1c61600032fc67f78000034f1bca4000004c420bc0002d0980e95000030ce538f000004961109000278b94fe500002ccfd6870000046796fd000227f1dde8000028f71a3e00000438b2980001de06d50800002544f3660000040963da00019abad399000021ba36b1000003d9aac300015dcdf9d900001e57b8d1000003a98753000126fde9f000001b1e4e7800000378f98a0000f605c7f00000180ecc580000034801680000ca9e39d50000152a0723000003169eed0000a47d678500001270d38b000002e4d21900008356fad000000fe40642000002b29aec000066dc1f7000000d8473fa0000027ff96600004ebb830900000b52f1650000024ced8700003aa1552900000950533500000219774f00002a3747480000077d6e1c000001e596be00001d248cc8000005db16cc000001b14bd40000130ddaf50000046a21f70000017c969100000b9569050000032b644f0000014776f50000065af0180000021fb28600000111ed00000002fbab3800000147e14e000000dbf8b2000001125759000000a4c559000000a59a0b0000003733590000003733590000006ed10b000000000000000000000000000000379db2000000000000000000000000000000000000

private theorem k145Band0Cuts :
    k145All (fun t => decide (k145GoodCut band0Shape 165 2564 t)) 382 = true := by decide +kernel

private theorem k145Band0Moments :
    k145All (fun r => decide (k145MomStep band0Shape 165 k145Band0Data r)) 135 = true := by decide +kernel

private theorem k145Band0BaseTotal : supportBase band0Shape 165 2564 = 8562631959199546459350 := by
  have h := k145Eval band0Shape 165 2564 k145Band0Data false (by decide) k145Band0Cuts k145Band0Moments
  exact h.trans (by decide +kernel)

private theorem k145Band0SlopeTotal : supportSlope band0Shape 165 2564 = 40012949540076582 := by
  have h := k145Eval band0Shape 165 2564 k145Band0Data true (by decide) k145Band0Cuts k145Band0Moments
  exact h.trans (by decide +kernel)

private theorem band0_test : PositiveSupport band0Shape 165 2564 := by
  have hB : band0Shape.B + 1 = 1165 := rfl
  rw [PositiveSupport, k145Band0BaseTotal, k145Band0SlopeTotal, k145Node_eq, k145Pole_eq, hB]
  have hn : k145Sum (k145NodeTerm band0Shape) 1165 = 66215380 := k145Band0NodeTotal
  have hp : k145Sum (k145PoleTerm band0Shape) 1165 = 127928356332 := k145Band0PoleTotal
  rw [hn, hp]
  decide +kernel

private theorem k145BridgeNodeTotal :
    k145Sum (k145NodeTerm bridgeShape) 1165 = 66215380 := by decide +kernel

private theorem k145BridgePoleTotal :
    k145Sum (k145PoleTerm bridgeShape) 1165 = 127928356332 := by decide +kernel

private def k145BridgeData : ℕ :=
  0xad06b753db0002886e77c300000e5802bb00ad06865ac00002886e1c4000000e58021000acf52676c00002884d67c000000e57c48000acc8389a30000287f834d000000e5722f000ac808e71f00002876f4b7000000e561d6000ac1ef752e0000286b373a000000e54b3d000aba44039e0000285c5756000000e52e64000ab1133cbd0000284a618b000000e50b4b000aa669a559000028356259000000e4e1f2000a9a539cc00000281d6640000000e4b259000a8cdd5cc00000280279c0000000e47c80000a7e12f9a7000027e4a959000000e44067000a6e006243000027c4018b000000e3fe0e000a5cb15fe2000027a08ed6000000e3b575000a4a3196520000277a5dba000000e3669c000a368c83e1000027517ab7000000e31183000a21cd815d00002725f24d000000e2b62a000a0bffc214000026f7d0fc000000e254910009f52e53d4000026c72344000000e1ecb80009dd641eeb00002693f5a5000000e17e9f0009c4abe6270000265e549f000000e10a460009ab1046d6000026264cb2000000e08fad0009909bb8c6000025ebea5e000000e00ed4000975588e45000025af3a23000000df87bb00095950f421000025704881000000defa6200093c8ef1a80000252f21f8000000de66c900091f1c68a8000024ebd308000000ddccf000090103156f000024a66831000000dd2cd70008e24c8ecb0000245eedf3000000dc867e0008c302460a0000241570ce000000dbd9e50008a32d86fa000023c9fd42000000db270c000882d777e90000237c9fcf000000da6df30008620919a50000232d64f5000000d9ae9a000840cb477c000022dc5934000000d8e90100081f26b73c00002289890c000000d81d280007fd23f9330000223500fd000000d74b0f0007dacb782f000021decd87000000d672b60007b825797e00002186fb2a000000d5941d0007953a1cee0000212d9666000000d4af44000772115ccd000020d2abbb000000d3c42b00074eb30de90000207647a9000000d2d2d200072b26df900000201876b0000000d1db39000707745b9000001fb94550000000d0dd600006e3a2e63700001f58c009000000cfd9470006bfb9be5300001ef6f35b000000ceceee00069bbffd3200001e93ebc6000000cdbe55000677bc96a200001e2fb5ca000000cca77c000653b658f100001dca5de7000000cb8a6300062fb3eced00001d63f09d000000ca670a00060bbbd5e400001cfc7a6c000000c93d710005e7d471a400001c9407d4000000c80d980005c403f87b00001c2aa555000000c6d77f0005a0507d3700001bc05f6f000000c59b2600057cbfed2600001b5542a2000000c4588d00055958101600001ae95b6e000000c30fb40005361e885500001a7cb653000000c1c09b00051318d2b100001a0f5fd1000000c06b420004f04c4678000019a16468000000bf0fa90004cdbe157800001932d098000000bdadd00004ab734bff000018c3b0e1000000bc45b700048970d0db0000185411c3000000bad75e000467bb655a000017e3ffbe000000b962c500044657a54a000017738752000000b7e7ec0004254a06f900001702b4ff000000b666d300040496db35000016919545000000b4df7a0003e4424d4c0000162034a4000000b351e10003c450630c000015ae9f9c000000b1be080003a4c4fcc30000153ce2ad000000b023ef000385a3d53f000014cb0a57000000ae8396000366f081ce00001459231a000000acdcfd000348ae723e000013e73976000000ab302400032ae0f0dd0000137559eb000000a97d0b00030d8b22790000130390f9000000a7c3b20002f0b0066000001291eb20000000a604190002d45276600000122074e0000000a43e400002b87526c7000011af3ab9000000a2722700029d1aa6630000113e492b000000a09fce000282455e82000010cdacb60000009ec735000267f792f20000105d71da0000009ce85c00024e33620100000feda5170000009b0343000234fac47d00000f7e52ed0000009917ea00021c4f8db400000f0f87dc000000972651000204336b7400000ea15064000000952e780001eca7e60b00000e33b90500000093305f0001d5ae604700000dc6ce3f000000912c060001bf48177600000d5a9c920000008f216d0001a976236600000cef307e0000008d109400019439766500000c8496830000008af97b00017f92dd4100000c1adb2100000088dc2200016b82ff4800000bb20ad800000086b8890001580a5e4800000b4a3228000000848eb000014529568f00000ae35d91000000825e97000132e01eeb00000a7d999300000080283e0001212ec8aa00000a18f2ae0000007deba5000110153f9a000009b575620000007ba8cc0000ff934a09000009532e2f000000795fb30000efa888c5000008f2299500000077105a0000e054771c00000892741400000074bac10000d1966adc000008341a2c000000725ee80000c36d9453000007d7285d0000006ffccf0000b5d8fe4f0000077bab270000006d94760000a8d78e1e00000721af0a0000006b25dd00009c68038e000006c9408600000068b10400009088f8ed000006726c1b0000006635eb00008538e3090000061d3e4900000063b49200007a761130000005c9c390000000612cf90000703ead300000057808700000005e9f2000006690bb570000052819690000005c0b0700005d6a1a73000004da02fb0000005970ae000054c883d20000048dd1a600000056d01500004ca98b420000044391ea00000054293c0000450a9f11000003fb5047000000517c2300003de9080d000003b5193d0000004ec8ca00003741e98400000370f94c0000004c0f310000311241440000032efcf4000000494f5800002b56e79b000002ef30b500000046893f0000260c8f57000002b1a10f00000043bce60000212fc5c6000002765a8200000040ea4d00001cbcf2b60000023d698e0000003e1174000018b0587500000206dab30000003b325b0000150613d1000001d2ba71000000384d02000011ba1c18000001a1154800000035616900000ec8431800000171f7b8000000326f9000000c2c351f000001456e410000002f7777000009e178fb0000011b85630000002c791e000007e36ffa000000f4499e0000002974850000062d55ea000000cfc7720000002669ac000004ba4119000000ae0b5f0000002358930000038522550000008f21e500000020413a00000288c4ec0000007317840000001d23a1000001bfceac00000059f8bc00000019ffc800000124bfe300000043d20d00000016d5af000000b1f35f00000030aff700000013a556000000619e6e000000209efa000000106ebd0000002dd0de00000013ab960000000d31e40000001074fd00000009e24b00000009eecb000000034f99000000034f9900000006a5720000000000000000000000000000000355d90000000000000000000000000000000000000

private theorem k145BridgeCuts :
    k145All (fun t => decide (k145GoodCut bridgeShape 160 2601 t)) 385 = true := by decide +kernel

private theorem k145BridgeMoments :
    k145All (fun r => decide (k145MomStep bridgeShape 160 k145BridgeData r)) 138 = true := by decide +kernel

private theorem k145BridgeBaseTotal : supportBase bridgeShape 160 2601 = 8383712375507560245140 := by
  have h := k145Eval bridgeShape 160 2601 k145BridgeData false (by decide) k145BridgeCuts k145BridgeMoments
  exact h.trans (by decide +kernel)

private theorem k145BridgeSlopeTotal : supportSlope bridgeShape 160 2601 = 38950407056429882 := by
  have h := k145Eval bridgeShape 160 2601 k145BridgeData true (by decide) k145BridgeCuts k145BridgeMoments
  exact h.trans (by decide +kernel)

private theorem bridge_test : PositiveSupport bridgeShape 160 2601 := by
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
  0x5de6841e4000029836d88000001beaa960005dd1d23640000297ed438000001be9a3c0005d8921d540000296e72c8000001be5f2c0005d0ef4db00000295285c2000001bdf90b0005c66302ce0000292b6348000001bd67d90005b91a889e000028f9617c000001bcab960005a94228aa000028bcd680000001bbc442000597052a16000028761876000001bab1dd0005828dd1a0000028257d80000001b9746700056c0561a0000027cb5bc0000001b80be0000553941a08000027680958000001b67848000539613864000026fbdc6a000001b4b99f00051d92f7da000026872b18000001b2cfe50005004e912a0000260a4b84000001b0bb1a0004e1b83aae0000258593d0000001ae7b3e0004c1f3285a000024f95a1e000001ac10510004a1218bbc00002465f490000001a97a5300047f6493fc000023cbb948000001a6b94400045cdc6ddc0000232afe68000001a3cd24000439a843b8000022841a12000001a0b5f3000415e63d86000021d762680000019d73b10003f1b380d6000021252d8c0000019a065e0003cd2c30d20000206dd1a0000001966dfa0003a86b6e3e00001fb1a4c600000192aa850003838b577800001ef0fd200000018ebbff00035ea5087800001e2c30d00000018aa268000339d09ad000001d6395f8000001865dc00003152525ac00001c9782ba00000181ee070002f0b8bdd200001bc84d380000017d533d0002cca075a200001af64b94000001788d620002a8f05d1600001a21d3f0000001739c76000285bb81c20000194b3c6e0000016e807900026313eed400001872db3000000169396b0002410aad1400001799065800000163c74c00021fafc2e4000016be14080000015e2a1c0001ff123440000015e25a620000015861db0001df4002be000015062f88000001526e890001c0462d8e00001429e99c0000014c50260001a230b17a0000134ddec00000014606b20001850a88e60000127265160000013f922d000168ddabd000001197d2c000000138f29700014db30fd0000010be7de00000013227f000013392a81800000fe6bc980000012b323800011a83657400000f10e50a00000124116f0001028b364a00000e3d4d580000011cc5950000ebaf069a00000d6c4ba4000001154eaa0000d5f2bffe00000c9e36100000010dacae0000c15949aa00000bd362be00000105dfa10000ade4886c00000b0c27d0000000fde78300009b955eac00000a48db68000000f5c45400008a6bac6c00000989d3a8000000ed761400007a664f48000008cf66b2000000e4fcc300006b83227600000819eaa8000000dc586100005dbefec600000769b5ac000000d388ee00005115baa2000006bf1de0000000ca8e6a000045822a0e0000061a7966000000c168d500003afe1ea80000057c1e60000000b8182f0000318267a8000004e462f0000000ae9c7800002906d1e0000004539d38000000a4f5b00000218227bc000003ca235a0000009b23d700001aea3142000003484b780000009126ed00001533b412000002ce6bb400000086fef20000105273660000025cda300000007cabe600000c393012000001f3ed0e000000722dc9000008d9a88400000193fa7000000067849b0000062498c40000013d58780000005cb05c00000409ba74000000f05d4800000051b10c00000277c4d0000000ad5f020000004686ab0000015c6cae00000074b3c80000003b3139000000a4647e00000046b1bc0000002fb0b60000003b5c4a00000023af000000002405220000000c01b60000000c01b6000000182e7d0000000000000000000000000000000c2cc7000000000000000000000000000000000000

private theorem k145LowCuts :
    k145All (fun t => decide (k145GoodCut pairedLowShape 105 3555 t)) 178 = true := by decide +kernel

private theorem k145LowMoments :
    k145All (fun r => decide (k145MomStep pairedLowShape 105 k145LowData r)) 73 = true := by decide +kernel

private theorem k145LowBaseTotal : supportBase pairedLowShape 105 3555 = 80448263632402569512 := by
  have h := k145Eval pairedLowShape 105 3555 k145LowData false (by decide) k145LowCuts k145LowMoments
  exact h.trans (by decide +kernel)

private theorem k145LowSlopeTotal : supportSlope pairedLowShape 105 3555 = 352443187412456 := by
  have h := k145Eval pairedLowShape 105 3555 k145LowData true (by decide) k145LowCuts k145LowMoments
  exact h.trans (by decide +kernel)

private theorem paired_low_test : PositiveSupport pairedLowShape 105 3555 := by
  have hB : pairedLowShape.B + 1 = 501 := rfl
  rw [PositiveSupport, k145LowBaseTotal, k145LowSlopeTotal, k145Node_eq, k145Pole_eq, hB]
  have hn : k145Sum (k145NodeTerm pairedLowShape) 501 = 5210801 := k145LowNodeTotal
  have hp : k145Sum (k145PoleTerm pairedLowShape) 501 = 4343593800 := k145LowPoleTotal
  rw [hn, hp]
  decide +kernel

private theorem k145MidNodeTotal :
    k145Sum (k145NodeTerm pairedMidShape) 501 = 5210801 := by decide +kernel

private theorem k145MidPoleTotal :
    k145Sum (k145PoleTerm pairedMidShape) 501 = 4343593800 := by decide +kernel

private def k145MidData : ℕ :=
  0x5d05da59a00001c296d34000000ce939e0005d055ee8600001c295a92000000ce93710005cf3da9e400001c26af40000000ce8cef0005cc9e732400001c203b08000000ce7d0c0005c887682000001c1610ac000000ce63c80005c3076e6c00001c0842ee000000ce41230005bc2d335600001bf6e490000000ce151d0005b4072be600001be20854000000cddfb60005aaa394de00001bc9c0fc000000cda0ee0005a01072ba00001bae214a000000cd58c50005945b91b000001b8f3c00000000cd073b0005879285b000001b6d23e0000000ccac50000579c2aa6400001b47ebac000000cc480400056af9233000001b1fa626000000cbda5700055b42db3200001af46610000000cb634900054aac854200001ac63e2c000000cae2da000539429bf200001a95413c000000ca590a00052711618e00001a618202000000c9c5d900051424e01c00001a2b1340000000c9294700050088e95c000019f207b8000000c883540004ec4916c8000019b6722c000000c7d4000004d770c99400001978655e000000c71b4b0004c20b2aae00001937f410000000c659350004ac232abe000018f53104000000c58dbe000495c38226000018b02efc000000c4b8e600047ef6b1020000186900ba000000c3daad000467c6ff280000181fb900000000c2f3130004503e7c28000017d46a90000000c2021800043866ff4c00001787282c000000c107bc0004204a2798000017380496000000c003ff000407f15bca000016e71290000000bef6e10003ef65ca5a0000169464dc000000bde0620003d6b0697a000016400e3c000000bcc0820003bdd9f716000015ea2172000000bb97410003a4eaf8d400001592b140000000ba649f00038bebbc1400001539d068000000b9289c000372e455f0000014df91ac000000b7e338000359dca33c0000148407ce000000b69473000340dc4886000014274590000000b53c4d000327eab216000013c95db4000000b3dac600030f0f13ee0000136a62fc000000b26fde0002f65069ca0000130a682a000000b0fb950002ddb57720000012a98000000000af7deb0002c544c72000001247bd40000000adf6e00002ad04acb4000011e532ac000000ac6674000294fb428000001181f306000000aacca700027d2e6ae20000111e1110000000a92979000265a3cff2000010b99f8c000000a77cea00024e60e38200001054b13c000000a5c6fa0002376adf1e00000fef58e2000000a407a9000220c6c40c00000f89a940000000a23ef700020a795b4c00000f23b518000000a06ce40001f487359800000ebd8f2c0000009e91700001def4ab6400000e574a3e0000009cac9b0001c9c5dcde00000df0f9100000009abe650001b4feb1ee00000d8aae6400000098c6ce0001a0a2da3600000d247cfc00000096c5d600018cb5cd1200000cbe779a00000094bb7d0001793ac99800000c58b10000000092a7c300016634d69800000bf33bf0000000908aa8000153a6c29c00000b8e2b2c0000008e642c0001419323e800000b2991760000008c344f00012ffc587a00000ac5819000000089fb1100011ee4860a00000a620e3c00000087b87200010e4d9a0a000009ff4a3c000000856c720000fe3949a60000099d48520000008317110000eea911c40000093c1b4000000080b84f0000df9e3704000008dbd5c80000007e502c0000d119c5c00000087c8aac0000007bdea80000c31c920c0000081e4cae0000007963c30000b5a737b6000007c12e9000000076df7d0000a8ba1a460000076543140000007451d600009c5564fe0000070a9cfc00000071bace000090790ada000006b14f0a0000006f1a6500008524c690000006596c000000006c709b00007a581a900000060306a000000069bd70000070125104000005ae31ac0000006700e4000066527bd00000055affe6000000643af700005d177492000005098410000000616ba90000545fdca2000004b9d0ec0000005e92fa00004c2a1d120000046bf93c0000005bb0ea0000447466ae000004200fc200000058c57900003d3cb1fc000003d6274000000055d0a700003680bf3c0000038e527800000052d2740000303e166800000348a42c0000004fcae000002a720734000003052f1e0000004cb9eb00002519a90e000002c40610000000499f9500002031db1e000002853bc4000000467bde00001bb7444600000248e2fc000000434ec6000017a653220000020f0e7a00000040184d000013fb3e08000001d7d1000000003cd873000010b20308000001a33d50000000398f3800000dc667ec00000171662c000000363c9c00000b33fa38000001425e5600000032e09f000008f60f2a0000011638900000002f7b4100000707c3ba000000ed079c0000002c0c8200000563fc9a000000c6de3c000000289462000004056636000000a3cf320000002512e1000002e674b400000083ed400000002187ff0000020163f4000000674b280000001df3bc0000015037900000004dfbac0000001a5618000000ccbadc00000038118e00000016af130000007080e6000000259f9000000012fead00000034e47600000016b8740000000f44e600000013080e0000000b6efc0000000b81be00000003d5ea00000003d5ea00000007b53500000000000000000000000000000003df4b000000000000000000000000000000000000

private theorem k145MidCuts :
    k145All (fun t => decide (k145GoodCut pairedMidShape 49 8211 t)) 212 = true := by decide +kernel

private theorem k145MidMoments :
    k145All (fun r => decide (k145MomStep pairedMidShape 49 k145MidData r)) 107 = true := by decide +kernel

private theorem k145MidBaseTotal : supportBase pairedMidShape 49 8211 = 37731192179193786858 := by
  have h := k145Eval pairedMidShape 49 8211 k145MidData false (by decide) k145MidCuts k145MidMoments
  exact h.trans (by decide +kernel)

private theorem k145MidSlopeTotal : supportSlope pairedMidShape 49 8211 = 134620998125682 := by
  have h := k145Eval pairedMidShape 49 8211 k145MidData true (by decide) k145MidCuts k145MidMoments
  exact h.trans (by decide +kernel)

private theorem paired_mid_test : PositiveSupport pairedMidShape 49 8211 := by
  have hB : pairedMidShape.B + 1 = 501 := rfl
  rw [PositiveSupport, k145MidBaseTotal, k145MidSlopeTotal, k145Node_eq, k145Pole_eq, hB]
  have hn : k145Sum (k145NodeTerm pairedMidShape) 501 = 5210801 := k145MidNodeTotal
  have hp : k145Sum (k145PoleTerm pairedMidShape) 501 = 4343593800 := k145MidPoleTotal
  rw [hn, hp]
  decide +kernel

private theorem k145HighNodeTotal :
    k145Sum (k145NodeTerm pairedHighShape) 501 = 5210801 := by decide +kernel

private theorem k145HighPoleTotal :
    k145Sum (k145PoleTerm pairedHighShape) 501 = 4343593800 := by decide +kernel

private def k145HighData : ℕ :=
  0x62651327b00001986444b000000a03645000625deb20b0000198555fb000000a034550006243a89e300001981e457000000a02d1b0006216b66c00000197bf2dc000000a0208800061d7b4bc0000019738c3c000000a00e9c000618741beb00001968bb290000009ff7570006125f9a330000195b8a550000009fdab900060b4769740000194c04720000009fb8c2000603350c740000193a34320000009f91720005fa31e5e30000192624470000009f64c90005f047385b0000190fdf630000009f32c70005e57e2660000018f770380000009efb6c0005d9dfb260000018dce1780000009ebeb80005cd74beb3000018c03dd50000009e7cab0005c0460d9b000018a190010000009e35450005b25c414400001880e2ae0000009de8860005a3bfdbc40000185e408e0000009d966e000594793f1b00001839b4530000009d3efd00058490ad330000181348af0000009ce2330005740e47e0000017eb08540000009c8010000562fa10e0000017c0fdf40000009c18940005515be9db0000179534410000009babbf00053f3b946300001767b5ed0000009b399100052ca0b1f4000017388daa0000009ac20a00051992c3f400001707c62a0000009a452a000506192bb3000016d56a1f00000099c2f10004f23b2a6b000016a1843b000000993b5f0004ddffe1400000166c1f3000000098ae740004c96e51400000163545b0000000981c300004b48d5b63000015fd026d00000097849300049f63c08b000015c3601900000096e79d000489f8218400001588696600000096454e00047450ff040000154c2906000000959da600045e74b9ab0000150ea9ab00000094f0a5000448699203000014cff607000000943e4b00043235a8800000149018cc00000093869800041bdefd800000144f1cac00000092c98c0004056b714b0000140d0c590000009207270003eee0c413000013c9f285000000913f690003d84495f400001385d9e20000009072520003c19c66f400001340cd220000008f9fe20003aaed9703000012fad6f70000008ec8190003943d65fb000012b402130000008deaf700037d90f3a00000126c59280000008d087c000366ed3fa000001223e6e80000008c20a8000350572993000011dab6050000008b337b000339d370fb00001190d1310000008a40f500032366b54400001146431e00000089491600030d1575c4000010fb167e000000884bde0002f6e411bb000010af560300000087494d0002e0d6c853000010630c5f0000008641630002caf1b8a00000101644440000008534200002b538e1a000000fc9086400000084218400029fb0223b00000f7b637100000083098f00028a5b394300000f2d601d00000081ec410002753dc57400000edf091a00000080c99a0002605b457400000e90691a0000007fa19a00024bb717d300000e418acf0000007e7441000237547b0b00000df278eb0000007d418f000223368d8000000da33e200000007c098400020f604d8000000d53e5200000007acc200001fbd4994300000d04789d0000007989630001e8962eeb00000cb5034900000078414d0001d5a7ac8400000c658fd600000076f3de0001c30b900400000c1628f600000075a1160001b0c4374b00000bc6d95b0000007448f500019ed3e02300000b77abb700000072eb7b00018d3ca84000000b28aabc0000007188a800017c008d4000000ad9e11c00000070207c00016b216cab00000a8b59890000006eb2f700015aa103f300000a3d1eb50000006d401900014a80f074000009ef3b520000006bc7e200013ac2af74000009a1ba120000006a4a5200012b679e2300000954a5a700000068c76900011c70f99b0000090808c3000000673f2700010ddfdee0000008bbee1800000065b18c0000ffb54ae0000008706058000000641e980000f1f21a73000008256a3500000062864b0000e4970a5b000007db166100000060e8a50000d7a4b744000007916f8e0000005f45a60000cb1b9dc400000748806e0000005d9d4e0000befc1a5b0000070053b30000005bef9d0000b3466973000006b8f40f0000005a3c930000a7faa760000006726c3400000058843000009d18d0600000062cc6d400000056c674000092a0c09b000005e80ea100000055035f000088923423000005a44e4d000000533af100007eecc6f400000561908a000000516d2a000075aff4f40000051fe00a0000004f9a0a00006cdb19f3000004df477f0000004dc1910000646d71ab0000049fd19b0000004be3bf00005c6617c00000046189100000004a0094000054c407c000000424789000000048181000004d861d23000003e8aacd000000462a33000046ab134b000003ae2a790000004436fd000040318584000003750246000000423e6e00003a17ef040000033d3ce60000004040860000345caaeb00000306e50b0000003e3d4500002efdf443000002d205670000003c34ab000029f9e6000000029ea8ac0000003a26b80000254e7b000000026cd98c00000038136c000020f98e0b0000023ca2b900000035fac700001cf8d9d30000020e0ee500000033dcc900001949f8f4000001e128c200000031b972000015ea65f4000001b5fb020000002f90c2000012d77b430000018c90570000002d62b90000100e733b00000164f3730000002b2f5700000d8c68200000013f2f0800000028f69c00000b4e54200000011b4dc800000026b888000009511153000000f95a6500000024751b0000079159bb000000d95f91000000222c550000060bc744000000bb67fe0000001fde36000004bcd3c40000009f7e5e0000001d8abe000003a0d8fb00000085ad630000001b31ed000002b410930000006dffbf00000018d3c3000001f29420000000588024000000167040000001585d20000000453944000000140764000000e144fb0000003435d100000011992f00000089050300000025807d0000000f25a10000004b36740000001923fa0000000cacba0000002352740000000f2afa0000000a2e7a0000000cb21300000007a02f00000007aae1000000028e4b000000028e4b0000000521ef0000000000000000000000000000000293a4000000000000000000000000000000000000

private theorem k145HighCuts :
    k145All (fun t => decide (k145GoodCut pairedHighShape 37 24000 t)) 229 = true := by decide +kernel

private theorem k145HighMoments :
    k145All (fun r => decide (k145MomStep pairedHighShape 37 k145HighData r)) 124 = true := by decide +kernel

private theorem k145HighBaseTotal : supportBase pairedHighShape 37 24000 = 30629147715513145328 := by
  have h := k145Eval pairedHighShape 37 24000 k145HighData false (by decide) k145HighCuts k145HighMoments
  exact h.trans (by decide +kernel)

private theorem k145HighSlopeTotal : supportSlope pairedHighShape 37 24000 = 92655832557612 := by
  have h := k145Eval pairedHighShape 37 24000 k145HighData true (by decide) k145HighCuts k145HighMoments
  exact h.trans (by decide +kernel)

private theorem paired_high_test : PositiveSupport pairedHighShape 37 24000 := by
  have hB : pairedHighShape.B + 1 = 501 := rfl
  rw [PositiveSupport, k145HighBaseTotal, k145HighSlopeTotal, k145Node_eq, k145Pole_eq, hB]
  have hn : k145Sum (k145NodeTerm pairedHighShape) 501 = 5210801 := k145HighNodeTotal
  have hp : k145Sum (k145PoleTerm pairedHighShape) 501 = 4343593800 := k145HighPoleTotal
  rw [hn, hp]
  decide +kernel

end

/-- The strict inequality (T) for all five native terminal subbanks (69.18 bands). -/
theorem proof : K1_14.c5 := by
  intro w hlo hhi
  have hw : w ≤ 131071 := by omega
  by_cases h0 : w ≤ 2600
  · exact test_of_support w
      (by simp [terminalShape, band, h0, band0Shape])
      (by simp [band, h0]) (by omega) hw band0_test.1 band0_test.2
  by_cases hb : w ≤ 3554
  · exact test_of_support w
      (by simp [terminalShape, band, h0, hb, bridgeShape])
      (by simp [band, h0, hb]) (by omega) hw bridge_test.1 bridge_test.2
  by_cases hl : w ≤ 8210
  · exact test_of_support w
      (by simp [terminalShape, band, h0, hb, hl, pairedLowShape])
      (by simp [band, h0, hb, hl]) (by omega) hw paired_low_test.1 paired_low_test.2
  by_cases hm : w ≤ 23999
  · exact test_of_support w
      (by simp [terminalShape, band, h0, hb, hl, hm, pairedMidShape])
      (by simp [band, h0, hb, hl, hm]) (by omega) hw paired_mid_test.1 paired_mid_test.2
  · exact test_of_support w
      (by simp [terminalShape, band, h0, hb, hl, hm, pairedHighShape])
      (by simp [band, h0, hb, hl, hm]) (by omega) hw paired_high_test.1 paired_high_test.2

end K1_14_5
end PackSource_K1_14_5Proof

import ProximityPrize.SubmissionLower.FadicGateDim
import ProximityPrize.SubmissionLower.FadicVar

-- merged module FadicChunk
section Merged_FadicChunk
/-!
# Chunked bounds for the gate dimensions

The non-flat grade ranges of every box count are bounded in blocks of `h` grades: inside a block
the padded degree lies between `min lo ((Θ - 26 hi) / 25)` and `min hi ((Θ - 26 lo) / 25)`, and
the accepted `cappedCount` is monotone in the degree.  The flat range stays exact.

* `fastLow ≤ boxCount ≤ fastHigh`;
* `depthLow ≤ depthDim`, `fadicLow ≤ fadicDim`, `plainLow ≤ plainDim`;
* `loss_le_certLoss`: the level loss is at most `certLoss`, which a certificate evaluates.
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2 (cappedCount)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeColumns cumulativeExponents
  mem_cumulativeColumns)
open scoped BigOperators
open Finset
open private K1_13_2_2_3.cappedColumns K1_13_2_2_3.mem_cappedColumns K1_13_2_2_3.capped_card
  from ProximityPrize.SubmissionLower.Fast068
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)

/-! ### Monotonicity of the accepted count -/

theorem cappedCount_nonneg (d u t : ℤ) : 0 ≤ cappedCount d u t := by
  rw [← capped_card K1_13_2_2_2.proof]
  positivity

theorem cappedCount_mono {d d' : ℕ} (hd : d ≤ d') (u t : ℤ) :
    cappedCount d u t ≤ cappedCount d' u t := by
  rw [← capped_card K1_13_2_2_2.proof, ← capped_card K1_13_2_2_2.proof]
  have hcard : (cappedColumns d u t).card ≤ (cappedColumns d' u t).card := by
    let shift : JetExp → JetExp := fun e => e + Finsupp.single 0 (d' - d)
    apply Finset.card_le_card_of_injOn shift
    · intro e he
      obtain ⟨hj, ht⟩ := mem_cappedColumns.mp he
      obtain ⟨hg, hi⟩ := mem_cumulativeColumns.mp hj
      have hg' : ((Finsupp.weight gradeWeight e : ℕ) : ℤ) = (d : ℤ) := hg
      have hi' : ((Finsupp.weight oldWeight e : ℕ) : ℤ) ≤ u := hi
      apply mem_cappedColumns.mpr
      have e0 : shift e 0 = e 0 + (d' - d) := by simp [shift]
      have e1 : shift e 1 = e 1 := by simp [shift]
      have e2 : shift e 2 = e 2 := by simp [shift]
      have e3 : shift e 3 = e 3 := by simp [shift]
      refine ⟨mem_cumulativeColumns.mpr ⟨?_, ?_⟩, ?_⟩
      · change ((Finsupp.weight gradeWeight (shift e) : ℕ) : ℤ) = (d' : ℤ)
        rw [w_grade, e0, e1, e2, e3]
        rw [w_grade] at hg'
        push_cast at hg' ⊢
        omega
      · change ((Finsupp.weight oldWeight (shift e) : ℕ) : ℤ) ≤ u
        rw [w_old, e1, e2, e3, ← w_old]
        exact hi'
      · change ((shift e 3 : ℕ) : ℤ) ≤ t
        rw [e3]
        exact ht
    · intro x _ y _ hxy
      exact add_right_cancel hxy
  exact_mod_cast hcard

/-! ### The padded degree inside a block -/

theorem padGrade_ge {Θ lo q hi : ℕ} (hlo : lo ≤ q) (hhi : q ≤ hi) :
    min lo ((Θ - 26 * hi) / 25) ≤ padGrade Θ q := by
  unfold padGrade
  apply le_min
  · exact (min_le_left _ _).trans hlo
  · exact (min_le_right _ _).trans (Nat.div_le_div_right (by omega))

theorem padGrade_le {Θ lo q hi : ℕ} (hlo : lo ≤ q) (hhi : q ≤ hi) :
    padGrade Θ q ≤ min hi ((Θ - 26 * lo) / 25) := by
  unfold padGrade
  exact min_le_min hhi (Nat.div_le_div_right (by omega))

theorem term_nonneg (J T Θ q : ℕ) : 0 ≤ term J T Θ q := by
  unfold term
  split
  · exact cappedCount_nonneg _ _ _
  · exact le_rfl

/-! ### Blocks -/

def segLo (base h k : ℕ) : ℕ := base + h * k
def segHi (base h m k : ℕ) : ℕ := base + min (h * k + h - 1) (m - 1)

/-- Smallest padded degree in block `k` (natural-number arithmetic). -/
def lowDeg (Θ base h m k : ℕ) : ℕ := min (segLo base h k) ((Θ - 26 * segHi base h m k) / 25)

/-- Largest padded degree in block `k` (natural-number arithmetic). -/
def highDeg (Θ base h m k : ℕ) : ℕ := min (segHi base h m k) ((Θ - 26 * segLo base h k) / 25)

def lowSeg (J T Θ base h m k : ℕ) : ℤ :=
  if 26 * segHi base h m k ≤ Θ then cappedCount (lowDeg Θ base h m k : ℕ) J T else 0

def highSeg (J T Θ base h m k : ℕ) : ℤ :=
  if 26 * segLo base h k ≤ Θ then cappedCount (highDeg Θ base h m k : ℕ) J T else 0

theorem seg_bounds {base h m i : ℕ} (hh : 0 < h) (hi : i < m) :
    segLo base h (i / h) ≤ base + i ∧ base + i ≤ segHi base h m (i / h) := by
  have h1 : h * (i / h) ≤ i := Nat.mul_div_le i h
  have h2 : i % h < h := Nat.mod_lt i hh
  have h3 : i % h + h * (i / h) = i := Nat.mod_add_div i h
  unfold segLo segHi
  constructor
  · omega
  · have : i ≤ h * (i / h) + h - 1 := by omega
    have : i ≤ m - 1 := by omega
    omega

theorem term_of_le {J T Θ q : ℕ} (hq : 26 * q ≤ Θ) :
    term J T Θ q = cappedCount (padGrade Θ q : ℕ) J T := by
  unfold term
  exact if_pos hq

theorem term_of_gt {J T Θ q : ℕ} (hq : ¬ 26 * q ≤ Θ) : term J T Θ q = 0 := by
  unfold term
  exact if_neg hq

theorem lowSeg_le {J T Θ base h m i : ℕ} (hh : 0 < h) (hi : i < m) :
    lowSeg J T Θ base h m (i / h) ≤ term J T Θ (base + i) := by
  obtain ⟨hlo, hhi⟩ := seg_bounds (base := base) (m := m) hh hi
  set lo := segLo base h (i / h)
  set hi' := segHi base h m (i / h)
  by_cases h26 : 26 * hi' ≤ Θ
  · have hq : 26 * (base + i) ≤ Θ := le_trans (Nat.mul_le_mul_left 26 hhi) h26
    have hl : lowSeg J T Θ base h m (i / h) = cappedCount (lowDeg Θ base h m (i / h) : ℕ) J T := by
      unfold lowSeg
      exact if_pos h26
    rw [hl, term_of_le hq]
    exact cappedCount_mono (padGrade_ge hlo hhi) (J : ℤ) (T : ℤ)
  · have hl : lowSeg J T Θ base h m (i / h) = 0 := by
      unfold lowSeg
      exact if_neg h26
    rw [hl]
    exact term_nonneg _ _ _ _

theorem le_highSeg {J T Θ base h m i : ℕ} (hh : 0 < h) (hi : i < m) :
    term J T Θ (base + i) ≤ highSeg J T Θ base h m (i / h) := by
  obtain ⟨hlo, hhi⟩ := seg_bounds (base := base) (m := m) hh hi
  set lo := segLo base h (i / h)
  set hi' := segHi base h m (i / h)
  by_cases h26 : 26 * lo ≤ Θ
  · have hl : highSeg J T Θ base h m (i / h) =
        cappedCount (min hi' ((Θ - 26 * lo) / 25) : ℕ) J T := by
      unfold highSeg
      exact if_pos h26
    rw [hl]
    by_cases hq : 26 * (base + i) ≤ Θ
    · rw [term_of_le hq]
      exact cappedCount_mono (padGrade_le hlo hhi) (J : ℤ) (T : ℤ)
    · rw [term_of_gt hq]
      exact cappedCount_nonneg _ _ _
  · have hq : ¬ 26 * (base + i) ≤ Θ := fun hq => h26 (le_trans (Nat.mul_le_mul_left 26 hlo) hq)
    have hl : highSeg J T Θ base h m (i / h) = 0 := by
      unfold highSeg
      exact if_neg h26
    rw [hl, term_of_gt hq]

/-- Summing a block-constant function. -/
theorem sum_div_block (F : ℕ → ℤ) {h : ℕ} (hh : 0 < h) (n : ℕ) :
    ∑ i ∈ range n, F (i / h) = h * ∑ k ∈ range (n / h), F k + ((n % h : ℕ) : ℤ) * F (n / h) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    have e1 := Nat.mod_add_div n h
    have e2 := Nat.mod_lt n hh
    rcases Nat.lt_or_ge (n % h + 1) h with hlt | hge
    · have hq : (n + 1) / h = n / h ∧ (n + 1) % h = n % h + 1 :=
        (Nat.div_mod_unique hh).mpr ⟨by omega, hlt⟩
      rw [hq.1, hq.2]
      push_cast
      ring
    · have hq : (n + 1) / h = n / h + 1 ∧ (n + 1) % h = 0 := by
        apply (Nat.div_mod_unique hh).mpr
        refine ⟨?_, hh⟩
        rw [Nat.mul_succ]
        omega
      have hr : n % h = h - 1 := by omega
      rw [hq.1, hq.2, sum_range_succ, hr]
      have hh1 : ((h - 1 : ℕ) : ℤ) = (h : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        simp
      rw [hh1]
      push_cast
      ring

def segSumLow (J T Θ base h m : ℕ) : ℤ :=
  h * ∑ k ∈ range (m / h), lowSeg J T Θ base h m k +
    ((m % h : ℕ) : ℤ) * lowSeg J T Θ base h m (m / h)

def segSumHigh (J T Θ base h m : ℕ) : ℤ :=
  h * ∑ k ∈ range (m / h), highSeg J T Θ base h m k +
    ((m % h : ℕ) : ℤ) * highSeg J T Θ base h m (m / h)

theorem segSumLow_le {J T Θ base h m : ℕ} (hh : 0 < h) :
    segSumLow J T Θ base h m ≤ ∑ i ∈ range m, term J T Θ (base + i) := by
  unfold segSumLow
  rw [← sum_div_block (lowSeg J T Θ base h m) hh m]
  exact sum_le_sum fun i hi => lowSeg_le hh (mem_range.mp hi)

theorem le_segSumHigh {J T Θ base h m : ℕ} (hh : 0 < h) :
    ∑ i ∈ range m, term J T Θ (base + i) ≤ segSumHigh J T Θ base h m := by
  unfold segSumHigh
  rw [← sum_div_block (highSeg J T Θ base h m) hh m]
  exact sum_le_sum fun i hi => le_highSeg hh (mem_range.mp hi)

/-! ### Box counts -/

def fastLow (B J T Θ h : ℕ) : ℤ :=
  segSumLow J T Θ 0 h (flatLo B J) +
    ((flatHi B J Θ - flatLo B J : ℕ) : ℤ) * cappedCount J J T +
    segSumLow J T Θ (flatHi B J Θ) h (B + 1 - flatHi B J Θ)

def fastHigh (B J T Θ h : ℕ) : ℤ :=
  segSumHigh J T Θ 0 h (flatLo B J) +
    ((flatHi B J Θ - flatLo B J : ℕ) : ℤ) * cappedCount J J T +
    segSumHigh J T Θ (flatHi B J Θ) h (B + 1 - flatHi B J Θ)

theorem fastLow_le (B J T Θ : ℕ) {h : ℕ} (hh : 0 < h) : fastLow B J T Θ h ≤ boxCount B J T Θ := by
  rw [← fastCount_eq]
  unfold fastLow fastCount
  rw [intPrefix_eq, intPrefix_eq]
  have h1 := segSumLow_le (J := J) (T := T) (Θ := Θ) (base := 0) (m := flatLo B J) hh
  have h2 := segSumLow_le (J := J) (T := T) (Θ := Θ) (base := flatHi B J Θ)
    (m := B + 1 - flatHi B J Θ) hh
  simp only [zero_add] at h1
  linarith

theorem le_fastHigh (B J T Θ : ℕ) {h : ℕ} (hh : 0 < h) : boxCount B J T Θ ≤ fastHigh B J T Θ h := by
  rw [← fastCount_eq]
  unfold fastHigh fastCount
  rw [intPrefix_eq, intPrefix_eq]
  have h1 := le_segSumHigh (J := J) (T := T) (Θ := Θ) (base := 0) (m := flatLo B J) hh
  have h2 := le_segSumHigh (J := J) (T := T) (Θ := Θ) (base := flatHi B J Θ)
    (m := B + 1 - flatHi B J Θ) hh
  simp only [zero_add] at h1
  linarith

/-! ### Gate dimensions -/

def multHigh (h σb σj σt bl bh jl jh r a : ℕ) : ℤ :=
  if bl ≤ depthB σb bh r a ∧ jl ≤ depthJ σj jh r a ∧ 26 * bl ≤ depthΘ bh jh a then
    fastHigh (depthB σb bh r a - bl) (depthJ σj jh r a - jl) ((r - a) * σt)
      (depthΘ bh jh a - 26 * bl) h
  else 0

def depthLow (h σb σj σt bl bh jl jh r a : ℕ) : ℤ :=
  if DepthOK bh jh r a then
    max 0 (fastLow (depthB σb bh r a) (depthJ σj jh r a) ((r - a) * σt) (depthΘ bh jh a) h -
      multHigh h σb σj σt bl bh jl jh r a)
  else 0

def fadicLow (h σb σj σt bl bh jl jh r : ℕ) : ℤ :=
  ∑ a ∈ range (r / 3 + 1), depthLow h σb σj σt bl bh jl jh r a

def plainLow (h σb σj σt r : ℕ) : ℤ :=
  fastLow (min (r * σb) 4012) (min (r * σj) 1650) (r * σt) 131312 h

theorem multCount_le_multHigh (h σb σj σt bl bh jl jh r a : ℕ) (hh : 0 < h) :
    multCount σb σj σt bl bh jl jh r a ≤ multHigh h σb σj σt bl bh jl jh r a := by
  unfold multCount multHigh
  split
  · exact le_fastHigh _ _ _ _ hh
  · exact le_rfl

theorem depthLow_le (h σb σj σt bl bh jl jh r a : ℕ) (hh : 0 < h) :
    depthLow h σb σj σt bl bh jl jh r a ≤ depthDim σb σj σt bl bh jl jh r a := by
  unfold depthLow depthDim
  split
  · apply max_le_max le_rfl
    have h1 := fastLow_le (depthB σb bh r a) (depthJ σj jh r a) ((r - a) * σt) (depthΘ bh jh a) hh
    have h2 := multCount_le_multHigh h σb σj σt bl bh jl jh r a hh
    linarith
  · exact le_rfl

theorem fadicLow_le (h σb σj σt bl bh jl jh r : ℕ) (hh : 0 < h) :
    fadicLow h σb σj σt bl bh jl jh r ≤ fadicDim σb σj σt bl bh jl jh r :=
  sum_le_sum fun a _ => depthLow_le h σb σj σt bl bh jl jh r a hh

theorem plainLow_le (h σb σj σt r : ℕ) (hh : 0 < h) :
    plainLow h σb σj σt r ≤ plainDim σb σj σt r :=
  fastLow_le _ _ _ _ hh

/-- The loss a certificate evaluates at level `i + 1`. -/
def certLoss (S : ℤ) (h σb σj σt bl bh jl jh i : ℕ) : ℤ :=
  if IsFull σb σj σt (i + 1) then 0
  else max 0 (S - max (plainLow h σb σj σt (i + 1)) (fadicLow h σb σj σt bl bh jl jh (i + 1)))

theorem loss_le_certLoss (S : ℤ) (h σb σj σt bl bh jl jh i : ℕ) (hh : 0 < h) :
    max 0 (S - gateDim S σb σj σt bl bh jl jh (i + 1)) ≤ certLoss S h σb σj σt bl bh jl jh i := by
  unfold certLoss gateDim
  split
  · simp
  · apply max_le_max le_rfl
    have h1 := plainLow_le h σb σj σt (i + 1) hh
    have h2 := fadicLow_le h σb σj σt bl bh jl jh (i + 1) hh
    have h3 : max (plainLow h σb σj σt (i + 1)) (fadicLow h σb σj σt bl bh jl jh (i + 1)) ≤
        max (plainDim σb σj σt (i + 1)) (fadicDim σb σj σt bl bh jl jh (i + 1)) :=
      max_le_max h1 h2
    linarith

/-- **Certificate.**  If level `R0 + 1` is full and the first `R0` certified losses add up to `L`,
the total gate loss over any number of levels is at most `L`. -/
theorem loss_of_cert (S : ℤ) (h σb σj σt bl bh jl jh R0 : ℕ) (L : ℤ) (hh : 0 < h)
    (hfull : IsFull σb σj σt (R0 + 1))
    (hsum : ∑ i ∈ range R0, certLoss S h σb σj σt bl bh jl jh i = L) (N : ℕ) :
    ∑ i ∈ range N, max 0 (S - gateDim S σb σj σt bl bh jl jh (i + 1)) ≤ L := by
  have hzero (i : ℕ) (hi : R0 ≤ i) : certLoss S h σb σj σt bl bh jl jh i = 0 := by
    unfold certLoss
    exact if_pos (isFull_mono hfull (by omega))
  have hnonneg (i : ℕ) : 0 ≤ certLoss S h σb σj σt bl bh jl jh i := by
    unfold certLoss
    split
    · exact le_rfl
    · exact le_max_left _ _
  refine (sum_le_sum fun i _ => loss_le_certLoss S h σb σj σt bl bh jl jh i hh).trans ?_
  rw [← hsum]
  rcases le_total N R0 with hN | hN
  · exact sum_le_sum_of_subset_of_nonneg (range_mono hN) (fun i _ _ => hnonneg i)
  · rw [← sum_range_add_sum_Ico _ hN]
    have : ∑ i ∈ Ico R0 N, certLoss S h σb σj σt bl bh jl jh i = 0 :=
      sum_eq_zero fun i hi => hzero i (mem_Ico.mp hi).1
    rw [this, add_zero]

end FadicGate

#print axioms FadicGate.cappedCount_mono
#print axioms FadicGate.sum_div_block
#print axioms FadicGate.fastLow_le
#print axioms FadicGate.le_fastHigh
#print axioms FadicGate.loss_of_cert
end Merged_FadicChunk

-- merged module FadicNat
section Merged_FadicNat
/-!
# A Nat-only evaluator for the gate certificate

The kernel evaluates `Nat` literals on its accelerated path and `Int` on none.  This file mirrors
the evaluation chain of `FadicGateDim` in `ℕ`: truncated subtraction stands for every
`max 0 (…)`, and the inner subtractions of the accepted counting formulas never truncate because
each of them is a cardinality.  `rowLossN_eq` identifies the two once, generically.
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2 (cappedCount cumulative denominator)
open scoped BigOperators
open Finset

/-- The accepted `denominator` at a natural argument, with `q = n / 6`, `r = n % 6`. -/
def denomQR (q r : ℕ) : ℕ :=
  1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)

def denomN (n : ℕ) : ℕ := denomQR (n / 6) (n % 6)

/-- `denominator (v - k)`, which vanishes for a negative argument. -/
def denomSub (v k : ℕ) : ℕ := if k ≤ v then denomN (v - k) else 0

def cumAux (d v : ℕ) : ℕ :=
  (denomN v + denomSub v (2 * d + 3) + denomSub v (2 * d + 4) + denomSub v (2 * d + 5)) -
    (denomSub v (d + 1) + denomSub v (d + 2) + denomSub v (d + 3) + denomSub v (3 * d + 6))

def cumulativeN (d u : ℕ) : ℕ := cumAux d (min u (3 * d))

/-- The accepted `cappedCount` at natural arguments.  The subtracted count is tested on the
index first: it vanishes whenever the top bound is implied by the index bound. -/
def cappedCountN (d u t : ℕ) : ℕ :=
  cumulativeN d u -
    (if 3 * (t + 1) ≤ u then (if t + 1 ≤ d then cumulativeN (d - (t + 1)) (u - 3 * (t + 1))
      else 0) else 0)










end FadicGate
end Merged_FadicNat

-- merged module FadicRaw
section Merged_FadicRaw
/-!
# Kernel-raw evaluator

The same evaluation chain as `FadicNat`, written with the primitive `Nat.add`, `Nat.sub`,
`Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.ble` and `cond`, which the kernel reduces on literals
without unfolding any instance.
-/

set_option autoImplicit false

namespace FadicGate

def rMin (a b : ℕ) : ℕ := cond (Nat.ble a b) a b
def rMax (a b : ℕ) : ℕ := cond (Nat.ble a b) b a

def rDenomQR (q r : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.add (Nat.add 1 (Nat.div (Nat.mul r (Nat.add r 1)) 2))
      (Nat.mul q (Nat.add (Nat.add 22 (Nat.mul 7 r)) (Nat.div (Nat.mul r (Nat.sub r 1)) 2))))
    (Nat.mul (Nat.add 57 (Nat.mul 6 r)) (Nat.div (Nat.mul q (Nat.sub q 1)) 2)))
    (Nat.mul (Nat.mul (Nat.mul 6 q) (Nat.sub q 1)) (Nat.sub q 2))

def rDenom (n : ℕ) : ℕ := rDenomQR (Nat.div n 6) (Nat.mod n 6)

def rDenomSub (v k : ℕ) : ℕ := cond (Nat.ble k v) (rDenom (Nat.sub v k)) 0

def rCumAux (d v : ℕ) : ℕ :=
  Nat.sub
    (Nat.add (Nat.add (Nat.add (rDenom v) (rDenomSub v (Nat.add (Nat.mul 2 d) 3)))
      (rDenomSub v (Nat.add (Nat.mul 2 d) 4))) (rDenomSub v (Nat.add (Nat.mul 2 d) 5)))
    (Nat.add (Nat.add (Nat.add (rDenomSub v (Nat.add d 1)) (rDenomSub v (Nat.add d 2)))
      (rDenomSub v (Nat.add d 3))) (rDenomSub v (Nat.add (Nat.mul 3 d) 6)))

def rCumulative (d u : ℕ) : ℕ := rCumAux d (rMin u (Nat.mul 3 d))

def rCapped (d u t : ℕ) : ℕ :=
  Nat.sub (rCumulative d u)
    (cond (Nat.ble (Nat.mul 3 (Nat.add t 1)) u)
      (cond (Nat.ble (Nat.add t 1) d)
        (rCumulative (Nat.sub d (Nat.add t 1)) (Nat.sub u (Nat.mul 3 (Nat.add t 1)))) 0) 0)



def rPrefix (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Nat.add (rPrefix f n) (f n)

def rFlatLo (B J : ℕ) : ℕ := rMin J (Nat.add B 1)

def rFlatHi (B J Θ : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul 25 J) Θ)
    (rMax (rFlatLo B J) (rMin (Nat.add B 1) (Nat.add (Nat.div (Nat.sub Θ (Nat.mul 25 J)) 26) 1)))
    (rFlatLo B J)



def rDepthB (σb xb r a : ℕ) : ℕ := rMin (Nat.mul (Nat.sub r a) σb) (Nat.sub 4012 (Nat.mul a xb))
def rDepthJ (σj xj r a : ℕ) : ℕ := rMin (Nat.mul (Nat.sub r a) σj) (Nat.sub 1650 (Nat.mul a xj))
def rDepthΘ (xb xj a : ℕ) : ℕ :=
  Nat.sub 131312 (Nat.mul a (Nat.add (Nat.mul 26 xb) (Nat.mul 25 xj)))

def rDepthOK (xb xj r a : ℕ) : Bool :=
  (Nat.ble (Nat.mul 3 a) r && Nat.ble (Nat.add a 1) r) &&
    (Nat.ble (Nat.mul a xb) 4012 && Nat.ble (Nat.mul a xj) 1650 &&
      Nat.ble (Nat.mul a (Nat.add (Nat.mul 26 xb) (Nat.mul 25 xj))) 131312)






def rIsFull (σb σj σt r : ℕ) : Bool :=
  Nat.ble 4012 (Nat.mul r σb) && Nat.ble 1650 (Nat.mul r σj) && Nat.ble 550 (Nat.mul r σt)



end FadicGate
end Merged_FadicRaw

-- merged module FadicChunkRaw
section Merged_FadicChunkRaw
/-!
# Kernel-raw evaluator of the chunked certificate
-/

set_option autoImplicit false

namespace FadicGate

def rSegLo (base h k : ℕ) : ℕ := Nat.add base (Nat.mul h k)
def rSegHi (base h m k : ℕ) : ℕ :=
  Nat.add base (rMin (Nat.sub (Nat.add (Nat.mul h k) h) 1) (Nat.sub m 1))

def rLowSegAux (J T Θ lo hi : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul 26 hi) Θ)
    (rCapped (rMin lo (Nat.div (Nat.sub Θ (Nat.mul 26 hi)) 25)) J T) 0

def rHighSegAux (J T Θ lo hi : ℕ) : ℕ :=
  cond (Nat.ble (Nat.mul 26 lo) Θ)
    (rCapped (rMin hi (Nat.div (Nat.sub Θ (Nat.mul 26 lo)) 25)) J T) 0

def rLowSeg (J T Θ base h m k : ℕ) : ℕ := rLowSegAux J T Θ (rSegLo base h k) (rSegHi base h m k)
def rHighSeg (J T Θ base h m k : ℕ) : ℕ := rHighSegAux J T Θ (rSegLo base h k) (rSegHi base h m k)

def rSegSumLow (J T Θ base h m : ℕ) : ℕ :=
  Nat.add (Nat.mul h (rPrefix (rLowSeg J T Θ base h m) (Nat.div m h)))
    (Nat.mul (Nat.mod m h) (rLowSeg J T Θ base h m (Nat.div m h)))

def rSegSumHigh (J T Θ base h m : ℕ) : ℕ :=
  Nat.add (Nat.mul h (rPrefix (rHighSeg J T Θ base h m) (Nat.div m h)))
    (Nat.mul (Nat.mod m h) (rHighSeg J T Θ base h m (Nat.div m h)))

def rFastLowAux (B J T Θ h lo hi : ℕ) : ℕ :=
  Nat.add (Nat.add (rSegSumLow J T Θ 0 h lo) (Nat.mul (Nat.sub hi lo) (rCapped J J T)))
    (rSegSumLow J T Θ hi h (Nat.sub (Nat.add B 1) hi))

def rFastHighAux (B J T Θ h lo hi : ℕ) : ℕ :=
  Nat.add (Nat.add (rSegSumHigh J T Θ 0 h lo) (Nat.mul (Nat.sub hi lo) (rCapped J J T)))
    (rSegSumHigh J T Θ hi h (Nat.sub (Nat.add B 1) hi))

def rFastLow (B J T Θ h : ℕ) : ℕ := rFastLowAux B J T Θ h (rFlatLo B J) (rFlatHi B J Θ)
def rFastHigh (B J T Θ h : ℕ) : ℕ := rFastHighAux B J T Θ h (rFlatLo B J) (rFlatHi B J Θ)

def rMultHighAux (h σt bl jl r a B J Θ : ℕ) : ℕ :=
  cond (Nat.ble bl B && Nat.ble jl J && Nat.ble (Nat.mul 26 bl) Θ)
    (rFastHigh (Nat.sub B bl) (Nat.sub J jl) (Nat.mul (Nat.sub r a) σt) (Nat.sub Θ (Nat.mul 26 bl)) h) 0

def rDepthLowAux (h σt bl jl r a B J Θ : ℕ) : ℕ :=
  Nat.sub (rFastLow B J (Nat.mul (Nat.sub r a) σt) Θ h) (rMultHighAux h σt bl jl r a B J Θ)

def rDepthLow (h σb σj σt bl bh jl jh r a : ℕ) : ℕ :=
  cond (rDepthOK bh jh r a)
    (rDepthLowAux h σt bl jl r a (rDepthB σb bh r a) (rDepthJ σj jh r a) (rDepthΘ bh jh a)) 0

def rFadicLow (h σb σj σt bl bh jl jh r : ℕ) : ℕ :=
  rPrefix (rDepthLow h σb σj σt bl bh jl jh r) (Nat.add (Nat.div r 3) 1)

def rPlainLow (h σb σj σt r : ℕ) : ℕ :=
  rFastLow (rMin (Nat.mul r σb) 4012) (rMin (Nat.mul r σj) 1650) (Nat.mul r σt) 131312 h

def rCertLoss (S h σb σj σt bl bh jl jh i : ℕ) : ℕ :=
  cond (rIsFull σb σj σt (Nat.add i 1)) 0
    (Nat.sub S (rMax (rPlainLow h σb σj σt (Nat.add i 1)) (rFadicLow h σb σj σt bl bh jl jh (Nat.add i 1))))

end FadicGate
end Merged_FadicChunkRaw

-- merged module FadicCast
section Merged_FadicCast
/-!
# The raw evaluator computes the checked bounds

`rCertLoss_cast : ((rCertLoss S h σb σj σt bl bh jl jh i : ℕ) : ℤ) = certLoss S h … i`.

The accepted `denominator`, `cumulative` and `cappedCount` are evaluated in `ℕ`.  The two
subtractions of the accepted formulas never truncate because both sides are cardinalities
(`K1_13_2_2_2.proof` and `capped_card`).
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2 (cappedCount cumulative denominator)
open scoped BigOperators
open Finset
open private K1_13_2_2_3.cappedColumns K1_13_2_2_3.mem_cappedColumns K1_13_2_2_3.capped_card
  from ProximityPrize.SubmissionLower.Fast068
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)

/-! ### Raw forms are the plain forms -/

theorem cond_ble {α : Type*} (a b : ℕ) (x y : α) :
    cond (Nat.ble a b) x y = if a ≤ b then x else y := by
  by_cases h : a ≤ b
  · have hb : Nat.ble a b = true := Nat.ble_eq.mpr h
    rw [hb, if_pos h]
    rfl
  · have hb : Nat.ble a b = false := by
      cases hc : Nat.ble a b
      · rfl
      · exact absurd (Nat.ble_eq.mp hc) h
    rw [hb, if_neg h]
    rfl

theorem rMin_eq (a b : ℕ) : rMin a b = min a b := by
  unfold rMin
  rw [cond_ble]
  rfl

theorem rMax_eq (a b : ℕ) : rMax a b = max a b := by
  unfold rMax
  rw [cond_ble]
  by_cases h : a ≤ b
  · rw [if_pos h, max_eq_right h]
  · rw [if_neg h, max_eq_left (by omega)]

theorem rDenomSub_eq (v k : ℕ) : rDenomSub v k = denomSub v k := by
  unfold rDenomSub denomSub
  rw [cond_ble]
  rfl

theorem rCumAux_eq (d v : ℕ) : rCumAux d v = cumAux d v := by
  unfold rCumAux cumAux
  simp only [rDenomSub_eq]
  rfl

theorem rCumulative_eq (d u : ℕ) : rCumulative d u = cumulativeN d u := by
  unfold rCumulative cumulativeN
  rw [rMin_eq, rCumAux_eq]
  rfl

theorem rCapped_eq (d u t : ℕ) : rCapped d u t = cappedCountN d u t := by
  unfold rCapped cappedCountN
  rw [cond_ble, cond_ble]
  simp only [rCumulative_eq]
  rfl

/-! ### The plain forms compute the accepted counts -/

theorem denominator_neg {x : ℤ} (hx : x < 0) : denominator x = 0 := by
  unfold denominator
  simp [hx]

private theorem half_succ (r : ℕ) : ((r * (r + 1) / 2 : ℕ) : ℤ) = (r : ℤ) * ((r : ℤ) + 1) / 2 := by
  push_cast
  rfl

private theorem half_pred (r : ℕ) : ((r * (r - 1) / 2 : ℕ) : ℤ) = (r : ℤ) * ((r : ℤ) - 1) / 2 := by
  rcases r with _ | r
  · simp
  · have : r + 1 - 1 = r := by omega
    rw [this]
    push_cast
    ring_nf

private theorem cube_term (q : ℕ) :
    ((6 * q * (q - 1) * (q - 2) : ℕ) : ℤ) = 6 * (q : ℤ) * ((q : ℤ) - 1) * ((q : ℤ) - 2) := by
  rcases q with _ | _ | q
  · simp
  · simp
  · have h1 : q + 2 - 1 = q + 1 := by omega
    have h2 : q + 2 - 2 = q := by omega
    simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h2 ⊢
    rw [h1, h2]
    push_cast
    ring

theorem denomQR_cast (q r : ℕ) :
    ((denomQR q r : ℕ) : ℤ) =
      1 + (r : ℤ) * ((r : ℤ) + 1) / 2 +
        (q : ℤ) * (22 + 7 * (r : ℤ) + (r : ℤ) * ((r : ℤ) - 1) / 2) +
        (57 + 6 * (r : ℤ)) * ((q : ℤ) * ((q : ℤ) - 1) / 2) +
        6 * (q : ℤ) * ((q : ℤ) - 1) * ((q : ℤ) - 2) := by
  rw [← half_succ, ← half_pred, ← half_pred, ← cube_term]
  unfold denomQR
  push_cast
  ring

theorem denomN_cast (n : ℕ) : ((denomN n : ℕ) : ℤ) = denominator n := by
  unfold denomN denominator
  have h0 : ¬ ((n : ℤ) < 0) := by omega
  rw [if_neg h0]
  have hq : (n : ℤ) / 6 = ((n / 6 : ℕ) : ℤ) := by push_cast; rfl
  have hr : (n : ℤ) % 6 = ((n % 6 : ℕ) : ℤ) := by push_cast; rfl
  simp only [hq, hr]
  exact denomQR_cast (n / 6) (n % 6)

theorem denomSub_cast (v k : ℕ) : ((denomSub v k : ℕ) : ℤ) = denominator ((v : ℤ) - (k : ℤ)) := by
  unfold denomSub
  split
  · rename_i h
    rw [denomN_cast, Nat.cast_sub h]
  · rename_i h
    rw [denominator_neg (by omega)]
    rfl

/-- The accepted formula for `cumulative` with the negative terms collected. -/
private theorem cumulative_split (d u : ℕ) :
    cumulative d u =
      ((denomN (min u (3 * d)) + denomSub (min u (3 * d)) (2 * d + 3) +
          denomSub (min u (3 * d)) (2 * d + 4) + denomSub (min u (3 * d)) (2 * d + 5) : ℕ) : ℤ) -
      ((denomSub (min u (3 * d)) (d + 1) + denomSub (min u (3 * d)) (d + 2) +
          denomSub (min u (3 * d)) (d + 3) + denomSub (min u (3 * d)) (3 * d + 6) : ℕ) : ℤ) := by
  unfold cumulative
  have h1 : ¬ ((d : ℤ) < 0) := by omega
  have h2 : ¬ ((u : ℤ) < 0) := by omega
  have hv : min (u : ℤ) (3 * (d : ℤ)) = ((min u (3 * d) : ℕ) : ℤ) := by push_cast; rfl
  simp only [h1, h2, decide_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hv]
  set V := min u (3 * d)
  push_cast
  rw [denomN_cast, denomSub_cast, denomSub_cast, denomSub_cast, denomSub_cast, denomSub_cast,
    denomSub_cast, denomSub_cast]
  push_cast
  ring_nf

theorem cumulative_nonneg (d u : ℤ) : 0 ≤ cumulative d u := by
  rw [← K1_13_2_2_2.proof d u]
  positivity

theorem cumulativeN_cast (d u : ℕ) : ((cumulativeN d u : ℕ) : ℤ) = cumulative d u := by
  have hs := cumulative_split d u
  have hn := cumulative_nonneg d u
  unfold cumulativeN cumAux
  rw [hs] at hn
  rw [hs, Nat.cast_sub (by exact_mod_cast (sub_nonneg.mp hn))]

theorem cumulative_of_neg {d u : ℤ} (h : d < 0 ∨ u < 0) : cumulative d u = 0 := by
  unfold cumulative
  rcases h with h | h <;> simp [h]

theorem cappedCountN_cast (d u t : ℕ) : ((cappedCountN d u t : ℕ) : ℤ) = cappedCount d u t := by
  have hcc : cappedCount d u t = cumulative d u -
      cumulative ((d : ℤ) - (t : ℤ) - 1) ((u : ℤ) - 3 * ((t : ℤ) + 1)) := by
    unfold cappedCount
    have ht : ¬ ((t : ℤ) < 0) := by omega
    rw [if_neg ht]
  have hsub : ((if 3 * (t + 1) ≤ u then (if t + 1 ≤ d then cumulativeN (d - (t + 1)) (u - 3 * (t + 1))
      else 0) else 0 : ℕ) : ℤ) = cumulative ((d : ℤ) - (t : ℤ) - 1) ((u : ℤ) - 3 * ((t : ℤ) + 1)) := by
    split
    · rename_i hu
      split
      · rename_i hd
        rw [cumulativeN_cast, Nat.cast_sub hd, Nat.cast_sub hu]
        push_cast
        ring_nf
      · rename_i hd
        rw [cumulative_of_neg (Or.inl (by omega))]
        rfl
    · rename_i hu
      rw [cumulative_of_neg (Or.inr (by omega))]
      rfl
  have hn := cappedCount_nonneg d u t
  unfold cappedCountN
  rw [hcc, ← cumulativeN_cast, ← hsub] at hn
  rw [Nat.cast_sub (by exact_mod_cast (sub_nonneg.mp hn)), cumulativeN_cast, hsub, hcc]

theorem rCapped_cast (d u t : ℕ) : ((rCapped d u t : ℕ) : ℤ) = cappedCount d u t := by
  rw [rCapped_eq, cappedCountN_cast]

/-! ### The chunked chain -/

theorem rPrefix_cast (f : ℕ → ℕ) (n : ℕ) : ((rPrefix f n : ℕ) : ℤ) = ∑ k ∈ range n, (f k : ℤ) := by
  induction n with
  | zero => simp [rPrefix]
  | succ n ih =>
    rw [rPrefix, sum_range_succ, ← ih]
    rfl

theorem rSegHi_eq (base h m k : ℕ) : rSegHi base h m k = segHi base h m k := by
  unfold rSegHi segHi
  rw [rMin_eq]
  rfl

theorem rLowSeg_cast (J T Θ base h m k : ℕ) :
    ((rLowSeg J T Θ base h m k : ℕ) : ℤ) = lowSeg J T Θ base h m k := by
  unfold rLowSeg rLowSegAux lowSeg lowDeg
  rw [cond_ble, rSegHi_eq, rMin_eq]
  show ((if 26 * segHi base h m k ≤ Θ then rCapped (min (segLo base h k) ((Θ - 26 * segHi base h m k) / 25)) J T else 0 : ℕ) : ℤ) = _
  by_cases hc : 26 * segHi base h m k ≤ Θ
  · rw [if_pos hc, if_pos hc, rCapped_cast]
  · rw [if_neg hc, if_neg hc]
    rfl

theorem rHighSeg_cast (J T Θ base h m k : ℕ) :
    ((rHighSeg J T Θ base h m k : ℕ) : ℤ) = highSeg J T Θ base h m k := by
  unfold rHighSeg rHighSegAux highSeg highDeg
  rw [cond_ble, rSegHi_eq, rMin_eq]
  show ((if 26 * segLo base h k ≤ Θ then rCapped (min (segHi base h m k) ((Θ - 26 * segLo base h k) / 25)) J T else 0 : ℕ) : ℤ) = _
  by_cases hc : 26 * segLo base h k ≤ Θ
  · rw [if_pos hc, if_pos hc, rCapped_cast]
  · rw [if_neg hc, if_neg hc]
    rfl

theorem rSegSumLow_cast (J T Θ base h m : ℕ) :
    ((rSegSumLow J T Θ base h m : ℕ) : ℤ) = segSumLow J T Θ base h m := by
  unfold rSegSumLow segSumLow
  show ((h * rPrefix (rLowSeg J T Θ base h m) (m / h) + (m % h) * rLowSeg J T Θ base h m (m / h) : ℕ)
    : ℤ) = _
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, rPrefix_cast, rLowSeg_cast]
  simp only [rLowSeg_cast]

theorem rSegSumHigh_cast (J T Θ base h m : ℕ) :
    ((rSegSumHigh J T Θ base h m : ℕ) : ℤ) = segSumHigh J T Θ base h m := by
  unfold rSegSumHigh segSumHigh
  show ((h * rPrefix (rHighSeg J T Θ base h m) (m / h) + (m % h) * rHighSeg J T Θ base h m (m / h) : ℕ)
    : ℤ) = _
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, rPrefix_cast, rHighSeg_cast]
  simp only [rHighSeg_cast]

theorem rFlatLo_eq (B J : ℕ) : rFlatLo B J = flatLo B J := by
  unfold rFlatLo flatLo
  rw [rMin_eq]

theorem rFlatHi_eq (B J Θ : ℕ) : rFlatHi B J Θ = flatHi B J Θ := by
  unfold rFlatHi flatHi
  rw [cond_ble, rMax_eq, rMin_eq, rFlatLo_eq]
  rfl

theorem rFastLow_cast (B J T Θ h : ℕ) : ((rFastLow B J T Θ h : ℕ) : ℤ) = fastLow B J T Θ h := by
  unfold rFastLow rFastLowAux fastLow
  rw [rFlatLo_eq, rFlatHi_eq]
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  push_cast
  rw [rSegSumLow_cast, rSegSumLow_cast, rCapped_cast]

theorem rFastHigh_cast (B J T Θ h : ℕ) : ((rFastHigh B J T Θ h : ℕ) : ℤ) = fastHigh B J T Θ h := by
  unfold rFastHigh rFastHighAux fastHigh
  rw [rFlatLo_eq, rFlatHi_eq]
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  push_cast
  rw [rSegSumHigh_cast, rSegSumHigh_cast, rCapped_cast]

theorem rDepthB_eq (σb xb r a : ℕ) : rDepthB σb xb r a = depthB σb xb r a := by
  unfold rDepthB depthB
  rw [rMin_eq]
  rfl

theorem rDepthJ_eq (σj xj r a : ℕ) : rDepthJ σj xj r a = depthJ σj xj r a := by
  unfold rDepthJ depthJ
  rw [rMin_eq]
  rfl

theorem rDepthΘ_eq (xb xj a : ℕ) : rDepthΘ xb xj a = depthΘ xb xj a := rfl

theorem ble_true (a b : ℕ) : Nat.ble a b = true ↔ a ≤ b := by
  rw [Nat.ble_eq]

theorem rDepthOK_iff (xb xj r a : ℕ) : rDepthOK xb xj r a = true ↔ DepthOK xb xj r a := by
  unfold rDepthOK DepthOK
  simp only [Bool.and_eq_true, ble_true, Nat.mul_eq, Nat.add_eq]
  omega

theorem natSub_cast (a b : ℕ) : ((a - b : ℕ) : ℤ) = max 0 ((a : ℤ) - (b : ℤ)) := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h, max_eq_right (by omega)]
  · rw [Nat.sub_eq_zero_of_le (by omega), max_eq_left (by omega)]
    rfl

theorem rMultHigh_cast (h σb σj σt bl bh jl jh r a : ℕ) :
    ((rMultHighAux h σt bl jl r a (rDepthB σb bh r a) (rDepthJ σj jh r a) (rDepthΘ bh jh a) : ℕ) : ℤ) =
      multHigh h σb σj σt bl bh jl jh r a := by
  unfold rMultHighAux multHigh
  rw [rDepthB_eq, rDepthJ_eq, rDepthΘ_eq]
  by_cases hg : bl ≤ depthB σb bh r a ∧ jl ≤ depthJ σj jh r a ∧ 26 * bl ≤ depthΘ bh jh a
  · have hb : (Nat.ble bl (depthB σb bh r a) && Nat.ble jl (depthJ σj jh r a) &&
        Nat.ble (Nat.mul 26 bl) (depthΘ bh jh a)) = true := by
      simp only [Bool.and_eq_true, ble_true, Nat.mul_eq]
      exact ⟨⟨hg.1, hg.2.1⟩, hg.2.2⟩
    rw [hb, if_pos hg]
    show ((rFastHigh _ _ _ _ h : ℕ) : ℤ) = _
    rw [rFastHigh_cast]
    rfl
  · have hb : (Nat.ble bl (depthB σb bh r a) && Nat.ble jl (depthJ σj jh r a) &&
        Nat.ble (Nat.mul 26 bl) (depthΘ bh jh a)) = false := by
      cases hc : (Nat.ble bl (depthB σb bh r a) && Nat.ble jl (depthJ σj jh r a) &&
        Nat.ble (Nat.mul 26 bl) (depthΘ bh jh a))
      · rfl
      · simp only [Bool.and_eq_true, ble_true, Nat.mul_eq] at hc
        exact absurd ⟨hc.1.1, hc.1.2, hc.2⟩ hg
    rw [hb, if_neg hg]
    rfl

theorem rDepthLow_cast (h σb σj σt bl bh jl jh r a : ℕ) :
    ((rDepthLow h σb σj σt bl bh jl jh r a : ℕ) : ℤ) = depthLow h σb σj σt bl bh jl jh r a := by
  unfold rDepthLow depthLow
  by_cases hok : DepthOK bh jh r a
  · rw [(rDepthOK_iff bh jh r a).mpr hok, if_pos hok]
    show ((rDepthLowAux h σt bl jl r a _ _ _ : ℕ) : ℤ) = _
    unfold rDepthLowAux
    simp only [Nat.sub_eq]
    rw [natSub_cast, rMultHigh_cast, rFastLow_cast, rDepthB_eq, rDepthJ_eq, rDepthΘ_eq]
    rfl
  · have hb : rDepthOK bh jh r a = false := by
      cases hc : rDepthOK bh jh r a
      · rfl
      · exact absurd ((rDepthOK_iff bh jh r a).mp hc) hok
    rw [hb, if_neg hok]
    rfl

theorem rFadicLow_cast (h σb σj σt bl bh jl jh r : ℕ) :
    ((rFadicLow h σb σj σt bl bh jl jh r : ℕ) : ℤ) = fadicLow h σb σj σt bl bh jl jh r := by
  unfold rFadicLow fadicLow
  rw [rPrefix_cast]
  simp only [rDepthLow_cast]
  rfl

theorem rPlainLow_cast (h σb σj σt r : ℕ) :
    ((rPlainLow h σb σj σt r : ℕ) : ℤ) = plainLow h σb σj σt r := by
  unfold rPlainLow plainLow
  rw [rMin_eq, rMin_eq, rFastLow_cast]
  rfl

theorem rIsFull_iff (σb σj σt r : ℕ) : rIsFull σb σj σt r = true ↔ IsFull σb σj σt r := by
  unfold rIsFull IsFull
  simp only [Bool.and_eq_true, ble_true, Nat.mul_eq]
  tauto

/-- **The raw certificate value is the checked certified loss.** -/
theorem rCertLoss_cast (S h σb σj σt bl bh jl jh i : ℕ) :
    ((rCertLoss S h σb σj σt bl bh jl jh i : ℕ) : ℤ) = certLoss S h σb σj σt bl bh jl jh i := by
  unfold rCertLoss certLoss
  by_cases hf : IsFull σb σj σt (i + 1)
  · rw [(rIsFull_iff σb σj σt (Nat.add i 1)).mpr hf, if_pos hf]
    rfl
  · have hb : rIsFull σb σj σt (Nat.add i 1) = false := by
      cases hc : rIsFull σb σj σt (Nat.add i 1)
      · rfl
      · exact absurd ((rIsFull_iff σb σj σt (Nat.add i 1)).mp hc) hf
    rw [hb, if_neg hf]
    show (((S - rMax (rPlainLow h σb σj σt (i + 1)) (rFadicLow h σb σj σt bl bh jl jh (i + 1)) : ℕ)) : ℤ) = _
    rw [natSub_cast, rMax_eq, Nat.cast_max, rPlainLow_cast, rFadicLow_cast]

end FadicGate

#print axioms FadicGate.rCapped_cast
#print axioms FadicGate.rCertLoss_cast
end Merged_FadicCast

/-!
# Certificates for the variable-depth gate

* `varDepthLow ≤ varDepthDim`, `varPlainLow ≤ varPlainDim` (blocks of `h` grades);
* `varLevelLoss`: the certified loss of one level from its plain box and its literal depth list;
* `rVarLevelLoss_cast`: the kernel-raw evaluator computes it;
* `loss_of_varCert`: from the per-level values to the total loss of `varGateDim`.
-/

set_option autoImplicit false

namespace FadicGate

open K1_13_2 (cappedCount)
open scoped BigOperators
open Finset

/-! ### Chunked bounds -/

def varMultHigh (h bl jl tl L B J T Θ : ℕ) : ℤ :=
  if bl ≤ B ∧ jl ≤ J ∧ tl ≤ T ∧ L ≤ Θ then fastHigh (B - bl) (J - jl) (T - tl) (Θ - L) h else 0

def varDepthLow (h bl bh jl jh tl L H a : ℕ) : Entry → ℤ
  | none => 0
  | some (B, J, T) =>
    if BoxOK bh jh H a B J then
      max 0 (fastLow B J T (varΘ H a) h - varMultHigh h bl jl tl L B J T (varΘ H a))
    else 0

theorem varMult_le (h bl jl tl L B J T Θ : ℕ) (hh : 0 < h) :
    varMult bl jl tl L B J T Θ ≤ varMultHigh h bl jl tl L B J T Θ := by
  unfold varMult varMultHigh
  split
  · exact le_fastHigh _ _ _ _ hh
  · exact le_rfl

theorem varDepthLow_le (h bl bh jl jh tl L H a : ℕ) (e : Entry) (hh : 0 < h) :
    varDepthLow h bl bh jl jh tl L H a e ≤ varDepthDim bl bh jl jh tl L H a e := by
  rcases e with _ | ⟨B, J, T⟩
  · exact le_rfl
  · simp only [varDepthLow, varDepthDim]
    split
    · apply max_le_max le_rfl
      have h1 := fastLow_le B J T (varΘ H a) hh
      have h2 := varMult_le h bl jl tl L B J T (varΘ H a) hh
      linarith
    · exact le_rfl

def varPlainLow (h B J T : ℕ) : ℤ := fastLow (min B 4012) (min J 1650) T 131312 h

theorem varPlainLow_le (h B J T : ℕ) (hh : 0 < h) : varPlainLow h B J T ≤ varPlainDim B J T :=
  fastLow_le _ _ _ _ hh

/-- The certified loss of one level. -/
def varLevelLoss (S : ℤ) (h bl bh jl jh tl L H : ℕ) (plain : ℕ × ℕ × ℕ) (es : List Entry) : ℤ :=
  max 0 (S - max (varPlainLow h plain.1 plain.2.1 plain.2.2)
    (∑ a ∈ range es.length, varDepthLow h bl bh jl jh tl L H a (es.getD a none)))

/-- The certified loss of level `i + 1` of a schedule given by tables. -/
def varCertLoss (S : ℤ) (h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (i : ℕ) : ℤ :=
  if Rt ≤ i + 1 then 0 else varLevelLoss S h bl bh jl jh tl L H (plain (i + 1)) (table (i + 1))

theorem gateLoss_le_varCertLoss (S : ℤ) (h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (i : ℕ) (hh : 0 < h) :
    max 0 (S - varGateDim S bl bh jl jh tl L H Rt plain (fun r => (table r).length)
      (fun r a => (table r).getD a none) (i + 1)) ≤
      varCertLoss S h bl bh jl jh tl L H Rt plain table i := by
  unfold varCertLoss varGateDim
  split
  · simp
  · unfold varLevelLoss
    apply max_le_max le_rfl
    have h1 := varPlainLow_le h (plain (i + 1)).1 (plain (i + 1)).2.1 (plain (i + 1)).2.2 hh
    have h2 : (∑ a ∈ range (table (i + 1)).length,
        varDepthLow h bl bh jl jh tl L H a ((table (i + 1)).getD a none)) ≤
        varFadicDim bl bh jl jh tl L H (table (i + 1)).length (fun a => (table (i + 1)).getD a none) :=
      sum_le_sum fun a _ => varDepthLow_le h bl bh jl jh tl L H a _ hh
    have h3 := max_le_max h1 h2
    linarith

/-- **Certificate.**  The total gate loss is at most the sum of the certified level losses. -/
theorem loss_of_varCert (S : ℤ) (h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (Ltot : ℤ) (hh : 0 < h)
    (hsum : ∑ i ∈ range Rt, varCertLoss S h bl bh jl jh tl L H Rt plain table i = Ltot) (N : ℕ) :
    ∑ i ∈ range N, max 0 (S - varGateDim S bl bh jl jh tl L H Rt plain
      (fun r => (table r).length) (fun r a => (table r).getD a none) (i + 1)) ≤ Ltot := by
  have hzero (i : ℕ) (hi : Rt ≤ i) : varCertLoss S h bl bh jl jh tl L H Rt plain table i = 0 := by
    unfold varCertLoss
    exact if_pos (by omega)
  have hnonneg (i : ℕ) : 0 ≤ varCertLoss S h bl bh jl jh tl L H Rt plain table i := by
    unfold varCertLoss
    split
    · exact le_rfl
    · exact le_max_left _ _
  refine (sum_le_sum fun i _ =>
    gateLoss_le_varCertLoss S h bl bh jl jh tl L H Rt plain table i hh).trans ?_
  rw [← hsum]
  rcases le_total N Rt with hN | hN
  · exact sum_le_sum_of_subset_of_nonneg (range_mono hN) (fun i _ _ => hnonneg i)
  · rw [← sum_range_add_sum_Ico _ hN]
    have : ∑ i ∈ Ico Rt N, varCertLoss S h bl bh jl jh tl L H Rt plain table i = 0 :=
      sum_eq_zero fun i hi => hzero i (mem_Ico.mp hi).1
    rw [this, add_zero]

/-! ### Kernel-raw evaluator -/

def rBoxOK (bh jh H a B J : ℕ) : Bool :=
  Nat.ble (Nat.add B (Nat.mul a bh)) 4012 && Nat.ble (Nat.add J (Nat.mul a jh)) 1650 &&
    Nat.ble (Nat.mul a H) 131312

def rVarMultHigh (h bl jl tl L B J T Θ : ℕ) : ℕ :=
  cond (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L Θ)
    (rFastHigh (Nat.sub B bl) (Nat.sub J jl) (Nat.sub T tl) (Nat.sub Θ L) h) 0

def rVarDepthAux (h bl jl tl L B J T Θ : ℕ) : ℕ :=
  Nat.sub (rFastLow B J T Θ h) (rVarMultHigh h bl jl tl L B J T Θ)

def rVarDepthLow (h bl bh jl jh tl L H a : ℕ) : Entry → ℕ
  | none => 0
  | some (B, J, T) =>
    cond (rBoxOK bh jh H a B J)
      (rVarDepthAux h bl jl tl L B J T (Nat.sub 131312 (Nat.mul a H))) 0

def rVarList (h bl bh jl jh tl L H : ℕ) : ℕ → List Entry → ℕ
  | _, [] => 0
  | k, e :: es => Nat.add (rVarDepthLow h bl bh jl jh tl L H k e) (rVarList h bl bh jl jh tl L H (k + 1) es)

def rVarPlainLow (h B J T : ℕ) : ℕ := rFastLow (rMin B 4012) (rMin J 1650) T 131312 h

def rVarLevelLoss (S h bl bh jl jh tl L H pB pJ pT : ℕ) (es : List Entry) : ℕ :=
  Nat.sub S (rMax (rVarPlainLow h pB pJ pT) (rVarList h bl bh jl jh tl L H 0 es))

/-! ### The raw evaluator computes the certified loss -/

theorem rBoxOK_iff (bh jh H a B J : ℕ) : rBoxOK bh jh H a B J = true ↔ BoxOK bh jh H a B J := by
  unfold rBoxOK BoxOK
  simp only [Bool.and_eq_true, ble_true, Nat.mul_eq, Nat.add_eq]
  tauto

theorem rVarMultHigh_cast (h bl jl tl L B J T Θ : ℕ) :
    ((rVarMultHigh h bl jl tl L B J T Θ : ℕ) : ℤ) = varMultHigh h bl jl tl L B J T Θ := by
  unfold rVarMultHigh varMultHigh
  by_cases hg : bl ≤ B ∧ jl ≤ J ∧ tl ≤ T ∧ L ≤ Θ
  · have hb : (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L Θ) = true := by
      simp only [Bool.and_eq_true, ble_true]
      exact ⟨⟨⟨hg.1, hg.2.1⟩, hg.2.2.1⟩, hg.2.2.2⟩
    rw [hb, if_pos hg]
    exact rFastHigh_cast _ _ _ _ _
  · have hb : (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L Θ) = false := by
      cases hc : (Nat.ble bl B && Nat.ble jl J && Nat.ble tl T && Nat.ble L Θ)
      · rfl
      · simp only [Bool.and_eq_true, ble_true] at hc
        exact absurd ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩ hg
    rw [hb, if_neg hg]
    rfl

theorem rVarDepthLow_cast (h bl bh jl jh tl L H a : ℕ) (e : Entry) :
    ((rVarDepthLow h bl bh jl jh tl L H a e : ℕ) : ℤ) = varDepthLow h bl bh jl jh tl L H a e := by
  rcases e with _ | ⟨B, J, T⟩
  · rfl
  · simp only [rVarDepthLow, varDepthLow]
    by_cases hok : BoxOK bh jh H a B J
    · rw [(rBoxOK_iff bh jh H a B J).mpr hok, if_pos hok]
      show ((Nat.sub (rFastLow B J T (Nat.sub 131312 (Nat.mul a H)) h)
        (rVarMultHigh h bl jl tl L B J T (Nat.sub 131312 (Nat.mul a H))) : ℕ) : ℤ) = _
      rw [Nat.sub_eq, natSub_cast, rFastLow_cast, rVarMultHigh_cast]
      rfl
    · have hb : rBoxOK bh jh H a B J = false := by
        cases hc : rBoxOK bh jh H a B J
        · rfl
        · exact absurd ((rBoxOK_iff bh jh H a B J).mp hc) hok
      rw [hb, if_neg hok]
      rfl

theorem rVarList_cast (h bl bh jl jh tl L H : ℕ) (es : List Entry) (k : ℕ) :
    ((rVarList h bl bh jl jh tl L H k es : ℕ) : ℤ) =
      ∑ a ∈ range es.length, varDepthLow h bl bh jl jh tl L H (k + a) (es.getD a none) := by
  induction es generalizing k with
  | nil => simp [rVarList]
  | cons e es ih =>
    rw [rVarList, Nat.add_eq, Nat.cast_add, ih (k + 1), rVarDepthLow_cast, List.length_cons,
      sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    congr 1
    omega

theorem rVarPlainLow_cast (h B J T : ℕ) :
    ((rVarPlainLow h B J T : ℕ) : ℤ) = varPlainLow h B J T := by
  unfold rVarPlainLow varPlainLow
  rw [rMin_eq, rMin_eq, rFastLow_cast]

/-- **The raw level loss is the certified level loss.** -/
theorem rVarLevelLoss_cast (S h bl bh jl jh tl L H pB pJ pT : ℕ) (es : List Entry) :
    ((rVarLevelLoss S h bl bh jl jh tl L H pB pJ pT es : ℕ) : ℤ) =
      varLevelLoss S h bl bh jl jh tl L H (pB, pJ, pT) es := by
  unfold rVarLevelLoss varLevelLoss
  rw [Nat.sub_eq, natSub_cast, rMax_eq, Nat.cast_max, rVarPlainLow_cast, rVarList_cast]
  simp only [zero_add]

/-! ### Row lemmas for generated certificates -/

/-- One level of a generated certificate: the table lookups are closed by `rfl` and the value by
the raw evaluator. -/
theorem varCertLoss_row (S h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (i pB pJ pT : ℕ) (es : List Entry) (v : ℕ)
    (hi : ¬ Rt ≤ i + 1) (hp : plain (i + 1) = (pB, pJ, pT)) (ht : table (i + 1) = es)
    (hv : rVarLevelLoss S h bl bh jl jh tl L H pB pJ pT es = v) :
    varCertLoss (S : ℤ) h bl bh jl jh tl L H Rt plain table i = (v : ℤ) := by
  unfold varCertLoss
  rw [if_neg hi, hp, ht, ← rVarLevelLoss_cast, hv]

theorem varCertLoss_terminal (S : ℤ) (h bl bh jl jh tl L H Rt : ℕ) (plain : ℕ → ℕ × ℕ × ℕ)
    (table : ℕ → List Entry) (i : ℕ) (hi : Rt ≤ i + 1) :
    varCertLoss S h bl bh jl jh tl L H Rt plain table i = ((0 : ℕ) : ℤ) := by
  unfold varCertLoss
  rw [if_pos hi]
  rfl

end FadicGate

#print axioms FadicGate.loss_of_varCert
#print axioms FadicGate.rVarLevelLoss_cast
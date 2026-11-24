import ProximityPrize.SubmissionLower.FadicGateDim

set_option Elab.async false

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
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
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












end FadicGate

#print axioms FadicGate.cappedCount_mono
#print axioms FadicGate.sum_div_block
#print axioms FadicGate.fastLow_le
#print axioms FadicGate.le_fastHigh

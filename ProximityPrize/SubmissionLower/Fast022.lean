import Mathlib.Algebra.AffineMonoid.UniqueSums
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast029
set_option autoImplicit true
section
namespace K1_13_2_3
open K1_13_2
open scoped BigOperators
def baseline (i : BlockIndex) : ℕ := blockBound i (fun _ => 0)
structure Powers where
  value : ℕ
  top : ℕ
  cubic : ℕ
def Powers.expand (p : Powers) : Fin 11 → ℕ :=
  ![p.value, 0, 0, p.top, 0, 0, 0, 0, 0, 0, p.cubic]
structure Window where
  gradeLo : ℕ
  gradeHi : ℕ
  offsetLo : ℕ
  offsetHi : ℕ
  diagonalLo : ℕ
  diagonalHi : ℕ
def Window.Contains (w : Window) (i : BlockIndex) : Prop :=
  w.gradeLo ≤ i.1.val ∧ i.1.val < w.gradeHi ∧
  w.offsetLo ≤ i.2.val ∧ i.2.val ≤ w.offsetHi ∧
  w.diagonalLo ≤ i.1.val + i.2.val ∧ i.1.val + i.2.val ≤ w.diagonalHi
instance (w : Window) (i : BlockIndex) : Decidable (w.Contains i) := by
  unfold Window.Contains
  infer_instance
def w1 : Window := ⟨1004, 2008, 993, 1581, 3000, 3070⟩
def w2 : Window := ⟨2008, 3012, 322, 1062, 3000, 3419⟩
def w3 : Window := ⟨3012, 3514, 23, 408, 3333, 3796⟩
def w4 : Window := ⟨3514, 4013, 0, 282, 3537, 4170⟩
def baselineSumOn (S : Finset BlockIndex) (lo hi : ℕ) : ℕ :=
  ∑ i ∈ S, if lo ≤ i.1.val ∧ i.1.val < hi then baseline i else 0
abbrev baselineSum (lo hi : ℕ) : ℕ := baselineSumOn Finset.univ lo hi
def savings (i : BlockIndex) (p : Powers) : ℕ := baseline i - blockBound i p.expand
def savingsSum (w : Window) (p : BlockIndex → Powers) : ℕ :=
  ∑ i : BlockIndex, if w.Contains i then savings i (p i) else 0
theorem residualFlag_expand (F : Flag) (p : Powers) :
    residualFlag F p.expand =
      ⟨F.degree - ((p.value : ℤ) + p.top + 3 * p.cubic),
        F.lower - (3 * (p.top : ℤ) + 2 * p.cubic),
        F.upper - (3 * (p.top : ℤ) + 3 * p.cubic),
        F.cap - ((p.top : ℤ) + p.cubic),
        F.order - (2 * (p.top : ℤ) + 3 * p.cubic)⟩ := by
  simp [residualFlag, Powers.expand, Fin.sum_univ_succ, factorFlag]
  ring_nf
  simp
end K1_13_2_3
end
section
namespace K1_13_2_3
open K1_13_2
open scoped BigOperators
private def difference (k : ℕ) (f : ℤ → ℤ) (u : ℤ) : ℤ := f u - f (u - k)
private theorem difference_comm (a b : ℕ) (f : ℤ → ℤ) :
    difference a (difference b f) = difference b (difference a f) := by
  funext u
  unfold difference
  rw [show u - (a : ℤ) - b = u - (b : ℤ) - a by ring]
  ring
private theorem difference_mul (k n : ℕ) (f : ℤ → ℤ) (u : ℤ) :
    difference (k * n) f u = ∑ j ∈ Finset.range n, difference k f (u - (k : ℤ) * j) := by
  induction n with
  | zero => simp [difference]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [difference, Nat.cast_mul, Nat.cast_succ]
    rw [show u - (k : ℤ) * ((n : ℤ) + 1) = u - (k : ℤ) * n - k by ring]
    ring
private theorem difference_mono_of_dvd {a b : ℕ} {f : ℤ → ℤ} (h : a ∣ b)
    (hm : Monotone (difference a f)) : Monotone (difference b f) := by
  obtain ⟨n, rfl⟩ := h
  intro u v huv
  rw [difference_mul, difference_mul]
  exact Finset.sum_le_sum fun j _ => hm (sub_le_sub_right huv _)
private theorem mono_of_difference_nonneg {f : ℤ → ℤ}
    (h : ∀ u, 0 ≤ difference 1 f u) : Monotone f := by
  intro u v huv
  let n := (v - u).toNat
  have hn : (n : ℤ) = v - u := Int.toNat_of_nonneg (by omega)
  have hz : 0 ≤ difference (1 * n) f v := by
    rw [difference_mul]
    exact Finset.sum_nonneg fun _ _ => h _
  simpa only [difference, Nat.cast_one, Nat.cast_mul, one_mul, hn, sub_sub_cancel,
    sub_nonneg] using hz
private def polyDen (q r : ℤ) : ℤ :=
  2 + r * (r + 1) + q * (44 + 14 * r + r * (r - 1)) +
    (57 + 6 * r) * (q * (q - 1)) + 12 * q * (q - 1) * (q - 2)
private theorem twice_half (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
private theorem scaled_denominator (u : ℤ) (hu : 0 ≤ u) :
    2 * denominator u = polyDen (u / 6) (u % 6) := by
  let q := u / 6
  let r := u % 6
  simp only [denominator, not_lt.mpr hu, ite_false, polyDen]
  change 2 * (1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)) = _
  have h := twice_half (r + 1)
  rw [show (r + 1) * (r + 1 - 1) = r * (r + 1) by ring] at h
  change _ = 2 + r * (r + 1) + q * (44 + 14 * r + r * (r - 1)) +
    (57 + 6 * r) * (q * (q - 1)) + 12 * q * (q - 1) * (q - 2)
  linear_combination h + q * twice_half r + (57 + 6 * r) * twice_half q
private theorem scaled_shift (u k : ℤ) (h : k ≤ u) :
    2 * denominator (u - k) = polyDen (u / 6 + (u % 6 - k) / 6) ((u % 6 - k) % 6) := by
  rw [scaled_denominator _ (by omega)]
  congr 1 <;> omega
private theorem denominator_of_neg (u : ℤ) (h : u < 0) : denominator u = 0 := by
  simp only [denominator, ite_eq_left h]
private theorem simple_step (u : ℤ) :
    difference 1 (difference 2 (difference 3 denominator)) u = if u < 0 then 0 else 1 := by
  by_cases hu : u < 0
  · simp (disch := omega) only [difference, denominator_of_neg, hu, sub_self, ite_true]
  by_cases hs : u < 8
  · interval_cases u <;> decide
  rw [ite_eq_right hu]
  have hf : difference 1 (difference 2 (difference 3 denominator)) u =
      denominator u - denominator (u - 1) - denominator (u - 2) +
        denominator (u - 4) + denominator (u - 5) - denominator (u - 6) := by
    simp only [difference, Nat.cast_ofNat, Nat.cast_one]
    rw [show u - 2 - 3 = u - 5 by ring, show u - 1 - 3 = u - 4 by ring,
      show u - 1 - 2 = u - 3 by ring, show u - 3 - 3 = u - 6 by ring]
    ring
  rw [hf]
  apply (mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide))
  have hh (k : ℤ) (hk : k ≤ 8) := scaled_shift u k (by omega)
  have h0 := hh 0 (by decide)
  rw [sub_zero] at h0
  have h1 := hh 1 (by decide)
  have h2 := hh 2 (by decide)
  have h4 := hh 4 (by decide)
  have h5 := hh 5 (by decide)
  have h6 := hh 6 (by decide)
  have hd : 0 ≤ u % 6 := by omega
  have hb : u % 6 < 6 := by omega
  generalize u % 6 = r at h0 h1 h2 h4 h5 h6 hd hb
  interval_cases r <;> norm_num [polyDen] at h0 h1 h2 h4 h5 h6 <;>
    linear_combination (norm := ring_nf) h0 - h1 - h2 + h4 + h5 - h6
private theorem missing_one_step (u : ℤ) :
    difference 1 (difference 1 (difference 6 denominator)) u =
      if u < 0 ∨ u = 1 then 0 else 1 := by
  by_cases hu : u < 0
  · simp (disch := omega) only [difference, denominator_of_neg, hu, sub_self, true_or, ite_true]
  by_cases hs : u < 8
  · interval_cases u <;> decide
  rw [ite_eq_right (by omega)]
  have hf : difference 1 (difference 1 (difference 6 denominator)) u =
      denominator u - 2 * denominator (u - 1) + denominator (u - 2) -
        denominator (u - 6) + 2 * denominator (u - 7) - denominator (u - 8) := by
    simp only [difference, Nat.cast_ofNat, Nat.cast_one]
    rw [show u - 1 - 6 = u - 7 by ring, show u - 1 - 1 = u - 2 by ring,
      show u - 2 - 6 = u - 8 by ring]
    ring
  rw [hf]
  apply (mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by decide))
  have hh (k : ℤ) (hk : k ≤ 8) := scaled_shift u k (by omega)
  have h0 := hh 0 (by decide)
  rw [sub_zero] at h0
  have h1 := hh 1 (by decide)
  have h2 := hh 2 (by decide)
  have h6 := hh 6 (by decide)
  have h7 := hh 7 (by decide)
  have h8 := hh 8 (by decide)
  have hd : 0 ≤ u % 6 := by omega
  have hb : u % 6 < 6 := by omega
  generalize u % 6 = r at h0 h1 h2 h6 h7 h8 hd hb
  interval_cases r <;> norm_num [polyDen] at h0 h1 h2 h6 h7 h8 <;>
    linear_combination (norm := ring_nf) h0 - 2*h1 + h2 - h6 + 2*h7 - h8
private theorem difference_mono_three {a b c k l m : ℕ} (f : ℤ → ℤ)
    (ha : k ∣ a) (hb : l ∣ b) (hc : m ∣ c)
    (hm : Monotone (difference k (difference l (difference m f)))) :
    Monotone (difference a (difference b (difference c f))) := by
  have H₁ := difference_mono_of_dvd ha hm
  rw [difference_comm a l] at H₁
  have H₂ := difference_mono_of_dvd hb H₁
  rw [difference_comm b a, difference_comm b m, difference_comm a m] at H₂
  have H₃ := difference_mono_of_dvd hc H₂
  rwa [difference_comm c a, difference_comm c b] at H₃
private theorem simple_step_mono : Monotone (difference 1 (difference 2 (difference 3 denominator))) := by
  intro u v huv
  rw [simple_step, simple_step]
  split <;> split <;> omega
private theorem special_step_mono (a : ℕ) (ha : 2 ≤ a) :
    Monotone (difference a (difference 1 (difference 6 denominator))) := by
  apply mono_of_difference_nonneg
  intro u
  rw [difference_comm 1 a]
  simp only [difference]
  change 0 ≤ difference 1 (difference 1 (difference 6 denominator)) u -
    difference 1 (difference 1 (difference 6 denominator)) (u - a)
  rw [missing_one_step, missing_one_step]
  split <;> split <;> omega
private def rawCount (d : ℕ) : ℤ → ℤ :=
  difference (d + 1) (difference (d + 2) (difference (d + 3) denominator))
private theorem rawCount_mono (d : ℕ) : Monotone (rawCount d) := by
  unfold rawCount
  have hmod : d % 6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases hr : d % 6
  · exact difference_mono_three _ (one_dvd _) (by omega) (by omega) simple_step_mono
  · rw [difference_comm (d+2) (d+3), difference_comm (d+1) (d+3)]
    exact difference_mono_three _ (one_dvd _) (by omega) (by omega) simple_step_mono
  · rw [difference_comm (d+1) (d+2), difference_comm (d+1) (d+3), difference_comm (d+2) (d+3)]
    exact difference_mono_three _ (one_dvd _) (by omega) (by omega) simple_step_mono
  · rw [difference_comm (d+1) (d+2)]
    exact difference_mono_three _ (one_dvd _) (by omega) (by omega) simple_step_mono
  · have ha : 2 ≤ d + 1 := by omega
    rw [difference_comm (d+2) (d+3)]
    exact difference_mono_three _ (dvd_refl _) (one_dvd _) (by omega) (special_step_mono _ ha)
  · rw [difference_comm (d+1) (d+2), difference_comm (d+1) (d+3)]
    exact difference_mono_three _ (one_dvd _) (by omega) (by omega) simple_step_mono
private theorem rawCount_eq_zero (d : ℕ) (u : ℤ) (h : u < 0) : rawCount d u = 0 := by
  simp (disch := omega) only [rawCount, difference, denominator_of_neg, sub_self]
private theorem cumulative_eq_raw (d : ℕ) (u : ℤ) :
    cumulative d u = rawCount d (min u (3 * (d : ℤ))) := by
  by_cases hu : u < 0
  · rw [min_eq_left (by omega), rawCount_eq_zero _ _ hu]
    simp [cumulative, hu]
  · have hd : ¬ (d : ℤ) < 0 := by omega
    simp [cumulative, hu, hd, rawCount, difference]
    ring_nf
theorem cumulative_mono (d : ℕ) : Monotone (cumulative (d : ℤ)) := by
  intro u v huv
  rw [cumulative_eq_raw, cumulative_eq_raw]
  exact rawCount_mono d (min_le_min_right _ huv)
private theorem baseline_le_target (i : BlockIndex) :
    baseline i ≤ (targetCount (initialFlag i)).toNat := by
  have hk : kernelLower (initialFlag i) = oldCount (initialFlag i) - targetCount (initialFlag i) := by
    simp [kernelLower, initialFlag]
  unfold baseline blockBound
  dsimp
  split
  · exact Nat.zero_le _
  · apply Int.toNat_le_toNat
    apply (min_le_right _ _).trans
    have hm : kernelLower (initialFlag i) ≤ max 0 (max (kernelLower (initialFlag i))
        (kernelLower (residualFlag (initialFlag i) (fun _ => 0)))) :=
      (le_max_left _ _).trans (le_max_right _ _)
    omega
private theorem targetCount_low (s : Fin 4013) (j : Fin 4650) (hs : s.val < 551) :
    targetCount (initialFlag (s,j)) = cumulative (s.val : ℤ) (4649 - (s.val : ℤ) - j.val) -
      cumulative (s.val : ℤ) (1649 - (j.val : ℤ)) := by
  simp only [targetCount, initialFlag, offset, min_eq_left (show (s.val : ℤ) ≤ 1650 by omega)]
  rw [show 3000 - (s.val : ℤ) - ((j.val : ℤ) - 1650) - 1 -
    (-((j.val : ℤ) - 1650)) + s.val = (2999 : ℤ) by ring]
  norm_num only [Int.reduceLT, ite_false, Int.reduceDiv]
  rw [min_eq_left (show (s.val : ℤ) ≤ 749 by omega)]
  have hz (u : ℤ) : cumulative ((s.val : ℤ) - ((s.val : ℤ) + 1)) u = 0 := by
    simp [cumulative, show (s.val : ℤ) - ((s.val : ℤ) + 1) = -1 by ring]
  simp only [hz, sub_zero, add_zero]
  congr 1 <;> congr 1 <;> ring
private theorem sum_reverse_truncate (d a n : ℕ) (ha : a < n) :
    (∑ j ∈ Finset.range n, cumulative (d : ℤ) ((a : ℤ) - (j : ℤ))) =
      ∑ j ∈ Finset.range (a + 1), cumulative (d : ℤ) j := by
  calc
    _ = ∑ j ∈ Finset.range (a + 1), cumulative (d : ℤ) ((a : ℤ) - (j : ℤ)) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hja
      have hlt : (a : ℤ) - (j : ℤ) < 0 := by rw [Finset.mem_range] at hja; omega
      simp [cumulative, hlt]
    _ = _ := by
      conv_rhs => rw [← Finset.sum_range_reflect (fun j => cumulative (d : ℤ) (j : ℤ)) (a+1)]
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      have hja := Finset.mem_range.mp hj
      rw [show a + 1 - 1 - j = a - j by omega, Nat.cast_sub (by omega)]
private theorem sum_target_low (s : Fin 4013) (hs : s.val < 551) :
    (∑ j : Fin 4650, targetCount (initialFlag (s,j))) =
      ((3000 - s.val : ℕ) : ℤ) * cumulative (s.val : ℤ) (3 * s.val) := by
  simp_rw [targetCount_low s _ hs]
  rw [Finset.sum_sub_distrib,
    Fin.sum_univ_eq_sum_range (fun j : ℕ => cumulative (s.val : ℤ) (4649 - (s.val : ℤ) - j)),
    Fin.sum_univ_eq_sum_range (fun j : ℕ => cumulative (s.val : ℤ) (1649 - (j : ℤ)))]
  rw [show (4649 : ℤ) - (s.val : ℤ) = ((4649 - s.val : ℕ) : ℤ) by omega]
  rw [sum_reverse_truncate _ _ _ (by omega)]
  have hr := sum_reverse_truncate s.val 1649 4650 (by decide)
  norm_num only [Nat.cast_ofNat] at hr
  rw [hr]
  rw [show 4649 - s.val + 1 = 1650 + (3000 - s.val) by omega, Finset.sum_range_add]
  rw [add_sub_cancel_left]
  have heq (j : ℕ) : cumulative (s.val : ℤ) ((1650 + j : ℕ) : ℤ) =
      cumulative (s.val : ℤ) (3 * s.val) := by
    rw [cumulative_eq_raw, cumulative_eq_raw, min_self, min_eq_right (by omega)]
  simp_rw [heq]
  simp
private theorem bound_grade_low (s : Fin 4013) (hs : s.val < 551) :
    (∑ j : Fin 4650, baseline (s,j)) ≤ (3000 - s.val) *
      (cumulative (s.val : ℤ) (3 * s.val)).toNat := by
  have hn (j : Fin 4650) : 0 ≤ targetCount (initialFlag (s,j)) := by
    rw [targetCount_low s j hs]
    exact sub_nonneg.mpr (cumulative_mono _ (by omega))
  have hc : 0 ≤ cumulative (s.val : ℤ) (3 * s.val) := by
    apply le_trans _ (cumulative_mono (s.val) (show -1 ≤ 3 * (s.val : ℤ) by omega))
    simp [cumulative]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4650)))
    (fun j _ => baseline_le_target (s,j))
  refine h.trans ?_
  exact_mod_cast (show ((∑ j : Fin 4650, (targetCount (initialFlag (s,j))).toNat : ℕ) : ℤ) ≤
    (((3000 - s.val) * (cumulative (s.val : ℤ) (3 * s.val)).toNat : ℕ) : ℤ) by
      rw [Nat.cast_sum, Nat.cast_mul]
      simp_rw [Int.toNat_of_nonneg (hn _)]
      rw [Int.toNat_of_nonneg hc, sum_target_low s hs])
private def gradeTotal (s : ℕ) : ℕ :=
  (3000 - s) * (cumulative (s : ℤ) (3 * s)).toNat
private def lowTotal : ℕ → ℕ
  | 0 => 0
  | n + 1 => lowTotal n + gradeTotal n
private theorem lowTotal_eq (n : ℕ) : lowTotal n = ∑ j ∈ Finset.range n, gradeTotal j := by
  induction n with
  | zero => simp [lowTotal]
  | succ n ih => rw [lowTotal, Finset.sum_range_succ, ih]
private def auxLowChunk (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | count + 1 => auxLowChunk start count + gradeTotal (start + count)
private theorem auxLowChunk_eq (start count : ℕ) :
    lowTotal (start + count) = lowTotal start + auxLowChunk start count := by
  induction count with
  | zero => simp [auxLowChunk]
  | succ count ih => rw [Nat.add_succ, lowTotal, auxLowChunk, ih, Nat.add_assoc]
private theorem auxLowChunk_extend {start count initial delta : ℕ}
    (hi : lowTotal start = initial) (hd : auxLowChunk start count = delta) :
    lowTotal (start + count) = initial + delta :=
  (auxLowChunk_eq start count).trans (congrArg₂ Nat.add hi hd)
private theorem auxLow_total_0 : lowTotal 0 = 0 := rfl
private theorem auxLow_total_16 : lowTotal 16 = 11581488 :=
  auxLowChunk_extend (count := 16) (delta := 11581488) auxLow_total_0 (by decide +kernel)
private theorem auxLow_total_32 : lowTotal 32 = 155781472 :=
  auxLowChunk_extend (count := 16) (delta := 144199984) auxLow_total_16 (by decide +kernel)
private theorem auxLow_total_48 : lowTotal 48 = 740303760 :=
  auxLowChunk_extend (count := 16) (delta := 584522288) auxLow_total_32 (by decide +kernel)
private theorem auxLow_total_64 : lowTotal 64 = 2260809408 :=
  auxLowChunk_extend (count := 16) (delta := 1520505648) auxLow_total_48 (by decide +kernel)
private theorem auxLow_total_80 : lowTotal 80 = 5396722416 :=
  auxLowChunk_extend (count := 16) (delta := 3135913008) auxLow_total_64 (by decide +kernel)
private theorem auxLow_total_96 : lowTotal 96 = 11007035424 :=
  auxLowChunk_extend (count := 16) (delta := 5610313008) auxLow_total_80 (by decide +kernel)
private theorem auxLow_total_112 : lowTotal 112 = 20126115408 :=
  auxLowChunk_extend (count := 16) (delta := 9119079984) auxLow_total_96 (by decide +kernel)
private theorem auxLow_total_128 : lowTotal 128 = 33959509376 :=
  auxLowChunk_extend (count := 16) (delta := 13833393968) auxLow_total_112 (by decide +kernel)
private theorem auxLow_total_144 : lowTotal 144 = 53879750064 :=
  auxLowChunk_extend (count := 16) (delta := 19920240688) auxLow_total_128 (by decide +kernel)
private theorem auxLow_total_160 : lowTotal 160 = 81422161632 :=
  auxLowChunk_extend (count := 16) (delta := 27542411568) auxLow_total_144 (by decide +kernel)
private theorem auxLow_total_176 : lowTotal 176 = 118280665360 :=
  auxLowChunk_extend (count := 16) (delta := 36858503728) auxLow_total_160 (by decide +kernel)
private theorem auxLow_total_192 : lowTotal 192 = 166303585344 :=
  auxLowChunk_extend (count := 16) (delta := 48022919984) auxLow_total_176 (by decide +kernel)
private theorem auxLow_total_208 : lowTotal 208 = 227489454192 :=
  auxLowChunk_extend (count := 16) (delta := 61185868848) auxLow_total_192 (by decide +kernel)
private theorem auxLow_total_224 : lowTotal 224 = 303982818720 :=
  auxLowChunk_extend (count := 16) (delta := 76493364528) auxLow_total_208 (by decide +kernel)
private theorem auxLow_total_240 : lowTotal 240 = 398070045648 :=
  auxLowChunk_extend (count := 16) (delta := 94087226928) auxLow_total_224 (by decide +kernel)
private theorem auxLow_total_256 : lowTotal 256 = 512175127296 :=
  auxLowChunk_extend (count := 16) (delta := 114105081648) auxLow_total_240 (by decide +kernel)
private theorem auxLow_total_272 : lowTotal 272 = 648855487280 :=
  auxLowChunk_extend (count := 16) (delta := 136680359984) auxLow_total_256 (by decide +kernel)
private theorem auxLow_total_288 : lowTotal 288 = 810797786208 :=
  auxLowChunk_extend (count := 16) (delta := 161942298928) auxLow_total_272 (by decide +kernel)
private theorem auxLow_total_304 : lowTotal 304 = 1000813727376 :=
  auxLowChunk_extend (count := 16) (delta := 190015941168) auxLow_total_288 (by decide +kernel)
private theorem auxLow_total_320 : lowTotal 320 = 1221835862464 :=
  auxLowChunk_extend (count := 16) (delta := 221022135088) auxLow_total_304 (by decide +kernel)
private theorem auxLow_total_336 : lowTotal 336 = 1476913397232 :=
  auxLowChunk_extend (count := 16) (delta := 255077534768) auxLow_total_320 (by decide +kernel)
private theorem auxLow_total_352 : lowTotal 352 = 1769207997216 :=
  auxLowChunk_extend (count := 16) (delta := 292294599984) auxLow_total_336 (by decide +kernel)
private theorem auxLow_total_368 : lowTotal 368 = 2101989593424 :=
  auxLowChunk_extend (count := 16) (delta := 332781596208) auxLow_total_352 (by decide +kernel)
private theorem auxLow_total_384 : lowTotal 384 = 2478632188032 :=
  auxLowChunk_extend (count := 16) (delta := 376642594608) auxLow_total_368 (by decide +kernel)
private theorem auxLow_total_400 : lowTotal 400 = 2902609660080 :=
  auxLowChunk_extend (count := 16) (delta := 423977472048) auxLow_total_384 (by decide +kernel)
private theorem auxLow_total_416 : lowTotal 416 = 3377491571168 :=
  auxLowChunk_extend (count := 16) (delta := 474881911088) auxLow_total_400 (by decide +kernel)
private theorem auxLow_total_432 : lowTotal 432 = 3906938971152 :=
  auxLowChunk_extend (count := 16) (delta := 529447399984) auxLow_total_416 (by decide +kernel)
private theorem auxLow_total_448 : lowTotal 448 = 4494700203840 :=
  auxLowChunk_extend (count := 16) (delta := 587761232688) auxLow_total_432 (by decide +kernel)
private theorem auxLow_total_464 : lowTotal 464 = 5144606712688 :=
  auxLowChunk_extend (count := 16) (delta := 649906508848) auxLow_total_448 (by decide +kernel)
private theorem auxLow_total_480 : lowTotal 480 = 5860568846496 :=
  auxLowChunk_extend (count := 16) (delta := 715962133808) auxLow_total_464 (by decide +kernel)
private theorem auxLow_total_496 : lowTotal 496 = 6646571665104 :=
  auxLowChunk_extend (count := 16) (delta := 786002818608) auxLow_total_480 (by decide +kernel)
private theorem auxLow_total_512 : lowTotal 512 = 7506670745088 :=
  auxLowChunk_extend (count := 16) (delta := 860099079984) auxLow_total_496 (by decide +kernel)
private theorem auxLow_total_528 : lowTotal 528 = 8444987985456 :=
  auxLowChunk_extend (count := 16) (delta := 938317240368) auxLow_total_512 (by decide +kernel)
private theorem auxLow_total_544 : lowTotal 544 = 9465707413344 :=
  auxLowChunk_extend (count := 16) (delta := 1020719427888) auxLow_total_528 (by decide +kernel)
private theorem lowTotal_check : lowTotal 551 = 9939265602560 :=
  auxLowChunk_extend (count := 7) (delta := 473558189216) auxLow_total_544 (by decide +kernel)
private theorem sum_cutoff (f : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    (∑ j ∈ Finset.range n, if j < m then f j else 0) = ∑ j ∈ Finset.range m, f j := by
  calc
    _ = ∑ j ∈ Finset.range m, if j < m then f j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono h)
      intro j _ hj
      rw [Finset.mem_range] at hj
      rw [ite_eq_right hj]
    _ = _ := Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_range.mp hj)
theorem baseline_low : baselineSum 0 551 ≤ 9939265602560 := by
  unfold baselineSum baselineSumOn
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [zero_le, true_and]
  calc
    _ ≤ ∑ s : Fin 4013, if s.val < 551 then gradeTotal s else 0 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : s.val < 551
      · simpa only [ite_eq_left hs, gradeTotal] using bound_grade_low s hs
      · simp [hs]
    _ = ∑ j ∈ Finset.range 551, gradeTotal j := by
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < 551 then gradeTotal j else 0)]
      exact sum_cutoff gradeTotal (by decide)
    _ = _ := (lowTotal_eq _).symm.trans lowTotal_check
end K1_13_2_3
end
section
namespace K1_13_2_3
open K1_13_2
open scoped BigOperators
def c1 : Prop := baselineSum 551 1650 ≤ 196232494523570
def c2 : Prop := baselineSum 1650 2510 ≤ 101832665783054
def c3 : Prop := baselineSum 2510 4013 ≤ 36565173831277
def c4 : Prop := ∃ p : BlockIndex → Powers, 9573892230 ≤ savingsSum w1 p
def c5 : Prop := ∃ p : BlockIndex → Powers, 159735926601 ≤ savingsSum w2 p
def c6 : Prop := ∃ p : BlockIndex → Powers, 100540921280 ≤ savingsSum w3 p
def c7 : Prop := ∃ p : BlockIndex → Powers, 174062508216 ≤ savingsSum w4 p
private theorem bound_le_baseline (i : BlockIndex) (p : Fin 11 → ℕ) :
    blockBound i p ≤ baseline i := by
  have hz (F : Flag) : residualFlag F (fun _ => 0) = F := by
    cases F
    simp [residualFlag]
  unfold baseline blockBound
  simp only [hz, max_self]
  split
  · rfl
  · apply Int.toNat_le_toNat
    apply min_le_min_left
    apply sub_le_sub_left
    exact max_le_max_left _ (le_max_left _ _)
private theorem sum_four_le {α : Type*} (S : Finset α)
    (a b c d f : α → ℕ) (h : ∀ i ∈ S, a i + b i + c i + d i ≤ f i) :
    (∑ i ∈ S, a i) + (∑ i ∈ S, b i) + (∑ i ∈ S, c i) + (∑ i ∈ S, d i) ≤
      ∑ i ∈ S, f i := by
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum h
private theorem sum_four_eq {α : Type*} (S : Finset α)
    (a b c d f : α → ℕ) (h : ∀ i ∈ S, f i = a i + b i + c i + d i) :
    (∑ i ∈ S, f i) = (∑ i ∈ S, a i) + (∑ i ∈ S, b i) + (∑ i ∈ S, c i) + (∑ i ∈ S, d i) := by
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl h
private theorem sum_add_pointwise_eq {α : Type*} (S : Finset α)
    (f g t : α → ℕ) (h : ∀ i ∈ S, f i + g i = t i) :
    (∑ i ∈ S, f i) + (∑ i ∈ S, g i) = ∑ i ∈ S, t i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl h
private theorem baseline_parts_on (S : Finset BlockIndex) :
    (∑ i ∈ S, baseline i) = baselineSumOn S 0 551 + baselineSumOn S 551 1650 +
      baselineSumOn S 1650 2510 + baselineSumOn S 2510 4013 := by
  unfold baselineSumOn
  exact sum_four_eq S
    (fun i => if 0 ≤ i.1.val ∧ i.1.val < 551 then baseline i else 0)
    (fun i => if 551 ≤ i.1.val ∧ i.1.val < 1650 then baseline i else 0)
    (fun i => if 1650 ≤ i.1.val ∧ i.1.val < 2510 then baseline i else 0)
    (fun i => if 2510 ≤ i.1.val ∧ i.1.val < 4013 then baseline i else 0)
    baseline (fun i _ => by
      have h := i.1.isLt
      by_cases hs₁ : i.1.val < 551
      · have hn : ¬ 551 ≤ i.1.val := by omega
        have hn' : ¬ 1650 ≤ i.1.val := by omega
        have hn'' : ¬ 2510 ≤ i.1.val := by omega
        simp [hs₁, hn, hn', hn'']
      · have ha : 551 ≤ i.1.val := by omega
        by_cases hs₂ : i.1.val < 1650
        · have hn : ¬ 1650 ≤ i.1.val := by omega
          have hn' : ¬ 2510 ≤ i.1.val := by omega
          simp [hs₁, ha, hs₂, hn, hn']
        · have hb : 1650 ≤ i.1.val := by omega
          by_cases hs₃ : i.1.val < 2510
          · have hn : ¬ 2510 ≤ i.1.val := by omega
            simp [hs₁, hs₂, hb, hs₃, hn]
          · have hc : 2510 ≤ i.1.val := by omega
            simp [hs₁, hs₂, hs₃, hc, h])
private theorem baseline_budget_on (S : Finset BlockIndex)
    (h₀ : baselineSumOn S 0 551 ≤ 9939265602560)
    (h₁ : baselineSumOn S 551 1650 ≤ 196232494523570)
    (h₂ : baselineSumOn S 1650 2510 ≤ 101832665783054)
    (h₃ : baselineSumOn S 2510 4013 ≤ 36565173831277) :
    (∑ i ∈ S, baseline i) ≤ 344569599740461 := calc
  _ = _ := baseline_parts_on S
  _ ≤ (9939265602560 + 196232494523570 + 101832665783054 + 36565173831277) :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h₀ h₁) h₂) h₃
  _ ≤ _ := by decide
private def combine (p₁ p₂ p₃ p₄ : BlockIndex → Powers) (i : BlockIndex) : Powers :=
  if i.1.val < 2008 then p₁ i else if i.1.val < 3012 then p₂ i
  else if i.1.val < 3514 then p₃ i else p₄ i
private theorem savings_parts (p₁ p₂ p₃ p₄ : BlockIndex → Powers) :
    savingsSum w1 p₁ + savingsSum w2 p₂ + savingsSum w3 p₃ + savingsSum w4 p₄ ≤
      ∑ i : BlockIndex, savings i (combine p₁ p₂ p₃ p₄ i) := by
  exact sum_four_le Finset.univ
    (fun i => if w1.Contains i then savings i (p₁ i) else 0)
    (fun i => if w2.Contains i then savings i (p₂ i) else 0)
    (fun i => if w3.Contains i then savings i (p₃ i) else 0)
    (fun i => if w4.Contains i then savings i (p₄ i) else 0)
    (fun i => savings i (combine p₁ p₂ p₃ p₄ i)) (fun i _ => by
      by_cases hs₁ : i.1.val < 2008
      · have hn₂ : ¬ w2.Contains i := by simp [w2, Window.Contains]; omega
        have hn₃ : ¬ w3.Contains i := by simp [w3, Window.Contains]; omega
        have hn₄ : ¬ w4.Contains i := by simp [w4, Window.Contains]; omega
        simp only [combine, hs₁, ite_true, hn₂, hn₃, hn₄, ite_false, add_zero]
        split <;> simp
      · have hn₁ : ¬ w1.Contains i := by simp [w1, Window.Contains, hs₁]
        by_cases hs₂ : i.1.val < 3012
        · have hn₃ : ¬ w3.Contains i := by simp [w3, Window.Contains]; omega
          have hn₄ : ¬ w4.Contains i := by simp [w4, Window.Contains]; omega
          simp only [combine, hs₁, hs₂, ite_false, ite_true, hn₁, hn₃, hn₄, zero_add, add_zero]
          split <;> simp
        · have hn₂ : ¬ w2.Contains i := by simp [w2, Window.Contains, hs₂]
          by_cases hs₃ : i.1.val < 3514
          · have hn₄ : ¬ w4.Contains i := by simp [w4, Window.Contains]; omega
            simp only [combine, hs₁, hs₂, hs₃, ite_false, ite_true, hn₁, hn₂, hn₄, zero_add, add_zero]
            split <;> simp
          · have hn₃ : ¬ w3.Contains i := by simp [w3, Window.Contains, hs₃]
            simp only [combine, hs₁, hs₂, hs₃, ite_false, hn₁, hn₂, hn₃, zero_add]
            split <;> simp)
private theorem finish_budget (a b c : ℕ) (h : a + b = c)
    (hc : c ≤ 344569599740461) (hb : 443913248327 ≤ b) :
    a ≤ 344125686492134 := by omega
set_option maxHeartbeats 200000 in
theorem of_children (h₂ : c1) (h₃ : c2) (h₄ : c3)
    (h₅ : c4) (h₆ : c5) (h₇ : c6) (h₈ : c7) : K1_13_2.c3 := by
  unfold c1 at h₂
  unfold c2 at h₃
  unfold c3 at h₄
  obtain ⟨p₁, hp₁⟩ := h₅
  obtain ⟨p₂, hp₂⟩ := h₆
  obtain ⟨p₃, hp₃⟩ := h₇
  obtain ⟨p₄, hp₄⟩ := h₈
  let p := combine p₁ p₂ p₃ p₄
  refine ⟨fun i => (p i).expand, ?_⟩
  have hstatic := baseline_budget_on (Finset.univ : Finset BlockIndex) baseline_low h₂ h₃ h₄
  have hsave : 443913248327 ≤ ∑ i : BlockIndex, savings i (p i) := calc
    _ ≤ (9573892230 + 159735926601 + 100540921280 + 174062508216) := by decide
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp₁ hp₂) hp₃) hp₄
    _ ≤ _ := savings_parts p₁ p₂ p₃ p₄
  have hsum : (∑ i : BlockIndex, blockBound i (p i).expand) +
      (∑ i : BlockIndex, savings i (p i)) = ∑ i : BlockIndex, baseline i :=
    sum_add_pointwise_eq Finset.univ (fun i => blockBound i (p i).expand)
      (fun i => savings i (p i)) baseline
      (fun i _ => Nat.add_sub_of_le (bound_le_baseline i (p i).expand))
  exact finish_budget _ _ _ hsum hstatic hsave
end K1_13_2_3
end

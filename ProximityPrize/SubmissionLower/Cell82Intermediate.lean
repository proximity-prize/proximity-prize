import ProximityPrize.SubmissionLower.Fast014

set_option Elab.async false

namespace Cell82Intermediate

open ProximityPrize.Benchmark ToyProblem CoreDefinitions ProximityGap
open scoped NNReal

inductive Target
  | s51 | s52 | s53 | s54

structure RadiusData where
  score : ℕ
  errors : ℕ
  boundaryNumerator : ℕ
  boundaryDenominator : ℕ
  numerator : ℕ
  denominator : ℕ

def data : Target → RadiusData
  | .s51 => ⟨6951,82229,41115,131072,2893210916864619832,9223372036854662547⟩
  | .s52 => ⟨6952,82239,1285,4096,2893562760585543664,9223372036854775757⟩
  | .s53 => ⟨6953,82248,82249,262144,2893879419934332965,9223372036854743289⟩
  | .s54 => ⟨6954,82258,82259,262144,2894231263655162954,9223372036854557403⟩

abbrev agreement (t : Target) : ℕ := 262144 - (data t).errors
abbrev maxDenominator : ℕ := 9223372036854775807

noncomputable def radius (t : Target) : ℝ≥0 :=
  claimedRadius (data t).numerator (data t).denominator

theorem components_allowed (t : Target) :
    0 < (data t).numerator ∧ (data t).numerator < (data t).denominator ∧
      (data t).denominator ≤ maxDenominator := by cases t <;> decide

theorem radius_interval (t : Target) :
    (data t).errors / (262144 : ℝ≥0) ≤ radius t ∧
      radius t < ((data t).errors + 1 : ℕ) / (262144 : ℝ≥0) := by
  cases t <;> constructor <;> push_cast
  all_goals first | rw [← NNReal.coe_le_coe] | rw [← NNReal.coe_lt_coe]
  all_goals norm_num [radius, data, claimedRadius]

theorem error_count (t : Target) :
    ⌊radius t * (262144 : ℝ≥0)⌋₊ = (data t).errors := by
  cases t <;> norm_num [radius, data, claimedRadius]

theorem radius_admissible (t : Target) :
    radius t ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  cases t <;> norm_num [radius, data, claimedRadius, IRSProfile.minRelativeDistance]

/-- The largest allowed fraction strictly below the next error cutoff. -/
theorem maximal_in_cell (t : Target) (a b : ℕ) (size : b ≤ maxDenominator)
    (below : a * (data t).boundaryDenominator < (data t).boundaryNumerator * b) :
    a * (data t).denominator ≤ (data t).numerator * b := by
  let d := data t
  change a * d.boundaryDenominator < d.boundaryNumerator * b at below
  change a * d.denominator ≤ d.numerator * b
  have hdet : d.boundaryNumerator * d.denominator =
      d.numerator * d.boundaryDenominator + 1 := by cases t <;> decide
  have hbig : maxDenominator < d.denominator + d.boundaryDenominator := by cases t <;> decide
  by_contra! above
  have habove : (d.numerator : ℤ) * b + 1 ≤ (a : ℤ) * d.denominator := by exact_mod_cast above
  have hbelow : (a : ℤ) * d.boundaryDenominator + 1 ≤ (d.boundaryNumerator : ℤ) * b := by
    exact_mod_cast below
  have hd' : (d.boundaryNumerator : ℤ) * d.denominator -
      (d.numerator : ℤ) * d.boundaryDenominator = 1 := by
    have hh : (d.boundaryNumerator : ℤ) * d.denominator =
        (d.numerator : ℤ) * d.boundaryDenominator + 1 := by exact_mod_cast hdet
    rw [hh]
    ring
  have hp : (1 : ℤ) ≤ (a : ℤ) * d.denominator - (d.numerator : ℤ) * b := by linarith
  have hq : (1 : ℤ) ≤ (d.boundaryNumerator : ℤ) * b - (a : ℤ) * d.boundaryDenominator := by linarith
  have hsum := add_le_add (mul_le_mul_of_nonneg_right hp (Int.natCast_nonneg d.boundaryDenominator))
    (mul_le_mul_of_nonneg_right hq (Int.natCast_nonneg d.denominator))
  have hlin : ((a : ℤ) * d.denominator - (d.numerator : ℤ) * b) * d.boundaryDenominator +
      ((d.boundaryNumerator : ℤ) * b - (a : ℤ) * d.boundaryDenominator) * d.denominator = b := by
    calc
      _ = ((d.boundaryNumerator : ℤ) * d.denominator -
        (d.numerator : ℤ) * d.boundaryDenominator) * b := by ring
      _ = b := by rw [hd', one_mul]
  rw [hlin, one_mul, one_mul] at hsum
  have hsum' : d.boundaryDenominator + d.denominator ≤ b := by exact_mod_cast hsum
  rw [Nat.add_comm] at hsum'
  exact (not_le_of_gt hbig) (hsum'.trans size)

theorem boundary_is_next_error (t : Target) :
    (data t).boundaryNumerator * 262144 =
      ((data t).errors+1) * (data t).boundaryDenominator := by cases t <;> decide

private theorem score_ratio_iff (a b score : ℕ) (hb : 0 < b) (hab : a ≤ b) :
    (1 - claimedRadius a b) ^ IRSProfile.repetitions ≤ claimedError score ↔
      (b-a)^12800 * 2^score ≤ b^12800 := by
  have hab' : (a : ℝ≥0) ≤ b := by exact_mod_cast hab
  have hb' : (0 : ℝ≥0) < b := by exact_mod_cast hb
  have hr : claimedRadius a b ≤ 1 := by
    unfold claimedRadius
    exact (div_le_one hb').mpr hab'
  have hcomp : 1 - claimedRadius a b = ((b-a : ℕ) : ℝ≥0) / b := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    simp only [claimedRadius, NNReal.coe_div, NNReal.coe_natCast,
      NNReal.coe_one, Nat.cast_sub hab]
    field_simp
  change (1 - claimedRadius a b) ^ 128 ≤ claimedError score ↔ _
  rw [← pow_le_pow_iff_left₀ (by positivity : 0 ≤ (1 - claimedRadius a b)^128)
    (by positivity : 0 ≤ claimedError score) (by decide : (100 : ℕ) ≠ 0)]
  rw [← pow_mul, Sol1.C42.claimedError_pow_100, hcomp]
  change (((b-a : ℕ) : ℝ≥0) / b)^12800 ≤ 1/(2 : ℝ≥0)^score ↔ _
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast Iff.rfl

-- The small dyadic denominator certifies the score with smaller kernel integers.
private abbrev dyadicNumerator (t : Target) := ((data t).errors + 1) * 4096 - 1
private abbrev dyadicDenominator : ℕ := 1073741824

theorem radius_score (t : Target) :
    (1 - radius t) ^ IRSProfile.repetitions ≤ claimedError (data t).score := by
  have hz : claimedRadius (dyadicNumerator t) dyadicDenominator ≤ radius t := by
    rw [← NNReal.coe_le_coe]
    cases t <;> norm_num [radius, data, dyadicNumerator, dyadicDenominator, claimedRadius]
  have hp : dyadicNumerator t ≤ dyadicDenominator := by cases t <;> decide
  have hc := (score_ratio_iff _ _ (data t).score (by decide) hp).mpr
    (show (dyadicDenominator-dyadicNumerator t)^12800 * 2^(data t).score ≤ dyadicDenominator^12800 by
      cases t <;> decide +kernel)
  exact (pow_le_pow_left' (tsub_le_tsub_left hz _) _).trans hc

/-- Even the upper endpoint of the preceding cell has insufficient score. -/
theorem earlier_radius_insufficient (t : Target) {r : ℝ≥0}
    (hr : r ≤ claimedRadius (data t).errors 262144) :
    ¬ (1-r)^IRSProfile.repetitions ≤ claimedError (data t).score := by
  intro h
  have hp : (data t).errors ≤ 262144 := by cases t <;> decide
  have hprev := (pow_le_pow_left' (tsub_le_tsub_left hr _) _).trans h
  have hc := (score_ratio_iff (data t).errors 262144 (data t).score (by decide) hp).mp hprev
  exact (show ¬ (262144-(data t).errors)^12800 * 2^(data t).score ≤ 262144^12800 by
    cases t <;> decide +kernel) hc

#print axioms maximal_in_cell
#print axioms radius_score
#print axioms earlier_radius_insufficient
end Cell82Intermediate

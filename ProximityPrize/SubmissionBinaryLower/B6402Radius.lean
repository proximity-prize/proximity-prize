import ProximityPrize.Benchmark.BinaryTargetLower
import Mathlib.Tactic

namespace ProximityPrize.SubmissionBinaryLower.B6402Radius
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open scoped NNReal
set_option maxRecDepth 65536
set_option exponentiation.threshold 14000

abbrev numerator : ℕ := 78643482
abbrev denominator : ℕ := 268435456
abbrev agreement : ℕ := 1482750
noncomputable abbrev radius := claimedRadius numerator denominator

theorem admissible : radius ∈ Set.Ioo (0 : ℝ≥0) BinaryIRSProfile.minRelativeDistance := by
  norm_num [radius,claimedRadius,BinaryIRSProfile.minRelativeDistance]

theorem agreement_ge {n : ℕ} (h : (Fintype.card BinaryIRSProfile.Index : ℝ) * (1 - (radius : ℝ)) ≤ n) :
    agreement ≤ n := by
  rw [BinaryIRSProfile.card_index] at h
  have h' : (1482749 : ℝ) < (2097152 : ℝ) * (1 - (radius : ℝ)) := by
    norm_num [radius,claimedRadius]
  exact_mod_cast h'.trans_le h

private theorem integer_score :
    (189791974 : ℕ)^12800 * 2^6402 ≤ (268435456 : ℕ)^12800 := by decide

private theorem score_from_nat {p q k : ℕ} (hq : 0 < q)
    (hbound : p^12800 * 2^k ≤ q^12800) :
    ((p : ℝ≥0)/q)^128 ≤ (2 : ℝ≥0)^(-((k : ℝ)/100)) := by
  have hv : (0 : ℝ≥0) < q := by exact_mod_cast hq
  refine le_of_pow_le_pow_left₀ (n := 100) (by decide) zero_le ?_
  rw [← pow_mul, ← NNReal.rpow_natCast ((2 : ℝ≥0)^(-((k : ℝ)/100))) 100,
      ← NNReal.rpow_mul, show -((k : ℝ)/100)*(↑(100 : ℕ) : ℝ) = -(k : ℝ) by push_cast; ring,
      NNReal.rpow_neg (2 : ℝ≥0) (k : ℝ), NNReal.rpow_natCast, inv_eq_one_div, div_pow,
      div_le_div_iff₀ (pow_pos hv _) (pow_pos (by norm_num) _), one_mul]
  exact_mod_cast hbound

theorem score : (1-radius)^BinaryIRSProfile.repetitions ≤ claimedError 6402 := by
  have hsmall : radius ≤ 1 := by
    change (78643482 : ℝ≥0) / 268435456 ≤ 1
    rw [div_le_iff₀ (by positivity)]
    norm_num
  have hr : 1-radius = (189791974 : ℝ≥0)/268435456 := by
    apply NNReal.eq
    rw [NNReal.coe_sub hsmall]
    norm_num [radius,claimedRadius]
  rw [hr]
  exact score_from_nat (p := 189791974) (q := 268435456) (k := 6402) (by decide) integer_score

#print axioms score
end ProximityPrize.SubmissionBinaryLower.B6402Radius

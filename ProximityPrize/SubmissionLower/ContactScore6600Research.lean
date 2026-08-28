import ProximityPrize.Benchmark.TargetLower

/-!
# Exact radius and score arithmetic for the 66.00 candidate

The radius is the top grid point in the `78777`-error cell,
`(4 * 78777 + 3) / 2^20`.  Since the claimed score is an integer number of
bits, the final comparison is directly against `2^-66` and needs no
fractional-power enclosure.
-/

namespace ProximityPrize.SubmissionLower.ContactScore6600Research

open ProximityPrize.Benchmark
open scoped NNReal

noncomputable section

def radius6600 : ℝ≥0 := claimedRadius 315111 1048576
def errors6600 : ℕ := 78777
def score6600 : ℕ := 6600

theorem radius_numerator_exact : 315111 = 4 * errors6600 + 3 := by
  norm_num [errors6600]

theorem radius6600_floor :
    ⌊(radius6600 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6600 := by
  norm_num [radius6600, claimedRadius, errors6600, IRSProfile.Index]

theorem radius6600_cell_cross :
    315111 * Fintype.card IRSProfile.Index <
      (errors6600 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6600]

theorem radius6600_gap :
    131071 < Fintype.card IRSProfile.Index - errors6600 := by
  norm_num [IRSProfile.Index, errors6600]

theorem radius6600_admissible :
    radius6600 ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius6600, claimedRadius, IRSProfile.minRelativeDistance]

/-- Exact rational 128th-power comparison at the claimed radius. -/
theorem radius6600_power_rational_bound :
    (1 - radius6600) ^ IRSProfile.repetitions ≤
      (1 : ℝ≥0) / 2 ^ (66 : ℕ) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6600, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem claimedError_6600_exact :
    claimedError score6600 = (1 : ℝ≥0) / 2 ^ (66 : ℕ) := by
  unfold claimedError score6600
  rw [show -((((6600 : ℕ) : ℝ) / 100)) = -((66 : ℕ) : ℝ) by norm_num]
  simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

theorem radius6600_score :
    (1 - radius6600) ^ IRSProfile.repetitions ≤ claimedError score6600 := by
  rw [claimedError_6600_exact]
  exact radius6600_power_rational_bound

end

end ProximityPrize.SubmissionLower.ContactScore6600Research

#print axioms ProximityPrize.SubmissionLower.ContactScore6600Research.radius6600_floor
#print axioms ProximityPrize.SubmissionLower.ContactScore6600Research.radius6600_admissible
#print axioms ProximityPrize.SubmissionLower.ContactScore6600Research.radius6600_power_rational_bound
#print axioms ProximityPrize.SubmissionLower.ContactScore6600Research.radius6600_score

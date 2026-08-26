import ProximityPrize.SubmissionLower.BCHKSBridge

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap
open scoped NNReal

/-- The first quarter-grid radius above the 64-bit score threshold.  Its
absolute Hamming ball still has radius `76780`. -/
noncomputable def bchksRadius6400 : ℝ≥0 :=
  (307121 : ℝ≥0) / 1048576

def bchksErrors6400 : ℕ := 76780
def bchksNumerator6400 : ℕ := 100000000000000000
def bchksListBound6400 : ℕ := 42324

/-- Parameters inherited by the universal-resultant alignment route. -/
def bchksMultiplicity6400 : ℕ := 3733
def bchksXCap6400 : ℕ := 692001142
def bchksYCap6400 : ℕ := 5280
def bchksZCap6400 : ℕ := 13141403
def bchksFactorMass6400 : ℕ := 5279
def bchksFactorZMass6400 : ℕ := 13141402
def bchksUniversalExponent6400 : ℕ := 262141
def bchksIncidenceCoefficient6400 : ℕ := 1265711

lemma bchksRadius6400_floor :
    ⌊(bchksRadius6400 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      bchksErrors6400 := by
  norm_num [bchksRadius6400, bchksErrors6400, IRSProfile.Index]

lemma bchksRadius6400_floor_nnreal :
    ⌊bchksRadius6400 * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ =
      bchksErrors6400 := by
  norm_num [bchksRadius6400, bchksErrors6400, IRSProfile.Index]

/-- The universal-resultant numerator and the exact boundary list bound fit
the 128-bit field budget. -/
lemma bchks6400_budget_nat :
    2 ^ (128 : ℕ) * (bchksNumerator6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksNumerator6400, bchksListBound6400]

/-- Exact score arithmetic for the 64.00-bit endpoint. -/
lemma bchksRadius6400_score :
    (1 - bchksRadius6400) ^ IRSProfile.repetitions ≤
      ProximityPrize.Benchmark.claimedError 6400 := by
  unfold ProximityPrize.Benchmark.claimedError
  rw [show -((((6400 : ℕ) : ℝ) / 100)) = -((64 : ℕ) : ℝ) by norm_num,
    NNReal.rpow_neg, NNReal.rpow_natCast]
  rw [← NNReal.coe_le_coe]
  norm_num [bchksRadius6400, IRSProfile.repetitions, div_le_iff₀]

/-- The larger incidence coefficient required by the ten additional errors
still satisfies the fused-floor inequality. -/
lemma bchks6400_incidence_rounding :
    (262144 - 131071) * (2 * (2 * 131071 - 1)) ≤
      bchksIncidenceCoefficient6400 *
        (262144 - bchksErrors6400 - 131071) := by
  norm_num [bchksErrors6400, bchksIncidenceCoefficient6400]

/-- The existing seed ledger has ample room for the slightly larger
incidence coefficient. -/
lemma bchks6400_universal_seed_budget :
    bchksIncidenceCoefficient6400 * (5280 - 1) * (13141403 - 1) +
      (bchksErrors6400 + 1) * (5280 - 1) +
      2 * 13141403 * (5280 - 1) + 13141403 <
        bchksNumerator6400 := by
  norm_num [bchksIncidenceCoefficient6400, bchksErrors6400,
    bchksNumerator6400]

end ProximityPrize.SubmissionLower

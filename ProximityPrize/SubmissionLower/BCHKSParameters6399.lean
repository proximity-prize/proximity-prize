import ProximityPrize.SubmissionLower.BCHKSBridge

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap
open scoped NNReal

/-- Radius for the universal-numerator BCHKS certificate at 63.99 bits. -/
noncomputable def bchksRadius6399 : ℝ≥0 := (307083 : ℝ≥0) / 1048576

def bchksErrors6399 : ℕ := 76770

def bchksNumerator6399 : ℕ := 100000000000000000

def bchksListBound6399 : ℕ := 30000

def bchksMultiplicity6399 : ℕ := 3733
def bchksXCap6399 : ℕ := 692001142
def bchksYCap6399 : ℕ := 5280
def bchksZCap6399 : ℕ := 13141403
def bchksFactorMass6399 : ℕ := 5279
def bchksFactorZMass6399 : ℕ := 13141402
def bchksUniversalExponent6399 : ℕ := 262141
def bchksIncidenceCoefficient6399 : ℕ := 1265478

lemma bchksRadius6399_floor :
    ⌊(bchksRadius6399 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      bchksErrors6399 := by
  norm_num [bchksRadius6399, bchksErrors6399, IRSProfile.Index]

lemma bchksRadius6399_floor_nnreal :
    ⌊bchksRadius6399 * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ =
      bchksErrors6399 := by
  norm_num [bchksRadius6399, bchksErrors6399, IRSProfile.Index]

/-- The universal-resultant numerator and Johnson list contribution fit the
128-bit field budget. -/
lemma bchks6399_budget_nat :
    2 ^ (128 : ℕ) * (bchksNumerator6399 + bchksListBound6399) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksNumerator6399, bchksListBound6399]

/-- Rational lower approximation to `2^(1/100)`. -/
theorem two_rpow_one_hundred_ge :
    (5033 : ℝ≥0) / 5000 ≤ (2 : ℝ≥0) ^ ((1 : ℝ) / 100) := by
  have hroot :
      (5033 : ℝ≥0) / 5000 ≤
        ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
    rw [NNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [div_pow, div_le_iff₀]
  calc
    (5033 : ℝ≥0) / 5000 ≤
        ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((100 : ℝ)⁻¹) := hroot
    _ = (2 : ℝ≥0) ^ ((1 : ℝ) / 100) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]

/-- Standalone score arithmetic for `ProtocolClaim 6399`. -/
lemma bchksRadius6399_score :
    (1 - bchksRadius6399) ^ IRSProfile.repetitions ≤
      ProximityPrize.Benchmark.claimedError 6399 := by
  calc
    (1 - bchksRadius6399) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) * (5033 / 5000) := by
      rw [← NNReal.coe_le_coe]
      norm_num [bchksRadius6399, IRSProfile.repetitions, div_le_iff₀]
    _ ≤ ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) *
          (2 : ℝ≥0) ^ ((1 : ℝ) / 100) := by
      exact mul_le_mul_of_nonneg_left two_rpow_one_hundred_ge (by positivity)
    _ = ProximityPrize.Benchmark.claimedError 6399 := by
      unfold ProximityPrize.Benchmark.claimedError
      rw [show -((((6399 : ℕ) : ℝ) / 100)) =
          -((64 : ℕ) : ℝ) + (1 : ℝ) / 100 by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0),
        NNReal.rpow_neg, NNReal.rpow_natCast]
      norm_num

/-- The exact global seed ledger for the universal numerator/resultant route. -/
lemma bchks6399_universal_seed_budget :
    1265478 * (5280 - 1) * (13141403 - 1) +
      (bchksErrors6399 + 1) * (5280 - 1) +
      2 * 13141403 * (5280 - 1) + 13141403 <
        bchksNumerator6399 := by
  norm_num [bchksErrors6399, bchksNumerator6399]

/-- The fused incidence coefficient is valid at the new agreement radius. -/
lemma bchks6399_incidence_rounding :
    (262144 - 131071) * (2 * (2 * 131071 - 1)) ≤
      1265478 * (262144 - bchksErrors6399 - 131071) := by
  norm_num [bchksErrors6399]

/-- Aggregate ordinary-resultant degree after summing all positive factors. -/
lemma bchks6399_resultant_degree_cap :
    2 * bchksUniversalExponent6399 * bchksFactorMass6399 *
        bchksFactorZMass6399 + bchksFactorMass6399 =
      36371256962843835 := by
  norm_num [bchksUniversalExponent6399, bchksFactorMass6399,
    bchksFactorZMass6399]

/-- Exact fused-floor incidence inequality; no integer ceiling is taken. -/
lemma bchks6399_fused_incidence :
    (262144 - 131071) *
        (2 * bchksUniversalExponent6399 * bchksFactorMass6399 *
          bchksFactorZMass6399 + bchksFactorMass6399) ≤
      (262144 - bchksErrors6399 - 131071) *
        (bchksIncidenceCoefficient6399 * bchksFactorMass6399 *
          bchksFactorZMass6399) := by
  norm_num [bchksUniversalExponent6399, bchksFactorMass6399,
    bchksFactorZMass6399, bchksErrors6399,
    bchksIncidenceCoefficient6399]

lemma bchks6399_gap_pos :
    0 < 262144 - bchksErrors6399 - 131071 := by
  norm_num [bchksErrors6399]

lemma bchks6399_gap_le_nminus :
    262144 - bchksErrors6399 - 131071 ≤ 262144 - 131071 := by
  norm_num [bchksErrors6399]

/-- Once an alignment extractor is supplied, its exact MCA consequence at the
new radius is immediate. -/
theorem base_mca_bchks6399_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6399 bchksNumerator6399) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (bchksRadius6399 : ℝ) ≤
      ENNReal.ofReal
        ((bchksNumerator6399 : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (bchksRadius6399 : ℝ) bchksErrors6399 bchksNumerator6399
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (bchksRadius6399 : ℝ) by positivity)).mp hA
    rw [bchksRadius6399_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [bchksErrors6399] at hcomp ⊢
    omega
  · exact halign

end ProximityPrize.SubmissionLower

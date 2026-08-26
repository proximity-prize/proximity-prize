import ProximityPrize.SubmissionLower.BCHKSBridge

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap
open scoped NNReal

/-- Radius for the universal-numerator BCHKS certificate at 63.99 bits. -/
noncomputable def bchksRadius8207 : ℝ≥0 := (454947 : ℝ≥0) / 1048576

def bchksErrors8207 : ℕ := 113736

def bchksNumerator8207 : ℕ := 274980722241659877

def bchksListBound8207 : ℕ := 200000

def bchksMultiplicity8207 : ℕ := 3733
def bchksXCap8207 : ℕ := 692001142
def bchksYCap8207 : ℕ := 5280
def bchksZCap8207 : ℕ := 13141403
def bchksFactorMass8207 : ℕ := 5279
def bchksFactorZMass8207 : ℕ := 13141402
def bchksUniversalExponent8207 : ℕ := 262141
def bchksIncidenceCoefficient8207 : ℕ := 3963772

lemma bchksRadius8207_floor :
    ⌊(bchksRadius8207 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      bchksErrors8207 := by
  norm_num [bchksRadius8207, bchksErrors8207, IRSProfile.Index]

lemma bchksRadius8207_floor_nnreal :
    ⌊bchksRadius8207 * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ =
      bchksErrors8207 := by
  norm_num [bchksRadius8207, bchksErrors8207, IRSProfile.Index]

/-- The universal-resultant numerator and Johnson list contribution fit the
128-bit field budget. -/
lemma bchks8207_budget_nat :
    2 ^ (128 : ℕ) * (bchksNumerator8207 + bchksListBound8207) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksNumerator8207, bchksListBound8207]

/-- Rational lower approximation to `2^(93/100)`. -/
theorem two_rpow_ninety_three_ge :
    (1900 : ℝ≥0) / 1000 ≤ (2 : ℝ≥0) ^ ((93 : ℝ) / 100) := by
  have hroot :
      (1900 : ℝ≥0) / 1000 ≤
        ((2 : ℝ≥0) ^ (93 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
    rw [NNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [div_pow, div_le_iff₀]
  calc
    (1900 : ℝ≥0) / 1000 ≤
        ((2 : ℝ≥0) ^ (93 : ℕ)) ^ ((100 : ℝ)⁻¹) := hroot
    _ = (2 : ℝ≥0) ^ ((93 : ℝ) / 100) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]

/-- Standalone score arithmetic for `ProtocolClaim 8207`. -/
lemma bchksRadius8207_score :
    (1 - bchksRadius8207) ^ IRSProfile.repetitions ≤
      ProximityPrize.Benchmark.claimedError 8207 := by
  calc
    (1 - bchksRadius8207) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (83 : ℕ)) * (1900 / 1000) := by
      rw [← NNReal.coe_le_coe]
      norm_num [bchksRadius8207, IRSProfile.repetitions, div_le_iff₀]
    _ ≤ ((1 : ℝ≥0) / 2 ^ (83 : ℕ)) *
          (2 : ℝ≥0) ^ ((93 : ℝ) / 100) := by
      exact mul_le_mul_of_nonneg_left two_rpow_ninety_three_ge (by positivity)
    _ = ProximityPrize.Benchmark.claimedError 8207 := by
      unfold ProximityPrize.Benchmark.claimedError
      rw [show -((((8207 : ℕ) : ℝ) / 100)) =
          -((83 : ℕ) : ℝ) + (93 : ℝ) / 100 by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0),
        NNReal.rpow_neg, NNReal.rpow_natCast]
      norm_num

/-- The exact global seed ledger for the universal numerator/resultant route. -/
lemma bchks8207_universal_seed_budget :
    3963772 * (5280 - 1) * (13141403 - 1) +
      (bchksErrors8207 + 1) * (5280 - 1) +
      2 * 13141403 * (5280 - 1) + 13141403 <
        bchksNumerator8207 := by
  norm_num [bchksErrors8207, bchksNumerator8207]

/-- The fused incidence coefficient is valid at the new agreement radius. -/
lemma bchks8207_incidence_rounding :
    (262144 - 131071) * (2 * (2 * 131071 - 1)) ≤
      3963772 * (262144 - bchksErrors8207 - 131071) := by
  norm_num [bchksErrors8207]

/-- Aggregate ordinary-resultant degree after summing all positive factors. -/
lemma bchks8207_resultant_degree_cap :
    2 * bchksUniversalExponent8207 * bchksFactorMass8207 *
        bchksFactorZMass8207 + bchksFactorMass8207 =
      36371256962843835 := by
  norm_num [bchksUniversalExponent8207, bchksFactorMass8207,
    bchksFactorZMass8207]

/-- Exact fused-floor incidence inequality; no integer ceiling is taken. -/
lemma bchks8207_fused_incidence :
    (262144 - 131071) *
        (2 * bchksUniversalExponent8207 * bchksFactorMass8207 *
          bchksFactorZMass8207 + bchksFactorMass8207) ≤
      (262144 - bchksErrors8207 - 131071) *
        (bchksIncidenceCoefficient8207 * bchksFactorMass8207 *
          bchksFactorZMass8207) := by
  norm_num [bchksUniversalExponent8207, bchksFactorMass8207,
    bchksFactorZMass8207, bchksErrors8207,
    bchksIncidenceCoefficient8207]

lemma bchks8207_gap_pos :
    0 < 262144 - bchksErrors8207 - 131071 := by
  norm_num [bchksErrors8207]

lemma bchks8207_gap_le_nminus :
    262144 - bchksErrors8207 - 131071 ≤ 262144 - 131071 := by
  norm_num [bchksErrors8207]

/-- Once an alignment extractor is supplied, its exact MCA consequence at the
new radius is immediate. -/
theorem base_mca_bchks8207_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors8207 bchksNumerator8207) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (bchksRadius8207 : ℝ) ≤
      ENNReal.ofReal
        ((bchksNumerator8207 : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (bchksRadius8207 : ℝ) bchksErrors8207 bchksNumerator8207
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (bchksRadius8207 : ℝ) by positivity)).mp hA
    rw [bchksRadius8207_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [bchksErrors8207] at hcomp ⊢
    omega
  · exact halign

end ProximityPrize.SubmissionLower

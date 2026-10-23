import ProximityPrize.SubmissionBinaryLower.BCHKSBridge

namespace ProximityPrize.SubmissionBinaryLower

open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open CoreDefinitions ProximityGap
open scoped NNReal

noncomputable def bchksRadius : ℝ≥0 := (314491903 : ℝ≥0) / 1073741824

def bchksErrors : ℕ := 614241

def bchksNumerator : ℕ := 2000000000000000000

def bchksListBound : ℕ := 4000000

/-- Slack reserved for bad specializations without changing the sharp multiplicity target. -/
def bchksBadBudget : ℕ := 4000000000000000

lemma bchksRadius_floor :
    ⌊(bchksRadius : ℝ) * (Fintype.card BinaryIRSProfile.Index : ℝ)⌋₊ = bchksErrors := by
  norm_num [bchksRadius, bchksErrors, BinaryIRSProfile.Index]

lemma bchksRadius_floor_nnreal :
    ⌊bchksRadius * (Fintype.card BinaryIRSProfile.Index : ℝ≥0)⌋₊ = bchksErrors := by
  norm_num [bchksRadius, bchksErrors, BinaryIRSProfile.Index]

/-- The MCA numerator and Johnson-list contribution fit the 128-bit field budget. -/
lemma bchks_budget_nat :
    2 ^ (128 : ℕ) * (bchksNumerator + bchksListBound) ≤
      2 ^ (192 : ℕ) := by
  norm_num [bchksNumerator, bchksListBound]

/-- Rational lower approximation to `2^(1/100)`, used by the score certificate. -/
theorem two_rpow_one_hundred_ge :
    (10057 : ℝ≥0) / 10000 ≤ (2 : ℝ≥0) ^ ((1 : ℝ) / 100) := by
  have hroot :
      (10057 : ℝ≥0) / 10000 ≤
        ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
    rw [NNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [div_pow, div_le_iff₀]
  calc
    (10057 : ℝ≥0) / 10000 ≤
        ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((100 : ℝ)⁻¹) := hroot
    _ = (2 : ℝ≥0) ^ ((1 : ℝ) / 100) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]

lemma bchksRadius_score :
    (1 - bchksRadius) ^ BinaryIRSProfile.repetitions ≤
      ProximityPrize.Benchmark.Binary.claimedError 6400 := by
  have hclaim : ProximityPrize.Benchmark.Binary.claimedError 6400 =
      ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) := by
    unfold ProximityPrize.Benchmark.Binary.claimedError
    rw [show -((((6400 : ℕ) : ℝ) / 100)) = -((64 : ℕ) : ℝ) by norm_num,
      NNReal.rpow_neg, NNReal.rpow_natCast]
    norm_num
  calc
    (1 - bchksRadius) ^ BinaryIRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) := by
      rw [← NNReal.coe_le_coe]
      norm_num [bchksRadius, BinaryIRSProfile.repetitions, div_le_iff₀]
    _ = ProximityPrize.Benchmark.Binary.claimedError 6400 := hclaim.symm







set_option maxRecDepth 100000 in
lemma bchksBadBudget_lt_field :
    bchksBadBudget < Fintype.card BinaryIRSProfile.Field := by
  have h := bchks_budget_nat
  have hp : 2 ^ (128 : ℕ) ≤ 2 ^ (192 : ℕ) := by
    have hm : 1 ≤ bchksNumerator + bchksListBound := by
      norm_num [bchksNumerator, bchksListBound]
    exact (Nat.le_mul_of_pos_right (2 ^ (128 : ℕ)) (by omega)).trans h
  have hb : bchksBadBudget < 2 ^ (128 : ℕ) := by
    norm_num [bchksBadBudget]
  rw [show Fintype.card BinaryIRSProfile.Field = 2 ^ (192 : ℕ) from BF64.card_ext3]
  exact hb.trans_le hp

lemma bchks_top_points_arithmetic (r T : ℕ)
    (hT : 2 * 7236927760 * r + (bchksErrors + 1) < T) :
    (2097152 - bchksErrors - 1048576) * T >
      (2097152 - 1048576) * ((2 * 1048575 + 1) * r) := by
  norm_num [bchksErrors] at hT ⊢
  nlinarith

/-- Once the BCHKS alignment extractor is supplied, its exact MCA consequence at the
optimized radius is immediate. -/
theorem base_mca_bchks_le_of_alignment
    (halign : AffineLineAlignmentBound BinaryIRSProfile.baseCode bchksErrors bchksNumerator) :
    mcaError (AffineLineGenerator BinaryIRSProfile.Field) BinaryIRSProfile.baseCode
        (bchksRadius : ℝ) ≤
      ENNReal.ofReal ((bchksNumerator : ℝ) / Fintype.card BinaryIRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound BinaryIRSProfile.baseCode
    (bchksRadius : ℝ) bchksErrors bchksNumerator
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (bchksRadius : ℝ) by positivity)).mp hA
    rw [bchksRadius_floor] at hcomp
    have hn : Fintype.card BinaryIRSProfile.Index = 2097152 := by
      norm_num [BinaryIRSProfile.Index]
    rw [hn]
    norm_num [bchksErrors] at hcomp ⊢
    omega
  · exact halign

end ProximityPrize.SubmissionBinaryLower

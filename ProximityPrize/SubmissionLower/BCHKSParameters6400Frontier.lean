import ProximityPrize.SubmissionLower.BCHKSBridge
import ProximityPrize.SubmissionLower.BCHKSList6400IntegerBall

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open NNReal
open CoreDefinitions
open scoped NNReal

set_option maxRecDepth 100000

/-- Exact MCA numerator still available after the kernel-checked list allowance
`Lambda <= 42324` is charged against the `2^-128` field budget. -/
def bchksNumerator6400 : ℕ := 274980728111352763

/-- The MCA and list allowances exactly fit below the sextic KoalaBear field
budget. -/
lemma bchks6400_budget_nat :
    2 ^ (128 : ℕ) * (bchksNumerator6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksNumerator6400, bchksListBound6400]

/-- Exact score arithmetic at the largest denominator-`2^20` point in the
76,780-error cell. -/
lemma bchksRadius6400_score :
    (1 - bchksRadius6400) ^ IRSProfile.repetitions ≤
      ProximityPrize.Benchmark.claimedError 6400 := by
  have hsq : (1 - bchksRadius6400) ^ 2 ≤ 1 / 2 := by
    have hrle : bchksRadius6400 ≤ 1 := by
      exact (div_le_one (by norm_num : (0 : ℝ≥0) < 1048576)).mpr (by
        norm_num [bchksRadius6400])
    rw [← NNReal.coe_le_coe, NNReal.coe_pow]
    rw [NNReal.coe_sub hrle]
    simp only [bchksRadius6400]
    norm_num
  have hpow :
      (1 - bchksRadius6400) ^ IRSProfile.repetitions ≤
        (1 / 2 : ℝ≥0) ^ 64 := by
    rw [show IRSProfile.repetitions = 2 * 64 from rfl, pow_mul]
    exact pow_le_pow_left' hsq 64
  calc
    (1 - bchksRadius6400) ^ IRSProfile.repetitions ≤
        (1 / 2 : ℝ≥0) ^ 64 := hpow
    _ = ProximityPrize.Benchmark.claimedError 6400 := by
      unfold ProximityPrize.Benchmark.claimedError
      norm_num [NNReal.rpow_neg, NNReal.rpow_natCast]

/-- Once the missing score-64 alignment theorem is supplied, its exact MCA
consequence is immediate from the promoted incidence bridge. -/
theorem base_mca_bchks6400_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6400 bchksNumerator6400) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (bchksRadius6400 : ℝ) ≤
      ENNReal.ofReal
        ((bchksNumerator6400 : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (bchksRadius6400 : ℝ) bchksErrors6400 bchksNumerator6400
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (bchksRadius6400 : ℝ) by positivity)).mp hA
    rw [bchksRadius6400_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [bchksErrors6400] at hcomp ⊢
    omega
  · exact halign

end ProximityPrize.SubmissionLower

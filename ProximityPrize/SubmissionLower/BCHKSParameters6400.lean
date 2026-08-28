import ProximityPrize.SubmissionLower.BCHKSParameters6399
import ProximityPrize.SubmissionLower.BCHKSBridge

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open NNReal
open CoreDefinitions
open scoped NNReal

set_option maxRecDepth 100000

/-- Radius for the score-64 endpoint. -/
noncomputable def bchksRadius6400 : ℝ≥0 := (307121 : ℝ≥0) / 1048576

def bchksErrors6400 : ℕ := 76780

def bchksNumerator6400 : ℕ := 274972148031419760

def bchksListBound6400 : ℕ := 300000

/-- Retuned fused incidence coefficient for the score-64 universal extractor.
The old coefficient is short after the ten-error-coordinate increase;
this coefficient restores the fused inequality while remaining far inside the
score-64 seed budget. -/
def bchksIncidenceCoefficient6400 : ℕ := 1265711

lemma bchks6400_gap_pos :
    0 < 262144 - bchksErrors6400 - 131071 := by
  norm_num [bchksErrors6400]

lemma bchks6400_resultant_degree_cap :
    2 * bchksUniversalExponent6399 * bchksFactorMass6399 *
        bchksFactorZMass6399 + bchksFactorMass6399 =
      36371256962843835 := by
  norm_num [bchksUniversalExponent6399, bchksFactorMass6399,
    bchksFactorZMass6399]

lemma bchks6400_fused_incidence :
    (262144 - 131071) *
        (2 * bchksUniversalExponent6399 * bchksFactorMass6399 *
          bchksFactorZMass6399 + bchksFactorMass6399) ≤
      (262144 - bchksErrors6400 - 131071) *
        (bchksIncidenceCoefficient6400 * bchksFactorMass6399 *
          bchksFactorZMass6399) := by
  norm_num [bchksUniversalExponent6399, bchksFactorMass6399,
    bchksFactorZMass6399, bchksErrors6400,
    bchksIncidenceCoefficient6400]

lemma bchksRadius6400_floor :
    ⌊(bchksRadius6400 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      bchksErrors6400 := by
  norm_num [bchksRadius6400, bchksErrors6400, IRSProfile.Index]

lemma bchksRadius6400_floor_nnreal :
    ⌊bchksRadius6400 * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ =
      bchksErrors6400 := by
  norm_num [bchksRadius6400, bchksErrors6400, IRSProfile.Index]

lemma bchks6400_budget_nat :
    2 ^ (128 : ℕ) * (bchksNumerator6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksNumerator6400, bchksListBound6400]

/-- Exact score arithmetic: the target lies in the first denominator-`2^20`
cell scoring at least sixty-four bits. -/
lemma bchksRadius6400_score :
    (1 - bchksRadius6400) ^ IRSProfile.repetitions ≤
      ProximityPrize.Benchmark.claimedError 6400 := by
  have hsq : (1 - bchksRadius6400) ^ 2 ≤ 1 / 2 := by
    have hrle : bchksRadius6400 ≤ 1 := by
      exact (div_le_one (by norm_num : (0:ℝ≥0)<1048576)).mpr (by
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
  calc (1 - bchksRadius6400) ^ IRSProfile.repetitions ≤
      (1 / 2 : ℝ≥0) ^ 64 := hpow
    _ = ProximityPrize.Benchmark.claimedError 6400 := by
        unfold ProximityPrize.Benchmark.claimedError
        norm_num [NNReal.rpow_neg, NNReal.rpow_natCast]

/-- Once a 64-bit alignment extractor is supplied, its MCA consequence at the
score-64 radius is the same completed incidence argument used at 63.99. -/
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

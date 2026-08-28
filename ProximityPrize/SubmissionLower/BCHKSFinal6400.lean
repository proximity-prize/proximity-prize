import ProximityPrize.SubmissionLower.BCHKSParameters6400
import ProximityPrize.SubmissionLower.BCHKSList6400

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

lemma bchks6400_nat_div_le_inv_pow {m q t : ℕ}
    (hm : 0 < m) (hq : m * 2 ^ t ≤ q) :
    (m : ENNReal) / (q : ENNReal) ≤ 1 / 2 ^ t := by
  have hm0 : (m : ENNReal) ≠ 0 := by
    exact_mod_cast hm.ne'
  have hmtop : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hqE : ((m * 2 ^ t : ℕ) : ENNReal) ≤ (q : ENNReal) := by
    exact_mod_cast hq
  have hcast : ((m * 2 ^ t : ℕ) : ENNReal) =
      (m : ENNReal) * 2 ^ t := by
    push_cast
    ring
  calc
    (m : ENNReal) / (q : ENNReal) ≤
        (m : ENNReal) / ((m * 2 ^ t : ℕ) : ENNReal) :=
      ENNReal.div_le_div_left hqE _
    _ = (m : ENNReal) / ((m : ENNReal) * 2 ^ t) := by rw [hcast]
    _ = (m : ENNReal) * 1 / ((m : ENNReal) * 2 ^ t) := by rw [mul_one]
    _ = 1 / 2 ^ t := ENNReal.mul_div_mul_left 1 (2 ^ t) hm0 hmtop

/-- The score-64 alignment certificate implies the MCA term at its exact radius. -/
lemma mca_bchks6400_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6400 bchksNumerator6400) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (bchksRadius6400 : ℝ) ≤
      (bchksNumerator6400 : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (bchksRadius6400 : ℝ) := by
      simpa [IRSProfile.code, IRSProfile.baseCode,
        ReedSolomon.Interleaved.irsCode,
        IRSProfile.totalDimension_div_interleaving] using
        (ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
          IRSProfile.interleaving bchksRadius6400
          (by norm_num [IRSProfile.interleaving])
          (by norm_num [bchksRadius6400])
          (by norm_num [bchksRadius6400]))
    _ ≤ ENNReal.ofReal ((bchksNumerator6400 : ℝ) /
          Fintype.card IRSProfile.Field) :=
      base_mca_bchks6400_le_of_alignment halign
    _ = (bchksNumerator6400 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

/-- MCA, the finite-Johnson list term, and the field-capacity calculation close
the certified extractor error at the score-64 radius. -/
theorem certifiedGammaError_bchks6400_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6400 bchksNumerator6400) :
    certifiedGammaError IRSProfile.code bchksRadius6400 ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat :
      (Code.Lambda BCHKS6399SquaredCode
        (bchksRadius6400 : ℝ)).toNat ≤ bchksListBound6400 :=
    ENat.toNat_le_of_le_coe bchks6400_lambda_le
  have hList :
      ((Code.Lambda BCHKS6399SquaredCode
        (bchksRadius6400 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (bchksListBound6400 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
          (bchksRadius6400 : ℝ) +
        ((Code.Lambda
          ((IRSProfile.code ^⋈ (Fin 2) :
            ModuleCode IRSProfile.Index IRSProfile.Field
              (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
            Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
              IRSProfile.Field))
          (bchksRadius6400 : ℝ)).toNat : ENNReal) /
            (Fintype.card IRSProfile.Field : ENNReal) ≤
      (bchksNumerator6400 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (bchksListBound6400 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      apply add_le_add (mca_bchks6400_le_of_alignment halign)
      simpa [BCHKS6399SquaredCode] using hList
    _ = ((bchksNumerator6400 + bchksListBound6400 : ℕ) : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div]
      norm_num
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply bchks6400_nat_div_le_inv_pow
      · norm_num [bchksNumerator6400, bchksListBound6400]
      · simpa [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize,
          Nat.mul_comm] using bchks6400_budget_nat

end ProximityPrize.SubmissionLower

namespace ProximityPrize.Benchmark

open ToyProblem
open scoped NNReal

/-- Conditional final claim. Supplying a score-64 affine-line alignment bound
closes every reduction and score obligation for the one-centibit advance. -/
theorem protocolClaim6400_of_alignment
    (halign : ProximityPrize.SubmissionLower.AffineLineAlignmentBound
      IRSProfile.baseCode
      ProximityPrize.SubmissionLower.bchksErrors6400
      ProximityPrize.SubmissionLower.bchksNumerator6400) :
    ProtocolClaim 6400 307121 1048576 where
  admissible := by
    constructor <;>
      norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have h : ToyProblem.certifiedGammaError IRSProfile.code
        ProximityPrize.SubmissionLower.bchksRadius6400 ≤ reductionTarget :=
      (ProximityPrize.SubmissionLower.certifiedGammaError_bchks6400_le_of_alignment
        halign).trans (by
          norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hr : claimedRadius 307121 1048576 =
        ProximityPrize.SubmissionLower.bchksRadius6400 := by
      norm_num [claimedRadius,
        ProximityPrize.SubmissionLower.bchksRadius6400]
    have hc :
        ReedSolomon.Interleaved.irsCode IRSProfile.domain
            IRSProfile.totalDimension IRSProfile.interleaving =
          IRSProfile.code := by
      rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    exact h
  score := by
    have hr : claimedRadius 307121 1048576 =
        ProximityPrize.SubmissionLower.bchksRadius6400 := by
      norm_num [claimedRadius,
        ProximityPrize.SubmissionLower.bchksRadius6400]
    rw [hr]
    exact ProximityPrize.SubmissionLower.bchksRadius6400_score

end ProximityPrize.Benchmark

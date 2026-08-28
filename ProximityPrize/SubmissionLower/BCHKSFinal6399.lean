import ProximityPrize.SubmissionLower.BCHKSAlignmentInterface6399
import ProximityPrize.SubmissionLower.BCHKSList6399
import ProximityPrize.SubmissionLower.BCHKSUniversalPolynomialAlignment6399

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

lemma bchks6399_nat_div_le_inv_pow {m q t : ℕ}
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

/-- The 63.99 alignment certificate implies the MCA term at its exact radius. -/
lemma mca_bchks6399_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6399 bchksNumerator6399) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (bchksRadius6399 : ℝ) ≤
      (bchksNumerator6399 : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (bchksRadius6399 : ℝ) := by
      simpa [IRSProfile.code, IRSProfile.baseCode,
        ReedSolomon.Interleaved.irsCode,
        IRSProfile.totalDimension_div_interleaving] using
        (ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
          IRSProfile.interleaving bchksRadius6399
          (by norm_num [IRSProfile.interleaving])
          (by norm_num [bchksRadius6399])
          (by norm_num [bchksRadius6399]))
    _ ≤ ENNReal.ofReal ((bchksNumerator6399 : ℝ) /
          Fintype.card IRSProfile.Field) :=
      base_mca_bchks6399_le_of_alignment halign
    _ = (bchksNumerator6399 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

/-- MCA, the Johnson list bound, and the exact field-capacity calculation close
the certified gamma error at 63.99 bits. -/
theorem certifiedGammaError_bchks6399_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6399 bchksNumerator6399) :
    certifiedGammaError IRSProfile.code bchksRadius6399 ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat :
      (Code.Lambda BCHKS6399SquaredCode
        (bchksRadius6399 : ℝ)).toNat ≤ bchksListBound6399 :=
    ENat.toNat_le_of_le_coe bchks6399_lambda_le
  have hList :
      ((Code.Lambda BCHKS6399SquaredCode
        (bchksRadius6399 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (bchksListBound6399 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
          (bchksRadius6399 : ℝ) +
        ((Code.Lambda
          ((IRSProfile.code ^⋈ (Fin 2) :
            ModuleCode IRSProfile.Index IRSProfile.Field
              (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
            Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
              IRSProfile.Field))
          (bchksRadius6399 : ℝ)).toNat : ENNReal) /
            (Fintype.card IRSProfile.Field : ENNReal) ≤
      (bchksNumerator6399 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (bchksListBound6399 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      apply add_le_add (mca_bchks6399_le_of_alignment halign)
      simpa [BCHKS6399SquaredCode] using hList
    _ = ((bchksNumerator6399 + bchksListBound6399 : ℕ) : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div]
      norm_num
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply bchks6399_nat_div_le_inv_pow
      · norm_num [bchksNumerator6399, bchksListBound6399]
      · simpa [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize,
          Nat.mul_comm] using bchks6399_budget_nat

/-- The isolated polynomial-alignment statement supplies the alignment premise
of the completed analytic pipeline. -/
theorem certifiedGammaError_bchks6399_le_of_polynomialAlignment
    (halg : BCHKSPolynomialAlignment6399) :
    certifiedGammaError IRSProfile.code bchksRadius6399 ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) :=
  certifiedGammaError_bchks6399_le_of_alignment
    (alignmentBound6399_of_polynomialAlignment halg)

end ProximityPrize.SubmissionLower

namespace ProximityPrize.Benchmark

open ToyProblem
open scoped NNReal

/-- Conditional final claim.  Supplying the universal-resultant alignment
extractor closes every obligation of the 63.99 certificate. -/
theorem protocolClaim6399_of_polynomialAlignment
    (halg : ProximityPrize.SubmissionLower.BCHKSPolynomialAlignment6399) :
    ProtocolClaim 6399 307083 1048576 where
  admissible := by
    constructor <;>
      norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have h : ToyProblem.certifiedGammaError IRSProfile.code
        ProximityPrize.SubmissionLower.bchksRadius6399 ≤ reductionTarget :=
      (ProximityPrize.SubmissionLower.certifiedGammaError_bchks6399_le_of_polynomialAlignment
        halg).trans (by
          norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hr : claimedRadius 307083 1048576 =
        ProximityPrize.SubmissionLower.bchksRadius6399 := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.bchksRadius6399]
    have hc :
        ReedSolomon.Interleaved.irsCode IRSProfile.domain
            IRSProfile.totalDimension IRSProfile.interleaving =
          IRSProfile.code := by
      rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    exact h
  score := by
    have hr : claimedRadius 307083 1048576 =
        ProximityPrize.SubmissionLower.bchksRadius6399 := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.bchksRadius6399]
    rw [hr]
    exact ProximityPrize.SubmissionLower.bchksRadius6399_score

/-- Unconditional public endpoint supplied by the universal-resultant
alignment extractor. -/
theorem protocolClaim6399 : ProtocolClaim 6399 307083 1048576 :=
  protocolClaim6399_of_polynomialAlignment
    ProximityPrize.SubmissionLower.bchksPolynomialAlignment6399

end ProximityPrize.Benchmark

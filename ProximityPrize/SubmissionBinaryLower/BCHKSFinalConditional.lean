import ProximityPrize.SubmissionBinaryLower.BCHKSAlignmentInterface
import ProximityPrize.SubmissionBinaryLower.BCHKSSoundness

namespace ProximityPrize.SubmissionBinaryLower

open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open ToyProblem
open scoped NNReal

/-- The entire reduction certificate follows from the now-isolated polynomial
alignment theorem. -/
theorem certifiedGammaError_bchks_le_of_polynomialAlignment
    (halg : BCHKSPolynomialAlignment) :
    certifiedGammaError BinaryIRSProfile.code bchksRadius ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) :=
  certifiedGammaError_bchks_le_of_alignment
    (alignmentBound_of_polynomialAlignment halg)

end ProximityPrize.SubmissionBinaryLower

namespace ProximityPrize.Benchmark.Binary

open ToyProblem
open scoped NNReal

/-- Conditional final claim: every obligation except `BCHKSPolynomialAlignment`
is compiled with the optimized score `63.99`. -/
theorem protocolClaim6358_of_polynomialAlignment
    (halg : ProximityPrize.SubmissionBinaryLower.BCHKSPolynomialAlignment) :
    ProtocolClaim 6399 314458111 1073741824 where
  admissible := by
    constructor <;>
      norm_num [claimedRadius, BinaryIRSProfile.minRelativeDistance]
  reduction := by
    have h : ToyProblem.certifiedGammaError BinaryIRSProfile.code
        ProximityPrize.SubmissionBinaryLower.bchksRadius ≤ reductionTarget :=
      (ProximityPrize.SubmissionBinaryLower.certifiedGammaError_bchks_le_of_polynomialAlignment halg).trans (by
        norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hr : claimedRadius 314458111 1073741824 =
        ProximityPrize.SubmissionBinaryLower.bchksRadius := by
      norm_num [claimedRadius, ProximityPrize.SubmissionBinaryLower.bchksRadius]
    have hc :
        ReedSolomon.Interleaved.irsCode BinaryIRSProfile.domain
            BinaryIRSProfile.totalDimension BinaryIRSProfile.interleaving = BinaryIRSProfile.code := by
      rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    exact h
  score := by
    have hr : claimedRadius 314458111 1073741824 =
        ProximityPrize.SubmissionBinaryLower.bchksRadius := by
      norm_num [claimedRadius, ProximityPrize.SubmissionBinaryLower.bchksRadius]
    rw [hr]
    exact ProximityPrize.SubmissionBinaryLower.bchksRadius_score

end ProximityPrize.Benchmark.Binary

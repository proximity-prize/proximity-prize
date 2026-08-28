import ProximityPrize.SubmissionLower.BCHKSAlignmentInterface
import ProximityPrize.SubmissionLower.BCHKSSoundness

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open ToyProblem
open scoped NNReal

/-- The entire reduction certificate follows from the now-isolated polynomial
alignment theorem. -/
theorem certifiedGammaError_bchks_le_of_polynomialAlignment
    (halg : BCHKSPolynomialAlignment) :
    certifiedGammaError IRSProfile.code bchksRadius ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) :=
  certifiedGammaError_bchks_le_of_alignment
    (alignmentBound_of_polynomialAlignment halg)

end ProximityPrize.SubmissionLower

namespace ProximityPrize.Benchmark

open ToyProblem
open scoped NNReal

/-- Conditional final claim: every obligation except `BCHKSPolynomialAlignment`
is compiled with the optimized score `63.94`. -/
theorem protocolClaim6394_of_polynomialAlignment
    (halg : ProximityPrize.SubmissionLower.BCHKSPolynomialAlignment) :
    ProtocolClaim 6394 306887 1048576 where
  admissible := by
    constructor <;>
      norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have h : ToyProblem.certifiedGammaError IRSProfile.code
        ProximityPrize.SubmissionLower.bchksRadius ≤ reductionTarget :=
      (ProximityPrize.SubmissionLower.certifiedGammaError_bchks_le_of_polynomialAlignment halg).trans (by
        norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hr : claimedRadius 306887 1048576 =
        ProximityPrize.SubmissionLower.bchksRadius := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.bchksRadius]
    have hc :
        ReedSolomon.Interleaved.irsCode IRSProfile.domain
            IRSProfile.totalDimension IRSProfile.interleaving = IRSProfile.code := by
      rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    exact h
  score := by
    have hr : claimedRadius 306887 1048576 =
        ProximityPrize.SubmissionLower.bchksRadius := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.bchksRadius]
    rw [hr]
    exact ProximityPrize.SubmissionLower.bchksRadius_score

end ProximityPrize.Benchmark

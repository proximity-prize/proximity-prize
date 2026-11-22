import ProximityPrize.SubmissionLower.FrontIntermediate
import ProximityPrize.SubmissionLower.Cell82IntermediateProtocol

set_option Elab.async false
namespace FrontIntermediate

open Cell82Intermediate ProximityPrize.Benchmark

/-- A count at the original agreement and the common height cap gives the exact cell claim. -/
theorem of_core_count (t : Target) (count : CoreCount (agreement t) coreBudget) :
    ProtocolClaim (data t).score (data t).numerator (data t).denominator := by
  apply Cell82Intermediate.of_bad_slopes t
  exact count_of_bad_slopes (by cases t <;> decide) count

#print axioms of_core_count
end FrontIntermediate

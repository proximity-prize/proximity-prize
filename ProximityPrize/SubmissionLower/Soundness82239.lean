import ProximityPrize.SubmissionLower.Front52Interval
import ProximityPrize.SubmissionLower.Rect52Window

set_option Elab.async false
namespace Soundness82239
open ProximityPrize.Benchmark

/-- The exact radius permits 82,239 errors in a word of length 262,144. -/
theorem protocol : ProtocolClaim 6952 2893562760585543664 9223372036854775757 := by
  apply Front52Interval.of_interval
  intro u del M Γ F hlo hhi
  exact (Rect52Window.ordinary M F hlo hhi).trans (by decide)

#print axioms protocol
end Soundness82239

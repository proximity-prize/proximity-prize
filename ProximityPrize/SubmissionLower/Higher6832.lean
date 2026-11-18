import ProximityPrize.SubmissionLower.Koala6831BenchmarkShortCount
import ProximityPrize.SubmissionLower.LP32EarlierComplete

namespace ProximityPrize.SubmissionLower
open ProximityPrize.Benchmark Koala6831BenchmarkField Koala6831BenchmarkResidual
open Koala6831BenchmarkRetention Koala6831BenchmarkPrimitive

theorem higher6832 : ProtocolClaim 6832 332050431 1073741824 := by
  let _ : CharP IRSProfile.Field 2130706433 := characteristic
  apply protocolClaim_6832_of_separated_counts
  · intro u Γ f q h lo hi N _
    exact Koala6831BenchmarkResidual.separated_from_9554_at_81066 domain_fixed frobenius_apply IRSProfile.card_index
      h.primitive h.first_ne h.second_ne lo hi N h.good h.selection.degree_le
      h.selection.agreement h.selection.pencil
  · exact Koala6831BenchmarkShortCount.benchmark_short_separated_count

#print axioms higher6832
end ProximityPrize.SubmissionLower

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/

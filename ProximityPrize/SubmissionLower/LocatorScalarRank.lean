import ProximityPrize.SubmissionLower.LocatorScalarRankA
import ProximityPrize.SubmissionLower.LocatorScalarRankB

/-! Assembly of the separately checked scalar local-rank chunks. -/

namespace ProximityPrize.SubmissionLower.LocatorScalarRank

open scoped BigOperators
open ProximityPrize.Benchmark RCN279
open LocatorScalarParameters

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem localRankBound_exact :
    localRankBound 92 127 27 = 91938 := by
  change (∑ r ∈ Finset.range 92, rankRow r) = _
  rw [Finset.sum_range_add rankRow 72 20,
    Finset.sum_range_add rankRow 48 24,
    Finset.sum_range_add rankRow 24 24,
    chunk_0, chunk_24, chunk_48, chunk_72]

end ProximityPrize.SubmissionLower.LocatorScalarRank

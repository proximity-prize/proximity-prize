import ProximityPrize.SubmissionLower.LocatorSplit500RankA
import ProximityPrize.SubmissionLower.LocatorSplit500RankB

/-! Assembly of the separately checked Split500 local-rank chunks. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit500Rank

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN119
open LocatorFastKernelArithmetic LocatorLowQuotient LocatorSplit500Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem fastLocalRankBound_exact :
    fastLocalRankBound 500 21000 155 = 306404547280 := by
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 500, rankRow r) = _
  rw [Finset.sum_range_add rankRow 448 52,
    Finset.sum_range_add rankRow 384 64,
    Finset.sum_range_add rankRow 320 64,
    Finset.sum_range_add rankRow 256 64,
    Finset.sum_range_add rankRow 192 64,
    Finset.sum_range_add rankRow 128 64,
    Finset.sum_range_add rankRow 64 64,
    chunk_0, chunk_64, chunk_128, chunk_192,
    chunk_256, chunk_320, chunk_384, chunk_448]

theorem localRankBound_exact :
    localRankBound 500 21000 155 = 306404547280 := by
  rw [localRankBound_eq_fastLocalRankBound 500 21000 155 (by decide)]
  exact fastLocalRankBound_exact

end ProximityPrize.SubmissionLower.LocatorSplit500Rank

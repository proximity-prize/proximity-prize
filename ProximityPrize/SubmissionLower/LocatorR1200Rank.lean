import ProximityPrize.SubmissionLower.LocatorR1200RankA
import ProximityPrize.SubmissionLower.LocatorR1200RankB
import ProximityPrize.SubmissionLower.LocatorR1200RankC
import ProximityPrize.SubmissionLower.LocatorR1200RankD

/-! Assembly of the separately checked R1200 local-rank chunks. -/

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN119
open LocatorFastKernelArithmetic LocatorLowQuotient LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem fastLocalRankBound_exact :
    fastLocalRankBound 1200 82100 370 = 16470445690720 := by
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 1200, rankRow r) = _
  rw [Finset.sum_range_add rankRow 1152 48,
    Finset.sum_range_add rankRow 1088 64,
    Finset.sum_range_add rankRow 1024 64,
    Finset.sum_range_add rankRow 960 64,
    Finset.sum_range_add rankRow 896 64,
    Finset.sum_range_add rankRow 832 64,
    Finset.sum_range_add rankRow 768 64,
    Finset.sum_range_add rankRow 704 64,
    Finset.sum_range_add rankRow 640 64,
    Finset.sum_range_add rankRow 576 64,
    Finset.sum_range_add rankRow 512 64,
    Finset.sum_range_add rankRow 448 64,
    Finset.sum_range_add rankRow 384 64,
    Finset.sum_range_add rankRow 320 64,
    Finset.sum_range_add rankRow 256 64,
    Finset.sum_range_add rankRow 192 64,
    Finset.sum_range_add rankRow 128 64,
    Finset.sum_range_add rankRow 64 64,
    chunk_0, chunk_64, chunk_128, chunk_192, chunk_256,
    chunk_320, chunk_384, chunk_448, chunk_512, chunk_576,
    chunk_640, chunk_704, chunk_768, chunk_832, chunk_896,
    chunk_960, chunk_1024, chunk_1088, chunk_1152]

theorem localRankBound_exact :
    localRankBound 1200 82100 370 = 16470445690720 := by
  rw [localRankBound_eq_fastLocalRankBound 1200 82100 370 (by decide)]
  exact fastLocalRankBound_exact

end ProximityPrize.SubmissionLower.LocatorR1200Rank

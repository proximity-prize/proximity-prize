import ProximityPrize.SubmissionLower.LocatorSplit390RankB

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390Rank. -/
section PackedLocator_LocatorSplit390Rank

/-! Assembly of the separately checked Split390 local-rank chunks. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit390Rank

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN119
open LocatorFastKernelArithmetic LocatorLowQuotient LocatorSplit390Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem fastLocalRankBound_exact :
    fastLocalRankBound 390 19500 120 = 134851176130 := by
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 390, rankRow r) = _
  rw [Finset.sum_range_add rankRow 384 6,
    Finset.sum_range_add rankRow 320 64,
    Finset.sum_range_add rankRow 256 64,
    Finset.sum_range_add rankRow 192 64,
    Finset.sum_range_add rankRow 128 64,
    Finset.sum_range_add rankRow 64 64,
    chunk_0, chunk_64, chunk_128, chunk_192,
    chunk_256, chunk_320, chunk_384]

theorem localRankBound_exact :
    localRankBound 390 19500 120 = 134851176130 := by
  rw [localRankBound_eq_fastLocalRankBound 390 19500 120 (by decide)]
  exact fastLocalRankBound_exact

end ProximityPrize.SubmissionLower.LocatorSplit390Rank
end PackedLocator_LocatorSplit390Rank

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier41 : True := by trivial
end ProximityPrize.SubmissionLower


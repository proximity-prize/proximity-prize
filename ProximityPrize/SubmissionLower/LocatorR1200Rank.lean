import ProximityPrize.SubmissionLower.LocatorR1200RankO

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Rank. -/
section PackedLocator_LocatorR1200Rank

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
    fastLocalRankBound 4800 328400 1480 = 4204024854809180 := by
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 4800, rankRow r) = _
  rw [Finset.sum_range_add rankRow 4736 64,
    Finset.sum_range_add rankRow 4672 64,
    Finset.sum_range_add rankRow 4608 64,
    Finset.sum_range_add rankRow 4544 64,
    Finset.sum_range_add rankRow 4480 64,
    Finset.sum_range_add rankRow 4416 64,
    Finset.sum_range_add rankRow 4352 64,
    Finset.sum_range_add rankRow 4288 64,
    Finset.sum_range_add rankRow 4224 64,
    Finset.sum_range_add rankRow 4160 64,
    Finset.sum_range_add rankRow 4096 64,
    Finset.sum_range_add rankRow 4032 64,
    Finset.sum_range_add rankRow 3968 64,
    Finset.sum_range_add rankRow 3904 64,
    Finset.sum_range_add rankRow 3840 64,
    Finset.sum_range_add rankRow 3776 64,
    Finset.sum_range_add rankRow 3712 64,
    Finset.sum_range_add rankRow 3648 64,
    Finset.sum_range_add rankRow 3584 64,
    Finset.sum_range_add rankRow 3520 64,
    Finset.sum_range_add rankRow 3456 64,
    Finset.sum_range_add rankRow 3392 64,
    Finset.sum_range_add rankRow 3328 64,
    Finset.sum_range_add rankRow 3264 64,
    Finset.sum_range_add rankRow 3200 64,
    Finset.sum_range_add rankRow 3136 64,
    Finset.sum_range_add rankRow 3072 64,
    Finset.sum_range_add rankRow 3008 64,
    Finset.sum_range_add rankRow 2944 64,
    Finset.sum_range_add rankRow 2880 64,
    Finset.sum_range_add rankRow 2816 64,
    Finset.sum_range_add rankRow 2752 64,
    Finset.sum_range_add rankRow 2688 64,
    Finset.sum_range_add rankRow 2624 64,
    Finset.sum_range_add rankRow 2560 64,
    Finset.sum_range_add rankRow 2496 64,
    Finset.sum_range_add rankRow 2432 64,
    Finset.sum_range_add rankRow 2368 64,
    Finset.sum_range_add rankRow 2304 64,
    Finset.sum_range_add rankRow 2240 64,
    Finset.sum_range_add rankRow 2176 64,
    Finset.sum_range_add rankRow 2112 64,
    Finset.sum_range_add rankRow 2048 64,
    Finset.sum_range_add rankRow 1984 64,
    Finset.sum_range_add rankRow 1920 64,
    Finset.sum_range_add rankRow 1856 64,
    Finset.sum_range_add rankRow 1792 64,
    Finset.sum_range_add rankRow 1728 64,
    Finset.sum_range_add rankRow 1664 64,
    Finset.sum_range_add rankRow 1600 64,
    Finset.sum_range_add rankRow 1536 64,
    Finset.sum_range_add rankRow 1472 64,
    Finset.sum_range_add rankRow 1408 64,
    Finset.sum_range_add rankRow 1344 64,
    Finset.sum_range_add rankRow 1280 64,
    Finset.sum_range_add rankRow 1216 64,
    Finset.sum_range_add rankRow 1152 64,
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
    chunk_960, chunk_1024, chunk_1088, chunk_1152, chunk_1216,
    chunk_1280, chunk_1344, chunk_1408, chunk_1472, chunk_1536,
    chunk_1600, chunk_1664, chunk_1728, chunk_1792, chunk_1856,
    chunk_1920, chunk_1984, chunk_2048, chunk_2112, chunk_2176,
    chunk_2240, chunk_2304, chunk_2368, chunk_2432, chunk_2496,
    chunk_2560, chunk_2624, chunk_2688, chunk_2752, chunk_2816,
    chunk_2880, chunk_2944, chunk_3008, chunk_3072, chunk_3136,
    chunk_3200, chunk_3264, chunk_3328, chunk_3392, chunk_3456,
    chunk_3520, chunk_3584, chunk_3648, chunk_3712, chunk_3776,
    chunk_3840, chunk_3904, chunk_3968, chunk_4032, chunk_4096,
    chunk_4160, chunk_4224, chunk_4288, chunk_4352, chunk_4416,
    chunk_4480, chunk_4544, chunk_4608, chunk_4672, chunk_4736]

theorem localRankBound_exact :
    localRankBound 4800 328400 1480 = 4204024854809180 := by
  rw [localRankBound_eq_fastLocalRankBound 4800 328400 1480 (by decide)]
  exact fastLocalRankBound_exact

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200Rank

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier26 : True := by trivial
end ProximityPrize.SubmissionLower


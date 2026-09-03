import ProximityPrize.SubmissionLower.LocatorPhase6802SourceSound

namespace ProximityPrize.SubmissionLower.LocatorKernels6802Arithmetic

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119
open LocatorFastKernelArithmetic LocatorLowQuotient

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem coefficientCount_R4800L300k :
    coefficientCount 870590400 131071 300000 1477 =
      1009189622590133608008 := by
  rw [coefficientCount_eq_oneResidueCoefficientCount
    6642 16818 131071 300000 1477
    (by decide) (by decide) (by decide) (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

theorem coefficientCount_R2400L200k :
    coefficientCount 435295200 131071 200000 738 =
      84316274739920078196 := by
  rw [coefficientCount_eq_oneResidueCoefficientCount
    3321 8409 131071 200000 738
    (by decide) (by decide) (by decide) (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

theorem coefficientCount_R1200 :
    coefficientCount 217647600 131071 82100 370 =
      4336440015677516390 := by
  rw [coefficientCount_eq_oneResidueCoefficientCount
    1660 69740 131071 82100 370
    (by decide) (by decide) (by decide) (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

theorem coefficientCount_Split390 :
    coefficientCount 70735470 131071 19500 120 =
      35445850035150610 := by
  rw [coefficientCount_eq_oneResidueCoefficientCount
    539 88201 131071 19500 120
    (by decide) (by decide) (by decide) (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

def rankRow_R2400_L200k (r : ℕ) : ℕ :=
  let M := min r 200000
  let h := min (r + 1) (2400 - r)
  rectangularCount (M + 1) (738 + 1) 0 200000 -
    rectangularCount (M + 1 - h) (738 + 1 - h) h 200000

theorem rankRow_R2400_L200k_chunk_0 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k r) =
      306826060320 := by decide

theorem rankRow_R2400_L200k_chunk_64 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (64 + r)) =
      910907220512 := by decide

theorem rankRow_R2400_L200k_chunk_128 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (128 + r)) =
      1514794656288 := by decide

theorem rankRow_R2400_L200k_chunk_192 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (192 + r)) =
      2118488367648 := by decide

theorem rankRow_R2400_L200k_chunk_256 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (256 + r)) =
      2721988354592 := by decide

theorem rankRow_R2400_L200k_chunk_320 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (320 + r)) =
      3325294617120 := by decide

theorem rankRow_R2400_L200k_chunk_384 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (384 + r)) =
      3928407155232 := by decide

theorem rankRow_R2400_L200k_chunk_448 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (448 + r)) =
      4531325968928 := by decide

theorem rankRow_R2400_L200k_chunk_512 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (512 + r)) =
      5134051058208 := by decide

theorem rankRow_R2400_L200k_chunk_576 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (576 + r)) =
      5736582423072 := by decide

theorem rankRow_R2400_L200k_chunk_640 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (640 + r)) =
      6338920063520 := by decide

theorem rankRow_R2400_L200k_chunk_704 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (704 + r)) =
      6941063979552 := by decide

theorem rankRow_R2400_L200k_chunk_768 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (768 + r)) =
      7543014171168 := by decide

theorem rankRow_R2400_L200k_chunk_832 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (832 + r)) =
      8144770638368 := by decide

theorem rankRow_R2400_L200k_chunk_896 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (896 + r)) =
      8746333381152 := by decide

theorem rankRow_R2400_L200k_chunk_960 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (960 + r)) =
      9347702399520 := by decide

theorem rankRow_R2400_L200k_chunk_1024 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1024 + r)) =
      9948877693472 := by decide

theorem rankRow_R2400_L200k_chunk_1088 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1088 + r)) =
      10549859263008 := by decide

theorem rankRow_R2400_L200k_chunk_1152 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1152 + r)) =
      11150647108128 := by decide

theorem rankRow_R2400_L200k_chunk_1216 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1216 + r)) =
      11751241228832 := by decide

theorem rankRow_R2400_L200k_chunk_1280 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1280 + r)) =
      12351641625120 := by decide

theorem rankRow_R2400_L200k_chunk_1344 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1344 + r)) =
      12951848296992 := by decide

theorem rankRow_R2400_L200k_chunk_1408 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1408 + r)) =
      13551861244448 := by decide

theorem rankRow_R2400_L200k_chunk_1472 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1472 + r)) =
      14151680467488 := by decide

theorem rankRow_R2400_L200k_chunk_1536 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1536 + r)) =
      14751305966112 := by decide

theorem rankRow_R2400_L200k_chunk_1600 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1600 + r)) =
      15350185273268 := by decide

theorem rankRow_R2400_L200k_chunk_1664 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1664 + r)) =
      15505900181184 := by decide

theorem rankRow_R2400_L200k_chunk_1728 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1728 + r)) =
      15137066712768 := by decide

theorem rankRow_R2400_L200k_chunk_1792 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1792 + r)) =
      14559977924288 := by decide

theorem rankRow_R2400_L200k_chunk_1856 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1856 + r)) =
      13774734479040 := by decide

theorem rankRow_R2400_L200k_chunk_1920 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1920 + r)) =
      12781437040320 := by decide

theorem rankRow_R2400_L200k_chunk_1984 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (1984 + r)) =
      11580186271424 := by decide

theorem rankRow_R2400_L200k_chunk_2048 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (2048 + r)) =
      10171082835648 := by decide

theorem rankRow_R2400_L200k_chunk_2112 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (2112 + r)) =
      8554227396288 := by decide

theorem rankRow_R2400_L200k_chunk_2176 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (2176 + r)) =
      6729720616640 := by decide

theorem rankRow_R2400_L200k_chunk_2240 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (2240 + r)) =
      4697663160000 := by decide

theorem rankRow_R2400_L200k_chunk_2304 :
    (∑ r ∈ Finset.range 64, rankRow_R2400_L200k (2304 + r)) =
      2458155689664 := by decide

theorem rankRow_R2400_L200k_chunk_2368 :
    (∑ r ∈ Finset.range 32, rankRow_R2400_L200k (2368 + r)) =
      324461939296 := by decide

theorem localRank_R2400L200k :
    localRankBound 2400 200000 738 = 320074232928628 := by
  rw [localRankBound_eq_fastLocalRankBound 2400 200000 738 (by decide)]
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 2400, rankRow_R2400_L200k r) = _
  rw [Finset.sum_range_add rankRow_R2400_L200k 2368 32,
    Finset.sum_range_add rankRow_R2400_L200k 2304 64,
    Finset.sum_range_add rankRow_R2400_L200k 2240 64,
    Finset.sum_range_add rankRow_R2400_L200k 2176 64,
    Finset.sum_range_add rankRow_R2400_L200k 2112 64,
    Finset.sum_range_add rankRow_R2400_L200k 2048 64,
    Finset.sum_range_add rankRow_R2400_L200k 1984 64,
    Finset.sum_range_add rankRow_R2400_L200k 1920 64,
    Finset.sum_range_add rankRow_R2400_L200k 1856 64,
    Finset.sum_range_add rankRow_R2400_L200k 1792 64,
    Finset.sum_range_add rankRow_R2400_L200k 1728 64,
    Finset.sum_range_add rankRow_R2400_L200k 1664 64,
    Finset.sum_range_add rankRow_R2400_L200k 1600 64,
    Finset.sum_range_add rankRow_R2400_L200k 1536 64,
    Finset.sum_range_add rankRow_R2400_L200k 1472 64,
    Finset.sum_range_add rankRow_R2400_L200k 1408 64,
    Finset.sum_range_add rankRow_R2400_L200k 1344 64,
    Finset.sum_range_add rankRow_R2400_L200k 1280 64,
    Finset.sum_range_add rankRow_R2400_L200k 1216 64,
    Finset.sum_range_add rankRow_R2400_L200k 1152 64,
    Finset.sum_range_add rankRow_R2400_L200k 1088 64,
    Finset.sum_range_add rankRow_R2400_L200k 1024 64,
    Finset.sum_range_add rankRow_R2400_L200k 960 64,
    Finset.sum_range_add rankRow_R2400_L200k 896 64,
    Finset.sum_range_add rankRow_R2400_L200k 832 64,
    Finset.sum_range_add rankRow_R2400_L200k 768 64,
    Finset.sum_range_add rankRow_R2400_L200k 704 64,
    Finset.sum_range_add rankRow_R2400_L200k 640 64,
    Finset.sum_range_add rankRow_R2400_L200k 576 64,
    Finset.sum_range_add rankRow_R2400_L200k 512 64,
    Finset.sum_range_add rankRow_R2400_L200k 448 64,
    Finset.sum_range_add rankRow_R2400_L200k 384 64,
    Finset.sum_range_add rankRow_R2400_L200k 320 64,
    Finset.sum_range_add rankRow_R2400_L200k 256 64,
    Finset.sum_range_add rankRow_R2400_L200k 192 64,
    Finset.sum_range_add rankRow_R2400_L200k 128 64,
    Finset.sum_range_add rankRow_R2400_L200k 64 64,
    rankRow_R2400_L200k_chunk_0,
    rankRow_R2400_L200k_chunk_64,
    rankRow_R2400_L200k_chunk_128,
    rankRow_R2400_L200k_chunk_192,
    rankRow_R2400_L200k_chunk_256,
    rankRow_R2400_L200k_chunk_320,
    rankRow_R2400_L200k_chunk_384,
    rankRow_R2400_L200k_chunk_448,
    rankRow_R2400_L200k_chunk_512,
    rankRow_R2400_L200k_chunk_576,
    rankRow_R2400_L200k_chunk_640,
    rankRow_R2400_L200k_chunk_704,
    rankRow_R2400_L200k_chunk_768,
    rankRow_R2400_L200k_chunk_832,
    rankRow_R2400_L200k_chunk_896,
    rankRow_R2400_L200k_chunk_960,
    rankRow_R2400_L200k_chunk_1024,
    rankRow_R2400_L200k_chunk_1088,
    rankRow_R2400_L200k_chunk_1152,
    rankRow_R2400_L200k_chunk_1216,
    rankRow_R2400_L200k_chunk_1280,
    rankRow_R2400_L200k_chunk_1344,
    rankRow_R2400_L200k_chunk_1408,
    rankRow_R2400_L200k_chunk_1472,
    rankRow_R2400_L200k_chunk_1536,
    rankRow_R2400_L200k_chunk_1600,
    rankRow_R2400_L200k_chunk_1664,
    rankRow_R2400_L200k_chunk_1728,
    rankRow_R2400_L200k_chunk_1792,
    rankRow_R2400_L200k_chunk_1856,
    rankRow_R2400_L200k_chunk_1920,
    rankRow_R2400_L200k_chunk_1984,
    rankRow_R2400_L200k_chunk_2048,
    rankRow_R2400_L200k_chunk_2112,
    rankRow_R2400_L200k_chunk_2176,
    rankRow_R2400_L200k_chunk_2240,
    rankRow_R2400_L200k_chunk_2304,
    rankRow_R2400_L200k_chunk_2368]

theorem nullity_R4800L300k :
    coefficientCount 870590400 131071 300000 1477 -
      262144 * localRankBound 4800 300000 1477 =
        4607803177954025032 := by
  rw [coefficientCount_R4800L300k, LocatorKernels6801.localRank_R4800L300k]

theorem nullity_R2400L200k :
    coefficientCount 435295200 131071 200000 738 -
      262144 * localRankBound 2400 200000 738 =
        410735023077819764 := by
  rw [coefficientCount_R2400L200k, localRank_R2400L200k]

theorem nullity_R1200 :
    coefficientCount 217647600 131071 82100 370 -
      262144 * localRankBound 1200 82100 370 =
        18811500529412710 := by
  rw [coefficientCount_R1200, LocatorKernels6801.localRank_R1200]

theorem nullity_Split390 :
    coefficientCount 70735470 131071 19500 120 -
      262144 * localRankBound 390 19500 120 =
        95423319727890 := by
  rw [coefficientCount_Split390, LocatorKernels6801.localRank_Split390]

end ProximityPrize.SubmissionLower.LocatorKernels6802Arithmetic

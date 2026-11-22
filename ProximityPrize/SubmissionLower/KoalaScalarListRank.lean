import ProximityPrize.SubmissionLower.KoalaScalarListDefs
import ProximityPrize.SubmissionLower.KoalaScalarListCells0
import ProximityPrize.SubmissionLower.KoalaScalarListCells1
import ProximityPrize.SubmissionLower.KoalaScalarListCells2
import ProximityPrize.SubmissionLower.KoalaScalarListCells3

-- merged module KoalaScalarListCells4
section Merged_KoalaScalarListCells4
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
private def witness_64_2 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc0aa,0x7efe9c39,0x7efacdb1,0x7eefd541],[0,0,0,0,1035,3915,11088,27864],[0,0,0x7effffd4,0x7effffab,0x7effff5d,0x7efffec9],[1]],
    [[0,0,0,0,0,0,0,0x7effc4b5,0x7efeb36d,0x7efb2661],[0,0,0,0,0,990,3740,10578],[0,0,0,0x7effffd5,0x7effffad,0x7effff61],[0,1]],
    [[0,0,0,0,0,0,0,0,0x7effc893,0x7efec999],[0,0,0,0,0,0,946,3569],[0,0,0,0,0x7effffd6,0x7effffaf],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0,0x7effcc45],[0,0,0,0,0,0,0,903],[0,0,0,0,0,0x7effffd7],[0,0,0,1]],
    [[0,0,0,0,0,0,0,0,0x7ef92df8,0x7ecdae25],[0,0,0,0,0,0,26488,148092],[0,0,0,0,0x7efffc7a,0x7efff2b7],[],[1]],
    [[0,0,0,0,0,0,0,0,0,0x7ef9c92c],[0,0,0,0,0,0,0,24682],[0,0,0,0,0,0x7efffca4],[],[0,1]]]
theorem improved_64_2 : (CJ0.blockMatrix source 64 ((2 : ℤ)-22)).rank ≤ 24 :=
  Fast.cell (z := witness_64_2) (Fast.bands [(42,42,1),(43,43,2),(44,44,3),(45,46,3),(46,48,3),(47,50,3),(48,52,3),(49,54,3),(50,56,3),(51,58,3),(52,60,3),(53,62,2),(54,64,1)]) (by decide +kernel) (by decide +kernel)

private def witness_64_3 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(4,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,148995],[0,0,0,0,0,0,0x7effcc45],[0,0,0,0,903],[0,0,0x7effffd7],[1]]]
theorem improved_64_3 : (CJ0.blockMatrix source 64 ((3 : ℤ)-22)).rank ≤ 24 :=
  Fast.cell (z := witness_64_3) (Fast.bands [(42,42,1),(43,43,2),(44,44,3),(45,45,4),(46,47,4),(47,49,4),(48,51,4),(49,53,4),(50,55,4),(51,57,4),(52,59,4),(53,61,3),(54,63,2)]) (by decide +kernel) (by decide +kernel)

private def witness_65_1 : CJ1.Block where
  bank := .rightLow
  cap := 18
  free := [(1,0),(2,0),(4,0),(6,0)]
  vectors := [
    [[],[1]],
    [[],[],[1]],
    [[],[],[],[0x7f000000],[1]],
    [[],[],[],[0x7f000000],[],[0x7f000000],[1]]]
theorem improved_65_1 : (CJ0.blockMatrix source 65 ((1 : ℤ)-22)).rank ≤ 18 :=
  Fast.cell (z := witness_65_1) (Fast.bands [(0,56,10),(1,57,8),(2,58,6),(3,59,4),(4,60,2)]) (by decide +kernel) (by decide +kernel)

private def witness_65_2 : CJ1.Block where
  bank := .leftLow
  cap := 21
  free := [(3,0),(3,1),(3,2),(4,0)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc0aa,0x7efe9c39,0x7efacdb1],[0,0,0,0,1035,3915,11088],[0,0,0x7effffd4,0x7effffab,0x7effff5d],[1]],
    [[0,0,0,0,0,0,0,0x7effc4b5,0x7efeb36d],[0,0,0,0,0,990,3740],[0,0,0,0x7effffd5,0x7effffad],[0,1]],
    [[0,0,0,0,0,0,0,0,0x7effc893],[0,0,0,0,0,0,946],[0,0,0,0,0x7effffd6],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0x7ef92df8],[0,0,0,0,0,0,26488],[0,0,0,0,0x7efffc7a],[],[1]]]
theorem improved_65_2 : (CJ0.blockMatrix source 65 ((2 : ℤ)-22)).rank ≤ 21 :=
  Fast.cell (z := witness_65_2) (Fast.bands [(43,43,1),(44,44,2),(45,45,3),(46,47,3),(47,49,3),(48,51,3),(49,53,3),(50,55,3),(51,57,3),(52,59,3),(53,61,3),(54,63,2),(55,65,1)]) (by decide +kernel) (by decide +kernel)

private def witness_66_0 : CJ1.Block where
  bank := .rightLow
  cap := 10
  free := [(2,0)]
  vectors := [
    [[],[],[1]]]
theorem improved_66_0 : (CJ0.blockMatrix source 66 ((0 : ℤ)-22)).rank ≤ 10 :=
  Fast.cell (z := witness_66_0) (Fast.bands [(0,57,10),(1,58,8),(2,59,6),(3,60,4),(4,61,2)]) (by decide +kernel) (by decide +kernel)

private def witness_66_1 : CJ1.Block where
  bank := .rightLow
  cap := 16
  free := [(1,0),(2,0),(3,0),(4,0),(6,0),(8,0)]
  vectors := [
    [[],[1]],
    [[],[],[1]],
    [[],[],[],[1]],
    [[],[],[],[],[1]],
    [[],[],[],[],[],[0x7f000000],[1]],
    [[],[],[],[],[],[0x7f000000],[],[0x7f000000],[1]]]
theorem improved_66_1 : (CJ0.blockMatrix source 66 ((1 : ℤ)-22)).rank ≤ 16 :=
  Fast.cell (z := witness_66_1) (Fast.bands [(0,58,9),(1,59,7),(2,60,5),(3,61,3),(4,62,1)]) (by decide +kernel) (by decide +kernel)

private def witness_66_2 : CJ1.Block where
  bank := .leftLow
  cap := 18
  free := [(3,0),(3,1)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc0aa,0x7efe9c39],[0,0,0,0,1035,3915],[0,0,0x7effffd4,0x7effffab],[1]],
    [[0,0,0,0,0,0,0,0x7effc4b5],[0,0,0,0,0,990],[0,0,0,0x7effffd5],[0,1]]]
theorem improved_66_2 : (CJ0.blockMatrix source 66 ((2 : ℤ)-22)).rank ≤ 18 :=
  Fast.cell (z := witness_66_2) (Fast.bands [(44,44,1),(45,45,2),(46,46,3),(47,48,3),(48,50,3),(49,52,3),(50,54,3),(51,56,3),(52,58,3),(53,60,3),(54,62,3),(55,64,2),(56,66,1)]) (by decide +kernel) (by decide +kernel)

private def witness_67_0 : CJ1.Block where
  bank := .rightLow
  cap := 9
  free := [(2,0),(4,0)]
  vectors := [
    [[],[],[1]],
    [[],[],[],[],[1]]]
theorem improved_67_0 : (CJ0.blockMatrix source 67 ((0 : ℤ)-22)).rank ≤ 9 :=
  Fast.cell (z := witness_67_0) (Fast.bands [(0,59,9),(1,60,7),(2,61,5),(3,62,3),(4,63,1)]) (by decide +kernel) (by decide +kernel)

private def witness_67_1 : CJ1.Block where
  bank := .leftLow
  cap := 14
  free := [(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)]
  vectors := [
    [[0,0,0,0,1176,4512,12972,33120],[0,0,0x7effffd1,0x7effffa4,0x7effff4d,0x7efffea5],[1]],
    [[0,0,0,0,0,1128,4324,12420],[0,0,0,0x7effffd2,0x7effffa6,0x7effff51],[0,1]],
    [[0,0,0,0,0,0,1081,4140],[0,0,0,0,0x7effffd3,0x7effffa8],[0,0,1]],
    [[0,0,0,0,0,0,0,1035],[0,0,0,0,0,0x7effffd4],[0,0,0,1]],
    [[0,0,0,0,0,0,32430,184230],[0,0,0,0,0x7efffbf6,0x7efff089],[],[1]],
    [[0,0,0,0,0,0,0,30360],[0,0,0,0,0,0x7efffc23],[],[0,1]]]
theorem improved_67_1 : (CJ0.blockMatrix source 67 ((1 : ℤ)-22)).rank ≤ 14 :=
  Fast.cell (z := witness_67_1) (Fast.bands [(45,45,1),(46,46,2),(47,48,2),(48,50,2),(49,52,2),(50,54,2),(51,56,2),(52,58,2),(53,60,2),(54,62,2),(55,64,2),(56,66,1)]) (by decide +kernel) (by decide +kernel)

private def witness_67_2 : CJ1.Block where
  bank := .leftLow
  cap := 15
  free := [(3,0)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc0aa],[0,0,0,0,1035],[0,0,0x7effffd4],[1]]]
theorem improved_67_2 : (CJ0.blockMatrix source 67 ((2 : ℤ)-22)).rank ≤ 15 :=
  Fast.cell (z := witness_67_2) (Fast.bands [(45,45,1),(46,46,2),(47,47,3),(48,49,3),(49,51,3),(50,53,3),(51,55,3),(52,57,3),(53,59,3),(54,61,3),(55,63,3),(56,65,2),(57,67,1)]) (by decide +kernel) (by decide +kernel)

private def witness_68_0 : CJ1.Block where
  bank := .rightLow
  cap := 8
  free := [(2,0),(4,0),(6,0)]
  vectors := [
    [[],[],[1]],
    [[],[],[],[],[1]],
    [[],[],[],[],[],[],[1]]]
theorem improved_68_0 : (CJ0.blockMatrix source 68 ((0 : ℤ)-22)).rank ≤ 8 :=
  Fast.cell (z := witness_68_0) (Fast.bands [(0,61,8),(1,62,6),(2,63,4),(3,64,2)]) (by decide +kernel) (by decide +kernel)

private def witness_68_1 : CJ1.Block where
  bank := .leftLow
  cap := 12
  free := [(2,0),(2,1),(2,2),(3,0)]
  vectors := [
    [[0,0,0,0,1176,4512,12972],[0,0,0x7effffd1,0x7effffa4,0x7effff4d],[1]],
    [[0,0,0,0,0,1128,4324],[0,0,0,0x7effffd2,0x7effffa6],[0,1]],
    [[0,0,0,0,0,0,1081],[0,0,0,0,0x7effffd3],[0,0,1]],
    [[0,0,0,0,0,0,32430],[0,0,0,0,0x7efffbf6],[],[1]]]
theorem improved_68_1 : (CJ0.blockMatrix source 68 ((1 : ℤ)-22)).rank ≤ 12 :=
  Fast.cell (z := witness_68_1) (Fast.bands [(46,46,1),(47,47,2),(48,49,2),(49,51,2),(50,53,2),(51,55,2),(52,57,2),(53,59,2),(54,61,2),(55,63,2),(56,65,2),(57,67,1)]) (by decide +kernel) (by decide +kernel)

end KoalaScalarListBank
end Merged_KoalaScalarListCells4

-- merged module KoalaScalarListCells5
section Merged_KoalaScalarListCells5
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
private def witness_69_0 : CJ1.Block where
  bank := .rightLow
  cap := 7
  free := [(2,0),(4,0),(6,0),(8,0)]
  vectors := [
    [[],[],[1]],
    [[],[],[],[],[1]],
    [[],[],[],[],[],[],[1]],
    [[],[],[],[],[],[],[],[],[1]]]
theorem improved_69_0 : (CJ0.blockMatrix source 69 ((0 : ℤ)-22)).rank ≤ 7 :=
  Fast.cell (z := witness_69_0) (Fast.bands [(0,63,7),(1,64,5),(2,65,3),(3,66,1)]) (by decide +kernel) (by decide +kernel)

private def witness_69_1 : CJ1.Block where
  bank := .leftLow
  cap := 10
  free := [(2,0),(2,1)]
  vectors := [
    [[0,0,0,0,1176,4512],[0,0,0x7effffd1,0x7effffa4],[1]],
    [[0,0,0,0,0,1128],[0,0,0,0x7effffd2],[0,1]]]
theorem improved_69_1 : (CJ0.blockMatrix source 69 ((1 : ℤ)-22)).rank ≤ 10 :=
  Fast.cell (z := witness_69_1) (Fast.bands [(47,47,1),(48,48,2),(49,50,2),(50,52,2),(51,54,2),(52,56,2),(53,58,2),(54,60,2),(55,62,2),(56,64,2),(57,66,2),(58,68,1)]) (by decide +kernel) (by decide +kernel)

private def witness_70_0 : CJ1.Block where
  bank := .rightLow
  cap := 6
  free := [(2,0),(4,0),(6,0),(8,0),(10,0)]
  vectors := [
    [[],[],[1]],
    [[],[],[],[],[1]],
    [[],[],[],[],[],[],[1]],
    [[],[],[],[],[],[],[],[],[1]],
    [[],[],[],[],[],[],[],[],[],[],[1]]]
theorem improved_70_0 : (CJ0.blockMatrix source 70 ((0 : ℤ)-22)).rank ≤ 6 :=
  Fast.cell (z := witness_70_0) (Fast.bands [(0,65,6),(1,66,4),(2,67,2)]) (by decide +kernel) (by decide +kernel)

private def witness_70_1 : CJ1.Block where
  bank := .leftLow
  cap := 8
  free := [(2,0)]
  vectors := [
    [[0,0,0,0,1176],[0,0,0x7effffd1],[1]]]
theorem improved_70_1 : (CJ0.blockMatrix source 70 ((1 : ℤ)-22)).rank ≤ 8 :=
  Fast.cell (z := witness_70_1) (Fast.bands [(48,48,1),(49,49,2),(50,51,2),(51,53,2),(52,55,2),(53,57,2),(54,59,2),(55,61,2),(56,63,2),(57,65,2),(58,67,2),(59,69,1)]) (by decide +kernel) (by decide +kernel)

private def witness_71_0 : CJ1.Block where
  bank := .leftLow
  cap := 5
  free := [(1,0),(1,1),(1,2),(2,0)]
  vectors := [
    [[0,0,0x7effffce,0x7effff9d,0x7effff3d],[1]],
    [[0,0,0,0x7effffcf,0x7effff9f],[0,1]],
    [[0,0,0,0,0x7effffd0],[0,0,1]],
    [[0,0,0,0,0x7efffb69],[],[1]]]
theorem improved_71_0 : (CJ0.blockMatrix source 71 ((0 : ℤ)-22)).rank ≤ 5 :=
  Fast.cell (z := witness_71_0) (Fast.bands [(49,49,1),(50,51,1),(51,53,1),(52,55,1),(53,57,1),(54,59,1),(55,61,1),(56,63,1),(57,65,1),(58,67,1),(59,69,1)]) (by decide +kernel) (by decide +kernel)

private def witness_72_0 : CJ1.Block where
  bank := .leftLow
  cap := 4
  free := [(1,0),(1,1)]
  vectors := [
    [[0,0,0x7effffce,0x7effff9d],[1]],
    [[0,0,0,0x7effffcf],[0,1]]]
theorem improved_72_0 : (CJ0.blockMatrix source 72 ((0 : ℤ)-22)).rank ≤ 4 :=
  Fast.cell (z := witness_72_0) (Fast.bands [(50,50,1),(51,52,1),(52,54,1),(53,56,1),(54,58,1),(55,60,1),(56,62,1),(57,64,1),(58,66,1),(59,68,1),(60,70,1)]) (by decide +kernel) (by decide +kernel)

private def witness_73_0 : CJ1.Block where
  bank := .leftLow
  cap := 3
  free := [(1,0)]
  vectors := [
    [[0,0,0x7effffce],[1]]]
theorem improved_73_0 : (CJ0.blockMatrix source 73 ((0 : ℤ)-22)).rank ≤ 3 :=
  Fast.cell (z := witness_73_0) (Fast.bands [(51,51,1),(52,53,1),(53,55,1),(54,57,1),(55,59,1),(56,61,1),(57,63,1),(58,65,1),(59,67,1),(60,69,1),(61,71,1)]) (by decide +kernel) (by decide +kernel)

end KoalaScalarListBank
end Merged_KoalaScalarListCells5

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
open scoped BigOperators
open CJ1 (total total_eq_sum)

private def allowance_37 : ℕ → ℕ
  | 17 => 128
  | u => nominal 37 u

private theorem bound_37 (u : ℕ) :
    (CJ0.blockMatrix source 37 ((u : ℤ)-22)).rank ≤ allowance_37 u := by
  unfold allowance_37
  split
  · exact improved_37_17
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_38 : ℕ → ℕ
  | 16 => 126
  | 17 => 120
  | u => nominal 38 u

private theorem bound_38 (u : ℕ) :
    (CJ0.blockMatrix source 38 ((u : ℤ)-22)).rank ≤ allowance_38 u := by
  unfold allowance_38
  split
  · exact improved_38_16
  · exact improved_38_17
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_39 : ℕ → ℕ
  | 15 => 123
  | 16 => 119
  | u => nominal 39 u

private theorem bound_39 (u : ℕ) :
    (CJ0.blockMatrix source 39 ((u : ℤ)-22)).rank ≤ allowance_39 u := by
  unfold allowance_39
  split
  · exact improved_39_15
  · exact improved_39_16
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_40 : ℕ → ℕ
  | 14 => 120
  | 15 => 117
  | u => nominal 40 u

private theorem bound_40 (u : ℕ) :
    (CJ0.blockMatrix source 40 ((u : ℤ)-22)).rank ≤ allowance_40 u := by
  unfold allowance_40
  split
  · exact improved_40_14
  · exact improved_40_15
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_41 : ℕ → ℕ
  | 13 => 116
  | 14 => 115
  | 15 => 109
  | u => nominal 41 u

private theorem bound_41 (u : ℕ) :
    (CJ0.blockMatrix source 41 ((u : ℤ)-22)).rank ≤ allowance_41 u := by
  unfold allowance_41
  split
  · exact improved_41_13
  · exact improved_41_14
  · exact improved_41_15
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_42 : ℕ → ℕ
  | 12 => 112
  | 13 => 112
  | 14 => 108
  | u => nominal 42 u

private theorem bound_42 (u : ℕ) :
    (CJ0.blockMatrix source 42 ((u : ℤ)-22)).rank ≤ allowance_42 u := by
  unfold allowance_42
  split
  · exact improved_42_12
  · exact improved_42_13
  · exact improved_42_14
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_43 : ℕ → ℕ
  | 12 => 109
  | 13 => 106
  | u => nominal 43 u

private theorem bound_43 (u : ℕ) :
    (CJ0.blockMatrix source 43 ((u : ℤ)-22)).rank ≤ allowance_43 u := by
  unfold allowance_43
  split
  · exact improved_43_12
  · exact improved_43_13
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_44 : ℕ → ℕ
  | 11 => 105
  | 12 => 104
  | 13 => 99
  | u => nominal 44 u

private theorem bound_44 (u : ℕ) :
    (CJ0.blockMatrix source 44 ((u : ℤ)-22)).rank ≤ allowance_44 u := by
  unfold allowance_44
  split
  · exact improved_44_11
  · exact improved_44_12
  · exact improved_44_13
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_45 : ℕ → ℕ
  | 11 => 101
  | 12 => 98
  | u => nominal 45 u

private theorem bound_45 (u : ℕ) :
    (CJ0.blockMatrix source 45 ((u : ℤ)-22)).rank ≤ allowance_45 u := by
  unfold allowance_45
  split
  · exact improved_45_11
  · exact improved_45_12
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_46 : ℕ → ℕ
  | 10 => 98
  | 11 => 96
  | u => nominal 46 u

private theorem bound_46 (u : ℕ) :
    (CJ0.blockMatrix source 46 ((u : ℤ)-22)).rank ≤ allowance_46 u := by
  unfold allowance_46
  split
  · exact improved_46_10
  · exact improved_46_11
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_47 : ℕ → ℕ
  | 10 => 94
  | 11 => 89
  | u => nominal 47 u

private theorem bound_47 (u : ℕ) :
    (CJ0.blockMatrix source 47 ((u : ℤ)-22)).rank ≤ allowance_47 u := by
  unfold allowance_47
  split
  · exact improved_47_10
  · exact improved_47_11
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_48 : ℕ → ℕ
  | 9 => 91
  | 10 => 88
  | u => nominal 48 u

private theorem bound_48 (u : ℕ) :
    (CJ0.blockMatrix source 48 ((u : ℤ)-22)).rank ≤ allowance_48 u := by
  unfold allowance_48
  split
  · exact improved_48_9
  · exact improved_48_10
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_49 : ℕ → ℕ
  | 9 => 86
  | u => nominal 49 u

private theorem bound_49 (u : ℕ) :
    (CJ0.blockMatrix source 49 ((u : ℤ)-22)).rank ≤ allowance_49 u := by
  unfold allowance_49
  split
  · exact improved_49_9
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_50 : ℕ → ℕ
  | 8 => 84
  | 9 => 80
  | u => nominal 50 u

private theorem bound_50 (u : ℕ) :
    (CJ0.blockMatrix source 50 ((u : ℤ)-22)).rank ≤ allowance_50 u := by
  unfold allowance_50
  split
  · exact improved_50_8
  · exact improved_50_9
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_51 : ℕ → ℕ
  | 8 => 79
  | u => nominal 51 u

private theorem bound_51 (u : ℕ) :
    (CJ0.blockMatrix source 51 ((u : ℤ)-22)).rank ≤ allowance_51 u := by
  unfold allowance_51
  split
  · exact improved_51_8
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_52 : ℕ → ℕ
  | 7 => 76
  | u => nominal 52 u

private theorem bound_52 (u : ℕ) :
    (CJ0.blockMatrix source 52 ((u : ℤ)-22)).rank ≤ allowance_52 u := by
  unfold allowance_52
  split
  · exact improved_52_7
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_53 : ℕ → ℕ
  | 7 => 71
  | u => nominal 53 u

private theorem bound_53 (u : ℕ) :
    (CJ0.blockMatrix source 53 ((u : ℤ)-22)).rank ≤ allowance_53 u := by
  unfold allowance_53
  split
  · exact improved_53_7
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_54 : ℕ → ℕ
  | 6 => 68
  | u => nominal 54 u

private theorem bound_54 (u : ℕ) :
    (CJ0.blockMatrix source 54 ((u : ℤ)-22)).rank ≤ allowance_54 u := by
  unfold allowance_54
  split
  · exact improved_54_6
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_55 : ℕ → ℕ
  | 6 => 63
  | u => nominal 55 u

private theorem bound_55 (u : ℕ) :
    (CJ0.blockMatrix source 55 ((u : ℤ)-22)).rank ≤ allowance_55 u := by
  unfold allowance_55
  split
  · exact improved_55_6
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_56 : ℕ → ℕ
  | 5 => 59
  | u => nominal 56 u

private theorem bound_56 (u : ℕ) :
    (CJ0.blockMatrix source 56 ((u : ℤ)-22)).rank ≤ allowance_56 u := by
  unfold allowance_56
  split
  · exact improved_56_5
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_57 : ℕ → ℕ
  | 5 => 54
  | u => nominal 57 u

private theorem bound_57 (u : ℕ) :
    (CJ0.blockMatrix source 57 ((u : ℤ)-22)).rank ≤ allowance_57 u := by
  unfold allowance_57
  split
  · exact improved_57_5
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_58 : ℕ → ℕ
  | 4 => 50
  | 5 => 48
  | u => nominal 58 u

private theorem bound_58 (u : ℕ) :
    (CJ0.blockMatrix source 58 ((u : ℤ)-22)).rank ≤ allowance_58 u := by
  unfold allowance_58
  split
  · exact improved_58_4
  · exact improved_58_5
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_59 : ℕ → ℕ
  | 4 => 45
  | u => nominal 59 u

private theorem bound_59 (u : ℕ) :
    (CJ0.blockMatrix source 59 ((u : ℤ)-22)).rank ≤ allowance_59 u := by
  unfold allowance_59
  split
  · exact improved_59_4
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_60 : ℕ → ℕ
  | 3 => 40
  | 4 => 40
  | u => nominal 60 u

private theorem bound_60 (u : ℕ) :
    (CJ0.blockMatrix source 60 ((u : ℤ)-22)).rank ≤ allowance_60 u := by
  unfold allowance_60
  split
  · exact improved_60_3
  · exact improved_60_4
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_61 : ℕ → ℕ
  | 3 => 36
  | 4 => 35
  | u => nominal 61 u

private theorem bound_61 (u : ℕ) :
    (CJ0.blockMatrix source 61 ((u : ℤ)-22)).rank ≤ allowance_61 u := by
  unfold allowance_61
  split
  · exact improved_61_3
  · exact improved_61_4
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_62 : ℕ → ℕ
  | 2 => 30
  | 3 => 32
  | u => nominal 62 u

private theorem bound_62 (u : ℕ) :
    (CJ0.blockMatrix source 62 ((u : ℤ)-22)).rank ≤ allowance_62 u := by
  unfold allowance_62
  split
  · exact improved_62_2
  · exact improved_62_3
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_63 : ℕ → ℕ
  | 2 => 27
  | 3 => 28
  | u => nominal 63 u

private theorem bound_63 (u : ℕ) :
    (CJ0.blockMatrix source 63 ((u : ℤ)-22)).rank ≤ allowance_63 u := by
  unfold allowance_63
  split
  · exact improved_63_2
  · exact improved_63_3
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_64 : ℕ → ℕ
  | 1 => 20
  | 2 => 24
  | 3 => 24
  | u => nominal 64 u

private theorem bound_64 (u : ℕ) :
    (CJ0.blockMatrix source 64 ((u : ℤ)-22)).rank ≤ allowance_64 u := by
  unfold allowance_64
  split
  · exact improved_64_1
  · exact improved_64_2
  · exact improved_64_3
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_65 : ℕ → ℕ
  | 1 => 18
  | 2 => 21
  | u => nominal 65 u

private theorem bound_65 (u : ℕ) :
    (CJ0.blockMatrix source 65 ((u : ℤ)-22)).rank ≤ allowance_65 u := by
  unfold allowance_65
  split
  · exact improved_65_1
  · exact improved_65_2
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_66 : ℕ → ℕ
  | 0 => 10
  | 1 => 16
  | 2 => 18
  | u => nominal 66 u

private theorem bound_66 (u : ℕ) :
    (CJ0.blockMatrix source 66 ((u : ℤ)-22)).rank ≤ allowance_66 u := by
  unfold allowance_66
  split
  · exact improved_66_0
  · exact improved_66_1
  · exact improved_66_2
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_67 : ℕ → ℕ
  | 0 => 9
  | 1 => 14
  | 2 => 15
  | u => nominal 67 u

private theorem bound_67 (u : ℕ) :
    (CJ0.blockMatrix source 67 ((u : ℤ)-22)).rank ≤ allowance_67 u := by
  unfold allowance_67
  split
  · exact improved_67_0
  · exact improved_67_1
  · exact improved_67_2
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_68 : ℕ → ℕ
  | 0 => 8
  | 1 => 12
  | u => nominal 68 u

private theorem bound_68 (u : ℕ) :
    (CJ0.blockMatrix source 68 ((u : ℤ)-22)).rank ≤ allowance_68 u := by
  unfold allowance_68
  split
  · exact improved_68_0
  · exact improved_68_1
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_69 : ℕ → ℕ
  | 0 => 7
  | 1 => 10
  | u => nominal 69 u

private theorem bound_69 (u : ℕ) :
    (CJ0.blockMatrix source 69 ((u : ℤ)-22)).rank ≤ allowance_69 u := by
  unfold allowance_69
  split
  · exact improved_69_0
  · exact improved_69_1
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_70 : ℕ → ℕ
  | 0 => 6
  | 1 => 8
  | u => nominal 70 u

private theorem bound_70 (u : ℕ) :
    (CJ0.blockMatrix source 70 ((u : ℤ)-22)).rank ≤ allowance_70 u := by
  unfold allowance_70
  split
  · exact improved_70_0
  · exact improved_70_1
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_71 : ℕ → ℕ
  | 0 => 5
  | u => nominal 71 u

private theorem bound_71 (u : ℕ) :
    (CJ0.blockMatrix source 71 ((u : ℤ)-22)).rank ≤ allowance_71 u := by
  unfold allowance_71
  split
  · exact improved_71_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_72 : ℕ → ℕ
  | 0 => 4
  | u => nominal 72 u

private theorem bound_72 (u : ℕ) :
    (CJ0.blockMatrix source 72 ((u : ℤ)-22)).rank ≤ allowance_72 u := by
  unfold allowance_72
  split
  · exact improved_72_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_73 : ℕ → ℕ
  | 0 => 3
  | u => nominal 73 u

private theorem bound_73 (u : ℕ) :
    (CJ0.blockMatrix source 73 ((u : ℤ)-22)).rank ≤ allowance_73 u := by
  unfold allowance_73
  split
  · exact improved_73_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance : ℕ → ℕ → ℕ
  | 37, u => allowance_37 u
  | 38, u => allowance_38 u
  | 39, u => allowance_39 u
  | 40, u => allowance_40 u
  | 41, u => allowance_41 u
  | 42, u => allowance_42 u
  | 43, u => allowance_43 u
  | 44, u => allowance_44 u
  | 45, u => allowance_45 u
  | 46, u => allowance_46 u
  | 47, u => allowance_47 u
  | 48, u => allowance_48 u
  | 49, u => allowance_49 u
  | 50, u => allowance_50 u
  | 51, u => allowance_51 u
  | 52, u => allowance_52 u
  | 53, u => allowance_53 u
  | 54, u => allowance_54 u
  | 55, u => allowance_55 u
  | 56, u => allowance_56 u
  | 57, u => allowance_57 u
  | 58, u => allowance_58 u
  | 59, u => allowance_59 u
  | 60, u => allowance_60 u
  | 61, u => allowance_61 u
  | 62, u => allowance_62 u
  | 63, u => allowance_63 u
  | 64, u => allowance_64 u
  | 65, u => allowance_65 u
  | 66, u => allowance_66 u
  | 67, u => allowance_67 u
  | 68, u => allowance_68 u
  | 69, u => allowance_69 u
  | 70, u => allowance_70 u
  | 71, u => allowance_71 u
  | 72, u => allowance_72 u
  | 73, u => allowance_73 u
  | q, u => nominal q u

private theorem bound (q u : ℕ) :
    (CJ0.blockMatrix source q ((u : ℤ)-22)).rank ≤ allowance q u := by
  unfold allowance
  split
  · exact bound_37 _
  · exact bound_38 _
  · exact bound_39 _
  · exact bound_40 _
  · exact bound_41 _
  · exact bound_42 _
  · exact bound_43 _
  · exact bound_44 _
  · exact bound_45 _
  · exact bound_46 _
  · exact bound_47 _
  · exact bound_48 _
  · exact bound_49 _
  · exact bound_50 _
  · exact bound_51 _
  · exact bound_52 _
  · exact bound_53 _
  · exact bound_54 _
  · exact bound_55 _
  · exact bound_56 _
  · exact bound_57 _
  · exact bound_58 _
  · exact bound_59 _
  · exact bound_60 _
  · exact bound_61 _
  · exact bound_62 _
  · exact bound_63 _
  · exact bound_64 _
  · exact bound_65 _
  · exact bound_66 _
  · exact bound_67 _
  · exact bound_68 _
  · exact bound_69 _
  · exact bound_70 _
  · exact bound_71 _
  · exact bound_72 _
  · exact bound_73 _
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def grade (q : ℕ) := total (allowance q) (76-q)
private def gradeTable : Fin 75 → ℕ := ![54,159,312,510,750,1029,1344,1692,2070,2475,2904,3311,3696,4018,4280,4485,4636,4736,4788,4795,4760,4686,4576,4433,4290,4147,4004,3861,3718,3575,3432,3289,3146,3004,2863,2724,2587,2449,2315,2184,2056,1931,1810,1693,1579,1470,1364,1263,1165,1072,982,897,815,738,664,595,529,468,410,357,307,262,220,183,149,120,94,72,54,39,27,18,11,6,3]
private theorem grade_0 : grade 0 = 54 := by decide +kernel
private theorem grade_1 : grade 1 = 159 := by decide +kernel
private theorem grade_2 : grade 2 = 312 := by decide +kernel
private theorem grade_3 : grade 3 = 510 := by decide +kernel
private theorem grade_4 : grade 4 = 750 := by decide +kernel
private theorem grade_5 : grade 5 = 1029 := by decide +kernel
private theorem grade_6 : grade 6 = 1344 := by decide +kernel
private theorem grade_7 : grade 7 = 1692 := by decide +kernel
private theorem grade_8 : grade 8 = 2070 := by decide +kernel
private theorem grade_9 : grade 9 = 2475 := by decide +kernel
private theorem grade_10 : grade 10 = 2904 := by decide +kernel
private theorem grade_11 : grade 11 = 3311 := by decide +kernel
private theorem grade_12 : grade 12 = 3696 := by decide +kernel
private theorem grade_13 : grade 13 = 4018 := by decide +kernel
private theorem grade_14 : grade 14 = 4280 := by decide +kernel
private theorem grade_15 : grade 15 = 4485 := by decide +kernel
private theorem grade_16 : grade 16 = 4636 := by decide +kernel
private theorem grade_17 : grade 17 = 4736 := by decide +kernel
private theorem grade_18 : grade 18 = 4788 := by decide +kernel
private theorem grade_19 : grade 19 = 4795 := by decide +kernel
private theorem grade_20 : grade 20 = 4760 := by decide +kernel
private theorem grade_21 : grade 21 = 4686 := by decide +kernel
private theorem grade_22 : grade 22 = 4576 := by decide +kernel
private theorem grade_23 : grade 23 = 4433 := by decide +kernel
private theorem grade_24 : grade 24 = 4290 := by decide +kernel
private theorem grade_25 : grade 25 = 4147 := by decide +kernel
private theorem grade_26 : grade 26 = 4004 := by decide +kernel
private theorem grade_27 : grade 27 = 3861 := by decide +kernel
private theorem grade_28 : grade 28 = 3718 := by decide +kernel
private theorem grade_29 : grade 29 = 3575 := by decide +kernel
private theorem grade_30 : grade 30 = 3432 := by decide +kernel
private theorem grade_31 : grade 31 = 3289 := by decide +kernel
private theorem grade_32 : grade 32 = 3146 := by decide +kernel
private theorem grade_33 : grade 33 = 3004 := by decide +kernel
private theorem grade_34 : grade 34 = 2863 := by decide +kernel
private theorem grade_35 : grade 35 = 2724 := by decide +kernel
private theorem grade_36 : grade 36 = 2587 := by decide +kernel
private theorem grade_37 : grade 37 = 2449 := by decide +kernel
private theorem grade_38 : grade 38 = 2315 := by decide +kernel
private theorem grade_39 : grade 39 = 2184 := by decide +kernel
private theorem grade_40 : grade 40 = 2056 := by decide +kernel
private theorem grade_41 : grade 41 = 1931 := by decide +kernel
private theorem grade_42 : grade 42 = 1810 := by decide +kernel
private theorem grade_43 : grade 43 = 1693 := by decide +kernel
private theorem grade_44 : grade 44 = 1579 := by decide +kernel
private theorem grade_45 : grade 45 = 1470 := by decide +kernel
private theorem grade_46 : grade 46 = 1364 := by decide +kernel
private theorem grade_47 : grade 47 = 1263 := by decide +kernel
private theorem grade_48 : grade 48 = 1165 := by decide +kernel
private theorem grade_49 : grade 49 = 1072 := by decide +kernel
private theorem grade_50 : grade 50 = 982 := by decide +kernel
private theorem grade_51 : grade 51 = 897 := by decide +kernel
private theorem grade_52 : grade 52 = 815 := by decide +kernel
private theorem grade_53 : grade 53 = 738 := by decide +kernel
private theorem grade_54 : grade 54 = 664 := by decide +kernel
private theorem grade_55 : grade 55 = 595 := by decide +kernel
private theorem grade_56 : grade 56 = 529 := by decide +kernel
private theorem grade_57 : grade 57 = 468 := by decide +kernel
private theorem grade_58 : grade 58 = 410 := by decide +kernel
private theorem grade_59 : grade 59 = 357 := by decide +kernel
private theorem grade_60 : grade 60 = 307 := by decide +kernel
private theorem grade_61 : grade 61 = 262 := by decide +kernel
private theorem grade_62 : grade 62 = 220 := by decide +kernel
private theorem grade_63 : grade 63 = 183 := by decide +kernel
private theorem grade_64 : grade 64 = 149 := by decide +kernel
private theorem grade_65 : grade 65 = 120 := by decide +kernel
private theorem grade_66 : grade 66 = 94 := by decide +kernel
private theorem grade_67 : grade 67 = 72 := by decide +kernel
private theorem grade_68 : grade 68 = 54 := by decide +kernel
private theorem grade_69 : grade 69 = 39 := by decide +kernel
private theorem grade_70 : grade 70 = 27 := by decide +kernel
private theorem grade_71 : grade 71 = 18 := by decide +kernel
private theorem grade_72 : grade 72 = 11 := by decide +kernel
private theorem grade_73 : grade 73 = 6 := by decide +kernel
private theorem grade_74 : grade 74 = 3 := by decide +kernel

private theorem grade_table (q : Fin 75) : grade q.val = gradeTable q := by
  fin_cases q
  · exact grade_0
  · exact grade_1
  · exact grade_2
  · exact grade_3
  · exact grade_4
  · exact grade_5
  · exact grade_6
  · exact grade_7
  · exact grade_8
  · exact grade_9
  · exact grade_10
  · exact grade_11
  · exact grade_12
  · exact grade_13
  · exact grade_14
  · exact grade_15
  · exact grade_16
  · exact grade_17
  · exact grade_18
  · exact grade_19
  · exact grade_20
  · exact grade_21
  · exact grade_22
  · exact grade_23
  · exact grade_24
  · exact grade_25
  · exact grade_26
  · exact grade_27
  · exact grade_28
  · exact grade_29
  · exact grade_30
  · exact grade_31
  · exact grade_32
  · exact grade_33
  · exact grade_34
  · exact grade_35
  · exact grade_36
  · exact grade_37
  · exact grade_38
  · exact grade_39
  · exact grade_40
  · exact grade_41
  · exact grade_42
  · exact grade_43
  · exact grade_44
  · exact grade_45
  · exact grade_46
  · exact grade_47
  · exact grade_48
  · exact grade_49
  · exact grade_50
  · exact grade_51
  · exact grade_52
  · exact grade_53
  · exact grade_54
  · exact grade_55
  · exact grade_56
  · exact grade_57
  · exact grade_58
  · exact grade_59
  · exact grade_60
  · exact grade_61
  · exact grade_62
  · exact grade_63
  · exact grade_64
  · exact grade_65
  · exact grade_66
  · exact grade_67
  · exact grade_68
  · exact grade_69
  · exact grade_70
  · exact grade_71
  · exact grade_72
  · exact grade_73
  · exact grade_74

theorem prefix_bound : CJ0.prefixRank source 75 ≤ 145510 := by
  change (∑ q ∈ Finset.range 75, ∑ u ∈ Finset.range (76-q),
    (CJ0.blockMatrix source q ((u : ℤ)-22)).rank) ≤ _
  calc
    _ ≤ ∑ q ∈ Finset.range 75, ∑ u ∈ Finset.range (76-q), allowance q u :=
      Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun u _ => bound q u
    _ = ∑ q : Fin 75, grade q.val := by
      rw [Fin.sum_univ_eq_sum_range]
      simp only [grade, total_eq_sum]
    _ = ∑ q : Fin 75, gradeTable q := Finset.sum_congr rfl fun q _ => grade_table q
    _ = 145510 := by decide +kernel

end KoalaScalarListBank
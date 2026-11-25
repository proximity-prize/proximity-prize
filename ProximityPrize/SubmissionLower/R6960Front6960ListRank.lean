import ProximityPrize.SubmissionLower.R6960Front6960ListCells0
import ProximityPrize.SubmissionLower.R6960Front6960ListCells1
import ProximityPrize.SubmissionLower.R6960Front6960ListCells2
import ProximityPrize.SubmissionLower.R6960Front6960ListCells3
import ProximityPrize.SubmissionLower.R6960Front6960ListCells4
import ProximityPrize.SubmissionLower.R6960Front6960ListCells5
import ProximityPrize.SubmissionLower.R6960Front6960ListCells6

set_option Elab.async false

-- merged module R6960Front6960ListCells7
section Merged_R6960Front6960ListCells7

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def matrix_70_1 : CJ1.Block where
  bank := .rightLow
  cap := 18
  free := [(3, 0), (4, 0), (6, 0), (8, 0)]
  vectors := [
    [[], [], [], [1]],
    [[], [], [], [], [1]],
    [[], [], [], [], [], [2130706432], [1]],
    [[], [], [], [], [], [2130706432], [], [2130706432], [1]]
  ]
private theorem cell_70_1 : (CJ0.blockMatrix source 70 ((1 : ℤ)-24)).rank ≤ 18 :=
  Fast.cell (z := matrix_70_1) (Fast.bands [(0, 61, 10), (1, 62, 8), (2, 63, 6), (3, 64, 4), (4, 65, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_70_2 : CJ1.Block where
  bank := .leftLow
  cap := 21
  free := [(3, 0), (3, 1), (3, 2), (4, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130686833, 2130595889, 2130291329], [0, 0, 0, 0, 1176, 4464, 12690], [0, 0, 2130706385, 2130706341, 2130706257], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 2130688009, 2130602657], [0, 0, 0, 0, 0, 1128, 4277], [0, 0, 0, 2130706386, 2130706343], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130689137], [0, 0, 0, 0, 0, 0, 1081], [0, 0, 0, 0, 2130706387], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130122693], [0, 0, 0, 0, 0, 0, 32430], [0, 0, 0, 0, 2130705398], [], [1]]
  ]
private theorem cell_70_2 : (CJ0.blockMatrix source 70 ((2 : ℤ)-24)).rank ≤ 21 :=
  Fast.cell (z := matrix_70_2) (Fast.bands [(46, 46, 1), (47, 47, 2), (48, 48, 3), (49, 50, 3), (50, 52, 3), (51, 54, 3), (52, 56, 3), (53, 58, 3), (54, 60, 3), (55, 62, 3), (56, 64, 3), (57, 66, 2), (58, 68, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_70 (u : ℕ) : ℕ :=
  match u with
  | 1 => 18
  | 2 => 21
  | u => nominal 70 u

private theorem bound_70 (u : ℕ) :
    (CJ0.blockMatrix source 70 ((u : ℤ)-24)).rank ≤ allowance_70 u := by
  unfold allowance_70
  split
  · exact cell_70_1
  · exact cell_70_2
  · exact (block_rank_le 70 _).trans (rank_le_nominal 70 _)

theorem grade_70 : (∑ u ∈ Finset.range (81-70), (CJ0.blockMatrix source 70 ((u : ℤ)-24)).rank) ≤ 120 := by
  refine (Finset.sum_le_sum fun u _ => bound_70 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_70)]
  decide +kernel

private def matrix_71_0 : CJ1.Block where
  bank := .rightLow
  cap := 10
  free := [(4, 0)]
  vectors := [
    [[], [], [], [], [1]]
  ]
private theorem cell_71_0 : (CJ0.blockMatrix source 71 ((0 : ℤ)-24)).rank ≤ 10 :=
  Fast.cell (z := matrix_71_0) (Fast.bands [(0, 62, 10), (1, 63, 8), (2, 64, 6), (3, 65, 4), (4, 66, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_71_1 : CJ1.Block where
  bank := .rightLow
  cap := 16
  free := [(3, 0), (4, 0), (5, 0), (6, 0), (8, 0), (10, 0)]
  vectors := [
    [[], [], [], [1]],
    [[], [], [], [], [1]],
    [[], [], [], [], [], [1]],
    [[], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [2130706432], [1]],
    [[], [], [], [], [], [], [], [2130706432], [], [2130706432], [1]]
  ]
private theorem cell_71_1 : (CJ0.blockMatrix source 71 ((1 : ℤ)-24)).rank ≤ 16 :=
  Fast.cell (z := matrix_71_1) (Fast.bands [(0, 63, 9), (1, 64, 7), (2, 65, 5), (3, 66, 3), (4, 67, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_71_2 : CJ1.Block where
  bank := .leftLow
  cap := 18
  free := [(3, 0), (3, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130686833, 2130595889], [0, 0, 0, 0, 1176, 4464], [0, 0, 2130706385, 2130706341], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 2130688009], [0, 0, 0, 0, 0, 1128], [0, 0, 0, 2130706386], [0, 1]]
  ]
private theorem cell_71_2 : (CJ0.blockMatrix source 71 ((2 : ℤ)-24)).rank ≤ 18 :=
  Fast.cell (z := matrix_71_2) (Fast.bands [(47, 47, 1), (48, 48, 2), (49, 49, 3), (50, 51, 3), (51, 53, 3), (52, 55, 3), (53, 57, 3), (54, 59, 3), (55, 61, 3), (56, 63, 3), (57, 65, 3), (58, 67, 2), (59, 69, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_71 (u : ℕ) : ℕ :=
  match u with
  | 0 => 10
  | 1 => 16
  | 2 => 18
  | u => nominal 71 u

private theorem bound_71 (u : ℕ) :
    (CJ0.blockMatrix source 71 ((u : ℤ)-24)).rank ≤ allowance_71 u := by
  unfold allowance_71
  split
  · exact cell_71_0
  · exact cell_71_1
  · exact cell_71_2
  · exact (block_rank_le 71 _).trans (rank_le_nominal 71 _)

theorem grade_71 : (∑ u ∈ Finset.range (81-71), (CJ0.blockMatrix source 71 ((u : ℤ)-24)).rank) ≤ 94 := by
  refine (Finset.sum_le_sum fun u _ => bound_71 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_71)]
  decide +kernel

private def matrix_72_0 : CJ1.Block where
  bank := .rightLow
  cap := 9
  free := [(4, 0), (6, 0)]
  vectors := [
    [[], [], [], [], [1]],
    [[], [], [], [], [], [], [1]]
  ]
private theorem cell_72_0 : (CJ0.blockMatrix source 72 ((0 : ℤ)-24)).rank ≤ 9 :=
  Fast.cell (z := matrix_72_0) (Fast.bands [(0, 64, 9), (1, 65, 7), (2, 66, 5), (3, 67, 3), (4, 68, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_72_1 : CJ1.Block where
  bank := .leftLow
  cap := 14
  free := [(2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1)]
  vectors := [
    [[0, 0, 0, 0, 1326, 5100, 14700, 37632], [0, 0, 2130706382, 2130706334, 2130706241, 2130706061], [1]],
    [[0, 0, 0, 0, 0, 1275, 4900, 14112], [0, 0, 0, 2130706383, 2130706336, 2130706245], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 1225, 4704], [0, 0, 0, 0, 2130706384, 2130706338], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 1176], [0, 0, 0, 0, 0, 2130706385], [0, 0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 39200, 223440], [0, 0, 0, 0, 2130705257, 2130701921], [], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 36848], [0, 0, 0, 0, 0, 2130705305], [], [0, 1]]
  ]
private theorem cell_72_1 : (CJ0.blockMatrix source 72 ((1 : ℤ)-24)).rank ≤ 14 :=
  Fast.cell (z := matrix_72_1) (Fast.bands [(48, 48, 1), (49, 49, 2), (50, 51, 2), (51, 53, 2), (52, 55, 2), (53, 57, 2), (54, 59, 2), (55, 61, 2), (56, 63, 2), (57, 65, 2), (58, 67, 2), (59, 69, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_72_2 : CJ1.Block where
  bank := .leftLow
  cap := 15
  free := [(3, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130686833], [0, 0, 0, 0, 1176], [0, 0, 2130706385], [1]]
  ]
private theorem cell_72_2 : (CJ0.blockMatrix source 72 ((2 : ℤ)-24)).rank ≤ 15 :=
  Fast.cell (z := matrix_72_2) (Fast.bands [(48, 48, 1), (49, 49, 2), (50, 50, 3), (51, 52, 3), (52, 54, 3), (53, 56, 3), (54, 58, 3), (55, 60, 3), (56, 62, 3), (57, 64, 3), (58, 66, 3), (59, 68, 2), (60, 70, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_72 (u : ℕ) : ℕ :=
  match u with
  | 0 => 9
  | 1 => 14
  | 2 => 15
  | u => nominal 72 u

private theorem bound_72 (u : ℕ) :
    (CJ0.blockMatrix source 72 ((u : ℤ)-24)).rank ≤ allowance_72 u := by
  unfold allowance_72
  split
  · exact cell_72_0
  · exact cell_72_1
  · exact cell_72_2
  · exact (block_rank_le 72 _).trans (rank_le_nominal 72 _)

theorem grade_72 : (∑ u ∈ Finset.range (81-72), (CJ0.blockMatrix source 72 ((u : ℤ)-24)).rank) ≤ 72 := by
  refine (Finset.sum_le_sum fun u _ => bound_72 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_72)]
  decide +kernel

private def matrix_73_0 : CJ1.Block where
  bank := .rightLow
  cap := 8
  free := [(4, 0), (6, 0), (8, 0)]
  vectors := [
    [[], [], [], [], [1]],
    [[], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [1]]
  ]
private theorem cell_73_0 : (CJ0.blockMatrix source 73 ((0 : ℤ)-24)).rank ≤ 8 :=
  Fast.cell (z := matrix_73_0) (Fast.bands [(0, 66, 8), (1, 67, 6), (2, 68, 4), (3, 69, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_73_1 : CJ1.Block where
  bank := .leftLow
  cap := 12
  free := [(2, 0), (2, 1), (2, 2), (3, 0)]
  vectors := [
    [[0, 0, 0, 0, 1326, 5100, 14700], [0, 0, 2130706382, 2130706334, 2130706241], [1]],
    [[0, 0, 0, 0, 0, 1275, 4900], [0, 0, 0, 2130706383, 2130706336], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 1225], [0, 0, 0, 0, 2130706384], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 39200], [0, 0, 0, 0, 2130705257], [], [1]]
  ]
private theorem cell_73_1 : (CJ0.blockMatrix source 73 ((1 : ℤ)-24)).rank ≤ 12 :=
  Fast.cell (z := matrix_73_1) (Fast.bands [(49, 49, 1), (50, 50, 2), (51, 52, 2), (52, 54, 2), (53, 56, 2), (54, 58, 2), (55, 60, 2), (56, 62, 2), (57, 64, 2), (58, 66, 2), (59, 68, 2), (60, 70, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_73 (u : ℕ) : ℕ :=
  match u with
  | 0 => 8
  | 1 => 12
  | u => nominal 73 u

private theorem bound_73 (u : ℕ) :
    (CJ0.blockMatrix source 73 ((u : ℤ)-24)).rank ≤ allowance_73 u := by
  unfold allowance_73
  split
  · exact cell_73_0
  · exact cell_73_1
  · exact (block_rank_le 73 _).trans (rank_le_nominal 73 _)

theorem grade_73 : (∑ u ∈ Finset.range (81-73), (CJ0.blockMatrix source 73 ((u : ℤ)-24)).rank) ≤ 54 := by
  refine (Finset.sum_le_sum fun u _ => bound_73 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_73)]
  decide +kernel

private def matrix_74_0 : CJ1.Block where
  bank := .rightLow
  cap := 7
  free := [(4, 0), (6, 0), (8, 0), (10, 0)]
  vectors := [
    [[], [], [], [], [1]],
    [[], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [], [], [1]]
  ]
private theorem cell_74_0 : (CJ0.blockMatrix source 74 ((0 : ℤ)-24)).rank ≤ 7 :=
  Fast.cell (z := matrix_74_0) (Fast.bands [(0, 68, 7), (1, 69, 5), (2, 70, 3), (3, 71, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_74_1 : CJ1.Block where
  bank := .leftLow
  cap := 10
  free := [(2, 0), (2, 1)]
  vectors := [
    [[0, 0, 0, 0, 1326, 5100], [0, 0, 2130706382, 2130706334], [1]],
    [[0, 0, 0, 0, 0, 1275], [0, 0, 0, 2130706383], [0, 1]]
  ]
private theorem cell_74_1 : (CJ0.blockMatrix source 74 ((1 : ℤ)-24)).rank ≤ 10 :=
  Fast.cell (z := matrix_74_1) (Fast.bands [(50, 50, 1), (51, 51, 2), (52, 53, 2), (53, 55, 2), (54, 57, 2), (55, 59, 2), (56, 61, 2), (57, 63, 2), (58, 65, 2), (59, 67, 2), (60, 69, 2), (61, 71, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_74 (u : ℕ) : ℕ :=
  match u with
  | 0 => 7
  | 1 => 10
  | u => nominal 74 u

private theorem bound_74 (u : ℕ) :
    (CJ0.blockMatrix source 74 ((u : ℤ)-24)).rank ≤ allowance_74 u := by
  unfold allowance_74
  split
  · exact cell_74_0
  · exact cell_74_1
  · exact (block_rank_le 74 _).trans (rank_le_nominal 74 _)

theorem grade_74 : (∑ u ∈ Finset.range (81-74), (CJ0.blockMatrix source 74 ((u : ℤ)-24)).rank) ≤ 39 := by
  refine (Finset.sum_le_sum fun u _ => bound_74 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_74)]
  decide +kernel

private def matrix_75_0 : CJ1.Block where
  bank := .rightLow
  cap := 6
  free := [(4, 0), (6, 0), (8, 0), (10, 0), (12, 0)]
  vectors := [
    [[], [], [], [], [1]],
    [[], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [], [], [], [], [1]]
  ]
private theorem cell_75_0 : (CJ0.blockMatrix source 75 ((0 : ℤ)-24)).rank ≤ 6 :=
  Fast.cell (z := matrix_75_0) (Fast.bands [(0, 70, 6), (1, 71, 4), (2, 72, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_75_1 : CJ1.Block where
  bank := .leftLow
  cap := 8
  free := [(2, 0)]
  vectors := [
    [[0, 0, 0, 0, 1326], [0, 0, 2130706382], [1]]
  ]
private theorem cell_75_1 : (CJ0.blockMatrix source 75 ((1 : ℤ)-24)).rank ≤ 8 :=
  Fast.cell (z := matrix_75_1) (Fast.bands [(51, 51, 1), (52, 52, 2), (53, 54, 2), (54, 56, 2), (55, 58, 2), (56, 60, 2), (57, 62, 2), (58, 64, 2), (59, 66, 2), (60, 68, 2), (61, 70, 2), (62, 72, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_75 (u : ℕ) : ℕ :=
  match u with
  | 0 => 6
  | 1 => 8
  | u => nominal 75 u

private theorem bound_75 (u : ℕ) :
    (CJ0.blockMatrix source 75 ((u : ℤ)-24)).rank ≤ allowance_75 u := by
  unfold allowance_75
  split
  · exact cell_75_0
  · exact cell_75_1
  · exact (block_rank_le 75 _).trans (rank_le_nominal 75 _)

theorem grade_75 : (∑ u ∈ Finset.range (81-75), (CJ0.blockMatrix source 75 ((u : ℤ)-24)).rank) ≤ 27 := by
  refine (Finset.sum_le_sum fun u _ => bound_75 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_75)]
  decide +kernel

private def matrix_76_0 : CJ1.Block where
  bank := .leftLow
  cap := 5
  free := [(1, 0), (1, 1), (1, 2), (2, 0)]
  vectors := [
    [[0, 0, 2130706379, 2130706327, 2130706225], [1]],
    [[0, 0, 0, 2130706380, 2130706329], [0, 1]],
    [[0, 0, 0, 0, 2130706381], [0, 0, 1]],
    [[0, 0, 0, 0, 2130705107], [], [1]]
  ]
private theorem cell_76_0 : (CJ0.blockMatrix source 76 ((0 : ℤ)-24)).rank ≤ 5 :=
  Fast.cell (z := matrix_76_0) (Fast.bands [(52, 52, 1), (53, 54, 1), (54, 56, 1), (55, 58, 1), (56, 60, 1), (57, 62, 1), (58, 64, 1), (59, 66, 1), (60, 68, 1), (61, 70, 1), (62, 72, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_76 (u : ℕ) : ℕ :=
  match u with
  | 0 => 5
  | u => nominal 76 u

private theorem bound_76 (u : ℕ) :
    (CJ0.blockMatrix source 76 ((u : ℤ)-24)).rank ≤ allowance_76 u := by
  unfold allowance_76
  split
  · exact cell_76_0
  · exact (block_rank_le 76 _).trans (rank_le_nominal 76 _)

theorem grade_76 : (∑ u ∈ Finset.range (81-76), (CJ0.blockMatrix source 76 ((u : ℤ)-24)).rank) ≤ 18 := by
  refine (Finset.sum_le_sum fun u _ => bound_76 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_76)]
  decide +kernel

private def matrix_77_0 : CJ1.Block where
  bank := .leftLow
  cap := 4
  free := [(1, 0), (1, 1)]
  vectors := [
    [[0, 0, 2130706379, 2130706327], [1]],
    [[0, 0, 0, 2130706380], [0, 1]]
  ]
private theorem cell_77_0 : (CJ0.blockMatrix source 77 ((0 : ℤ)-24)).rank ≤ 4 :=
  Fast.cell (z := matrix_77_0) (Fast.bands [(53, 53, 1), (54, 55, 1), (55, 57, 1), (56, 59, 1), (57, 61, 1), (58, 63, 1), (59, 65, 1), (60, 67, 1), (61, 69, 1), (62, 71, 1), (63, 73, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_77 (u : ℕ) : ℕ :=
  match u with
  | 0 => 4
  | u => nominal 77 u

private theorem bound_77 (u : ℕ) :
    (CJ0.blockMatrix source 77 ((u : ℤ)-24)).rank ≤ allowance_77 u := by
  unfold allowance_77
  split
  · exact cell_77_0
  · exact (block_rank_le 77 _).trans (rank_le_nominal 77 _)

theorem grade_77 : (∑ u ∈ Finset.range (81-77), (CJ0.blockMatrix source 77 ((u : ℤ)-24)).rank) ≤ 11 := by
  refine (Finset.sum_le_sum fun u _ => bound_77 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_77)]
  decide +kernel

private def matrix_78_0 : CJ1.Block where
  bank := .leftLow
  cap := 3
  free := [(1, 0)]
  vectors := [
    [[0, 0, 2130706379], [1]]
  ]
private theorem cell_78_0 : (CJ0.blockMatrix source 78 ((0 : ℤ)-24)).rank ≤ 3 :=
  Fast.cell (z := matrix_78_0) (Fast.bands [(54, 54, 1), (55, 56, 1), (56, 58, 1), (57, 60, 1), (58, 62, 1), (59, 64, 1), (60, 66, 1), (61, 68, 1), (62, 70, 1), (63, 72, 1), (64, 74, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_78 (u : ℕ) : ℕ :=
  match u with
  | 0 => 3
  | u => nominal 78 u

private theorem bound_78 (u : ℕ) :
    (CJ0.blockMatrix source 78 ((u : ℤ)-24)).rank ≤ allowance_78 u := by
  unfold allowance_78
  split
  · exact cell_78_0
  · exact (block_rank_le 78 _).trans (rank_le_nominal 78 _)

theorem grade_78 : (∑ u ∈ Finset.range (81-78), (CJ0.blockMatrix source 78 ((u : ℤ)-24)).rank) ≤ 6 := by
  refine (Finset.sum_le_sum fun u _ => bound_78 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_78)]
  decide +kernel

end Front6960ListBank

end Merged_R6960Front6960ListCells7

-- merged module R6960Front6960ListRank
section Merged_R6960Front6960ListRank

set_option Elab.async false

namespace Front6960ListBank
open scoped BigOperators

private def rankTable : List ℕ := [57, 168, 330, 540, 795, 1092, 1428, 1800, 2205, 2640, 3102, 3542, 3960, 4356, 4730, 5040, 5289, 5480, 5616, 5700, 5735, 5724, 5670, 5576, 5445, 5280, 5115, 4950, 4785, 4620, 4455, 4290, 4125, 3960, 3796, 3633, 3471, 3311, 3153, 2997, 2844, 2694, 2547, 2404, 2265, 2129, 1998, 1870, 1747, 1627, 1513, 1401, 1296, 1193, 1096, 1002, 914, 828, 749, 672, 601, 533, 471, 411, 358, 307, 262, 220, 183, 149, 120, 94, 72, 54, 39, 27, 18, 11, 6]

private theorem grades (q : Fin 79) :
    (∑ u ∈ Finset.range (81-q.val), (CJ0.blockMatrix source q.val ((u : ℤ)-24)).rank) ≤
      rankTable[q.val]'(by simpa [rankTable] using q.isLt) := by
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
  · exact grade_75
  · exact grade_76
  · exact grade_77
  · exact grade_78

theorem prefix_bound : CJ0.prefixRank source 79 ≤ 184686 := by
  unfold CJ0.prefixRank
  change (∑ q ∈ Finset.range 79, ∑ u ∈ Finset.range (81-q),
    (CJ0.blockMatrix source q ((u : ℤ)-24)).rank) ≤ _
  rw [← Fin.sum_univ_eq_sum_range]
  apply (Finset.sum_le_sum fun q _ => grades q).trans_eq
  decide +kernel

#print axioms prefix_bound
end Front6960ListBank

end Merged_R6960Front6960ListRank

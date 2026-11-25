import ProximityPrize.SubmissionLower.Front6963ListBank

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6963ListBank
open scoped BigOperators

private def matrix_70_2 : CJ1.Block where
  bank := .rightLow
  cap := 27
  free := [(3, 0), (4, 1), (5, 0), (6, 1), (8, 1), (10, 1)]
  vectors := [
    [[], [], [2130706432], [1]],
    [[], [], [2130706432], [], [0, 1]],
    [[], [], [2130706432], [], [2130706432], [1]],
    [[], [], [2130706431], [], [2130706432], [], [0, 1]],
    [[], [], [2130706432], [], [], [], [1], [2130706431], [0, 1]],
    [[], [], [], [], [1], [], [2], [2130706431], [1], [2130706431], [0, 1]]
  ]
private theorem cell_70_2 : (CJ0.blockMatrix source 70 ((2 : ℤ)-24)).rank ≤ 27 :=
  Fast.cell (z := matrix_70_2) (Fast.bands [(0, 60, 11), (1, 61, 9), (2, 62, 7), (3, 63, 5), (4, 64, 3), (5, 65, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_70_3 : CJ1.Block where
  bank := .leftLow
  cap := 28
  free := [(4, 0), (4, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 230300, 1695008], [0, 0, 0, 0, 0, 0, 2130688009, 2130603785], [0, 0, 0, 0, 1128, 4230], [0, 0, 2130706386, 2130706344], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 211876], [0, 0, 0, 0, 0, 0, 0, 2130689137], [0, 0, 0, 0, 0, 1081], [0, 0, 0, 2130706387], [0, 1]]
  ]
private theorem cell_70_3 : (CJ0.blockMatrix source 70 ((3 : ℤ)-24)).rank ≤ 28 :=
  Fast.cell (z := matrix_70_3) (Fast.bands [(46, 46, 1), (47, 47, 2), (48, 48, 3), (49, 49, 4), (50, 51, 4), (51, 53, 4), (52, 55, 4), (53, 57, 4), (54, 59, 4), (55, 61, 4), (56, 63, 4), (57, 65, 3), (58, 67, 2), (59, 69, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_70 (u : ℕ) : ℕ :=
  match u with
  | 2 => 27
  | 3 => 28
  | u => nominal 70 u

private theorem bound_70 (u : ℕ) :
    (CJ0.blockMatrix source 70 ((u : ℤ)-24)).rank ≤ allowance_70 u := by
  unfold allowance_70
  split
  · exact cell_70_2
  · exact cell_70_3
  · exact (block_rank_le 70 _).trans (rank_le_nominal 70 _)

theorem grade_70 : (∑ u ∈ Finset.range (83-70), (CJ0.blockMatrix source 70 ((u : ℤ)-24)).rank) ≤ 183 := by
  refine (Finset.sum_le_sum fun u _ => bound_70 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_70)]
  decide +kernel

private def matrix_71_1 : CJ1.Block where
  bank := .rightLow
  cap := 20
  free := [(4, 0), (6, 0)]
  vectors := [
    [[], [], [], [2130706432], [1]],
    [[], [], [], [2130706432], [], [2130706432], [1]]
  ]
private theorem cell_71_1 : (CJ0.blockMatrix source 71 ((1 : ℤ)-24)).rank ≤ 20 :=
  Fast.cell (z := matrix_71_1) (Fast.bands [(0, 61, 11), (1, 62, 9), (2, 63, 7), (3, 64, 5), (4, 65, 3), (5, 66, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_71_2 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130684333, 2130581483, 2130236033, 2129232513], [0, 0, 0, 0, 1275, 4850, 13818, 34944], [0, 0, 2130706383, 2130706337, 2130706249, 2130706081], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 2130685608, 2130588833, 2130264257], [0, 0, 0, 0, 0, 1225, 4655, 13248], [0, 0, 0, 2130706384, 2130706339, 2130706253], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130686833, 2130595889], [0, 0, 0, 0, 0, 0, 1176, 4464], [0, 0, 0, 0, 2130706385, 2130706341], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 2130688009], [0, 0, 0, 0, 0, 0, 0, 1128], [0, 0, 0, 0, 0, 2130706386], [0, 0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130015533, 2125566137], [0, 0, 0, 0, 0, 0, 36848, 207552], [0, 0, 0, 0, 2130705305, 2130702156], [], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 2130070805], [0, 0, 0, 0, 0, 0, 0, 34592], [0, 0, 0, 0, 0, 2130705352], [], [0, 1]]
  ]
private theorem cell_71_2 : (CJ0.blockMatrix source 71 ((2 : ℤ)-24)).rank ≤ 24 :=
  Fast.cell (z := matrix_71_2) (Fast.bands [(47, 47, 1), (48, 48, 2), (49, 49, 3), (50, 51, 3), (51, 53, 3), (52, 55, 3), (53, 57, 3), (54, 59, 3), (55, 61, 3), (56, 63, 3), (57, 65, 3), (58, 67, 2), (59, 69, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_71_3 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(4, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 230300], [0, 0, 0, 0, 0, 0, 2130688009], [0, 0, 0, 0, 1128], [0, 0, 2130706386], [1]]
  ]
private theorem cell_71_3 : (CJ0.blockMatrix source 71 ((3 : ℤ)-24)).rank ≤ 24 :=
  Fast.cell (z := matrix_71_3) (Fast.bands [(47, 47, 1), (48, 48, 2), (49, 49, 3), (50, 50, 4), (51, 52, 4), (52, 54, 4), (53, 56, 4), (54, 58, 4), (55, 60, 4), (56, 62, 4), (57, 64, 4), (58, 66, 3), (59, 68, 2), (60, 70, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_71 (u : ℕ) : ℕ :=
  match u with
  | 1 => 20
  | 2 => 24
  | 3 => 24
  | u => nominal 71 u

private theorem bound_71 (u : ℕ) :
    (CJ0.blockMatrix source 71 ((u : ℤ)-24)).rank ≤ allowance_71 u := by
  unfold allowance_71
  split
  · exact cell_71_1
  · exact cell_71_2
  · exact cell_71_3
  · exact (block_rank_le 71 _).trans (rank_le_nominal 71 _)

theorem grade_71 : (∑ u ∈ Finset.range (83-71), (CJ0.blockMatrix source 71 ((u : ℤ)-24)).rank) ≤ 149 := by
  refine (Finset.sum_le_sum fun u _ => bound_71 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_71)]
  decide +kernel

private def matrix_72_1 : CJ1.Block where
  bank := .rightLow
  cap := 18
  free := [(3, 0), (4, 0), (6, 0), (8, 0)]
  vectors := [
    [[], [], [], [1]],
    [[], [], [], [], [1]],
    [[], [], [], [], [], [2130706432], [1]],
    [[], [], [], [], [], [2130706432], [], [2130706432], [1]]
  ]
private theorem cell_72_1 : (CJ0.blockMatrix source 72 ((1 : ℤ)-24)).rank ≤ 18 :=
  Fast.cell (z := matrix_72_1) (Fast.bands [(0, 63, 10), (1, 64, 8), (2, 65, 6), (3, 66, 4), (4, 67, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_72_2 : CJ1.Block where
  bank := .leftLow
  cap := 21
  free := [(3, 0), (3, 1), (3, 2), (4, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130684333, 2130581483, 2130236033], [0, 0, 0, 0, 1275, 4850, 13818], [0, 0, 2130706383, 2130706337, 2130706249], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 2130685608, 2130588833], [0, 0, 0, 0, 0, 1225, 4655], [0, 0, 0, 2130706384, 2130706339], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130686833], [0, 0, 0, 0, 0, 0, 1176], [0, 0, 0, 0, 2130706385], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130015533], [0, 0, 0, 0, 0, 0, 36848], [0, 0, 0, 0, 2130705305], [], [1]]
  ]
private theorem cell_72_2 : (CJ0.blockMatrix source 72 ((2 : ℤ)-24)).rank ≤ 21 :=
  Fast.cell (z := matrix_72_2) (Fast.bands [(48, 48, 1), (49, 49, 2), (50, 50, 3), (51, 52, 3), (52, 54, 3), (53, 56, 3), (54, 58, 3), (55, 60, 3), (56, 62, 3), (57, 64, 3), (58, 66, 3), (59, 68, 2), (60, 70, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_72 (u : ℕ) : ℕ :=
  match u with
  | 1 => 18
  | 2 => 21
  | u => nominal 72 u

private theorem bound_72 (u : ℕ) :
    (CJ0.blockMatrix source 72 ((u : ℤ)-24)).rank ≤ allowance_72 u := by
  unfold allowance_72
  split
  · exact cell_72_1
  · exact cell_72_2
  · exact (block_rank_le 72 _).trans (rank_le_nominal 72 _)

theorem grade_72 : (∑ u ∈ Finset.range (83-72), (CJ0.blockMatrix source 72 ((u : ℤ)-24)).rank) ≤ 120 := by
  refine (Finset.sum_le_sum fun u _ => bound_72 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_72)]
  decide +kernel

private def matrix_73_0 : CJ1.Block where
  bank := .rightLow
  cap := 10
  free := [(4, 0)]
  vectors := [
    [[], [], [], [], [1]]
  ]
private theorem cell_73_0 : (CJ0.blockMatrix source 73 ((0 : ℤ)-24)).rank ≤ 10 :=
  Fast.cell (z := matrix_73_0) (Fast.bands [(0, 64, 10), (1, 65, 8), (2, 66, 6), (3, 67, 4), (4, 68, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_73_1 : CJ1.Block where
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
private theorem cell_73_1 : (CJ0.blockMatrix source 73 ((1 : ℤ)-24)).rank ≤ 16 :=
  Fast.cell (z := matrix_73_1) (Fast.bands [(0, 65, 9), (1, 66, 7), (2, 67, 5), (3, 68, 3), (4, 69, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_73_2 : CJ1.Block where
  bank := .leftLow
  cap := 18
  free := [(3, 0), (3, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130684333, 2130581483], [0, 0, 0, 0, 1275, 4850], [0, 0, 2130706383, 2130706337], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 2130685608], [0, 0, 0, 0, 0, 1225], [0, 0, 0, 2130706384], [0, 1]]
  ]
private theorem cell_73_2 : (CJ0.blockMatrix source 73 ((2 : ℤ)-24)).rank ≤ 18 :=
  Fast.cell (z := matrix_73_2) (Fast.bands [(49, 49, 1), (50, 50, 2), (51, 51, 3), (52, 53, 3), (53, 55, 3), (54, 57, 3), (55, 59, 3), (56, 61, 3), (57, 63, 3), (58, 65, 3), (59, 67, 3), (60, 69, 2), (61, 71, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_73 (u : ℕ) : ℕ :=
  match u with
  | 0 => 10
  | 1 => 16
  | 2 => 18
  | u => nominal 73 u

private theorem bound_73 (u : ℕ) :
    (CJ0.blockMatrix source 73 ((u : ℤ)-24)).rank ≤ allowance_73 u := by
  unfold allowance_73
  split
  · exact cell_73_0
  · exact cell_73_1
  · exact cell_73_2
  · exact (block_rank_le 73 _).trans (rank_le_nominal 73 _)

theorem grade_73 : (∑ u ∈ Finset.range (83-73), (CJ0.blockMatrix source 73 ((u : ℤ)-24)).rank) ≤ 94 := by
  refine (Finset.sum_le_sum fun u _ => bound_73 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_73)]
  decide +kernel

private def matrix_74_0 : CJ1.Block where
  bank := .rightLow
  cap := 9
  free := [(4, 0), (6, 0)]
  vectors := [
    [[], [], [], [], [1]],
    [[], [], [], [], [], [], [1]]
  ]
private theorem cell_74_0 : (CJ0.blockMatrix source 74 ((0 : ℤ)-24)).rank ≤ 9 :=
  Fast.cell (z := matrix_74_0) (Fast.bands [(0, 66, 9), (1, 67, 7), (2, 68, 5), (3, 69, 3), (4, 70, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_74_1 : CJ1.Block where
  bank := .leftLow
  cap := 14
  free := [(2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1)]
  vectors := [
    [[0, 0, 0, 0, 1431, 5512, 15912, 40800], [0, 0, 2130706380, 2130706330, 2130706233, 2130706045], [1]],
    [[0, 0, 0, 0, 0, 1378, 5304, 15300], [0, 0, 0, 2130706381, 2130706332, 2130706237], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 1326, 5100], [0, 0, 0, 0, 2130706382, 2130706334], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 1275], [0, 0, 0, 0, 0, 2130706383], [0, 0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 44200, 252450], [0, 0, 0, 0, 2130705158, 2130701533], [], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 41650], [0, 0, 0, 0, 0, 2130705208], [], [0, 1]]
  ]
private theorem cell_74_1 : (CJ0.blockMatrix source 74 ((1 : ℤ)-24)).rank ≤ 14 :=
  Fast.cell (z := matrix_74_1) (Fast.bands [(50, 50, 1), (51, 51, 2), (52, 53, 2), (53, 55, 2), (54, 57, 2), (55, 59, 2), (56, 61, 2), (57, 63, 2), (58, 65, 2), (59, 67, 2), (60, 69, 2), (61, 71, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_74_2 : CJ1.Block where
  bank := .leftLow
  cap := 15
  free := [(3, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130684333], [0, 0, 0, 0, 1275], [0, 0, 2130706383], [1]]
  ]
private theorem cell_74_2 : (CJ0.blockMatrix source 74 ((2 : ℤ)-24)).rank ≤ 15 :=
  Fast.cell (z := matrix_74_2) (Fast.bands [(50, 50, 1), (51, 51, 2), (52, 52, 3), (53, 54, 3), (54, 56, 3), (55, 58, 3), (56, 60, 3), (57, 62, 3), (58, 64, 3), (59, 66, 3), (60, 68, 3), (61, 70, 2), (62, 72, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_74 (u : ℕ) : ℕ :=
  match u with
  | 0 => 9
  | 1 => 14
  | 2 => 15
  | u => nominal 74 u

private theorem bound_74 (u : ℕ) :
    (CJ0.blockMatrix source 74 ((u : ℤ)-24)).rank ≤ allowance_74 u := by
  unfold allowance_74
  split
  · exact cell_74_0
  · exact cell_74_1
  · exact cell_74_2
  · exact (block_rank_le 74 _).trans (rank_le_nominal 74 _)

theorem grade_74 : (∑ u ∈ Finset.range (83-74), (CJ0.blockMatrix source 74 ((u : ℤ)-24)).rank) ≤ 72 := by
  refine (Finset.sum_le_sum fun u _ => bound_74 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_74)]
  decide +kernel

private def matrix_75_0 : CJ1.Block where
  bank := .rightLow
  cap := 8
  free := [(4, 0), (6, 0), (8, 0)]
  vectors := [
    [[], [], [], [], [1]],
    [[], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [1]]
  ]
private theorem cell_75_0 : (CJ0.blockMatrix source 75 ((0 : ℤ)-24)).rank ≤ 8 :=
  Fast.cell (z := matrix_75_0) (Fast.bands [(0, 68, 8), (1, 69, 6), (2, 70, 4), (3, 71, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_75_1 : CJ1.Block where
  bank := .leftLow
  cap := 12
  free := [(2, 0), (2, 1), (2, 2), (3, 0)]
  vectors := [
    [[0, 0, 0, 0, 1431, 5512, 15912], [0, 0, 2130706380, 2130706330, 2130706233], [1]],
    [[0, 0, 0, 0, 0, 1378, 5304], [0, 0, 0, 2130706381, 2130706332], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 1326], [0, 0, 0, 0, 2130706382], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 44200], [0, 0, 0, 0, 2130705158], [], [1]]
  ]
private theorem cell_75_1 : (CJ0.blockMatrix source 75 ((1 : ℤ)-24)).rank ≤ 12 :=
  Fast.cell (z := matrix_75_1) (Fast.bands [(51, 51, 1), (52, 52, 2), (53, 54, 2), (54, 56, 2), (55, 58, 2), (56, 60, 2), (57, 62, 2), (58, 64, 2), (59, 66, 2), (60, 68, 2), (61, 70, 2), (62, 72, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_75 (u : ℕ) : ℕ :=
  match u with
  | 0 => 8
  | 1 => 12
  | u => nominal 75 u

private theorem bound_75 (u : ℕ) :
    (CJ0.blockMatrix source 75 ((u : ℤ)-24)).rank ≤ allowance_75 u := by
  unfold allowance_75
  split
  · exact cell_75_0
  · exact cell_75_1
  · exact (block_rank_le 75 _).trans (rank_le_nominal 75 _)

theorem grade_75 : (∑ u ∈ Finset.range (83-75), (CJ0.blockMatrix source 75 ((u : ℤ)-24)).rank) ≤ 54 := by
  refine (Finset.sum_le_sum fun u _ => bound_75 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_75)]
  decide +kernel

end Front6963ListBank

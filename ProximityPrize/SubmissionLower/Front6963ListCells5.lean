import ProximityPrize.SubmissionLower.Front6963ListCells0

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6963ListBank
open scoped BigOperators

private def allowance_60 (u : ℕ) : ℕ :=
  nominal 60 u

private theorem bound_60 (u : ℕ) :
    (CJ0.blockMatrix source 60 ((u : ℤ)-24)).rank ≤ allowance_60 u := by
  unfold allowance_60
  exact (block_rank_le 60 _).trans (rank_le_nominal 60 _)

theorem grade_60 : (∑ u ∈ Finset.range (83-60), (CJ0.blockMatrix source 60 ((u : ℤ)-24)).rank) ≤ 749 := by
  refine (Finset.sum_le_sum fun u _ => bound_60 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_60)]
  decide +kernel

private def matrix_61_6 : CJ1.Block where
  bank := .leftLow
  cap := 70
  free := [(7, 0), (7, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2092385865, 1679568837], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6096454, 62098764], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129855765, 2123414993], [0, 0, 0, 0, 0, 0, 0, 0, 101270, 701480], [0, 0, 0, 0, 0, 0, 2130696553, 2130654563], [0, 0, 0, 0, 741, 2622], [0, 0, 2130706395, 2130706365], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2098482319], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5245786], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129957035], [0, 0, 0, 0, 0, 0, 0, 0, 0, 91390], [0, 0, 0, 0, 0, 0, 0, 2130697294], [0, 0, 0, 0, 0, 703], [0, 0, 0, 2130706396], [0, 1]]
  ]
private theorem cell_61_6 : (CJ0.blockMatrix source 61 ((6 : ℤ)-24)).rank ≤ 70 :=
  Fast.cell (z := matrix_61_6) (Fast.bands [(37, 37, 1), (38, 38, 2), (39, 39, 3), (40, 40, 4), (41, 41, 5), (42, 42, 6), (43, 43, 7), (44, 45, 7), (45, 47, 7), (46, 49, 7), (47, 51, 7), (48, 53, 6), (49, 55, 5), (50, 57, 4), (51, 59, 3), (52, 61, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_61 (u : ℕ) : ℕ :=
  match u with
  | 6 => 70
  | u => nominal 61 u

private theorem bound_61 (u : ℕ) :
    (CJ0.blockMatrix source 61 ((u : ℤ)-24)).rank ≤ allowance_61 u := by
  unfold allowance_61
  split
  · exact cell_61_6
  · exact (block_rank_le 61 _).trans (rank_le_nominal 61 _)

theorem grade_61 : (∑ u ∈ Finset.range (83-61), (CJ0.blockMatrix source 61 ((u : ℤ)-24)).rank) ≤ 672 := by
  refine (Finset.sum_le_sum fun u _ => bound_61 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_61)]
  decide +kernel

private def matrix_62_6 : CJ1.Block where
  bank := .leftLow
  cap := 63
  free := [(7, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2092385865], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6096454], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129855765], [0, 0, 0, 0, 0, 0, 0, 0, 101270], [0, 0, 0, 0, 0, 0, 2130696553], [0, 0, 0, 0, 741], [0, 0, 2130706395], [1]]
  ]
private theorem cell_62_6 : (CJ0.blockMatrix source 62 ((6 : ℤ)-24)).rank ≤ 63 :=
  Fast.cell (z := matrix_62_6) (Fast.bands [(38, 38, 1), (39, 39, 2), (40, 40, 3), (41, 41, 4), (42, 42, 5), (43, 43, 6), (44, 44, 7), (45, 46, 7), (46, 48, 7), (47, 50, 7), (48, 52, 7), (49, 54, 6), (50, 56, 5), (51, 58, 4), (52, 60, 3), (53, 62, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_62 (u : ℕ) : ℕ :=
  match u with
  | 6 => 63
  | u => nominal 62 u

private theorem bound_62 (u : ℕ) :
    (CJ0.blockMatrix source 62 ((u : ℤ)-24)).rank ≤ allowance_62 u := by
  unfold allowance_62
  split
  · exact cell_62_6
  · exact (block_rank_le 62 _).trans (rank_le_nominal 62 _)

theorem grade_62 : (∑ u ∈ Finset.range (83-62), (CJ0.blockMatrix source 62 ((u : ℤ)-24)).rank) ≤ 601 := by
  refine (Finset.sum_le_sum fun u _ => bound_62 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_62)]
  decide +kernel

private def matrix_63_5 : CJ1.Block where
  bank := .leftLow
  cap := 60
  free := [(6, 0), (6, 1), (6, 2), (7, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9366819, 97740720, 592960368], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129484674, 2119982104, 2074431473], [0, 0, 0, 0, 0, 0, 0, 0, 135751, 962598, 4248461], [0, 0, 0, 0, 0, 0, 2130694092, 2130640136, 2130470150], [0, 0, 0, 0, 861, 3116, 8406], [0, 0, 2130706392, 2130706358, 2130706297], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8145060, 84708624], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129620425, 2121203863], [0, 0, 0, 0, 0, 0, 0, 0, 0, 123410, 872480], [0, 0, 0, 0, 0, 0, 0, 2130694953, 2130644933], [0, 0, 0, 0, 0, 820, 2960], [0, 0, 0, 2130706393, 2130706360], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7059052], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129743835], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 111930], [0, 0, 0, 0, 0, 0, 0, 0, 2130695773], [0, 0, 0, 0, 0, 0, 780], [0, 0, 0, 0, 2130706394], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 229923408], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2100224163], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3402672], [0, 0, 0, 0, 0, 0, 0, 0, 2130402623], [0, 0, 0, 0, 0, 0, 19760], [0, 0, 0, 0, 2130705692], [], [1]]
  ]
private theorem cell_63_5 : (CJ0.blockMatrix source 63 ((5 : ℤ)-24)).rank ≤ 60 :=
  Fast.cell (z := matrix_63_5) (Fast.bands [(39, 39, 1), (40, 40, 2), (41, 41, 3), (42, 42, 4), (43, 43, 5), (44, 44, 6), (45, 46, 6), (46, 48, 6), (47, 50, 6), (48, 52, 6), (49, 54, 6), (50, 56, 5), (51, 58, 4), (52, 60, 3), (53, 62, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_63 (u : ℕ) : ℕ :=
  match u with
  | 5 => 60
  | u => nominal 63 u

private theorem bound_63 (u : ℕ) :
    (CJ0.blockMatrix source 63 ((u : ℤ)-24)).rank ≤ allowance_63 u := by
  unfold allowance_63
  split
  · exact cell_63_5
  · exact (block_rank_le 63 _).trans (rank_le_nominal 63 _)

theorem grade_63 : (∑ u ∈ Finset.range (83-63), (CJ0.blockMatrix source 63 ((u : ℤ)-24)).rank) ≤ 533 := by
  refine (Finset.sum_le_sum fun u _ => bound_63 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_63)]
  decide +kernel

private def matrix_64_5 : CJ1.Block where
  bank := .leftLow
  cap := 54
  free := [(6, 0), (6, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9366819, 97740720], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129484674, 2119982104], [0, 0, 0, 0, 0, 0, 0, 0, 135751, 962598], [0, 0, 0, 0, 0, 0, 2130694092, 2130640136], [0, 0, 0, 0, 861, 3116], [0, 0, 2130706392, 2130706358], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8145060], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129620425], [0, 0, 0, 0, 0, 0, 0, 0, 0, 123410], [0, 0, 0, 0, 0, 0, 0, 2130694953], [0, 0, 0, 0, 0, 820], [0, 0, 0, 2130706393], [0, 1]]
  ]
private theorem cell_64_5 : (CJ0.blockMatrix source 64 ((5 : ℤ)-24)).rank ≤ 54 :=
  Fast.cell (z := matrix_64_5) (Fast.bands [(40, 40, 1), (41, 41, 2), (42, 42, 3), (43, 43, 4), (44, 44, 5), (45, 45, 6), (46, 47, 6), (47, 49, 6), (48, 51, 6), (49, 53, 6), (50, 55, 6), (51, 57, 5), (52, 59, 4), (53, 61, 3), (54, 63, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_64 (u : ℕ) : ℕ :=
  match u with
  | 5 => 54
  | u => nominal 64 u

private theorem bound_64 (u : ℕ) :
    (CJ0.blockMatrix source 64 ((u : ℤ)-24)).rank ≤ allowance_64 u := by
  unfold allowance_64
  split
  · exact cell_64_5
  · exact (block_rank_le 64 _).trans (rank_le_nominal 64 _)

theorem grade_64 : (∑ u ∈ Finset.range (83-64), (CJ0.blockMatrix source 64 ((u : ℤ)-24)).rank) ≤ 471 := by
  refine (Finset.sum_le_sum fun u _ => bound_64 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_64)]
  decide +kernel

private def matrix_65_4 : CJ1.Block where
  bank := .rightLow
  cap := 50
  free := [(4, 2), (6, 2), (8, 2), (10, 2), (12, 2)]
  vectors := [
    [[1], [2130706429], [0, 6], [0, 2130706429], [0, 0, 1]],
    [[1], [2130706430], [1, 3], [2130706429, 2130706432], [0, 6], [0, 2130706429], [0, 0, 1]],
    [[1], [2130706431], [2, 1], [2130706427], [1, 6], [2130706429, 2130706431], [0, 6], [0, 2130706429], [0, 0, 1]],
    [[1], [2130706432], [3], [2130706427], [3, 3], [2130706424], [1, 9], [2130706429, 2130706430], [0, 6], [0, 2130706429], [0, 0, 1]],
    [[1], [], [4], [2130706429], [6], [2130706421], [4, 6], [2130706421], [1, 12], [2130706429, 2130706429], [0, 6], [0, 2130706429], [0, 0, 1]]
  ]
private theorem cell_65_4 : (CJ0.blockMatrix source 65 ((4 : ℤ)-24)).rank ≤ 50 :=
  Fast.cell (z := matrix_65_4) (Fast.bands [(0, 52, 14), (1, 53, 12), (2, 54, 10), (3, 55, 8), (4, 56, 6), (5, 57, 4), (6, 58, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_65_5 : CJ1.Block where
  bank := .leftLow
  cap := 48
  free := [(6, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9366819], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129484674], [0, 0, 0, 0, 0, 0, 0, 0, 135751], [0, 0, 0, 0, 0, 0, 2130694092], [0, 0, 0, 0, 861], [0, 0, 2130706392], [1]]
  ]
private theorem cell_65_5 : (CJ0.blockMatrix source 65 ((5 : ℤ)-24)).rank ≤ 48 :=
  Fast.cell (z := matrix_65_5) (Fast.bands [(41, 41, 1), (42, 42, 2), (43, 43, 3), (44, 44, 4), (45, 45, 5), (46, 46, 6), (47, 48, 6), (48, 50, 6), (49, 52, 6), (50, 54, 6), (51, 56, 6), (52, 58, 5), (53, 60, 4), (54, 62, 3), (55, 64, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_65 (u : ℕ) : ℕ :=
  match u with
  | 4 => 50
  | 5 => 48
  | u => nominal 65 u

private theorem bound_65 (u : ℕ) :
    (CJ0.blockMatrix source 65 ((u : ℤ)-24)).rank ≤ allowance_65 u := by
  unfold allowance_65
  split
  · exact cell_65_4
  · exact cell_65_5
  · exact (block_rank_le 65 _).trans (rank_le_nominal 65 _)

theorem grade_65 : (∑ u ∈ Finset.range (83-65), (CJ0.blockMatrix source 65 ((u : ℤ)-24)).rank) ≤ 411 := by
  refine (Finset.sum_le_sum fun u _ => bound_65 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_65)]
  decide +kernel

private def matrix_66_4 : CJ1.Block where
  bank := .leftLow
  cap := 45
  free := [(5, 0), (5, 1), (5, 2), (6, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2128994129, 2115367043, 2048461193], [0, 0, 0, 0, 0, 0, 0, 0, 178365, 1290300, 5817900], [0, 0, 0, 0, 0, 0, 2130691253, 2130623273, 2130403669], [0, 0, 0, 0, 990, 3652, 10065], [0, 0, 2130706389, 2130706351, 2130706281], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129172494, 2116998893], [0, 0, 0, 0, 0, 0, 0, 0, 0, 163185, 1177770], [0, 0, 0, 0, 0, 0, 0, 2130692243, 2130628861], [0, 0, 0, 0, 0, 946, 3483], [0, 0, 0, 2130706390, 2130706353], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129335679], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 148995], [0, 0, 0, 0, 0, 0, 0, 0, 2130693189], [0, 0, 0, 0, 0, 0, 903], [0, 0, 0, 0, 2130706391], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2083872338], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4887036], [0, 0, 0, 0, 0, 0, 0, 0, 2130299180], [0, 0, 0, 0, 0, 0, 24682], [0, 0, 0, 0, 2130705572], [], [1]]
  ]
private theorem cell_66_4 : (CJ0.blockMatrix source 66 ((4 : ℤ)-24)).rank ≤ 45 :=
  Fast.cell (z := matrix_66_4) (Fast.bands [(42, 42, 1), (43, 43, 2), (44, 44, 3), (45, 45, 4), (46, 46, 5), (47, 48, 5), (48, 50, 5), (49, 52, 5), (50, 54, 5), (51, 56, 5), (52, 58, 5), (53, 60, 4), (54, 62, 3), (55, 64, 2), (56, 66, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_66 (u : ℕ) : ℕ :=
  match u with
  | 4 => 45
  | u => nominal 66 u

private theorem bound_66 (u : ℕ) :
    (CJ0.blockMatrix source 66 ((u : ℤ)-24)).rank ≤ allowance_66 u := by
  unfold allowance_66
  split
  · exact cell_66_4
  · exact (block_rank_le 66 _).trans (rank_le_nominal 66 _)

theorem grade_66 : (∑ u ∈ Finset.range (83-66), (CJ0.blockMatrix source 66 ((u : ℤ)-24)).rank) ≤ 358 := by
  refine (Finset.sum_le_sum fun u _ => bound_66 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_66)]
  decide +kernel

private def matrix_67_3 : CJ1.Block where
  bank := .rightLow
  cap := 40
  free := [(4, 1), (6, 1), (8, 1), (10, 1)]
  vectors := [
    [[], [2130706432], [3], [0, 2130706430], [0, 1]],
    [[], [2130706432], [2], [2130706432, 2130706432], [3], [0, 2130706430], [0, 1]],
    [[], [2130706432], [1], [2130706431], [4], [2130706432, 2130706431], [3], [0, 2130706430], [0, 1]],
    [[], [2130706432], [], [2130706430], [3], [2130706430], [6], [2130706432, 2130706430], [3], [0, 2130706430], [0, 1]]
  ]
private theorem cell_67_3 : (CJ0.blockMatrix source 67 ((3 : ℤ)-24)).rank ≤ 40 :=
  Fast.cell (z := matrix_67_3) (Fast.bands [(0, 55, 13), (1, 56, 11), (2, 57, 9), (3, 58, 7), (4, 59, 5), (5, 60, 3), (6, 61, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_67_4 : CJ1.Block where
  bank := .leftLow
  cap := 40
  free := [(5, 0), (5, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2128994129, 2115367043], [0, 0, 0, 0, 0, 0, 0, 0, 178365, 1290300], [0, 0, 0, 0, 0, 0, 2130691253, 2130623273], [0, 0, 0, 0, 990, 3652], [0, 0, 2130706389, 2130706351], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129172494], [0, 0, 0, 0, 0, 0, 0, 0, 0, 163185], [0, 0, 0, 0, 0, 0, 0, 2130692243], [0, 0, 0, 0, 0, 946], [0, 0, 0, 2130706390], [0, 1]]
  ]
private theorem cell_67_4 : (CJ0.blockMatrix source 67 ((4 : ℤ)-24)).rank ≤ 40 :=
  Fast.cell (z := matrix_67_4) (Fast.bands [(43, 43, 1), (44, 44, 2), (45, 45, 3), (46, 46, 4), (47, 47, 5), (48, 49, 5), (49, 51, 5), (50, 53, 5), (51, 55, 5), (52, 57, 5), (53, 59, 5), (54, 61, 4), (55, 63, 3), (56, 65, 2), (57, 67, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_67 (u : ℕ) : ℕ :=
  match u with
  | 3 => 40
  | 4 => 40
  | u => nominal 67 u

private theorem bound_67 (u : ℕ) :
    (CJ0.blockMatrix source 67 ((u : ℤ)-24)).rank ≤ allowance_67 u := by
  unfold allowance_67
  split
  · exact cell_67_3
  · exact cell_67_4
  · exact (block_rank_le 67 _).trans (rank_le_nominal 67 _)

theorem grade_67 : (∑ u ∈ Finset.range (83-67), (CJ0.blockMatrix source 67 ((u : ℤ)-24)).rank) ≤ 307 := by
  refine (Finset.sum_le_sum fun u _ => bound_67 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_67)]
  decide +kernel

private def matrix_68_3 : CJ1.Block where
  bank := .leftLow
  cap := 36
  free := [(4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 230300, 1695008, 7783200, 28538400], [0, 0, 0, 0, 0, 0, 2130688009, 2130603785, 2130325921, 2129533433], [0, 0, 0, 0, 1128, 4230, 11869, 29528], [0, 0, 2130706386, 2130706344, 2130706265, 2130706117], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 211876, 1556640, 7134600], [0, 0, 0, 0, 0, 0, 0, 2130689137, 2130610224, 2130350393], [0, 0, 0, 0, 0, 1081, 4048, 11341], [0, 0, 0, 2130706387, 2130706346, 2130706269], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 194580, 1426920], [0, 0, 0, 0, 0, 0, 0, 0, 2130690218, 2130616388], [0, 0, 0, 0, 0, 0, 1035, 3870], [0, 0, 0, 0, 2130706388, 2130706348], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 178365], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2130691253], [0, 0, 0, 0, 0, 0, 0, 990], [0, 0, 0, 0, 0, 2130706389], [0, 0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6849216, 62071020], [0, 0, 0, 0, 0, 0, 0, 0, 2130171338, 2126789993], [0, 0, 0, 0, 0, 0, 30360, 168300], [0, 0, 0, 0, 2130705443, 2130702737], [], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6135756], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2130216878], [0, 0, 0, 0, 0, 0, 0, 28380], [0, 0, 0, 0, 0, 2130705487], [], [0, 1]]
  ]
private theorem cell_68_3 : (CJ0.blockMatrix source 68 ((3 : ℤ)-24)).rank ≤ 36 :=
  Fast.cell (z := matrix_68_3) (Fast.bands [(44, 44, 1), (45, 45, 2), (46, 46, 3), (47, 47, 4), (48, 49, 4), (49, 51, 4), (50, 53, 4), (51, 55, 4), (52, 57, 4), (53, 59, 4), (54, 61, 4), (55, 63, 3), (56, 65, 2), (57, 67, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_68_4 : CJ1.Block where
  bank := .leftLow
  cap := 35
  free := [(5, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2128994129], [0, 0, 0, 0, 0, 0, 0, 0, 178365], [0, 0, 0, 0, 0, 0, 2130691253], [0, 0, 0, 0, 990], [0, 0, 2130706389], [1]]
  ]
private theorem cell_68_4 : (CJ0.blockMatrix source 68 ((4 : ℤ)-24)).rank ≤ 35 :=
  Fast.cell (z := matrix_68_4) (Fast.bands [(44, 44, 1), (45, 45, 2), (46, 46, 3), (47, 47, 4), (48, 48, 5), (49, 50, 5), (50, 52, 5), (51, 54, 5), (52, 56, 5), (53, 58, 5), (54, 60, 5), (55, 62, 4), (56, 64, 3), (57, 66, 2), (58, 68, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_68 (u : ℕ) : ℕ :=
  match u with
  | 3 => 36
  | 4 => 35
  | u => nominal 68 u

private theorem bound_68 (u : ℕ) :
    (CJ0.blockMatrix source 68 ((u : ℤ)-24)).rank ≤ allowance_68 u := by
  unfold allowance_68
  split
  · exact cell_68_3
  · exact cell_68_4
  · exact (block_rank_le 68 _).trans (rank_le_nominal 68 _)

theorem grade_68 : (∑ u ∈ Finset.range (83-68), (CJ0.blockMatrix source 68 ((u : ℤ)-24)).rank) ≤ 262 := by
  refine (Finset.sum_le_sum fun u _ => bound_68 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_68)]
  decide +kernel

private def matrix_69_2 : CJ1.Block where
  bank := .rightLow
  cap := 30
  free := [(4, 1), (6, 1), (8, 1)]
  vectors := [
    [[], [], [1], [2130706431], [0, 1]],
    [[], [], [1], [2130706432], [1], [2130706431], [0, 1]],
    [[], [], [1], [], [2], [2130706431], [1], [2130706431], [0, 1]]
  ]
private theorem cell_69_2 : (CJ0.blockMatrix source 69 ((2 : ℤ)-24)).rank ≤ 30 :=
  Fast.cell (z := matrix_69_2) (Fast.bands [(0, 58, 12), (1, 59, 10), (2, 60, 8), (3, 61, 6), (4, 62, 4), (5, 63, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_69_3 : CJ1.Block where
  bank := .leftLow
  cap := 32
  free := [(4, 0), (4, 1), (4, 2), (5, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 230300, 1695008, 7783200], [0, 0, 0, 0, 0, 0, 2130688009, 2130603785, 2130325921], [0, 0, 0, 0, 1128, 4230, 11869], [0, 0, 2130706386, 2130706344, 2130706265], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 211876, 1556640], [0, 0, 0, 0, 0, 0, 0, 2130689137, 2130610224], [0, 0, 0, 0, 0, 1081, 4048], [0, 0, 0, 2130706387, 2130706346], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 194580], [0, 0, 0, 0, 0, 0, 0, 0, 2130690218], [0, 0, 0, 0, 0, 0, 1035], [0, 0, 0, 0, 2130706388], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6849216], [0, 0, 0, 0, 0, 0, 0, 0, 2130171338], [0, 0, 0, 0, 0, 0, 30360], [0, 0, 0, 0, 2130705443], [], [1]]
  ]
private theorem cell_69_3 : (CJ0.blockMatrix source 69 ((3 : ℤ)-24)).rank ≤ 32 :=
  Fast.cell (z := matrix_69_3) (Fast.bands [(45, 45, 1), (46, 46, 2), (47, 47, 3), (48, 48, 4), (49, 50, 4), (50, 52, 4), (51, 54, 4), (52, 56, 4), (53, 58, 4), (54, 60, 4), (55, 62, 4), (56, 64, 3), (57, 66, 2), (58, 68, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_69 (u : ℕ) : ℕ :=
  match u with
  | 2 => 30
  | 3 => 32
  | u => nominal 69 u

private theorem bound_69 (u : ℕ) :
    (CJ0.blockMatrix source 69 ((u : ℤ)-24)).rank ≤ allowance_69 u := by
  unfold allowance_69
  split
  · exact cell_69_2
  · exact cell_69_3
  · exact (block_rank_le 69 _).trans (rank_le_nominal 69 _)

theorem grade_69 : (∑ u ∈ Finset.range (83-69), (CJ0.blockMatrix source 69 ((u : ℤ)-24)).rank) ≤ 220 := by
  refine (Finset.sum_le_sum fun u _ => bound_69 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_69)]
  decide +kernel

end Front6963ListBank

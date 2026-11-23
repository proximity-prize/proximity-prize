import ProximityPrize.SubmissionLower.R6960Front6960ListBank

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def matrix_60_6 : CJ1.Block where
  bank := .leftLow
  cap := 63
  free := [(7, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2098482319], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5245786], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129957035], [0, 0, 0, 0, 0, 0, 0, 0, 91390], [0, 0, 0, 0, 0, 0, 2130697294], [0, 0, 0, 0, 703], [0, 0, 2130706396], [1]]
  ]
private theorem cell_60_6 : (CJ0.blockMatrix source 60 ((6 : ℤ)-23)).rank ≤ 63 :=
  Fast.cell (z := matrix_60_6) (Fast.bands [(37, 37, 1), (38, 38, 2), (39, 39, 3), (40, 40, 4), (41, 41, 5), (42, 42, 6), (43, 43, 7), (44, 45, 7), (45, 47, 7), (46, 49, 7), (47, 51, 7), (48, 53, 6), (49, 55, 5), (50, 57, 4), (51, 59, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_60 (u : ℕ) : ℕ :=
  match u with
  | 6 => 63
  | u => nominal 60 u

private theorem bound_60 (u : ℕ) :
    (CJ0.blockMatrix source 60 ((u : ℤ)-23)).rank ≤ allowance_60 u := by
  unfold allowance_60
  split
  · exact cell_60_6
  · exact (block_rank_le 60 _).trans (rank_le_nominal 60 _)

theorem grade_60 : (∑ u ∈ Finset.range (81-60), (CJ0.blockMatrix source 60 ((u : ℤ)-23)).rank) ≤ 599 := by
  refine (Finset.sum_le_sum fun u _ => bound_60 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_60)]
  decide +kernel

private def matrix_61_5 : CJ1.Block where
  bank := .leftLow
  cap := 60
  free := [(6, 0), (6, 1), (6, 2), (7, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8145060, 84708624, 512102136], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129620425, 2121203863, 2081009513], [0, 0, 0, 0, 0, 0, 0, 0, 123410, 872480, 3838420], [0, 0, 0, 0, 0, 0, 2130694953, 2130644933, 2130487913], [0, 0, 0, 0, 820, 2960, 7962], [0, 0, 2130706393, 2130706360, 2130706301], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7059052, 73157448], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129743835, 2122311683], [0, 0, 0, 0, 0, 0, 0, 0, 0, 111930, 788840], [0, 0, 0, 0, 0, 0, 0, 2130695773, 2130649493], [0, 0, 0, 0, 0, 780, 2808], [0, 0, 0, 2130706394, 2130706362], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6096454], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129855765], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 101270], [0, 0, 0, 0, 0, 0, 0, 0, 2130696553], [0, 0, 0, 0, 0, 0, 741], [0, 0, 0, 0, 2130706395], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 193344684], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2104477503], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2997592], [0, 0, 0, 0, 0, 0, 0, 0, 2130432263], [0, 0, 0, 0, 0, 0, 18278], [0, 0, 0, 0, 2130705730], [], [1]]
  ]
private theorem cell_61_5 : (CJ0.blockMatrix source 61 ((5 : ℤ)-23)).rank ≤ 60 :=
  Fast.cell (z := matrix_61_5) (Fast.bands [(38, 38, 1), (39, 39, 2), (40, 40, 3), (41, 41, 4), (42, 42, 5), (43, 43, 6), (44, 45, 6), (45, 47, 6), (46, 49, 6), (47, 51, 6), (48, 53, 6), (49, 55, 5), (50, 57, 4), (51, 59, 3), (52, 61, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_61 (u : ℕ) : ℕ :=
  match u with
  | 5 => 60
  | u => nominal 61 u

private theorem bound_61 (u : ℕ) :
    (CJ0.blockMatrix source 61 ((u : ℤ)-23)).rank ≤ allowance_61 u := by
  unfold allowance_61
  split
  · exact cell_61_5
  · exact (block_rank_le 61 _).trans (rank_le_nominal 61 _)

theorem grade_61 : (∑ u ∈ Finset.range (81-61), (CJ0.blockMatrix source 61 ((u : ℤ)-23)).rank) ≤ 532 := by
  refine (Finset.sum_le_sum fun u _ => bound_61 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_61)]
  decide +kernel

private def matrix_62_5 : CJ1.Block where
  bank := .leftLow
  cap := 54
  free := [(6, 0), (6, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8145060, 84708624], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129620425, 2121203863], [0, 0, 0, 0, 0, 0, 0, 0, 123410, 872480], [0, 0, 0, 0, 0, 0, 2130694953, 2130644933], [0, 0, 0, 0, 820, 2960], [0, 0, 2130706393, 2130706360], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7059052], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129743835], [0, 0, 0, 0, 0, 0, 0, 0, 0, 111930], [0, 0, 0, 0, 0, 0, 0, 2130695773], [0, 0, 0, 0, 0, 780], [0, 0, 0, 2130706394], [0, 1]]
  ]
private theorem cell_62_5 : (CJ0.blockMatrix source 62 ((5 : ℤ)-23)).rank ≤ 54 :=
  Fast.cell (z := matrix_62_5) (Fast.bands [(39, 39, 1), (40, 40, 2), (41, 41, 3), (42, 42, 4), (43, 43, 5), (44, 44, 6), (45, 46, 6), (46, 48, 6), (47, 50, 6), (48, 52, 6), (49, 54, 6), (50, 56, 5), (51, 58, 4), (52, 60, 3), (53, 62, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_62 (u : ℕ) : ℕ :=
  match u with
  | 5 => 54
  | u => nominal 62 u

private theorem bound_62 (u : ℕ) :
    (CJ0.blockMatrix source 62 ((u : ℤ)-23)).rank ≤ allowance_62 u := by
  unfold allowance_62
  split
  · exact cell_62_5
  · exact (block_rank_le 62 _).trans (rank_le_nominal 62 _)

theorem grade_62 : (∑ u ∈ Finset.range (81-62), (CJ0.blockMatrix source 62 ((u : ℤ)-23)).rank) ≤ 470 := by
  refine (Finset.sum_le_sum fun u _ => bound_62 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_62)]
  decide +kernel

private def matrix_63_4 : CJ1.Block where
  bank := .rightLow
  cap := 50
  free := [(5, 2), (7, 2), (9, 2), (11, 2)]
  vectors := [
    [[1], [1, 2130706430], [2130706429, 3], [0, 6, 2130706432], [0, 2130706429], [0, 0, 1]],
    [[2], [2, 2130706428], [2130706427, 4], [1, 6, 2130706432], [2130706429, 2130706431], [0, 6], [0, 2130706429], [0, 0, 1]],
    [[3], [3, 2130706427], [2130706427, 4], [3, 3, 2130706432], [2130706424], [1, 9], [2130706429, 2130706430], [0, 6], [0, 2130706429], [0, 0, 1]],
    [[4], [4, 2130706427], [2130706429, 4], [6, 0, 2130706432], [2130706421], [4, 6], [2130706421], [1, 12], [2130706429, 2130706429], [0, 6], [0, 2130706429], [0, 0, 1]]
  ]
private theorem cell_63_4 : (CJ0.blockMatrix source 63 ((4 : ℤ)-23)).rank ≤ 50 :=
  Fast.cell (z := matrix_63_4) (Fast.bands [(0, 50, 14), (1, 51, 12), (2, 52, 10), (3, 53, 8), (4, 54, 6), (5, 55, 4), (6, 56, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_63_5 : CJ1.Block where
  bank := .leftLow
  cap := 48
  free := [(6, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8145060], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129620425], [0, 0, 0, 0, 0, 0, 0, 0, 123410], [0, 0, 0, 0, 0, 0, 2130694953], [0, 0, 0, 0, 820], [0, 0, 2130706393], [1]]
  ]
private theorem cell_63_5 : (CJ0.blockMatrix source 63 ((5 : ℤ)-23)).rank ≤ 48 :=
  Fast.cell (z := matrix_63_5) (Fast.bands [(40, 40, 1), (41, 41, 2), (42, 42, 3), (43, 43, 4), (44, 44, 5), (45, 45, 6), (46, 47, 6), (47, 49, 6), (48, 51, 6), (49, 53, 6), (50, 55, 6), (51, 57, 5), (52, 59, 4), (53, 61, 3), (54, 63, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_63 (u : ℕ) : ℕ :=
  match u with
  | 4 => 50
  | 5 => 48
  | u => nominal 63 u

private theorem bound_63 (u : ℕ) :
    (CJ0.blockMatrix source 63 ((u : ℤ)-23)).rank ≤ allowance_63 u := by
  unfold allowance_63
  split
  · exact cell_63_4
  · exact cell_63_5
  · exact (block_rank_le 63 _).trans (rank_le_nominal 63 _)

theorem grade_63 : (∑ u ∈ Finset.range (81-63), (CJ0.blockMatrix source 63 ((u : ℤ)-23)).rank) ≤ 411 := by
  refine (Finset.sum_le_sum fun u _ => bound_63 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_63)]
  decide +kernel

private def matrix_64_4 : CJ1.Block where
  bank := .leftLow
  cap := 45
  free := [(5, 0), (5, 1), (5, 2), (6, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129172494, 2116998893, 2057400893], [0, 0, 0, 0, 0, 0, 0, 0, 163185, 1177770, 5297600], [0, 0, 0, 0, 0, 0, 2130692243, 2130628861, 2130424654], [0, 0, 0, 0, 946, 3483, 9579], [0, 0, 2130706390, 2130706353, 2130706285], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129335679, 2118488843], [0, 0, 0, 0, 0, 0, 0, 0, 0, 148995, 1072764], [0, 0, 0, 0, 0, 0, 0, 2130693189, 2130634193], [0, 0, 0, 0, 0, 903, 3318], [0, 0, 0, 2130706391, 2130706355], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129484674], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 135751], [0, 0, 0, 0, 0, 0, 0, 0, 2130694092], [0, 0, 0, 0, 0, 0, 861], [0, 0, 0, 0, 2130706392], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2089981133], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4344032], [0, 0, 0, 0, 0, 0, 0, 0, 2130336203], [0, 0, 0, 0, 0, 0, 22960], [0, 0, 0, 0, 2130705613], [], [1]]
  ]
private theorem cell_64_4 : (CJ0.blockMatrix source 64 ((4 : ℤ)-23)).rank ≤ 45 :=
  Fast.cell (z := matrix_64_4) (Fast.bands [(41, 41, 1), (42, 42, 2), (43, 43, 3), (44, 44, 4), (45, 45, 5), (46, 47, 5), (47, 49, 5), (48, 51, 5), (49, 53, 5), (50, 55, 5), (51, 57, 5), (52, 59, 4), (53, 61, 3), (54, 63, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_64 (u : ℕ) : ℕ :=
  match u with
  | 4 => 45
  | u => nominal 64 u

private theorem bound_64 (u : ℕ) :
    (CJ0.blockMatrix source 64 ((u : ℤ)-23)).rank ≤ allowance_64 u := by
  unfold allowance_64
  split
  · exact cell_64_4
  · exact (block_rank_le 64 _).trans (rank_le_nominal 64 _)

theorem grade_64 : (∑ u ∈ Finset.range (81-64), (CJ0.blockMatrix source 64 ((u : ℤ)-23)).rank) ≤ 358 := by
  refine (Finset.sum_le_sum fun u _ => bound_64 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_64)]
  decide +kernel

private def matrix_65_3 : CJ1.Block where
  bank := .rightLow
  cap := 40
  free := [(3, 1), (5, 1), (7, 1), (9, 1)]
  vectors := [
    [[2130706432], [3], [0, 2130706430], [0, 1]],
    [[2130706432], [2], [2130706432, 2130706432], [3], [0, 2130706430], [0, 1]],
    [[2130706432], [1], [2130706431], [4], [2130706432, 2130706431], [3], [0, 2130706430], [0, 1]],
    [[2130706432], [], [2130706430], [3], [2130706430], [6], [2130706432, 2130706430], [3], [0, 2130706430], [0, 1]]
  ]
private theorem cell_65_3 : (CJ0.blockMatrix source 65 ((3 : ℤ)-23)).rank ≤ 40 :=
  Fast.cell (z := matrix_65_3) (Fast.bands [(0, 53, 13), (1, 54, 11), (2, 55, 9), (3, 56, 7), (4, 57, 5), (5, 58, 3), (6, 59, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_65_4 : CJ1.Block where
  bank := .leftLow
  cap := 40
  free := [(5, 0), (5, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129172494, 2116998893], [0, 0, 0, 0, 0, 0, 0, 0, 163185, 1177770], [0, 0, 0, 0, 0, 0, 2130692243, 2130628861], [0, 0, 0, 0, 946, 3483], [0, 0, 2130706390, 2130706353], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129335679], [0, 0, 0, 0, 0, 0, 0, 0, 0, 148995], [0, 0, 0, 0, 0, 0, 0, 2130693189], [0, 0, 0, 0, 0, 903], [0, 0, 0, 2130706391], [0, 1]]
  ]
private theorem cell_65_4 : (CJ0.blockMatrix source 65 ((4 : ℤ)-23)).rank ≤ 40 :=
  Fast.cell (z := matrix_65_4) (Fast.bands [(42, 42, 1), (43, 43, 2), (44, 44, 3), (45, 45, 4), (46, 46, 5), (47, 48, 5), (48, 50, 5), (49, 52, 5), (50, 54, 5), (51, 56, 5), (52, 58, 5), (53, 60, 4), (54, 62, 3), (55, 64, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_65 (u : ℕ) : ℕ :=
  match u with
  | 3 => 40
  | 4 => 40
  | u => nominal 65 u

private theorem bound_65 (u : ℕ) :
    (CJ0.blockMatrix source 65 ((u : ℤ)-23)).rank ≤ allowance_65 u := by
  unfold allowance_65
  split
  · exact cell_65_3
  · exact cell_65_4
  · exact (block_rank_le 65 _).trans (rank_le_nominal 65 _)

theorem grade_65 : (∑ u ∈ Finset.range (81-65), (CJ0.blockMatrix source 65 ((u : ℤ)-23)).rank) ≤ 307 := by
  refine (Finset.sum_le_sum fun u _ => bound_65 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_65)]
  decide +kernel

private def matrix_66_3 : CJ1.Block where
  bank := .leftLow
  cap := 36
  free := [(4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 211876, 1556640, 7134600, 26109600], [0, 0, 0, 0, 0, 0, 2130689137, 2130610224, 2130350393, 2129610833], [0, 0, 0, 0, 1081, 4048, 11341, 28168], [0, 0, 2130706387, 2130706346, 2130706269, 2130706125], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 194580, 1426920, 6527400], [0, 0, 0, 0, 0, 0, 0, 2130690218, 2130616388, 2130373793], [0, 0, 0, 0, 0, 1035, 3870, 10825], [0, 0, 0, 2130706388, 2130706348, 2130706273], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 178365, 1305480], [0, 0, 0, 0, 0, 0, 0, 0, 2130691253, 2130622283], [0, 0, 0, 0, 0, 0, 990, 3696], [0, 0, 0, 0, 2130706389, 2130706350], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 163185], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2130692243], [0, 0, 0, 0, 0, 0, 0, 946], [0, 0, 0, 0, 0, 2130706390], [0, 0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6135756, 55482900], [0, 0, 0, 0, 0, 0, 0, 0, 2130216878, 2127130553], [0, 0, 0, 0, 0, 0, 28380, 157036], [0, 0, 0, 0, 2130705487, 2130702907], [], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5483016], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2130259448], [0, 0, 0, 0, 0, 0, 0, 26488], [0, 0, 0, 0, 0, 2130705530], [], [0, 1]]
  ]
private theorem cell_66_3 : (CJ0.blockMatrix source 66 ((3 : ℤ)-23)).rank ≤ 36 :=
  Fast.cell (z := matrix_66_3) (Fast.bands [(43, 43, 1), (44, 44, 2), (45, 45, 3), (46, 46, 4), (47, 48, 4), (48, 50, 4), (49, 52, 4), (50, 54, 4), (51, 56, 4), (52, 58, 4), (53, 60, 4), (54, 62, 3), (55, 64, 2), (56, 66, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_66_4 : CJ1.Block where
  bank := .leftLow
  cap := 35
  free := [(5, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129172494], [0, 0, 0, 0, 0, 0, 0, 0, 163185], [0, 0, 0, 0, 0, 0, 2130692243], [0, 0, 0, 0, 946], [0, 0, 2130706390], [1]]
  ]
private theorem cell_66_4 : (CJ0.blockMatrix source 66 ((4 : ℤ)-23)).rank ≤ 35 :=
  Fast.cell (z := matrix_66_4) (Fast.bands [(43, 43, 1), (44, 44, 2), (45, 45, 3), (46, 46, 4), (47, 47, 5), (48, 49, 5), (49, 51, 5), (50, 53, 5), (51, 55, 5), (52, 57, 5), (53, 59, 5), (54, 61, 4), (55, 63, 3), (56, 65, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_66 (u : ℕ) : ℕ :=
  match u with
  | 3 => 36
  | 4 => 35
  | u => nominal 66 u

private theorem bound_66 (u : ℕ) :
    (CJ0.blockMatrix source 66 ((u : ℤ)-23)).rank ≤ allowance_66 u := by
  unfold allowance_66
  split
  · exact cell_66_3
  · exact cell_66_4
  · exact (block_rank_le 66 _).trans (rank_le_nominal 66 _)

theorem grade_66 : (∑ u ∈ Finset.range (81-66), (CJ0.blockMatrix source 66 ((u : ℤ)-23)).rank) ≤ 262 := by
  refine (Finset.sum_le_sum fun u _ => bound_66 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_66)]
  decide +kernel

private def matrix_67_2 : CJ1.Block where
  bank := .rightLow
  cap := 30
  free := [(3, 1), (5, 1), (7, 1)]
  vectors := [
    [[], [1], [2130706431], [0, 1]],
    [[], [1], [2130706432], [1], [2130706431], [0, 1]],
    [[], [1], [], [2], [2130706431], [1], [2130706431], [0, 1]]
  ]
private theorem cell_67_2 : (CJ0.blockMatrix source 67 ((2 : ℤ)-23)).rank ≤ 30 :=
  Fast.cell (z := matrix_67_2) (Fast.bands [(0, 56, 12), (1, 57, 10), (2, 58, 8), (3, 59, 6), (4, 60, 4), (5, 61, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_67_3 : CJ1.Block where
  bank := .leftLow
  cap := 32
  free := [(4, 0), (4, 1), (4, 2), (5, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 211876, 1556640, 7134600], [0, 0, 0, 0, 0, 0, 2130689137, 2130610224, 2130350393], [0, 0, 0, 0, 1081, 4048, 11341], [0, 0, 2130706387, 2130706346, 2130706269], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 194580, 1426920], [0, 0, 0, 0, 0, 0, 0, 2130690218, 2130616388], [0, 0, 0, 0, 0, 1035, 3870], [0, 0, 0, 2130706388, 2130706348], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 178365], [0, 0, 0, 0, 0, 0, 0, 0, 2130691253], [0, 0, 0, 0, 0, 0, 990], [0, 0, 0, 0, 2130706389], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6135756], [0, 0, 0, 0, 0, 0, 0, 0, 2130216878], [0, 0, 0, 0, 0, 0, 28380], [0, 0, 0, 0, 2130705487], [], [1]]
  ]
private theorem cell_67_3 : (CJ0.blockMatrix source 67 ((3 : ℤ)-23)).rank ≤ 32 :=
  Fast.cell (z := matrix_67_3) (Fast.bands [(44, 44, 1), (45, 45, 2), (46, 46, 3), (47, 47, 4), (48, 49, 4), (49, 51, 4), (50, 53, 4), (51, 55, 4), (52, 57, 4), (53, 59, 4), (54, 61, 4), (55, 63, 3), (56, 65, 2), (57, 67, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_67 (u : ℕ) : ℕ :=
  match u with
  | 2 => 30
  | 3 => 32
  | u => nominal 67 u

private theorem bound_67 (u : ℕ) :
    (CJ0.blockMatrix source 67 ((u : ℤ)-23)).rank ≤ allowance_67 u := by
  unfold allowance_67
  split
  · exact cell_67_2
  · exact cell_67_3
  · exact (block_rank_le 67 _).trans (rank_le_nominal 67 _)

theorem grade_67 : (∑ u ∈ Finset.range (81-67), (CJ0.blockMatrix source 67 ((u : ℤ)-23)).rank) ≤ 220 := by
  refine (Finset.sum_le_sum fun u _ => bound_67 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_67)]
  decide +kernel

private def matrix_68_2 : CJ1.Block where
  bank := .rightLow
  cap := 27
  free := [(2, 0), (3, 1), (4, 0), (5, 1), (7, 1), (9, 1)]
  vectors := [
    [[], [2130706432], [1]],
    [[], [2130706432], [], [0, 1]],
    [[], [2130706432], [], [2130706432], [1]],
    [[], [2130706431], [], [2130706432], [], [0, 1]],
    [[], [2130706432], [], [], [], [1], [2130706431], [0, 1]],
    [[], [], [], [1], [], [2], [2130706431], [1], [2130706431], [0, 1]]
  ]
private theorem cell_68_2 : (CJ0.blockMatrix source 68 ((2 : ℤ)-23)).rank ≤ 27 :=
  Fast.cell (z := matrix_68_2) (Fast.bands [(0, 58, 11), (1, 59, 9), (2, 60, 7), (3, 61, 5), (4, 62, 3), (5, 63, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_68_3 : CJ1.Block where
  bank := .leftLow
  cap := 28
  free := [(4, 0), (4, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 211876, 1556640], [0, 0, 0, 0, 0, 0, 2130689137, 2130610224], [0, 0, 0, 0, 1081, 4048], [0, 0, 2130706387, 2130706346], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 194580], [0, 0, 0, 0, 0, 0, 0, 2130690218], [0, 0, 0, 0, 0, 1035], [0, 0, 0, 2130706388], [0, 1]]
  ]
private theorem cell_68_3 : (CJ0.blockMatrix source 68 ((3 : ℤ)-23)).rank ≤ 28 :=
  Fast.cell (z := matrix_68_3) (Fast.bands [(45, 45, 1), (46, 46, 2), (47, 47, 3), (48, 48, 4), (49, 50, 4), (50, 52, 4), (51, 54, 4), (52, 56, 4), (53, 58, 4), (54, 60, 4), (55, 62, 4), (56, 64, 3), (57, 66, 2), (58, 68, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_68 (u : ℕ) : ℕ :=
  match u with
  | 2 => 27
  | 3 => 28
  | u => nominal 68 u

private theorem bound_68 (u : ℕ) :
    (CJ0.blockMatrix source 68 ((u : ℤ)-23)).rank ≤ allowance_68 u := by
  unfold allowance_68
  split
  · exact cell_68_2
  · exact cell_68_3
  · exact (block_rank_le 68 _).trans (rank_le_nominal 68 _)

theorem grade_68 : (∑ u ∈ Finset.range (81-68), (CJ0.blockMatrix source 68 ((u : ℤ)-23)).rank) ≤ 183 := by
  refine (Finset.sum_le_sum fun u _ => bound_68 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_68)]
  decide +kernel

private def matrix_69_1 : CJ1.Block where
  bank := .rightLow
  cap := 20
  free := [(3, 0), (5, 0)]
  vectors := [
    [[], [], [2130706432], [1]],
    [[], [], [2130706432], [], [2130706432], [1]]
  ]
private theorem cell_69_1 : (CJ0.blockMatrix source 69 ((1 : ℤ)-23)).rank ≤ 20 :=
  Fast.cell (z := matrix_69_1) (Fast.bands [(0, 59, 11), (1, 60, 9), (2, 61, 7), (3, 62, 5), (4, 63, 3), (5, 64, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_69_2 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130685608, 2130588833, 2130264257, 2129322753], [0, 0, 0, 0, 1225, 4655, 13248, 33464], [0, 0, 2130706384, 2130706339, 2130706253, 2130706089], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 2130686833, 2130595889, 2130291329], [0, 0, 0, 0, 0, 1176, 4464, 12690], [0, 0, 0, 2130706385, 2130706341, 2130706257], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130688009, 2130602657], [0, 0, 0, 0, 0, 0, 1128, 4277], [0, 0, 0, 0, 2130706386, 2130706343], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 2130689137], [0, 0, 0, 0, 0, 0, 0, 1081], [0, 0, 0, 0, 0, 2130706387], [0, 0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130070805, 2125984625], [0, 0, 0, 0, 0, 0, 34592, 194580], [0, 0, 0, 0, 2130705352, 2130702339], [], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 2130122693], [0, 0, 0, 0, 0, 0, 0, 32430], [0, 0, 0, 0, 0, 2130705398], [], [0, 1]]
  ]
private theorem cell_69_2 : (CJ0.blockMatrix source 69 ((2 : ℤ)-23)).rank ≤ 24 :=
  Fast.cell (z := matrix_69_2) (Fast.bands [(46, 46, 1), (47, 47, 2), (48, 48, 3), (49, 50, 3), (50, 52, 3), (51, 54, 3), (52, 56, 3), (53, 58, 3), (54, 60, 3), (55, 62, 3), (56, 64, 3), (57, 66, 2), (58, 68, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_69_3 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(4, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 211876], [0, 0, 0, 0, 0, 0, 2130689137], [0, 0, 0, 0, 1081], [0, 0, 2130706387], [1]]
  ]
private theorem cell_69_3 : (CJ0.blockMatrix source 69 ((3 : ℤ)-23)).rank ≤ 24 :=
  Fast.cell (z := matrix_69_3) (Fast.bands [(46, 46, 1), (47, 47, 2), (48, 48, 3), (49, 49, 4), (50, 51, 4), (51, 53, 4), (52, 55, 4), (53, 57, 4), (54, 59, 4), (55, 61, 4), (56, 63, 4), (57, 65, 3), (58, 67, 2), (59, 69, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_69 (u : ℕ) : ℕ :=
  match u with
  | 1 => 20
  | 2 => 24
  | 3 => 24
  | u => nominal 69 u

private theorem bound_69 (u : ℕ) :
    (CJ0.blockMatrix source 69 ((u : ℤ)-23)).rank ≤ allowance_69 u := by
  unfold allowance_69
  split
  · exact cell_69_1
  · exact cell_69_2
  · exact cell_69_3
  · exact (block_rank_le 69 _).trans (rank_le_nominal 69 _)

theorem grade_69 : (∑ u ∈ Finset.range (81-69), (CJ0.blockMatrix source 69 ((u : ℤ)-23)).rank) ≤ 149 := by
  refine (Finset.sum_le_sum fun u _ => bound_69 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_69)]
  decide +kernel

end Front6960ListBank

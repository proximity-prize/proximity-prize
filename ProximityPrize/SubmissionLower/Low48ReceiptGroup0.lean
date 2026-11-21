import ProximityPrize.SubmissionLower.Low48ReceiptGroup5

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Low48Receipt
open K1_13_1_1 (bandCount)

private def c0_0 := witness48 0 0 0 0 0 1 91
  0x0 (by decide +kernel)
private def chunks0 : List (Chunk 0) := [
  c0_0]
def rows0 := rowsFrom chunks0
theorem good0 : ∀ r ∈ rows0, good 0 r = true := rowsFrom_good chunks0
theorem sorted0 : rows0.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks0 0 (by decide +kernel)).1
theorem mass0 (i : Fin 51) :
    bandCount 0 (i.val : ℤ) 50 13 ≤ (rows0.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks0).filter _).length
  rw [mass_eq]
  have h : (List.range 51).all (fun j => decide (bandCount 0 (j : ℤ) 50 13 ≤ mass j chunks0)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total0 : (rows0.map (price 0)).sum = 91 :=
  (total_eq chunks0).trans (by decide +kernel)

private def c1_0 := witness48 1 3 0 64 64 1 91
  0x0 (by decide +kernel)
private def c1_1 := witness48 1 2 0 10001 10001 1 91
  0x0 (by decide +kernel)
private def c1_2 := witness48 1 1 0 20000 20000 1 91
  0x0 (by decide +kernel)
private def c1_3 := witness48 1 0 0 30000 30000 1 87
  0x91 (by decide +kernel)
private def chunks1 : List (Chunk 1) := [
  c1_0, c1_1, c1_2, c1_3]
def rows1 := rowsFrom chunks1
theorem good1 : ∀ r ∈ rows1, good 1 r = true := rowsFrom_good chunks1
theorem sorted1 : rows1.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks1 0 (by decide +kernel)).1
theorem mass1 (i : Fin 51) :
    bandCount 1 (i.val : ℤ) 50 13 ≤ (rows1.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks1).filter _).length
  rw [mass_eq]
  have h : (List.range 51).all (fun j => decide (bandCount 1 (j : ℤ) 50 13 ≤ mass j chunks1)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total1 : (rows1.map (price 1)).sum = 360 :=
  (total_eq chunks1).trans (by decide +kernel)

private def c2_0 := witness48 2 6 0 128 128 1 91
  0x0 (by decide +kernel)
private def c2_1 := witness48 2 5 0 10065 10065 1 91
  0x0 (by decide +kernel)
private def c2_2 := witness48 2 4 0 20002 20064 2 182
  0x0 (by decide +kernel)
private def c2_3 := witness48 2 3 0 30001 30064 2 178
  0x488 (by decide +kernel)
private def c2_4 := witness48 2 2 0 40000 40001 2 178
  0x488 (by decide +kernel)
private def c2_5 := witness48 2 1 0 50000 50000 1 87
  0x91 (by decide +kernel)
private def c2_6 := witness48 2 0 0 60000 60000 1 83
  0x111 (by decide +kernel)
private def chunks2 : List (Chunk 2) := [
  c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6]
def rows2 := rowsFrom chunks2
theorem good2 : ∀ r ∈ rows2, good 2 r = true := rowsFrom_good chunks2
theorem sorted2 : rows2.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks2 0 (by decide +kernel)).1
theorem mass2 (i : Fin 51) :
    bandCount 2 (i.val : ℤ) 50 13 ≤ (rows2.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks2).filter _).length
  rw [mass_eq]
  have h : (List.range 51).all (fun j => decide (bandCount 2 (j : ℤ) 50 13 ≤ mass j chunks2)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total2 : (rows2.map (price 2)).sum = 890 :=
  (total_eq chunks2).trans (by decide +kernel)

private def c3_0 := witness48 3 9 0 192 192 1 91
  0x0 (by decide +kernel)
private def c3_1 := witness48 3 8 0 10129 10129 1 91
  0x0 (by decide +kernel)
private def c3_2 := witness48 3 7 0 20066 20128 2 182
  0x0 (by decide +kernel)
private def c3_3 := witness48 3 6 0 30003 30128 3 269
  0x2440 (by decide +kernel)
private def c3_4 := witness48 3 5 0 40002 40065 3 269
  0x2440 (by decide +kernel)
private def c3_5 := witness48 3 4 0 50001 50064 3 265
  0x244488 (by decide +kernel)
private def c3_6 := witness48 3 3 0 60000 60064 3 261
  0x444488 (by decide +kernel)
private def c3_7 := witness48 3 2 0 70000 70001 2 170
  0x88891 (by decide +kernel)
private def c3_8 := witness48 3 1 0 80000 80000 1 83
  0x111 (by decide +kernel)
private def c3_9 := witness48 3 0 0 90000 90000 1 79
  0x191 (by decide +kernel)
private def chunks3 : List (Chunk 3) := [
  c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9]
def rows3 := rowsFrom chunks3
theorem good3 : ∀ r ∈ rows3, good 3 r = true := rowsFrom_good chunks3
theorem sorted3 : rows3.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks3 0 (by decide +kernel)).1
theorem mass3 (i : Fin 51) :
    bandCount 3 (i.val : ℤ) 50 13 ≤ (rows3.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks3).filter _).length
  rw [mass_eq]
  have h : (List.range 51).all (fun j => decide (bandCount 3 (j : ℤ) 50 13 ≤ mass j chunks3)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total3 : (rows3.map (price 3)).sum = 1760 :=
  (total_eq chunks3).trans (by decide +kernel)

private def c4_0 := witness48 4 12 0 256 256 1 91
  0x0 (by decide +kernel)
private def c4_1 := witness48 4 11 0 10193 10193 1 91
  0x0 (by decide +kernel)
private def c4_2 := witness48 4 10 0 20130 20192 2 182
  0x0 (by decide +kernel)
private def c4_3 := witness48 4 9 0 30067 30192 3 269
  0x2440 (by decide +kernel)
private def c4_4 := witness48 4 8 0 40004 40129 4 360
  0x12200 (by decide +kernel)
private def c4_5 := witness48 4 7 0 50003 50128 4 356
  0x1222440 (by decide +kernel)
private def c4_6 := witness48 4 6 0 60002 60128 5 439
  0x1111220488 (by decide +kernel)
private def c4_7 := witness48 4 5 0 70001 70065 4 348
  0x222244488 (by decide +kernel)
private def c4_8 := witness48 4 4 0 80000 80064 4 344
  0x222444488 (by decide +kernel)
private def c4_9 := witness48 4 3 0 90000 90064 3 249
  0x64488891 (by decide +kernel)
private def c4_10 := witness48 4 2 0 100000 100001 2 162
  0xc8911 (by decide +kernel)
private def c4_11 := witness48 4 1 0 110000 110000 1 79
  0x191 (by decide +kernel)
private def c4_12 := witness48 4 0 0 120000 120000 1 75
  0x211 (by decide +kernel)
private def chunks4 : List (Chunk 4) := [
  c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12]
def rows4 := rowsFrom chunks4
theorem good4 : ∀ r ∈ rows4, good 4 r = true := rowsFrom_good chunks4
theorem sorted4 : rows4.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks4 0 (by decide +kernel)).1
theorem mass4 (i : Fin 51) :
    bandCount 4 (i.val : ℤ) 50 13 ≤ (rows4.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks4).filter _).length
  rw [mass_eq]
  have h : (List.range 51).all (fun j => decide (bandCount 4 (j : ℤ) 50 13 ≤ mass j chunks4)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total4 : (rows4.map (price 4)).sum = 3045 :=
  (total_eq chunks4).trans (by decide +kernel)

end Low48Receipt

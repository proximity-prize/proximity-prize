import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptBase

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Low51EdgeRankReceipt
open K1_13_1_1 (bandCount)

def cert0_0 := witnessLow51 0 0 0 0 0 1 94
  0x0 (by decide +kernel)
def chunks0 : List (Chunk 0) := [
  cert0_0]

def rows0 := rowsFrom chunks0

theorem good0 : ∀ r ∈ rows0, good 0 r = true := rowsFrom_good chunks0

theorem sorted0 : rows0.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks0 0 (by decide +kernel)).1

theorem mass0 (i : Fin 54) :
    bandCount 0 (i.val : ℤ) 53 13 ≤ (rows0.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks0).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 0 (j : ℤ) 53 13 ≤ mass j chunks0)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total0 : (rows0.map (price 0)).sum = 94 :=
  (total_eq chunks0).trans (by decide +kernel)

def cert1_0 := witnessLow51 1 3 0 64 64 1 94
  0x0 (by decide +kernel)
def cert1_1 := witnessLow51 1 2 0 10001 10001 1 94
  0x0 (by decide +kernel)
def cert1_2 := witnessLow51 1 1 0 20000 20000 1 94
  0x0 (by decide +kernel)
def cert1_3 := witnessLow51 1 0 0 30000 30000 1 90
  0x91 (by decide +kernel)
def chunks1 : List (Chunk 1) := [
  cert1_0, cert1_1, cert1_2, cert1_3]

def rows1 := rowsFrom chunks1

theorem good1 : ∀ r ∈ rows1, good 1 r = true := rowsFrom_good chunks1

theorem sorted1 : rows1.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks1 0 (by decide +kernel)).1

theorem mass1 (i : Fin 54) :
    bandCount 1 (i.val : ℤ) 53 13 ≤ (rows1.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks1).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 1 (j : ℤ) 53 13 ≤ mass j chunks1)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total1 : (rows1.map (price 1)).sum = 372 :=
  (total_eq chunks1).trans (by decide +kernel)

def cert2_0 := witnessLow51 2 6 0 128 128 1 94
  0x0 (by decide +kernel)
def cert2_1 := witnessLow51 2 5 0 10065 10065 1 94
  0x0 (by decide +kernel)
def cert2_2 := witnessLow51 2 4 0 20002 20064 2 188
  0x0 (by decide +kernel)
def cert2_3 := witnessLow51 2 3 0 30001 30064 2 184
  0x488 (by decide +kernel)
def cert2_4 := witnessLow51 2 2 0 40000 40001 2 184
  0x488 (by decide +kernel)
def cert2_5 := witnessLow51 2 1 0 50000 50000 1 90
  0x91 (by decide +kernel)
def cert2_6 := witnessLow51 2 0 0 60000 60000 1 86
  0x111 (by decide +kernel)
def chunks2 : List (Chunk 2) := [
  cert2_0, cert2_1, cert2_2, cert2_3, cert2_4, cert2_5, cert2_6]

def rows2 := rowsFrom chunks2

theorem good2 : ∀ r ∈ rows2, good 2 r = true := rowsFrom_good chunks2

theorem sorted2 : rows2.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks2 0 (by decide +kernel)).1

theorem mass2 (i : Fin 54) :
    bandCount 2 (i.val : ℤ) 53 13 ≤ (rows2.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks2).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 2 (j : ℤ) 53 13 ≤ mass j chunks2)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total2 : (rows2.map (price 2)).sum = 920 :=
  (total_eq chunks2).trans (by decide +kernel)

def cert3_0 := witnessLow51 3 9 0 192 192 1 94
  0x0 (by decide +kernel)
def cert3_1 := witnessLow51 3 8 0 10129 10129 1 94
  0x0 (by decide +kernel)
def cert3_2 := witnessLow51 3 7 0 20066 20128 2 188
  0x0 (by decide +kernel)
def cert3_3 := witnessLow51 3 6 0 30003 30128 3 278
  0x2440 (by decide +kernel)
def cert3_4 := witnessLow51 3 5 0 40002 40065 3 278
  0x2440 (by decide +kernel)
def cert3_5 := witnessLow51 3 4 0 50001 50064 3 274
  0x244488 (by decide +kernel)
def cert3_6 := witnessLow51 3 3 0 60000 60064 3 270
  0x444488 (by decide +kernel)
def cert3_7 := witnessLow51 3 2 0 70000 70001 2 176
  0x88891 (by decide +kernel)
def cert3_8 := witnessLow51 3 1 0 80000 80000 1 86
  0x111 (by decide +kernel)
def cert3_9 := witnessLow51 3 0 0 90000 90000 1 82
  0x191 (by decide +kernel)
def chunks3 : List (Chunk 3) := [
  cert3_0, cert3_1, cert3_2, cert3_3, cert3_4, cert3_5, cert3_6, cert3_7, cert3_8, cert3_9]

def rows3 := rowsFrom chunks3

theorem good3 : ∀ r ∈ rows3, good 3 r = true := rowsFrom_good chunks3

theorem sorted3 : rows3.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks3 0 (by decide +kernel)).1

theorem mass3 (i : Fin 54) :
    bandCount 3 (i.val : ℤ) 53 13 ≤ (rows3.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks3).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 3 (j : ℤ) 53 13 ≤ mass j chunks3)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total3 : (rows3.map (price 3)).sum = 1820 :=
  (total_eq chunks3).trans (by decide +kernel)

def cert4_0 := witnessLow51 4 12 0 256 256 1 94
  0x0 (by decide +kernel)
def cert4_1 := witnessLow51 4 11 0 10193 10193 1 94
  0x0 (by decide +kernel)
def cert4_2 := witnessLow51 4 10 0 20130 20192 2 188
  0x0 (by decide +kernel)
def cert4_3 := witnessLow51 4 9 0 30067 30192 3 278
  0x2440 (by decide +kernel)
def cert4_4 := witnessLow51 4 8 0 40004 40129 4 372
  0x12200 (by decide +kernel)
def cert4_5 := witnessLow51 4 7 0 50003 50128 4 368
  0x1222440 (by decide +kernel)
def cert4_6 := witnessLow51 4 6 0 60002 60128 5 454
  0x1111220488 (by decide +kernel)
def cert4_7 := witnessLow51 4 5 0 70001 70065 4 360
  0x222244488 (by decide +kernel)
def cert4_8 := witnessLow51 4 4 0 80000 80064 4 356
  0x222444488 (by decide +kernel)
def cert4_9 := witnessLow51 4 3 0 90000 90064 3 258
  0x64488891 (by decide +kernel)
def cert4_10 := witnessLow51 4 2 0 100000 100001 2 168
  0xc8911 (by decide +kernel)
def cert4_11 := witnessLow51 4 1 0 110000 110000 1 82
  0x191 (by decide +kernel)
def cert4_12 := witnessLow51 4 0 0 120000 120000 1 78
  0x211 (by decide +kernel)
def chunks4 : List (Chunk 4) := [
  cert4_0, cert4_1, cert4_2, cert4_3, cert4_4, cert4_5, cert4_6, cert4_7, cert4_8, cert4_9,
  cert4_10, cert4_11, cert4_12]

def rows4 := rowsFrom chunks4

theorem good4 : ∀ r ∈ rows4, good 4 r = true := rowsFrom_good chunks4

theorem sorted4 : rows4.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks4 0 (by decide +kernel)).1

theorem mass4 (i : Fin 54) :
    bandCount 4 (i.val : ℤ) 53 13 ≤ (rows4.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks4).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 4 (j : ℤ) 53 13 ≤ mass j chunks4)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total4 : (rows4.map (price 4)).sum = 3150 :=
  (total_eq chunks4).trans (by decide +kernel)

end Low51EdgeRankReceipt

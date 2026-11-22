import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup5

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert6_0 := witness 6 18 0 384 384 1 96
  0x0 (by decide +kernel)
private def cert6_1 := witness 6 17 0 10321 10321 1 96
  0x0 (by decide +kernel)
private def cert6_2 := witness 6 16 0 20258 20320 2 192
  0x0 (by decide +kernel)
private def cert6_3 := witness 6 15 0 30195 30320 3 284
  0x2440 (by decide +kernel)
private def cert6_4 := witness 6 14 0 40132 40257 4 380
  0x12200 (by decide +kernel)
private def cert6_5 := witness 6 13 0 50069 50256 5 472
  0x9112200 (by decide +kernel)
private def cert6_6 := witness 6 12 0 60006 60256 7 656
  0x44448812200 (by decide +kernel)
private def cert6_7 := witness 6 11 0 70005 70193 7 652
  0x4444889102440 (by decide +kernel)
private def cert6_8 := witness 6 10 0 80004 80192 8 740
  0x2224444881220488 (by decide +kernel)
private def cert6_9 := witness 6 9 0 90003 90192 8 728
  0x322444489111220488 (by decide +kernel)
private def cert6_10 := witness 6 8 0 100002 100129 8 724
  0x322444888910444488 (by decide +kernel)
private def cert6_11 := witness 6 7 0 110001 110128 7 624
  0x644c8911122444488 (by decide +kernel)
private def cert6_12 := witness 6 6 0 120000 120128 7 612
  0x844c8911322444488 (by decide +kernel)
private def cert6_13 := witness 6 5 0 130000 130065 5 428
  0x21132264488891 (by decide +kernel)
private def cert6_14 := witness 6 4 0 140000 140064 4 332
  0x422844c8911 (by decide +kernel)
private def cert6_15 := witness 6 3 0 150000 150064 3 240
  0xa4508991 (by decide +kernel)
private def cert6_16 := witness 6 2 0 160000 160001 2 156
  0x148a11 (by decide +kernel)
private def cert6_17 := witness 6 1 0 170000 170000 1 76
  0x291 (by decide +kernel)
private def cert6_18 := witness 6 0 0 180000 180000 1 72
  0x311 (by decide +kernel)
private def chunks6 : List (Chunk 6) := [
  cert6_0, cert6_1, cert6_2, cert6_3, cert6_4, cert6_5, cert6_6, cert6_7, cert6_8, cert6_9,
  cert6_10, cert6_11, cert6_12, cert6_13, cert6_14, cert6_15, cert6_16, cert6_17, cert6_18]

def rows6 := rowsFrom chunks6

theorem good6 : ∀ r ∈ rows6, good 6 r = true := rowsFrom_good chunks6

theorem sorted6 : rows6.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks6 0 (by decide +kernel)).1

theorem mass6 (i : Fin 54) :
    bandCount 6 (i.val : ℤ) 53 13 ≤ (rows6.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks6).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 6 (j : ℤ) 53 13 ≤ mass j chunks6)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total6 : (rows6.map (price 6)).sum = 7560 :=
  (total_eq chunks6).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

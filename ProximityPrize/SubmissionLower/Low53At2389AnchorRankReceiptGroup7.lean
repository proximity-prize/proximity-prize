import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup6

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert7_0 := witness 7 21 0 448 448 1 96
  0x0 (by decide +kernel)
private def cert7_1 := witness 7 20 0 10385 10385 1 96
  0x0 (by decide +kernel)
private def cert7_2 := witness 7 19 0 20322 20384 2 192
  0x0 (by decide +kernel)
private def cert7_3 := witness 7 18 0 30259 30384 3 284
  0x2440 (by decide +kernel)
private def cert7_4 := witness 7 17 0 40196 40321 4 380
  0x12200 (by decide +kernel)
private def cert7_5 := witness 7 16 0 50133 50320 5 472
  0x9112200 (by decide +kernel)
private def cert7_6 := witness 7 15 0 60070 60320 7 656
  0x44448812200 (by decide +kernel)
private def cert7_7 := witness 7 14 0 70007 70257 8 748
  0x22224448812200 (by decide +kernel)
private def cert7_8 := witness 7 13 0 80006 80256 9 836
  0x11122224409102440 (by decide +kernel)
private def cert7_9 := witness 7 12 0 90005 90256 10 916
  0xc89111224444881220488 (by decide +kernel)
private def cert7_10 := witness 7 11 0 100004 100193 10 912
  0xc89112222441111220488 (by decide +kernel)
private def cert7_11 := witness 7 10 0 110003 110192 10 900
  0xc8991222244888910444488 (by decide +kernel)
private def cert7_12 := witness 7 9 0 120002 120192 10 888
  0x108991222644888910444488 (by decide +kernel)
private def cert7_13 := witness 7 8 0 130001 130129 9 788
  0x21132264488891322444488 (by decide +kernel)
private def cert7_14 := witness 7 7 0 140000 140128 8 692
  0x422844c8911322444488 (by decide +kernel)
private def cert7_15 := witness 7 6 0 150000 150128 7 584
  0xa450899142264488891 (by decide +kernel)
private def cert7_16 := witness 7 5 0 160000 160065 5 408
  0x291422844c8911 (by decide +kernel)
private def cert7_17 := witness 7 4 0 170000 170064 4 316
  0x522a4508991 (by decide +kernel)
private def cert7_18 := witness 7 3 0 180000 180064 3 228
  0xc4548a11 (by decide +kernel)
private def cert7_19 := witness 7 2 0 190000 190001 2 148
  0x188a91 (by decide +kernel)
private def cert7_20 := witness 7 1 0 200000 200000 1 72
  0x311 (by decide +kernel)
private def cert7_21 := witness 7 0 0 210000 210000 1 68
  0x391 (by decide +kernel)
private def chunks7 : List (Chunk 7) := [
  cert7_0, cert7_1, cert7_2, cert7_3, cert7_4, cert7_5, cert7_6, cert7_7, cert7_8, cert7_9,
  cert7_10, cert7_11, cert7_12, cert7_13, cert7_14, cert7_15, cert7_16, cert7_17, cert7_18, cert7_19,
  cert7_20, cert7_21]

def rows7 := rowsFrom chunks7

theorem good7 : ∀ r ∈ rows7, good 7 r = true := rowsFrom_good chunks7

theorem sorted7 : rows7.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks7 0 (by decide +kernel)).1

theorem mass7 (i : Fin 54) :
    bandCount 7 (i.val : ℤ) 53 13 ≤ (rows7.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks7).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 7 (j : ℤ) 53 13 ≤ mass j chunks7)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total7 : (rows7.map (price 7)).sum = 10680 :=
  (total_eq chunks7).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup3

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert4_0 := witness 4 12 0 256 256 1 96
  0x0 (by decide +kernel)
private def cert4_1 := witness 4 11 0 10193 10193 1 96
  0x0 (by decide +kernel)
private def cert4_2 := witness 4 10 0 20130 20192 2 192
  0x0 (by decide +kernel)
private def cert4_3 := witness 4 9 0 30067 30192 3 284
  0x2440 (by decide +kernel)
private def cert4_4 := witness 4 8 0 40004 40129 4 380
  0x12200 (by decide +kernel)
private def cert4_5 := witness 4 7 0 50003 50128 4 376
  0x1222440 (by decide +kernel)
private def cert4_6 := witness 4 6 0 60002 60128 5 464
  0x1111220488 (by decide +kernel)
private def cert4_7 := witness 4 5 0 70001 70065 4 368
  0x222244488 (by decide +kernel)
private def cert4_8 := witness 4 4 0 80000 80064 4 364
  0x222444488 (by decide +kernel)
private def cert4_9 := witness 4 3 0 90000 90064 3 264
  0x64488891 (by decide +kernel)
private def cert4_10 := witness 4 2 0 100000 100001 2 172
  0xc8911 (by decide +kernel)
private def cert4_11 := witness 4 1 0 110000 110000 1 84
  0x191 (by decide +kernel)
private def cert4_12 := witness 4 0 0 120000 120000 1 80
  0x211 (by decide +kernel)
private def chunks4 : List (Chunk 4) := [
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

theorem total4 : (rows4.map (price 4)).sum = 3220 :=
  (total_eq chunks4).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

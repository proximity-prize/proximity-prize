import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup2

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert3_0 := witness 3 9 0 192 192 1 96
  0x0 (by decide +kernel)
private def cert3_1 := witness 3 8 0 10129 10129 1 96
  0x0 (by decide +kernel)
private def cert3_2 := witness 3 7 0 20066 20128 2 192
  0x0 (by decide +kernel)
private def cert3_3 := witness 3 6 0 30003 30128 3 284
  0x2440 (by decide +kernel)
private def cert3_4 := witness 3 5 0 40002 40065 3 284
  0x2440 (by decide +kernel)
private def cert3_5 := witness 3 4 0 50001 50064 3 280
  0x244488 (by decide +kernel)
private def cert3_6 := witness 3 3 0 60000 60064 3 276
  0x444488 (by decide +kernel)
private def cert3_7 := witness 3 2 0 70000 70001 2 180
  0x88891 (by decide +kernel)
private def cert3_8 := witness 3 1 0 80000 80000 1 88
  0x111 (by decide +kernel)
private def cert3_9 := witness 3 0 0 90000 90000 1 84
  0x191 (by decide +kernel)
private def chunks3 : List (Chunk 3) := [
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

theorem total3 : (rows3.map (price 3)).sum = 1860 :=
  (total_eq chunks3).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

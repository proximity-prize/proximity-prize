import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptBase

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert0_0 := witness 0 0 0 0 0 1 96
  0x0 (by decide +kernel)
private def chunks0 : List (Chunk 0) := [
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

theorem total0 : (rows0.map (price 0)).sum = 96 :=
  (total_eq chunks0).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

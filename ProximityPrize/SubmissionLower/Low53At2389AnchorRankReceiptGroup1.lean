import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup0

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert1_0 := witness 1 3 0 64 64 1 96
  0x0 (by decide +kernel)
private def cert1_1 := witness 1 2 0 10001 10001 1 96
  0x0 (by decide +kernel)
private def cert1_2 := witness 1 1 0 20000 20000 1 96
  0x0 (by decide +kernel)
private def cert1_3 := witness 1 0 0 30000 30000 1 92
  0x91 (by decide +kernel)
private def chunks1 : List (Chunk 1) := [
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

theorem total1 : (rows1.map (price 1)).sum = 380 :=
  (total_eq chunks1).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

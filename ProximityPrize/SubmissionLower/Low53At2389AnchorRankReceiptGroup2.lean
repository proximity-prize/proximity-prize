import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup1

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert2_0 := witness 2 6 0 128 128 1 96
  0x0 (by decide +kernel)
private def cert2_1 := witness 2 5 0 10065 10065 1 96
  0x0 (by decide +kernel)
private def cert2_2 := witness 2 4 0 20002 20064 2 192
  0x0 (by decide +kernel)
private def cert2_3 := witness 2 3 0 30001 30064 2 188
  0x488 (by decide +kernel)
private def cert2_4 := witness 2 2 0 40000 40001 2 188
  0x488 (by decide +kernel)
private def cert2_5 := witness 2 1 0 50000 50000 1 92
  0x91 (by decide +kernel)
private def cert2_6 := witness 2 0 0 60000 60000 1 88
  0x111 (by decide +kernel)
private def chunks2 : List (Chunk 2) := [
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

theorem total2 : (rows2.map (price 2)).sum = 940 :=
  (total_eq chunks2).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

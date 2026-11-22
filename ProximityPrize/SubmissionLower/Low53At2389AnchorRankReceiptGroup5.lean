import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup4

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert5_0 := witness 5 15 0 320 320 1 96
  0x0 (by decide +kernel)
private def cert5_1 := witness 5 14 0 10257 10257 1 96
  0x0 (by decide +kernel)
private def cert5_2 := witness 5 13 0 20194 20256 2 192
  0x0 (by decide +kernel)
private def cert5_3 := witness 5 12 0 30131 30256 3 284
  0x2440 (by decide +kernel)
private def cert5_4 := witness 5 11 0 40068 40193 4 380
  0x12200 (by decide +kernel)
private def cert5_5 := witness 5 10 0 50005 50192 5 472
  0x9112200 (by decide +kernel)
private def cert5_6 := witness 5 9 0 60004 60192 6 560
  0x8889102440 (by decide +kernel)
private def cert5_7 := witness 5 8 0 70003 70129 6 556
  0x888911220488 (by decide +kernel)
private def cert5_8 := witness 5 7 0 80002 80128 6 552
  0x889111220488 (by decide +kernel)
private def cert5_9 := witness 5 6 0 90001 90128 6 540
  0xc8911122444488 (by decide +kernel)
private def cert5_10 := witness 5 5 0 100000 100065 5 448
  0x191222444488 (by decide +kernel)
private def cert5_11 := witness 5 4 0 110000 110064 4 348
  0x32264488891 (by decide +kernel)
private def cert5_12 := witness 5 3 0 120000 120064 3 252
  0x844c8911 (by decide +kernel)
private def cert5_13 := witness 5 2 0 130000 130001 2 164
  0x108991 (by decide +kernel)
private def cert5_14 := witness 5 1 0 140000 140000 1 80
  0x211 (by decide +kernel)
private def cert5_15 := witness 5 0 0 150000 150000 1 76
  0x291 (by decide +kernel)
private def chunks5 : List (Chunk 5) := [
  cert5_0, cert5_1, cert5_2, cert5_3, cert5_4, cert5_5, cert5_6, cert5_7, cert5_8, cert5_9,
  cert5_10, cert5_11, cert5_12, cert5_13, cert5_14, cert5_15]

def rows5 := rowsFrom chunks5

theorem good5 : ∀ r ∈ rows5, good 5 r = true := rowsFrom_good chunks5

theorem sorted5 : rows5.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks5 0 (by decide +kernel)).1

theorem mass5 (i : Fin 54) :
    bandCount 5 (i.val : ℤ) 53 13 ≤ (rows5.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks5).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 5 (j : ℤ) 53 13 ≤ mass j chunks5)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total5 : (rows5.map (price 5)).sum = 5096 :=
  (total_eq chunks5).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup7

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert8_0 := witness 8 24 0 512 512 1 96
  0x0 (by decide +kernel)
private def cert8_1 := witness 8 23 0 10449 10449 1 96
  0x0 (by decide +kernel)
private def cert8_2 := witness 8 22 0 20386 20448 2 192
  0x0 (by decide +kernel)
private def cert8_3 := witness 8 21 0 30323 30448 3 284
  0x2440 (by decide +kernel)
private def cert8_4 := witness 8 20 0 40260 40385 4 380
  0x12200 (by decide +kernel)
private def cert8_5 := witness 8 19 0 50197 50384 5 472
  0x9112200 (by decide +kernel)
private def cert8_6 := witness 8 18 0 60134 60384 7 656
  0x44448812200 (by decide +kernel)
private def cert8_7 := witness 8 17 0 70071 70321 8 748
  0x22224448812200 (by decide +kernel)
private def cert8_8 := witness 8 16 0 80008 80320 10 932
  0x88911122048812200 (by decide +kernel)
private def cert8_9 := witness 8 15 0 90007 90320 11 1012
  0x6448889122224409102440 (by decide +kernel)
private def cert8_10 := witness 8 14 0 100006 100257 12 1100
  0x3224448889104444881220488 (by decide +kernel)
private def cert8_11 := witness 8 13 0 110005 110256 12 1088
  0x322644888912222441111220488 (by decide +kernel)
private def cert8_12 := witness 8 12 0 120004 120256 13 1164
  0x211322444c89111220888910444488 (by decide +kernel)
private def cert8_13 := witness 8 11 0 130003 130193 12 1064
  0x422644c8911122644888910444488 (by decide +kernel)
private def cert8_14 := witness 8 10 0 140002 140192 12 1052
  0x422844c8911322444488322444488 (by decide +kernel)
private def cert8_15 := witness 8 9 0 150001 150192 11 944
  0xa450899142264488891322444488 (by decide +kernel)
private def cert8_16 := witness 8 8 0 160000 160129 10 848
  0x148a1142264488a11322444488 (by decide +kernel)
private def cert8_17 := witness 8 7 0 170000 170128 8 660
  0x522a450899142264488891 (by decide +kernel)
private def cert8_18 := witness 8 6 0 180000 180128 7 556
  0xc4548a11522844c8911 (by decide +kernel)
private def cert8_19 := witness 8 5 0 190000 190065 5 388
  0x311522a4508991 (by decide +kernel)
private def cert8_20 := witness 8 4 0 200000 200064 4 300
  0x622c4548a11 (by decide +kernel)
private def cert8_21 := witness 8 3 0 210000 210064 3 216
  0xe4588a91 (by decide +kernel)
private def cert8_22 := witness 8 2 0 220000 220001 2 140
  0x1c8b11 (by decide +kernel)
private def cert8_23 := witness 8 1 0 230000 230000 1 68
  0x391 (by decide +kernel)
private def cert8_24 := witness 8 0 0 240000 240000 1 64
  0x411 (by decide +kernel)
private def chunks8 : List (Chunk 8) := [
  cert8_0, cert8_1, cert8_2, cert8_3, cert8_4, cert8_5, cert8_6, cert8_7, cert8_8, cert8_9,
  cert8_10, cert8_11, cert8_12, cert8_13, cert8_14, cert8_15, cert8_16, cert8_17, cert8_18, cert8_19,
  cert8_20, cert8_21, cert8_22, cert8_23, cert8_24]

def rows8 := rowsFrom chunks8

theorem good8 : ∀ r ∈ rows8, good 8 r = true := rowsFrom_good chunks8

theorem sorted8 : rows8.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks8 0 (by decide +kernel)).1

theorem mass8 (i : Fin 54) :
    bandCount 8 (i.val : ℤ) 53 13 ≤ (rows8.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks8).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 8 (j : ℤ) 53 13 ≤ mass j chunks8)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total8 : (rows8.map (price 8)).sum = 14520 :=
  (total_eq chunks8).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

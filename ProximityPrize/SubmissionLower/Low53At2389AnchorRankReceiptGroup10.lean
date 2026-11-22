import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup9

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert10_0 := witness 10 30 0 640 640 1 96
  0x0 (by decide +kernel)
private def cert10_1 := witness 10 29 0 10577 10577 1 96
  0x0 (by decide +kernel)
private def cert10_2 := witness 10 28 0 20514 20576 2 192
  0x0 (by decide +kernel)
private def cert10_3 := witness 10 27 0 30451 30576 3 284
  0x2440 (by decide +kernel)
private def cert10_4 := witness 10 26 0 40388 40513 4 380
  0x12200 (by decide +kernel)
private def cert10_5 := witness 10 25 0 50325 50512 5 472
  0x9112200 (by decide +kernel)
private def cert10_6 := witness 10 24 0 60262 60512 7 656
  0x44448812200 (by decide +kernel)
private def cert10_7 := witness 10 23 0 70199 70449 8 748
  0x22224448812200 (by decide +kernel)
private def cert10_8 := witness 10 22 0 80136 80448 10 932
  0x88911122048812200 (by decide +kernel)
private def cert10_9 := witness 10 21 0 90073 90448 12 1108
  0x32244448911122048812200 (by decide +kernel)
private def cert10_10 := witness 10 20 0 100010 100385 14 1292
  0xc8911222244111122048812200 (by decide +kernel)
private def cert10_11 := witness 10 19 0 110009 110384 15 1372
  0x644c891112244448822224409102440 (by decide +kernel)
private def cert10_12 := witness 10 18 0 120008 120384 17 1540
  0x211322444c891112208889104444881220488 (by decide +kernel)
private def cert10_13 := witness 10 17 0 130007 130321 17 1528
  0x211322644888913224444882222441111220488 (by decide +kernel)
private def cert10_14 := witness 10 16 0 140006 140320 18 1604
  0x108a11322444c89111220c89111220888910444488 (by decide +kernel)
private def cert10_15 := witness 10 15 0 150005 150320 18 1580
  0x148a11322844c8911122644888910644888910444488 (by decide +kernel)
private def cert10_16 := witness 10 14 0 160004 160257 18 1568
  0x148a1142264488a11322444488322444488322444488 (by decide +kernel)
private def cert10_17 := witness 10 13 0 170003 170256 17 1460
  0x291522844c8a1132244448a11322444488322444488 (by decide +kernel)
private def cert10_18 := witness 10 12 0 180002 180256 17 1436
  0x31152284548a1132244508991222244211322444488 (by decide +kernel)
private def cert10_19 := witness 10 11 0 190001 190193 15 1248
  0xc4548a9142264548a1132244448a11322444488 (by decide +kernel)
private def cert10_20 := witness 10 10 0 200000 200192 14 1144
  0x188b1152284548a1132244548a11322444488 (by decide +kernel)
private def cert10_21 := witness 10 9 0 210000 210192 12 948
  0x722c4548b11522844c8a9142264488891 (by decide +kernel)
private def cert10_22 := witness 10 8 0 220000 220129 10 768
  0x1c8b11622a4508b11522844c8911 (by decide +kernel)
private def cert10_23 := witness 10 7 0 230000 230128 8 596
  0x722e4588a91622a4508991 (by decide +kernel)
private def cert10_24 := witness 10 6 0 240000 240128 7 500
  0x1045c8b11722c4548a11 (by decide +kernel)
private def cert10_25 := witness 10 5 0 250000 250065 5 348
  0x411722e4588a91 (by decide +kernel)
private def cert10_26 := witness 10 4 0 260000 260064 4 268
  0x823045c8b11 (by decide +kernel)
private def cert10_27 := witness 10 3 0 270000 270064 3 192
  0x124608b91 (by decide +kernel)
private def cert10_28 := witness 10 2 0 280000 280001 2 124
  0x248c11 (by decide +kernel)
private def cert10_29 := witness 10 1 0 290000 290000 1 60
  0x491 (by decide +kernel)
private def cert10_30 := witness 10 0 0 300000 300000 1 56
  0x511 (by decide +kernel)
private def chunks10 : List (Chunk 10) := [
  cert10_0, cert10_1, cert10_2, cert10_3, cert10_4, cert10_5, cert10_6, cert10_7, cert10_8, cert10_9,
  cert10_10, cert10_11, cert10_12, cert10_13, cert10_14, cert10_15, cert10_16, cert10_17, cert10_18, cert10_19,
  cert10_20, cert10_21, cert10_22, cert10_23, cert10_24, cert10_25, cert10_26, cert10_27, cert10_28, cert10_29,
  cert10_30]

def rows10 := rowsFrom chunks10

theorem good10 : ∀ r ∈ rows10, good 10 r = true := rowsFrom_good chunks10

theorem sorted10 : rows10.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks10 0 (by decide +kernel)).1

theorem mass10 (i : Fin 54) :
    bandCount 10 (i.val : ℤ) 53 13 ≤ (rows10.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks10).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 10 (j : ℤ) 53 13 ≤ mass j chunks10)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total10 : (rows10.map (price 10)).sum = 24596 :=
  (total_eq chunks10).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

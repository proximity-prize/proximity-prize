import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup8

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert9_0 := witness 9 27 0 576 576 1 96
  0x0 (by decide +kernel)
private def cert9_1 := witness 9 26 0 10513 10513 1 96
  0x0 (by decide +kernel)
private def cert9_2 := witness 9 25 0 20450 20512 2 192
  0x0 (by decide +kernel)
private def cert9_3 := witness 9 24 0 30387 30512 3 284
  0x2440 (by decide +kernel)
private def cert9_4 := witness 9 23 0 40324 40449 4 380
  0x12200 (by decide +kernel)
private def cert9_5 := witness 9 22 0 50261 50448 5 472
  0x9112200 (by decide +kernel)
private def cert9_6 := witness 9 21 0 60198 60448 7 656
  0x44448812200 (by decide +kernel)
private def cert9_7 := witness 9 20 0 70135 70385 8 748
  0x22224448812200 (by decide +kernel)
private def cert9_8 := witness 9 19 0 80072 80384 10 932
  0x88911122048812200 (by decide +kernel)
private def cert9_9 := witness 9 18 0 90009 90384 12 1108
  0x32244448911122048812200 (by decide +kernel)
private def cert9_10 := witness 9 17 0 100008 100321 13 1196
  0x19122244448822224409102440 (by decide +kernel)
private def cert9_11 := witness 9 16 0 110007 110320 14 1276
  0xc89912222448889104444881220488 (by decide +kernel)
private def cert9_12 := witness 9 15 0 120006 120320 15 1352
  0x844c89113224444882222441111220488 (by decide +kernel)
private def cert9_13 := witness 9 14 0 130005 130257 15 1340
  0x844c8991222244c89111220888910444488 (by decide +kernel)
private def cert9_14 := witness 9 13 0 140004 140256 15 1328
  0x84508991222644888910644888910444488 (by decide +kernel)
private def cert9_15 := witness 9 12 0 150003 150256 15 1304
  0xa450899142264488891322444488322444488 (by decide +kernel)
private def cert9_16 := witness 9 11 0 160002 160193 14 1208
  0x148a1142264488a11322444488322444488 (by decide +kernel)
private def cert9_17 := witness 9 10 0 170001 170192 13 1100
  0x291522844c8a1132244448a11322444488 (by decide +kernel)
private def cert9_18 := witness 9 9 0 180000 180192 12 996
  0x622a4508a9142264488a11322444488 (by decide +kernel)
private def cert9_19 := witness 9 8 0 190000 190129 10 808
  0x188a91522844c8a9142264488891 (by decide +kernel)
private def cert9_20 := witness 9 7 0 200000 200128 8 628
  0x622c4548a11522844c8911 (by decide +kernel)
private def cert9_21 := witness 9 6 0 210000 210128 7 528
  0xe4588a91622a4508991 (by decide +kernel)
private def cert9_22 := witness 9 5 0 220000 220065 5 368
  0x391622c4548a11 (by decide +kernel)
private def cert9_23 := witness 9 4 0 230000 230064 4 284
  0x722e4588a91 (by decide +kernel)
private def cert9_24 := witness 9 3 0 240000 240064 3 204
  0x1045c8b11 (by decide +kernel)
private def cert9_25 := witness 9 2 0 250000 250001 2 132
  0x208b91 (by decide +kernel)
private def cert9_26 := witness 9 1 0 260000 260000 1 64
  0x411 (by decide +kernel)
private def cert9_27 := witness 9 0 0 270000 270000 1 60
  0x491 (by decide +kernel)
private def chunks9 : List (Chunk 9) := [
  cert9_0, cert9_1, cert9_2, cert9_3, cert9_4, cert9_5, cert9_6, cert9_7, cert9_8, cert9_9,
  cert9_10, cert9_11, cert9_12, cert9_13, cert9_14, cert9_15, cert9_16, cert9_17, cert9_18, cert9_19,
  cert9_20, cert9_21, cert9_22, cert9_23, cert9_24, cert9_25, cert9_26, cert9_27]

def rows9 := rowsFrom chunks9

theorem good9 : ∀ r ∈ rows9, good 9 r = true := rowsFrom_good chunks9

theorem sorted9 : rows9.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks9 0 (by decide +kernel)).1

theorem mass9 (i : Fin 54) :
    bandCount 9 (i.val : ℤ) 53 13 ≤ (rows9.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks9).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 9 (j : ℤ) 53 13 ≤ mass j chunks9)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total9 : (rows9.map (price 9)).sum = 19140 :=
  (total_eq chunks9).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

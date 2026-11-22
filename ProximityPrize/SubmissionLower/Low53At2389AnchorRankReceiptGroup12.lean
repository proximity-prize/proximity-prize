import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup11

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert12_0 := witness 12 36 0 768 768 1 96
  0x0 (by decide +kernel)
private def cert12_1 := witness 12 35 0 10705 10705 1 96
  0x0 (by decide +kernel)
private def cert12_2 := witness 12 34 0 20642 20704 2 192
  0x0 (by decide +kernel)
private def cert12_3 := witness 12 33 0 30579 30704 3 284
  0x2440 (by decide +kernel)
private def cert12_4 := witness 12 32 0 40516 40641 4 380
  0x12200 (by decide +kernel)
private def cert12_5 := witness 12 31 0 50453 50640 5 472
  0x9112200 (by decide +kernel)
private def cert12_6 := witness 12 30 0 60390 60640 7 656
  0x44448812200 (by decide +kernel)
private def cert12_7 := witness 12 29 0 70327 70577 8 748
  0x22224448812200 (by decide +kernel)
private def cert12_8 := witness 12 28 0 80264 80576 10 932
  0x88911122048812200 (by decide +kernel)
private def cert12_9 := witness 12 27 0 90201 90576 12 1108
  0x32244448911122048812200 (by decide +kernel)
private def cert12_10 := witness 12 26 0 100138 100513 14 1292
  0xc8911222244111122048812200 (by decide +kernel)
private def cert12_11 := witness 12 25 0 110075 110512 16 1468
  0x32264488891222244111122048812200 (by decide +kernel)
private def cert12_12 := witness 12 24 0 120012 120512 19 1732
  0x844c8911322444488222244111122048812200 (by decide +kernel)
private def cert12_13 := witness 12 23 0 130011 130449 20 1812
  0x422644c891112264488891044448822224409102440 (by decide +kernel)
private def cert12_14 := witness 12 22 0 140010 140448 22 1980
  0x108a11322444c89111220c891112208889104444881220488 (by decide +kernel)
private def cert12_15 := witness 12 21 0 150009 150448 23 2044
  0xa4508991422644888913224444883224444882222441111220488 (by decide +kernel)
private def cert12_16 := witness 12 20 0 160008 160385 24 2120
  0x52284508991222844c89111220c89111220c89111220888910444488 (by decide +kernel)
private def cert12_17 := witness 12 19 0 170007 170384 24 2096
  0x522a450899142264488891422644888910644888910644888910444488 (by decide +kernel)
private def cert12_18 := witness 12 18 0 180006 180384 25 2156
  0x31152284548a1132244508991222244211322444488322444488322444488 (by decide +kernel)
private def cert12_19 := witness 12 17 0 190005 190321 24 2048
  0x622a4548a11322a450899122224508991222244211322444488322444488 (by decide +kernel)
private def cert12_20 := witness 12 16 0 200004 200320 24 2024
  0x622c4548a11522844c8911522844c8911122108991222244211322444488 (by decide +kernel)
private def cert12_21 := witness 12 15 0 210003 210320 23 1904
  0xe4588a91622a4508991522844c8911122a4508991222244211322444488 (by decide +kernel)
private def cert12_22 := witness 12 14 0 220002 220257 22 1800
  0x1c8b11622a4508b11522844c8911522844c8911122148a11322444488 (by decide +kernel)
private def cert12_23 := witness 12 13 0 230001 230256 20 1604
  0x722e4588a91622a4508991622a450899122224548a11322444488 (by decide +kernel)
private def cert12_24 := witness 12 12 0 240000 240256 19 1488
  0x1045c8b11722c4548a11622a4508991222c4548a11322444488 (by decide +kernel)
private def cert12_25 := witness 12 11 0 250000 250193 16 1220
  0x822e45c8b11522e4588a9142264588a9142264488891 (by decide +kernel)
private def cert12_26 := witness 12 10 0 260000 260192 14 1032
  0x208c11722c45c8b11522845c8b11522844c8911 (by decide +kernel)
private def cert12_27 := witness 12 9 0 270000 270192 12 852
  0x923045c8c11722c4548b91622a4508991 (by decide +kernel)
private def cert12_28 := witness 12 8 0 280000 280129 10 688
  0x248c11822e4588c11722c4548a11 (by decide +kernel)
private def cert12_29 := witness 12 7 0 290000 290128 8 532
  0x92324608b91822e4588a91 (by decide +kernel)
private def cert12_30 := witness 12 6 0 300000 300128 7 444
  0x144648c11923045c8b11 (by decide +kernel)
private def cert12_31 := witness 12 5 0 310000 310065 5 308
  0x51192324608b91 (by decide +kernel)
private def cert12_32 := witness 12 4 0 320000 320064 4 236
  0xa2344648c11 (by decide +kernel)
private def cert12_33 := witness 12 3 0 330000 330064 3 168
  0x164688c91 (by decide +kernel)
private def cert12_34 := witness 12 2 0 340000 340001 2 108
  0x2c8d11 (by decide +kernel)
private def cert12_35 := witness 12 1 0 350000 350000 1 52
  0x591 (by decide +kernel)
private def cert12_36 := witness 12 0 0 360000 360000 1 48
  0x611 (by decide +kernel)
private def chunks12 : List (Chunk 12) := [
  cert12_0, cert12_1, cert12_2, cert12_3, cert12_4, cert12_5, cert12_6, cert12_7, cert12_8, cert12_9,
  cert12_10, cert12_11, cert12_12, cert12_13, cert12_14, cert12_15, cert12_16, cert12_17, cert12_18, cert12_19,
  cert12_20, cert12_21, cert12_22, cert12_23, cert12_24, cert12_25, cert12_26, cert12_27, cert12_28, cert12_29,
  cert12_30, cert12_31, cert12_32, cert12_33, cert12_34, cert12_35, cert12_36]

def rows12 := rowsFrom chunks12

theorem good12 : ∀ r ∈ rows12, good 12 r = true := rowsFrom_good chunks12

theorem sorted12 : rows12.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks12 0 (by decide +kernel)).1

theorem mass12 (i : Fin 54) :
    bandCount 12 (i.val : ℤ) 53 13 ≤ (rows12.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks12).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 12 (j : ℤ) 53 13 ≤ mass j chunks12)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total12 : (rows12.map (price 12)).sum = 38220 :=
  (total_eq chunks12).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

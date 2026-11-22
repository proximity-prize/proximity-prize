import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup10

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 20000000

namespace Low53At2389AnchorRankReceipt
open K1_13_1_1 (bandCount)

private def cert11_0 := witness 11 33 0 704 704 1 96
  0x0 (by decide +kernel)
private def cert11_1 := witness 11 32 0 10641 10641 1 96
  0x0 (by decide +kernel)
private def cert11_2 := witness 11 31 0 20578 20640 2 192
  0x0 (by decide +kernel)
private def cert11_3 := witness 11 30 0 30515 30640 3 284
  0x2440 (by decide +kernel)
private def cert11_4 := witness 11 29 0 40452 40577 4 380
  0x12200 (by decide +kernel)
private def cert11_5 := witness 11 28 0 50389 50576 5 472
  0x9112200 (by decide +kernel)
private def cert11_6 := witness 11 27 0 60326 60576 7 656
  0x44448812200 (by decide +kernel)
private def cert11_7 := witness 11 26 0 70263 70513 8 748
  0x22224448812200 (by decide +kernel)
private def cert11_8 := witness 11 25 0 80200 80512 10 932
  0x88911122048812200 (by decide +kernel)
private def cert11_9 := witness 11 24 0 90137 90512 12 1108
  0x32244448911122048812200 (by decide +kernel)
private def cert11_10 := witness 11 23 0 100074 100449 14 1292
  0xc8911222244111122048812200 (by decide +kernel)
private def cert11_11 := witness 11 22 0 110011 110448 16 1468
  0x32264488891222244111122048812200 (by decide +kernel)
private def cert11_12 := witness 11 21 0 120010 120448 18 1636
  0x10899122264488891044448822224409102440 (by decide +kernel)
private def cert11_13 := witness 11 20 0 130009 130385 19 1716
  0x844c8991222244c891112208889104444881220488 (by decide +kernel)
private def cert11_14 := witness 11 19 0 140008 140384 20 1792
  0x422844c89113224444883224444882222441111220488 (by decide +kernel)
private def cert11_15 := witness 11 18 0 150007 150384 21 1856
  0x29142264508991222244c89111220c89111220888910444488 (by decide +kernel)
private def cert11_16 := witness 11 17 0 160006 160321 21 1844
  0x291422844c8911422644888910644888910644888910444488 (by decide +kernel)
private def cert11_17 := witness 11 16 0 170005 170320 21 1820
  0x291522844c8a1132244448a11322444488322444488322444488 (by decide +kernel)
private def cert11_18 := witness 11 15 0 180004 180320 21 1796
  0x31152284548a1132244508991222244211322444488322444488 (by decide +kernel)
private def cert11_19 := witness 11 14 0 190003 190257 20 1688
  0x622a4548a11322a450899122224508991222244211322444488 (by decide +kernel)
private def cert11_20 := witness 11 13 0 200002 200256 19 1584
  0xc4588a91422a4508991222a4508991222244211322444488 (by decide +kernel)
private def cert11_21 := witness 11 12 0 210001 210256 18 1464
  0x1c8b11522c4548a11322a450899122224548a11322444488 (by decide +kernel)
private def cert11_22 := witness 11 11 0 220000 220193 16 1284
  0x722c4588a91422c4548a1132244548a11322444488 (by decide +kernel)
private def cert11_23 := witness 11 10 0 230000 230192 14 1088
  0x1c8b91622a4588a9142264588a9142264488891 (by decide +kernel)
private def cert11_24 := witness 11 9 0 240000 240192 12 900
  0x822e4588b91622a4508b11522844c8911 (by decide +kernel)
private def cert11_25 := witness 11 8 0 250000 250129 10 728
  0x208b91722c4548b91622a4508991 (by decide +kernel)
private def cert11_26 := witness 11 7 0 260000 260128 8 564
  0x823045c8b11722c4548a11 (by decide +kernel)
private def cert11_27 := witness 11 6 0 270000 270128 7 472
  0x124608b91822e4588a91 (by decide +kernel)
private def cert11_28 := witness 11 5 0 280000 280065 5 328
  0x491823045c8b11 (by decide +kernel)
private def cert11_29 := witness 11 4 0 290000 290064 4 252
  0x92324608b91 (by decide +kernel)
private def cert11_30 := witness 11 3 0 300000 300064 3 180
  0x144648c11 (by decide +kernel)
private def cert11_31 := witness 11 2 0 310000 310001 2 116
  0x288c91 (by decide +kernel)
private def cert11_32 := witness 11 1 0 320000 320000 1 56
  0x511 (by decide +kernel)
private def cert11_33 := witness 11 0 0 330000 330000 1 52
  0x591 (by decide +kernel)
private def chunks11 : List (Chunk 11) := [
  cert11_0, cert11_1, cert11_2, cert11_3, cert11_4, cert11_5, cert11_6, cert11_7, cert11_8, cert11_9,
  cert11_10, cert11_11, cert11_12, cert11_13, cert11_14, cert11_15, cert11_16, cert11_17, cert11_18, cert11_19,
  cert11_20, cert11_21, cert11_22, cert11_23, cert11_24, cert11_25, cert11_26, cert11_27, cert11_28, cert11_29,
  cert11_30, cert11_31, cert11_32, cert11_33]

def rows11 := rowsFrom chunks11

theorem good11 : ∀ r ∈ rows11, good 11 r = true := rowsFrom_good chunks11

theorem sorted11 : rows11.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks11 0 (by decide +kernel)).1

theorem mass11 (i : Fin 54) :
    bandCount 11 (i.val : ℤ) 53 13 ≤ (rows11.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks11).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 11 (j : ℤ) 53 13 ≤ mass j chunks11)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total11 : (rows11.map (price 11)).sum = 30940 :=
  (total_eq chunks11).trans (by decide +kernel)

end Low53At2389AnchorRankReceipt

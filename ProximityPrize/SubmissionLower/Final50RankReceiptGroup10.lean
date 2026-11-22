import ProximityPrize.SubmissionLower.Final50RankReceiptBase
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup5

set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Final50RankReceipt
open K1_13_1_1 (bandCount)

private def cert10_0 := witnessFinal50 10 30 0 640 640 1 99
  0x0 (by decide +kernel)
private def cert10_1 := witnessFinal50 10 29 0 10577 10577 1 99
  0x0 (by decide +kernel)
private def cert10_2 := witnessFinal50 10 28 0 20514 20576 2 198
  0x0 (by decide +kernel)
private def cert10_3 := witnessFinal50 10 27 0 30451 30576 3 293
  0x2440 (by decide +kernel)
private def cert10_4 := witnessFinal50 10 26 0 40388 40513 4 392
  0x12200 (by decide +kernel)
private def cert10_5 := witnessFinal50 10 25 0 50325 50512 5 487
  0x9112200 (by decide +kernel)
private def cert10_6 := witnessFinal50 10 24 0 60262 60512 7 677
  0x44448812200 (by decide +kernel)
private def cert10_7 := witnessFinal50 10 23 0 70199 70449 8 772
  0x22224448812200 (by decide +kernel)
private def cert10_8 := witnessFinal50 10 22 0 80136 80448 10 962
  0x88911122048812200 (by decide +kernel)
private def cert10_9 := witnessFinal50 10 21 0 90073 90448 12 1144
  0x32244448911122048812200 (by decide +kernel)
private def cert10_10 := witnessFinal50 10 20 0 100010 100385 14 1334
  0xc8911222244111122048812200 (by decide +kernel)
private def cert10_11 := witnessFinal50 10 19 0 110009 110384 15 1417
  0x644c891112244448822224409102440 (by decide +kernel)
private def cert10_12 := witnessFinal50 10 18 0 120008 120384 17 1591
  0x211322444c891112208889104444881220488 (by decide +kernel)
private def cert10_13 := witnessFinal50 10 17 0 130007 130321 17 1579
  0x211322644888913224444882222441111220488 (by decide +kernel)
private def cert10_14 := witnessFinal50 10 16 0 140006 140320 18 1658
  0x108a11322444c89111220c89111220888910444488 (by decide +kernel)
private def cert10_15 := witnessFinal50 10 15 0 150005 150320 18 1634
  0x148a11322844c8911122644888910644888910444488 (by decide +kernel)
private def cert10_16 := witnessFinal50 10 14 0 160004 160257 18 1622
  0x148a1142264488a11322444488322444488322444488 (by decide +kernel)
private def cert10_17 := witnessFinal50 10 13 0 170003 170256 17 1511
  0x291522844c8a1132244448a11322444488322444488 (by decide +kernel)
private def cert10_18 := witnessFinal50 10 12 0 180002 180256 17 1487
  0x31152284548a1132244508991222244211322444488 (by decide +kernel)
private def cert10_19 := witnessFinal50 10 11 0 190001 190193 15 1293
  0xc4548a9142264548a1132244448a11322444488 (by decide +kernel)
private def cert10_20 := witnessFinal50 10 10 0 200000 200192 14 1186
  0x188b1152284548a1132244548a11322444488 (by decide +kernel)
private def cert10_21 := witnessFinal50 10 9 0 210000 210192 12 984
  0x722c4548b11522844c8a9142264488891 (by decide +kernel)
private def cert10_22 := witnessFinal50 10 8 0 220000 220129 10 798
  0x1c8b11622a4508b11522844c8911 (by decide +kernel)
private def cert10_23 := witnessFinal50 10 7 0 230000 230128 8 620
  0x722e4588a91622a4508991 (by decide +kernel)
private def cert10_24 := witnessFinal50 10 6 0 240000 240128 7 521
  0x1045c8b11722c4548a11 (by decide +kernel)
private def cert10_25 := witnessFinal50 10 5 0 250000 250065 5 363
  0x411722e4588a91 (by decide +kernel)
private def cert10_26 := witnessFinal50 10 4 0 260000 260064 4 280
  0x823045c8b11 (by decide +kernel)
private def cert10_27 := witnessFinal50 10 3 0 270000 270064 3 201
  0x124608b91 (by decide +kernel)
private def cert10_28 := witnessFinal50 10 2 0 280000 280001 2 130
  0x248c11 (by decide +kernel)
private def cert10_29 := witnessFinal50 10 1 0 290000 290000 1 63
  0x491 (by decide +kernel)
private def cert10_30 := witnessFinal50 10 0 0 300000 300000 1 59
  0x511 (by decide +kernel)
private def chunks10 : List (Chunk 10) := [
  cert10_0,
  cert10_1,
  cert10_2,
  cert10_3,
  cert10_4,
  cert10_5,
  cert10_6,
  cert10_7,
  cert10_8,
  cert10_9,
  cert10_10,
  cert10_11,
  cert10_12,
  cert10_13,
  cert10_14,
  cert10_15,
  cert10_16,
  cert10_17,
  cert10_18,
  cert10_19,
  cert10_20,
  cert10_21,
  cert10_22,
  cert10_23,
  cert10_24,
  cert10_25,
  cert10_26,
  cert10_27,
  cert10_28,
  cert10_29,
  cert10_30]
def rows10 := rowsFrom chunks10

theorem good10 : ∀ r ∈ rows10, good 10 r = true := rowsFrom_good chunks10

theorem sorted10 : rows10.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks10 0 (by decide +kernel)).1

theorem mass10 (i : Fin 56) :
    bandCount 10 (i.val : ℤ) 55 14 ≤ (rows10.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks10).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 10 (j : ℤ) 55 14 ≤ mass j chunks10)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total10 : (rows10.map (price 10)).sum = 25454 :=
  (total_eq chunks10).trans (by decide +kernel)

private def cert11_0 := witnessFinal50 11 33 0 704 704 1 99
  0x0 (by decide +kernel)
private def cert11_1 := witnessFinal50 11 32 0 10641 10641 1 99
  0x0 (by decide +kernel)
private def cert11_2 := witnessFinal50 11 31 0 20578 20640 2 198
  0x0 (by decide +kernel)
private def cert11_3 := witnessFinal50 11 30 0 30515 30640 3 293
  0x2440 (by decide +kernel)
private def cert11_4 := witnessFinal50 11 29 0 40452 40577 4 392
  0x12200 (by decide +kernel)
private def cert11_5 := witnessFinal50 11 28 0 50389 50576 5 487
  0x9112200 (by decide +kernel)
private def cert11_6 := witnessFinal50 11 27 0 60326 60576 7 677
  0x44448812200 (by decide +kernel)
private def cert11_7 := witnessFinal50 11 26 0 70263 70513 8 772
  0x22224448812200 (by decide +kernel)
private def cert11_8 := witnessFinal50 11 25 0 80200 80512 10 962
  0x88911122048812200 (by decide +kernel)
private def cert11_9 := witnessFinal50 11 24 0 90137 90512 12 1144
  0x32244448911122048812200 (by decide +kernel)
private def cert11_10 := witnessFinal50 11 23 0 100074 100449 14 1334
  0xc8911222244111122048812200 (by decide +kernel)
private def cert11_11 := witnessFinal50 11 22 0 110011 110448 16 1516
  0x32264488891222244111122048812200 (by decide +kernel)
private def cert11_12 := witnessFinal50 11 21 0 120010 120448 18 1690
  0x10899122264488891044448822224409102440 (by decide +kernel)
private def cert11_13 := witnessFinal50 11 20 0 130009 130385 19 1773
  0x844c8991222244c891112208889104444881220488 (by decide +kernel)
private def cert11_14 := witnessFinal50 11 19 0 140008 140384 20 1852
  0x422844c89113224444883224444882222441111220488 (by decide +kernel)
private def cert11_15 := witnessFinal50 11 18 0 150007 150384 21 1919
  0x29142264508991222244c89111220c89111220888910444488 (by decide +kernel)
private def cert11_16 := witnessFinal50 11 17 0 160006 160321 21 1907
  0x291422844c8911422644888910644888910644888910444488 (by decide +kernel)
private def cert11_17 := witnessFinal50 11 16 0 170005 170320 21 1883
  0x291522844c8a1132244448a11322444488322444488322444488 (by decide +kernel)
private def cert11_18 := witnessFinal50 11 15 0 180004 180320 21 1859
  0x31152284548a1132244508991222244211322444488322444488 (by decide +kernel)
private def cert11_19 := witnessFinal50 11 14 0 190003 190257 20 1748
  0x622a4548a11322a450899122224508991222244211322444488 (by decide +kernel)
private def cert11_20 := witnessFinal50 11 13 0 200002 200256 19 1641
  0xc4588a91422a4508991222a4508991222244211322444488 (by decide +kernel)
private def cert11_21 := witnessFinal50 11 12 0 210001 210256 18 1518
  0x1c8b11522c4548a11322a450899122224548a11322444488 (by decide +kernel)
private def cert11_22 := witnessFinal50 11 11 0 220000 220193 16 1332
  0x722c4588a91422c4548a1132244548a11322444488 (by decide +kernel)
private def cert11_23 := witnessFinal50 11 10 0 230000 230192 14 1130
  0x1c8b91622a4588a9142264588a9142264488891 (by decide +kernel)
private def cert11_24 := witnessFinal50 11 9 0 240000 240192 12 936
  0x822e4588b91622a4508b11522844c8911 (by decide +kernel)
private def cert11_25 := witnessFinal50 11 8 0 250000 250129 10 758
  0x208b91722c4548b91622a4508991 (by decide +kernel)
private def cert11_26 := witnessFinal50 11 7 0 260000 260128 8 588
  0x823045c8b11722c4548a11 (by decide +kernel)
private def cert11_27 := witnessFinal50 11 6 0 270000 270128 7 493
  0x124608b91822e4588a91 (by decide +kernel)
private def cert11_28 := witnessFinal50 11 5 0 280000 280065 5 343
  0x491823045c8b11 (by decide +kernel)
private def cert11_29 := witnessFinal50 11 4 0 290000 290064 4 264
  0x92324608b91 (by decide +kernel)
private def cert11_30 := witnessFinal50 11 3 0 300000 300064 3 189
  0x144648c11 (by decide +kernel)
private def cert11_31 := witnessFinal50 11 2 0 310000 310001 2 122
  0x288c91 (by decide +kernel)
private def cert11_32 := witnessFinal50 11 1 0 320000 320000 1 59
  0x511 (by decide +kernel)
private def cert11_33 := witnessFinal50 11 0 0 330000 330000 1 55
  0x591 (by decide +kernel)
private def chunks11 : List (Chunk 11) := [
  cert11_0,
  cert11_1,
  cert11_2,
  cert11_3,
  cert11_4,
  cert11_5,
  cert11_6,
  cert11_7,
  cert11_8,
  cert11_9,
  cert11_10,
  cert11_11,
  cert11_12,
  cert11_13,
  cert11_14,
  cert11_15,
  cert11_16,
  cert11_17,
  cert11_18,
  cert11_19,
  cert11_20,
  cert11_21,
  cert11_22,
  cert11_23,
  cert11_24,
  cert11_25,
  cert11_26,
  cert11_27,
  cert11_28,
  cert11_29,
  cert11_30,
  cert11_31,
  cert11_32,
  cert11_33]
def rows11 := rowsFrom chunks11

theorem good11 : ∀ r ∈ rows11, good 11 r = true := rowsFrom_good chunks11

theorem sorted11 : rows11.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks11 0 (by decide +kernel)).1

theorem mass11 (i : Fin 56) :
    bandCount 11 (i.val : ℤ) 55 14 ≤ (rows11.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks11).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 11 (j : ℤ) 55 14 ≤ mass j chunks11)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total11 : (rows11.map (price 11)).sum = 32032 :=
  (total_eq chunks11).trans (by decide +kernel)

private def cert12_0 := witnessFinal50 12 36 0 768 768 1 99
  0x0 (by decide +kernel)
private def cert12_1 := witnessFinal50 12 35 0 10705 10705 1 99
  0x0 (by decide +kernel)
private def cert12_2 := witnessFinal50 12 34 0 20642 20704 2 198
  0x0 (by decide +kernel)
private def cert12_3 := witnessFinal50 12 33 0 30579 30704 3 293
  0x2440 (by decide +kernel)
private def cert12_4 := witnessFinal50 12 32 0 40516 40641 4 392
  0x12200 (by decide +kernel)
private def cert12_5 := witnessFinal50 12 31 0 50453 50640 5 487
  0x9112200 (by decide +kernel)
private def cert12_6 := witnessFinal50 12 30 0 60390 60640 7 677
  0x44448812200 (by decide +kernel)
private def cert12_7 := witnessFinal50 12 29 0 70327 70577 8 772
  0x22224448812200 (by decide +kernel)
private def cert12_8 := witnessFinal50 12 28 0 80264 80576 10 962
  0x88911122048812200 (by decide +kernel)
private def cert12_9 := witnessFinal50 12 27 0 90201 90576 12 1144
  0x32244448911122048812200 (by decide +kernel)
private def cert12_10 := witnessFinal50 12 26 0 100138 100513 14 1334
  0xc8911222244111122048812200 (by decide +kernel)
private def cert12_11 := witnessFinal50 12 25 0 110075 110512 16 1516
  0x32264488891222244111122048812200 (by decide +kernel)
private def cert12_12 := witnessFinal50 12 24 0 120012 120512 19 1789
  0x844c8911322444488222244111122048812200 (by decide +kernel)
private def cert12_13 := witnessFinal50 12 23 0 130011 130449 20 1872
  0x422644c891112264488891044448822224409102440 (by decide +kernel)
private def cert12_14 := witnessFinal50 12 22 0 140010 140448 22 2046
  0x108a11322444c89111220c891112208889104444881220488 (by decide +kernel)
private def cert12_15 := witnessFinal50 12 21 0 150009 150448 23 2113
  0xa4508991422644888913224444883224444882222441111220488 (by decide +kernel)
private def cert12_16 := witnessFinal50 12 20 0 160008 160385 24 2192
  0x52284508991222844c89111220c89111220c89111220888910444488 (by decide +kernel)
private def cert12_17 := witnessFinal50 12 19 0 170007 170384 24 2168
  0x522a450899142264488891422644888910644888910644888910444488 (by decide +kernel)
private def cert12_18 := witnessFinal50 12 18 0 180006 180384 25 2231
  0x31152284548a1132244508991222244211322444488322444488322444488 (by decide +kernel)
private def cert12_19 := witnessFinal50 12 17 0 190005 190321 24 2120
  0x622a4548a11322a450899122224508991222244211322444488322444488 (by decide +kernel)
private def cert12_20 := witnessFinal50 12 16 0 200004 200320 24 2096
  0x622c4548a11522844c8911522844c8911122108991222244211322444488 (by decide +kernel)
private def cert12_21 := witnessFinal50 12 15 0 210003 210320 23 1973
  0xe4588a91622a4508991522844c8911122a4508991222244211322444488 (by decide +kernel)
private def cert12_22 := witnessFinal50 12 14 0 220002 220257 22 1866
  0x1c8b11622a4508b11522844c8911522844c8911122148a11322444488 (by decide +kernel)
private def cert12_23 := witnessFinal50 12 13 0 230001 230256 20 1664
  0x722e4588a91622a4508991622a450899122224548a11322444488 (by decide +kernel)
private def cert12_24 := witnessFinal50 12 12 0 240000 240256 19 1545
  0x1045c8b11722c4548a11622a4508991222c4548a11322444488 (by decide +kernel)
private def cert12_25 := witnessFinal50 12 11 0 250000 250193 16 1268
  0x822e45c8b11522e4588a9142264588a9142264488891 (by decide +kernel)
private def cert12_26 := witnessFinal50 12 10 0 260000 260192 14 1074
  0x208c11722c45c8b11522845c8b11522844c8911 (by decide +kernel)
private def cert12_27 := witnessFinal50 12 9 0 270000 270192 12 888
  0x923045c8c11722c4548b91622a4508991 (by decide +kernel)
private def cert12_28 := witnessFinal50 12 8 0 280000 280129 10 718
  0x248c11822e4588c11722c4548a11 (by decide +kernel)
private def cert12_29 := witnessFinal50 12 7 0 290000 290128 8 556
  0x92324608b91822e4588a91 (by decide +kernel)
private def cert12_30 := witnessFinal50 12 6 0 300000 300128 7 465
  0x144648c11923045c8b11 (by decide +kernel)
private def cert12_31 := witnessFinal50 12 5 0 310000 310065 5 323
  0x51192324608b91 (by decide +kernel)
private def cert12_32 := witnessFinal50 12 4 0 320000 320064 4 248
  0xa2344648c11 (by decide +kernel)
private def cert12_33 := witnessFinal50 12 3 0 330000 330064 3 177
  0x164688c91 (by decide +kernel)
private def cert12_34 := witnessFinal50 12 2 0 340000 340001 2 114
  0x2c8d11 (by decide +kernel)
private def cert12_35 := witnessFinal50 12 1 0 350000 350000 1 55
  0x591 (by decide +kernel)
private def cert12_36 := witnessFinal50 12 0 0 360000 360000 1 51
  0x611 (by decide +kernel)
private def chunks12 : List (Chunk 12) := [
  cert12_0,
  cert12_1,
  cert12_2,
  cert12_3,
  cert12_4,
  cert12_5,
  cert12_6,
  cert12_7,
  cert12_8,
  cert12_9,
  cert12_10,
  cert12_11,
  cert12_12,
  cert12_13,
  cert12_14,
  cert12_15,
  cert12_16,
  cert12_17,
  cert12_18,
  cert12_19,
  cert12_20,
  cert12_21,
  cert12_22,
  cert12_23,
  cert12_24,
  cert12_25,
  cert12_26,
  cert12_27,
  cert12_28,
  cert12_29,
  cert12_30,
  cert12_31,
  cert12_32,
  cert12_33,
  cert12_34,
  cert12_35,
  cert12_36]
def rows12 := rowsFrom chunks12

theorem good12 : ∀ r ∈ rows12, good 12 r = true := rowsFrom_good chunks12

theorem sorted12 : rows12.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks12 0 (by decide +kernel)).1

theorem mass12 (i : Fin 56) :
    bandCount 12 (i.val : ℤ) 55 14 ≤ (rows12.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks12).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 12 (j : ℤ) 55 14 ≤ mass j chunks12)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total12 : (rows12.map (price 12)).sum = 39585 :=
  (total_eq chunks12).trans (by decide +kernel)

private def cert13_0 := witnessFinal50 13 39 0 832 832 1 99
  0x0 (by decide +kernel)
private def cert13_1 := witnessFinal50 13 38 0 10769 10769 1 99
  0x0 (by decide +kernel)
private def cert13_2 := witnessFinal50 13 37 0 20706 20768 2 198
  0x0 (by decide +kernel)
private def cert13_3 := witnessFinal50 13 36 0 30643 30768 3 293
  0x2440 (by decide +kernel)
private def cert13_4 := witnessFinal50 13 35 0 40580 40705 4 392
  0x12200 (by decide +kernel)
private def cert13_5 := witnessFinal50 13 34 0 50517 50704 5 487
  0x9112200 (by decide +kernel)
private def cert13_6 := witnessFinal50 13 33 0 60454 60704 7 677
  0x44448812200 (by decide +kernel)
private def cert13_7 := witnessFinal50 13 32 0 70391 70641 8 772
  0x22224448812200 (by decide +kernel)
private def cert13_8 := witnessFinal50 13 31 0 80328 80640 10 962
  0x88911122048812200 (by decide +kernel)
private def cert13_9 := witnessFinal50 13 30 0 90265 90640 12 1144
  0x32244448911122048812200 (by decide +kernel)
private def cert13_10 := witnessFinal50 13 29 0 100202 100577 14 1334
  0xc8911222244111122048812200 (by decide +kernel)
private def cert13_11 := witnessFinal50 13 28 0 110139 110576 16 1516
  0x32264488891222244111122048812200 (by decide +kernel)
private def cert13_12 := witnessFinal50 13 27 0 120076 120576 19 1789
  0x844c8911322444488222244111122048812200 (by decide +kernel)
private def cert13_13 := witnessFinal50 13 26 0 130013 130513 21 1971
  0x21132264488891322444488222244111122048812200 (by decide +kernel)
private def cert13_14 := witnessFinal50 13 25 0 140012 140512 23 2145
  0x8450899122264488891064488891044448822224409102440 (by decide +kernel)
private def cert13_15 := witnessFinal50 13 24 0 150011 150512 25 2307
  0x29142264508991222244c89111220c891112208889104444881220488 (by decide +kernel)
private def cert13_16 := witnessFinal50 13 23 0 160010 160449 26 2386
  0x148a1142264488a113224444883224444883224444882222441111220488 (by decide +kernel)
private def cert13_17 := witnessFinal50 13 22 0 170009 170448 27 2453
  0xa4548a11322844c8911122844c89111220c89111220c89111220888910444488 (by decide +kernel)
private def cert13_18 := witnessFinal50 13 21 0 180008 180448 28 2516
  0x622a4508a9142264488a11322444488422644888910644888910644888910444488 (by decide +kernel)
private def cert13_19 := witnessFinal50 13 20 0 190007 190385 28 2492
  0x622a4548a11322a450899122224508991222244211322444488322444488322444488 (by decide +kernel)
private def cert13_20 := witnessFinal50 13 19 0 200006 200384 28 2468
  0x622c4548a11522844c8911522844c8911122108991222244211322444488322444488 (by decide +kernel)
private def cert13_21 := witnessFinal50 13 18 0 210005 210384 28 2428
  0x722c4548b11522844c8a9142264488891522844c8911122108991222244211322444488 (by decide +kernel)
private def cert13_22 := witnessFinal50 13 17 0 220004 220321 27 2321
  0xe4588b1152284588a9142264488a91422644888910a4508991222244211322444488 (by decide +kernel)
private def cert13_23 := witnessFinal50 13 16 0 230003 230320 26 2198
  0x1c8b91622a4588a9142264588a9142264488891522844c8911122148a11322444488 (by decide +kernel)
private def cert13_24 := witnessFinal50 13 15 0 240002 240320 25 2079
  0x411722c45c8b1152284588a9142264488b11522844c8911122148a11322444488 (by decide +kernel)
private def cert13_25 := witnessFinal50 13 14 0 250001 250257 23 1877
  0x1045c8b91622a45c8b11522844c8b11522844c8911122c4548a11322444488 (by decide +kernel)
private def cert13_26 := witnessFinal50 13 13 0 260000 260256 21 1683
  0x411822e4588b91622a4508b91622a4508991222c4548a11322444488 (by decide +kernel)
private def cert13_27 := witnessFinal50 13 12 0 270000 270256 19 1469
  0x124608b91822e4588a91722c4548a11322e4588a9142264488891 (by decide +kernel)
private def cert13_28 := witnessFinal50 13 11 0 280000 280193 16 1204
  0x92304608b91623045c8b11522845c8b11522844c8911 (by decide +kernel)
private def cert13_29 := witnessFinal50 13 10 0 290000 290192 14 1018
  0x248c91822e4608b91622a4608b91622a4508991 (by decide +kernel)
private def cert13_30 := witnessFinal50 13 9 0 300000 300192 12 840
  0xa2324608c91822e4588c11722c4548a11 (by decide +kernel)
private def cert13_31 := witnessFinal50 13 8 0 310000 310129 10 678
  0x288c91923045c8c91822e4588a91 (by decide +kernel)
private def cert13_32 := witnessFinal50 13 7 0 320000 320128 8 524
  0xa2344648c11923045c8b11 (by decide +kernel)
private def cert13_33 := witnessFinal50 13 6 0 330000 330128 7 437
  0x164688c91a2324608b91 (by decide +kernel)
private def cert13_34 := witnessFinal50 13 5 0 340000 340065 5 303
  0x591a2344648c11 (by decide +kernel)
private def cert13_35 := witnessFinal50 13 4 0 350000 350064 4 232
  0xb2364688c91 (by decide +kernel)
private def cert13_36 := witnessFinal50 13 3 0 360000 360064 3 165
  0x1846c8d11 (by decide +kernel)
private def cert13_37 := witnessFinal50 13 2 0 370000 370001 2 106
  0x308d91 (by decide +kernel)
private def cert13_38 := witnessFinal50 13 1 0 380000 380000 1 51
  0x611 (by decide +kernel)
private def cert13_39 := witnessFinal50 13 0 0 390000 390000 1 47
  0x691 (by decide +kernel)
private def chunks13 : List (Chunk 13) := [
  cert13_0,
  cert13_1,
  cert13_2,
  cert13_3,
  cert13_4,
  cert13_5,
  cert13_6,
  cert13_7,
  cert13_8,
  cert13_9,
  cert13_10,
  cert13_11,
  cert13_12,
  cert13_13,
  cert13_14,
  cert13_15,
  cert13_16,
  cert13_17,
  cert13_18,
  cert13_19,
  cert13_20,
  cert13_21,
  cert13_22,
  cert13_23,
  cert13_24,
  cert13_25,
  cert13_26,
  cert13_27,
  cert13_28,
  cert13_29,
  cert13_30,
  cert13_31,
  cert13_32,
  cert13_33,
  cert13_34,
  cert13_35,
  cert13_36,
  cert13_37,
  cert13_38,
  cert13_39]
def rows13 := rowsFrom chunks13

theorem good13 : ∀ r ∈ rows13, good 13 r = true := rowsFrom_good chunks13

theorem sorted13 : rows13.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks13 0 (by decide +kernel)).1

theorem mass13 (i : Fin 56) :
    bandCount 13 (i.val : ℤ) 55 14 ≤ (rows13.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks13).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 13 (j : ℤ) 55 14 ≤ mass j chunks13)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total13 : (rows13.map (price 13)).sum = 48160 :=
  (total_eq chunks13).trans (by decide +kernel)

private def cert14_0 := witnessFinal50 14 42 0 896 896 1 99
  0x0 (by decide +kernel)
private def cert14_1 := witnessFinal50 14 41 0 10833 10833 1 99
  0x0 (by decide +kernel)
private def cert14_2 := witnessFinal50 14 40 0 20770 20832 2 198
  0x0 (by decide +kernel)
private def cert14_3 := witnessFinal50 14 39 0 30707 30832 3 293
  0x2440 (by decide +kernel)
private def cert14_4 := witnessFinal50 14 38 0 40644 40769 4 392
  0x12200 (by decide +kernel)
private def cert14_5 := witnessFinal50 14 37 0 50581 50768 5 487
  0x9112200 (by decide +kernel)
private def cert14_6 := witnessFinal50 14 36 0 60518 60768 7 677
  0x44448812200 (by decide +kernel)
private def cert14_7 := witnessFinal50 14 35 0 70455 70705 8 772
  0x22224448812200 (by decide +kernel)
private def cert14_8 := witnessFinal50 14 34 0 80392 80704 10 962
  0x88911122048812200 (by decide +kernel)
private def cert14_9 := witnessFinal50 14 33 0 90329 90704 12 1144
  0x32244448911122048812200 (by decide +kernel)
private def cert14_10 := witnessFinal50 14 32 0 100266 100641 14 1334
  0xc8911222244111122048812200 (by decide +kernel)
private def cert14_11 := witnessFinal50 14 31 0 110203 110640 16 1516
  0x32264488891222244111122048812200 (by decide +kernel)
private def cert14_12 := witnessFinal50 14 30 0 120140 120640 19 1789
  0x844c8911322444488222244111122048812200 (by decide +kernel)
private def cert14_13 := witnessFinal50 14 29 0 130077 130577 21 1971
  0x21132264488891322444488222244111122048812200 (by decide +kernel)
private def cert14_14 := witnessFinal50 14 28 0 140014 140576 24 2244
  0x422844c8911322444488322444488222244111122048812200 (by decide +kernel)
private def cert14_15 := witnessFinal50 14 27 0 150013 150576 26 2406
  0x148a11322844c891112264488891064488891044448822224409102440 (by decide +kernel)
private def cert14_16 := witnessFinal50 14 26 0 160012 160513 28 2580
  0x52284508991222844c89111220c89111220c891112208889104444881220488 (by decide +kernel)
private def cert14_17 := witnessFinal50 14 25 0 170011 170512 29 2647
  0x291522844c8a1132244448a113224444883224444883224444882222441111220488 (by decide +kernel)
private def cert14_18 := witnessFinal50 14 24 0 180010 180512 31 2801
  0xc4548a11522844c8911422644888910844c89111220c89111220c89111220888910444488 (by decide +kernel)
private def cert14_19 := witnessFinal50 14 23 0 190009 190449 31 2777
  0xc4548a9142264548a1132244448a11322444488422644888910644888910644888910444488 (by decide +kernel)
private def cert14_20 := witnessFinal50 14 22 0 200008 200448 32 2840
  0x622c4548a11522844c8911522844c8911122108991222244211322444488322444488322444488 (by decide +kernel)
private def cert14_21 := witnessFinal50 14 21 0 210007 210448 32 2800
  0x722c4548b11522844c8a9142264488891522844c8911122108991222244211322444488322444488 (by decide +kernel)
private def cert14_22 := witnessFinal50 14 20 0 220006 220385 32 2776
  0x722c4588a91422c4548a1132244548a11322444488522844c8911122108991222244211322444488 (by decide +kernel)
private def cert14_23 := witnessFinal50 14 19 0 230005 230384 31 2653
  0xe45c8b11522c4548a11322c4548a1132244448a91422644888910a4508991222244211322444488 (by decide +kernel)
private def cert14_24 := witnessFinal50 14 18 0 240004 240384 31 2613
  0x1045c8b11722c4548a11622a4508991222c4548a11322444488522844c8911122148a11322444488 (by decide +kernel)
private def cert14_25 := witnessFinal50 14 17 0 250003 250321 29 2411
  0x411722e4588a91722c4548a11322c4548a1132244448b11522844c8911122148a11322444488 (by decide +kernel)
private def cert14_26 := witnessFinal50 14 16 0 260002 260320 28 2292
  0x823045c8b11722c4548a11722c4548a1132244588a91422644888910c4548a11322444488 (by decide +kernel)
private def cert14_27 := witnessFinal50 14 15 0 270001 270320 26 2078
  0x248c11723045c8b11522e4588a91422645c8b11522844c8911122c4548a11322444488 (by decide +kernel)
private def cert14_28 := witnessFinal50 14 14 0 280000 280257 24 1884
  0x92304608b91623045c8b11522845c8b11522844c8911722c4548a11322444488 (by decide +kernel)
private def cert14_29 := witnessFinal50 14 13 0 290000 290256 21 1599
  0x491923045c8c11722c4548c11722c4548a11322e4588a9142264488891 (by decide +kernel)
private def cert14_30 := witnessFinal50 14 12 0 300000 300256 19 1393
  0x144648c11923045c8b11822e4588a91423045c8b11522844c8911 (by decide +kernel)
private def cert14_31 := witnessFinal50 14 11 0 310000 310193 16 1140
  0xa2324648c1172324608b91622a4608b91622a4508991 (by decide +kernel)
private def cert14_32 := witnessFinal50 14 10 0 320000 320192 14 962
  0x288d1192304648c11722c4648c11722c4548a11 (by decide +kernel)
private def cert14_33 := witnessFinal50 14 9 0 330000 330192 12 792
  0xb2344648d11923045c8c91822e4588a91 (by decide +kernel)
private def cert14_34 := witnessFinal50 14 8 0 340000 340129 10 638
  0x2c8d11a2324608d11923045c8b11 (by decide +kernel)
private def cert14_35 := witnessFinal50 14 7 0 350000 350128 8 492
  0xb2364688c91a2324608b91 (by decide +kernel)
private def cert14_36 := witnessFinal50 14 6 0 360000 360128 7 409
  0x1846c8d11b2344648c11 (by decide +kernel)
private def cert14_37 := witnessFinal50 14 5 0 370000 370065 5 283
  0x611b2364688c91 (by decide +kernel)
private def cert14_38 := witnessFinal50 14 4 0 380000 380064 4 216
  0xc23846c8d11 (by decide +kernel)
private def cert14_39 := witnessFinal50 14 3 0 390000 390064 3 153
  0x1a4708d91 (by decide +kernel)
private def cert14_40 := witnessFinal50 14 2 0 400000 400001 2 98
  0x348e11 (by decide +kernel)
private def cert14_41 := witnessFinal50 14 1 0 410000 410000 1 47
  0x691 (by decide +kernel)
private def cert14_42 := witnessFinal50 14 0 0 420000 420000 1 43
  0x711 (by decide +kernel)
private def chunks14 : List (Chunk 14) := [
  cert14_0,
  cert14_1,
  cert14_2,
  cert14_3,
  cert14_4,
  cert14_5,
  cert14_6,
  cert14_7,
  cert14_8,
  cert14_9,
  cert14_10,
  cert14_11,
  cert14_12,
  cert14_13,
  cert14_14,
  cert14_15,
  cert14_16,
  cert14_17,
  cert14_18,
  cert14_19,
  cert14_20,
  cert14_21,
  cert14_22,
  cert14_23,
  cert14_24,
  cert14_25,
  cert14_26,
  cert14_27,
  cert14_28,
  cert14_29,
  cert14_30,
  cert14_31,
  cert14_32,
  cert14_33,
  cert14_34,
  cert14_35,
  cert14_36,
  cert14_37,
  cert14_38,
  cert14_39,
  cert14_40,
  cert14_41,
  cert14_42]
def rows14 := rowsFrom chunks14

theorem good14 : ∀ r ∈ rows14, good 14 r = true := rowsFrom_good chunks14

theorem sorted14 : rows14.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks14 0 (by decide +kernel)).1

theorem mass14 (i : Fin 56) :
    bandCount 14 (i.val : ℤ) 55 14 ≤ (rows14.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks14).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 14 (j : ℤ) 55 14 ≤ mass j chunks14)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total14 : (rows14.map (price 14)).sum = 57800 :=
  (total_eq chunks14).trans (by decide +kernel)

end Final50RankReceipt

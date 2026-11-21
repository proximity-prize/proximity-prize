import ProximityPrize.SubmissionLower.Low48SharedSchedules

set_option Elab.async false

set_option maxRecDepth 17000

set_option maxHeartbeats 6000000

namespace Low48Receipt

open K1_13_1_1 (bandCount)

private def c10_0 := witness48 10 30 0 640 640 1 92
  0x3

private def c10_1 := witness48 10 29 0 10577 10577 1 92
  0x3

private def c10_2 := witness48 10 28 0 20514 20576 2 184
  0x33

private def c10_3 := witness48 10 27 0 30451 30576 3 272
  0x1033

private def c10_4 := witness48 10 26 0 40388 40513 4 364
  0x10333

private def c10_5 := witness48 10 25 0 50325 50512 5 452
  0x810333

private def c10_6 := witness48 10 24 0 60262 60512 7 628
  0x808190333

private def c10_7 := witness48 10 23 0 70199 70449 8 716
  0x40408190333

private def c10_8 := witness48 10 22 0 80136 80448 10 892
  0x204040c8190333

private def c10_9 := witness48 10 21 0 90073 90448 12 1060
  0xc10104040c8190333

private def c10_10 := witness48 10 20 0 100010 100385 14 1236
  0x608101034040c8190333

private def c10_11 := witness48 10 19 0 110009 110384 15 1312
  0x1830404101034040c819033

private def c10_12 := witness48 10 18 0 120008 120384 17 1472
  0x80c10304040d01034040c81903

private def c10_13 := witness48 10 17 0 130007 130321 17 1460
  0x4060c1010608081a02068081903

private def c10_14 := witness48 10 16 0 140006 140320 18 1532
  0x20406081820206c101034040d0103

private def c10_15 := witness48 10 15 0 150005 150320 18 1508
  0x14203080c1010608081b04040d0103

private def c10_16 := witness48 10 14 0 160004 160257 18 1496
  0x14204060820304040d820206c10103

private def c10_17 := witness48 10 13 0 170003 170256 17 1392
  0x14284061018202101820206c10103

private def c10_18 := witness48 10 12 0 180002 180256 17 1368
  0x182840a10182080c1010380c10103

private def c10_19 := witness48 10 11 0 190001 190193 15 1188
  0x3050a10185080c101080c10103

private def c10_20 := witness48 10 10 0 200000 200192 14 1088
  0x60c14205080c105080c10103

private def c10_21 := witness48 10 9 0 210000 210192 12 900
  0xe182860a10185080c1010

private def c10_22 := witness48 10 8 0 220000 220129 10 728
  0x3860c142060a101820

private def c10_23 := witness48 10 7 0 230000 230128 8 564
  0xe1c3050c142030

private def c10_24 := witness48 10 6 0 240000 240128 7 472
  0x1003860e182840

private def c10_25 := witness48 10 5 0 250000 250065 5 328
  0x400e1c3050

private def c10_26 := witness48 10 4 0 260000 260064 4 252
  0x2001003860

private def c10_27 := witness48 10 3 0 270000 270064 3 180
  0x48020070

private def c10_28 := witness48 10 2 0 280000 280001 2 116
  0x900400

private def c10_29 := witness48 10 1 0 290000 290000 1 56
  0x480

private def c10_30 := witness48 10 0 0 300000 300000 1 52
  0x500

private def chunks10 : List (Chunk 10) := [
  c10_0, c10_1, c10_2, c10_3, c10_4, c10_5, c10_6, c10_7, c10_8, c10_9,
  c10_10, c10_11, c10_12, c10_13, c10_14, c10_15, c10_16, c10_17, c10_18, c10_19,
  c10_20, c10_21, c10_22, c10_23, c10_24, c10_25, c10_26, c10_27, c10_28, c10_29,
  c10_30]

def rows10 := rowsFrom chunks10

theorem good10 : ∀ r ∈ rows10, good 10 r = true := rowsFrom_good chunks10

theorem sorted10 : rows10.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks10 0 (by decide +kernel)).1

theorem mass10 (i : Fin 51) :
    bandCount 10 (i.val : ℤ) 50 13 ≤ (rows10.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks10).filter _).length
  rw [mass_eq]
  have h : (List.range 51).all (fun j => decide (bandCount 10 (j : ℤ) 50 13 ≤ mass j chunks10)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total10 : (rows10.map (price 10)).sum = 23452 :=
  (total_eq chunks10).trans (by decide +kernel)

private def c11_0 := witness48 11 33 0 704 704 1 92
  0x3

private def c11_1 := witness48 11 32 0 10641 10641 1 92
  0x3

private def c11_2 := witness48 11 31 0 20578 20640 2 184
  0x33

private def c11_3 := witness48 11 30 0 30515 30640 3 272
  0x1033

private def c11_4 := witness48 11 29 0 40452 40577 4 364
  0x10333

private def c11_5 := witness48 11 28 0 50389 50576 5 452
  0x810333

private def c11_6 := witness48 11 27 0 60326 60576 7 628
  0x808190333

private def c11_7 := witness48 11 26 0 70263 70513 8 716
  0x40408190333

private def c11_8 := witness48 11 25 0 80200 80512 10 892
  0x204040c8190333

private def c11_9 := witness48 11 24 0 90137 90512 12 1060
  0xc10104040c8190333

private def c11_10 := witness48 11 23 0 100074 100449 14 1236
  0x608101034040c8190333

private def c11_11 := witness48 11 22 0 110011 110448 16 1404
  sharedSchedule14

private def c11_12 := witness48 11 21 0 120010 120448 18 1564
  0x80c10304040d01034040c819033

private def c11_13 := witness48 11 20 0 130009 130385 19 1640
  0x203060808304040d01034040c81903

private def c11_14 := witness48 11 19 0 140008 140384 20 1712
  0x10203040c10103608081a02068081903

private def c11_15 := witness48 11 18 0 150007 150384 21 1772
  0x5080c20304041820206c101034040d0103

private def c11_16 := witness48 11 17 0 160006 160321 21 1760
  0x50810182080c10103608081b04040d0103

private def c11_17 := witness48 11 16 0 170005 170320 21 1736
  0x285080c203040420304040d820206c10103

private def c11_18 := witness48 11 15 0 180004 180320 21 1712
  0x30508142030410182020701820206c10103

private def c11_19 := witness48 11 14 0 190003 190257 20 1608
  0x3050a10185080c101080c1010380c10103

private def c11_20 := witness48 11 13 0 200002 200256 19 1508
  0x60c14205080c105080c1010380c10103

private def c11_21 := witness48 11 12 0 210001 210256 18 1392
  0x70c14305080c2840608085080c10103

private def c11_22 := witness48 11 11 0 220000 220193 16 1220
  0x1c3060a10305080c105080c10103

private def c11_23 := witness48 11 10 0 230000 230192 14 1032
  0x3870c14305080c305080c1010

private def c11_24 := witness48 11 9 0 240000 240192 12 852
  0x801c3070c142060a101820

private def c11_25 := witness48 11 8 0 250000 250129 10 688
  0x20070e182870c142030

private def c11_26 := witness48 11 7 0 260000 260128 8 532
  0x2001003860e182840

private def c11_27 := witness48 11 6 0 270000 270128 7 444
  0x1200801c0801c3050

private def c11_28 := witness48 11 5 0 280000 280065 5 308
  0x4802001003860

private def c11_29 := witness48 11 4 0 290000 290064 4 236
  0x90048020070

private def c11_30 := witness48 11 3 0 300000 300064 3 168
  0x1400900400

private def c11_31 := witness48 11 2 0 310000 310001 2 108
  0xa00480

private def c11_32 := witness48 11 1 0 320000 320000 1 52
  0x500

private def c11_33 := witness48 11 0 0 330000 330000 1 48
  0x580

private def chunks11 : List (Chunk 11) := [
  c11_0, c11_1, c11_2, c11_3, c11_4, c11_5, c11_6, c11_7, c11_8, c11_9,
  c11_10, c11_11, c11_12, c11_13, c11_14, c11_15, c11_16, c11_17, c11_18, c11_19,
  c11_20, c11_21, c11_22, c11_23, c11_24, c11_25, c11_26, c11_27, c11_28, c11_29,
  c11_30, c11_31, c11_32, c11_33]

def rows11 := rowsFrom chunks11

theorem good11 : ∀ r ∈ rows11, good 11 r = true := rowsFrom_good chunks11

theorem sorted11 : rows11.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks11 0 (by decide +kernel)).1

theorem mass11 (i : Fin 51) :
    bandCount 11 (i.val : ℤ) 50 13 ≤ (rows11.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks11).filter _).length
  rw [mass_eq]
  have h : (List.range 51).all (fun j => decide (bandCount 11 (j : ℤ) 50 13 ≤ mass j chunks11)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total11 : (rows11.map (price 11)).sum = 29484 :=
  (total_eq chunks11).trans (by decide +kernel)

private def c12_0 := witness48 12 36 0 768 768 1 92
  0x3

private def c12_1 := witness48 12 35 0 10705 10705 1 92
  0x3

private def c12_2 := witness48 12 34 0 20642 20704 2 184
  0x33

private def c12_3 := witness48 12 33 0 30579 30704 3 272
  0x1033

private def c12_4 := witness48 12 32 0 40516 40641 4 364
  0x10333

private def c12_5 := witness48 12 31 0 50453 50640 5 452
  0x810333

private def c12_6 := witness48 12 30 0 60390 60640 7 628
  0x808190333

private def c12_7 := witness48 12 29 0 70327 70577 8 716
  0x40408190333

private def c12_8 := witness48 12 28 0 80264 80576 10 892
  0x204040c8190333

private def c12_9 := witness48 12 27 0 90201 90576 12 1060
  0xc10104040c8190333

private def c12_10 := witness48 12 26 0 100138 100513 14 1236
  0x608101034040c8190333

private def c12_11 := witness48 12 25 0 110075 110512 16 1404
  sharedSchedule14

private def c12_12 := witness48 12 24 0 120012 120512 19 1656
  0x80c10304040d01034040c8190333

private def c12_13 := witness48 12 23 0 130011 130449 20 1732
  0x203060808304040d01034040c819033

private def c12_14 := witness48 12 22 0 140010 140448 22 1892
  0x8101820608081b04040d01034040c81903

private def c12_15 := witness48 12 21 0 150009 150448 23 1952
  0x2840610182020c10103608081a02068081903

private def c12_16 := witness48 12 20 0 160008 160385 24 2024
  0x14204060820304040d820206c101034040d0103

private def c12_17 := witness48 12 19 0 170007 170384 24 2000
  0xa14203080c101080c10103608081b04040d0103

private def c12_18 := witness48 12 18 0 180006 180384 25 2056
  0x60a10284060820304040e0304040d820206c10103

private def c12_19 := witness48 12 17 0 190005 190321 24 1952
  0x60a142030a101820210182020701820206c10103

private def c12_20 := witness48 12 16 0 200004 200320 24 1928
  0x60c14205080c105080c1010380c1010380c10103

private def c12_21 := witness48 12 15 0 210003 210320 23 1812
  0x70c14305080c2840608085080c1010380c10103

private def c12_22 := witness48 12 14 0 220002 220257 22 1712
  0xe18305081828406082840608081d080c10103

private def c12_23 := witness48 12 13 0 230001 230256 20 1524
  0x1c3860a1828406182840608085080c10103

private def c12_24 := witness48 12 12 0 240000 240256 19 1412
  0x20070c1c30508182840608305080c10103

private def c12_25 := witness48 12 11 0 250000 250193 16 1156
  0x801c3860a1c305080c305080c1010

private def c12_26 := witness48 12 10 0 260000 260192 14 976
  0x800400e183860a103860a101820

private def c12_27 := witness48 12 9 0 270000 270192 12 804
  0x900400e0400e182870c142030

private def c12_28 := witness48 12 8 0 280000 280129 10 648
  0x90040020070c0400e182840

private def c12_29 := witness48 12 7 0 290000 290128 8 500
  0x2401200801c0801c3050

private def c12_30 := witness48 12 6 0 300000 300128 7 416
  0x14009004002401003860

private def c12_31 := witness48 12 5 0 310000 310065 5 288
  0x140090048020070

private def c12_32 := witness48 12 4 0 320000 320064 4 220
  0x2801400900400

private def c12_33 := witness48 12 3 0 330000 330064 3 156
  0x1600a00480

private def c12_34 := witness48 12 2 0 340000 340001 2 100
  0xb00500

private def c12_35 := witness48 12 1 0 350000 350000 1 48
  0x580

private def c12_36 := witness48 12 0 0 360000 360000 1 44
  0x600

private def chunks12 : List (Chunk 12) := [
  c12_0, c12_1, c12_2, c12_3, c12_4, c12_5, c12_6, c12_7, c12_8, c12_9,
  c12_10, c12_11, c12_12, c12_13, c12_14, c12_15, c12_16, c12_17, c12_18, c12_19,
  c12_20, c12_21, c12_22, c12_23, c12_24, c12_25, c12_26, c12_27, c12_28, c12_29,
  c12_30, c12_31, c12_32, c12_33, c12_34, c12_35, c12_36]

def rows12 := rowsFrom chunks12

theorem good12 : ∀ r ∈ rows12, good 12 r = true := rowsFrom_good chunks12

theorem sorted12 : rows12.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks12 0 (by decide +kernel)).1

theorem mass12 (i : Fin 51) :
    bandCount 12 (i.val : ℤ) 50 13 ≤ (rows12.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks12).filter _).length
  rw [mass_eq]
  have h : (List.range 51).all (fun j => decide (bandCount 12 (j : ℤ) 50 13 ≤ mass j chunks12)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total12 : (rows12.map (price 12)).sum = 36400 :=
  (total_eq chunks12).trans (by decide +kernel)

private def c13_0 := witness48 13 39 0 832 832 1 92
  0x3

private def c13_1 := witness48 13 38 0 10769 10769 1 92
  0x3

private def c13_2 := witness48 13 37 0 20706 20768 2 184
  0x33

private def c13_3 := witness48 13 36 0 30643 30768 3 272
  0x1033

private def c13_4 := witness48 13 35 0 40580 40705 4 364
  0x10333

private def c13_5 := witness48 13 34 0 50517 50704 5 452
  0x810333

private def c13_6 := witness48 13 33 0 60454 60704 7 628
  0x808190333

private def c13_7 := witness48 13 32 0 70391 70641 8 716
  0x40408190333

private def c13_8 := witness48 13 31 0 80328 80640 10 892
  0x204040c8190333

private def c13_9 := witness48 13 30 0 90265 90640 12 1060
  0xc10104040c8190333

private def c13_10 := witness48 13 29 0 100202 100577 14 1236
  0x608101034040c8190333

private def c13_11 := witness48 13 28 0 110139 110576 16 1404
  sharedSchedule14

private def c13_12 := witness48 13 27 0 120076 120576 19 1656
  0x80c10304040d01034040c8190333

private def c13_13 := witness48 13 26 0 130013 130513 21 1824
  0x203060808304040d01034040c8190333

private def c13_14 := witness48 13 25 0 140012 140512 23 1984
  0x8101820608081b04040d01034040c819033

private def c13_15 := witness48 13 24 0 150011 150512 25 2132
  0x14203080c1010608081b04040d01034040c81903

private def c13_16 := witness48 13 23 0 160010 160449 26 2204
  0xa1020304101820206c10103608081a02068081903

private def c13_17 := witness48 13 22 0 170009 170448 27 2264
  0x285080c203040420304040d820206c101034040d0103

private def c13_18 := witness48 13 21 0 180008 180448 28 2320
  0x182840a10182080c1010380c10103608081b04040d0103

private def c13_19 := witness48 13 20 0 190007 190385 28 2296
  0xc142840614203040420304040e0304040d820206c10103

private def c13_20 := witness48 13 19 0 200006 200384 28 2272
  0xc182840a101820a1018202070182020701820206c10103

private def c13_21 := witness48 13 18 0 210005 210384 28 2232
  0x70c14305080c2840608085080c1010380c1010380c10103

private def c13_22 := witness48 13 17 0 220004 220321 27 2132
  0xe18305081828406082840608081d080c1010380c10103

private def c13_23 := witness48 13 16 0 230003 230320 26 2016
  0xe1c3050c142030c1420304042840608081d080c10103

private def c13_24 := witness48 13 15 0 240002 240320 25 1904
  0x1003860e182840c1420304182840608081d080c10103

private def c13_25 := witness48 13 14 0 250001 250257 23 1716
  0x20070e182870c142030c142030404305080c10103

private def c13_26 := witness48 13 13 0 260000 260256 21 1536
  0x2001003860e182840e182840608305080c10103

private def c13_27 := witness48 13 12 0 270000 270256 19 1336
  0x1200801c0801c3050e18284061c305080c1010

private def c13_28 := witness48 13 11 0 280000 280193 16 1092
  0x2401000801c301003860a103860a101820

private def c13_29 := witness48 13 10 0 290000 290192 14 920
  0x2401200801c0801c305020070c142030

private def c13_30 := witness48 13 9 0 300000 300192 12 756
  0x280120080048020070c0400e182840

private def c13_31 := witness48 13 8 0 310000 310129 10 608
  0xa00480240100381200801c3050

private def c13_32 := witness48 13 7 0 320000 320128 8 468
  0x28014009004002401003860

private def c13_33 := witness48 13 6 0 330000 330128 7 388
  0x5802801200a0048020070

private def c13_34 := witness48 13 5 0 340000 340065 5 268
  0x5802801400900400

private def c13_35 := witness48 13 4 0 350000 350064 4 204
  0x2c01600a00480

private def c13_36 := witness48 13 3 0 360000 360064 3 144
  0x1800b00500

private def c13_37 := witness48 13 2 0 370000 370001 2 92
  0xc00580

private def c13_38 := witness48 13 1 0 380000 380000 1 44
  0x600

private def c13_39 := witness48 13 0 0 390000 390000 1 40
  0x680

private def chunks13 : List (Chunk 13) := [
  c13_0, c13_1, c13_2, c13_3, c13_4, c13_5, c13_6, c13_7, c13_8, c13_9,
  c13_10, c13_11, c13_12, c13_13, c13_14, c13_15, c13_16, c13_17, c13_18, c13_19,
  c13_20, c13_21, c13_22, c13_23, c13_24, c13_25, c13_26, c13_27, c13_28, c13_29,
  c13_30, c13_31, c13_32, c13_33, c13_34, c13_35, c13_36, c13_37, c13_38, c13_39]

def rows13 := rowsFrom chunks13

theorem good13 : ∀ r ∈ rows13, good 13 r = true := rowsFrom_good chunks13

theorem sorted13 : rows13.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks13 0 (by decide +kernel)).1

theorem mass13 (i : Fin 51) :
    bandCount 13 (i.val : ℤ) 50 13 ≤ (rows13.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks13).filter _).length
  rw [mass_eq]
  have h : (List.range 51).all (fun j => decide (bandCount 13 (j : ℤ) 50 13 ≤ mass j chunks13)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total13 : (rows13.map (price 13)).sum = 44240 :=
  (total_eq chunks13).trans (by decide +kernel)

private def c14_0 := witness48 14 41 0 10833 10833 1 92
  0x3

private def c14_1 := witness48 14 40 0 20770 20832 2 184
  0x33

private def c14_2 := witness48 14 39 0 30707 30832 3 273
  0x202f33

private def c14_3 := witness48 14 38 0 40644 40769 4 364
  0x10333

private def c14_4 := witness48 14 37 0 50581 50768 5 452
  0x810333

private def c14_5 := witness48 14 36 0 60518 60768 7 629
  0x481bc8190333

private def c14_6 := witness48 14 35 0 70455 70705 8 716
  0x40408190333

private def c14_7 := witness48 14 34 0 80392 80704 10 892
  0x204040c8190333

private def c14_8 := witness48 14 33 0 90329 90704 12 1061
  0x881bd0104040c8190333

private def c14_9 := witness48 14 32 0 100266 100641 14 1236
  0x608101034040c8190333

private def c14_10 := witness48 14 31 0 110203 110640 16 1404
  sharedSchedule14

private def c14_11 := witness48 14 30 0 120140 120640 19 1657
  0x640dec10304040d01034040c8190333

private def c14_12 := witness48 14 29 0 130077 130577 21 1824
  0x203060808304040d01034040c8190333

private def c14_13 := witness48 14 28 0 140014 140576 24 2076
  0x8101820608081b04040d01034040c8190333

private def c14_14 := witness48 14 27 0 150013 150576 26 2225
  0x1081be03080c1010608081b04040d01034040c819033

private def c14_15 := witness48 14 26 0 160012 160513 28 2384
  0x50810182080c10103608081b04040d01034040c81903

private def c14_16 := witness48 14 25 0 170011 170512 29 2444
  0x14284061018202101820206c10103608081a02068081903

private def c14_17 := witness48 14 24 0 180010 180512 31 2585
  0x5206fa10284060820304040e0304040d820206c101034040d0103

private def c14_18 := witness48 14 23 0 190009 190449 31 2560
  0x3050a10185080c101080c1010380c10103608081b04040d0103

private def c14_19 := witness48 14 22 0 200008 200448 32 2616
  0x183050814203041420304040e0304040e0304040d820206c10103

private def c14_20 := witness48 14 21 0 210007 210448 32 2577
  0xc40df82860a10185080c1010a1018202070182020701820206c10103

private def c14_21 := witness48 14 20 0 220006 220385 32 2552
  0xe18305081828406082840608081d080c1010380c1010380c10103

private def c14_22 := witness48 14 19 0 230005 230384 31 2436
  0xe1c3050c142030c1420304042840608081d080c1010380c10103

private def c14_23 := witness48 14 18 0 240004 240384 31 2397
  0xe40dfc3070c142060a101820c1420304040e840608081d080c10103

private def c14_24 := witness48 14 17 0 250003 250321 29 2208
  0x1003870c143860a101860a1018202182840608081d080c10103

private def c14_25 := witness48 14 16 0 260002 260320 28 2096
  0x800400e183860a103860a101820c1420304040f05080c10103

private def c14_26 := witness48 14 15 0 270001 270320 26 1897
  0x40206f2007020070c143860a101870c142030404305080c10103

private def c14_27 := witness48 14 14 0 280000 280257 24 1716
  0x480200100386020070c142070c14203041c305080c10103

private def c14_28 := witness48 14 13 0 290000 290256 21 1452
  0x480240100381003860a0400e18284061c305080c1010

private def c14_29 := witness48 14 12 0 300000 300256 19 1261
  0x12081bc900400240100386020070c14201003860a101820

private def c14_30 := witness48 14 11 0 310000 310193 16 1028
  0xa00480240100381200801c305020070c142030

private def c14_31 := witness48 14 10 0 320000 320192 14 864
  0xa005002401000900400e180900400e182840

private def c14_32 := witness48 14 9 0 330000 330192 12 709
  0x2810379400900500240100381200801c3050

private def c14_33 := witness48 14 8 0 340000 340129 10 568
  0xb0050028012008005002401003860

private def c14_34 := witness48 14 7 0 350000 350128 8 436
  0xb005802801200a0048020070

private def c14_35 := witness48 14 6 0 360000 360128 7 361
  0x16081bcb005002c01400900400

private def c14_36 := witness48 14 5 0 370000 370065 5 248
  0x6002c01600a00480

private def c14_37 := witness48 14 4 0 380000 380064 4 188
  0x3001800b00500

private def c14_38 := witness48 14 3 0 390000 390064 3 133
  0x18081bcc00580

private def c14_39 := witness48 14 2 0 400000 400001 2 84
  0xd00600

private def c14_40 := witness48 14 1 0 410000 410000 1 40
  0x680

private def c14_41 := witness48 14 0 0 420000 420000 1 37
  0x68206f

private def chunks14 : List (Chunk 14) := [
  c14_0, c14_1, c14_2, c14_3, c14_4, c14_5, c14_6, c14_7, c14_8, c14_9,
  c14_10, c14_11, c14_12, c14_13, c14_14, c14_15, c14_16, c14_17, c14_18, c14_19,
  c14_20, c14_21, c14_22, c14_23, c14_24, c14_25, c14_26, c14_27, c14_28, c14_29,
  c14_30, c14_31, c14_32, c14_33, c14_34, c14_35, c14_36, c14_37, c14_38, c14_39,
  c14_40, c14_41]

def rows14 := rowsFrom chunks14

theorem good14 : ∀ r ∈ rows14, good 14 r = true := rowsFrom_good chunks14

theorem sorted14 : rows14.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks14 0 (by decide +kernel)).1

theorem mass14 (i : Fin 51) :
    bandCount 14 (i.val : ℤ) 50 13 ≤ (rows14.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks14).filter _).length
  rw [mass_eq]
  have h : (List.range 51).all (fun j => decide (bandCount 14 (j : ℤ) 50 13 ≤ mass j chunks14)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total14 : (rows14.map (price 14)).sum = 52962 :=
  (total_eq chunks14).trans (by decide +kernel)

end Low48Receipt

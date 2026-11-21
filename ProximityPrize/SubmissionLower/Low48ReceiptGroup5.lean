import ProximityPrize.SubmissionLower.Low48ReceiptGroup10

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Low48Receipt
open K1_13_1_1 (bandCount)

private def c5_0 := witness48 5 15 0 320 320 1 90
  0x0 (by decide +kernel)
private def c5_1 := witness48 5 14 0 10257 10257 1 90
  0x0 (by decide +kernel)
private def c5_2 := witness48 5 13 0 20194 20256 2 180
  0x0 (by decide +kernel)
private def c5_3 := witness48 5 12 0 30131 30256 3 266
  0x2440 (by decide +kernel)
private def c5_4 := witness48 5 11 0 40068 40193 4 356
  0x12200 (by decide +kernel)
private def c5_5 := witness48 5 10 0 50005 50192 5 442
  0x9112200 (by decide +kernel)
private def c5_6 := witness48 5 9 0 60004 60192 6 524
  0x8889102440 (by decide +kernel)
private def c5_7 := witness48 5 8 0 70003 70129 6 520
  0x888911220488 (by decide +kernel)
private def c5_8 := witness48 5 7 0 80002 80128 6 516
  0x889111220488 (by decide +kernel)
private def c5_9 := witness48 5 6 0 90001 90128 6 504
  0xc8911122444488 (by decide +kernel)
private def c5_10 := witness48 5 5 0 100000 100065 5 418
  0x191222444488 (by decide +kernel)
private def c5_11 := witness48 5 4 0 110000 110064 4 324
  0x32264488891 (by decide +kernel)
private def c5_12 := witness48 5 3 0 120000 120064 3 234
  0x844c8911 (by decide +kernel)
private def c5_13 := witness48 5 2 0 130000 130001 2 152
  0x108991 (by decide +kernel)
private def c5_14 := witness48 5 1 0 140000 140000 1 74
  0x211 (by decide +kernel)
private def c5_15 := witness48 5 0 0 150000 150000 1 70
  0x291 (by decide +kernel)
private def chunks5 : List (Chunk 5) := [
  c5_0, c5_1, c5_2, c5_3, c5_4, c5_5, c5_6, c5_7, c5_8, c5_9, c5_10, c5_11,
  c5_12, c5_13, c5_14, c5_15]
def rows5 := rowsFrom chunks5
theorem good5 : ∀ r ∈ rows5, good 5 r = true := rowsFrom_good chunks5
theorem sorted5 : rows5.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks5 0 (by decide +kernel)).1
theorem mass5 (i : Fin 50) :
    bandCount 5 (i.val : ℤ) 49 13 ≤ (rows5.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks5).filter _).length
  rw [mass_eq]
  have h : (List.range 50).all (fun j => decide (bandCount 5 (j : ℤ) 49 13 ≤ mass j chunks5)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total5 : (rows5.map (price 5)).sum = 4760 :=
  (total_eq chunks5).trans (by decide +kernel)

private def c6_0 := witness48 6 18 0 384 384 1 90
  0x0 (by decide +kernel)
private def c6_1 := witness48 6 17 0 10321 10321 1 90
  0x0 (by decide +kernel)
private def c6_2 := witness48 6 16 0 20258 20320 2 180
  0x0 (by decide +kernel)
private def c6_3 := witness48 6 15 0 30195 30320 3 266
  0x2440 (by decide +kernel)
private def c6_4 := witness48 6 14 0 40132 40257 4 356
  0x12200 (by decide +kernel)
private def c6_5 := witness48 6 13 0 50069 50256 5 442
  0x9112200 (by decide +kernel)
private def c6_6 := witness48 6 12 0 60006 60256 7 614
  0x44448812200 (by decide +kernel)
private def c6_7 := witness48 6 11 0 70005 70193 7 610
  0x4444889102440 (by decide +kernel)
private def c6_8 := witness48 6 10 0 80004 80192 8 692
  0x2224444881220488 (by decide +kernel)
private def c6_9 := witness48 6 9 0 90003 90192 8 680
  0x322444489111220488 (by decide +kernel)
private def c6_10 := witness48 6 8 0 100002 100129 8 676
  0x322444888910444488 (by decide +kernel)
private def c6_11 := witness48 6 7 0 110001 110128 7 582
  0x644c8911122444488 (by decide +kernel)
private def c6_12 := witness48 6 6 0 120000 120128 7 570
  0x844c8911322444488 (by decide +kernel)
private def c6_13 := witness48 6 5 0 130000 130065 5 398
  0x21132264488891 (by decide +kernel)
private def c6_14 := witness48 6 4 0 140000 140064 4 308
  0x422844c8911 (by decide +kernel)
private def c6_15 := witness48 6 3 0 150000 150064 3 222
  0xa4508991 (by decide +kernel)
private def c6_16 := witness48 6 2 0 160000 160001 2 144
  0x148a11 (by decide +kernel)
private def c6_17 := witness48 6 1 0 170000 170000 1 70
  0x291 (by decide +kernel)
private def c6_18 := witness48 6 0 0 180000 180000 1 66
  0x311 (by decide +kernel)
private def chunks6 : List (Chunk 6) := [
  c6_0, c6_1, c6_2, c6_3, c6_4, c6_5, c6_6, c6_7, c6_8, c6_9, c6_10, c6_11,
  c6_12, c6_13, c6_14, c6_15, c6_16, c6_17, c6_18]
def rows6 := rowsFrom chunks6
theorem good6 : ∀ r ∈ rows6, good 6 r = true := rowsFrom_good chunks6
theorem sorted6 : rows6.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks6 0 (by decide +kernel)).1
theorem mass6 (i : Fin 50) :
    bandCount 6 (i.val : ℤ) 49 13 ≤ (rows6.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks6).filter _).length
  rw [mass_eq]
  have h : (List.range 50).all (fun j => decide (bandCount 6 (j : ℤ) 49 13 ≤ mass j chunks6)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total6 : (rows6.map (price 6)).sum = 7056 :=
  (total_eq chunks6).trans (by decide +kernel)

private def c7_0 := witness48 7 21 0 448 448 1 90
  0x0 (by decide +kernel)
private def c7_1 := witness48 7 20 0 10385 10385 1 90
  0x0 (by decide +kernel)
private def c7_2 := witness48 7 19 0 20322 20384 2 180
  0x0 (by decide +kernel)
private def c7_3 := witness48 7 18 0 30259 30384 3 266
  0x2440 (by decide +kernel)
private def c7_4 := witness48 7 17 0 40196 40321 4 356
  0x12200 (by decide +kernel)
private def c7_5 := witness48 7 16 0 50133 50320 5 442
  0x9112200 (by decide +kernel)
private def c7_6 := witness48 7 15 0 60070 60320 7 614
  0x44448812200 (by decide +kernel)
private def c7_7 := witness48 7 14 0 70007 70257 8 700
  0x22224448812200 (by decide +kernel)
private def c7_8 := witness48 7 13 0 80006 80256 9 782
  0x11122224409102440 (by decide +kernel)
private def c7_9 := witness48 7 12 0 90005 90256 10 856
  0xc89111224444881220488 (by decide +kernel)
private def c7_10 := witness48 7 11 0 100004 100193 10 852
  0xc89112222441111220488 (by decide +kernel)
private def c7_11 := witness48 7 10 0 110003 110192 10 840
  0xc8991222244888910444488 (by decide +kernel)
private def c7_12 := witness48 7 9 0 120002 120192 10 828
  0x108991222644888910444488 (by decide +kernel)
private def c7_13 := witness48 7 8 0 130001 130129 9 734
  0x21132264488891322444488 (by decide +kernel)
private def c7_14 := witness48 7 7 0 140000 140128 8 644
  0x422844c8911322444488 (by decide +kernel)
private def c7_15 := witness48 7 6 0 150000 150128 7 542
  0xa450899142264488891 (by decide +kernel)
private def c7_16 := witness48 7 5 0 160000 160065 5 378
  0x291422844c8911 (by decide +kernel)
private def c7_17 := witness48 7 4 0 170000 170064 4 292
  0x522a4508991 (by decide +kernel)
private def c7_18 := witness48 7 3 0 180000 180064 3 210
  0xc4548a11 (by decide +kernel)
private def c7_19 := witness48 7 2 0 190000 190001 2 136
  0x188a91 (by decide +kernel)
private def c7_20 := witness48 7 1 0 200000 200000 1 66
  0x311 (by decide +kernel)
private def c7_21 := witness48 7 0 0 210000 210000 1 62
  0x391 (by decide +kernel)
private def chunks7 : List (Chunk 7) := [
  c7_0, c7_1, c7_2, c7_3, c7_4, c7_5, c7_6, c7_7, c7_8, c7_9, c7_10, c7_11,
  c7_12, c7_13, c7_14, c7_15, c7_16, c7_17, c7_18, c7_19, c7_20, c7_21]
def rows7 := rowsFrom chunks7
theorem good7 : ∀ r ∈ rows7, good 7 r = true := rowsFrom_good chunks7
theorem sorted7 : rows7.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks7 0 (by decide +kernel)).1
theorem mass7 (i : Fin 50) :
    bandCount 7 (i.val : ℤ) 49 13 ≤ (rows7.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks7).filter _).length
  rw [mass_eq]
  have h : (List.range 50).all (fun j => decide (bandCount 7 (j : ℤ) 49 13 ≤ mass j chunks7)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total7 : (rows7.map (price 7)).sum = 9960 :=
  (total_eq chunks7).trans (by decide +kernel)

private def c8_0 := witness48 8 24 0 512 512 1 90
  0x0 (by decide +kernel)
private def c8_1 := witness48 8 23 0 10449 10449 1 90
  0x0 (by decide +kernel)
private def c8_2 := witness48 8 22 0 20386 20448 2 180
  0x0 (by decide +kernel)
private def c8_3 := witness48 8 21 0 30323 30448 3 266
  0x2440 (by decide +kernel)
private def c8_4 := witness48 8 20 0 40260 40385 4 356
  0x12200 (by decide +kernel)
private def c8_5 := witness48 8 19 0 50197 50384 5 442
  0x9112200 (by decide +kernel)
private def c8_6 := witness48 8 18 0 60134 60384 7 614
  0x44448812200 (by decide +kernel)
private def c8_7 := witness48 8 17 0 70071 70321 8 700
  0x22224448812200 (by decide +kernel)
private def c8_8 := witness48 8 16 0 80008 80320 10 872
  0x88911122048812200 (by decide +kernel)
private def c8_9 := witness48 8 15 0 90007 90320 11 946
  0x6448889122224409102440 (by decide +kernel)
private def c8_10 := witness48 8 14 0 100006 100257 12 1028
  0x3224448889104444881220488 (by decide +kernel)
private def c8_11 := witness48 8 13 0 110005 110256 12 1016
  0x322644888912222441111220488 (by decide +kernel)
private def c8_12 := witness48 8 12 0 120004 120256 13 1086
  0x211322444c89111220888910444488 (by decide +kernel)
private def c8_13 := witness48 8 11 0 130003 130193 12 992
  0x422644c8911122644888910444488 (by decide +kernel)
private def c8_14 := witness48 8 10 0 140002 140192 12 980
  0x422844c8911322444488322444488 (by decide +kernel)
private def c8_15 := witness48 8 9 0 150001 150192 11 878
  0xa450899142264488891322444488 (by decide +kernel)
private def c8_16 := witness48 8 8 0 160000 160129 10 788
  0x148a1142264488a11322444488 (by decide +kernel)
private def c8_17 := witness48 8 7 0 170000 170128 8 612
  0x522a450899142264488891 (by decide +kernel)
private def c8_18 := witness48 8 6 0 180000 180128 7 514
  0xc4548a11522844c8911 (by decide +kernel)
private def c8_19 := witness48 8 5 0 190000 190065 5 358
  0x311522a4508991 (by decide +kernel)
private def c8_20 := witness48 8 4 0 200000 200064 4 276
  0x622c4548a11 (by decide +kernel)
private def c8_21 := witness48 8 3 0 210000 210064 3 198
  0xe4588a91 (by decide +kernel)
private def c8_22 := witness48 8 2 0 220000 220001 2 128
  0x1c8b11 (by decide +kernel)
private def c8_23 := witness48 8 1 0 230000 230000 1 62
  0x391 (by decide +kernel)
private def c8_24 := witness48 8 0 0 240000 240000 1 58
  0x411 (by decide +kernel)
private def chunks8 : List (Chunk 8) := [
  c8_0, c8_1, c8_2, c8_3, c8_4, c8_5, c8_6, c8_7, c8_8, c8_9, c8_10, c8_11,
  c8_12, c8_13, c8_14, c8_15, c8_16, c8_17, c8_18, c8_19, c8_20, c8_21, c8_22, c8_23,
  c8_24]
def rows8 := rowsFrom chunks8
theorem good8 : ∀ r ∈ rows8, good 8 r = true := rowsFrom_good chunks8
theorem sorted8 : rows8.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks8 0 (by decide +kernel)).1
theorem mass8 (i : Fin 50) :
    bandCount 8 (i.val : ℤ) 49 13 ≤ (rows8.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks8).filter _).length
  rw [mass_eq]
  have h : (List.range 50).all (fun j => decide (bandCount 8 (j : ℤ) 49 13 ≤ mass j chunks8)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total8 : (rows8.map (price 8)).sum = 13530 :=
  (total_eq chunks8).trans (by decide +kernel)

private def c9_0 := witness48 9 27 0 576 576 1 90
  0x0 (by decide +kernel)
private def c9_1 := witness48 9 26 0 10513 10513 1 90
  0x0 (by decide +kernel)
private def c9_2 := witness48 9 25 0 20450 20512 2 180
  0x0 (by decide +kernel)
private def c9_3 := witness48 9 24 0 30387 30512 3 266
  0x2440 (by decide +kernel)
private def c9_4 := witness48 9 23 0 40324 40449 4 356
  0x12200 (by decide +kernel)
private def c9_5 := witness48 9 22 0 50261 50448 5 442
  0x9112200 (by decide +kernel)
private def c9_6 := witness48 9 21 0 60198 60448 7 614
  0x44448812200 (by decide +kernel)
private def c9_7 := witness48 9 20 0 70135 70385 8 700
  0x22224448812200 (by decide +kernel)
private def c9_8 := witness48 9 19 0 80072 80384 10 872
  0x88911122048812200 (by decide +kernel)
private def c9_9 := witness48 9 18 0 90009 90384 12 1036
  0x32244448911122048812200 (by decide +kernel)
private def c9_10 := witness48 9 17 0 100008 100321 13 1118
  0x19122244448822224409102440 (by decide +kernel)
private def c9_11 := witness48 9 16 0 110007 110320 14 1192
  0xc89912222448889104444881220488 (by decide +kernel)
private def c9_12 := witness48 9 15 0 120006 120320 15 1262
  0x844c89113224444882222441111220488 (by decide +kernel)
private def c9_13 := witness48 9 14 0 130005 130257 15 1250
  0x844c8991222244c89111220888910444488 (by decide +kernel)
private def c9_14 := witness48 9 13 0 140004 140256 15 1238
  0x84508991222644888910644888910444488 (by decide +kernel)
private def c9_15 := witness48 9 12 0 150003 150256 15 1214
  0xa450899142264488891322444488322444488 (by decide +kernel)
private def c9_16 := witness48 9 11 0 160002 160193 14 1124
  0x148a1142264488a11322444488322444488 (by decide +kernel)
private def c9_17 := witness48 9 10 0 170001 170192 13 1022
  0x291522844c8a1132244448a11322444488 (by decide +kernel)
private def c9_18 := witness48 9 9 0 180000 180192 12 924
  0x622a4508a9142264488a11322444488 (by decide +kernel)
private def c9_19 := witness48 9 8 0 190000 190129 10 748
  0x188a91522844c8a9142264488891 (by decide +kernel)
private def c9_20 := witness48 9 7 0 200000 200128 8 580
  0x622c4548a11522844c8911 (by decide +kernel)
private def c9_21 := witness48 9 6 0 210000 210128 7 486
  0xe4588a91622a4508991 (by decide +kernel)
private def c9_22 := witness48 9 5 0 220000 220065 5 338
  0x391622c4548a11 (by decide +kernel)
private def c9_23 := witness48 9 4 0 230000 230064 4 260
  0x722e4588a91 (by decide +kernel)
private def c9_24 := witness48 9 3 0 240000 240064 3 186
  0x1045c8b11 (by decide +kernel)
private def c9_25 := witness48 9 2 0 250000 250001 2 120
  0x208b91 (by decide +kernel)
private def c9_26 := witness48 9 1 0 260000 260000 1 58
  0x411 (by decide +kernel)
private def c9_27 := witness48 9 0 0 270000 270000 1 54
  0x491 (by decide +kernel)
private def chunks9 : List (Chunk 9) := [
  c9_0, c9_1, c9_2, c9_3, c9_4, c9_5, c9_6, c9_7, c9_8, c9_9, c9_10, c9_11,
  c9_12, c9_13, c9_14, c9_15, c9_16, c9_17, c9_18, c9_19, c9_20, c9_21, c9_22, c9_23,
  c9_24, c9_25, c9_26, c9_27]
def rows9 := rowsFrom chunks9
theorem good9 : ∀ r ∈ rows9, good 9 r = true := rowsFrom_good chunks9
theorem sorted9 : rows9.Pairwise (fun a b => a.tag < b.tag) := (rowsFrom_sorted_aux chunks9 0 (by decide +kernel)).1
theorem mass9 (i : Fin 50) :
    bandCount 9 (i.val : ℤ) 49 13 ≤ (rows9.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks9).filter _).length
  rw [mass_eq]
  have h : (List.range 50).all (fun j => decide (bandCount 9 (j : ℤ) 49 13 ≤ mass j chunks9)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total9 : (rows9.map (price 9)).sum = 17820 :=
  (total_eq chunks9).trans (by decide +kernel)

end Low48Receipt

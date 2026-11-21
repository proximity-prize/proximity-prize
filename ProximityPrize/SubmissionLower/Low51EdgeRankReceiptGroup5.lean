import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptBase

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Low51EdgeRankReceipt
open K1_13_1_1 (bandCount)

private def cert5_0 := witnessLow51 5 15 0 320 320 1 94
  0x0 (by decide +kernel)
private def cert5_1 := witnessLow51 5 14 0 10257 10257 1 94
  0x0 (by decide +kernel)
private def cert5_2 := witnessLow51 5 13 0 20194 20256 2 188
  0x0 (by decide +kernel)
private def cert5_3 := witnessLow51 5 12 0 30131 30256 3 278
  0x2440 (by decide +kernel)
private def cert5_4 := witnessLow51 5 11 0 40068 40193 4 372
  0x12200 (by decide +kernel)
private def cert5_5 := witnessLow51 5 10 0 50005 50192 5 462
  0x9112200 (by decide +kernel)
private def cert5_6 := witnessLow51 5 9 0 60004 60192 6 548
  0x8889102440 (by decide +kernel)
private def cert5_7 := witnessLow51 5 8 0 70003 70129 6 544
  0x888911220488 (by decide +kernel)
private def cert5_8 := witnessLow51 5 7 0 80002 80128 6 540
  0x889111220488 (by decide +kernel)
private def cert5_9 := witnessLow51 5 6 0 90001 90128 6 528
  0xc8911122444488 (by decide +kernel)
private def cert5_10 := witnessLow51 5 5 0 100000 100065 5 438
  0x191222444488 (by decide +kernel)
private def cert5_11 := witnessLow51 5 4 0 110000 110064 4 340
  0x32264488891 (by decide +kernel)
private def cert5_12 := witnessLow51 5 3 0 120000 120064 3 246
  0x844c8911 (by decide +kernel)
private def cert5_13 := witnessLow51 5 2 0 130000 130001 2 160
  0x108991 (by decide +kernel)
private def cert5_14 := witnessLow51 5 1 0 140000 140000 1 78
  0x211 (by decide +kernel)
private def cert5_15 := witnessLow51 5 0 0 150000 150000 1 74
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

theorem total5 : (rows5.map (price 5)).sum = 4984 :=
  (total_eq chunks5).trans (by decide +kernel)

private def cert6_0 := witnessLow51 6 18 0 384 384 1 94
  0x0 (by decide +kernel)
private def cert6_1 := witnessLow51 6 17 0 10321 10321 1 94
  0x0 (by decide +kernel)
private def cert6_2 := witnessLow51 6 16 0 20258 20320 2 188
  0x0 (by decide +kernel)
private def cert6_3 := witnessLow51 6 15 0 30195 30320 3 278
  0x2440 (by decide +kernel)
private def cert6_4 := witnessLow51 6 14 0 40132 40257 4 372
  0x12200 (by decide +kernel)
private def cert6_5 := witnessLow51 6 13 0 50069 50256 5 462
  0x9112200 (by decide +kernel)
private def cert6_6 := witnessLow51 6 12 0 60006 60256 7 642
  0x44448812200 (by decide +kernel)
private def cert6_7 := witnessLow51 6 11 0 70005 70193 7 638
  0x4444889102440 (by decide +kernel)
private def cert6_8 := witnessLow51 6 10 0 80004 80192 8 724
  0x2224444881220488 (by decide +kernel)
private def cert6_9 := witnessLow51 6 9 0 90003 90192 8 712
  0x322444489111220488 (by decide +kernel)
private def cert6_10 := witnessLow51 6 8 0 100002 100129 8 708
  0x322444888910444488 (by decide +kernel)
private def cert6_11 := witnessLow51 6 7 0 110001 110128 7 610
  0x644c8911122444488 (by decide +kernel)
private def cert6_12 := witnessLow51 6 6 0 120000 120128 7 598
  0x844c8911322444488 (by decide +kernel)
private def cert6_13 := witnessLow51 6 5 0 130000 130065 5 418
  0x21132264488891 (by decide +kernel)
private def cert6_14 := witnessLow51 6 4 0 140000 140064 4 324
  0x422844c8911 (by decide +kernel)
private def cert6_15 := witnessLow51 6 3 0 150000 150064 3 234
  0xa4508991 (by decide +kernel)
private def cert6_16 := witnessLow51 6 2 0 160000 160001 2 152
  0x148a11 (by decide +kernel)
private def cert6_17 := witnessLow51 6 1 0 170000 170000 1 74
  0x291 (by decide +kernel)
private def cert6_18 := witnessLow51 6 0 0 180000 180000 1 70
  0x311 (by decide +kernel)
private def chunks6 : List (Chunk 6) := [
  cert6_0, cert6_1, cert6_2, cert6_3, cert6_4, cert6_5, cert6_6, cert6_7, cert6_8, cert6_9,
  cert6_10, cert6_11, cert6_12, cert6_13, cert6_14, cert6_15, cert6_16, cert6_17, cert6_18]

def rows6 := rowsFrom chunks6

theorem good6 : ∀ r ∈ rows6, good 6 r = true := rowsFrom_good chunks6

theorem sorted6 : rows6.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks6 0 (by decide +kernel)).1

theorem mass6 (i : Fin 54) :
    bandCount 6 (i.val : ℤ) 53 13 ≤ (rows6.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks6).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 6 (j : ℤ) 53 13 ≤ mass j chunks6)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total6 : (rows6.map (price 6)).sum = 7392 :=
  (total_eq chunks6).trans (by decide +kernel)

private def cert7_0 := witnessLow51 7 21 0 448 448 1 94
  0x0 (by decide +kernel)
private def cert7_1 := witnessLow51 7 20 0 10385 10385 1 94
  0x0 (by decide +kernel)
private def cert7_2 := witnessLow51 7 19 0 20322 20384 2 188
  0x0 (by decide +kernel)
private def cert7_3 := witnessLow51 7 18 0 30259 30384 3 278
  0x2440 (by decide +kernel)
private def cert7_4 := witnessLow51 7 17 0 40196 40321 4 372
  0x12200 (by decide +kernel)
private def cert7_5 := witnessLow51 7 16 0 50133 50320 5 462
  0x9112200 (by decide +kernel)
private def cert7_6 := witnessLow51 7 15 0 60070 60320 7 642
  0x44448812200 (by decide +kernel)
private def cert7_7 := witnessLow51 7 14 0 70007 70257 8 732
  0x22224448812200 (by decide +kernel)
private def cert7_8 := witnessLow51 7 13 0 80006 80256 9 818
  0x11122224409102440 (by decide +kernel)
private def cert7_9 := witnessLow51 7 12 0 90005 90256 10 896
  0xc89111224444881220488 (by decide +kernel)
private def cert7_10 := witnessLow51 7 11 0 100004 100193 10 892
  0xc89112222441111220488 (by decide +kernel)
private def cert7_11 := witnessLow51 7 10 0 110003 110192 10 880
  0xc8991222244888910444488 (by decide +kernel)
private def cert7_12 := witnessLow51 7 9 0 120002 120192 10 868
  0x108991222644888910444488 (by decide +kernel)
private def cert7_13 := witnessLow51 7 8 0 130001 130129 9 770
  0x21132264488891322444488 (by decide +kernel)
private def cert7_14 := witnessLow51 7 7 0 140000 140128 8 676
  0x422844c8911322444488 (by decide +kernel)
private def cert7_15 := witnessLow51 7 6 0 150000 150128 7 570
  0xa450899142264488891 (by decide +kernel)
private def cert7_16 := witnessLow51 7 5 0 160000 160065 5 398
  0x291422844c8911 (by decide +kernel)
private def cert7_17 := witnessLow51 7 4 0 170000 170064 4 308
  0x522a4508991 (by decide +kernel)
private def cert7_18 := witnessLow51 7 3 0 180000 180064 3 222
  0xc4548a11 (by decide +kernel)
private def cert7_19 := witnessLow51 7 2 0 190000 190001 2 144
  0x188a91 (by decide +kernel)
private def cert7_20 := witnessLow51 7 1 0 200000 200000 1 70
  0x311 (by decide +kernel)
private def cert7_21 := witnessLow51 7 0 0 210000 210000 1 66
  0x391 (by decide +kernel)
private def chunks7 : List (Chunk 7) := [
  cert7_0, cert7_1, cert7_2, cert7_3, cert7_4, cert7_5, cert7_6, cert7_7, cert7_8, cert7_9,
  cert7_10, cert7_11, cert7_12, cert7_13, cert7_14, cert7_15, cert7_16, cert7_17, cert7_18, cert7_19,
  cert7_20, cert7_21]

def rows7 := rowsFrom chunks7

theorem good7 : ∀ r ∈ rows7, good 7 r = true := rowsFrom_good chunks7

theorem sorted7 : rows7.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks7 0 (by decide +kernel)).1

theorem mass7 (i : Fin 54) :
    bandCount 7 (i.val : ℤ) 53 13 ≤ (rows7.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks7).filter _).length
  rw [mass_eq]
  have h : (List.range 54).all
      (fun j => decide (bandCount 7 (j : ℤ) 53 13 ≤ mass j chunks7)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total7 : (rows7.map (price 7)).sum = 10440 :=
  (total_eq chunks7).trans (by decide +kernel)

private def cert8_0 := witnessLow51 8 24 0 512 512 1 94
  0x0 (by decide +kernel)
private def cert8_1 := witnessLow51 8 23 0 10449 10449 1 94
  0x0 (by decide +kernel)
private def cert8_2 := witnessLow51 8 22 0 20386 20448 2 188
  0x0 (by decide +kernel)
private def cert8_3 := witnessLow51 8 21 0 30323 30448 3 278
  0x2440 (by decide +kernel)
private def cert8_4 := witnessLow51 8 20 0 40260 40385 4 372
  0x12200 (by decide +kernel)
private def cert8_5 := witnessLow51 8 19 0 50197 50384 5 462
  0x9112200 (by decide +kernel)
private def cert8_6 := witnessLow51 8 18 0 60134 60384 7 642
  0x44448812200 (by decide +kernel)
private def cert8_7 := witnessLow51 8 17 0 70071 70321 8 732
  0x22224448812200 (by decide +kernel)
private def cert8_8 := witnessLow51 8 16 0 80008 80320 10 912
  0x88911122048812200 (by decide +kernel)
private def cert8_9 := witnessLow51 8 15 0 90007 90320 11 990
  0x6448889122224409102440 (by decide +kernel)
private def cert8_10 := witnessLow51 8 14 0 100006 100257 12 1076
  0x3224448889104444881220488 (by decide +kernel)
private def cert8_11 := witnessLow51 8 13 0 110005 110256 12 1064
  0x322644888912222441111220488 (by decide +kernel)
private def cert8_12 := witnessLow51 8 12 0 120004 120256 13 1138
  0x211322444c89111220888910444488 (by decide +kernel)
private def cert8_13 := witnessLow51 8 11 0 130003 130193 12 1040
  0x422644c8911122644888910444488 (by decide +kernel)
private def cert8_14 := witnessLow51 8 10 0 140002 140192 12 1028
  0x422844c8911322444488322444488 (by decide +kernel)
private def cert8_15 := witnessLow51 8 9 0 150001 150192 11 922
  0xa450899142264488891322444488 (by decide +kernel)
private def cert8_16 := witnessLow51 8 8 0 160000 160129 10 828
  0x148a1142264488a11322444488 (by decide +kernel)
private def cert8_17 := witnessLow51 8 7 0 170000 170128 8 644
  0x522a450899142264488891 (by decide +kernel)
private def cert8_18 := witnessLow51 8 6 0 180000 180128 7 542
  0xc4548a11522844c8911 (by decide +kernel)
private def cert8_19 := witnessLow51 8 5 0 190000 190065 5 378
  0x311522a4508991 (by decide +kernel)
private def cert8_20 := witnessLow51 8 4 0 200000 200064 4 292
  0x622c4548a11 (by decide +kernel)
private def cert8_21 := witnessLow51 8 3 0 210000 210064 3 210
  0xe4588a91 (by decide +kernel)
private def cert8_22 := witnessLow51 8 2 0 220000 220001 2 136
  0x1c8b11 (by decide +kernel)
private def cert8_23 := witnessLow51 8 1 0 230000 230000 1 66
  0x391 (by decide +kernel)
private def cert8_24 := witnessLow51 8 0 0 240000 240000 1 62
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

theorem total8 : (rows8.map (price 8)).sum = 14190 :=
  (total_eq chunks8).trans (by decide +kernel)

private def cert9_0 := witnessLow51 9 27 0 576 576 1 94
  0x0 (by decide +kernel)
private def cert9_1 := witnessLow51 9 26 0 10513 10513 1 94
  0x0 (by decide +kernel)
private def cert9_2 := witnessLow51 9 25 0 20450 20512 2 188
  0x0 (by decide +kernel)
private def cert9_3 := witnessLow51 9 24 0 30387 30512 3 278
  0x2440 (by decide +kernel)
private def cert9_4 := witnessLow51 9 23 0 40324 40449 4 372
  0x12200 (by decide +kernel)
private def cert9_5 := witnessLow51 9 22 0 50261 50448 5 462
  0x9112200 (by decide +kernel)
private def cert9_6 := witnessLow51 9 21 0 60198 60448 7 642
  0x44448812200 (by decide +kernel)
private def cert9_7 := witnessLow51 9 20 0 70135 70385 8 732
  0x22224448812200 (by decide +kernel)
private def cert9_8 := witnessLow51 9 19 0 80072 80384 10 912
  0x88911122048812200 (by decide +kernel)
private def cert9_9 := witnessLow51 9 18 0 90009 90384 12 1084
  0x32244448911122048812200 (by decide +kernel)
private def cert9_10 := witnessLow51 9 17 0 100008 100321 13 1170
  0x19122244448822224409102440 (by decide +kernel)
private def cert9_11 := witnessLow51 9 16 0 110007 110320 14 1248
  0xc89912222448889104444881220488 (by decide +kernel)
private def cert9_12 := witnessLow51 9 15 0 120006 120320 15 1322
  0x844c89113224444882222441111220488 (by decide +kernel)
private def cert9_13 := witnessLow51 9 14 0 130005 130257 15 1310
  0x844c8991222244c89111220888910444488 (by decide +kernel)
private def cert9_14 := witnessLow51 9 13 0 140004 140256 15 1298
  0x84508991222644888910644888910444488 (by decide +kernel)
private def cert9_15 := witnessLow51 9 12 0 150003 150256 15 1274
  0xa450899142264488891322444488322444488 (by decide +kernel)
private def cert9_16 := witnessLow51 9 11 0 160002 160193 14 1180
  0x148a1142264488a11322444488322444488 (by decide +kernel)
private def cert9_17 := witnessLow51 9 10 0 170001 170192 13 1074
  0x291522844c8a1132244448a11322444488 (by decide +kernel)
private def cert9_18 := witnessLow51 9 9 0 180000 180192 12 972
  0x622a4508a9142264488a11322444488 (by decide +kernel)
private def cert9_19 := witnessLow51 9 8 0 190000 190129 10 788
  0x188a91522844c8a9142264488891 (by decide +kernel)
private def cert9_20 := witnessLow51 9 7 0 200000 200128 8 612
  0x622c4548a11522844c8911 (by decide +kernel)
private def cert9_21 := witnessLow51 9 6 0 210000 210128 7 514
  0xe4588a91622a4508991 (by decide +kernel)
private def cert9_22 := witnessLow51 9 5 0 220000 220065 5 358
  0x391622c4548a11 (by decide +kernel)
private def cert9_23 := witnessLow51 9 4 0 230000 230064 4 276
  0x722e4588a91 (by decide +kernel)
private def cert9_24 := witnessLow51 9 3 0 240000 240064 3 198
  0x1045c8b11 (by decide +kernel)
private def cert9_25 := witnessLow51 9 2 0 250000 250001 2 128
  0x208b91 (by decide +kernel)
private def cert9_26 := witnessLow51 9 1 0 260000 260000 1 62
  0x411 (by decide +kernel)
private def cert9_27 := witnessLow51 9 0 0 270000 270000 1 58
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

theorem total9 : (rows9.map (price 9)).sum = 18700 :=
  (total_eq chunks9).trans (by decide +kernel)

end Low51EdgeRankReceipt

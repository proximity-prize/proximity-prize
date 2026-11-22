import ProximityPrize.SubmissionLower.Final50RankReceiptBase

set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Final50RankReceipt
open K1_13_1_1 (bandCount)

private def cert5_0 := witnessFinal50 5 15 0 320 320 1 99
  0x0 (by decide +kernel)
private def cert5_1 := witnessFinal50 5 14 0 10257 10257 1 99
  0x0 (by decide +kernel)
private def cert5_2 := witnessFinal50 5 13 0 20194 20256 2 198
  0x0 (by decide +kernel)
private def cert5_3 := witnessFinal50 5 12 0 30131 30256 3 293
  0x2440 (by decide +kernel)
private def cert5_4 := witnessFinal50 5 11 0 40068 40193 4 392
  0x12200 (by decide +kernel)
private def cert5_5 := witnessFinal50 5 10 0 50005 50192 5 487
  0x9112200 (by decide +kernel)
private def cert5_6 := witnessFinal50 5 9 0 60004 60192 6 578
  0x8889102440 (by decide +kernel)
private def cert5_7 := witnessFinal50 5 8 0 70003 70129 6 574
  0x888911220488 (by decide +kernel)
private def cert5_8 := witnessFinal50 5 7 0 80002 80128 6 570
  0x889111220488 (by decide +kernel)
private def cert5_9 := witnessFinal50 5 6 0 90001 90128 6 558
  0xc8911122444488 (by decide +kernel)
private def cert5_10 := witnessFinal50 5 5 0 100000 100065 5 463
  0x191222444488 (by decide +kernel)
private def cert5_11 := witnessFinal50 5 4 0 110000 110064 4 360
  0x32264488891 (by decide +kernel)
private def cert5_12 := witnessFinal50 5 3 0 120000 120064 3 261
  0x844c8911 (by decide +kernel)
private def cert5_13 := witnessFinal50 5 2 0 130000 130001 2 170
  0x108991 (by decide +kernel)
private def cert5_14 := witnessFinal50 5 1 0 140000 140000 1 83
  0x211 (by decide +kernel)
private def cert5_15 := witnessFinal50 5 0 0 150000 150000 1 79
  0x291 (by decide +kernel)
private def chunks5 : List (Chunk 5) := [
  cert5_0,
  cert5_1,
  cert5_2,
  cert5_3,
  cert5_4,
  cert5_5,
  cert5_6,
  cert5_7,
  cert5_8,
  cert5_9,
  cert5_10,
  cert5_11,
  cert5_12,
  cert5_13,
  cert5_14,
  cert5_15]
def rows5 := rowsFrom chunks5

theorem good5 : ∀ r ∈ rows5, good 5 r = true := rowsFrom_good chunks5

theorem sorted5 : rows5.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks5 0 (by decide +kernel)).1

theorem mass5 (i : Fin 56) :
    bandCount 5 (i.val : ℤ) 55 14 ≤ (rows5.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks5).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 5 (j : ℤ) 55 14 ≤ mass j chunks5)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total5 : (rows5.map (price 5)).sum = 5264 :=
  (total_eq chunks5).trans (by decide +kernel)

private def cert6_0 := witnessFinal50 6 18 0 384 384 1 99
  0x0 (by decide +kernel)
private def cert6_1 := witnessFinal50 6 17 0 10321 10321 1 99
  0x0 (by decide +kernel)
private def cert6_2 := witnessFinal50 6 16 0 20258 20320 2 198
  0x0 (by decide +kernel)
private def cert6_3 := witnessFinal50 6 15 0 30195 30320 3 293
  0x2440 (by decide +kernel)
private def cert6_4 := witnessFinal50 6 14 0 40132 40257 4 392
  0x12200 (by decide +kernel)
private def cert6_5 := witnessFinal50 6 13 0 50069 50256 5 487
  0x9112200 (by decide +kernel)
private def cert6_6 := witnessFinal50 6 12 0 60006 60256 7 677
  0x44448812200 (by decide +kernel)
private def cert6_7 := witnessFinal50 6 11 0 70005 70193 7 673
  0x4444889102440 (by decide +kernel)
private def cert6_8 := witnessFinal50 6 10 0 80004 80192 8 764
  0x2224444881220488 (by decide +kernel)
private def cert6_9 := witnessFinal50 6 9 0 90003 90192 8 752
  0x322444489111220488 (by decide +kernel)
private def cert6_10 := witnessFinal50 6 8 0 100002 100129 8 748
  0x322444888910444488 (by decide +kernel)
private def cert6_11 := witnessFinal50 6 7 0 110001 110128 7 645
  0x644c8911122444488 (by decide +kernel)
private def cert6_12 := witnessFinal50 6 6 0 120000 120128 7 633
  0x844c8911322444488 (by decide +kernel)
private def cert6_13 := witnessFinal50 6 5 0 130000 130065 5 443
  0x21132264488891 (by decide +kernel)
private def cert6_14 := witnessFinal50 6 4 0 140000 140064 4 344
  0x422844c8911 (by decide +kernel)
private def cert6_15 := witnessFinal50 6 3 0 150000 150064 3 249
  0xa4508991 (by decide +kernel)
private def cert6_16 := witnessFinal50 6 2 0 160000 160001 2 162
  0x148a11 (by decide +kernel)
private def cert6_17 := witnessFinal50 6 1 0 170000 170000 1 79
  0x291 (by decide +kernel)
private def cert6_18 := witnessFinal50 6 0 0 180000 180000 1 75
  0x311 (by decide +kernel)
private def chunks6 : List (Chunk 6) := [
  cert6_0,
  cert6_1,
  cert6_2,
  cert6_3,
  cert6_4,
  cert6_5,
  cert6_6,
  cert6_7,
  cert6_8,
  cert6_9,
  cert6_10,
  cert6_11,
  cert6_12,
  cert6_13,
  cert6_14,
  cert6_15,
  cert6_16,
  cert6_17,
  cert6_18]
def rows6 := rowsFrom chunks6

theorem good6 : ∀ r ∈ rows6, good 6 r = true := rowsFrom_good chunks6

theorem sorted6 : rows6.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks6 0 (by decide +kernel)).1

theorem mass6 (i : Fin 56) :
    bandCount 6 (i.val : ℤ) 55 14 ≤ (rows6.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks6).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 6 (j : ℤ) 55 14 ≤ mass j chunks6)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total6 : (rows6.map (price 6)).sum = 7812 :=
  (total_eq chunks6).trans (by decide +kernel)

private def cert7_0 := witnessFinal50 7 21 0 448 448 1 99
  0x0 (by decide +kernel)
private def cert7_1 := witnessFinal50 7 20 0 10385 10385 1 99
  0x0 (by decide +kernel)
private def cert7_2 := witnessFinal50 7 19 0 20322 20384 2 198
  0x0 (by decide +kernel)
private def cert7_3 := witnessFinal50 7 18 0 30259 30384 3 293
  0x2440 (by decide +kernel)
private def cert7_4 := witnessFinal50 7 17 0 40196 40321 4 392
  0x12200 (by decide +kernel)
private def cert7_5 := witnessFinal50 7 16 0 50133 50320 5 487
  0x9112200 (by decide +kernel)
private def cert7_6 := witnessFinal50 7 15 0 60070 60320 7 677
  0x44448812200 (by decide +kernel)
private def cert7_7 := witnessFinal50 7 14 0 70007 70257 8 772
  0x22224448812200 (by decide +kernel)
private def cert7_8 := witnessFinal50 7 13 0 80006 80256 9 863
  0x11122224409102440 (by decide +kernel)
private def cert7_9 := witnessFinal50 7 12 0 90005 90256 10 946
  0xc89111224444881220488 (by decide +kernel)
private def cert7_10 := witnessFinal50 7 11 0 100004 100193 10 942
  0xc89112222441111220488 (by decide +kernel)
private def cert7_11 := witnessFinal50 7 10 0 110003 110192 10 930
  0xc8991222244888910444488 (by decide +kernel)
private def cert7_12 := witnessFinal50 7 9 0 120002 120192 10 918
  0x108991222644888910444488 (by decide +kernel)
private def cert7_13 := witnessFinal50 7 8 0 130001 130129 9 815
  0x21132264488891322444488 (by decide +kernel)
private def cert7_14 := witnessFinal50 7 7 0 140000 140128 8 716
  0x422844c8911322444488 (by decide +kernel)
private def cert7_15 := witnessFinal50 7 6 0 150000 150128 7 605
  0xa450899142264488891 (by decide +kernel)
private def cert7_16 := witnessFinal50 7 5 0 160000 160065 5 423
  0x291422844c8911 (by decide +kernel)
private def cert7_17 := witnessFinal50 7 4 0 170000 170064 4 328
  0x522a4508991 (by decide +kernel)
private def cert7_18 := witnessFinal50 7 3 0 180000 180064 3 237
  0xc4548a11 (by decide +kernel)
private def cert7_19 := witnessFinal50 7 2 0 190000 190001 2 154
  0x188a91 (by decide +kernel)
private def cert7_20 := witnessFinal50 7 1 0 200000 200000 1 75
  0x311 (by decide +kernel)
private def cert7_21 := witnessFinal50 7 0 0 210000 210000 1 71
  0x391 (by decide +kernel)
private def chunks7 : List (Chunk 7) := [
  cert7_0,
  cert7_1,
  cert7_2,
  cert7_3,
  cert7_4,
  cert7_5,
  cert7_6,
  cert7_7,
  cert7_8,
  cert7_9,
  cert7_10,
  cert7_11,
  cert7_12,
  cert7_13,
  cert7_14,
  cert7_15,
  cert7_16,
  cert7_17,
  cert7_18,
  cert7_19,
  cert7_20,
  cert7_21]
def rows7 := rowsFrom chunks7

theorem good7 : ∀ r ∈ rows7, good 7 r = true := rowsFrom_good chunks7

theorem sorted7 : rows7.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks7 0 (by decide +kernel)).1

theorem mass7 (i : Fin 56) :
    bandCount 7 (i.val : ℤ) 55 14 ≤ (rows7.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks7).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 7 (j : ℤ) 55 14 ≤ mass j chunks7)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total7 : (rows7.map (price 7)).sum = 11040 :=
  (total_eq chunks7).trans (by decide +kernel)

private def cert8_0 := witnessFinal50 8 24 0 512 512 1 99
  0x0 (by decide +kernel)
private def cert8_1 := witnessFinal50 8 23 0 10449 10449 1 99
  0x0 (by decide +kernel)
private def cert8_2 := witnessFinal50 8 22 0 20386 20448 2 198
  0x0 (by decide +kernel)
private def cert8_3 := witnessFinal50 8 21 0 30323 30448 3 293
  0x2440 (by decide +kernel)
private def cert8_4 := witnessFinal50 8 20 0 40260 40385 4 392
  0x12200 (by decide +kernel)
private def cert8_5 := witnessFinal50 8 19 0 50197 50384 5 487
  0x9112200 (by decide +kernel)
private def cert8_6 := witnessFinal50 8 18 0 60134 60384 7 677
  0x44448812200 (by decide +kernel)
private def cert8_7 := witnessFinal50 8 17 0 70071 70321 8 772
  0x22224448812200 (by decide +kernel)
private def cert8_8 := witnessFinal50 8 16 0 80008 80320 10 962
  0x88911122048812200 (by decide +kernel)
private def cert8_9 := witnessFinal50 8 15 0 90007 90320 11 1045
  0x6448889122224409102440 (by decide +kernel)
private def cert8_10 := witnessFinal50 8 14 0 100006 100257 12 1136
  0x3224448889104444881220488 (by decide +kernel)
private def cert8_11 := witnessFinal50 8 13 0 110005 110256 12 1124
  0x322644888912222441111220488 (by decide +kernel)
private def cert8_12 := witnessFinal50 8 12 0 120004 120256 13 1203
  0x211322444c89111220888910444488 (by decide +kernel)
private def cert8_13 := witnessFinal50 8 11 0 130003 130193 12 1100
  0x422644c8911122644888910444488 (by decide +kernel)
private def cert8_14 := witnessFinal50 8 10 0 140002 140192 12 1088
  0x422844c8911322444488322444488 (by decide +kernel)
private def cert8_15 := witnessFinal50 8 9 0 150001 150192 11 977
  0xa450899142264488891322444488 (by decide +kernel)
private def cert8_16 := witnessFinal50 8 8 0 160000 160129 10 878
  0x148a1142264488a11322444488 (by decide +kernel)
private def cert8_17 := witnessFinal50 8 7 0 170000 170128 8 684
  0x522a450899142264488891 (by decide +kernel)
private def cert8_18 := witnessFinal50 8 6 0 180000 180128 7 577
  0xc4548a11522844c8911 (by decide +kernel)
private def cert8_19 := witnessFinal50 8 5 0 190000 190065 5 403
  0x311522a4508991 (by decide +kernel)
private def cert8_20 := witnessFinal50 8 4 0 200000 200064 4 312
  0x622c4548a11 (by decide +kernel)
private def cert8_21 := witnessFinal50 8 3 0 210000 210064 3 225
  0xe4588a91 (by decide +kernel)
private def cert8_22 := witnessFinal50 8 2 0 220000 220001 2 146
  0x1c8b11 (by decide +kernel)
private def cert8_23 := witnessFinal50 8 1 0 230000 230000 1 71
  0x391 (by decide +kernel)
private def cert8_24 := witnessFinal50 8 0 0 240000 240000 1 67
  0x411 (by decide +kernel)
private def chunks8 : List (Chunk 8) := [
  cert8_0,
  cert8_1,
  cert8_2,
  cert8_3,
  cert8_4,
  cert8_5,
  cert8_6,
  cert8_7,
  cert8_8,
  cert8_9,
  cert8_10,
  cert8_11,
  cert8_12,
  cert8_13,
  cert8_14,
  cert8_15,
  cert8_16,
  cert8_17,
  cert8_18,
  cert8_19,
  cert8_20,
  cert8_21,
  cert8_22,
  cert8_23,
  cert8_24]
def rows8 := rowsFrom chunks8

theorem good8 : ∀ r ∈ rows8, good 8 r = true := rowsFrom_good chunks8

theorem sorted8 : rows8.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks8 0 (by decide +kernel)).1

theorem mass8 (i : Fin 56) :
    bandCount 8 (i.val : ℤ) 55 14 ≤ (rows8.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks8).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 8 (j : ℤ) 55 14 ≤ mass j chunks8)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total8 : (rows8.map (price 8)).sum = 15015 :=
  (total_eq chunks8).trans (by decide +kernel)

private def cert9_0 := witnessFinal50 9 27 0 576 576 1 99
  0x0 (by decide +kernel)
private def cert9_1 := witnessFinal50 9 26 0 10513 10513 1 99
  0x0 (by decide +kernel)
private def cert9_2 := witnessFinal50 9 25 0 20450 20512 2 198
  0x0 (by decide +kernel)
private def cert9_3 := witnessFinal50 9 24 0 30387 30512 3 293
  0x2440 (by decide +kernel)
private def cert9_4 := witnessFinal50 9 23 0 40324 40449 4 392
  0x12200 (by decide +kernel)
private def cert9_5 := witnessFinal50 9 22 0 50261 50448 5 487
  0x9112200 (by decide +kernel)
private def cert9_6 := witnessFinal50 9 21 0 60198 60448 7 677
  0x44448812200 (by decide +kernel)
private def cert9_7 := witnessFinal50 9 20 0 70135 70385 8 772
  0x22224448812200 (by decide +kernel)
private def cert9_8 := witnessFinal50 9 19 0 80072 80384 10 962
  0x88911122048812200 (by decide +kernel)
private def cert9_9 := witnessFinal50 9 18 0 90009 90384 12 1144
  0x32244448911122048812200 (by decide +kernel)
private def cert9_10 := witnessFinal50 9 17 0 100008 100321 13 1235
  0x19122244448822224409102440 (by decide +kernel)
private def cert9_11 := witnessFinal50 9 16 0 110007 110320 14 1318
  0xc89912222448889104444881220488 (by decide +kernel)
private def cert9_12 := witnessFinal50 9 15 0 120006 120320 15 1397
  0x844c89113224444882222441111220488 (by decide +kernel)
private def cert9_13 := witnessFinal50 9 14 0 130005 130257 15 1385
  0x844c8991222244c89111220888910444488 (by decide +kernel)
private def cert9_14 := witnessFinal50 9 13 0 140004 140256 15 1373
  0x84508991222644888910644888910444488 (by decide +kernel)
private def cert9_15 := witnessFinal50 9 12 0 150003 150256 15 1349
  0xa450899142264488891322444488322444488 (by decide +kernel)
private def cert9_16 := witnessFinal50 9 11 0 160002 160193 14 1250
  0x148a1142264488a11322444488322444488 (by decide +kernel)
private def cert9_17 := witnessFinal50 9 10 0 170001 170192 13 1139
  0x291522844c8a1132244448a11322444488 (by decide +kernel)
private def cert9_18 := witnessFinal50 9 9 0 180000 180192 12 1032
  0x622a4508a9142264488a11322444488 (by decide +kernel)
private def cert9_19 := witnessFinal50 9 8 0 190000 190129 10 838
  0x188a91522844c8a9142264488891 (by decide +kernel)
private def cert9_20 := witnessFinal50 9 7 0 200000 200128 8 652
  0x622c4548a11522844c8911 (by decide +kernel)
private def cert9_21 := witnessFinal50 9 6 0 210000 210128 7 549
  0xe4588a91622a4508991 (by decide +kernel)
private def cert9_22 := witnessFinal50 9 5 0 220000 220065 5 383
  0x391622c4548a11 (by decide +kernel)
private def cert9_23 := witnessFinal50 9 4 0 230000 230064 4 296
  0x722e4588a91 (by decide +kernel)
private def cert9_24 := witnessFinal50 9 3 0 240000 240064 3 213
  0x1045c8b11 (by decide +kernel)
private def cert9_25 := witnessFinal50 9 2 0 250000 250001 2 138
  0x208b91 (by decide +kernel)
private def cert9_26 := witnessFinal50 9 1 0 260000 260000 1 67
  0x411 (by decide +kernel)
private def cert9_27 := witnessFinal50 9 0 0 270000 270000 1 63
  0x491 (by decide +kernel)
private def chunks9 : List (Chunk 9) := [
  cert9_0,
  cert9_1,
  cert9_2,
  cert9_3,
  cert9_4,
  cert9_5,
  cert9_6,
  cert9_7,
  cert9_8,
  cert9_9,
  cert9_10,
  cert9_11,
  cert9_12,
  cert9_13,
  cert9_14,
  cert9_15,
  cert9_16,
  cert9_17,
  cert9_18,
  cert9_19,
  cert9_20,
  cert9_21,
  cert9_22,
  cert9_23,
  cert9_24,
  cert9_25,
  cert9_26,
  cert9_27]
def rows9 := rowsFrom chunks9

theorem good9 : ∀ r ∈ rows9, good 9 r = true := rowsFrom_good chunks9

theorem sorted9 : rows9.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks9 0 (by decide +kernel)).1

theorem mass9 (i : Fin 56) :
    bandCount 9 (i.val : ℤ) 55 14 ≤ (rows9.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom chunks9).filter _).length
  rw [mass_eq]
  have h : (List.range 56).all
      (fun j => decide (bandCount 9 (j : ℤ) 55 14 ≤ mass j chunks9)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total9 : (rows9.map (price 9)).sum = 19800 :=
  (total_eq chunks9).trans (by decide +kernel)

end Final50RankReceipt

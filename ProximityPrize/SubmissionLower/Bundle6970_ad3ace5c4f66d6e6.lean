import ProximityPrize.SubmissionLower.E6970ReceiptBase

section Pack_E6970Receipt0

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt0_chunk0 := witnessRule 0 0 0 0 0 1 107
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt0_chunks : List (Chunk 0) := [pack_E6970Receipt0_chunk0]
def rows0 := rowsFrom pack_E6970Receipt0_chunks
theorem good0 : ∀ r ∈ rows0, good 0 r = true := rowsFrom_good pack_E6970Receipt0_chunks
theorem sorted0 : rows0.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt0_chunks 0 (by decide +kernel)).1
theorem mass0 (i : Fin 61) :
    bandCount 0 (i.val : ℤ) 60 16 ≤ (rows0.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt0_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 0 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt0_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total0 : (rows0.map (price 0)).sum = 107 :=
  (total_eq pack_E6970Receipt0_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt0

section Pack_E6970Receipt1

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt1_chunk0 := witnessRule 1 3 0 64 64 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt1_chunk1 := witnessRule 1 2 0 10001 10001 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt1_chunk2 := witnessRule 1 1 0 20000 20000 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt1_chunk3 := witnessRule 1 0 0 30000 30000 1 103
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt1_chunks : List (Chunk 1) := [pack_E6970Receipt1_chunk0, pack_E6970Receipt1_chunk1, pack_E6970Receipt1_chunk2, pack_E6970Receipt1_chunk3]
def rows1 := rowsFrom pack_E6970Receipt1_chunks
theorem good1 : ∀ r ∈ rows1, good 1 r = true := rowsFrom_good pack_E6970Receipt1_chunks
theorem sorted1 : rows1.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt1_chunks 0 (by decide +kernel)).1
theorem mass1 (i : Fin 61) :
    bandCount 1 (i.val : ℤ) 60 16 ≤ (rows1.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt1_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 1 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt1_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total1 : (rows1.map (price 1)).sum = 424 :=
  (total_eq pack_E6970Receipt1_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt1

section Pack_E6970Receipt10

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt10_chunk0 := witnessRule 10 30 0 640 640 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk1 := witnessRule 10 29 0 10577 10577 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk2 := witnessRule 10 28 0 20514 20576 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk3 := witnessRule 10 27 0 30451 30576 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk4 := witnessRule 10 26 0 40388 40513 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk5 := witnessRule 10 25 0 50325 50512 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk6 := witnessRule 10 24 0 60262 60512 7 733
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk7 := witnessRule 10 23 0 70199 70449 8 836
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk8 := witnessRule 10 22 0 80136 80448 10 1042
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk9 := witnessRule 10 21 0 90073 90448 12 1240
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk10 := witnessRule 10 20 0 100010 100385 14 1446
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk11 := witnessRule 10 19 0 110009 110384 15 1537
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk12 := witnessRule 10 18 0 120008 120384 17 1727
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk13 := witnessRule 10 17 0 130007 130321 17 1715
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk14 := witnessRule 10 16 0 140006 140320 18 1802
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk15 := witnessRule 10 15 0 150005 150320 18 1778
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk16 := witnessRule 10 14 0 160004 160257 18 1766
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk17 := witnessRule 10 13 0 170003 170256 17 1647
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk18 := witnessRule 10 12 0 180002 180256 17 1623
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk19 := witnessRule 10 11 0 190001 190193 15 1413
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk20 := witnessRule 10 10 0 200000 200192 14 1298
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk21 := witnessRule 10 9 0 210000 210192 12 1080
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk22 := witnessRule 10 8 0 220000 220129 10 878
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk23 := witnessRule 10 7 0 230000 230128 8 684
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk24 := witnessRule 10 6 0 240000 240128 7 577
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk25 := witnessRule 10 5 0 250000 250065 5 403
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk26 := witnessRule 10 4 0 260000 260064 4 312
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk27 := witnessRule 10 3 0 270000 270064 3 225
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk28 := witnessRule 10 2 0 280000 280001 2 146
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk29 := witnessRule 10 1 0 290000 290000 1 71
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt10_chunk30 := witnessRule 10 0 0 300000 300000 1 67
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt10_chunks : List (Chunk 10) := [pack_E6970Receipt10_chunk0, pack_E6970Receipt10_chunk1, pack_E6970Receipt10_chunk2, pack_E6970Receipt10_chunk3, pack_E6970Receipt10_chunk4, pack_E6970Receipt10_chunk5, pack_E6970Receipt10_chunk6, pack_E6970Receipt10_chunk7, pack_E6970Receipt10_chunk8, pack_E6970Receipt10_chunk9, pack_E6970Receipt10_chunk10, pack_E6970Receipt10_chunk11, pack_E6970Receipt10_chunk12, pack_E6970Receipt10_chunk13, pack_E6970Receipt10_chunk14, pack_E6970Receipt10_chunk15, pack_E6970Receipt10_chunk16, pack_E6970Receipt10_chunk17, pack_E6970Receipt10_chunk18, pack_E6970Receipt10_chunk19, pack_E6970Receipt10_chunk20, pack_E6970Receipt10_chunk21, pack_E6970Receipt10_chunk22, pack_E6970Receipt10_chunk23, pack_E6970Receipt10_chunk24, pack_E6970Receipt10_chunk25, pack_E6970Receipt10_chunk26, pack_E6970Receipt10_chunk27, pack_E6970Receipt10_chunk28, pack_E6970Receipt10_chunk29, pack_E6970Receipt10_chunk30]
def rows10 := rowsFrom pack_E6970Receipt10_chunks
theorem good10 : ∀ r ∈ rows10, good 10 r = true := rowsFrom_good pack_E6970Receipt10_chunks
theorem sorted10 : rows10.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt10_chunks 0 (by decide +kernel)).1
theorem mass10 (i : Fin 61) :
    bandCount 10 (i.val : ℤ) 60 16 ≤ (rows10.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt10_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 10 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt10_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total10 : (rows10.map (price 10)).sum = 27742 :=
  (total_eq pack_E6970Receipt10_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt10

section Pack_E6970Receipt11

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt11_chunk0 := witnessRule 11 33 0 704 704 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk1 := witnessRule 11 32 0 10641 10641 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk2 := witnessRule 11 31 0 20578 20640 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk3 := witnessRule 11 30 0 30515 30640 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk4 := witnessRule 11 29 0 40452 40577 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk5 := witnessRule 11 28 0 50389 50576 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk6 := witnessRule 11 27 0 60326 60576 7 733
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk7 := witnessRule 11 26 0 70263 70513 8 836
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk8 := witnessRule 11 25 0 80200 80512 10 1042
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk9 := witnessRule 11 24 0 90137 90512 12 1240
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk10 := witnessRule 11 23 0 100074 100449 14 1446
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk11 := witnessRule 11 22 0 110011 110448 16 1644
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk12 := witnessRule 11 21 0 120010 120448 18 1834
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk13 := witnessRule 11 20 0 130009 130385 19 1925
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk14 := witnessRule 11 19 0 140008 140384 20 2012
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk15 := witnessRule 11 18 0 150007 150384 21 2087
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk16 := witnessRule 11 17 0 160006 160321 21 2075
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk17 := witnessRule 11 16 0 170005 170320 21 2051
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk18 := witnessRule 11 15 0 180004 180320 21 2027
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk19 := witnessRule 11 14 0 190003 190257 20 1908
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk20 := witnessRule 11 13 0 200002 200256 19 1793
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk21 := witnessRule 11 12 0 210001 210256 18 1662
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk22 := witnessRule 11 11 0 220000 220193 16 1460
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk23 := witnessRule 11 10 0 230000 230192 14 1242
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk24 := witnessRule 11 9 0 240000 240192 12 1032
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk25 := witnessRule 11 8 0 250000 250129 10 838
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk26 := witnessRule 11 7 0 260000 260128 8 652
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk27 := witnessRule 11 6 0 270000 270128 7 549
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk28 := witnessRule 11 5 0 280000 280065 5 383
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk29 := witnessRule 11 4 0 290000 290064 4 296
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk30 := witnessRule 11 3 0 300000 300064 3 213
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk31 := witnessRule 11 2 0 310000 310001 2 138
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk32 := witnessRule 11 1 0 320000 320000 1 67
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt11_chunk33 := witnessRule 11 0 0 330000 330000 1 63
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt11_chunks : List (Chunk 11) := [pack_E6970Receipt11_chunk0, pack_E6970Receipt11_chunk1, pack_E6970Receipt11_chunk2, pack_E6970Receipt11_chunk3, pack_E6970Receipt11_chunk4, pack_E6970Receipt11_chunk5, pack_E6970Receipt11_chunk6, pack_E6970Receipt11_chunk7, pack_E6970Receipt11_chunk8, pack_E6970Receipt11_chunk9, pack_E6970Receipt11_chunk10, pack_E6970Receipt11_chunk11, pack_E6970Receipt11_chunk12, pack_E6970Receipt11_chunk13, pack_E6970Receipt11_chunk14, pack_E6970Receipt11_chunk15, pack_E6970Receipt11_chunk16, pack_E6970Receipt11_chunk17, pack_E6970Receipt11_chunk18, pack_E6970Receipt11_chunk19, pack_E6970Receipt11_chunk20, pack_E6970Receipt11_chunk21, pack_E6970Receipt11_chunk22, pack_E6970Receipt11_chunk23, pack_E6970Receipt11_chunk24, pack_E6970Receipt11_chunk25, pack_E6970Receipt11_chunk26, pack_E6970Receipt11_chunk27, pack_E6970Receipt11_chunk28, pack_E6970Receipt11_chunk29, pack_E6970Receipt11_chunk30, pack_E6970Receipt11_chunk31, pack_E6970Receipt11_chunk32, pack_E6970Receipt11_chunk33]
def rows11 := rowsFrom pack_E6970Receipt11_chunks
theorem good11 : ∀ r ∈ rows11, good 11 r = true := rowsFrom_good pack_E6970Receipt11_chunks
theorem sorted11 : rows11.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt11_chunks 0 (by decide +kernel)).1
theorem mass11 (i : Fin 61) :
    bandCount 11 (i.val : ℤ) 60 16 ≤ (rows11.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt11_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 11 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt11_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total11 : (rows11.map (price 11)).sum = 34944 :=
  (total_eq pack_E6970Receipt11_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt11

section Pack_E6970Receipt12

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt12_chunk0 := witnessRule 12 36 0 768 768 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk1 := witnessRule 12 35 0 10705 10705 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk2 := witnessRule 12 34 0 20642 20704 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk3 := witnessRule 12 33 0 30579 30704 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk4 := witnessRule 12 32 0 40516 40641 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk5 := witnessRule 12 31 0 50453 50640 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk6 := witnessRule 12 30 0 60390 60640 7 733
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk7 := witnessRule 12 29 0 70327 70577 8 836
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk8 := witnessRule 12 28 0 80264 80576 10 1042
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk9 := witnessRule 12 27 0 90201 90576 12 1240
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk10 := witnessRule 12 26 0 100138 100513 14 1446
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk11 := witnessRule 12 25 0 110075 110512 16 1644
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk12 := witnessRule 12 24 0 120012 120512 19 1941
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk13 := witnessRule 12 23 0 130011 130449 20 2032
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk14 := witnessRule 12 22 0 140010 140448 22 2222
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk15 := witnessRule 12 21 0 150009 150448 23 2297
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk16 := witnessRule 12 20 0 160008 160385 24 2384
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk17 := witnessRule 12 19 0 170007 170384 24 2360
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk18 := witnessRule 12 18 0 180006 180384 25 2431
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk19 := witnessRule 12 17 0 190005 190321 24 2312
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk20 := witnessRule 12 16 0 200004 200320 24 2288
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk21 := witnessRule 12 15 0 210003 210320 23 2157
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk22 := witnessRule 12 14 0 220002 220257 22 2042
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk23 := witnessRule 12 13 0 230001 230256 20 1824
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk24 := witnessRule 12 12 0 240000 240256 19 1697
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk25 := witnessRule 12 11 0 250000 250193 16 1396
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk26 := witnessRule 12 10 0 260000 260192 14 1186
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk27 := witnessRule 12 9 0 270000 270192 12 984
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk28 := witnessRule 12 8 0 280000 280129 10 798
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk29 := witnessRule 12 7 0 290000 290128 8 620
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk30 := witnessRule 12 6 0 300000 300128 7 521
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk31 := witnessRule 12 5 0 310000 310065 5 363
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk32 := witnessRule 12 4 0 320000 320064 4 280
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk33 := witnessRule 12 3 0 330000 330064 3 201
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk34 := witnessRule 12 2 0 340000 340001 2 130
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk35 := witnessRule 12 1 0 350000 350000 1 63
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt12_chunk36 := witnessRule 12 0 0 360000 360000 1 59
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt12_chunks : List (Chunk 12) := [pack_E6970Receipt12_chunk0, pack_E6970Receipt12_chunk1, pack_E6970Receipt12_chunk2, pack_E6970Receipt12_chunk3, pack_E6970Receipt12_chunk4, pack_E6970Receipt12_chunk5, pack_E6970Receipt12_chunk6, pack_E6970Receipt12_chunk7, pack_E6970Receipt12_chunk8, pack_E6970Receipt12_chunk9, pack_E6970Receipt12_chunk10, pack_E6970Receipt12_chunk11, pack_E6970Receipt12_chunk12, pack_E6970Receipt12_chunk13, pack_E6970Receipt12_chunk14, pack_E6970Receipt12_chunk15, pack_E6970Receipt12_chunk16, pack_E6970Receipt12_chunk17, pack_E6970Receipt12_chunk18, pack_E6970Receipt12_chunk19, pack_E6970Receipt12_chunk20, pack_E6970Receipt12_chunk21, pack_E6970Receipt12_chunk22, pack_E6970Receipt12_chunk23, pack_E6970Receipt12_chunk24, pack_E6970Receipt12_chunk25, pack_E6970Receipt12_chunk26, pack_E6970Receipt12_chunk27, pack_E6970Receipt12_chunk28, pack_E6970Receipt12_chunk29, pack_E6970Receipt12_chunk30, pack_E6970Receipt12_chunk31, pack_E6970Receipt12_chunk32, pack_E6970Receipt12_chunk33, pack_E6970Receipt12_chunk34, pack_E6970Receipt12_chunk35, pack_E6970Receipt12_chunk36]
def rows12 := rowsFrom pack_E6970Receipt12_chunks
theorem good12 : ∀ r ∈ rows12, good 12 r = true := rowsFrom_good pack_E6970Receipt12_chunks
theorem sorted12 : rows12.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt12_chunks 0 (by decide +kernel)).1
theorem mass12 (i : Fin 61) :
    bandCount 12 (i.val : ℤ) 60 16 ≤ (rows12.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt12_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 12 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt12_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total12 : (rows12.map (price 12)).sum = 43225 :=
  (total_eq pack_E6970Receipt12_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt12

section Pack_E6970Receipt13

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt13_chunk0 := witnessRule 13 39 0 832 832 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk1 := witnessRule 13 38 0 10769 10769 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk2 := witnessRule 13 37 0 20706 20768 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk3 := witnessRule 13 36 0 30643 30768 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk4 := witnessRule 13 35 0 40580 40705 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk5 := witnessRule 13 34 0 50517 50704 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk6 := witnessRule 13 33 0 60454 60704 7 733
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk7 := witnessRule 13 32 0 70391 70641 8 836
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk8 := witnessRule 13 31 0 80328 80640 10 1042
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk9 := witnessRule 13 30 0 90265 90640 12 1240
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk10 := witnessRule 13 29 0 100202 100577 14 1446
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk11 := witnessRule 13 28 0 110139 110576 16 1644
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk12 := witnessRule 13 27 0 120076 120576 19 1941
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk13 := witnessRule 13 26 0 130013 130513 21 2139
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk14 := witnessRule 13 25 0 140012 140512 23 2329
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk15 := witnessRule 13 24 0 150011 150512 25 2507
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk16 := witnessRule 13 23 0 160010 160449 26 2594
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk17 := witnessRule 13 22 0 170009 170448 27 2669
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk18 := witnessRule 13 21 0 180008 180448 28 2740
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk19 := witnessRule 13 20 0 190007 190385 28 2716
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk20 := witnessRule 13 19 0 200006 200384 28 2692
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk21 := witnessRule 13 18 0 210005 210384 28 2652
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk22 := witnessRule 13 17 0 220004 220321 27 2537
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk23 := witnessRule 13 16 0 230003 230320 26 2406
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk24 := witnessRule 13 15 0 240002 240320 25 2279
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk25 := witnessRule 13 14 0 250001 250257 23 2061
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk26 := witnessRule 13 13 0 260000 260256 21 1851
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk27 := witnessRule 13 12 0 270000 270256 19 1621
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk28 := witnessRule 13 11 0 280000 280193 16 1332
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk29 := witnessRule 13 10 0 290000 290192 14 1130
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk30 := witnessRule 13 9 0 300000 300192 12 936
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk31 := witnessRule 13 8 0 310000 310129 10 758
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk32 := witnessRule 13 7 0 320000 320128 8 588
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk33 := witnessRule 13 6 0 330000 330128 7 493
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk34 := witnessRule 13 5 0 340000 340065 5 343
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk35 := witnessRule 13 4 0 350000 350064 4 264
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk36 := witnessRule 13 3 0 360000 360064 3 189
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk37 := witnessRule 13 2 0 370000 370001 2 122
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk38 := witnessRule 13 1 0 380000 380000 1 59
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt13_chunk39 := witnessRule 13 0 0 390000 390000 1 55
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt13_chunks : List (Chunk 13) := [pack_E6970Receipt13_chunk0, pack_E6970Receipt13_chunk1, pack_E6970Receipt13_chunk2, pack_E6970Receipt13_chunk3, pack_E6970Receipt13_chunk4, pack_E6970Receipt13_chunk5, pack_E6970Receipt13_chunk6, pack_E6970Receipt13_chunk7, pack_E6970Receipt13_chunk8, pack_E6970Receipt13_chunk9, pack_E6970Receipt13_chunk10, pack_E6970Receipt13_chunk11, pack_E6970Receipt13_chunk12, pack_E6970Receipt13_chunk13, pack_E6970Receipt13_chunk14, pack_E6970Receipt13_chunk15, pack_E6970Receipt13_chunk16, pack_E6970Receipt13_chunk17, pack_E6970Receipt13_chunk18, pack_E6970Receipt13_chunk19, pack_E6970Receipt13_chunk20, pack_E6970Receipt13_chunk21, pack_E6970Receipt13_chunk22, pack_E6970Receipt13_chunk23, pack_E6970Receipt13_chunk24, pack_E6970Receipt13_chunk25, pack_E6970Receipt13_chunk26, pack_E6970Receipt13_chunk27, pack_E6970Receipt13_chunk28, pack_E6970Receipt13_chunk29, pack_E6970Receipt13_chunk30, pack_E6970Receipt13_chunk31, pack_E6970Receipt13_chunk32, pack_E6970Receipt13_chunk33, pack_E6970Receipt13_chunk34, pack_E6970Receipt13_chunk35, pack_E6970Receipt13_chunk36, pack_E6970Receipt13_chunk37, pack_E6970Receipt13_chunk38, pack_E6970Receipt13_chunk39]
def rows13 := rowsFrom pack_E6970Receipt13_chunks
theorem good13 : ∀ r ∈ rows13, good 13 r = true := rowsFrom_good pack_E6970Receipt13_chunks
theorem sorted13 : rows13.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt13_chunks 0 (by decide +kernel)).1
theorem mass13 (i : Fin 61) :
    bandCount 13 (i.val : ℤ) 60 16 ≤ (rows13.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt13_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 13 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt13_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total13 : (rows13.map (price 13)).sum = 52640 :=
  (total_eq pack_E6970Receipt13_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt13

section Pack_E6970Receipt14

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt14_chunk0 := witnessRule 14 42 0 896 896 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk1 := witnessRule 14 41 0 10833 10833 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk2 := witnessRule 14 40 0 20770 20832 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk3 := witnessRule 14 39 0 30707 30832 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk4 := witnessRule 14 38 0 40644 40769 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk5 := witnessRule 14 37 0 50581 50768 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk6 := witnessRule 14 36 0 60518 60768 7 733
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk7 := witnessRule 14 35 0 70455 70705 8 836
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk8 := witnessRule 14 34 0 80392 80704 10 1042
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk9 := witnessRule 14 33 0 90329 90704 12 1240
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk10 := witnessRule 14 32 0 100266 100641 14 1446
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk11 := witnessRule 14 31 0 110203 110640 16 1644
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk12 := witnessRule 14 30 0 120140 120640 19 1941
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk13 := witnessRule 14 29 0 130077 130577 21 2139
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk14 := witnessRule 14 28 0 140014 140576 24 2436
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk15 := witnessRule 14 27 0 150013 150576 26 2614
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk16 := witnessRule 14 26 0 160012 160513 28 2804
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk17 := witnessRule 14 25 0 170011 170512 29 2879
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk18 := witnessRule 14 24 0 180010 180512 31 3049
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk19 := witnessRule 14 23 0 190009 190449 31 3025
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk20 := witnessRule 14 22 0 200008 200448 32 3096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk21 := witnessRule 14 21 0 210007 210448 32 3056
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk22 := witnessRule 14 20 0 220006 220385 32 3032
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk23 := witnessRule 14 19 0 230005 230384 31 2901
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk24 := witnessRule 14 18 0 240004 240384 31 2861
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk25 := witnessRule 14 17 0 250003 250321 29 2643
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk26 := witnessRule 14 16 0 260002 260320 28 2516
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk27 := witnessRule 14 15 0 270001 270320 26 2286
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk28 := witnessRule 14 14 0 280000 280257 24 2076
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk29 := witnessRule 14 13 0 290000 290256 21 1767
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk30 := witnessRule 14 12 0 300000 300256 19 1545
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk31 := witnessRule 14 11 0 310000 310193 16 1268
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk32 := witnessRule 14 10 0 320000 320192 14 1074
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk33 := witnessRule 14 9 0 330000 330192 12 888
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk34 := witnessRule 14 8 0 340000 340129 10 718
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk35 := witnessRule 14 7 0 350000 350128 8 556
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk36 := witnessRule 14 6 0 360000 360128 7 465
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk37 := witnessRule 14 5 0 370000 370065 5 323
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk38 := witnessRule 14 4 0 380000 380064 4 248
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk39 := witnessRule 14 3 0 390000 390064 3 177
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk40 := witnessRule 14 2 0 400000 400001 2 114
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk41 := witnessRule 14 1 0 410000 410000 1 55
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt14_chunk42 := witnessRule 14 0 0 420000 420000 1 51
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt14_chunks : List (Chunk 14) := [pack_E6970Receipt14_chunk0, pack_E6970Receipt14_chunk1, pack_E6970Receipt14_chunk2, pack_E6970Receipt14_chunk3, pack_E6970Receipt14_chunk4, pack_E6970Receipt14_chunk5, pack_E6970Receipt14_chunk6, pack_E6970Receipt14_chunk7, pack_E6970Receipt14_chunk8, pack_E6970Receipt14_chunk9, pack_E6970Receipt14_chunk10, pack_E6970Receipt14_chunk11, pack_E6970Receipt14_chunk12, pack_E6970Receipt14_chunk13, pack_E6970Receipt14_chunk14, pack_E6970Receipt14_chunk15, pack_E6970Receipt14_chunk16, pack_E6970Receipt14_chunk17, pack_E6970Receipt14_chunk18, pack_E6970Receipt14_chunk19, pack_E6970Receipt14_chunk20, pack_E6970Receipt14_chunk21, pack_E6970Receipt14_chunk22, pack_E6970Receipt14_chunk23, pack_E6970Receipt14_chunk24, pack_E6970Receipt14_chunk25, pack_E6970Receipt14_chunk26, pack_E6970Receipt14_chunk27, pack_E6970Receipt14_chunk28, pack_E6970Receipt14_chunk29, pack_E6970Receipt14_chunk30, pack_E6970Receipt14_chunk31, pack_E6970Receipt14_chunk32, pack_E6970Receipt14_chunk33, pack_E6970Receipt14_chunk34, pack_E6970Receipt14_chunk35, pack_E6970Receipt14_chunk36, pack_E6970Receipt14_chunk37, pack_E6970Receipt14_chunk38, pack_E6970Receipt14_chunk39, pack_E6970Receipt14_chunk40, pack_E6970Receipt14_chunk41, pack_E6970Receipt14_chunk42]
def rows14 := rowsFrom pack_E6970Receipt14_chunks
theorem good14 : ∀ r ∈ rows14, good 14 r = true := rowsFrom_good pack_E6970Receipt14_chunks
theorem sorted14 : rows14.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt14_chunks 0 (by decide +kernel)).1
theorem mass14 (i : Fin 61) :
    bandCount 14 (i.val : ℤ) 60 16 ≤ (rows14.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt14_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 14 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt14_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total14 : (rows14.map (price 14)).sum = 63240 :=
  (total_eq pack_E6970Receipt14_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt14

section Pack_E6970Receipt15

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt15_chunk0 := witnessRule 15 45 0 960 960 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk1 := witnessRule 15 44 0 10897 10897 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk2 := witnessRule 15 43 0 20834 20896 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk3 := witnessRule 15 42 0 30771 30896 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk4 := witnessRule 15 41 0 40708 40833 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk5 := witnessRule 15 40 0 50645 50832 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk6 := witnessRule 15 39 0 60582 60832 7 733
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk7 := witnessRule 15 38 0 70519 70769 8 836
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk8 := witnessRule 15 37 0 80456 80768 10 1042
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk9 := witnessRule 15 36 0 90393 90768 12 1240
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk10 := witnessRule 15 35 0 100330 100705 14 1446
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk11 := witnessRule 15 34 0 110267 110704 16 1644
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk12 := witnessRule 15 33 0 120204 120704 19 1941
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk13 := witnessRule 15 32 0 130141 130641 21 2139
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk14 := witnessRule 15 31 0 140078 140640 24 2436
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk15 := witnessRule 15 30 0 150015 150640 27 2721
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk16 := witnessRule 15 29 0 160014 160577 29 2911
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk17 := witnessRule 15 28 0 170013 170576 31 3089
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk18 := witnessRule 15 27 0 180012 180513 32 3176
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk19 := witnessRule 15 27 32 180576 180576 1 83
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk20 := witnessRule 15 26 0 190011 190450 32 3164
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk21 := witnessRule 15 26 32 190512 190513 2 170
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk22 := witnessRule 15 25 0 200010 200448 32 3152
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk23 := witnessRule 15 25 32 200449 200512 3 253
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk24 := witnessRule 15 24 0 210009 210386 32 3128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk25 := witnessRule 15 24 32 210387 210512 4 332
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk26 := witnessRule 15 23 0 220008 220384 32 3104
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk27 := witnessRule 15 23 32 220385 220449 4 332
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk28 := witnessRule 15 22 0 230007 230323 32 3068
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk29 := witnessRule 15 22 32 230384 230448 4 328
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk30 := witnessRule 15 21 0 240006 240322 32 3040
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk31 := witnessRule 15 21 32 240323 240448 4 316
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk32 := witnessRule 15 20 0 250005 250321 32 2992
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk33 := witnessRule 15 20 32 250322 250385 3 233
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk34 := witnessRule 15 19 0 260004 260321 32 2948
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk35 := witnessRule 15 19 32 260322 260384 2 150
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk36 := witnessRule 15 18 0 270003 270321 32 2880
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk37 := witnessRule 15 18 32 270384 270384 1 71
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk38 := witnessRule 15 17 0 280002 280321 31 2741
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk39 := witnessRule 15 16 0 290001 290320 29 2511
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk40 := witnessRule 15 15 0 300000 300320 27 2289
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk41 := witnessRule 15 14 0 310000 310257 24 1980
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk42 := witnessRule 15 13 0 320000 320256 21 1683
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk43 := witnessRule 15 12 0 330000 330256 19 1469
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk44 := witnessRule 15 11 0 340000 340193 16 1204
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk45 := witnessRule 15 10 0 350000 350192 14 1018
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk46 := witnessRule 15 9 0 360000 360192 12 840
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk47 := witnessRule 15 8 0 370000 370129 10 678
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk48 := witnessRule 15 7 0 380000 380128 8 524
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk49 := witnessRule 15 6 0 390000 390128 7 437
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk50 := witnessRule 15 5 0 400000 400065 5 303
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk51 := witnessRule 15 4 0 410000 410064 4 232
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk52 := witnessRule 15 3 0 420000 420064 3 165
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk53 := witnessRule 15 2 0 430000 430001 2 106
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk54 := witnessRule 15 1 0 440000 440000 1 51
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt15_chunk55 := witnessRule 15 0 0 450000 450000 1 47
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt15_chunks : List (Chunk 15) := [pack_E6970Receipt15_chunk0, pack_E6970Receipt15_chunk1, pack_E6970Receipt15_chunk2, pack_E6970Receipt15_chunk3, pack_E6970Receipt15_chunk4, pack_E6970Receipt15_chunk5, pack_E6970Receipt15_chunk6, pack_E6970Receipt15_chunk7, pack_E6970Receipt15_chunk8, pack_E6970Receipt15_chunk9, pack_E6970Receipt15_chunk10, pack_E6970Receipt15_chunk11, pack_E6970Receipt15_chunk12, pack_E6970Receipt15_chunk13, pack_E6970Receipt15_chunk14, pack_E6970Receipt15_chunk15, pack_E6970Receipt15_chunk16, pack_E6970Receipt15_chunk17, pack_E6970Receipt15_chunk18, pack_E6970Receipt15_chunk19, pack_E6970Receipt15_chunk20, pack_E6970Receipt15_chunk21, pack_E6970Receipt15_chunk22, pack_E6970Receipt15_chunk23, pack_E6970Receipt15_chunk24, pack_E6970Receipt15_chunk25, pack_E6970Receipt15_chunk26, pack_E6970Receipt15_chunk27, pack_E6970Receipt15_chunk28, pack_E6970Receipt15_chunk29, pack_E6970Receipt15_chunk30, pack_E6970Receipt15_chunk31, pack_E6970Receipt15_chunk32, pack_E6970Receipt15_chunk33, pack_E6970Receipt15_chunk34, pack_E6970Receipt15_chunk35, pack_E6970Receipt15_chunk36, pack_E6970Receipt15_chunk37, pack_E6970Receipt15_chunk38, pack_E6970Receipt15_chunk39, pack_E6970Receipt15_chunk40, pack_E6970Receipt15_chunk41, pack_E6970Receipt15_chunk42, pack_E6970Receipt15_chunk43, pack_E6970Receipt15_chunk44, pack_E6970Receipt15_chunk45, pack_E6970Receipt15_chunk46, pack_E6970Receipt15_chunk47, pack_E6970Receipt15_chunk48, pack_E6970Receipt15_chunk49, pack_E6970Receipt15_chunk50, pack_E6970Receipt15_chunk51, pack_E6970Receipt15_chunk52, pack_E6970Receipt15_chunk53, pack_E6970Receipt15_chunk54, pack_E6970Receipt15_chunk55]
def rows15 := rowsFrom pack_E6970Receipt15_chunks
theorem good15 : ∀ r ∈ rows15, good 15 r = true := rowsFrom_good pack_E6970Receipt15_chunks
theorem sorted15 : rows15.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt15_chunks 0 (by decide +kernel)).1
theorem mass15 (i : Fin 61) :
    bandCount 15 (i.val : ℤ) 60 16 ≤ (rows15.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt15_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 15 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt15_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total15 : (rows15.map (price 15)).sum = 75072 :=
  (total_eq pack_E6970Receipt15_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt15

section Pack_E6970Receipt16

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt16_chunk0 := witnessRule 16 48 0 1024 1024 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk1 := witnessRule 16 47 0 10961 10961 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk2 := witnessRule 16 46 0 20898 20960 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk3 := witnessRule 16 45 0 30835 30960 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk4 := witnessRule 16 44 0 40772 40897 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk5 := witnessRule 16 43 0 50709 50896 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk6 := witnessRule 16 42 0 60646 60896 7 733
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk7 := witnessRule 16 41 0 70583 70833 8 836
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk8 := witnessRule 16 40 0 80520 80832 10 1042
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk9 := witnessRule 16 39 0 90457 90832 12 1240
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk10 := witnessRule 16 38 0 100394 100769 14 1446
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk11 := witnessRule 16 37 0 110331 110768 16 1644
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk12 := witnessRule 16 36 0 120268 120768 19 1941
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk13 := witnessRule 16 35 0 130205 130705 21 2139
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk14 := witnessRule 16 34 0 140142 140704 24 2436
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk15 := witnessRule 16 33 0 150079 150704 27 2721
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk16 := witnessRule 16 32 0 160016 160641 30 3018
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk17 := witnessRule 16 31 0 170015 170640 32 3196
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk18 := witnessRule 16 30 0 180014 180515 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk19 := witnessRule 16 30 32 180576 180640 3 261
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk20 := witnessRule 16 29 0 190013 190512 32 3196
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk21 := witnessRule 16 29 32 190513 190577 4 348
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk22 := witnessRule 16 28 0 200012 200449 32 3192
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk23 := witnessRule 16 28 32 200450 200576 6 522
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk24 := witnessRule 16 27 0 210011 210388 32 3164
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk25 := witnessRule 16 27 32 210448 210576 7 605
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk26 := witnessRule 16 26 0 220010 220385 32 3156
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk27 := witnessRule 16 26 32 220386 220513 8 684
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk28 := witnessRule 16 25 0 230009 230325 32 3116
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk29 := witnessRule 16 25 32 230384 230512 8 684
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk30 := witnessRule 16 24 0 240008 240322 32 3104
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk31 := witnessRule 16 24 32 240323 240512 9 747
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk32 := witnessRule 16 23 0 250007 250321 32 3068
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk33 := witnessRule 16 23 32 250322 250449 8 652
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk34 := witnessRule 16 22 0 260006 260261 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk35 := witnessRule 16 22 32 260320 260448 8 652
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk36 := witnessRule 16 21 0 270005 270260 32 2984
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk37 := witnessRule 16 21 32 270320 270448 7 549
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk38 := witnessRule 16 20 0 280004 280259 32 2948
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk39 := witnessRule 16 20 32 280260 280385 6 458
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk40 := witnessRule 16 19 0 290003 290259 32 2880
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk41 := witnessRule 16 19 32 290320 290384 4 296
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk42 := witnessRule 16 18 0 300002 300259 32 2820
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk43 := witnessRule 16 18 32 300320 300384 3 213
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk44 := witnessRule 16 17 0 310001 310321 32 2724
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk45 := witnessRule 16 16 0 320000 320320 30 2502
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk46 := witnessRule 16 15 0 330000 330320 27 2181
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk47 := witnessRule 16 14 0 340000 340257 24 1884
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk48 := witnessRule 16 13 0 350000 350256 21 1599
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk49 := witnessRule 16 12 0 360000 360256 19 1393
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk50 := witnessRule 16 11 0 370000 370193 16 1140
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk51 := witnessRule 16 10 0 380000 380192 14 962
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk52 := witnessRule 16 9 0 390000 390192 12 792
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk53 := witnessRule 16 8 0 400000 400129 10 638
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk54 := witnessRule 16 7 0 410000 410128 8 492
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk55 := witnessRule 16 6 0 420000 420128 7 409
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk56 := witnessRule 16 5 0 430000 430065 5 283
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk57 := witnessRule 16 4 0 440000 440064 4 216
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk58 := witnessRule 16 3 0 450000 450064 3 153
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk59 := witnessRule 16 2 0 460000 460001 2 98
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk60 := witnessRule 16 1 0 470000 470000 1 47
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt16_chunk61 := witnessRule 16 0 0 480000 480000 1 43
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt16_chunks : List (Chunk 16) := [pack_E6970Receipt16_chunk0, pack_E6970Receipt16_chunk1, pack_E6970Receipt16_chunk2, pack_E6970Receipt16_chunk3, pack_E6970Receipt16_chunk4, pack_E6970Receipt16_chunk5, pack_E6970Receipt16_chunk6, pack_E6970Receipt16_chunk7, pack_E6970Receipt16_chunk8, pack_E6970Receipt16_chunk9, pack_E6970Receipt16_chunk10, pack_E6970Receipt16_chunk11, pack_E6970Receipt16_chunk12, pack_E6970Receipt16_chunk13, pack_E6970Receipt16_chunk14, pack_E6970Receipt16_chunk15, pack_E6970Receipt16_chunk16, pack_E6970Receipt16_chunk17, pack_E6970Receipt16_chunk18, pack_E6970Receipt16_chunk19, pack_E6970Receipt16_chunk20, pack_E6970Receipt16_chunk21, pack_E6970Receipt16_chunk22, pack_E6970Receipt16_chunk23, pack_E6970Receipt16_chunk24, pack_E6970Receipt16_chunk25, pack_E6970Receipt16_chunk26, pack_E6970Receipt16_chunk27, pack_E6970Receipt16_chunk28, pack_E6970Receipt16_chunk29, pack_E6970Receipt16_chunk30, pack_E6970Receipt16_chunk31, pack_E6970Receipt16_chunk32, pack_E6970Receipt16_chunk33, pack_E6970Receipt16_chunk34, pack_E6970Receipt16_chunk35, pack_E6970Receipt16_chunk36, pack_E6970Receipt16_chunk37, pack_E6970Receipt16_chunk38, pack_E6970Receipt16_chunk39, pack_E6970Receipt16_chunk40, pack_E6970Receipt16_chunk41, pack_E6970Receipt16_chunk42, pack_E6970Receipt16_chunk43, pack_E6970Receipt16_chunk44, pack_E6970Receipt16_chunk45, pack_E6970Receipt16_chunk46, pack_E6970Receipt16_chunk47, pack_E6970Receipt16_chunk48, pack_E6970Receipt16_chunk49, pack_E6970Receipt16_chunk50, pack_E6970Receipt16_chunk51, pack_E6970Receipt16_chunk52, pack_E6970Receipt16_chunk53, pack_E6970Receipt16_chunk54, pack_E6970Receipt16_chunk55, pack_E6970Receipt16_chunk56, pack_E6970Receipt16_chunk57, pack_E6970Receipt16_chunk58, pack_E6970Receipt16_chunk59, pack_E6970Receipt16_chunk60, pack_E6970Receipt16_chunk61]
def rows16 := rowsFrom pack_E6970Receipt16_chunks
theorem good16 : ∀ r ∈ rows16, good 16 r = true := rowsFrom_good pack_E6970Receipt16_chunks
theorem sorted16 : rows16.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt16_chunks 0 (by decide +kernel)).1
theorem mass16 (i : Fin 61) :
    bandCount 16 (i.val : ℤ) 60 16 ≤ (rows16.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt16_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 16 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt16_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total16 : (rows16.map (price 16)).sum = 88179 :=
  (total_eq pack_E6970Receipt16_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt16

section Pack_E6970Receipt17

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt17_chunk0 := witnessRule 17 50 0 11025 11025 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk1 := witnessRule 17 49 0 20962 21024 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk2 := witnessRule 17 48 0 30899 31024 3 318
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk3 := witnessRule 17 47 0 40836 40961 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk4 := witnessRule 17 46 0 50773 50960 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk5 := witnessRule 17 45 0 60710 60960 7 734
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk6 := witnessRule 17 44 0 70647 70897 8 836
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk7 := witnessRule 17 43 0 80584 80896 10 1042
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk8 := witnessRule 17 42 0 90521 90896 12 1241
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk9 := witnessRule 17 41 0 100458 100833 14 1446
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk10 := witnessRule 17 40 0 110395 110832 16 1644
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk11 := witnessRule 17 39 0 120332 120832 19 1942
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk12 := witnessRule 17 38 0 130269 130769 21 2139
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk13 := witnessRule 17 37 0 140206 140768 24 2436
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk14 := witnessRule 17 36 0 150143 150768 27 2722
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk15 := witnessRule 17 35 0 160080 160705 30 3018
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk16 := witnessRule 17 34 0 170017 170642 32 3216
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk17 := witnessRule 17 34 32 170704 170704 1 87
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk18 := witnessRule 17 33 0 180016 180578 32 3228
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk19 := witnessRule 17 33 32 180579 180704 4 349
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk20 := witnessRule 17 32 0 190015 190515 32 3224
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk21 := witnessRule 17 32 32 190516 190641 6 530
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk22 := witnessRule 17 31 0 200014 200453 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk23 := witnessRule 17 31 32 200512 200640 8 716
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk24 := witnessRule 17 30 0 210013 210449 32 3200
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk25 := witnessRule 17 30 32 210450 210640 10 879
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk26 := witnessRule 17 29 0 220012 220388 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk27 := witnessRule 17 29 32 220389 220577 11 965
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk28 := witnessRule 17 28 0 230011 230385 32 3164
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk29 := witnessRule 17 28 32 230386 230576 12 1040
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk30 := witnessRule 17 27 0 240010 240325 32 3140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk31 := witnessRule 17 27 32 240326 240576 13 1116
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk32 := witnessRule 17 26 0 250009 250322 32 3116
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk33 := witnessRule 17 26 32 250323 250513 13 1099
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk34 := witnessRule 17 25 0 260008 260320 32 3088
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk35 := witnessRule 17 25 32 260321 260512 13 1087
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk36 := witnessRule 17 24 0 270007 270261 32 3052
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk37 := witnessRule 17 24 32 270262 270512 13 1064
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk38 := witnessRule 17 23 0 280006 280259 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk39 := witnessRule 17 23 32 280260 280449 12 960
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk40 := witnessRule 17 22 0 290005 290258 32 2984
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk41 := witnessRule 17 22 32 290259 290448 11 857
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk42 := witnessRule 17 21 0 300004 300257 32 2940
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk43 := witnessRule 17 21 32 300258 300448 10 759
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk44 := witnessRule 17 20 0 310003 310257 32 2880
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk45 := witnessRule 17 20 32 310258 310385 8 588
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk46 := witnessRule 17 19 0 320002 320257 32 2820
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk47 := witnessRule 17 19 32 320258 320384 6 426
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk48 := witnessRule 17 18 0 330001 330258 32 2732
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk49 := witnessRule 17 18 32 330259 330384 4 269
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk50 := witnessRule 17 17 0 340000 340320 32 2640
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk51 := witnessRule 17 17 32 340321 340321 1 63
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk52 := witnessRule 17 16 0 350000 350320 30 2382
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk53 := witnessRule 17 15 0 360000 360320 27 2074
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk54 := witnessRule 17 14 0 370000 370257 24 1788
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk55 := witnessRule 17 13 0 380000 380256 21 1515
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk56 := witnessRule 17 12 0 390000 390256 19 1318
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk57 := witnessRule 17 11 0 400000 400193 16 1076
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk58 := witnessRule 17 10 0 410000 410192 14 906
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk59 := witnessRule 17 9 0 420000 420192 12 745
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk60 := witnessRule 17 8 0 430000 430129 10 598
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk61 := witnessRule 17 7 0 440000 440128 8 460
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk62 := witnessRule 17 6 0 450000 450128 7 382
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk63 := witnessRule 17 5 0 460000 460065 5 263
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk64 := witnessRule 17 4 0 470000 470064 4 200
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk65 := witnessRule 17 3 0 480000 480064 3 142
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk66 := witnessRule 17 2 0 490000 490001 2 90
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk67 := witnessRule 17 1 0 500000 500000 1 43
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt17_chunk68 := witnessRule 17 0 0 510000 510000 1 40
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt17_chunks : List (Chunk 17) := [pack_E6970Receipt17_chunk0, pack_E6970Receipt17_chunk1, pack_E6970Receipt17_chunk2, pack_E6970Receipt17_chunk3, pack_E6970Receipt17_chunk4, pack_E6970Receipt17_chunk5, pack_E6970Receipt17_chunk6, pack_E6970Receipt17_chunk7, pack_E6970Receipt17_chunk8, pack_E6970Receipt17_chunk9, pack_E6970Receipt17_chunk10, pack_E6970Receipt17_chunk11, pack_E6970Receipt17_chunk12, pack_E6970Receipt17_chunk13, pack_E6970Receipt17_chunk14, pack_E6970Receipt17_chunk15, pack_E6970Receipt17_chunk16, pack_E6970Receipt17_chunk17, pack_E6970Receipt17_chunk18, pack_E6970Receipt17_chunk19, pack_E6970Receipt17_chunk20, pack_E6970Receipt17_chunk21, pack_E6970Receipt17_chunk22, pack_E6970Receipt17_chunk23, pack_E6970Receipt17_chunk24, pack_E6970Receipt17_chunk25, pack_E6970Receipt17_chunk26, pack_E6970Receipt17_chunk27, pack_E6970Receipt17_chunk28, pack_E6970Receipt17_chunk29, pack_E6970Receipt17_chunk30, pack_E6970Receipt17_chunk31, pack_E6970Receipt17_chunk32, pack_E6970Receipt17_chunk33, pack_E6970Receipt17_chunk34, pack_E6970Receipt17_chunk35, pack_E6970Receipt17_chunk36, pack_E6970Receipt17_chunk37, pack_E6970Receipt17_chunk38, pack_E6970Receipt17_chunk39, pack_E6970Receipt17_chunk40, pack_E6970Receipt17_chunk41, pack_E6970Receipt17_chunk42, pack_E6970Receipt17_chunk43, pack_E6970Receipt17_chunk44, pack_E6970Receipt17_chunk45, pack_E6970Receipt17_chunk46, pack_E6970Receipt17_chunk47, pack_E6970Receipt17_chunk48, pack_E6970Receipt17_chunk49, pack_E6970Receipt17_chunk50, pack_E6970Receipt17_chunk51, pack_E6970Receipt17_chunk52, pack_E6970Receipt17_chunk53, pack_E6970Receipt17_chunk54, pack_E6970Receipt17_chunk55, pack_E6970Receipt17_chunk56, pack_E6970Receipt17_chunk57, pack_E6970Receipt17_chunk58, pack_E6970Receipt17_chunk59, pack_E6970Receipt17_chunk60, pack_E6970Receipt17_chunk61, pack_E6970Receipt17_chunk62, pack_E6970Receipt17_chunk63, pack_E6970Receipt17_chunk64, pack_E6970Receipt17_chunk65, pack_E6970Receipt17_chunk66, pack_E6970Receipt17_chunk67, pack_E6970Receipt17_chunk68]
def rows17 := rowsFrom pack_E6970Receipt17_chunks
theorem good17 : ∀ r ∈ rows17, good 17 r = true := rowsFrom_good pack_E6970Receipt17_chunks
theorem sorted17 : rows17.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt17_chunks 0 (by decide +kernel)).1
theorem mass17 (i : Fin 61) :
    bandCount 17 (i.val : ℤ) 60 16 ≤ (rows17.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt17_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 17 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt17_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total17 : (rows17.map (price 17)).sum = 102510 :=
  (total_eq pack_E6970Receipt17_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt17

section Pack_E6970Receipt18

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt18_chunk0 := witnessRule 18 52 0 21026 21026 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk1 := witnessRule 18 51 0 30963 31025 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk2 := witnessRule 18 50 0 40900 41025 4 425
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk3 := witnessRule 18 49 0 50837 51024 5 528
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk4 := witnessRule 18 48 0 60774 61024 7 735
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk5 := witnessRule 18 47 0 70711 70961 8 837
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk6 := witnessRule 18 46 0 80648 80960 10 1043
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk7 := witnessRule 18 45 0 90585 90960 12 1242
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk8 := witnessRule 18 44 0 100522 100897 14 1447
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk9 := witnessRule 18 43 0 110459 110896 16 1645
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk10 := witnessRule 18 42 0 120396 120896 19 1943
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk11 := witnessRule 18 41 0 130333 130833 21 2140
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk12 := witnessRule 18 40 0 140270 140832 24 2437
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk13 := witnessRule 18 39 0 150207 150832 27 2723
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk14 := witnessRule 18 38 0 160144 160769 30 3019
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk15 := witnessRule 18 37 0 170081 170706 32 3216
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk16 := witnessRule 18 37 32 170768 170768 1 88
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk17 := witnessRule 18 36 0 180018 180641 32 3244
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk18 := witnessRule 18 36 32 180642 180768 5 441
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk19 := witnessRule 18 35 0 190017 190578 32 3240
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk20 := witnessRule 18 35 32 190579 190705 7 622
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk21 := witnessRule 18 34 0 200016 200515 32 3240
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk22 := witnessRule 18 34 32 200516 200704 10 895
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk23 := witnessRule 18 33 0 210015 210454 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk24 := witnessRule 18 33 32 210512 210704 12 1082
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk25 := witnessRule 18 32 0 220014 220449 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk26 := witnessRule 18 32 32 220450 220641 14 1251
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk27 := witnessRule 18 31 0 230013 230389 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk28 := witnessRule 18 31 32 230390 230640 15 1330
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk29 := witnessRule 18 30 0 240012 240385 32 3172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk30 := witnessRule 18 30 32 240386 240640 17 1489
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk31 := witnessRule 18 29 0 250011 250326 32 3140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk32 := witnessRule 18 29 32 250327 250577 17 1480
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk33 := witnessRule 18 28 0 260010 260322 32 3128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk34 := witnessRule 18 28 32 260323 260576 18 1543
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk35 := witnessRule 18 27 0 270009 270320 32 3092
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk36 := witnessRule 18 27 32 270321 270576 18 1520
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk37 := witnessRule 18 26 0 280008 280261 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk38 := witnessRule 18 26 32 280262 280513 18 1495
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk39 := witnessRule 18 25 0 290007 290259 32 3044
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk40 := witnessRule 18 25 32 290260 290512 17 1380
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk41 := witnessRule 18 24 0 300006 300257 32 3012
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk42 := witnessRule 18 24 32 300258 300512 17 1353
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk43 := witnessRule 18 23 0 310005 310256 32 2960
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk44 := witnessRule 18 23 32 310257 310449 15 1174
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk45 := witnessRule 18 22 0 320004 320198 32 2916
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk46 := witnessRule 18 22 32 320256 320448 14 1075
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk47 := witnessRule 18 21 0 330003 330198 32 2856
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk48 := witnessRule 18 21 32 330256 330448 12 890
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk49 := witnessRule 18 20 0 340002 340197 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk50 := witnessRule 18 20 32 340256 340385 10 719
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk51 := witnessRule 18 19 0 350001 350256 32 2724
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk52 := witnessRule 18 19 32 350257 350384 7 478
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk53 := witnessRule 18 18 0 360000 360257 32 2644
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk54 := witnessRule 18 18 32 360258 360384 5 321
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk55 := witnessRule 18 17 0 370000 370320 32 2512
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk56 := witnessRule 18 17 32 370321 370321 1 60
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk57 := witnessRule 18 16 0 380000 380320 30 2263
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk58 := witnessRule 18 15 0 390000 390320 27 1967
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk59 := witnessRule 18 14 0 400000 400257 24 1693
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk60 := witnessRule 18 13 0 410000 410256 21 1432
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk61 := witnessRule 18 12 0 420000 420256 19 1243
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk62 := witnessRule 18 11 0 430000 430193 16 1013
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk63 := witnessRule 18 10 0 440000 440192 14 851
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk64 := witnessRule 18 9 0 450000 450192 12 698
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk65 := witnessRule 18 8 0 460000 460129 10 559
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk66 := witnessRule 18 7 0 470000 470128 8 429
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk67 := witnessRule 18 6 0 480000 480128 7 355
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk68 := witnessRule 18 5 0 490000 490065 5 244
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk69 := witnessRule 18 4 0 500000 500064 4 185
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk70 := witnessRule 18 3 0 510000 510064 3 131
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk71 := witnessRule 18 2 0 520000 520001 2 83
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk72 := witnessRule 18 1 0 530000 530000 1 40
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt18_chunk73 := witnessRule 18 0 0 540000 540000 1 37
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt18_chunks : List (Chunk 18) := [pack_E6970Receipt18_chunk0, pack_E6970Receipt18_chunk1, pack_E6970Receipt18_chunk2, pack_E6970Receipt18_chunk3, pack_E6970Receipt18_chunk4, pack_E6970Receipt18_chunk5, pack_E6970Receipt18_chunk6, pack_E6970Receipt18_chunk7, pack_E6970Receipt18_chunk8, pack_E6970Receipt18_chunk9, pack_E6970Receipt18_chunk10, pack_E6970Receipt18_chunk11, pack_E6970Receipt18_chunk12, pack_E6970Receipt18_chunk13, pack_E6970Receipt18_chunk14, pack_E6970Receipt18_chunk15, pack_E6970Receipt18_chunk16, pack_E6970Receipt18_chunk17, pack_E6970Receipt18_chunk18, pack_E6970Receipt18_chunk19, pack_E6970Receipt18_chunk20, pack_E6970Receipt18_chunk21, pack_E6970Receipt18_chunk22, pack_E6970Receipt18_chunk23, pack_E6970Receipt18_chunk24, pack_E6970Receipt18_chunk25, pack_E6970Receipt18_chunk26, pack_E6970Receipt18_chunk27, pack_E6970Receipt18_chunk28, pack_E6970Receipt18_chunk29, pack_E6970Receipt18_chunk30, pack_E6970Receipt18_chunk31, pack_E6970Receipt18_chunk32, pack_E6970Receipt18_chunk33, pack_E6970Receipt18_chunk34, pack_E6970Receipt18_chunk35, pack_E6970Receipt18_chunk36, pack_E6970Receipt18_chunk37, pack_E6970Receipt18_chunk38, pack_E6970Receipt18_chunk39, pack_E6970Receipt18_chunk40, pack_E6970Receipt18_chunk41, pack_E6970Receipt18_chunk42, pack_E6970Receipt18_chunk43, pack_E6970Receipt18_chunk44, pack_E6970Receipt18_chunk45, pack_E6970Receipt18_chunk46, pack_E6970Receipt18_chunk47, pack_E6970Receipt18_chunk48, pack_E6970Receipt18_chunk49, pack_E6970Receipt18_chunk50, pack_E6970Receipt18_chunk51, pack_E6970Receipt18_chunk52, pack_E6970Receipt18_chunk53, pack_E6970Receipt18_chunk54, pack_E6970Receipt18_chunk55, pack_E6970Receipt18_chunk56, pack_E6970Receipt18_chunk57, pack_E6970Receipt18_chunk58, pack_E6970Receipt18_chunk59, pack_E6970Receipt18_chunk60, pack_E6970Receipt18_chunk61, pack_E6970Receipt18_chunk62, pack_E6970Receipt18_chunk63, pack_E6970Receipt18_chunk64, pack_E6970Receipt18_chunk65, pack_E6970Receipt18_chunk66, pack_E6970Receipt18_chunk67, pack_E6970Receipt18_chunk68, pack_E6970Receipt18_chunk69, pack_E6970Receipt18_chunk70, pack_E6970Receipt18_chunk71, pack_E6970Receipt18_chunk72, pack_E6970Receipt18_chunk73]
def rows18 := rowsFrom pack_E6970Receipt18_chunks
theorem good18 : ∀ r ∈ rows18, good 18 r = true := rowsFrom_good pack_E6970Receipt18_chunks
theorem sorted18 : rows18.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt18_chunks 0 (by decide +kernel)).1
theorem mass18 (i : Fin 61) :
    bandCount 18 (i.val : ℤ) 60 16 ≤ (rows18.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt18_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 18 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt18_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total18 : (rows18.map (price 18)).sum = 118014 :=
  (total_eq pack_E6970Receipt18_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt18

section Pack_E6970Receipt19

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt19_chunk0 := witnessRule 19 54 0 31027 31027 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk1 := witnessRule 19 53 0 40964 41026 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk2 := witnessRule 19 52 0 50901 51026 4 425
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk3 := witnessRule 19 51 0 60838 61025 6 635
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk4 := witnessRule 19 50 0 70775 71025 8 839
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk5 := witnessRule 19 49 0 80712 81024 10 1045
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk6 := witnessRule 19 48 0 90649 91024 12 1244
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk7 := witnessRule 19 47 0 100586 100961 14 1449
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk8 := witnessRule 19 46 0 110523 110960 16 1647
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk9 := witnessRule 19 45 0 120460 120960 19 1945
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk10 := witnessRule 19 44 0 130397 130897 21 2142
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk11 := witnessRule 19 43 0 140334 140896 24 2439
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk12 := witnessRule 19 42 0 150271 150896 27 2725
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk13 := witnessRule 19 41 0 160208 160833 30 3021
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk14 := witnessRule 19 40 0 170145 170770 32 3217
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk15 := witnessRule 19 40 32 170832 170832 1 89
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk16 := witnessRule 19 39 0 180082 180705 32 3244
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk17 := witnessRule 19 39 32 180706 180832 5 443
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk18 := witnessRule 19 38 0 190019 190641 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk19 := witnessRule 19 38 32 190642 190769 8 719
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk20 := witnessRule 19 37 0 200018 200578 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk21 := witnessRule 19 37 32 200579 200768 11 992
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk22 := witnessRule 19 36 0 210017 210516 32 3240
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk23 := witnessRule 19 36 32 210517 210768 14 1262
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk24 := witnessRule 19 35 0 220016 220455 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk25 := witnessRule 19 35 32 220512 220705 16 1463
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk26 := witnessRule 19 34 0 230015 230450 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk27 := witnessRule 19 34 32 230451 230704 18 1617
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk28 := witnessRule 19 33 0 240014 240390 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk29 := witnessRule 19 33 32 240391 240704 20 1788
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk30 := witnessRule 19 32 0 250013 250386 32 3172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk31 := witnessRule 19 32 32 250387 250641 21 1854
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk32 := witnessRule 19 31 0 260012 260327 32 3140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk33 := witnessRule 19 31 32 260328 260640 22 1937
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk34 := witnessRule 19 30 0 270011 270323 32 3128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk35 := witnessRule 19 30 32 270324 270640 23 1981
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk36 := witnessRule 19 29 0 280010 280320 32 3096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk37 := witnessRule 19 29 32 280321 280577 23 1972
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk38 := witnessRule 19 28 0 290009 290262 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk39 := witnessRule 19 28 32 290263 290576 23 1932
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk40 := witnessRule 19 27 0 300008 300259 32 3060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk41 := witnessRule 19 27 32 300260 300576 23 1889
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk42 := witnessRule 19 26 0 310007 310257 32 3020
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk43 := witnessRule 19 26 32 310258 310513 22 1781
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk44 := witnessRule 19 25 0 320006 320200 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk45 := witnessRule 19 25 32 320256 320512 21 1686
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk46 := witnessRule 19 24 0 330005 330198 32 2944
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk47 := witnessRule 19 24 32 330199 330512 20 1548
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk48 := witnessRule 19 23 0 340004 340197 32 2916
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk49 := witnessRule 19 23 32 340198 340449 18 1353
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk50 := witnessRule 19 22 0 350003 350196 32 2856
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk51 := witnessRule 19 22 32 350197 350448 16 1167
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk52 := witnessRule 19 21 0 360002 360196 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk53 := witnessRule 19 21 32 360197 360448 14 982
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk54 := witnessRule 19 20 0 370001 370196 32 2716
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk55 := witnessRule 19 20 32 370197 370385 11 748
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk56 := witnessRule 19 19 0 380000 380197 32 2628
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk57 := witnessRule 19 19 32 380256 380384 8 527
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk58 := witnessRule 19 18 0 390000 390257 32 2516
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk59 := witnessRule 19 18 32 390258 390384 5 303
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk60 := witnessRule 19 17 0 400000 400320 32 2385
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk61 := witnessRule 19 17 32 400321 400321 1 57
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk62 := witnessRule 19 16 0 410000 410320 30 2145
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk63 := witnessRule 19 15 0 420000 420320 27 1861
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk64 := witnessRule 19 14 0 430000 430257 24 1599
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk65 := witnessRule 19 13 0 440000 440256 21 1350
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk66 := witnessRule 19 12 0 450000 450256 19 1169
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk67 := witnessRule 19 11 0 460000 460193 16 951
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk68 := witnessRule 19 10 0 470000 470192 14 797
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk69 := witnessRule 19 9 0 480000 480192 12 652
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk70 := witnessRule 19 8 0 490000 490129 10 521
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk71 := witnessRule 19 7 0 500000 500128 8 399
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk72 := witnessRule 19 6 0 510000 510128 7 329
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk73 := witnessRule 19 5 0 520000 520065 5 226
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk74 := witnessRule 19 4 0 530000 530064 4 171
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk75 := witnessRule 19 3 0 540000 540064 3 121
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk76 := witnessRule 19 2 0 550000 550001 2 77
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk77 := witnessRule 19 1 0 560000 560000 1 37
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt19_chunk78 := witnessRule 19 0 0 570000 570000 1 34
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt19_chunks : List (Chunk 19) := [pack_E6970Receipt19_chunk0, pack_E6970Receipt19_chunk1, pack_E6970Receipt19_chunk2, pack_E6970Receipt19_chunk3, pack_E6970Receipt19_chunk4, pack_E6970Receipt19_chunk5, pack_E6970Receipt19_chunk6, pack_E6970Receipt19_chunk7, pack_E6970Receipt19_chunk8, pack_E6970Receipt19_chunk9, pack_E6970Receipt19_chunk10, pack_E6970Receipt19_chunk11, pack_E6970Receipt19_chunk12, pack_E6970Receipt19_chunk13, pack_E6970Receipt19_chunk14, pack_E6970Receipt19_chunk15, pack_E6970Receipt19_chunk16, pack_E6970Receipt19_chunk17, pack_E6970Receipt19_chunk18, pack_E6970Receipt19_chunk19, pack_E6970Receipt19_chunk20, pack_E6970Receipt19_chunk21, pack_E6970Receipt19_chunk22, pack_E6970Receipt19_chunk23, pack_E6970Receipt19_chunk24, pack_E6970Receipt19_chunk25, pack_E6970Receipt19_chunk26, pack_E6970Receipt19_chunk27, pack_E6970Receipt19_chunk28, pack_E6970Receipt19_chunk29, pack_E6970Receipt19_chunk30, pack_E6970Receipt19_chunk31, pack_E6970Receipt19_chunk32, pack_E6970Receipt19_chunk33, pack_E6970Receipt19_chunk34, pack_E6970Receipt19_chunk35, pack_E6970Receipt19_chunk36, pack_E6970Receipt19_chunk37, pack_E6970Receipt19_chunk38, pack_E6970Receipt19_chunk39, pack_E6970Receipt19_chunk40, pack_E6970Receipt19_chunk41, pack_E6970Receipt19_chunk42, pack_E6970Receipt19_chunk43, pack_E6970Receipt19_chunk44, pack_E6970Receipt19_chunk45, pack_E6970Receipt19_chunk46, pack_E6970Receipt19_chunk47, pack_E6970Receipt19_chunk48, pack_E6970Receipt19_chunk49, pack_E6970Receipt19_chunk50, pack_E6970Receipt19_chunk51, pack_E6970Receipt19_chunk52, pack_E6970Receipt19_chunk53, pack_E6970Receipt19_chunk54, pack_E6970Receipt19_chunk55, pack_E6970Receipt19_chunk56, pack_E6970Receipt19_chunk57, pack_E6970Receipt19_chunk58, pack_E6970Receipt19_chunk59, pack_E6970Receipt19_chunk60, pack_E6970Receipt19_chunk61, pack_E6970Receipt19_chunk62, pack_E6970Receipt19_chunk63, pack_E6970Receipt19_chunk64, pack_E6970Receipt19_chunk65, pack_E6970Receipt19_chunk66, pack_E6970Receipt19_chunk67, pack_E6970Receipt19_chunk68, pack_E6970Receipt19_chunk69, pack_E6970Receipt19_chunk70, pack_E6970Receipt19_chunk71, pack_E6970Receipt19_chunk72, pack_E6970Receipt19_chunk73, pack_E6970Receipt19_chunk74, pack_E6970Receipt19_chunk75, pack_E6970Receipt19_chunk76, pack_E6970Receipt19_chunk77, pack_E6970Receipt19_chunk78]
def rows19 := rowsFrom pack_E6970Receipt19_chunks
theorem good19 : ∀ r ∈ rows19, good 19 r = true := rowsFrom_good pack_E6970Receipt19_chunks
theorem sorted19 : rows19.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt19_chunks 0 (by decide +kernel)).1
theorem mass19 (i : Fin 61) :
    bandCount 19 (i.val : ℤ) 60 16 ≤ (rows19.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt19_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 19 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt19_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total19 : (rows19.map (price 19)).sum = 134640 :=
  (total_eq pack_E6970Receipt19_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt19

section Pack_E6970Receipt2

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt2_chunk0 := witnessRule 2 6 0 128 128 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt2_chunk1 := witnessRule 2 5 0 10065 10065 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt2_chunk2 := witnessRule 2 4 0 20002 20064 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt2_chunk3 := witnessRule 2 3 0 30001 30064 2 210
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt2_chunk4 := witnessRule 2 2 0 40000 40001 2 210
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt2_chunk5 := witnessRule 2 1 0 50000 50000 1 103
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt2_chunk6 := witnessRule 2 0 0 60000 60000 1 99
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt2_chunks : List (Chunk 2) := [pack_E6970Receipt2_chunk0, pack_E6970Receipt2_chunk1, pack_E6970Receipt2_chunk2, pack_E6970Receipt2_chunk3, pack_E6970Receipt2_chunk4, pack_E6970Receipt2_chunk5, pack_E6970Receipt2_chunk6]
def rows2 := rowsFrom pack_E6970Receipt2_chunks
theorem good2 : ∀ r ∈ rows2, good 2 r = true := rowsFrom_good pack_E6970Receipt2_chunks
theorem sorted2 : rows2.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt2_chunks 0 (by decide +kernel)).1
theorem mass2 (i : Fin 61) :
    bandCount 2 (i.val : ℤ) 60 16 ≤ (rows2.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt2_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 2 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt2_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total2 : (rows2.map (price 2)).sum = 1050 :=
  (total_eq pack_E6970Receipt2_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt2

section Pack_E6970Receipt20

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt20_chunk0 := witnessRule 20 56 0 41028 41028 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk1 := witnessRule 20 55 0 50965 51027 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk2 := witnessRule 20 54 0 60902 61027 4 425
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk3 := witnessRule 20 53 0 70839 71026 6 635
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk4 := witnessRule 20 52 0 80776 81026 9 946
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk5 := witnessRule 20 51 0 90713 91025 11 1149
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk6 := witnessRule 20 50 0 100650 101025 14 1452
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk7 := witnessRule 20 49 0 110587 111024 16 1650
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk8 := witnessRule 20 48 0 120524 121024 19 1949
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk9 := witnessRule 20 47 0 130461 130961 21 2145
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk10 := witnessRule 20 46 0 140398 140960 24 2442
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk11 := witnessRule 20 45 0 150335 150960 27 2729
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk12 := witnessRule 20 44 0 160272 160897 30 3024
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk13 := witnessRule 20 43 0 170209 170834 32 3219
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk14 := witnessRule 20 43 32 170896 170896 1 90
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk15 := witnessRule 20 42 0 180146 180769 32 3244
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk16 := witnessRule 20 42 32 180770 180896 5 447
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk17 := witnessRule 20 41 0 190083 190705 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk18 := witnessRule 20 41 32 190706 190833 8 722
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk19 := witnessRule 20 40 0 200020 200641 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk20 := witnessRule 20 40 32 200642 200832 12 1094
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk21 := witnessRule 20 39 0 210019 210579 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk22 := witnessRule 20 39 32 210580 210832 15 1361
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk23 := witnessRule 20 38 0 220018 220517 32 3240
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk24 := witnessRule 20 38 32 220518 220769 18 1644
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk25 := witnessRule 20 37 0 230017 230456 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk26 := witnessRule 20 37 32 230513 230768 20 1830
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk27 := witnessRule 20 36 0 240016 240451 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk28 := witnessRule 20 36 32 240452 240768 23 2077
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk29 := witnessRule 20 35 0 250015 250391 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk30 := witnessRule 20 35 32 250392 250705 24 2154
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk31 := witnessRule 20 34 0 260014 260387 32 3172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk32 := witnessRule 20 34 32 260388 260704 26 2312
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk33 := witnessRule 20 33 0 270013 270328 32 3140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk34 := witnessRule 20 33 32 270329 270704 27 2377
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk35 := witnessRule 20 32 0 280012 280324 32 3128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk36 := witnessRule 20 32 32 280325 280641 28 2438
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk37 := witnessRule 20 31 0 290011 290321 32 3096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk38 := witnessRule 20 31 32 290322 290640 28 2410
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk39 := witnessRule 20 30 0 300010 300263 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk40 := witnessRule 20 30 32 300264 300640 29 2459
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk41 := witnessRule 20 29 0 310009 310260 32 3060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk42 := witnessRule 20 29 32 310261 310577 28 2326
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk43 := witnessRule 20 28 0 320008 320257 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk44 := witnessRule 20 28 32 320258 320576 28 2298
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk45 := witnessRule 20 27 0 330007 330201 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk46 := witnessRule 20 27 32 330256 330576 27 2189
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk47 := witnessRule 20 26 0 340006 340198 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk48 := witnessRule 20 26 32 340199 340513 26 2044
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk49 := witnessRule 20 25 0 350005 350197 32 2940
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk50 := witnessRule 20 25 32 350198 350512 24 1830
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk51 := witnessRule 20 24 0 360004 360195 32 2900
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk52 := witnessRule 20 24 32 360196 360512 23 1709
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk53 := witnessRule 20 23 0 370003 370195 32 2848
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk54 := witnessRule 20 23 32 370196 370449 20 1438
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk55 := witnessRule 20 22 0 380002 380194 32 2788
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk56 := witnessRule 20 22 32 380195 380448 18 1260
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk57 := witnessRule 20 21 0 390001 390195 32 2712
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk58 := witnessRule 20 21 32 390196 390448 15 1001
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk59 := witnessRule 20 20 0 400000 400195 32 2628
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk60 := witnessRule 20 20 32 400196 400385 12 774
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk61 := witnessRule 20 19 0 410000 410197 32 2500
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk62 := witnessRule 20 19 32 410256 410384 8 498
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk63 := witnessRule 20 18 0 420000 420257 32 2388
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk64 := witnessRule 20 18 32 420258 420384 5 287
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk65 := witnessRule 20 17 0 430000 430320 32 2259
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk66 := witnessRule 20 17 32 430321 430321 1 54
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk67 := witnessRule 20 16 0 440000 440320 30 2028
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk68 := witnessRule 20 15 0 450000 450320 27 1757
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk69 := witnessRule 20 14 0 460000 460257 24 1506
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk70 := witnessRule 20 13 0 470000 470256 21 1269
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk71 := witnessRule 20 12 0 480000 480256 19 1097
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk72 := witnessRule 20 11 0 490000 490193 16 890
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk73 := witnessRule 20 10 0 500000 500192 14 744
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk74 := witnessRule 20 9 0 510000 510192 12 608
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk75 := witnessRule 20 8 0 520000 520129 10 484
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk76 := witnessRule 20 7 0 530000 530128 8 370
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk77 := witnessRule 20 6 0 540000 540128 7 305
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk78 := witnessRule 20 5 0 550000 550065 5 209
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk79 := witnessRule 20 4 0 560000 560064 4 158
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk80 := witnessRule 20 3 0 570000 570064 3 112
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk81 := witnessRule 20 2 0 580000 580001 2 71
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk82 := witnessRule 20 1 0 590000 590000 1 34
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt20_chunk83 := witnessRule 20 0 0 600000 600000 1 31
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt20_chunks : List (Chunk 20) := [pack_E6970Receipt20_chunk0, pack_E6970Receipt20_chunk1, pack_E6970Receipt20_chunk2, pack_E6970Receipt20_chunk3, pack_E6970Receipt20_chunk4, pack_E6970Receipt20_chunk5, pack_E6970Receipt20_chunk6, pack_E6970Receipt20_chunk7, pack_E6970Receipt20_chunk8, pack_E6970Receipt20_chunk9, pack_E6970Receipt20_chunk10, pack_E6970Receipt20_chunk11, pack_E6970Receipt20_chunk12, pack_E6970Receipt20_chunk13, pack_E6970Receipt20_chunk14, pack_E6970Receipt20_chunk15, pack_E6970Receipt20_chunk16, pack_E6970Receipt20_chunk17, pack_E6970Receipt20_chunk18, pack_E6970Receipt20_chunk19, pack_E6970Receipt20_chunk20, pack_E6970Receipt20_chunk21, pack_E6970Receipt20_chunk22, pack_E6970Receipt20_chunk23, pack_E6970Receipt20_chunk24, pack_E6970Receipt20_chunk25, pack_E6970Receipt20_chunk26, pack_E6970Receipt20_chunk27, pack_E6970Receipt20_chunk28, pack_E6970Receipt20_chunk29, pack_E6970Receipt20_chunk30, pack_E6970Receipt20_chunk31, pack_E6970Receipt20_chunk32, pack_E6970Receipt20_chunk33, pack_E6970Receipt20_chunk34, pack_E6970Receipt20_chunk35, pack_E6970Receipt20_chunk36, pack_E6970Receipt20_chunk37, pack_E6970Receipt20_chunk38, pack_E6970Receipt20_chunk39, pack_E6970Receipt20_chunk40, pack_E6970Receipt20_chunk41, pack_E6970Receipt20_chunk42, pack_E6970Receipt20_chunk43, pack_E6970Receipt20_chunk44, pack_E6970Receipt20_chunk45, pack_E6970Receipt20_chunk46, pack_E6970Receipt20_chunk47, pack_E6970Receipt20_chunk48, pack_E6970Receipt20_chunk49, pack_E6970Receipt20_chunk50, pack_E6970Receipt20_chunk51, pack_E6970Receipt20_chunk52, pack_E6970Receipt20_chunk53, pack_E6970Receipt20_chunk54, pack_E6970Receipt20_chunk55, pack_E6970Receipt20_chunk56, pack_E6970Receipt20_chunk57, pack_E6970Receipt20_chunk58, pack_E6970Receipt20_chunk59, pack_E6970Receipt20_chunk60, pack_E6970Receipt20_chunk61, pack_E6970Receipt20_chunk62, pack_E6970Receipt20_chunk63, pack_E6970Receipt20_chunk64, pack_E6970Receipt20_chunk65, pack_E6970Receipt20_chunk66, pack_E6970Receipt20_chunk67, pack_E6970Receipt20_chunk68, pack_E6970Receipt20_chunk69, pack_E6970Receipt20_chunk70, pack_E6970Receipt20_chunk71, pack_E6970Receipt20_chunk72, pack_E6970Receipt20_chunk73, pack_E6970Receipt20_chunk74, pack_E6970Receipt20_chunk75, pack_E6970Receipt20_chunk76, pack_E6970Receipt20_chunk77, pack_E6970Receipt20_chunk78, pack_E6970Receipt20_chunk79, pack_E6970Receipt20_chunk80, pack_E6970Receipt20_chunk81, pack_E6970Receipt20_chunk82, pack_E6970Receipt20_chunk83]
def rows20 := rowsFrom pack_E6970Receipt20_chunks
theorem good20 : ∀ r ∈ rows20, good 20 r = true := rowsFrom_good pack_E6970Receipt20_chunks
theorem sorted20 : rows20.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt20_chunks 0 (by decide +kernel)).1
theorem mass20 (i : Fin 61) :
    bandCount 20 (i.val : ℤ) 60 16 ≤ (rows20.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt20_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 20 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt20_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total20 : (rows20.map (price 20)).sum = 152337 :=
  (total_eq pack_E6970Receipt20_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt20

section Pack_E6970Receipt21

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt21_chunk0 := witnessRule 21 58 0 51029 51029 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk1 := witnessRule 21 57 0 60966 61028 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk2 := witnessRule 21 56 0 70903 71028 4 425
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk3 := witnessRule 21 55 0 80840 81027 6 635
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk4 := witnessRule 21 54 0 90777 91027 9 946
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk5 := witnessRule 21 53 0 100714 101026 12 1256
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk6 := witnessRule 21 52 0 110651 111026 15 1556
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk7 := witnessRule 21 51 0 120588 121025 18 1858
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk8 := witnessRule 21 50 0 130525 131025 21 2150
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk9 := witnessRule 21 49 0 140462 141024 24 2447
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk10 := witnessRule 21 48 0 150399 151024 27 2734
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk11 := witnessRule 21 47 0 160336 160961 30 3029
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk12 := witnessRule 21 46 0 170273 170898 32 3223
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk13 := witnessRule 21 46 32 170960 170960 1 91
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk14 := witnessRule 21 45 0 180210 180833 32 3244
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk15 := witnessRule 21 45 32 180834 180960 5 452
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk16 := witnessRule 21 44 0 190147 190769 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk17 := witnessRule 21 44 32 190770 190897 8 727
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk18 := witnessRule 21 43 0 200084 200705 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk19 := witnessRule 21 43 32 200706 200896 12 1099
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk20 := witnessRule 21 42 0 210021 210642 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk21 := witnessRule 21 42 32 210643 210896 16 1465
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk22 := witnessRule 21 41 0 220020 220580 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk23 := witnessRule 21 41 32 220581 220833 19 1744
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk24 := witnessRule 21 40 0 230019 230518 32 3240
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk25 := witnessRule 21 40 32 230519 230832 22 2013
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk26 := witnessRule 21 39 0 240018 240457 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk27 := witnessRule 21 39 32 240514 240832 25 2292
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk28 := witnessRule 21 38 0 250017 250452 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk29 := witnessRule 21 38 32 250453 250769 27 2444
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk30 := witnessRule 21 37 0 260016 260392 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk31 := witnessRule 21 37 32 260393 260768 29 2614
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk32 := witnessRule 21 36 0 270015 270388 32 3172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk33 := witnessRule 21 36 32 270389 270768 31 2754
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk34 := witnessRule 21 35 0 280014 280329 32 3140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk35 := witnessRule 21 35 32 280330 280705 32 2835
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk36 := witnessRule 21 34 0 290013 290325 32 3128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk37 := witnessRule 21 34 32 290326 290642 32 2803
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk38 := witnessRule 21 34 64 290704 290704 1 75
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk39 := witnessRule 21 33 0 300012 300322 32 3096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk40 := witnessRule 21 33 32 300323 300640 32 2793
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk41 := witnessRule 21 33 64 300641 300704 2 146
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk42 := witnessRule 21 32 0 310011 310264 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk43 := witnessRule 21 32 32 310265 310578 32 2752
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk44 := witnessRule 21 32 64 310640 310641 2 145
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk45 := witnessRule 21 31 0 320010 320261 32 3060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk46 := witnessRule 21 31 32 320262 320577 32 2712
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk47 := witnessRule 21 31 64 320578 320640 2 141
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk48 := witnessRule 21 30 0 330009 330258 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk49 := witnessRule 21 30 32 330259 330576 32 2665
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk50 := witnessRule 21 30 64 330577 330640 2 138
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk51 := witnessRule 21 29 0 340008 340202 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk52 := witnessRule 21 29 32 340256 340576 32 2647
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk53 := witnessRule 21 29 64 340577 340577 1 67
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk54 := witnessRule 21 28 0 350007 350199 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk55 := witnessRule 21 28 32 350200 350576 32 2547
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk56 := witnessRule 21 27 0 360006 360197 32 2964
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk57 := witnessRule 21 27 32 360198 360576 31 2394
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk58 := witnessRule 21 26 0 370005 370195 32 2916
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk59 := witnessRule 21 26 32 370196 370513 29 2194
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk60 := witnessRule 21 25 0 380004 380194 32 2884
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk61 := witnessRule 21 25 32 380195 380512 27 1988
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk62 := witnessRule 21 24 0 390003 390193 32 2816
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk63 := witnessRule 21 24 32 390194 390512 25 1792
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk64 := witnessRule 21 23 0 400002 400193 32 2772
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk65 := witnessRule 21 23 32 400194 400449 22 1525
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk66 := witnessRule 21 22 0 410001 410193 32 2688
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk67 := witnessRule 21 22 32 410194 410448 19 1272
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk68 := witnessRule 21 21 0 420000 420194 32 2620
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk69 := witnessRule 21 21 32 420195 420448 16 1017
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk70 := witnessRule 21 20 0 430000 430195 32 2500
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk71 := witnessRule 21 20 32 430196 430385 12 731
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk72 := witnessRule 21 19 0 440000 440197 32 2372
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk73 := witnessRule 21 19 32 440256 440384 8 471
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk74 := witnessRule 21 18 0 450000 450257 32 2260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk75 := witnessRule 21 18 32 450258 450384 5 272
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk76 := witnessRule 21 17 0 460000 460320 32 2135
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk77 := witnessRule 21 17 32 460321 460321 1 51
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk78 := witnessRule 21 16 0 470000 470320 30 1913
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk79 := witnessRule 21 15 0 480000 480320 27 1654
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk80 := witnessRule 21 14 0 490000 490257 24 1415
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk81 := witnessRule 21 13 0 500000 500256 21 1190
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk82 := witnessRule 21 12 0 510000 510256 19 1026
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk83 := witnessRule 21 11 0 520000 520193 16 831
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk84 := witnessRule 21 10 0 530000 530192 14 693
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk85 := witnessRule 21 9 0 540000 540192 12 565
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk86 := witnessRule 21 8 0 550000 550129 10 449
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk87 := witnessRule 21 7 0 560000 560128 8 343
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk88 := witnessRule 21 6 0 570000 570128 7 282
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk89 := witnessRule 21 5 0 580000 580065 5 193
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk90 := witnessRule 21 4 0 590000 590064 4 146
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk91 := witnessRule 21 3 0 600000 600064 3 103
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk92 := witnessRule 21 2 0 610000 610001 2 65
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk93 := witnessRule 21 1 0 620000 620000 1 31
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt21_chunk94 := witnessRule 21 0 0 630000 630000 1 28
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt21_chunks : List (Chunk 21) := [pack_E6970Receipt21_chunk0, pack_E6970Receipt21_chunk1, pack_E6970Receipt21_chunk2, pack_E6970Receipt21_chunk3, pack_E6970Receipt21_chunk4, pack_E6970Receipt21_chunk5, pack_E6970Receipt21_chunk6, pack_E6970Receipt21_chunk7, pack_E6970Receipt21_chunk8, pack_E6970Receipt21_chunk9, pack_E6970Receipt21_chunk10, pack_E6970Receipt21_chunk11, pack_E6970Receipt21_chunk12, pack_E6970Receipt21_chunk13, pack_E6970Receipt21_chunk14, pack_E6970Receipt21_chunk15, pack_E6970Receipt21_chunk16, pack_E6970Receipt21_chunk17, pack_E6970Receipt21_chunk18, pack_E6970Receipt21_chunk19, pack_E6970Receipt21_chunk20, pack_E6970Receipt21_chunk21, pack_E6970Receipt21_chunk22, pack_E6970Receipt21_chunk23, pack_E6970Receipt21_chunk24, pack_E6970Receipt21_chunk25, pack_E6970Receipt21_chunk26, pack_E6970Receipt21_chunk27, pack_E6970Receipt21_chunk28, pack_E6970Receipt21_chunk29, pack_E6970Receipt21_chunk30, pack_E6970Receipt21_chunk31, pack_E6970Receipt21_chunk32, pack_E6970Receipt21_chunk33, pack_E6970Receipt21_chunk34, pack_E6970Receipt21_chunk35, pack_E6970Receipt21_chunk36, pack_E6970Receipt21_chunk37, pack_E6970Receipt21_chunk38, pack_E6970Receipt21_chunk39, pack_E6970Receipt21_chunk40, pack_E6970Receipt21_chunk41, pack_E6970Receipt21_chunk42, pack_E6970Receipt21_chunk43, pack_E6970Receipt21_chunk44, pack_E6970Receipt21_chunk45, pack_E6970Receipt21_chunk46, pack_E6970Receipt21_chunk47, pack_E6970Receipt21_chunk48, pack_E6970Receipt21_chunk49, pack_E6970Receipt21_chunk50, pack_E6970Receipt21_chunk51, pack_E6970Receipt21_chunk52, pack_E6970Receipt21_chunk53, pack_E6970Receipt21_chunk54, pack_E6970Receipt21_chunk55, pack_E6970Receipt21_chunk56, pack_E6970Receipt21_chunk57, pack_E6970Receipt21_chunk58, pack_E6970Receipt21_chunk59, pack_E6970Receipt21_chunk60, pack_E6970Receipt21_chunk61, pack_E6970Receipt21_chunk62, pack_E6970Receipt21_chunk63, pack_E6970Receipt21_chunk64, pack_E6970Receipt21_chunk65, pack_E6970Receipt21_chunk66, pack_E6970Receipt21_chunk67, pack_E6970Receipt21_chunk68, pack_E6970Receipt21_chunk69, pack_E6970Receipt21_chunk70, pack_E6970Receipt21_chunk71, pack_E6970Receipt21_chunk72, pack_E6970Receipt21_chunk73, pack_E6970Receipt21_chunk74, pack_E6970Receipt21_chunk75, pack_E6970Receipt21_chunk76, pack_E6970Receipt21_chunk77, pack_E6970Receipt21_chunk78, pack_E6970Receipt21_chunk79, pack_E6970Receipt21_chunk80, pack_E6970Receipt21_chunk81, pack_E6970Receipt21_chunk82, pack_E6970Receipt21_chunk83, pack_E6970Receipt21_chunk84, pack_E6970Receipt21_chunk85, pack_E6970Receipt21_chunk86, pack_E6970Receipt21_chunk87, pack_E6970Receipt21_chunk88, pack_E6970Receipt21_chunk89, pack_E6970Receipt21_chunk90, pack_E6970Receipt21_chunk91, pack_E6970Receipt21_chunk92, pack_E6970Receipt21_chunk93, pack_E6970Receipt21_chunk94]
def rows21 := rowsFrom pack_E6970Receipt21_chunks
theorem good21 : ∀ r ∈ rows21, good 21 r = true := rowsFrom_good pack_E6970Receipt21_chunks
theorem sorted21 : rows21.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt21_chunks 0 (by decide +kernel)).1
theorem mass21 (i : Fin 61) :
    bandCount 21 (i.val : ℤ) 60 16 ≤ (rows21.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt21_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 21 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt21_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total21 : (rows21.map (price 21)).sum = 171054 :=
  (total_eq pack_E6970Receipt21_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt21

section Pack_E6970Receipt22

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt22_chunk0 := witnessRule 22 60 0 61030 61030 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk1 := witnessRule 22 59 0 70967 71029 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk2 := witnessRule 22 58 0 80904 81029 4 425
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk3 := witnessRule 22 57 0 90841 91028 6 635
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk4 := witnessRule 22 56 0 100778 101028 9 946
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk5 := witnessRule 22 55 0 110715 111027 12 1256
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk6 := witnessRule 22 54 0 120652 121027 16 1663
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk7 := witnessRule 22 53 0 130589 131026 19 1962
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk8 := witnessRule 22 52 0 140526 141026 23 2358
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk9 := witnessRule 22 51 0 150463 151025 26 2648
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk10 := witnessRule 22 50 0 160400 161025 30 3036
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk11 := witnessRule 22 49 0 170337 170962 32 3229
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk12 := witnessRule 22 49 32 171024 171024 1 92
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk13 := witnessRule 22 48 0 180274 180897 32 3246
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk14 := witnessRule 22 48 32 180898 181024 5 457
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk15 := witnessRule 22 47 0 190211 190833 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk16 := witnessRule 22 47 32 190834 190961 8 734
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk17 := witnessRule 22 46 0 200148 200769 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk18 := witnessRule 22 46 32 200770 200960 12 1106
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk19 := witnessRule 22 45 0 210085 210706 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk20 := witnessRule 22 45 32 210707 210960 16 1472
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk21 := witnessRule 22 44 0 220022 220643 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk22 := witnessRule 22 44 32 220644 220897 20 1850
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk23 := witnessRule 22 43 0 230021 230581 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk24 := witnessRule 22 43 32 230582 230896 23 2115
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk25 := witnessRule 22 42 0 240020 240519 32 3240
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk26 := witnessRule 22 42 32 240520 240896 27 2477
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk27 := witnessRule 22 41 0 250019 250458 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk28 := witnessRule 22 41 32 250515 250833 29 2661
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk29 := witnessRule 22 40 0 260018 260453 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk30 := witnessRule 22 40 32 260454 260832 32 2906
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk31 := witnessRule 22 39 0 270017 270393 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk32 := witnessRule 22 39 32 270394 270768 32 2902
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk33 := witnessRule 22 39 64 270769 270832 2 156
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk34 := witnessRule 22 38 0 280016 280389 32 3172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk35 := witnessRule 22 38 32 280390 280704 32 2900
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk36 := witnessRule 22 38 64 280705 280769 4 314
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk37 := witnessRule 22 37 0 290015 290330 32 3140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk38 := witnessRule 22 37 32 290331 290642 32 2890
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk39 := witnessRule 22 37 64 290643 290768 5 387
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk40 := witnessRule 22 36 0 300014 300326 32 3128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk41 := witnessRule 22 36 32 300327 300580 32 2869
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk42 := witnessRule 22 36 64 300640 300768 7 540
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk43 := witnessRule 22 35 0 310013 310323 32 3096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk44 := witnessRule 22 35 32 310324 310578 32 2852
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk45 := witnessRule 22 35 64 310579 310705 7 527
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk46 := witnessRule 22 34 0 320012 320265 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk47 := witnessRule 22 34 32 320266 320517 32 2821
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk48 := witnessRule 22 34 64 320576 320704 8 605
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk49 := witnessRule 22 33 0 330011 330262 32 3060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk50 := witnessRule 22 33 32 330263 330515 32 2776
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk51 := witnessRule 22 33 64 330516 330704 8 584
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk52 := witnessRule 22 32 0 340010 340259 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk53 := witnessRule 22 32 32 340260 340513 32 2756
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk54 := witnessRule 22 32 64 340514 340641 8 574
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk55 := witnessRule 22 31 0 350009 350203 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk56 := witnessRule 22 31 32 350257 350512 32 2725
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk57 := witnessRule 22 31 64 350513 350640 7 494
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk58 := witnessRule 22 30 0 360008 360200 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk59 := witnessRule 22 30 32 360201 360452 32 2653
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk60 := witnessRule 22 30 64 360512 360640 7 484
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk61 := witnessRule 22 29 0 370007 370198 32 2964
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk62 := witnessRule 22 29 32 370199 370452 32 2559
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk63 := witnessRule 22 29 64 370512 370577 5 338
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk64 := witnessRule 22 28 0 380006 380195 32 2932
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk65 := witnessRule 22 28 32 380196 380451 32 2504
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk66 := witnessRule 22 28 64 380512 380576 4 262
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk67 := witnessRule 22 27 0 390005 390194 32 2896
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk68 := witnessRule 22 27 32 390195 390512 32 2414
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk69 := witnessRule 22 27 64 390513 390576 2 124
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk70 := witnessRule 22 26 0 400004 400192 32 2836
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk71 := witnessRule 22 26 32 400193 400513 32 2358
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk72 := witnessRule 22 25 0 410003 410192 32 2792
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk73 := witnessRule 22 25 32 410193 410512 29 2065
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk74 := witnessRule 22 24 0 420002 420137 32 2724
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk75 := witnessRule 22 24 32 420192 420512 27 1877
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk76 := witnessRule 22 23 0 430001 430192 32 2668
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk77 := witnessRule 22 23 32 430193 430449 23 1527
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk78 := witnessRule 22 22 0 440000 440192 32 2588
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk79 := witnessRule 22 22 32 440193 440448 20 1282
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk80 := witnessRule 22 21 0 450000 450194 32 2492
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk81 := witnessRule 22 21 32 450195 450448 16 960
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk82 := witnessRule 22 20 0 460000 460195 32 2372
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk83 := witnessRule 22 20 32 460196 460385 12 690
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk84 := witnessRule 22 19 0 470000 470197 32 2245
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk85 := witnessRule 22 19 32 470256 470384 8 445
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk86 := witnessRule 22 18 0 480000 480257 32 2134
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk87 := witnessRule 22 18 32 480258 480384 5 257
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk88 := witnessRule 22 17 0 490000 490320 32 2013
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk89 := witnessRule 22 17 32 490321 490321 1 48
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk90 := witnessRule 22 16 0 500000 500320 30 1800
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk91 := witnessRule 22 15 0 510000 510320 27 1553
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk92 := witnessRule 22 14 0 520000 520257 24 1326
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk93 := witnessRule 22 13 0 530000 530256 21 1113
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk94 := witnessRule 22 12 0 540000 540256 19 957
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk95 := witnessRule 22 11 0 550000 550193 16 774
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk96 := witnessRule 22 10 0 560000 560192 14 644
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk97 := witnessRule 22 9 0 570000 570192 12 524
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk98 := witnessRule 22 8 0 580000 580129 10 416
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk99 := witnessRule 22 7 0 590000 590128 8 317
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk100 := witnessRule 22 6 0 600000 600128 7 260
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk101 := witnessRule 22 5 0 610000 610065 5 178
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk102 := witnessRule 22 4 0 620000 620064 4 134
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk103 := witnessRule 22 3 0 630000 630064 3 94
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk104 := witnessRule 22 2 0 640000 640001 2 59
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk105 := witnessRule 22 1 0 650000 650000 1 28
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt22_chunk106 := witnessRule 22 0 0 660000 660000 1 25
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt22_chunks : List (Chunk 22) := [pack_E6970Receipt22_chunk0, pack_E6970Receipt22_chunk1, pack_E6970Receipt22_chunk2, pack_E6970Receipt22_chunk3, pack_E6970Receipt22_chunk4, pack_E6970Receipt22_chunk5, pack_E6970Receipt22_chunk6, pack_E6970Receipt22_chunk7, pack_E6970Receipt22_chunk8, pack_E6970Receipt22_chunk9, pack_E6970Receipt22_chunk10, pack_E6970Receipt22_chunk11, pack_E6970Receipt22_chunk12, pack_E6970Receipt22_chunk13, pack_E6970Receipt22_chunk14, pack_E6970Receipt22_chunk15, pack_E6970Receipt22_chunk16, pack_E6970Receipt22_chunk17, pack_E6970Receipt22_chunk18, pack_E6970Receipt22_chunk19, pack_E6970Receipt22_chunk20, pack_E6970Receipt22_chunk21, pack_E6970Receipt22_chunk22, pack_E6970Receipt22_chunk23, pack_E6970Receipt22_chunk24, pack_E6970Receipt22_chunk25, pack_E6970Receipt22_chunk26, pack_E6970Receipt22_chunk27, pack_E6970Receipt22_chunk28, pack_E6970Receipt22_chunk29, pack_E6970Receipt22_chunk30, pack_E6970Receipt22_chunk31, pack_E6970Receipt22_chunk32, pack_E6970Receipt22_chunk33, pack_E6970Receipt22_chunk34, pack_E6970Receipt22_chunk35, pack_E6970Receipt22_chunk36, pack_E6970Receipt22_chunk37, pack_E6970Receipt22_chunk38, pack_E6970Receipt22_chunk39, pack_E6970Receipt22_chunk40, pack_E6970Receipt22_chunk41, pack_E6970Receipt22_chunk42, pack_E6970Receipt22_chunk43, pack_E6970Receipt22_chunk44, pack_E6970Receipt22_chunk45, pack_E6970Receipt22_chunk46, pack_E6970Receipt22_chunk47, pack_E6970Receipt22_chunk48, pack_E6970Receipt22_chunk49, pack_E6970Receipt22_chunk50, pack_E6970Receipt22_chunk51, pack_E6970Receipt22_chunk52, pack_E6970Receipt22_chunk53, pack_E6970Receipt22_chunk54, pack_E6970Receipt22_chunk55, pack_E6970Receipt22_chunk56, pack_E6970Receipt22_chunk57, pack_E6970Receipt22_chunk58, pack_E6970Receipt22_chunk59, pack_E6970Receipt22_chunk60, pack_E6970Receipt22_chunk61, pack_E6970Receipt22_chunk62, pack_E6970Receipt22_chunk63, pack_E6970Receipt22_chunk64, pack_E6970Receipt22_chunk65, pack_E6970Receipt22_chunk66, pack_E6970Receipt22_chunk67, pack_E6970Receipt22_chunk68, pack_E6970Receipt22_chunk69, pack_E6970Receipt22_chunk70, pack_E6970Receipt22_chunk71, pack_E6970Receipt22_chunk72, pack_E6970Receipt22_chunk73, pack_E6970Receipt22_chunk74, pack_E6970Receipt22_chunk75, pack_E6970Receipt22_chunk76, pack_E6970Receipt22_chunk77, pack_E6970Receipt22_chunk78, pack_E6970Receipt22_chunk79, pack_E6970Receipt22_chunk80, pack_E6970Receipt22_chunk81, pack_E6970Receipt22_chunk82, pack_E6970Receipt22_chunk83, pack_E6970Receipt22_chunk84, pack_E6970Receipt22_chunk85, pack_E6970Receipt22_chunk86, pack_E6970Receipt22_chunk87, pack_E6970Receipt22_chunk88, pack_E6970Receipt22_chunk89, pack_E6970Receipt22_chunk90, pack_E6970Receipt22_chunk91, pack_E6970Receipt22_chunk92, pack_E6970Receipt22_chunk93, pack_E6970Receipt22_chunk94, pack_E6970Receipt22_chunk95, pack_E6970Receipt22_chunk96, pack_E6970Receipt22_chunk97, pack_E6970Receipt22_chunk98, pack_E6970Receipt22_chunk99, pack_E6970Receipt22_chunk100, pack_E6970Receipt22_chunk101, pack_E6970Receipt22_chunk102, pack_E6970Receipt22_chunk103, pack_E6970Receipt22_chunk104, pack_E6970Receipt22_chunk105, pack_E6970Receipt22_chunk106]
def rows22 := rowsFrom pack_E6970Receipt22_chunks
theorem good22 : ∀ r ∈ rows22, good 22 r = true := rowsFrom_good pack_E6970Receipt22_chunks
theorem sorted22 : rows22.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt22_chunks 0 (by decide +kernel)).1
theorem mass22 (i : Fin 61) :
    bandCount 22 (i.val : ℤ) 60 16 ≤ (rows22.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt22_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 22 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt22_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total22 : (rows22.map (price 22)).sum = 190740 :=
  (total_eq pack_E6970Receipt22_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt22

section Pack_E6970Receipt23

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt23_chunk0 := witnessRule 23 60 0 90905 91030 4 427
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk1 := witnessRule 23 59 0 100842 101029 6 637
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk2 := witnessRule 23 58 0 110779 111029 9 948
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk3 := witnessRule 23 57 0 120716 121028 12 1257
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk4 := witnessRule 23 56 0 130653 131028 16 1665
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk5 := witnessRule 23 55 0 140590 141027 20 2070
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk6 := witnessRule 23 54 0 150527 151027 24 2464
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk7 := witnessRule 23 53 0 160464 161026 28 2857
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk8 := witnessRule 23 52 0 170401 171026 32 3239
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk9 := witnessRule 23 51 0 180338 180961 32 3251
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk10 := witnessRule 23 51 32 180962 181025 4 373
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk11 := witnessRule 23 50 0 190275 190897 32 3253
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk12 := witnessRule 23 50 32 190898 191025 8 744
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk13 := witnessRule 23 49 0 200212 200833 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk14 := witnessRule 23 49 32 200834 201024 12 1116
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk15 := witnessRule 23 48 0 210149 210770 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk16 := witnessRule 23 48 32 210771 211024 16 1484
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk17 := witnessRule 23 47 0 220086 220707 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk18 := witnessRule 23 47 32 220708 220961 20 1860
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk19 := witnessRule 23 46 0 230023 230644 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk20 := witnessRule 23 46 32 230645 230960 24 2223
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk21 := witnessRule 23 45 0 240022 240582 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk22 := witnessRule 23 45 32 240583 240960 28 2584
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk23 := witnessRule 23 44 0 250021 250520 32 3240
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk24 := witnessRule 23 44 32 250521 250897 31 2849
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk25 := witnessRule 23 43 0 260020 260459 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk26 := witnessRule 23 43 32 260516 260833 32 2964
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk27 := witnessRule 23 43 64 260834 260896 2 161
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk28 := witnessRule 23 42 0 270019 270454 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk29 := witnessRule 23 42 32 270455 270769 32 2951
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk30 := witnessRule 23 42 64 270770 270896 5 404
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk31 := witnessRule 23 41 0 280018 280394 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk32 := witnessRule 23 41 32 280395 280706 32 2958
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk33 := witnessRule 23 41 64 280707 280833 7 563
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk34 := witnessRule 23 40 0 290017 290390 32 3172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk35 := witnessRule 23 40 32 290391 290644 32 2937
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk36 := witnessRule 23 40 64 290645 290832 9 721
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk37 := witnessRule 23 39 0 300016 300331 32 3140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk38 := witnessRule 23 39 32 300332 300640 32 2937
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk39 := witnessRule 23 39 64 300641 300832 11 876
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk40 := witnessRule 23 38 0 310015 310327 32 3128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk41 := witnessRule 23 38 32 310328 310579 32 2912
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk42 := witnessRule 23 38 64 310580 310769 12 940
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk43 := witnessRule 23 37 0 320014 320324 32 3096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk44 := witnessRule 23 37 32 320325 320576 32 2900
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk45 := witnessRule 23 37 64 320577 320768 13 1010
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk46 := witnessRule 23 36 0 330013 330266 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk47 := witnessRule 23 36 32 330267 330516 32 2872
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk48 := witnessRule 23 36 64 330517 330768 14 1066
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk49 := witnessRule 23 35 0 340012 340263 32 3060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk50 := witnessRule 23 35 32 340264 340513 32 2836
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk51 := witnessRule 23 35 64 340514 340705 14 1054
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk52 := witnessRule 23 34 0 350011 350260 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk53 := witnessRule 23 34 32 350261 350454 32 2792
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk54 := witnessRule 23 34 64 350512 350704 14 1045
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk55 := witnessRule 23 33 0 360010 360204 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk56 := witnessRule 23 33 32 360258 360452 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk57 := witnessRule 23 33 64 360453 360704 14 1010
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk58 := witnessRule 23 32 0 370009 370201 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk59 := witnessRule 23 32 32 370202 370450 32 2724
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk60 := witnessRule 23 32 64 370451 370641 13 919
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk61 := witnessRule 23 31 0 380008 380199 32 2964
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk62 := witnessRule 23 31 32 380200 380449 32 2660
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk63 := witnessRule 23 31 64 380450 380640 12 827
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk64 := witnessRule 23 30 0 390007 390196 32 2932
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk65 := witnessRule 23 30 32 390197 390448 32 2589
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk66 := witnessRule 23 30 64 390449 390640 11 744
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk67 := witnessRule 23 29 0 400006 400194 32 2908
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk68 := witnessRule 23 29 32 400195 400448 32 2525
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk69 := witnessRule 23 29 64 400449 400577 9 590
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk70 := witnessRule 23 28 0 410005 410192 32 2840
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk71 := witnessRule 23 28 32 410193 410448 32 2471
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk72 := witnessRule 23 28 64 410449 410576 7 445
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk73 := witnessRule 23 27 0 420004 420138 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk74 := witnessRule 23 27 32 420192 420449 32 2395
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk75 := witnessRule 23 27 64 420450 420576 5 304
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk76 := witnessRule 23 26 0 430003 430137 32 2764
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk77 := witnessRule 23 26 32 430138 430450 32 2280
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk78 := witnessRule 23 26 64 430512 430513 2 118
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk79 := witnessRule 23 25 0 440002 440136 32 2724
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk80 := witnessRule 23 25 32 440137 440512 31 2112
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk81 := witnessRule 23 24 0 450001 450136 32 2644
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk82 := witnessRule 23 24 32 450137 450512 28 1840
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk83 := witnessRule 23 23 0 460000 460136 32 2564
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk84 := witnessRule 23 23 32 460192 460449 24 1528
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk85 := witnessRule 23 22 0 470000 470192 32 2460
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk86 := witnessRule 23 22 32 470193 470448 20 1211
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk87 := witnessRule 23 21 0 480000 480194 32 2364
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk88 := witnessRule 23 21 32 480195 480448 16 908
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk89 := witnessRule 23 20 0 490000 490195 32 2244
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk90 := witnessRule 23 20 32 490196 490385 12 652
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk91 := witnessRule 23 19 0 500000 500197 32 2119
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk92 := witnessRule 23 19 32 500256 500384 8 420
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk93 := witnessRule 23 18 0 510000 510257 32 2011
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk94 := witnessRule 23 18 32 510258 510384 5 244
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk95 := witnessRule 23 17 0 520000 520320 32 1893
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk96 := witnessRule 23 17 32 520321 520321 1 46
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk97 := witnessRule 23 16 0 530000 530320 30 1689
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk98 := witnessRule 23 15 0 540000 540320 27 1457
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk99 := witnessRule 23 14 0 550000 550257 24 1240
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk100 := witnessRule 23 13 0 560000 560256 21 1038
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk101 := witnessRule 23 12 0 570000 570256 19 893
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk102 := witnessRule 23 11 0 580000 580193 16 720
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk103 := witnessRule 23 10 0 590000 590192 14 597
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk104 := witnessRule 23 9 0 600000 600192 12 487
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk105 := witnessRule 23 8 0 610000 610129 10 385
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk106 := witnessRule 23 7 0 620000 620128 8 292
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk107 := witnessRule 23 6 0 630000 630128 7 241
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk108 := witnessRule 23 5 0 640000 640065 5 164
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk109 := witnessRule 23 4 0 650000 650064 4 122
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk110 := witnessRule 23 3 0 660000 660064 3 87
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk111 := witnessRule 23 2 0 670000 670001 2 54
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk112 := witnessRule 23 1 0 680000 680000 1 25
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt23_chunk113 := witnessRule 23 0 0 690000 690000 1 24
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt23_chunks : List (Chunk 23) := [pack_E6970Receipt23_chunk0, pack_E6970Receipt23_chunk1, pack_E6970Receipt23_chunk2, pack_E6970Receipt23_chunk3, pack_E6970Receipt23_chunk4, pack_E6970Receipt23_chunk5, pack_E6970Receipt23_chunk6, pack_E6970Receipt23_chunk7, pack_E6970Receipt23_chunk8, pack_E6970Receipt23_chunk9, pack_E6970Receipt23_chunk10, pack_E6970Receipt23_chunk11, pack_E6970Receipt23_chunk12, pack_E6970Receipt23_chunk13, pack_E6970Receipt23_chunk14, pack_E6970Receipt23_chunk15, pack_E6970Receipt23_chunk16, pack_E6970Receipt23_chunk17, pack_E6970Receipt23_chunk18, pack_E6970Receipt23_chunk19, pack_E6970Receipt23_chunk20, pack_E6970Receipt23_chunk21, pack_E6970Receipt23_chunk22, pack_E6970Receipt23_chunk23, pack_E6970Receipt23_chunk24, pack_E6970Receipt23_chunk25, pack_E6970Receipt23_chunk26, pack_E6970Receipt23_chunk27, pack_E6970Receipt23_chunk28, pack_E6970Receipt23_chunk29, pack_E6970Receipt23_chunk30, pack_E6970Receipt23_chunk31, pack_E6970Receipt23_chunk32, pack_E6970Receipt23_chunk33, pack_E6970Receipt23_chunk34, pack_E6970Receipt23_chunk35, pack_E6970Receipt23_chunk36, pack_E6970Receipt23_chunk37, pack_E6970Receipt23_chunk38, pack_E6970Receipt23_chunk39, pack_E6970Receipt23_chunk40, pack_E6970Receipt23_chunk41, pack_E6970Receipt23_chunk42, pack_E6970Receipt23_chunk43, pack_E6970Receipt23_chunk44, pack_E6970Receipt23_chunk45, pack_E6970Receipt23_chunk46, pack_E6970Receipt23_chunk47, pack_E6970Receipt23_chunk48, pack_E6970Receipt23_chunk49, pack_E6970Receipt23_chunk50, pack_E6970Receipt23_chunk51, pack_E6970Receipt23_chunk52, pack_E6970Receipt23_chunk53, pack_E6970Receipt23_chunk54, pack_E6970Receipt23_chunk55, pack_E6970Receipt23_chunk56, pack_E6970Receipt23_chunk57, pack_E6970Receipt23_chunk58, pack_E6970Receipt23_chunk59, pack_E6970Receipt23_chunk60, pack_E6970Receipt23_chunk61, pack_E6970Receipt23_chunk62, pack_E6970Receipt23_chunk63, pack_E6970Receipt23_chunk64, pack_E6970Receipt23_chunk65, pack_E6970Receipt23_chunk66, pack_E6970Receipt23_chunk67, pack_E6970Receipt23_chunk68, pack_E6970Receipt23_chunk69, pack_E6970Receipt23_chunk70, pack_E6970Receipt23_chunk71, pack_E6970Receipt23_chunk72, pack_E6970Receipt23_chunk73, pack_E6970Receipt23_chunk74, pack_E6970Receipt23_chunk75, pack_E6970Receipt23_chunk76, pack_E6970Receipt23_chunk77, pack_E6970Receipt23_chunk78, pack_E6970Receipt23_chunk79, pack_E6970Receipt23_chunk80, pack_E6970Receipt23_chunk81, pack_E6970Receipt23_chunk82, pack_E6970Receipt23_chunk83, pack_E6970Receipt23_chunk84, pack_E6970Receipt23_chunk85, pack_E6970Receipt23_chunk86, pack_E6970Receipt23_chunk87, pack_E6970Receipt23_chunk88, pack_E6970Receipt23_chunk89, pack_E6970Receipt23_chunk90, pack_E6970Receipt23_chunk91, pack_E6970Receipt23_chunk92, pack_E6970Receipt23_chunk93, pack_E6970Receipt23_chunk94, pack_E6970Receipt23_chunk95, pack_E6970Receipt23_chunk96, pack_E6970Receipt23_chunk97, pack_E6970Receipt23_chunk98, pack_E6970Receipt23_chunk99, pack_E6970Receipt23_chunk100, pack_E6970Receipt23_chunk101, pack_E6970Receipt23_chunk102, pack_E6970Receipt23_chunk103, pack_E6970Receipt23_chunk104, pack_E6970Receipt23_chunk105, pack_E6970Receipt23_chunk106, pack_E6970Receipt23_chunk107, pack_E6970Receipt23_chunk108, pack_E6970Receipt23_chunk109, pack_E6970Receipt23_chunk110, pack_E6970Receipt23_chunk111, pack_E6970Receipt23_chunk112, pack_E6970Receipt23_chunk113]
def rows23 := rowsFrom pack_E6970Receipt23_chunks
theorem good23 : ∀ r ∈ rows23, good 23 r = true := rowsFrom_good pack_E6970Receipt23_chunks
theorem sorted23 : rows23.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt23_chunks 0 (by decide +kernel)).1
theorem mass23 (i : Fin 61) :
    bandCount 23 (i.val : ℤ) 60 16 ≤ (rows23.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt23_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 23 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt23_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total23 : (rows23.map (price 23)).sum = 211092 :=
  (total_eq pack_E6970Receipt23_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt23

section Pack_E6970Receipt24

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt24_chunk0 := witnessA6966Final 24 60 0 120780 121030 9 958
  0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk1 := witnessRule 24 59 0 130717 131029 12 1265
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk2 := witnessRule 24 58 0 140654 141029 16 1672
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk3 := witnessRule 24 57 0 150591 151028 20 2077
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk4 := witnessRule 24 56 0 160528 161028 25 2576
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk5 := witnessRule 24 55 0 170465 171027 29 2967
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk6 := witnessRule 24 54 0 180402 181025 32 3261
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk7 := witnessRule 24 54 32 181026 181027 2 191
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk8 := witnessRule 24 53 0 190339 190961 32 3258
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk9 := witnessRule 24 53 32 190962 191026 6 572
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk10 := witnessRule 24 52 0 200276 200897 32 3261
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk11 := witnessRule 24 52 32 200898 201026 11 1043
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk12 := witnessRule 24 51 0 210213 210834 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk13 := witnessRule 24 51 32 210835 211025 15 1413
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk14 := witnessRule 24 50 0 220150 220771 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk15 := witnessRule 24 50 32 220772 221025 20 1878
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk16 := witnessRule 24 49 0 230087 230708 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk17 := witnessRule 24 49 32 230709 231024 24 2241
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk18 := witnessRule 24 48 0 240024 240645 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk19 := witnessRule 24 48 32 240646 241024 29 2700
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk20 := witnessRule 24 47 0 250023 250583 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk21 := witnessRule 24 47 32 250584 250961 32 2959
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk22 := witnessRule 24 46 0 260022 260521 32 3240
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk23 := witnessRule 24 46 32 260522 260835 32 2981
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk24 := witnessRule 24 46 64 260896 260960 4 338
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk25 := witnessRule 24 45 0 270021 270460 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk26 := witnessRule 24 45 32 270517 270772 32 2993
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk27 := witnessRule 24 45 64 270832 270960 7 588
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk28 := witnessRule 24 44 0 280020 280455 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk29 := witnessRule 24 44 32 280456 280709 32 2984
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk30 := witnessRule 24 44 64 280768 280897 10 836
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk31 := witnessRule 24 43 0 290019 290395 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk32 := witnessRule 24 43 32 290396 290705 32 2985
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk33 := witnessRule 24 43 64 290706 290896 12 986
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk34 := witnessRule 24 42 0 300018 300391 32 3172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk35 := witnessRule 24 42 32 300392 300643 32 2980
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk36 := witnessRule 24 42 64 300644 300896 15 1221
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk37 := witnessRule 24 41 0 310017 310332 32 3140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk38 := witnessRule 24 41 32 310333 310583 32 2949
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk39 := witnessRule 24 41 64 310640 310833 16 1309
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk40 := witnessRule 24 40 0 320016 320328 32 3128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk41 := witnessRule 24 40 32 320329 320578 32 2948
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk42 := witnessRule 24 40 64 320579 320832 18 1441
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk43 := witnessRule 24 39 0 330015 330325 32 3096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk44 := witnessRule 24 39 32 330326 330519 32 2912
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk45 := witnessRule 24 39 64 330576 330832 19 1517
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk46 := witnessRule 24 38 0 340014 340267 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk47 := witnessRule 24 38 32 340268 340515 32 2916
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk48 := witnessRule 24 38 64 340516 340769 20 1554
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk49 := witnessRule 24 37 0 350013 350264 32 3060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk50 := witnessRule 24 37 32 350265 350512 32 2856
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk51 := witnessRule 24 37 64 350513 350768 20 1547
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk52 := witnessRule 24 36 0 360012 360261 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk53 := witnessRule 24 36 32 360262 360453 32 2852
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk54 := witnessRule 24 36 64 360454 360768 21 1587
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk55 := witnessRule 24 35 0 370011 370205 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk56 := witnessRule 24 35 32 370259 370451 32 2848
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk57 := witnessRule 24 35 64 370452 370705 20 1474
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk58 := witnessRule 24 34 0 380010 380202 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk59 := witnessRule 24 34 32 380203 380448 32 2772
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk60 := witnessRule 24 34 64 380449 380704 20 1467
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk61 := witnessRule 24 33 0 390009 390200 32 2964
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk62 := witnessRule 24 33 32 390201 390391 32 2696
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk63 := witnessRule 24 33 64 390448 390704 19 1365
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk64 := witnessRule 24 32 0 400008 400197 32 2932
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk65 := witnessRule 24 32 32 400198 400389 32 2676
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk66 := witnessRule 24 32 64 400390 400641 18 1248
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk67 := witnessRule 24 31 0 410007 410195 32 2908
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk68 := witnessRule 24 31 32 410196 410388 32 2604
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk69 := witnessRule 24 31 64 410389 410640 16 1079
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk70 := witnessRule 24 30 0 420006 420192 32 2844
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk71 := witnessRule 24 30 32 420193 420387 32 2584
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk72 := witnessRule 24 30 64 420388 420640 15 981
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk73 := witnessRule 24 29 0 430005 430139 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk74 := witnessRule 24 29 32 430192 430387 32 2501
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk75 := witnessRule 24 29 64 430388 430577 12 761
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk76 := witnessRule 24 28 0 440004 440137 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk77 := witnessRule 24 28 32 440138 440387 32 2390
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk78 := witnessRule 24 28 64 440388 440576 10 615
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk79 := witnessRule 24 27 0 450003 450136 32 2760
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk80 := witnessRule 24 27 32 450137 450388 32 2277
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk81 := witnessRule 24 27 64 450448 450576 7 420
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk82 := witnessRule 24 26 0 460002 460135 32 2720
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk83 := witnessRule 24 26 32 460136 460448 32 2177
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk84 := witnessRule 24 26 64 460449 460513 4 229
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk85 := witnessRule 24 25 0 470001 470135 32 2640
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk86 := witnessRule 24 25 32 470136 470512 32 2067
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk87 := witnessRule 24 24 0 480000 480135 32 2564
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk88 := witnessRule 24 24 32 480136 480512 29 1803
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk89 := witnessRule 24 23 0 490000 490136 32 2436
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk90 := witnessRule 24 23 32 490192 490449 24 1446
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk91 := witnessRule 24 22 0 500000 500192 32 2332
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk92 := witnessRule 24 22 32 500193 500448 20 1147
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk93 := witnessRule 24 21 0 510000 510194 32 2236
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk94 := witnessRule 24 21 32 510195 510448 16 860
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk95 := witnessRule 24 20 0 520000 520195 32 2117
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk96 := witnessRule 24 20 32 520196 520385 12 617
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk97 := witnessRule 24 19 0 530000 530197 32 1995
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk98 := witnessRule 24 19 32 530256 530384 8 400
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk99 := witnessRule 24 18 0 540000 540257 32 1890
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk100 := witnessRule 24 18 32 540258 540384 5 233
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk101 := witnessRule 24 17 0 550000 550320 32 1776
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk102 := witnessRule 24 17 32 550321 550321 1 45
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk103 := witnessRule 24 16 0 560000 560320 30 1585
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk104 := witnessRule 24 15 0 570000 570320 27 1365
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk105 := witnessRule 24 14 0 580000 580257 24 1158
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk106 := witnessRule 24 13 0 590000 590256 21 970
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk107 := witnessRule 24 12 0 600000 600256 19 833
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk108 := witnessRule 24 11 0 610000 610193 16 669
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk109 := witnessRule 24 10 0 620000 620192 14 556
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk110 := witnessRule 24 9 0 630000 630192 12 453
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk111 := witnessRule 24 8 0 640000 640129 10 356
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk112 := witnessRule 24 7 0 650000 650128 8 272
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk113 := witnessRule 24 6 0 660000 660128 7 224
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk114 := witnessRule 24 5 0 670000 670065 5 151
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk115 := witnessRule 24 4 0 680000 680064 4 114
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk116 := witnessRule 24 3 0 690000 690064 3 81
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk117 := witnessRule 24 2 0 700000 700001 2 50
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk118 := witnessRule 24 1 0 710000 710000 1 24
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt24_chunk119 := witnessRule 24 0 0 720000 720000 1 23
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt24_chunks : List (Chunk 24) := [pack_E6970Receipt24_chunk0, pack_E6970Receipt24_chunk1, pack_E6970Receipt24_chunk2, pack_E6970Receipt24_chunk3, pack_E6970Receipt24_chunk4, pack_E6970Receipt24_chunk5, pack_E6970Receipt24_chunk6, pack_E6970Receipt24_chunk7, pack_E6970Receipt24_chunk8, pack_E6970Receipt24_chunk9, pack_E6970Receipt24_chunk10, pack_E6970Receipt24_chunk11, pack_E6970Receipt24_chunk12, pack_E6970Receipt24_chunk13, pack_E6970Receipt24_chunk14, pack_E6970Receipt24_chunk15, pack_E6970Receipt24_chunk16, pack_E6970Receipt24_chunk17, pack_E6970Receipt24_chunk18, pack_E6970Receipt24_chunk19, pack_E6970Receipt24_chunk20, pack_E6970Receipt24_chunk21, pack_E6970Receipt24_chunk22, pack_E6970Receipt24_chunk23, pack_E6970Receipt24_chunk24, pack_E6970Receipt24_chunk25, pack_E6970Receipt24_chunk26, pack_E6970Receipt24_chunk27, pack_E6970Receipt24_chunk28, pack_E6970Receipt24_chunk29, pack_E6970Receipt24_chunk30, pack_E6970Receipt24_chunk31, pack_E6970Receipt24_chunk32, pack_E6970Receipt24_chunk33, pack_E6970Receipt24_chunk34, pack_E6970Receipt24_chunk35, pack_E6970Receipt24_chunk36, pack_E6970Receipt24_chunk37, pack_E6970Receipt24_chunk38, pack_E6970Receipt24_chunk39, pack_E6970Receipt24_chunk40, pack_E6970Receipt24_chunk41, pack_E6970Receipt24_chunk42, pack_E6970Receipt24_chunk43, pack_E6970Receipt24_chunk44, pack_E6970Receipt24_chunk45, pack_E6970Receipt24_chunk46, pack_E6970Receipt24_chunk47, pack_E6970Receipt24_chunk48, pack_E6970Receipt24_chunk49, pack_E6970Receipt24_chunk50, pack_E6970Receipt24_chunk51, pack_E6970Receipt24_chunk52, pack_E6970Receipt24_chunk53, pack_E6970Receipt24_chunk54, pack_E6970Receipt24_chunk55, pack_E6970Receipt24_chunk56, pack_E6970Receipt24_chunk57, pack_E6970Receipt24_chunk58, pack_E6970Receipt24_chunk59, pack_E6970Receipt24_chunk60, pack_E6970Receipt24_chunk61, pack_E6970Receipt24_chunk62, pack_E6970Receipt24_chunk63, pack_E6970Receipt24_chunk64, pack_E6970Receipt24_chunk65, pack_E6970Receipt24_chunk66, pack_E6970Receipt24_chunk67, pack_E6970Receipt24_chunk68, pack_E6970Receipt24_chunk69, pack_E6970Receipt24_chunk70, pack_E6970Receipt24_chunk71, pack_E6970Receipt24_chunk72, pack_E6970Receipt24_chunk73, pack_E6970Receipt24_chunk74, pack_E6970Receipt24_chunk75, pack_E6970Receipt24_chunk76, pack_E6970Receipt24_chunk77, pack_E6970Receipt24_chunk78, pack_E6970Receipt24_chunk79, pack_E6970Receipt24_chunk80, pack_E6970Receipt24_chunk81, pack_E6970Receipt24_chunk82, pack_E6970Receipt24_chunk83, pack_E6970Receipt24_chunk84, pack_E6970Receipt24_chunk85, pack_E6970Receipt24_chunk86, pack_E6970Receipt24_chunk87, pack_E6970Receipt24_chunk88, pack_E6970Receipt24_chunk89, pack_E6970Receipt24_chunk90, pack_E6970Receipt24_chunk91, pack_E6970Receipt24_chunk92, pack_E6970Receipt24_chunk93, pack_E6970Receipt24_chunk94, pack_E6970Receipt24_chunk95, pack_E6970Receipt24_chunk96, pack_E6970Receipt24_chunk97, pack_E6970Receipt24_chunk98, pack_E6970Receipt24_chunk99, pack_E6970Receipt24_chunk100, pack_E6970Receipt24_chunk101, pack_E6970Receipt24_chunk102, pack_E6970Receipt24_chunk103, pack_E6970Receipt24_chunk104, pack_E6970Receipt24_chunk105, pack_E6970Receipt24_chunk106, pack_E6970Receipt24_chunk107, pack_E6970Receipt24_chunk108, pack_E6970Receipt24_chunk109, pack_E6970Receipt24_chunk110, pack_E6970Receipt24_chunk111, pack_E6970Receipt24_chunk112, pack_E6970Receipt24_chunk113, pack_E6970Receipt24_chunk114, pack_E6970Receipt24_chunk115, pack_E6970Receipt24_chunk116, pack_E6970Receipt24_chunk117, pack_E6970Receipt24_chunk118, pack_E6970Receipt24_chunk119]
def rows24 := rowsFrom pack_E6970Receipt24_chunks
theorem good24 : ∀ r ∈ rows24, good 24 r = true := rowsFrom_good pack_E6970Receipt24_chunks
theorem sorted24 : rows24.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt24_chunks 0 (by decide +kernel)).1
theorem mass24 (i : Fin 61) :
    bandCount 24 (i.val : ℤ) 60 16 ≤ (rows24.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt24_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 24 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt24_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total24 : (rows24.map (price 24)).sum = 231736 :=
  (total_eq pack_E6970Receipt24_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt24

section Pack_E6970Receipt25

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt25_chunk0 := witnessA6966Final 25 60 0 150655 151030 16 1698
  0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk1 := witnessRule 25 59 0 160592 161029 20 2095
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk2 := witnessRule 25 58 0 170529 171029 25 2594
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk3 := witnessRule 25 57 0 180466 181028 30 3089
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk4 := witnessRule 25 56 0 190403 191025 32 3278
  0xefffffff 0xa11a (by decide +kernel)
private def pack_E6970Receipt25_chunk5 := witnessRule 25 56 32 191026 191028 3 293
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk6 := witnessRule 25 55 0 200340 200961 32 3273
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk7 := witnessRule 25 55 32 200962 201027 8 778
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk8 := witnessRule 25 54 0 210277 210898 32 3266
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk9 := witnessRule 25 54 32 210899 211027 13 1252
  0x1f7f 0xa1188b (by decide +kernel)
private def pack_E6970Receipt25_chunk10 := witnessRule 25 53 0 220214 220835 32 3263
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk11 := witnessRule 25 53 32 220836 221026 18 1724
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk12 := witnessRule 25 52 0 230151 230772 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk13 := witnessRule 25 52 32 230773 231026 23 2181
  0x7bffff 0xa1190b (by decide +kernel)
private def pack_E6970Receipt25_chunk14 := witnessRule 25 51 0 240088 240709 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk15 := witnessRule 25 51 32 240710 241025 28 2641
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk16 := witnessRule 25 50 0 250025 250646 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk17 := witnessRule 25 50 32 250647 251024 32 2998
  0xdfffffff 0xa1198b (by decide +kernel)
private def pack_E6970Receipt25_chunk18 := witnessRule 25 50 64 251025 251025 1 89
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk19 := witnessRule 25 49 0 260024 260584 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk20 := witnessRule 25 49 32 260585 260898 32 3007
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk21 := witnessRule 25 49 64 260899 261024 5 434
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk22 := witnessRule 25 48 0 270023 270522 32 3240
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk23 := witnessRule 25 48 32 270523 270834 32 3012
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk24 := witnessRule 25 48 64 270835 271024 9 772
  0x1bf 0xa11a0b (by decide +kernel)
private def pack_E6970Receipt25_chunk25 := witnessRule 25 47 0 280022 280461 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk26 := witnessRule 25 47 32 280518 280771 32 3033
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk27 := witnessRule 25 47 64 280772 280961 12 1022
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk28 := witnessRule 25 46 0 290021 290456 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk29 := witnessRule 25 46 32 290457 290709 32 3006
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk30 := witnessRule 25 46 64 290710 290960 15 1273
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk31 := witnessRule 25 45 0 300020 300396 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk32 := witnessRule 25 45 32 300397 300704 32 3005
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk33 := witnessRule 25 45 64 300705 300960 18 1515
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk34 := witnessRule 25 44 0 310019 310392 32 3172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk35 := witnessRule 25 44 32 310393 310643 32 2996
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk36 := witnessRule 25 44 64 310644 310897 20 1657
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk37 := witnessRule 25 43 0 320018 320333 32 3140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk38 := witnessRule 25 43 32 320334 320583 32 2980
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk39 := witnessRule 25 43 64 320584 320896 22 1823
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk40 := witnessRule 25 42 0 330017 330329 32 3128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk41 := witnessRule 25 42 32 330330 330578 32 2960
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk42 := witnessRule 25 42 64 330579 330896 24 1953
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk43 := witnessRule 25 41 0 340016 340326 32 3096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk44 := witnessRule 25 41 32 340327 340519 32 2944
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk45 := witnessRule 25 41 64 340520 340833 25 2024
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk46 := witnessRule 25 40 0 350015 350268 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk47 := witnessRule 25 40 32 350269 350515 32 2932
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk48 := witnessRule 25 40 64 350516 350832 26 2059
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk49 := witnessRule 25 39 0 360014 360265 32 3060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk50 := witnessRule 25 39 32 360266 360457 32 2868
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk51 := witnessRule 25 39 64 360512 360832 27 2142
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk52 := witnessRule 25 38 0 370013 370262 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk53 := witnessRule 25 38 32 370263 370453 32 2876
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk54 := witnessRule 25 38 64 370454 370769 27 2078
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk55 := witnessRule 25 37 0 380012 380206 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk56 := witnessRule 25 37 32 380260 380450 32 2884
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk57 := witnessRule 25 37 64 380451 380768 27 2042
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk58 := witnessRule 25 36 0 390011 390203 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk59 := witnessRule 25 36 32 390204 390393 32 2784
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk60 := witnessRule 25 36 64 390448 390768 27 2034
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk61 := witnessRule 25 35 0 400010 400201 32 2964
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk62 := witnessRule 25 35 32 400202 400390 32 2764
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk63 := witnessRule 25 35 64 400391 400705 26 1895
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk64 := witnessRule 25 34 0 410009 410198 32 2932
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk65 := witnessRule 25 34 32 410199 410388 32 2728
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk66 := witnessRule 25 34 64 410389 410704 25 1772
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk67 := witnessRule 25 33 0 420008 420196 32 2908
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk68 := witnessRule 25 33 32 420197 420386 32 2676
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk69 := witnessRule 25 33 64 420387 420704 24 1665
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk70 := witnessRule 25 32 0 430007 430193 32 2844
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk71 := witnessRule 25 32 32 430194 430385 32 2644
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk72 := witnessRule 25 32 64 430386 430641 22 1491
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk73 := witnessRule 25 31 0 440006 440140 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk74 := witnessRule 25 31 32 440192 440384 32 2589
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk75 := witnessRule 25 31 64 440385 440640 20 1328
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk76 := witnessRule 25 30 0 450005 450138 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk77 := witnessRule 25 30 32 450139 450384 32 2477
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk78 := witnessRule 25 30 64 450385 450640 18 1154
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk79 := witnessRule 25 29 0 460004 460136 32 2796
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk80 := witnessRule 25 29 32 460137 460384 32 2375
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk81 := witnessRule 25 29 64 460385 460577 15 935
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk82 := witnessRule 25 28 0 470003 470135 32 2752
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk83 := witnessRule 25 28 32 470136 470385 32 2280
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk84 := witnessRule 25 28 64 470386 470576 12 717
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk85 := witnessRule 25 27 0 480002 480134 32 2708
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk86 := witnessRule 25 27 32 480135 480386 32 2182
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk87 := witnessRule 25 27 64 480387 480576 9 518
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk88 := witnessRule 25 26 0 490001 490134 32 2632
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk89 := witnessRule 25 26 32 490135 490388 32 2070
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk90 := witnessRule 25 26 64 490448 490513 5 282
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk91 := witnessRule 25 25 0 500000 500134 32 2556
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk92 := witnessRule 25 25 32 500135 500450 32 1969
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk93 := witnessRule 25 25 64 500512 500512 1 55
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk94 := witnessRule 25 24 0 510000 510135 32 2436
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk95 := witnessRule 25 24 32 510136 510512 29 1708
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk96 := witnessRule 25 23 0 520000 520136 32 2308
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk97 := witnessRule 25 23 32 520192 520449 24 1373
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk98 := witnessRule 25 22 0 530000 530192 32 2205
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk99 := witnessRule 25 22 32 530193 530448 20 1088
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk100 := witnessRule 25 21 0 540000 540194 32 2109
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk101 := witnessRule 25 21 32 540195 540448 16 816
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk102 := witnessRule 25 20 0 550000 550195 32 1992
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk103 := witnessRule 25 20 32 550196 550385 12 589
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk104 := witnessRule 25 19 0 560000 560197 32 1875
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk105 := witnessRule 25 19 32 560256 560384 8 382
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk106 := witnessRule 25 18 0 570000 570257 32 1772
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk107 := witnessRule 25 18 32 570258 570384 5 224
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk108 := witnessRule 25 17 0 580000 580320 32 1668
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk109 := witnessRule 25 17 32 580321 580321 1 44
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk110 := witnessRule 25 16 0 590000 590320 30 1487
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk111 := witnessRule 25 15 0 600000 600320 27 1278
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk112 := witnessRule 25 14 0 610000 610257 24 1085
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk113 := witnessRule 25 13 0 620000 620256 21 907
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk114 := witnessRule 25 12 0 630000 630256 19 777
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk115 := witnessRule 25 11 0 640000 640193 16 626
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk116 := witnessRule 25 10 0 650000 650192 14 519
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk117 := witnessRule 25 9 0 660000 660192 12 422
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk118 := witnessRule 25 8 0 670000 670129 10 334
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk119 := witnessRule 25 7 0 680000 680128 8 254
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk120 := witnessRule 25 6 0 690000 690128 7 209
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk121 := witnessRule 25 5 0 700000 700065 5 142
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk122 := witnessRule 25 4 0 710000 710064 4 107
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk123 := witnessRule 25 3 0 720000 720064 3 76
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk124 := witnessRule 25 2 0 730000 730001 2 48
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk125 := witnessRule 25 1 0 740000 740000 1 23
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt25_chunk126 := witnessRule 25 0 0 750000 750000 1 22
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt25_chunks : List (Chunk 25) := [pack_E6970Receipt25_chunk0, pack_E6970Receipt25_chunk1, pack_E6970Receipt25_chunk2, pack_E6970Receipt25_chunk3, pack_E6970Receipt25_chunk4, pack_E6970Receipt25_chunk5, pack_E6970Receipt25_chunk6, pack_E6970Receipt25_chunk7, pack_E6970Receipt25_chunk8, pack_E6970Receipt25_chunk9, pack_E6970Receipt25_chunk10, pack_E6970Receipt25_chunk11, pack_E6970Receipt25_chunk12, pack_E6970Receipt25_chunk13, pack_E6970Receipt25_chunk14, pack_E6970Receipt25_chunk15, pack_E6970Receipt25_chunk16, pack_E6970Receipt25_chunk17, pack_E6970Receipt25_chunk18, pack_E6970Receipt25_chunk19, pack_E6970Receipt25_chunk20, pack_E6970Receipt25_chunk21, pack_E6970Receipt25_chunk22, pack_E6970Receipt25_chunk23, pack_E6970Receipt25_chunk24, pack_E6970Receipt25_chunk25, pack_E6970Receipt25_chunk26, pack_E6970Receipt25_chunk27, pack_E6970Receipt25_chunk28, pack_E6970Receipt25_chunk29, pack_E6970Receipt25_chunk30, pack_E6970Receipt25_chunk31, pack_E6970Receipt25_chunk32, pack_E6970Receipt25_chunk33, pack_E6970Receipt25_chunk34, pack_E6970Receipt25_chunk35, pack_E6970Receipt25_chunk36, pack_E6970Receipt25_chunk37, pack_E6970Receipt25_chunk38, pack_E6970Receipt25_chunk39, pack_E6970Receipt25_chunk40, pack_E6970Receipt25_chunk41, pack_E6970Receipt25_chunk42, pack_E6970Receipt25_chunk43, pack_E6970Receipt25_chunk44, pack_E6970Receipt25_chunk45, pack_E6970Receipt25_chunk46, pack_E6970Receipt25_chunk47, pack_E6970Receipt25_chunk48, pack_E6970Receipt25_chunk49, pack_E6970Receipt25_chunk50, pack_E6970Receipt25_chunk51, pack_E6970Receipt25_chunk52, pack_E6970Receipt25_chunk53, pack_E6970Receipt25_chunk54, pack_E6970Receipt25_chunk55, pack_E6970Receipt25_chunk56, pack_E6970Receipt25_chunk57, pack_E6970Receipt25_chunk58, pack_E6970Receipt25_chunk59, pack_E6970Receipt25_chunk60, pack_E6970Receipt25_chunk61, pack_E6970Receipt25_chunk62, pack_E6970Receipt25_chunk63, pack_E6970Receipt25_chunk64, pack_E6970Receipt25_chunk65, pack_E6970Receipt25_chunk66, pack_E6970Receipt25_chunk67, pack_E6970Receipt25_chunk68, pack_E6970Receipt25_chunk69, pack_E6970Receipt25_chunk70, pack_E6970Receipt25_chunk71, pack_E6970Receipt25_chunk72, pack_E6970Receipt25_chunk73, pack_E6970Receipt25_chunk74, pack_E6970Receipt25_chunk75, pack_E6970Receipt25_chunk76, pack_E6970Receipt25_chunk77, pack_E6970Receipt25_chunk78, pack_E6970Receipt25_chunk79, pack_E6970Receipt25_chunk80, pack_E6970Receipt25_chunk81, pack_E6970Receipt25_chunk82, pack_E6970Receipt25_chunk83, pack_E6970Receipt25_chunk84, pack_E6970Receipt25_chunk85, pack_E6970Receipt25_chunk86, pack_E6970Receipt25_chunk87, pack_E6970Receipt25_chunk88, pack_E6970Receipt25_chunk89, pack_E6970Receipt25_chunk90, pack_E6970Receipt25_chunk91, pack_E6970Receipt25_chunk92, pack_E6970Receipt25_chunk93, pack_E6970Receipt25_chunk94, pack_E6970Receipt25_chunk95, pack_E6970Receipt25_chunk96, pack_E6970Receipt25_chunk97, pack_E6970Receipt25_chunk98, pack_E6970Receipt25_chunk99, pack_E6970Receipt25_chunk100, pack_E6970Receipt25_chunk101, pack_E6970Receipt25_chunk102, pack_E6970Receipt25_chunk103, pack_E6970Receipt25_chunk104, pack_E6970Receipt25_chunk105, pack_E6970Receipt25_chunk106, pack_E6970Receipt25_chunk107, pack_E6970Receipt25_chunk108, pack_E6970Receipt25_chunk109, pack_E6970Receipt25_chunk110, pack_E6970Receipt25_chunk111, pack_E6970Receipt25_chunk112, pack_E6970Receipt25_chunk113, pack_E6970Receipt25_chunk114, pack_E6970Receipt25_chunk115, pack_E6970Receipt25_chunk116, pack_E6970Receipt25_chunk117, pack_E6970Receipt25_chunk118, pack_E6970Receipt25_chunk119, pack_E6970Receipt25_chunk120, pack_E6970Receipt25_chunk121, pack_E6970Receipt25_chunk122, pack_E6970Receipt25_chunk123, pack_E6970Receipt25_chunk124, pack_E6970Receipt25_chunk125, pack_E6970Receipt25_chunk126]
def rows25 := rowsFrom pack_E6970Receipt25_chunks
theorem good25 : ∀ r ∈ rows25, good 25 r = true := rowsFrom_good pack_E6970Receipt25_chunks
theorem sorted25 : rows25.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt25_chunks 0 (by decide +kernel)).1
theorem mass25 (i : Fin 61) :
    bandCount 25 (i.val : ℤ) 60 16 ≤ (rows25.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt25_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 25 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt25_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total25 : (rows25.map (price 25)).sum = 252314 :=
  (total_eq pack_E6970Receipt25_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt25

section Pack_E6970Receipt26

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt26_chunk0 := witnessA6966Final 26 60 0 180530 181030 25 2645
  0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk1 := witnessRule 26 59 0 190467 191029 30 3125
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk2 := witnessRule 26 58 0 200404 201025 32 3310
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk3 := witnessRule 26 58 32 201026 201029 4 400
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk4 := witnessRule 26 57 0 210341 210962 32 3293
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk5 := witnessRule 26 57 32 210963 211028 9 891
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk6 := witnessRule 26 56 0 220278 220899 32 3281
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk7 := witnessRule 26 56 32 220900 221028 15 1473
  0x7efb 0xcc410a91a (by decide +kernel)
private def pack_E6970Receipt26_chunk8 := witnessRule 26 55 0 230215 230836 32 3272
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk9 := witnessRule 26 55 32 230837 231027 20 1941
  0xfdeff 0x50cd0a99a (by decide +kernel)
private def pack_E6970Receipt26_chunk10 := witnessRule 26 54 0 240152 240773 32 3266
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk11 := witnessRule 26 54 32 240774 241027 26 2502
  0x3effdfb 0x2a6620c58944d9291a (by decide +kernel)
private def pack_E6970Receipt26_chunk12 := witnessRule 26 53 0 250089 250710 32 3263
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk13 := witnessRule 26 53 32 250711 251026 31 2953
  0x7ddfffff 0x50cc459299a (by decide +kernel)
private def pack_E6970Receipt26_chunk14 := witnessRule 26 52 0 260026 260647 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk15 := witnessRule 26 52 32 260648 260961 32 3049
  0xffbf7fff 0x94508d9a91a (by decide +kernel)
private def pack_E6970Receipt26_chunk16 := witnessRule 26 52 64 260962 261026 5 449
  0x1e 0xa9988884 (by decide +kernel)
private def pack_E6970Receipt26_chunk17 := witnessRule 26 51 0 270025 270585 32 3252
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk18 := witnessRule 26 51 32 270586 270897 32 3040
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk19 := witnessRule 26 51 64 270898 271025 9 798
  0x1ed 0x50cc85929988b (by decide +kernel)
private def pack_E6970Receipt26_chunk20 := witnessRule 26 50 0 280024 280523 32 3240
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk21 := witnessRule 26 50 32 280524 280833 32 3044
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk22 := witnessRule 26 50 64 280834 281025 14 1232
  0x3bfb 0x54cc8442128a1188c (by decide +kernel)
private def pack_E6970Receipt26_chunk23 := witnessRule 26 49 0 290023 290462 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk24 := witnessRule 26 49 32 290519 290771 32 3053
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk25 := witnessRule 26 49 64 290772 291024 17 1476
  0x1d7ff 0x50ccc5929990b (by decide +kernel)
private def pack_E6970Receipt26_chunk26 := witnessRule 26 48 0 300022 300457 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk27 := witnessRule 26 48 32 300458 300709 32 3031
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk28 := witnessRule 26 48 64 300710 301024 21 1813
  0x1fefff 0x128a1190c (by decide +kernel)
private def pack_E6970Receipt26_chunk29 := witnessRule 26 47 0 310021 310397 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk30 := witnessRule 26 47 32 310398 310704 32 3011
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk31 := witnessRule 26 47 64 310705 310961 23 1975
  0x77ffff 0xa8a1198885 (by decide +kernel)
private def pack_E6970Receipt26_chunk32 := witnessRule 26 46 0 320020 320393 32 3172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk33 := witnessRule 26 46 32 320394 320643 32 3012
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk34 := witnessRule 26 46 64 320644 320960 26 2195
  0x3efffff 0x128a1198c (by decide +kernel)
private def pack_E6970Receipt26_chunk35 := witnessRule 26 45 0 330019 330334 32 3140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk36 := witnessRule 26 45 32 330335 330584 32 2980
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk37 := witnessRule 26 45 64 330585 330960 28 2360
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk38 := witnessRule 26 44 0 340018 340330 32 3128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk39 := witnessRule 26 44 32 340331 340578 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk40 := witnessRule 26 44 64 340579 340897 30 2490
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk41 := witnessRule 26 43 0 350017 350327 32 3096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk42 := witnessRule 26 43 32 350328 350520 32 2944
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk43 := witnessRule 26 43 64 350521 350896 31 2551
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk44 := witnessRule 26 42 0 360016 360269 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk45 := witnessRule 26 42 32 360270 360515 32 2948
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk46 := witnessRule 26 42 64 360516 360833 32 2584
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk47 := witnessRule 26 42 96 360896 360896 1 77
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk48 := witnessRule 26 41 0 370015 370266 32 3060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk49 := witnessRule 26 41 32 370267 370458 32 2868
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk50 := witnessRule 26 41 64 370512 370832 32 2591
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk51 := witnessRule 26 41 96 370833 370833 1 75
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk52 := witnessRule 26 40 0 380014 380263 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk53 := witnessRule 26 40 32 380264 380453 32 2900
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk54 := witnessRule 26 40 64 380454 380769 32 2516
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk55 := witnessRule 26 40 96 380770 380832 2 147
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk56 := witnessRule 26 39 0 390013 390207 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk57 := witnessRule 26 39 32 390261 390450 32 2896
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk58 := witnessRule 26 39 64 390451 390768 32 2475
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk59 := witnessRule 26 39 96 390769 390832 2 145
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk60 := witnessRule 26 38 0 400012 400204 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk61 := witnessRule 26 38 32 400205 400393 32 2824
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk62 := witnessRule 26 38 64 400394 400706 32 2459
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk63 := witnessRule 26 38 96 400768 400769 2 142
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk64 := witnessRule 26 37 0 410011 410202 32 2964
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk65 := witnessRule 26 37 32 410203 410390 32 2792
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk66 := witnessRule 26 37 64 410391 410706 32 2378
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk67 := witnessRule 26 37 96 410768 410768 1 70
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk68 := witnessRule 26 36 0 420010 420199 32 2932
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk69 := witnessRule 26 36 32 420200 420387 32 2772
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk70 := witnessRule 26 36 64 420388 420705 32 2328
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk71 := witnessRule 26 36 96 420768 420768 1 69
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk72 := witnessRule 26 35 0 430009 430197 32 2908
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk73 := witnessRule 26 35 32 430198 430385 32 2704
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk74 := witnessRule 26 35 64 430386 430705 31 2216
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk75 := witnessRule 26 34 0 440008 440194 32 2844
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk76 := witnessRule 26 34 32 440195 440329 32 2680
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk77 := witnessRule 26 34 64 440384 440704 30 2115
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk78 := witnessRule 26 33 0 450007 450141 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk79 := witnessRule 26 33 32 450193 450328 32 2644
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk80 := witnessRule 26 33 64 450329 450704 28 1910
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk81 := witnessRule 26 32 0 460006 460139 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk82 := witnessRule 26 32 32 460140 460326 32 2572
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk83 := witnessRule 26 32 64 460327 460641 26 1717
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk84 := witnessRule 26 31 0 470005 470137 32 2796
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk85 := witnessRule 26 31 32 470138 470326 32 2468
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk86 := witnessRule 26 31 64 470327 470640 23 1470
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk87 := witnessRule 26 30 0 480004 480135 32 2784
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk88 := witnessRule 26 30 32 480136 480325 32 2373
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk89 := witnessRule 26 30 64 480326 480640 21 1304
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk90 := witnessRule 26 29 0 490003 490134 32 2736
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk91 := witnessRule 26 29 32 490135 490326 32 2272
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk92 := witnessRule 26 29 64 490327 490577 17 1026
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk93 := witnessRule 26 28 0 500002 500133 32 2692
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk94 := witnessRule 26 28 32 500134 500326 32 2173
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk95 := witnessRule 26 28 64 500384 500576 14 822
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk96 := witnessRule 26 27 0 510001 510133 32 2616
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk97 := witnessRule 26 27 32 510134 510385 32 2079
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk98 := witnessRule 26 27 64 510386 510576 10 561
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk99 := witnessRule 26 26 0 520000 520133 32 2544
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk100 := witnessRule 26 26 32 520134 520387 32 1974
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk101 := witnessRule 26 26 64 520388 520513 6 327
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk102 := witnessRule 26 25 0 530000 530134 32 2428
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk103 := witnessRule 26 25 32 530135 530450 32 1866
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk104 := witnessRule 26 25 64 530512 530512 1 54
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk105 := witnessRule 26 24 0 540000 540135 32 2308
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk106 := witnessRule 26 24 32 540136 540512 29 1625
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk107 := witnessRule 26 23 0 550000 550136 32 2181
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk108 := witnessRule 26 23 32 550192 550449 24 1306
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk109 := witnessRule 26 22 0 560000 560192 32 2079
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk110 := witnessRule 26 22 32 560193 560448 20 1034
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk111 := witnessRule 26 21 0 570000 570194 32 1984
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk112 := witnessRule 26 21 32 570195 570448 16 782
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk113 := witnessRule 26 20 0 580000 580195 32 1871
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk114 := witnessRule 26 20 32 580196 580385 12 564
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk115 := witnessRule 26 19 0 590000 590197 32 1759
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk116 := witnessRule 26 19 32 590256 590384 8 366
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk117 := witnessRule 26 18 0 600000 600257 32 1662
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk118 := witnessRule 26 18 32 600258 600384 5 219
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk119 := witnessRule 26 17 0 610000 610320 32 1567
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk120 := witnessRule 26 17 32 610321 610321 1 43
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk121 := witnessRule 26 16 0 620000 620320 30 1395
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk122 := witnessRule 26 15 0 630000 630320 27 1202
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk123 := witnessRule 26 14 0 640000 640257 24 1018
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk124 := witnessRule 26 13 0 650000 650256 21 849
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk125 := witnessRule 26 12 0 660000 660256 19 731
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk126 := witnessRule 26 11 0 670000 670193 16 587
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk127 := witnessRule 26 10 0 680000 680192 14 486
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk128 := witnessRule 26 9 0 690000 690192 12 398
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk129 := witnessRule 26 8 0 700000 700129 10 314
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk130 := witnessRule 26 7 0 710000 710128 8 238
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk131 := witnessRule 26 6 0 720000 720128 7 198
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk132 := witnessRule 26 5 0 730000 730065 5 134
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk133 := witnessRule 26 4 0 740000 740064 4 101
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk134 := witnessRule 26 3 0 750000 750064 3 73
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk135 := witnessRule 26 2 0 760000 760001 2 46
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk136 := witnessRule 26 1 0 770000 770000 1 22
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt26_chunk137 := witnessRule 26 0 0 780000 780000 1 21
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt26_chunks : List (Chunk 26) := [pack_E6970Receipt26_chunk0, pack_E6970Receipt26_chunk1, pack_E6970Receipt26_chunk2, pack_E6970Receipt26_chunk3, pack_E6970Receipt26_chunk4, pack_E6970Receipt26_chunk5, pack_E6970Receipt26_chunk6, pack_E6970Receipt26_chunk7, pack_E6970Receipt26_chunk8, pack_E6970Receipt26_chunk9, pack_E6970Receipt26_chunk10, pack_E6970Receipt26_chunk11, pack_E6970Receipt26_chunk12, pack_E6970Receipt26_chunk13, pack_E6970Receipt26_chunk14, pack_E6970Receipt26_chunk15, pack_E6970Receipt26_chunk16, pack_E6970Receipt26_chunk17, pack_E6970Receipt26_chunk18, pack_E6970Receipt26_chunk19, pack_E6970Receipt26_chunk20, pack_E6970Receipt26_chunk21, pack_E6970Receipt26_chunk22, pack_E6970Receipt26_chunk23, pack_E6970Receipt26_chunk24, pack_E6970Receipt26_chunk25, pack_E6970Receipt26_chunk26, pack_E6970Receipt26_chunk27, pack_E6970Receipt26_chunk28, pack_E6970Receipt26_chunk29, pack_E6970Receipt26_chunk30, pack_E6970Receipt26_chunk31, pack_E6970Receipt26_chunk32, pack_E6970Receipt26_chunk33, pack_E6970Receipt26_chunk34, pack_E6970Receipt26_chunk35, pack_E6970Receipt26_chunk36, pack_E6970Receipt26_chunk37, pack_E6970Receipt26_chunk38, pack_E6970Receipt26_chunk39, pack_E6970Receipt26_chunk40, pack_E6970Receipt26_chunk41, pack_E6970Receipt26_chunk42, pack_E6970Receipt26_chunk43, pack_E6970Receipt26_chunk44, pack_E6970Receipt26_chunk45, pack_E6970Receipt26_chunk46, pack_E6970Receipt26_chunk47, pack_E6970Receipt26_chunk48, pack_E6970Receipt26_chunk49, pack_E6970Receipt26_chunk50, pack_E6970Receipt26_chunk51, pack_E6970Receipt26_chunk52, pack_E6970Receipt26_chunk53, pack_E6970Receipt26_chunk54, pack_E6970Receipt26_chunk55, pack_E6970Receipt26_chunk56, pack_E6970Receipt26_chunk57, pack_E6970Receipt26_chunk58, pack_E6970Receipt26_chunk59, pack_E6970Receipt26_chunk60, pack_E6970Receipt26_chunk61, pack_E6970Receipt26_chunk62, pack_E6970Receipt26_chunk63, pack_E6970Receipt26_chunk64, pack_E6970Receipt26_chunk65, pack_E6970Receipt26_chunk66, pack_E6970Receipt26_chunk67, pack_E6970Receipt26_chunk68, pack_E6970Receipt26_chunk69, pack_E6970Receipt26_chunk70, pack_E6970Receipt26_chunk71, pack_E6970Receipt26_chunk72, pack_E6970Receipt26_chunk73, pack_E6970Receipt26_chunk74, pack_E6970Receipt26_chunk75, pack_E6970Receipt26_chunk76, pack_E6970Receipt26_chunk77, pack_E6970Receipt26_chunk78, pack_E6970Receipt26_chunk79, pack_E6970Receipt26_chunk80, pack_E6970Receipt26_chunk81, pack_E6970Receipt26_chunk82, pack_E6970Receipt26_chunk83, pack_E6970Receipt26_chunk84, pack_E6970Receipt26_chunk85, pack_E6970Receipt26_chunk86, pack_E6970Receipt26_chunk87, pack_E6970Receipt26_chunk88, pack_E6970Receipt26_chunk89, pack_E6970Receipt26_chunk90, pack_E6970Receipt26_chunk91, pack_E6970Receipt26_chunk92, pack_E6970Receipt26_chunk93, pack_E6970Receipt26_chunk94, pack_E6970Receipt26_chunk95, pack_E6970Receipt26_chunk96, pack_E6970Receipt26_chunk97, pack_E6970Receipt26_chunk98, pack_E6970Receipt26_chunk99, pack_E6970Receipt26_chunk100, pack_E6970Receipt26_chunk101, pack_E6970Receipt26_chunk102, pack_E6970Receipt26_chunk103, pack_E6970Receipt26_chunk104, pack_E6970Receipt26_chunk105, pack_E6970Receipt26_chunk106, pack_E6970Receipt26_chunk107, pack_E6970Receipt26_chunk108, pack_E6970Receipt26_chunk109, pack_E6970Receipt26_chunk110, pack_E6970Receipt26_chunk111, pack_E6970Receipt26_chunk112, pack_E6970Receipt26_chunk113, pack_E6970Receipt26_chunk114, pack_E6970Receipt26_chunk115, pack_E6970Receipt26_chunk116, pack_E6970Receipt26_chunk117, pack_E6970Receipt26_chunk118, pack_E6970Receipt26_chunk119, pack_E6970Receipt26_chunk120, pack_E6970Receipt26_chunk121, pack_E6970Receipt26_chunk122, pack_E6970Receipt26_chunk123, pack_E6970Receipt26_chunk124, pack_E6970Receipt26_chunk125, pack_E6970Receipt26_chunk126, pack_E6970Receipt26_chunk127, pack_E6970Receipt26_chunk128, pack_E6970Receipt26_chunk129, pack_E6970Receipt26_chunk130, pack_E6970Receipt26_chunk131, pack_E6970Receipt26_chunk132, pack_E6970Receipt26_chunk133, pack_E6970Receipt26_chunk134, pack_E6970Receipt26_chunk135, pack_E6970Receipt26_chunk136, pack_E6970Receipt26_chunk137]
def rows26 := rowsFrom pack_E6970Receipt26_chunks
theorem good26 : ∀ r ∈ rows26, good 26 r = true := rowsFrom_good pack_E6970Receipt26_chunks
theorem sorted26 : rows26.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt26_chunks 0 (by decide +kernel)).1
theorem mass26 (i : Fin 61) :
    bandCount 26 (i.val : ℤ) 60 16 ≤ (rows26.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt26_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 26 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt26_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total26 : (rows26.map (price 26)).sum = 272484 :=
  (total_eq pack_E6970Receipt26_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt26

section Pack_E6970Receipt27

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt27_chunk0 := witnessA6966Final 27 60 0 210405 211026 32 3383
  0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk1 := witnessRule 27 60 32 211027 211030 4 414
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk2 := witnessRule 27 59 0 220342 220963 32 3332
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk3 := witnessRule 27 59 32 220964 221029 10 1021
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk4 := witnessRule 27 58 0 230279 230900 32 3308
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk5 := witnessRule 27 58 32 230901 231029 16 1602
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk6 := witnessRule 27 57 0 240216 240837 32 3293
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk7 := witnessRule 27 57 32 240838 241028 22 2176
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk8 := witnessRule 27 56 0 250153 250774 32 3281
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk9 := witnessRule 27 56 32 250775 251028 28 2733
  0xffffffb 0xa91a (by decide +kernel)
private def pack_E6970Receipt27_chunk10 := witnessRule 27 55 0 260090 260711 32 3272
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk11 := witnessRule 27 55 32 260712 261025 32 3101
  0xf7bfffff 0x10c410a99a (by decide +kernel)
private def pack_E6970Receipt27_chunk12 := witnessRule 27 55 64 261026 261027 2 187
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk13 := witnessRule 27 54 0 270027 270648 32 3266
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk14 := witnessRule 27 54 32 270649 270960 32 3089
  0xef7e7dfb 0x550d0b1289b262544a46858944d9291a (by decide +kernel)
private def pack_E6970Receipt27_chunk15 := witnessRule 27 54 64 270961 271027 8 736
  0xfd 0xa21a (by decide +kernel)
private def pack_E6970Receipt27_chunk16 := witnessRule 27 53 0 280026 280586 32 3255
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk17 := witnessRule 27 53 32 280587 280896 32 3079
  0xdfffffff 0xb1291b (by decide +kernel)
private def pack_E6970Receipt27_chunk18 := witnessRule 27 53 64 280897 281026 13 1183
  0x1f77 0x550c419299a (by decide +kernel)
private def pack_E6970Receipt27_chunk19 := witnessRule 27 52 0 290025 290524 32 3240
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk20 := witnessRule 27 52 32 290525 290833 32 3072
  0xefdfdfff 0x6a46858d44d9a91a (by decide +kernel)
private def pack_E6970Receipt27_chunk21 := witnessRule 27 52 64 290834 291026 18 1618
  0x3eef7 0x288622c950d1299883 (by decide +kernel)
private def pack_E6970Receipt27_chunk22 := witnessRule 27 51 0 300024 300463 32 3210
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk23 := witnessRule 27 51 32 300520 300771 32 3081
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk24 := witnessRule 27 51 64 300772 301025 22 1952
  0x3dbefb 0x1543111084a6640c9450cd9a99a (by decide +kernel)
private def pack_E6970Receipt27_chunk25 := witnessRule 27 50 0 310023 310458 32 3208
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk26 := witnessRule 27 50 32 310459 310710 32 3042
  0xfeffffff 0x2291a (by decide +kernel)
private def pack_E6970Receipt27_chunk27 := witnessRule 27 50 64 310711 311025 26 2291
  0x3dbbffd 0x14432164a8622cd4cc418b2289b (by decide +kernel)
private def pack_E6970Receipt27_chunk28 := witnessRule 27 49 0 320022 320398 32 3184
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk29 := witnessRule 27 49 32 320399 320704 32 3024
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk30 := witnessRule 27 49 64 320705 321024 29 2541
  0x1f7bdfff 0x4a66224109450cc462299a (by decide +kernel)
private def pack_E6970Receipt27_chunk31 := witnessRule 27 48 0 330021 330394 32 3172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk32 := witnessRule 27 48 32 330395 330644 32 3018
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk33 := witnessRule 27 48 64 330645 331024 32 2750
  0xfb7ff7f7 0x1514332110a6a662221114508daa91a (by decide +kernel)
private def pack_E6970Receipt27_chunk34 := witnessRule 27 47 0 340020 340335 32 3140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk35 := witnessRule 27 47 32 340336 340585 32 2984
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk36 := witnessRule 27 47 64 340586 340898 32 2757
  0xbbbfffff 0x2a2846426149450cc86229988b (by decide +kernel)
private def pack_E6970Receipt27_chunk37 := witnessRule 27 47 96 340960 340961 2 164
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk38 := witnessRule 27 46 0 350019 350331 32 3128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk39 := witnessRule 27 46 32 350332 350579 32 2975
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk40 := witnessRule 27 46 64 350580 350835 32 2712
  0xbfefffff 0x94508c8482a28a1188c (by decide +kernel)
private def pack_E6970Receipt27_chunk41 := witnessRule 27 46 96 350896 350960 4 321
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk42 := witnessRule 27 45 0 360018 360328 32 3096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk43 := witnessRule 27 45 32 360329 360521 32 2946
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk44 := witnessRule 27 45 64 360522 360832 32 2714
  0xdfffffff 0x1a8a1190885 (by decide +kernel)
private def pack_E6970Receipt27_chunk45 := witnessRule 27 45 96 360833 360960 6 472
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk46 := witnessRule 27 44 0 370017 370270 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk47 := witnessRule 27 44 32 370271 370516 32 2948
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk48 := witnessRule 27 44 64 370517 370770 32 2655
  0xf7ffffff 0x228a1190c (by decide +kernel)
private def pack_E6970Receipt27_chunk49 := witnessRule 27 44 96 370771 370897 7 539
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk50 := witnessRule 27 43 0 380016 380267 32 3060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk51 := witnessRule 27 43 32 380268 380459 32 2870
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk52 := witnessRule 27 43 64 380512 380709 32 2678
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk53 := witnessRule 27 43 96 380768 380896 8 610
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk54 := witnessRule 27 42 0 390015 390264 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk55 := witnessRule 27 42 32 390265 390454 32 2900
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk56 := witnessRule 27 42 64 390455 390706 32 2597
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk57 := witnessRule 27 42 96 390707 390896 9 670
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk58 := witnessRule 27 41 0 400014 400208 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk59 := witnessRule 27 41 32 400262 400450 32 2908
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk60 := witnessRule 27 41 64 400451 400704 32 2563
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk61 := witnessRule 27 41 96 400705 400833 9 658
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk62 := witnessRule 27 40 0 410013 410205 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk63 := witnessRule 27 40 32 410206 410394 32 2824
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk64 := witnessRule 27 40 64 410395 410644 32 2546
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk65 := witnessRule 27 40 96 410645 410832 9 648
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk66 := witnessRule 27 39 0 420012 420203 32 2964
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk67 := witnessRule 27 39 32 420204 420390 32 2820
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk68 := witnessRule 27 39 64 420391 420642 32 2468
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk69 := witnessRule 27 39 96 420643 420832 9 634
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk70 := witnessRule 27 38 0 430011 430200 32 2932
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk71 := witnessRule 27 38 32 430201 430387 32 2788
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk72 := witnessRule 27 38 64 430388 430641 32 2414
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk73 := witnessRule 27 38 96 430642 430769 8 551
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk74 := witnessRule 27 37 0 440010 440198 32 2908
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk75 := witnessRule 27 37 32 440199 440384 32 2724
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk76 := witnessRule 27 37 64 440385 440640 32 2393
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk77 := witnessRule 27 37 96 440641 440768 7 475
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk78 := witnessRule 27 36 0 450009 450195 32 2844
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk79 := witnessRule 27 36 32 450196 450329 32 2720
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk80 := witnessRule 27 36 64 450330 450640 32 2325
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk81 := witnessRule 27 36 96 450641 450768 6 400
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk82 := witnessRule 27 35 0 460008 460142 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk83 := witnessRule 27 35 32 460194 460327 32 2720
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk84 := witnessRule 27 35 64 460328 460640 32 2235
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk85 := witnessRule 27 35 96 460641 460705 4 262
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk86 := witnessRule 27 34 0 470007 470140 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk87 := witnessRule 27 34 32 470141 470325 32 2632
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk88 := witnessRule 27 34 64 470326 470641 32 2168
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk89 := witnessRule 27 34 96 470642 470704 2 129
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk90 := witnessRule 27 33 0 480006 480138 32 2796
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk91 := witnessRule 27 33 32 480139 480324 32 2564
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk92 := witnessRule 27 33 64 480325 480704 32 2099
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk93 := witnessRule 27 32 0 490005 490136 32 2784
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk94 := witnessRule 27 32 32 490137 490323 32 2457
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk95 := witnessRule 27 32 64 490324 490641 29 1851
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk96 := witnessRule 27 31 0 500004 500134 32 2764
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk97 := witnessRule 27 31 32 500135 500323 32 2377
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk98 := witnessRule 27 31 64 500324 500640 26 1608
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk99 := witnessRule 27 30 0 510003 510133 32 2716
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk100 := witnessRule 27 30 32 510134 510323 32 2280
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk101 := witnessRule 27 30 64 510324 510640 23 1380
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk102 := witnessRule 27 29 0 520002 520132 32 2668
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk103 := witnessRule 27 29 32 520133 520324 32 2193
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk104 := witnessRule 27 29 64 520325 520577 19 1101
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk105 := witnessRule 27 28 0 530001 530132 32 2596
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk106 := witnessRule 27 28 32 530133 530325 32 2079
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk107 := witnessRule 27 28 64 530326 530576 15 849
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk108 := witnessRule 27 27 0 540000 540132 32 2524
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk109 := witnessRule 27 27 32 540133 540384 32 1981
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk110 := witnessRule 27 27 64 540385 540576 11 603
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk111 := witnessRule 27 26 0 550000 550133 32 2416
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk112 := witnessRule 27 26 32 550134 550387 32 1868
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk113 := witnessRule 27 26 64 550388 550513 6 319
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk114 := witnessRule 27 25 0 560000 560134 32 2300
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk115 := witnessRule 27 25 32 560135 560450 32 1777
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk116 := witnessRule 27 25 64 560512 560512 1 53
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk117 := witnessRule 27 24 0 570000 570135 32 2180
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk118 := witnessRule 27 24 32 570136 570512 29 1550
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk119 := witnessRule 27 23 0 580000 580136 32 2056
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk120 := witnessRule 27 23 32 580192 580449 24 1245
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk121 := witnessRule 27 22 0 590000 590192 32 1957
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk122 := witnessRule 27 22 32 590193 590448 20 990
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk123 := witnessRule 27 21 0 600000 600194 32 1864
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk124 := witnessRule 27 21 32 600195 600448 16 751
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk125 := witnessRule 27 20 0 610000 610195 32 1755
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk126 := witnessRule 27 20 32 610196 610385 12 542
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk127 := witnessRule 27 19 0 620000 620197 32 1653
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk128 := witnessRule 27 19 32 620256 620384 8 354
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk129 := witnessRule 27 18 0 630000 630257 32 1560
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk130 := witnessRule 27 18 32 630258 630384 5 214
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk131 := witnessRule 27 17 0 640000 640320 32 1473
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk132 := witnessRule 27 17 32 640321 640321 1 42
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk133 := witnessRule 27 16 0 650000 650320 30 1316
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk134 := witnessRule 27 15 0 660000 660320 27 1132
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk135 := witnessRule 27 14 0 670000 670257 24 957
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk136 := witnessRule 27 13 0 680000 680256 21 801
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk137 := witnessRule 27 12 0 690000 690256 19 689
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk138 := witnessRule 27 11 0 700000 700193 16 552
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk139 := witnessRule 27 10 0 710000 710192 14 460
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk140 := witnessRule 27 9 0 720000 720192 12 376
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk141 := witnessRule 27 8 0 730000 730129 10 296
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk142 := witnessRule 27 7 0 740000 740128 8 226
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk143 := witnessRule 27 6 0 750000 750128 7 188
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk144 := witnessRule 27 5 0 760000 760065 5 127
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk145 := witnessRule 27 4 0 770000 770064 4 97
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk146 := witnessRule 27 3 0 780000 780064 3 70
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk147 := witnessRule 27 2 0 790000 790001 2 44
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk148 := witnessRule 27 1 0 800000 800000 1 21
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt27_chunk149 := witnessRule 27 0 0 810000 810000 1 20
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt27_chunks : List (Chunk 27) := [pack_E6970Receipt27_chunk0, pack_E6970Receipt27_chunk1, pack_E6970Receipt27_chunk2, pack_E6970Receipt27_chunk3, pack_E6970Receipt27_chunk4, pack_E6970Receipt27_chunk5, pack_E6970Receipt27_chunk6, pack_E6970Receipt27_chunk7, pack_E6970Receipt27_chunk8, pack_E6970Receipt27_chunk9, pack_E6970Receipt27_chunk10, pack_E6970Receipt27_chunk11, pack_E6970Receipt27_chunk12, pack_E6970Receipt27_chunk13, pack_E6970Receipt27_chunk14, pack_E6970Receipt27_chunk15, pack_E6970Receipt27_chunk16, pack_E6970Receipt27_chunk17, pack_E6970Receipt27_chunk18, pack_E6970Receipt27_chunk19, pack_E6970Receipt27_chunk20, pack_E6970Receipt27_chunk21, pack_E6970Receipt27_chunk22, pack_E6970Receipt27_chunk23, pack_E6970Receipt27_chunk24, pack_E6970Receipt27_chunk25, pack_E6970Receipt27_chunk26, pack_E6970Receipt27_chunk27, pack_E6970Receipt27_chunk28, pack_E6970Receipt27_chunk29, pack_E6970Receipt27_chunk30, pack_E6970Receipt27_chunk31, pack_E6970Receipt27_chunk32, pack_E6970Receipt27_chunk33, pack_E6970Receipt27_chunk34, pack_E6970Receipt27_chunk35, pack_E6970Receipt27_chunk36, pack_E6970Receipt27_chunk37, pack_E6970Receipt27_chunk38, pack_E6970Receipt27_chunk39, pack_E6970Receipt27_chunk40, pack_E6970Receipt27_chunk41, pack_E6970Receipt27_chunk42, pack_E6970Receipt27_chunk43, pack_E6970Receipt27_chunk44, pack_E6970Receipt27_chunk45, pack_E6970Receipt27_chunk46, pack_E6970Receipt27_chunk47, pack_E6970Receipt27_chunk48, pack_E6970Receipt27_chunk49, pack_E6970Receipt27_chunk50, pack_E6970Receipt27_chunk51, pack_E6970Receipt27_chunk52, pack_E6970Receipt27_chunk53, pack_E6970Receipt27_chunk54, pack_E6970Receipt27_chunk55, pack_E6970Receipt27_chunk56, pack_E6970Receipt27_chunk57, pack_E6970Receipt27_chunk58, pack_E6970Receipt27_chunk59, pack_E6970Receipt27_chunk60, pack_E6970Receipt27_chunk61, pack_E6970Receipt27_chunk62, pack_E6970Receipt27_chunk63, pack_E6970Receipt27_chunk64, pack_E6970Receipt27_chunk65, pack_E6970Receipt27_chunk66, pack_E6970Receipt27_chunk67, pack_E6970Receipt27_chunk68, pack_E6970Receipt27_chunk69, pack_E6970Receipt27_chunk70, pack_E6970Receipt27_chunk71, pack_E6970Receipt27_chunk72, pack_E6970Receipt27_chunk73, pack_E6970Receipt27_chunk74, pack_E6970Receipt27_chunk75, pack_E6970Receipt27_chunk76, pack_E6970Receipt27_chunk77, pack_E6970Receipt27_chunk78, pack_E6970Receipt27_chunk79, pack_E6970Receipt27_chunk80, pack_E6970Receipt27_chunk81, pack_E6970Receipt27_chunk82, pack_E6970Receipt27_chunk83, pack_E6970Receipt27_chunk84, pack_E6970Receipt27_chunk85, pack_E6970Receipt27_chunk86, pack_E6970Receipt27_chunk87, pack_E6970Receipt27_chunk88, pack_E6970Receipt27_chunk89, pack_E6970Receipt27_chunk90, pack_E6970Receipt27_chunk91, pack_E6970Receipt27_chunk92, pack_E6970Receipt27_chunk93, pack_E6970Receipt27_chunk94, pack_E6970Receipt27_chunk95, pack_E6970Receipt27_chunk96, pack_E6970Receipt27_chunk97, pack_E6970Receipt27_chunk98, pack_E6970Receipt27_chunk99, pack_E6970Receipt27_chunk100, pack_E6970Receipt27_chunk101, pack_E6970Receipt27_chunk102, pack_E6970Receipt27_chunk103, pack_E6970Receipt27_chunk104, pack_E6970Receipt27_chunk105, pack_E6970Receipt27_chunk106, pack_E6970Receipt27_chunk107, pack_E6970Receipt27_chunk108, pack_E6970Receipt27_chunk109, pack_E6970Receipt27_chunk110, pack_E6970Receipt27_chunk111, pack_E6970Receipt27_chunk112, pack_E6970Receipt27_chunk113, pack_E6970Receipt27_chunk114, pack_E6970Receipt27_chunk115, pack_E6970Receipt27_chunk116, pack_E6970Receipt27_chunk117, pack_E6970Receipt27_chunk118, pack_E6970Receipt27_chunk119, pack_E6970Receipt27_chunk120, pack_E6970Receipt27_chunk121, pack_E6970Receipt27_chunk122, pack_E6970Receipt27_chunk123, pack_E6970Receipt27_chunk124, pack_E6970Receipt27_chunk125, pack_E6970Receipt27_chunk126, pack_E6970Receipt27_chunk127, pack_E6970Receipt27_chunk128, pack_E6970Receipt27_chunk129, pack_E6970Receipt27_chunk130, pack_E6970Receipt27_chunk131, pack_E6970Receipt27_chunk132, pack_E6970Receipt27_chunk133, pack_E6970Receipt27_chunk134, pack_E6970Receipt27_chunk135, pack_E6970Receipt27_chunk136, pack_E6970Receipt27_chunk137, pack_E6970Receipt27_chunk138, pack_E6970Receipt27_chunk139, pack_E6970Receipt27_chunk140, pack_E6970Receipt27_chunk141, pack_E6970Receipt27_chunk142, pack_E6970Receipt27_chunk143, pack_E6970Receipt27_chunk144, pack_E6970Receipt27_chunk145, pack_E6970Receipt27_chunk146, pack_E6970Receipt27_chunk147, pack_E6970Receipt27_chunk148, pack_E6970Receipt27_chunk149]
def rows27 := rowsFrom pack_E6970Receipt27_chunks
theorem good27 : ∀ r ∈ rows27, good 27 r = true := rowsFrom_good pack_E6970Receipt27_chunks
theorem sorted27 : rows27.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt27_chunks 0 (by decide +kernel)).1
theorem mass27 (i : Fin 61) :
    bandCount 27 (i.val : ℤ) 60 16 ≤ (rows27.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt27_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 27 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt27_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total27 : (rows27.map (price 27)).sum = 291920 :=
  (total_eq pack_E6970Receipt27_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt27

section Pack_E6970Receipt28

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt28_chunk0 := witnessA6966Final 28 60 0 240280 240901 32 3383
  0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk1 := witnessA6966Final 28 60 32 240902 241030 17 1769
  0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk2 := witnessRule 28 59 0 250217 250838 32 3332
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk3 := witnessRule 28 59 32 250839 251029 23 2338
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk4 := witnessRule 28 58 0 260154 260775 32 3308
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk5 := witnessRule 28 58 32 260776 261029 30 2994
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk6 := witnessRule 28 57 0 270091 270712 32 3293
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk7 := witnessRule 28 57 32 270713 271024 32 3156
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk8 := witnessRule 28 57 64 271025 271028 4 384
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk9 := witnessRule 28 56 0 280028 280649 32 3281
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk10 := witnessRule 28 56 32 280650 280903 32 3136
  0xeffefffb 0x2e66898550a91a (by decide +kernel)
private def pack_E6970Receipt28_chunk11 := witnessRule 28 56 64 280960 281028 11 1043
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk12 := witnessRule 28 55 0 290027 290587 32 3264
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk13 := witnessRule 28 55 32 290588 290896 32 3118
  0xdfffffff 0xb0a91b (by decide +kernel)
private def pack_E6970Receipt28_chunk14 := witnessRule 28 55 64 290897 291027 16 1491
  0xffef 0xb19883 (by decide +kernel)
private def pack_E6970Receipt28_chunk15 := witnessRule 28 54 0 300026 300525 32 3246
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk16 := witnessRule 28 54 32 300526 300833 32 3109
  0xcfdf9f7e 0x4c4a858548c420b1289b262544a46858944d9291a (by decide +kernel)
private def pack_E6970Receipt28_chunk17 := witnessRule 28 54 64 300834 301027 22 2024
  0x3f7bcf 0x531042a86898544c420b0a99b (by decide +kernel)
private def pack_E6970Receipt28_chunk18 := witnessRule 28 53 0 310025 310464 32 3216
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk19 := witnessRule 28 53 32 310521 310772 32 3104
  0xfbffffff 0xb1291b (by decide +kernel)
private def pack_E6970Receipt28_chunk20 := witnessRule 28 53 64 310773 311026 26 2358
  0x3f67af5 0x28a685854cc420aa9a16252362e2a2847098944d8b9291b (by decide +kernel)
private def pack_E6970Receipt28_chunk21 := witnessRule 28 52 0 320024 320459 32 3211
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk22 := witnessRule 28 52 32 320460 320711 32 3061
  0xfcfdfdff 0x263546a46858d44d9a91a (by decide +kernel)
private def pack_E6970Receipt28_chunk23 := witnessRule 28 52 64 320712 321026 31 2797
  0x7ddefdfd 0xaa9883254342c4a66c58948c420b1a89b (by decide +kernel)
private def pack_E6970Receipt28_chunk24 := witnessRule 28 51 0 330023 330399 32 3186
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk25 := witnessRule 28 51 32 330400 330705 32 3043
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk26 := witnessRule 28 51 64 330706 330963 32 2855
  0xe9e7bfbf 0x28a622c94cc8192a9a25431062e2a2846234d4cd0b1a91b (by decide +kernel)
private def pack_E6970Receipt28_chunk27 := witnessRule 28 51 96 331024 331025 2 173
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk28 := witnessRule 28 50 0 340022 340395 32 3172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk29 := witnessRule 28 50 32 340396 340645 32 3033
  0xf7fbffff 0x59144da291a (by decide +kernel)
private def pack_E6970Receipt28_chunk30 := witnessRule 28 50 64 340646 340899 32 2825
  0xb9f7dfe7 0x4a8640cd4cc41928a21b354342c8a26c99152291a (by decide +kernel)
private def pack_E6970Receipt28_chunk31 := witnessRule 28 50 96 340900 341025 6 509
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk32 := witnessRule 28 49 0 350021 350336 32 3140
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk33 := witnessRule 28 49 32 350337 350586 32 2996
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk34 := witnessRule 28 49 64 350587 350837 32 2823
  0xcefdffff 0x35431062e2a284643514cd0b2291b (by decide +kernel)
private def pack_E6970Receipt28_chunk35 := witnessRule 28 49 96 350896 351024 8 665
  0xf9 0x94cd018a8a2188885 (by decide +kernel)
private def pack_E6970Receipt28_chunk36 := witnessRule 28 48 0 360020 360332 32 3128
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk37 := witnessRule 28 48 32 360333 360580 32 2986
  0xf7ffffff 0x2a91a (by decide +kernel)
private def pack_E6970Receipt28_chunk38 := witnessRule 28 48 64 360581 360832 32 2791
  0xefbfbfdf 0x454348a6620d548d0b2a89b (by decide +kernel)
private def pack_E6970Receipt28_chunk39 := witnessRule 28 48 96 360833 361024 11 896
  0x7d9 0x2a286622614d4ccc1928a2188c (by decide +kernel)
private def pack_E6970Receipt28_chunk40 := witnessRule 28 47 0 370019 370329 32 3096
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk41 := witnessRule 28 47 32 370330 370522 32 2952
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk42 := witnessRule 28 47 64 370523 370771 32 2781
  0xfdfbffff 0x11450cdaa99a (by decide +kernel)
private def pack_E6970Receipt28_chunk43 := witnessRule 28 47 96 370772 370961 12 960
  0xfe6 0x4a2866224145c54508cc6a299903 (by decide +kernel)
private def pack_E6970Receipt28_chunk44 := witnessRule 28 46 0 380018 380271 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk45 := witnessRule 28 46 32 380272 380517 32 2954
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk46 := witnessRule 28 46 64 380518 380710 32 2730
  0xbfff7fef 0xaa6620c59944db291a (by decide +kernel)
private def pack_E6970Receipt28_chunk47 := witnessRule 28 46 96 380768 380960 14 1109
  0x3ef7 0x94508c45029a8a1988885 (by decide +kernel)
private def pack_E6970Receipt28_chunk48 := witnessRule 28 45 0 390017 390268 32 3060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk49 := witnessRule 28 45 32 390269 390460 32 2876
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk50 := witnessRule 28 45 64 390513 390707 32 2749
  0xfbffffff 0x3299a (by decide +kernel)
private def pack_E6970Receipt28_chunk51 := witnessRule 28 45 96 390708 390960 15 1158
  0x7ebe 0x302846830d4508c44c2a28a1988c (by decide +kernel)
private def pack_E6970Receipt28_chunk52 := witnessRule 28 44 0 400016 400265 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk53 := witnessRule 28 44 32 400266 400455 32 2903
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk54 := witnessRule 28 44 64 400456 400647 32 2671
  0xffbfdfff 0x194508dba91a (by decide +kernel)
private def pack_E6970Receipt28_chunk55 := witnessRule 28 44 96 400704 400897 16 1228
  0xffef 0x228a1188905 (by decide +kernel)
private def pack_E6970Receipt28_chunk56 := witnessRule 28 43 0 410015 410209 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk57 := witnessRule 28 43 32 410263 410451 32 2911
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk58 := witnessRule 28 43 64 410452 410644 32 2636
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk59 := witnessRule 28 43 96 410645 410896 16 1196
  0xfffe 0x2a8a1188885 (by decide +kernel)
private def pack_E6970Receipt28_chunk60 := witnessRule 28 42 0 420014 420206 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk61 := witnessRule 28 42 32 420207 420395 32 2824
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk62 := witnessRule 28 42 64 420396 420641 32 2642
  0xefffffff 0x328a1188c (by decide +kernel)
private def pack_E6970Receipt28_chunk63 := witnessRule 28 42 96 420642 420896 17 1248
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk64 := witnessRule 28 41 0 430013 430204 32 2964
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk65 := witnessRule 28 41 32 430205 430391 32 2822
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk66 := witnessRule 28 41 64 430392 430583 32 2537
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk67 := witnessRule 28 41 96 430640 430833 16 1164
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk68 := witnessRule 28 40 0 440012 440201 32 2932
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk69 := witnessRule 28 40 32 440202 440387 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk70 := witnessRule 28 40 64 440388 440580 32 2504
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk71 := witnessRule 28 40 96 440581 440832 16 1132
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk72 := witnessRule 28 39 0 450011 450199 32 2908
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk73 := witnessRule 28 39 32 450200 450384 32 2730
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk74 := witnessRule 28 39 64 450385 450579 32 2485
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk75 := witnessRule 28 39 96 450580 450832 15 1037
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk76 := witnessRule 28 38 0 460010 460196 32 2844
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk77 := witnessRule 28 38 32 460197 460329 32 2760
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk78 := witnessRule 28 38 64 460330 460577 32 2410
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk79 := witnessRule 28 38 96 460578 460769 14 951
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk80 := witnessRule 28 37 0 470009 470143 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk81 := witnessRule 28 37 32 470195 470327 32 2752
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk82 := witnessRule 28 37 64 470328 470577 32 2322
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk83 := witnessRule 28 37 96 470578 470768 12 797
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk84 := witnessRule 28 36 0 480008 480141 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk85 := witnessRule 28 36 32 480142 480324 32 2684
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk86 := witnessRule 28 36 64 480325 480576 32 2260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk87 := witnessRule 28 36 96 480577 480768 11 718
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk88 := witnessRule 28 35 0 490007 490139 32 2796
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk89 := witnessRule 28 35 32 490140 490323 32 2608
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk90 := witnessRule 28 35 64 490324 490577 32 2188
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk91 := witnessRule 28 35 96 490578 490705 8 511
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk92 := witnessRule 28 34 0 500006 500137 32 2784
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk93 := witnessRule 28 34 32 500138 500321 32 2518
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk94 := witnessRule 28 34 64 500322 500577 32 2142
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk95 := witnessRule 28 34 96 500578 500704 6 377
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk96 := witnessRule 28 33 0 510005 510135 32 2764
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk97 := witnessRule 28 33 32 510136 510321 32 2437
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk98 := witnessRule 28 33 64 510322 510579 32 2058
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk99 := witnessRule 28 33 96 510640 510704 3 187
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk100 := witnessRule 28 32 0 520004 520133 32 2740
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk101 := witnessRule 28 32 32 520134 520320 32 2345
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk102 := witnessRule 28 32 64 520321 520641 32 2010
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk103 := witnessRule 28 31 0 530003 530132 32 2688
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk104 := witnessRule 28 31 32 530133 530321 32 2278
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk105 := witnessRule 28 31 64 530322 530640 28 1689
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk106 := witnessRule 28 30 0 540002 540131 32 2640
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk107 := witnessRule 28 30 32 540132 540321 32 2190
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk108 := witnessRule 28 30 64 540322 540640 25 1462
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk109 := witnessRule 28 29 0 550001 550131 32 2568
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk110 := witnessRule 28 29 32 550132 550323 32 2098
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk111 := witnessRule 28 29 64 550324 550577 20 1125
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk112 := witnessRule 28 28 0 560000 560131 32 2500
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk113 := witnessRule 28 28 32 560132 560324 32 1991
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk114 := witnessRule 28 28 64 560325 560576 16 876
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk115 := witnessRule 28 27 0 570000 570132 32 2396
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk116 := witnessRule 28 27 32 570133 570384 32 1876
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk117 := witnessRule 28 27 64 570385 570576 11 586
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk118 := witnessRule 28 26 0 580000 580133 32 2288
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk119 := witnessRule 28 26 32 580134 580387 32 1776
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk120 := witnessRule 28 26 64 580388 580513 6 313
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk121 := witnessRule 28 25 0 590000 590134 32 2174
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk122 := witnessRule 28 25 32 590135 590450 32 1696
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk123 := witnessRule 28 25 64 590512 590512 1 52
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk124 := witnessRule 28 24 0 600000 600135 32 2054
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk125 := witnessRule 28 24 32 600136 600512 29 1482
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk126 := witnessRule 28 23 0 610000 610136 32 1937
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk127 := witnessRule 28 23 32 610192 610449 24 1194
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk128 := witnessRule 28 22 0 620000 620192 32 1841
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk129 := witnessRule 28 22 32 620193 620448 20 950
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk130 := witnessRule 28 21 0 630000 630194 32 1750
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk131 := witnessRule 28 21 32 630195 630448 16 723
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk132 := witnessRule 28 20 0 640000 640195 32 1649
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk133 := witnessRule 28 20 32 640196 640385 12 526
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk134 := witnessRule 28 19 0 650000 650197 32 1554
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk135 := witnessRule 28 19 32 650256 650384 8 343
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk136 := witnessRule 28 18 0 660000 660257 32 1466
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk137 := witnessRule 28 18 32 660258 660384 5 209
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk138 := witnessRule 28 17 0 670000 670320 32 1392
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk139 := witnessRule 28 17 32 670321 670321 1 41
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk140 := witnessRule 28 16 0 680000 680320 30 1243
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk141 := witnessRule 28 15 0 690000 690320 27 1068
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk142 := witnessRule 28 14 0 700000 700257 24 906
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk143 := witnessRule 28 13 0 710000 710256 21 757
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk144 := witnessRule 28 12 0 720000 720256 19 651
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk145 := witnessRule 28 11 0 730000 730193 16 524
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk146 := witnessRule 28 10 0 740000 740192 14 436
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk147 := witnessRule 28 9 0 750000 750192 12 356
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk148 := witnessRule 28 8 0 760000 760129 10 282
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk149 := witnessRule 28 7 0 770000 770128 8 215
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk150 := witnessRule 28 6 0 780000 780128 7 179
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk151 := witnessRule 28 5 0 790000 790065 5 122
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk152 := witnessRule 28 4 0 800000 800064 4 93
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk153 := witnessRule 28 3 0 810000 810064 3 67
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk154 := witnessRule 28 2 0 820000 820001 2 42
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk155 := witnessRule 28 1 0 830000 830000 1 20
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt28_chunk156 := witnessRule 28 0 0 840000 840000 1 19
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt28_chunks : List (Chunk 28) := [pack_E6970Receipt28_chunk0, pack_E6970Receipt28_chunk1, pack_E6970Receipt28_chunk2, pack_E6970Receipt28_chunk3, pack_E6970Receipt28_chunk4, pack_E6970Receipt28_chunk5, pack_E6970Receipt28_chunk6, pack_E6970Receipt28_chunk7, pack_E6970Receipt28_chunk8, pack_E6970Receipt28_chunk9, pack_E6970Receipt28_chunk10, pack_E6970Receipt28_chunk11, pack_E6970Receipt28_chunk12, pack_E6970Receipt28_chunk13, pack_E6970Receipt28_chunk14, pack_E6970Receipt28_chunk15, pack_E6970Receipt28_chunk16, pack_E6970Receipt28_chunk17, pack_E6970Receipt28_chunk18, pack_E6970Receipt28_chunk19, pack_E6970Receipt28_chunk20, pack_E6970Receipt28_chunk21, pack_E6970Receipt28_chunk22, pack_E6970Receipt28_chunk23, pack_E6970Receipt28_chunk24, pack_E6970Receipt28_chunk25, pack_E6970Receipt28_chunk26, pack_E6970Receipt28_chunk27, pack_E6970Receipt28_chunk28, pack_E6970Receipt28_chunk29, pack_E6970Receipt28_chunk30, pack_E6970Receipt28_chunk31, pack_E6970Receipt28_chunk32, pack_E6970Receipt28_chunk33, pack_E6970Receipt28_chunk34, pack_E6970Receipt28_chunk35, pack_E6970Receipt28_chunk36, pack_E6970Receipt28_chunk37, pack_E6970Receipt28_chunk38, pack_E6970Receipt28_chunk39, pack_E6970Receipt28_chunk40, pack_E6970Receipt28_chunk41, pack_E6970Receipt28_chunk42, pack_E6970Receipt28_chunk43, pack_E6970Receipt28_chunk44, pack_E6970Receipt28_chunk45, pack_E6970Receipt28_chunk46, pack_E6970Receipt28_chunk47, pack_E6970Receipt28_chunk48, pack_E6970Receipt28_chunk49, pack_E6970Receipt28_chunk50, pack_E6970Receipt28_chunk51, pack_E6970Receipt28_chunk52, pack_E6970Receipt28_chunk53, pack_E6970Receipt28_chunk54, pack_E6970Receipt28_chunk55, pack_E6970Receipt28_chunk56, pack_E6970Receipt28_chunk57, pack_E6970Receipt28_chunk58, pack_E6970Receipt28_chunk59, pack_E6970Receipt28_chunk60, pack_E6970Receipt28_chunk61, pack_E6970Receipt28_chunk62, pack_E6970Receipt28_chunk63, pack_E6970Receipt28_chunk64, pack_E6970Receipt28_chunk65, pack_E6970Receipt28_chunk66, pack_E6970Receipt28_chunk67, pack_E6970Receipt28_chunk68, pack_E6970Receipt28_chunk69, pack_E6970Receipt28_chunk70, pack_E6970Receipt28_chunk71, pack_E6970Receipt28_chunk72, pack_E6970Receipt28_chunk73, pack_E6970Receipt28_chunk74, pack_E6970Receipt28_chunk75, pack_E6970Receipt28_chunk76, pack_E6970Receipt28_chunk77, pack_E6970Receipt28_chunk78, pack_E6970Receipt28_chunk79, pack_E6970Receipt28_chunk80, pack_E6970Receipt28_chunk81, pack_E6970Receipt28_chunk82, pack_E6970Receipt28_chunk83, pack_E6970Receipt28_chunk84, pack_E6970Receipt28_chunk85, pack_E6970Receipt28_chunk86, pack_E6970Receipt28_chunk87, pack_E6970Receipt28_chunk88, pack_E6970Receipt28_chunk89, pack_E6970Receipt28_chunk90, pack_E6970Receipt28_chunk91, pack_E6970Receipt28_chunk92, pack_E6970Receipt28_chunk93, pack_E6970Receipt28_chunk94, pack_E6970Receipt28_chunk95, pack_E6970Receipt28_chunk96, pack_E6970Receipt28_chunk97, pack_E6970Receipt28_chunk98, pack_E6970Receipt28_chunk99, pack_E6970Receipt28_chunk100, pack_E6970Receipt28_chunk101, pack_E6970Receipt28_chunk102, pack_E6970Receipt28_chunk103, pack_E6970Receipt28_chunk104, pack_E6970Receipt28_chunk105, pack_E6970Receipt28_chunk106, pack_E6970Receipt28_chunk107, pack_E6970Receipt28_chunk108, pack_E6970Receipt28_chunk109, pack_E6970Receipt28_chunk110, pack_E6970Receipt28_chunk111, pack_E6970Receipt28_chunk112, pack_E6970Receipt28_chunk113, pack_E6970Receipt28_chunk114, pack_E6970Receipt28_chunk115, pack_E6970Receipt28_chunk116, pack_E6970Receipt28_chunk117, pack_E6970Receipt28_chunk118, pack_E6970Receipt28_chunk119, pack_E6970Receipt28_chunk120, pack_E6970Receipt28_chunk121, pack_E6970Receipt28_chunk122, pack_E6970Receipt28_chunk123, pack_E6970Receipt28_chunk124, pack_E6970Receipt28_chunk125, pack_E6970Receipt28_chunk126, pack_E6970Receipt28_chunk127, pack_E6970Receipt28_chunk128, pack_E6970Receipt28_chunk129, pack_E6970Receipt28_chunk130, pack_E6970Receipt28_chunk131, pack_E6970Receipt28_chunk132, pack_E6970Receipt28_chunk133, pack_E6970Receipt28_chunk134, pack_E6970Receipt28_chunk135, pack_E6970Receipt28_chunk136, pack_E6970Receipt28_chunk137, pack_E6970Receipt28_chunk138, pack_E6970Receipt28_chunk139, pack_E6970Receipt28_chunk140, pack_E6970Receipt28_chunk141, pack_E6970Receipt28_chunk142, pack_E6970Receipt28_chunk143, pack_E6970Receipt28_chunk144, pack_E6970Receipt28_chunk145, pack_E6970Receipt28_chunk146, pack_E6970Receipt28_chunk147, pack_E6970Receipt28_chunk148, pack_E6970Receipt28_chunk149, pack_E6970Receipt28_chunk150, pack_E6970Receipt28_chunk151, pack_E6970Receipt28_chunk152, pack_E6970Receipt28_chunk153, pack_E6970Receipt28_chunk154, pack_E6970Receipt28_chunk155, pack_E6970Receipt28_chunk156]
def rows28 := rowsFrom pack_E6970Receipt28_chunks
theorem good28 : ∀ r ∈ rows28, good 28 r = true := rowsFrom_good pack_E6970Receipt28_chunks
theorem sorted28 : rows28.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt28_chunks 0 (by decide +kernel)).1
theorem mass28 (i : Fin 61) :
    bandCount 28 (i.val : ℤ) 60 16 ≤ (rows28.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt28_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 28 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt28_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total28 : (rows28.map (price 28)).sum = 310312 :=
  (total_eq pack_E6970Receipt28_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt28

section Pack_E6970Receipt29

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt29_chunk0 := witnessA6966Final 29 60 0 270155 270776 32 3383
  0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk1 := witnessA6966Final 29 60 32 270777 271030 31 3218
  0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk2 := witnessRule 29 59 0 280092 280713 32 3332
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk3 := witnessRule 29 59 32 280714 280967 32 3249
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk4 := witnessRule 29 59 64 281024 281029 6 603
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk5 := witnessRule 29 58 0 290029 290650 32 3308
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk6 := witnessRule 29 58 32 290651 290904 32 3192
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk7 := witnessRule 29 58 64 290960 291029 13 1277
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk8 := witnessRule 29 57 0 300028 300588 32 3285
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk9 := witnessRule 29 57 32 300589 300896 32 3166
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk10 := witnessRule 29 57 64 300897 301028 19 1826
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk11 := witnessRule 29 56 0 310027 310526 32 3262
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk12 := witnessRule 29 56 32 310527 310834 32 3149
  0xffffbffe 0x98550a91a (by decide +kernel)
private def pack_E6970Receipt29_chunk13 := witnessRule 29 56 64 310835 311028 25 2356
  0x1fffbff 0xb99a (by decide +kernel)
private def pack_E6970Receipt29_chunk14 := witnessRule 29 55 0 320026 320465 32 3231
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk15 := witnessRule 29 55 32 320522 320773 32 3134
  0xfbffffff 0xb0a91b (by decide +kernel)
private def pack_E6970Receipt29_chunk16 := witnessRule 29 55 64 320774 321027 30 2791
  0x3ffefbfd 0x2e868590d299 (by decide +kernel)
private def pack_E6970Receipt29_chunk17 := witnessRule 29 54 0 330025 330460 32 3222
  0xefffffff 0x1291a (by decide +kernel)
private def pack_E6970Receipt29_chunk18 := witnessRule 29 54 32 330461 330712 32 3089
  0xfcfdf9f7 0x98950b0a9188416251364c4a8948d0b1289b (by decide +kernel)
private def pack_E6970Receipt29_chunk19 := witnessRule 29 54 64 330713 331024 32 2950
  0xff7dfbfd 0x16431062c2a66cd85441930a89884 (by decide +kernel)
private def pack_E6970Receipt29_chunk20 := witnessRule 29 54 96 331025 331027 3 270
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk21 := witnessRule 29 53 0 340024 340400 32 3192
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk22 := witnessRule 29 53 32 340401 340706 32 3073
  0xafdfffff 0x4c4a26c5c948d8b1291b (by decide +kernel)
private def pack_E6970Receipt29_chunk23 := witnessRule 29 53 64 340707 340960 32 2931
  0xef1ebf1f 0xaa9a2615231082c2a86c5c54cc42131289b155346c4a858948d8b8b1289c (by decide +kernel)
private def pack_E6970Receipt29_chunk24 := witnessRule 29 53 96 340961 341026 7 615
  0x7e 0x31882 (by decide +kernel)
private def pack_E6970Receipt29_chunk25 := witnessRule 29 52 0 350023 350396 32 3178
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk26 := witnessRule 29 52 32 350397 350646 32 3054
  0xf7f3f7f7 0xb1a89b263546a46858d44d9a91a (by decide +kernel)
private def pack_E6970Receipt29_chunk27 := witnessRule 29 52 64 350647 350897 32 2894
  0xebd7dfe7 0x2c4a66c5c5450ce131291b17253364c4a2621098d50b1291884 (by decide +kernel)
private def pack_E6970Receipt29_chunk28 := witnessRule 29 52 96 350898 351026 11 947
  0x7ec 0x28c6858550c420ab1a (by decide +kernel)
private def pack_E6970Receipt29_chunk29 := witnessRule 29 51 0 360022 360337 32 3144
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk30 := witnessRule 29 51 32 360338 360587 32 3018
  0x7fffffff 0xb1a91b (by decide +kernel)
private def pack_E6970Receipt29_chunk31 := witnessRule 29 51 64 360588 360835 32 2901
  0x7bf9fd7f 0x5c94cc420b129988416352362e2c6a27098d44d8b9a91b (by decide +kernel)
private def pack_E6970Receipt29_chunk32 := witnessRule 29 51 96 360836 361025 14 1185
  0x3fde 0x954d0b12a1b (by decide +kernel)
private def pack_E6970Receipt29_chunk33 := witnessRule 29 50 0 370021 370333 32 3131
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk34 := witnessRule 29 50 32 370334 370581 32 3004
  0xe7f7fbff 0x264548a46859144da291a (by decide +kernel)
private def pack_E6970Receipt29_chunk35 := witnessRule 29 50 64 370582 370774 32 2847
  0x9e7f3fdf 0x6a8685cd4cd931a8988416353364c8a858d48c420b2289b (by decide +kernel)
private def pack_E6970Receipt29_chunk36 := witnessRule 29 50 96 370775 371025 17 1422
  0x1fcc7 0x12a19031514531082c4a66410954c418b8a8a1988d (by decide +kernel)
private def pack_E6970Receipt29_chunk37 := witnessRule 29 49 0 380020 380330 32 3099
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk38 := witnessRule 29 49 32 380331 380523 32 2967
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk39 := witnessRule 29 49 64 380524 380769 32 2856
  0xebebfdff 0xb2291b1735142384c8a26c5d148d8b2291b (by decide +kernel)
private def pack_E6970Receipt29_chunk40 := witnessRule 29 49 96 380770 381024 19 1555
  0x7ee73 0xa8a2198435431064a28a6c58d4cc421aa9a (by decide +kernel)
private def pack_E6970Receipt29_chunk41 := witnessRule 29 48 0 390019 390272 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk42 := witnessRule 29 48 32 390273 390518 32 2969
  0xf7fdffff 0x59544daa91a (by decide +kernel)
private def pack_E6970Receipt29_chunk43 := witnessRule 29 48 64 390519 390709 32 2795
  0xfeff7fcf 0x1645231082caa26c99552a91a (by decide +kernel)
private def pack_E6970Receipt29_chunk44 := witnessRule 29 48 96 390710 391024 21 1694
  0x1fe39e 0xd4ccc1928a219041715143321a8a8685cd4cc460b2299b (by decide +kernel)
private def pack_E6970Receipt29_chunk45 := witnessRule 29 47 0 400018 400269 32 3062
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk46 := witnessRule 29 47 32 400270 400461 32 2889
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk47 := witnessRule 29 47 64 400514 400705 32 2820
  0xeff7ffff 0x154cd0b2a91b (by decide +kernel)
private def pack_E6970Receipt29_chunk48 := witnessRule 29 47 96 400706 400961 22 1743
  0x3f99f3 0x9450cd020c0a999088545332066a2886211150c418b9a8a1188d (by decide +kernel)
private def pack_E6970Receipt29_chunk49 := witnessRule 29 46 0 410017 410266 32 3028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk50 := witnessRule 29 46 32 410267 410456 32 2914
  0xfeffffff 0x3291a (by decide +kernel)
private def pack_E6970Receipt29_chunk51 := witnessRule 29 46 64 410457 410646 32 2738
  0x7eff9ff7 0x2aa1a16651364cca9948d0b3289b (by decide +kernel)
private def pack_E6970Receipt29_chunk52 := witnessRule 29 46 96 410647 410960 23 1794
  0x7d673f 0x94508d820c0a1998c351433308304a6643154cc41a28a21b (by decide +kernel)
private def pack_E6970Receipt29_chunk53 := witnessRule 29 45 0 420016 420210 32 2974
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk54 := witnessRule 29 45 32 420264 420452 32 2918
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk55 := witnessRule 29 45 64 420453 420642 32 2718
  0xf7ffffff 0xb3291b (by decide +kernel)
private def pack_E6970Receipt29_chunk56 := witnessRule 29 45 96 420643 420960 24 1835
  0xff7cf7 0x3514235088a28664105cd4508c86b299a (by decide +kernel)
private def pack_E6970Receipt29_chunk57 := witnessRule 29 44 0 430015 430207 32 2972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk58 := witnessRule 29 44 32 430208 430396 32 2832
  0x7fffffff 0x3a91a (by decide +kernel)
private def pack_E6970Receipt29_chunk59 := witnessRule 29 44 64 430397 430584 32 2693
  0xbfdff7ff 0xca6620dd48d0b3a89b (by decide +kernel)
private def pack_E6970Receipt29_chunk60 := witnessRule 29 44 96 430640 430897 24 1820
  0xff6fdf 0x302a28466221914508d022a8a19884 (by decide +kernel)
private def pack_E6970Receipt29_chunk61 := witnessRule 29 43 0 440014 440205 32 2964
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk62 := witnessRule 29 43 32 440206 440392 32 2828
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk63 := witnessRule 29 43 64 440393 440581 32 2637
  0xfeffffff 0x3a99a (by decide +kernel)
private def pack_E6970Receipt29_chunk64 := witnessRule 29 43 96 440582 440896 24 1768
  0xffeefe 0x304a284663554508cc2328a19b (by decide +kernel)
private def pack_E6970Receipt29_chunk65 := witnessRule 29 42 0 450013 450202 32 2932
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk66 := witnessRule 29 42 32 450203 450388 32 2810
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk67 := witnessRule 29 42 64 450389 450578 32 2581
  0xfffbffbf 0x5a144dc291a (by decide +kernel)
private def pack_E6970Receipt29_chunk68 := witnessRule 29 42 96 450579 450896 24 1737
  0xfffff7 0x328a11904 (by decide +kernel)
private def pack_E6970Receipt29_chunk69 := witnessRule 29 41 0 460012 460200 32 2908
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk70 := witnessRule 29 41 32 460201 460384 32 2740
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk71 := witnessRule 29 41 64 460385 460576 32 2572
  0xdfffffff 0x3a8a11884 (by decide +kernel)
private def pack_E6970Receipt29_chunk72 := witnessRule 29 41 96 460577 460833 23 1640
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk73 := witnessRule 29 40 0 470011 470197 32 2844
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk74 := witnessRule 29 40 32 470198 470330 32 2763
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk75 := witnessRule 29 40 64 470331 470519 32 2489
  0xffbfefff 0x214508dca91a (by decide +kernel)
private def pack_E6970Receipt29_chunk76 := witnessRule 29 40 96 470520 470832 22 1539
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk77 := witnessRule 29 39 0 480010 480144 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk78 := witnessRule 29 39 32 480196 480327 32 2787
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk79 := witnessRule 29 39 64 480328 480517 32 2405
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk80 := witnessRule 29 39 96 480518 480832 21 1434
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk81 := witnessRule 29 38 0 490009 490142 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk82 := witnessRule 29 38 32 490143 490324 32 2707
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk83 := witnessRule 29 38 64 490325 490516 32 2351
  0xfffeffff 0x4a8a09884 (by decide +kernel)
private def pack_E6970Receipt29_chunk84 := witnessRule 29 38 96 490517 490769 19 1266
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk85 := witnessRule 29 37 0 500008 500140 32 2796
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk86 := witnessRule 29 37 32 500141 500322 32 2647
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk87 := witnessRule 29 37 64 500323 500515 32 2293
  0xffffff7f 0x528a09b (by decide +kernel)
private def pack_E6970Receipt29_chunk88 := witnessRule 29 37 96 500516 500768 17 1107
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk89 := witnessRule 29 36 0 510007 510138 32 2784
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk90 := witnessRule 29 36 32 510139 510320 32 2539
  0xdfffffff 0x52922 (by decide +kernel)
private def pack_E6970Receipt29_chunk91 := witnessRule 29 36 64 510321 510515 32 2254
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk92 := witnessRule 29 36 96 510516 510768 15 958
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk93 := witnessRule 29 35 0 520006 520136 32 2764
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk94 := witnessRule 29 35 32 520137 520267 32 2476
  0x7fffffff 0x5a8a083 (by decide +kernel)
private def pack_E6970Receipt29_chunk95 := witnessRule 29 35 64 520320 520515 32 2190
  0xfffffdff 0x4a9208884 (by decide +kernel)
private def pack_E6970Receipt29_chunk96 := witnessRule 29 35 96 520516 520705 12 751
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk97 := witnessRule 29 34 0 530005 530134 32 2740
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk98 := witnessRule 29 34 32 530135 530266 32 2405
  0x7fefffff 0x2949045e28a2 (by decide +kernel)
private def pack_E6970Receipt29_chunk99 := witnessRule 29 34 64 530267 530516 32 2098
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk100 := witnessRule 29 34 96 530517 530704 9 553
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk101 := witnessRule 29 33 0 540004 540132 32 2708
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk102 := witnessRule 29 33 32 540133 540265 32 2348
  0xffefffff 0x5292093 (by decide +kernel)
private def pack_E6970Receipt29_chunk103 := witnessRule 29 33 64 540266 540576 32 2020
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk104 := witnessRule 29 33 96 540577 540704 6 364
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk105 := witnessRule 29 32 0 550003 550131 32 2656
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk106 := witnessRule 29 32 32 550132 550265 32 2263
  0x7fdfffff 0x25490484442da8a09084 (by decide +kernel)
private def pack_E6970Receipt29_chunk107 := witnessRule 29 32 64 550266 550578 32 1951
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk108 := witnessRule 29 32 96 550640 550641 2 120
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk109 := witnessRule 29 31 0 560002 560130 32 2604
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk110 := witnessRule 29 31 32 560131 560265 32 2183
  0xffeffdff 0x294904846628a093 (by decide +kernel)
private def pack_E6970Receipt29_chunk111 := witnessRule 29 31 64 560320 560640 30 1776
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk112 := witnessRule 29 30 0 570001 570130 32 2536
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk113 := witnessRule 29 30 32 570131 570320 32 2093
  0xfffffeff 0x5292113 (by decide +kernel)
private def pack_E6970Receipt29_chunk114 := witnessRule 29 30 64 570321 570640 26 1483
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk115 := witnessRule 29 29 0 580000 580130 32 2469
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk116 := witnessRule 29 29 32 580131 580322 32 2009
  0xfffbfeff 0x25490884442da8a11084 (by decide +kernel)
private def pack_E6970Receipt29_chunk117 := witnessRule 29 29 64 580323 580577 21 1149
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk118 := witnessRule 29 28 0 590000 590131 32 2372
  0xf7ffffff 0x628a113 (by decide +kernel)
private def pack_E6970Receipt29_chunk119 := witnessRule 29 28 32 590132 590324 32 1885
  0xffffffbf 0x52921108c (by decide +kernel)
private def pack_E6970Receipt29_chunk120 := witnessRule 29 28 64 590325 590576 16 852
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk121 := witnessRule 29 27 0 600000 600132 32 2271
  0xfdffffff 0x5292193 (by decide +kernel)
private def pack_E6970Receipt29_chunk122 := witnessRule 29 27 32 600133 600384 32 1783
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk123 := witnessRule 29 27 64 600385 600576 11 573
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk124 := witnessRule 29 26 0 610000 610133 32 2163
  0xfdffffff 0x5a8a19084 (by decide +kernel)
private def pack_E6970Receipt29_chunk125 := witnessRule 29 26 32 610134 610387 32 1692
  0xfffffff7 0x4a921908885 (by decide +kernel)
private def pack_E6970Receipt29_chunk126 := witnessRule 29 26 64 610388 610513 6 307
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk127 := witnessRule 29 25 0 620000 620134 32 2050
  0xff7fefff 0x29490c846628a193 (by decide +kernel)
private def pack_E6970Receipt29_chunk128 := witnessRule 29 25 32 620135 620450 32 1623
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk129 := witnessRule 29 25 64 620512 620512 1 51
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk130 := witnessRule 29 24 0 630000 630135 32 1935
  0xfffff7ff 0x5292213 (by decide +kernel)
private def pack_E6970Receipt29_chunk131 := witnessRule 29 24 32 630136 630512 29 1426
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk132 := witnessRule 29 23 0 640000 640136 32 1824
  0xffdff7ff 0x25491084442da8a21084 (by decide +kernel)
private def pack_E6970Receipt29_chunk133 := witnessRule 29 23 32 640192 640449 24 1147
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk134 := witnessRule 29 22 0 650000 650192 32 1731
  0xfffffbff 0x52922108c (by decide +kernel)
private def pack_E6970Receipt29_chunk135 := witnessRule 29 22 32 650193 650448 20 914
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk136 := witnessRule 29 21 0 660000 660194 32 1646
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk137 := witnessRule 29 21 32 660195 660448 16 701
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk138 := witnessRule 29 20 0 670000 670195 32 1550
  0xfffffdff 0x4a922908885 (by decide +kernel)
private def pack_E6970Receipt29_chunk139 := witnessRule 29 20 32 670196 670385 12 511
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk140 := witnessRule 29 19 0 680000 680197 32 1462
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk141 := witnessRule 29 19 32 680256 680384 8 333
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk142 := witnessRule 29 18 0 690000 690257 32 1385
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk143 := witnessRule 29 18 32 690258 690384 5 204
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk144 := witnessRule 29 17 0 700000 700320 32 1317
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk145 := witnessRule 29 17 32 700321 700321 1 40
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk146 := witnessRule 29 16 0 710000 710320 30 1176
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk147 := witnessRule 29 15 0 720000 720320 27 1014
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk148 := witnessRule 29 14 0 730000 730257 24 859
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk149 := witnessRule 29 13 0 740000 740256 21 717
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk150 := witnessRule 29 12 0 750000 750256 19 620
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk151 := witnessRule 29 11 0 760000 760193 16 498
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk152 := witnessRule 29 10 0 770000 770192 14 414
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk153 := witnessRule 29 9 0 780000 780192 12 340
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk154 := witnessRule 29 8 0 790000 790129 10 269
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk155 := witnessRule 29 7 0 800000 800128 8 205
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk156 := witnessRule 29 6 0 810000 810128 7 172
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk157 := witnessRule 29 5 0 820000 820065 5 117
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk158 := witnessRule 29 4 0 830000 830064 4 89
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk159 := witnessRule 29 3 0 840000 840064 3 64
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk160 := witnessRule 29 2 0 850000 850001 2 40
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk161 := witnessRule 29 1 0 860000 860000 1 19
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt29_chunk162 := witnessRule 29 0 0 870000 870000 1 18
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt29_chunks : List (Chunk 29) := [pack_E6970Receipt29_chunk0, pack_E6970Receipt29_chunk1, pack_E6970Receipt29_chunk2, pack_E6970Receipt29_chunk3, pack_E6970Receipt29_chunk4, pack_E6970Receipt29_chunk5, pack_E6970Receipt29_chunk6, pack_E6970Receipt29_chunk7, pack_E6970Receipt29_chunk8, pack_E6970Receipt29_chunk9, pack_E6970Receipt29_chunk10, pack_E6970Receipt29_chunk11, pack_E6970Receipt29_chunk12, pack_E6970Receipt29_chunk13, pack_E6970Receipt29_chunk14, pack_E6970Receipt29_chunk15, pack_E6970Receipt29_chunk16, pack_E6970Receipt29_chunk17, pack_E6970Receipt29_chunk18, pack_E6970Receipt29_chunk19, pack_E6970Receipt29_chunk20, pack_E6970Receipt29_chunk21, pack_E6970Receipt29_chunk22, pack_E6970Receipt29_chunk23, pack_E6970Receipt29_chunk24, pack_E6970Receipt29_chunk25, pack_E6970Receipt29_chunk26, pack_E6970Receipt29_chunk27, pack_E6970Receipt29_chunk28, pack_E6970Receipt29_chunk29, pack_E6970Receipt29_chunk30, pack_E6970Receipt29_chunk31, pack_E6970Receipt29_chunk32, pack_E6970Receipt29_chunk33, pack_E6970Receipt29_chunk34, pack_E6970Receipt29_chunk35, pack_E6970Receipt29_chunk36, pack_E6970Receipt29_chunk37, pack_E6970Receipt29_chunk38, pack_E6970Receipt29_chunk39, pack_E6970Receipt29_chunk40, pack_E6970Receipt29_chunk41, pack_E6970Receipt29_chunk42, pack_E6970Receipt29_chunk43, pack_E6970Receipt29_chunk44, pack_E6970Receipt29_chunk45, pack_E6970Receipt29_chunk46, pack_E6970Receipt29_chunk47, pack_E6970Receipt29_chunk48, pack_E6970Receipt29_chunk49, pack_E6970Receipt29_chunk50, pack_E6970Receipt29_chunk51, pack_E6970Receipt29_chunk52, pack_E6970Receipt29_chunk53, pack_E6970Receipt29_chunk54, pack_E6970Receipt29_chunk55, pack_E6970Receipt29_chunk56, pack_E6970Receipt29_chunk57, pack_E6970Receipt29_chunk58, pack_E6970Receipt29_chunk59, pack_E6970Receipt29_chunk60, pack_E6970Receipt29_chunk61, pack_E6970Receipt29_chunk62, pack_E6970Receipt29_chunk63, pack_E6970Receipt29_chunk64, pack_E6970Receipt29_chunk65, pack_E6970Receipt29_chunk66, pack_E6970Receipt29_chunk67, pack_E6970Receipt29_chunk68, pack_E6970Receipt29_chunk69, pack_E6970Receipt29_chunk70, pack_E6970Receipt29_chunk71, pack_E6970Receipt29_chunk72, pack_E6970Receipt29_chunk73, pack_E6970Receipt29_chunk74, pack_E6970Receipt29_chunk75, pack_E6970Receipt29_chunk76, pack_E6970Receipt29_chunk77, pack_E6970Receipt29_chunk78, pack_E6970Receipt29_chunk79, pack_E6970Receipt29_chunk80, pack_E6970Receipt29_chunk81, pack_E6970Receipt29_chunk82, pack_E6970Receipt29_chunk83, pack_E6970Receipt29_chunk84, pack_E6970Receipt29_chunk85, pack_E6970Receipt29_chunk86, pack_E6970Receipt29_chunk87, pack_E6970Receipt29_chunk88, pack_E6970Receipt29_chunk89, pack_E6970Receipt29_chunk90, pack_E6970Receipt29_chunk91, pack_E6970Receipt29_chunk92, pack_E6970Receipt29_chunk93, pack_E6970Receipt29_chunk94, pack_E6970Receipt29_chunk95, pack_E6970Receipt29_chunk96, pack_E6970Receipt29_chunk97, pack_E6970Receipt29_chunk98, pack_E6970Receipt29_chunk99, pack_E6970Receipt29_chunk100, pack_E6970Receipt29_chunk101, pack_E6970Receipt29_chunk102, pack_E6970Receipt29_chunk103, pack_E6970Receipt29_chunk104, pack_E6970Receipt29_chunk105, pack_E6970Receipt29_chunk106, pack_E6970Receipt29_chunk107, pack_E6970Receipt29_chunk108, pack_E6970Receipt29_chunk109, pack_E6970Receipt29_chunk110, pack_E6970Receipt29_chunk111, pack_E6970Receipt29_chunk112, pack_E6970Receipt29_chunk113, pack_E6970Receipt29_chunk114, pack_E6970Receipt29_chunk115, pack_E6970Receipt29_chunk116, pack_E6970Receipt29_chunk117, pack_E6970Receipt29_chunk118, pack_E6970Receipt29_chunk119, pack_E6970Receipt29_chunk120, pack_E6970Receipt29_chunk121, pack_E6970Receipt29_chunk122, pack_E6970Receipt29_chunk123, pack_E6970Receipt29_chunk124, pack_E6970Receipt29_chunk125, pack_E6970Receipt29_chunk126, pack_E6970Receipt29_chunk127, pack_E6970Receipt29_chunk128, pack_E6970Receipt29_chunk129, pack_E6970Receipt29_chunk130, pack_E6970Receipt29_chunk131, pack_E6970Receipt29_chunk132, pack_E6970Receipt29_chunk133, pack_E6970Receipt29_chunk134, pack_E6970Receipt29_chunk135, pack_E6970Receipt29_chunk136, pack_E6970Receipt29_chunk137, pack_E6970Receipt29_chunk138, pack_E6970Receipt29_chunk139, pack_E6970Receipt29_chunk140, pack_E6970Receipt29_chunk141, pack_E6970Receipt29_chunk142, pack_E6970Receipt29_chunk143, pack_E6970Receipt29_chunk144, pack_E6970Receipt29_chunk145, pack_E6970Receipt29_chunk146, pack_E6970Receipt29_chunk147, pack_E6970Receipt29_chunk148, pack_E6970Receipt29_chunk149, pack_E6970Receipt29_chunk150, pack_E6970Receipt29_chunk151, pack_E6970Receipt29_chunk152, pack_E6970Receipt29_chunk153, pack_E6970Receipt29_chunk154, pack_E6970Receipt29_chunk155, pack_E6970Receipt29_chunk156, pack_E6970Receipt29_chunk157, pack_E6970Receipt29_chunk158, pack_E6970Receipt29_chunk159, pack_E6970Receipt29_chunk160, pack_E6970Receipt29_chunk161, pack_E6970Receipt29_chunk162]
def rows29 := rowsFrom pack_E6970Receipt29_chunks
theorem good29 : ∀ r ∈ rows29, good 29 r = true := rowsFrom_good pack_E6970Receipt29_chunks
theorem sorted29 : rows29.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt29_chunks 0 (by decide +kernel)).1
theorem mass29 (i : Fin 61) :
    bandCount 29 (i.val : ℤ) 60 16 ≤ (rows29.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt29_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 29 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt29_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total29 : (rows29.map (price 29)).sum = 327366 :=
  (total_eq pack_E6970Receipt29_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt29

section Pack_E6970Receipt3

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt3_chunk0 := witnessRule 3 9 0 192 192 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt3_chunk1 := witnessRule 3 8 0 10129 10129 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt3_chunk2 := witnessRule 3 7 0 20066 20128 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt3_chunk3 := witnessRule 3 6 0 30003 30128 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt3_chunk4 := witnessRule 3 5 0 40002 40065 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt3_chunk5 := witnessRule 3 4 0 50001 50064 3 313
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt3_chunk6 := witnessRule 3 3 0 60000 60064 3 309
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt3_chunk7 := witnessRule 3 2 0 70000 70001 2 202
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt3_chunk8 := witnessRule 3 1 0 80000 80000 1 99
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt3_chunk9 := witnessRule 3 0 0 90000 90000 1 95
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt3_chunks : List (Chunk 3) := [pack_E6970Receipt3_chunk0, pack_E6970Receipt3_chunk1, pack_E6970Receipt3_chunk2, pack_E6970Receipt3_chunk3, pack_E6970Receipt3_chunk4, pack_E6970Receipt3_chunk5, pack_E6970Receipt3_chunk6, pack_E6970Receipt3_chunk7, pack_E6970Receipt3_chunk8, pack_E6970Receipt3_chunk9]
def rows3 := rowsFrom pack_E6970Receipt3_chunks
theorem good3 : ∀ r ∈ rows3, good 3 r = true := rowsFrom_good pack_E6970Receipt3_chunks
theorem sorted3 : rows3.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt3_chunks 0 (by decide +kernel)).1
theorem mass3 (i : Fin 61) :
    bandCount 3 (i.val : ℤ) 60 16 ≤ (rows3.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt3_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 3 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt3_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total3 : (rows3.map (price 3)).sum = 2080 :=
  (total_eq pack_E6970Receipt3_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt3

section Pack_E6970Receipt30

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt30_chunk0 := witnessA6966Final 30 60 0 300030 300651 32 3383
  0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk1 := witnessA6966Final 30 60 32 300652 300905 32 3325
  0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk2 := witnessA6966Final 30 60 64 300960 301030 15 1542
  0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk3 := witnessRule 30 59 0 310029 310589 32 3327
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk4 := witnessRule 30 59 32 310590 310897 32 3254
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk5 := witnessRule 30 59 64 310898 311029 21 2096
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk6 := witnessRule 30 58 0 320028 320527 32 3292
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk7 := witnessRule 30 58 32 320528 320835 32 3204
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk8 := witnessRule 30 58 64 320836 321029 28 2732
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk9 := witnessRule 30 57 0 330027 330466 32 3260
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk10 := witnessRule 30 57 32 330523 330774 32 3171
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk11 := witnessRule 30 57 64 330775 331027 32 3061
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk12 := witnessRule 30 57 96 331028 331028 1 94
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk13 := witnessRule 30 56 0 340026 340461 32 3243
  0xefffffff 0xa91a (by decide +kernel)
private def pack_E6970Receipt30_chunk14 := witnessRule 30 56 32 340462 340713 32 3129
  0xfffffbff 0x130aa (by decide +kernel)
private def pack_E6970Receipt30_chunk15 := witnessRule 30 56 64 340714 340963 32 3032
  0xfeffffff 0xb99a (by decide +kernel)
private def pack_E6970Receipt30_chunk16 := witnessRule 30 56 96 340964 341028 7 644
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk17 := witnessRule 30 55 0 350025 350401 32 3210
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk18 := witnessRule 30 55 32 350402 350707 32 3109
  0xefdfffff 0x14c8b0a91b (by decide +kernel)
private def pack_E6970Receipt30_chunk19 := witnessRule 30 55 64 350708 350901 32 2996
  0xdfbf7f5f 0xba1a17163364c668d8550b21a (by decide +kernel)
private def pack_E6970Receipt30_chunk20 := witnessRule 30 55 96 350902 351027 11 991
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk21 := witnessRule 30 54 0 360024 360397 32 3193
  0xdfbfffff 0x58944d9291a (by decide +kernel)
private def pack_E6970Receipt30_chunk22 := witnessRule 30 54 32 360398 360647 32 3084
  0xf7f3f7e7 0x98544c421312a1615231082c4a26c98951291a (by decide +kernel)
private def pack_E6970Receipt30_chunk23 := witnessRule 30 54 64 360648 360839 32 2965
  0x9fbfffef 0x26331062ca6898548d9b0a883 (by decide +kernel)
private def pack_E6970Receipt30_chunk24 := witnessRule 30 54 96 360896 361027 16 1417
  0xfffb 0xba9a (by decide +kernel)
private def pack_E6970Receipt30_chunk25 := witnessRule 30 53 0 370023 370338 32 3156
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk26 := witnessRule 30 53 32 370339 370588 32 3049
  0x3f5fbfff 0xb1291b1716251384c4a26c5c948d8b1291b (by decide +kernel)
private def pack_E6970Receipt30_chunk27 := witnessRule 30 53 64 370589 370834 32 2960
  0xe3f1fc7e 0xd8544c42130a99b1716152310a6c4a898548c420b0aa1b26251362e4c4ac554d1b12a (by decide +kernel)
private def pack_E6970Receipt30_chunk28 := witnessRule 30 53 96 370835 371026 19 1647
  0x7fef9 0x2ca620c58550d8b8b0a99c (by decide +kernel)
private def pack_E6970Receipt30_chunk29 := witnessRule 30 52 0 380022 380334 32 3142
  0xf7ffffff 0x1a91a (by decide +kernel)
private def pack_E6970Receipt30_chunk30 := witnessRule 30 52 32 380335 380582 32 3029
  0xe7f7f3f7 0x98d50b129188416351364c6a8d48d0b1a89b (by decide +kernel)
private def pack_E6970Receipt30_chunk31 := witnessRule 30 52 64 380583 380773 32 2921
  0x7d7f3fdf 0x558d1b1289b1716252386c4a20c98948d931289884 (by decide +kernel)
private def pack_E6970Receipt30_chunk32 := witnessRule 30 52 96 380774 381026 23 1966
  0x7fee3d 0xab1a2615331082c2aa6c5c550c42131291b (by decide +kernel)
private def pack_E6970Receipt30_chunk33 := witnessRule 30 51 0 390021 390331 32 3108
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk34 := witnessRule 30 51 32 390332 390524 32 2992
  0xbfbfffff 0x5cd48d8b1a91b (by decide +kernel)
private def pack_E6970Receipt30_chunk35 := witnessRule 30 51 64 390525 390768 32 2905
  0xcfe3f8fe 0x13129188416254364c6a26c5c98d592a9a363542c6a46c5c58d44e131a89b (by decide +kernel)
private def pack_E6970Receipt30_chunk36 := witnessRule 30 51 96 390769 391025 25 2104
  0x1fe71d7 0x2c2aa621055cd0b12a1b15631062e2a288709894cd8b92a1b (by decide +kernel)
private def pack_E6970Receipt30_chunk37 := witnessRule 30 50 0 400020 400273 32 3082
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk38 := witnessRule 30 50 32 400274 400519 32 2990
  0xf7f9fdfe 0xb2289b264548a46859144da291a (by decide +kernel)
private def pack_E6970Receipt30_chunk39 := witnessRule 30 50 64 400520 400708 32 2868
  0xf9ff7fcf 0x1b1a88326352364c6a2621099150b1a91884 (by decide +kernel)
private def pack_E6970Receipt30_chunk40 := witnessRule 30 50 96 400709 401025 28 2311
  0xff63cf1 0xab19031625332082c4aa6c5c950c420b12a1884256344c6a2621058d4cd8b8b1a91c (by decide +kernel)
private def pack_E6970Receipt30_chunk41 := witnessRule 30 49 0 410019 410270 32 3068
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk42 := witnessRule 30 49 32 410271 410462 32 2912
  0xbfffffff 0xb2291b (by decide +kernel)
private def pack_E6970Receipt30_chunk43 := witnessRule 30 49 64 410515 410704 32 2864
  0xafe3fd7f 0x4c8a26cd54d1b22a16452362e2c8a27099144d8ba291b (by decide +kernel)
private def pack_E6970Receipt30_chunk44 := witnessRule 30 49 96 410705 411024 29 2362
  0x1ff8c78f 0xb12a190425631062e2a288623458d4cc421aa9a17354364c6a4621058d50d8b9a99884 (by decide +kernel)
private def pack_E6970Receipt30_chunk45 := witnessRule 30 48 0 420018 420267 32 3034
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk46 := witnessRule 30 48 32 420268 420457 32 2929
  0xfcff7fdf 0x26554aa46859544daa91a (by decide +kernel)
private def pack_E6970Receipt30_chunk47 := witnessRule 30 48 64 420458 420645 32 2815
  0xfdff9ff7 0x2645131084caa859148c420b2a89b (by decide +kernel)
private def pack_E6970Receipt30_chunk48 := witnessRule 30 48 96 420646 421024 31 2473
  0x7f8e7afa 0xb1299a042553306302a862221458d50c421ab1a16453362e6a2867099148d8ba299b (by decide +kernel)
private def pack_E6970Receipt30_chunk49 := witnessRule 30 47 0 430017 430211 32 2980
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk50 := witnessRule 30 47 32 430265 430453 32 2933
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk51 := witnessRule 30 47 64 430454 430641 32 2769
  0xe7faffbf 0xb2a91b1716551384caa26c5d548d8b2a91b (by decide +kernel)
private def pack_E6970Receipt30_chunk52 := witnessRule 30 47 96 430642 430961 31 2433
  0x7f51e7df 0x254350630288643058d4ccc21aa99031825431182c8a86c5d14cc420b2299884 (by decide +kernel)
private def pack_E6970Receipt30_chunk53 := witnessRule 30 46 0 440016 440208 32 2975
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk54 := witnessRule 30 46 32 440209 440397 32 2848
  0x7fdffbff 0xca46859944db291a (by decide +kernel)
private def pack_E6970Receipt30_chunk55 := witnessRule 30 46 64 440398 440583 32 2773
  0xff3ff7fe 0x266542caa4621059944d9332a (by decide +kernel)
private def pack_E6970Receipt30_chunk56 := witnessRule 30 46 96 440584 440960 32 2473
  0xffce3e7c 0x1aa1a031825331120a2c8a66411154c418b9a8a1988d554342eaa66c99544c420b2a99b (by decide +kernel)
private def pack_E6970Receipt30_chunk57 := witnessRule 30 45 0 450015 450206 32 2967
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk58 := witnessRule 30 45 32 450207 450393 32 2840
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk59 := witnessRule 30 45 64 450394 450580 32 2706
  0xfaffbfff 0x4cca26c5d948d8b3291b (by decide +kernel)
private def pack_E6970Receipt30_chunk60 := witnessRule 30 45 96 450581 450960 32 2413
  0xff5cf3f5 0x3533606302a286642219150cc18c1a9988885165533108aaa6859948d8baa8a11c (by decide +kernel)
private def pack_E6970Receipt30_chunk61 := witnessRule 30 44 0 460014 460203 32 2935
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk62 := witnessRule 30 44 32 460204 460389 32 2822
  0xf7ff7fff 0x59d44dba91a (by decide +kernel)
private def pack_E6970Receipt30_chunk63 := witnessRule 30 44 64 460390 460576 32 2648
  0xdff7ff3f 0x1665231082cea26c99d53a91a (by decide +kernel)
private def pack_E6970Receipt30_chunk64 := witnessRule 30 44 96 460577 460897 32 2387
  0xff6bcfbf 0x6054508c84c32299a831825143321aaa8640c6114cc460b3299b (by decide +kernel)
private def pack_E6970Receipt30_chunk65 := witnessRule 30 43 0 470013 470201 32 2911
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk66 := witnessRule 30 43 32 470202 470385 32 2752
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk67 := witnessRule 30 43 64 470386 470520 32 2634
  0x7fdfffff 0x1d4cd0b3a91b (by decide +kernel)
private def pack_E6970Receipt30_chunk68 := witnessRule 30 43 96 470521 470896 31 2269
  0x7ff77f3f 0x182514232120caa6680d950c418baa8a1188d (by decide +kernel)
private def pack_E6970Receipt30_chunk69 := witnessRule 30 42 0 480012 480198 32 2847
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk70 := witnessRule 30 42 32 480199 480331 32 2771
  0xffefffff 0x4291a (by decide +kernel)
private def pack_E6970Receipt30_chunk71 := witnessRule 30 42 64 480332 480517 32 2600
  0xfdff9ffd 0x16851364d0aa148d0b4289b (by decide +kernel)
private def pack_E6970Receipt30_chunk72 := witnessRule 30 42 96 480518 480896 31 2207
  0x7fff7bfd 0x306a28464221994ccc1baa1a (by decide +kernel)
private def pack_E6970Receipt30_chunk73 := witnessRule 30 41 0 490011 490145 32 2807
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk74 := witnessRule 30 41 32 490197 490328 32 2793
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk75 := witnessRule 30 41 64 490329 490515 32 2498
  0xfbffffff 0xb4291b (by decide +kernel)
private def pack_E6970Receipt30_chunk76 := witnessRule 30 41 96 490516 490833 29 2019
  0x1ffffdf7 0x6114508c86ba99903 (by decide +kernel)
private def pack_E6970Receipt30_chunk77 := witnessRule 30 40 0 500010 500143 32 2804
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk78 := witnessRule 30 40 32 500144 500324 32 2738
  0xfdffffff 0x4a91a (by decide +kernel)
private def pack_E6970Receipt30_chunk79 := witnessRule 30 40 64 500325 500513 32 2439
  0xeffbff7f 0x10a6620e548d0b4a89b (by decide +kernel)
private def pack_E6970Receipt30_chunk80 := witnessRule 30 40 96 500514 500832 28 1917
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk81 := witnessRule 30 39 0 510009 510141 32 2798
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk82 := witnessRule 30 39 32 510142 510322 32 2666
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk83 := witnessRule 30 39 64 510323 510512 32 2373
  0xfff7ffff 0x4a99a (by decide +kernel)
private def pack_E6970Receipt30_chunk84 := witnessRule 30 39 96 510513 510832 26 1749
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk85 := witnessRule 30 38 0 520008 520139 32 2784
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk86 := witnessRule 30 38 32 520140 520269 32 2562
  0xbfffffff 0x5291a (by decide +kernel)
private def pack_E6970Receipt30_chunk87 := witnessRule 30 38 64 520320 520456 32 2358
  0xffdff7ff 0x2548c818b5289b (by decide +kernel)
private def pack_E6970Receipt30_chunk88 := witnessRule 30 38 96 520512 520769 24 1584
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk89 := witnessRule 30 37 0 530007 530137 32 2766
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk90 := witnessRule 30 37 32 530138 530267 32 2526
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk91 := witnessRule 30 37 64 530268 530456 32 2258
  0xfffff7ff 0x5291883 (by decide +kernel)
private def pack_E6970Receipt30_chunk92 := witnessRule 30 37 96 530512 530768 21 1356
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk93 := witnessRule 30 36 0 540006 540135 32 2740
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk94 := witnessRule 30 36 32 540136 540265 32 2502
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk95 := witnessRule 30 36 64 540266 540455 32 2163
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk96 := witnessRule 30 36 96 540512 540768 19 1199
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk97 := witnessRule 30 35 0 550005 550133 32 2710
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk98 := witnessRule 30 35 32 550134 550264 32 2434
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk99 := witnessRule 30 35 64 550265 550512 32 2086
  0xffffeffb 0x25490c1da89903 (by decide +kernel)
private def pack_E6970Receipt30_chunk100 := witnessRule 30 35 96 550513 550705 15 920
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk101 := witnessRule 30 34 0 560004 560131 32 2672
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk102 := witnessRule 30 34 32 560132 560263 32 2378
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk103 := witnessRule 30 34 64 560264 560513 32 2010
  0xfffffffb 0x5292103 (by decide +kernel)
private def pack_E6970Receipt30_chunk104 := witnessRule 30 34 96 560514 560704 12 721
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk105 := witnessRule 30 33 0 570003 570130 32 2618
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk106 := witnessRule 30 33 32 570131 570263 32 2297
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk107 := witnessRule 30 33 64 570264 570515 32 1938
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk108 := witnessRule 30 33 96 570516 570704 8 475
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk109 := witnessRule 30 32 0 580002 580129 32 2564
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk110 := witnessRule 30 32 32 580130 580263 32 2219
  0xff7ffbff 0x2d450448262922 (by decide +kernel)
private def pack_E6970Receipt30_chunk111 := witnessRule 30 32 64 580264 580576 32 1872
  0xfffffffd 0x4a9209184 (by decide +kernel)
private def pack_E6970Receipt30_chunk112 := witnessRule 30 32 96 580577 580641 4 234
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk113 := witnessRule 30 31 0 590001 590129 32 2498
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk114 := witnessRule 30 31 32 590130 590264 32 2108
  0xffdfffff 0x529209104 (by decide +kernel)
private def pack_E6970Receipt30_chunk115 := witnessRule 30 31 64 590265 590640 31 1771
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk116 := witnessRule 30 30 0 600000 600129 32 2433
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk117 := witnessRule 30 30 32 600130 600265 32 2002
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk118 := witnessRule 30 30 64 600320 600640 27 1504
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk119 := witnessRule 30 29 0 610000 610130 32 2344
  0xf7ffffff 0x6292093 (by decide +kernel)
private def pack_E6970Receipt30_chunk120 := witnessRule 30 29 32 610131 610322 32 1904
  0xfffbfeff 0x2549088c25a8a0908905 (by decide +kernel)
private def pack_E6970Receipt30_chunk121 := witnessRule 30 29 64 610323 610577 21 1116
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk122 := witnessRule 30 28 0 620000 620131 32 2249
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk123 := witnessRule 30 28 32 620132 620324 32 1791
  0xffffffbf 0x529211104 (by decide +kernel)
private def pack_E6970Receipt30_chunk124 := witnessRule 30 28 64 620325 620576 16 832
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk125 := witnessRule 30 27 0 630000 630132 32 2149
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk126 := witnessRule 30 27 32 630133 630384 32 1697
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk127 := witnessRule 30 27 64 630385 630576 11 561
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk128 := witnessRule 30 26 0 640000 640133 32 2042
  0xfdffefff 0x2d450884482e292113 (by decide +kernel)
private def pack_E6970Receipt30_chunk129 := witnessRule 30 26 32 640134 640387 32 1616
  0xfffffff7 0x4a9219184 (by decide +kernel)
private def pack_E6970Receipt30_chunk130 := witnessRule 30 26 64 640388 640513 6 301
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk131 := witnessRule 30 25 0 650000 650134 32 1933
  0xff7fffff 0x529219104 (by decide +kernel)
private def pack_E6970Receipt30_chunk132 := witnessRule 30 25 32 650135 650450 32 1562
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk133 := witnessRule 30 25 64 650512 650512 1 50
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk134 := witnessRule 30 24 0 660000 660135 32 1822
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk135 := witnessRule 30 24 32 660136 660512 29 1374
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk136 := witnessRule 30 23 0 670000 670136 32 1717
  0xffdff7ff 0x2549108c25a8a1908905 (by decide +kernel)
private def pack_E6970Receipt30_chunk137 := witnessRule 30 23 32 670192 670449 24 1104
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk138 := witnessRule 30 22 0 680000 680192 32 1631
  0xfffffbff 0x529221104 (by decide +kernel)
private def pack_E6970Receipt30_chunk139 := witnessRule 30 22 32 680193 680448 20 884
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk140 := witnessRule 30 21 0 690000 690194 32 1548
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk141 := witnessRule 30 21 32 690195 690448 16 681
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk142 := witnessRule 30 20 0 700000 700195 32 1458
  0xfffffdff 0x4a9229184 (by decide +kernel)
private def pack_E6970Receipt30_chunk143 := witnessRule 30 20 32 700196 700385 12 497
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk144 := witnessRule 30 19 0 710000 710197 32 1381
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk145 := witnessRule 30 19 32 710256 710384 8 325
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk146 := witnessRule 30 18 0 720000 720257 32 1310
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk147 := witnessRule 30 18 32 720258 720384 5 199
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk148 := witnessRule 30 17 0 730000 730320 32 1248
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk149 := witnessRule 30 17 32 730321 730321 1 39
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk150 := witnessRule 30 16 0 740000 740320 30 1119
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk151 := witnessRule 30 15 0 750000 750320 27 964
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk152 := witnessRule 30 14 0 760000 760257 24 816
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk153 := witnessRule 30 13 0 770000 770256 21 684
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk154 := witnessRule 30 12 0 780000 780256 19 591
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk155 := witnessRule 30 11 0 790000 790193 16 474
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk156 := witnessRule 30 10 0 800000 800192 14 396
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk157 := witnessRule 30 9 0 810000 810192 12 325
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk158 := witnessRule 30 8 0 820000 820129 10 257
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk159 := witnessRule 30 7 0 830000 830128 8 197
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk160 := witnessRule 30 6 0 840000 840128 7 165
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk161 := witnessRule 30 5 0 850000 850065 5 112
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk162 := witnessRule 30 4 0 860000 860064 4 85
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk163 := witnessRule 30 3 0 870000 870064 3 61
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk164 := witnessRule 30 2 0 880000 880001 2 38
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk165 := witnessRule 30 1 0 890000 890000 1 18
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt30_chunk166 := witnessRule 30 0 0 900000 900000 1 17
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt30_chunks : List (Chunk 30) := [pack_E6970Receipt30_chunk0, pack_E6970Receipt30_chunk1, pack_E6970Receipt30_chunk2, pack_E6970Receipt30_chunk3, pack_E6970Receipt30_chunk4, pack_E6970Receipt30_chunk5, pack_E6970Receipt30_chunk6, pack_E6970Receipt30_chunk7, pack_E6970Receipt30_chunk8, pack_E6970Receipt30_chunk9, pack_E6970Receipt30_chunk10, pack_E6970Receipt30_chunk11, pack_E6970Receipt30_chunk12, pack_E6970Receipt30_chunk13, pack_E6970Receipt30_chunk14, pack_E6970Receipt30_chunk15, pack_E6970Receipt30_chunk16, pack_E6970Receipt30_chunk17, pack_E6970Receipt30_chunk18, pack_E6970Receipt30_chunk19, pack_E6970Receipt30_chunk20, pack_E6970Receipt30_chunk21, pack_E6970Receipt30_chunk22, pack_E6970Receipt30_chunk23, pack_E6970Receipt30_chunk24, pack_E6970Receipt30_chunk25, pack_E6970Receipt30_chunk26, pack_E6970Receipt30_chunk27, pack_E6970Receipt30_chunk28, pack_E6970Receipt30_chunk29, pack_E6970Receipt30_chunk30, pack_E6970Receipt30_chunk31, pack_E6970Receipt30_chunk32, pack_E6970Receipt30_chunk33, pack_E6970Receipt30_chunk34, pack_E6970Receipt30_chunk35, pack_E6970Receipt30_chunk36, pack_E6970Receipt30_chunk37, pack_E6970Receipt30_chunk38, pack_E6970Receipt30_chunk39, pack_E6970Receipt30_chunk40, pack_E6970Receipt30_chunk41, pack_E6970Receipt30_chunk42, pack_E6970Receipt30_chunk43, pack_E6970Receipt30_chunk44, pack_E6970Receipt30_chunk45, pack_E6970Receipt30_chunk46, pack_E6970Receipt30_chunk47, pack_E6970Receipt30_chunk48, pack_E6970Receipt30_chunk49, pack_E6970Receipt30_chunk50, pack_E6970Receipt30_chunk51, pack_E6970Receipt30_chunk52, pack_E6970Receipt30_chunk53, pack_E6970Receipt30_chunk54, pack_E6970Receipt30_chunk55, pack_E6970Receipt30_chunk56, pack_E6970Receipt30_chunk57, pack_E6970Receipt30_chunk58, pack_E6970Receipt30_chunk59, pack_E6970Receipt30_chunk60, pack_E6970Receipt30_chunk61, pack_E6970Receipt30_chunk62, pack_E6970Receipt30_chunk63, pack_E6970Receipt30_chunk64, pack_E6970Receipt30_chunk65, pack_E6970Receipt30_chunk66, pack_E6970Receipt30_chunk67, pack_E6970Receipt30_chunk68, pack_E6970Receipt30_chunk69, pack_E6970Receipt30_chunk70, pack_E6970Receipt30_chunk71, pack_E6970Receipt30_chunk72, pack_E6970Receipt30_chunk73, pack_E6970Receipt30_chunk74, pack_E6970Receipt30_chunk75, pack_E6970Receipt30_chunk76, pack_E6970Receipt30_chunk77, pack_E6970Receipt30_chunk78, pack_E6970Receipt30_chunk79, pack_E6970Receipt30_chunk80, pack_E6970Receipt30_chunk81, pack_E6970Receipt30_chunk82, pack_E6970Receipt30_chunk83, pack_E6970Receipt30_chunk84, pack_E6970Receipt30_chunk85, pack_E6970Receipt30_chunk86, pack_E6970Receipt30_chunk87, pack_E6970Receipt30_chunk88, pack_E6970Receipt30_chunk89, pack_E6970Receipt30_chunk90, pack_E6970Receipt30_chunk91, pack_E6970Receipt30_chunk92, pack_E6970Receipt30_chunk93, pack_E6970Receipt30_chunk94, pack_E6970Receipt30_chunk95, pack_E6970Receipt30_chunk96, pack_E6970Receipt30_chunk97, pack_E6970Receipt30_chunk98, pack_E6970Receipt30_chunk99, pack_E6970Receipt30_chunk100, pack_E6970Receipt30_chunk101, pack_E6970Receipt30_chunk102, pack_E6970Receipt30_chunk103, pack_E6970Receipt30_chunk104, pack_E6970Receipt30_chunk105, pack_E6970Receipt30_chunk106, pack_E6970Receipt30_chunk107, pack_E6970Receipt30_chunk108, pack_E6970Receipt30_chunk109, pack_E6970Receipt30_chunk110, pack_E6970Receipt30_chunk111, pack_E6970Receipt30_chunk112, pack_E6970Receipt30_chunk113, pack_E6970Receipt30_chunk114, pack_E6970Receipt30_chunk115, pack_E6970Receipt30_chunk116, pack_E6970Receipt30_chunk117, pack_E6970Receipt30_chunk118, pack_E6970Receipt30_chunk119, pack_E6970Receipt30_chunk120, pack_E6970Receipt30_chunk121, pack_E6970Receipt30_chunk122, pack_E6970Receipt30_chunk123, pack_E6970Receipt30_chunk124, pack_E6970Receipt30_chunk125, pack_E6970Receipt30_chunk126, pack_E6970Receipt30_chunk127, pack_E6970Receipt30_chunk128, pack_E6970Receipt30_chunk129, pack_E6970Receipt30_chunk130, pack_E6970Receipt30_chunk131, pack_E6970Receipt30_chunk132, pack_E6970Receipt30_chunk133, pack_E6970Receipt30_chunk134, pack_E6970Receipt30_chunk135, pack_E6970Receipt30_chunk136, pack_E6970Receipt30_chunk137, pack_E6970Receipt30_chunk138, pack_E6970Receipt30_chunk139, pack_E6970Receipt30_chunk140, pack_E6970Receipt30_chunk141, pack_E6970Receipt30_chunk142, pack_E6970Receipt30_chunk143, pack_E6970Receipt30_chunk144, pack_E6970Receipt30_chunk145, pack_E6970Receipt30_chunk146, pack_E6970Receipt30_chunk147, pack_E6970Receipt30_chunk148, pack_E6970Receipt30_chunk149, pack_E6970Receipt30_chunk150, pack_E6970Receipt30_chunk151, pack_E6970Receipt30_chunk152, pack_E6970Receipt30_chunk153, pack_E6970Receipt30_chunk154, pack_E6970Receipt30_chunk155, pack_E6970Receipt30_chunk156, pack_E6970Receipt30_chunk157, pack_E6970Receipt30_chunk158, pack_E6970Receipt30_chunk159, pack_E6970Receipt30_chunk160, pack_E6970Receipt30_chunk161, pack_E6970Receipt30_chunk162, pack_E6970Receipt30_chunk163, pack_E6970Receipt30_chunk164, pack_E6970Receipt30_chunk165, pack_E6970Receipt30_chunk166]
def rows30 := rowsFrom pack_E6970Receipt30_chunks
theorem good30 : ∀ r ∈ rows30, good 30 r = true := rowsFrom_good pack_E6970Receipt30_chunks
theorem sorted30 : rows30.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt30_chunks 0 (by decide +kernel)).1
theorem mass30 (i : Fin 61) :
    bandCount 30 (i.val : ℤ) 60 16 ≤ (rows30.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt30_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 30 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt30_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total30 : (rows30.map (price 30)).sum = 342881 :=
  (total_eq pack_E6970Receipt30_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt30

section Pack_E6970Receipt31

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt31_chunk0 := witnessA6966Final 31 60 0 330029 330528 32 3378
  0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk1 := witnessA6966Final 31 60 32 330529 330836 32 3329
  0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk2 := witnessA6966Final 31 60 64 330837 331030 30 3069
  0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk3 := witnessRule 31 59 0 340028 340467 32 3310
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk4 := witnessRule 31 59 32 340524 340775 32 3258
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk5 := witnessRule 31 59 64 340776 341025 32 3195
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk6 := witnessRule 31 59 96 341026 341029 4 390
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk7 := witnessRule 31 58 0 350027 350462 32 3279
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk8 := witnessRule 31 58 32 350463 350714 32 3188
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk9 := witnessRule 31 58 64 350715 350962 32 3131
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk10 := witnessRule 31 58 96 350963 351029 10 955
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk11 := witnessRule 31 57 0 360026 360402 32 3242
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk12 := witnessRule 31 57 32 360403 360708 32 3153
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk13 := witnessRule 31 57 64 360709 360900 32 3079
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk14 := witnessRule 31 57 96 360901 361028 15 1401
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk15 := witnessRule 31 56 0 370025 370398 32 3220
  0xffbfffff 0xa91a (by decide +kernel)
private def pack_E6970Receipt31_chunk16 := witnessRule 31 56 32 370399 370648 32 3123
  0xffffffef 0x130aa (by decide +kernel)
private def pack_E6970Receipt31_chunk17 := witnessRule 31 56 64 370649 370839 32 3029
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk18 := witnessRule 31 56 96 370840 371028 20 1829
  0xfffdf 0xb99a (by decide +kernel)
private def pack_E6970Receipt31_chunk19 := witnessRule 31 55 0 380024 380339 32 3180
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk20 := witnessRule 31 55 32 380340 380589 32 3086
  0xbfdfbfff 0x2c8694c8b0a91b (by decide +kernel)
private def pack_E6970Receipt31_chunk21 := witnessRule 31 55 64 380590 380833 32 3026
  0xfffffefe 0x98cd1b0aa (by decide +kernel)
private def pack_E6970Receipt31_chunk22 := witnessRule 31 55 96 380834 381027 24 2144
  0xfffbf7 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt31_chunk23 := witnessRule 31 54 0 390023 390335 32 3163
  0xe7dfbfff 0x262544a46858944d9291a (by decide +kernel)
private def pack_E6970Receipt31_chunk24 := witnessRule 31 54 32 390336 390583 32 3064
  0xeff7f3f7 0x1b0a8832615131084c4a858548c420b1289b (by decide +kernel)
private def pack_E6970Receipt31_chunk25 := witnessRule 31 54 64 390584 390773 32 2976
  0x7f5fbfff 0x175342ca68dc5441930a91b (by decide +kernel)
private def pack_E6970Receipt31_chunk26 := witnessRule 31 54 96 390774 391027 28 2457
  0xfffbefd 0x2ea685c590d9321a (by decide +kernel)
private def pack_E6970Receipt31_chunk27 := witnessRule 31 53 0 400022 400332 32 3127
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk28 := witnessRule 31 53 32 400333 400525 32 3022
  0x3f1fafdf 0x17262562aa68d8950b1291b1716251384c4a26c5c948d8b1291b (by decide +kernel)
private def pack_E6970Receipt31_chunk29 := witnessRule 31 53 64 400526 400714 32 2956
  0x5fe3f8fe 0x230a8831726151310a6c2a262109854cd8b8b0a91885362544c2a4621058550d931289b (by decide +kernel)
private def pack_E6970Receipt31_chunk30 := witnessRule 31 53 96 400768 401026 31 2691
  0x7ffb9f6f 0xbb1a26431062cc689854cd938a99b (by decide +kernel)
private def pack_E6970Receipt31_chunk31 := witnessRule 31 52 0 410021 410274 32 3098
  0xfdfdffff 0x58d44d9a91a (by decide +kernel)
private def pack_E6970Receipt31_chunk32 := witnessRule 31 52 32 410275 410520 32 3019
  0xf7f9fdfc 0x98944c42131aa1625231082c6a26c98d51a91a (by decide +kernel)
private def pack_E6970Receipt31_chunk33 := witnessRule 31 52 64 410521 410708 32 2920
  0xf8bf5fcf 0x462544c4a46c5c98944e139291b36251362e2c4a470d89441931291b (by decide +kernel)
private def pack_E6970Receipt31_chunk34 := witnessRule 31 52 96 410709 411024 32 2710
  0xff79e3e9 0xb3188316155362e2c2a870d8548c42130aa1b1716153310a6c4a26c58554d938b1289c (by decide +kernel)
private def pack_E6970Receipt31_chunk35 := witnessRule 31 52 128 411025 411026 2 171
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk36 := witnessRule 31 51 0 420020 420271 32 3081
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk37 := witnessRule 31 51 32 420272 420463 32 2942
  0x1fd7f7ff 0xd8d50b1a91b1716351384c6a26c5cd48d8b1a91b (by decide +kernel)
private def pack_E6970Receipt31_chunk38 := witnessRule 31 51 64 420516 420650 32 2908
  0x1fe3fc7f 0x1b128988426253362e2c4a46214d8d513129188416254364c6a26c5c98d592a9a (by decide +kernel)
private def pack_E6970Receipt31_chunk39 := witnessRule 31 51 96 420704 420961 32 2689
  0xfb8ebe3f 0xab9a2615431082c2ac6c5c554c42131299b157346c4a46c5c98944c428b8b1299c (by decide +kernel)
private def pack_E6970Receipt31_chunk40 := witnessRule 31 51 128 420962 421025 4 334
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk41 := witnessRule 31 50 0 430019 430268 32 3049
  0xdfefffff 0x59144da291a (by decide +kernel)
private def pack_E6970Receipt31_chunk42 := witnessRule 31 50 32 430269 430458 32 2950
  0xfcff7f9f 0x1322a1635231082c8a26c99152291a (by decide +kernel)
private def pack_E6970Receipt31_chunk43 := witnessRule 31 50 64 430459 430645 32 2868
  0xfd7f9ff7 0x1b1a89b1716352386c6a20c98d48d931a89884 (by decide +kernel)
private def pack_E6970Receipt31_chunk44 := witnessRule 31 50 96 430646 430899 32 2620
  0xfc71c5e2 0x58954d8ab98831715145384c4a86c5c5894cc428b92a9b3625132084c4a6621058954d93928a11c36351064c6a46c5c98d44e139a91b (by decide +kernel)
private def pack_E6970Receipt31_chunk45 := witnessRule 31 50 128 430900 431025 6 491
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk46 := witnessRule 31 49 0 440018 440212 32 2993
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk47 := witnessRule 31 49 32 440266 440454 32 2954
  0xebfdffff 0x4c8a26c5d148d8b2291b (by decide +kernel)
private def pack_E6970Receipt31_chunk48 := witnessRule 31 49 64 440455 440640 32 2818
  0x8ff8ff1f 0x1b22a2635231082c6a86c99144d8b9322b355346c8a859148d8b8b2289c (by decide +kernel)
private def pack_E6970Receipt31_chunk49 := witnessRule 31 49 96 440641 440896 32 2596
  0xe31e3e3f 0x1625432084ac620c60554c421312999041625531084ae6898d48c420b1aa1b1716353386c6a2621098d4cd8b8b1a91885 (by decide +kernel)
private def pack_E6970Receipt31_chunk50 := witnessRule 31 49 128 440897 441024 7 560
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk51 := witnessRule 31 48 0 450017 450209 32 2986
  0xff7fffff 0x2a91a (by decide +kernel)
private def pack_E6970Receipt31_chunk52 := witnessRule 31 48 32 450210 450398 32 2870
  0x7fdff3fd 0xb229188416551364caa9548d0b2a89b (by decide +kernel)
private def pack_E6970Receipt31_chunk53 := witnessRule 31 48 64 450399 450583 32 2826
  0xff3ff7fe 0x36451064c8a46c99144c42132aa (by decide +kernel)
private def pack_E6970Receipt31_chunk54 := witnessRule 31 48 96 450584 450835 32 2538
  0xac70f5fa 0x12a99831814531182c6a86210d58d0c12a9b2635331082c6aa6c5cd50c4213928a1188d26452366ac68d9144d8b8b2291c (by decide +kernel)
private def pack_E6970Receipt31_chunk55 := witnessRule 31 48 128 450836 451024 8 629
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk56 := witnessRule 31 47 0 460016 460207 32 2974
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk57 := witnessRule 31 47 32 460208 460394 32 2860
  0xff7fffff 0xb2a91b (by decide +kernel)
private def pack_E6970Receipt31_chunk58 := witnessRule 31 47 64 460395 460579 32 2775
  0xf1ff1ff5 0x26551362e4caad154d1b2aa16552362e2caa27099544d8baa91b (by decide +kernel)
private def pack_E6970Receipt31_chunk59 := witnessRule 31 47 96 460580 460833 32 2482
  0xe3c7afcf 0x58d4ccc21aa99031825432082c8a86cd58c418b9a8a21c26453362e8a86c99148c420b22a1b (by decide +kernel)
private def pack_E6970Receipt31_chunk60 := witnessRule 31 47 128 460834 460961 8 616
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk61 := witnessRule 31 46 0 470015 470204 32 2946
  0xfbffffff 0x3291a (by decide +kernel)
private def pack_E6970Receipt31_chunk62 := witnessRule 31 46 32 470205 470390 32 2838
  0xf7fe7fdf 0x16651364cca9948d0b3289b (by decide +kernel)
private def pack_E6970Receipt31_chunk63 := witnessRule 31 46 64 470391 470523 32 2687
  0x3ff7ff3f 0x1b2a88326552364caa2621099950b2a91884 (by decide +kernel)
private def pack_E6970Receipt31_chunk64 := witnessRule 31 46 96 470576 470773 32 2472
  0xc61e7c7f 0x3543406304a668106054510c44430b22999044553106306a862109c94508c868b22a1884456344caa262105954cd8b8b2a91c (by decide +kernel)
private def pack_E6970Receipt31_chunk65 := witnessRule 31 46 128 470832 470960 8 605
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk66 := witnessRule 31 45 0 480014 480202 32 2918
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk67 := witnessRule 31 45 32 480203 480386 32 2772
  0xdfffffff 0xb3291b (by decide +kernel)
private def pack_E6970Receipt31_chunk68 := witnessRule 31 45 64 480387 480519 32 2718
  0xff1ffaff 0x1b32a16652362e2cca27099944d8bb291b (by decide +kernel)
private def pack_E6970Receipt31_chunk69 := witnessRule 31 45 96 480520 480771 32 2395
  0x5c71f1fa 0x1a99b03181514331130c8a8660c60d4ccc20c128a2188d165533108aaa6861150d932a9188416554362eaa6621099944daaa9a (by decide +kernel)
private def pack_E6970Receipt31_chunk70 := witnessRule 31 45 128 480772 480960 8 595
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk71 := witnessRule 31 44 0 490013 490199 32 2858
  0xdfffffff 0x3a91a (by decide +kernel)
private def pack_E6970Receipt31_chunk72 := witnessRule 31 44 32 490200 490332 32 2782
  0xffcffdff 0x4cea9d48d0b3a89b (by decide +kernel)
private def pack_E6970Receipt31_chunk73 := witnessRule 31 44 64 490333 490516 32 2673
  0xfbff9ffd 0x2665131084cea859948c420b3a89b (by decide +kernel)
private def pack_E6970Receipt31_chunk74 := witnessRule 31 44 96 490517 490770 32 2333
  0xf4e7d7eb 0x2299a83182514331120c302e2a2846639550c818c229990416653362eaa2867099948d8bb299b (by decide +kernel)
private def pack_E6970Receipt31_chunk75 := witnessRule 31 44 128 490771 490897 7 511
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk76 := witnessRule 31 43 0 500012 500146 32 2814
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk77 := witnessRule 31 43 32 500198 500329 32 2805
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk78 := witnessRule 31 43 64 500330 500513 32 2581
  0xe7fd7ff7 0xb3a91b1716751384cea26c5dd48d8b3a91b (by decide +kernel)
private def pack_E6970Receipt31_chunk79 := witnessRule 31 43 96 500514 500769 32 2298
  0xfbaf9fbf 0x6094508c45032a99a03183514331110cca8620c6154cc420b3299884 (by decide +kernel)
private def pack_E6970Receipt31_chunk80 := witnessRule 31 43 128 500770 500896 6 431
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk81 := witnessRule 31 42 0 510011 510144 32 2810
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk82 := witnessRule 31 42 32 510145 510325 32 2753
  0xf9ffdffe 0x268550a4685a144dc291a (by decide +kernel)
private def pack_E6970Receipt31_chunk83 := witnessRule 31 42 64 510326 510458 32 2495
  0x3fe7ff7f 0x133a8988416753364d0a859d48c420b4289b (by decide +kernel)
private def pack_E6970Receipt31_chunk84 := witnessRule 31 42 96 510512 510769 32 2266
  0xfddebf3f 0xa0508d060c1a8a11889866533306308a2866235d50d0c3299b (by decide +kernel)
private def pack_E6970Receipt31_chunk85 := witnessRule 31 42 128 510770 510896 5 354
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk86 := witnessRule 31 41 0 520010 520142 32 2802
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk87 := witnessRule 31 41 32 520143 520322 32 2693
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk88 := witnessRule 31 41 64 520323 520456 32 2469
  0xbfaffdff 0x1775142384d0a26c5e148d8b4291b (by decide +kernel)
private def pack_E6970Receipt31_chunk89 := witnessRule 31 41 96 520457 520769 32 2203
  0xffff7dfe 0x308a284622419d4cc818b4291b (by decide +kernel)
private def pack_E6970Receipt31_chunk90 := witnessRule 31 41 128 520770 520833 3 209
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk91 := witnessRule 31 40 0 530009 530140 32 2790
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk92 := witnessRule 31 40 32 530141 530270 32 2577
  0x3ffdfff7 0x269552a4685a544dca91a (by decide +kernel)
private def pack_E6970Receipt31_chunk93 := witnessRule 31 40 64 530320 530454 32 2469
  0xff7fefff 0x5a148c420b4a89b (by decide +kernel)
private def pack_E6970Receipt31_chunk94 := witnessRule 31 40 96 530455 530770 32 2146
  0xfffffefd 0x6154508c44434299883 (by decide +kernel)
private def pack_E6970Receipt31_chunk95 := witnessRule 31 40 128 530832 530832 1 69
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk96 := witnessRule 31 39 0 540008 540138 32 2770
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk97 := witnessRule 31 39 32 540139 540267 32 2583
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk98 := witnessRule 31 39 64 540268 540453 32 2359
  0xfeffdfff 0x254cd0b4a91b (by decide +kernel)
private def pack_E6970Receipt31_chunk99 := witnessRule 31 39 96 540454 540832 31 2030
  0x7ffffffe 0xc328a1188d (by decide +kernel)
private def pack_E6970Receipt31_chunk100 := witnessRule 31 38 0 550007 550136 32 2746
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk101 := witnessRule 31 38 32 550137 550265 32 2551
  0xffdfffbf 0x5a944dd291a (by decide +kernel)
private def pack_E6970Receipt31_chunk102 := witnessRule 31 38 64 550266 550452 32 2257
  0xfdff7ff3 0x95232062d4a26c9a955291a (by decide +kernel)
private def pack_E6970Receipt31_chunk103 := witnessRule 31 38 96 550453 550769 28 1793
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk104 := witnessRule 31 37 0 560006 560134 32 2714
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk105 := witnessRule 31 37 32 560135 560263 32 2519
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk106 := witnessRule 31 37 64 560264 560452 32 2173
  0xffff7fff 0x5291883 (by decide +kernel)
private def pack_E6970Receipt31_chunk107 := witnessRule 31 37 96 560453 560768 25 1565
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk108 := witnessRule 31 36 0 570005 570132 32 2678
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk109 := witnessRule 31 36 32 570133 570262 32 2455
  0xfefffdff 0x5ad44dda91a (by decide +kernel)
private def pack_E6970Receipt31_chunk110 := witnessRule 31 36 64 570263 570452 32 2087
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk111 := witnessRule 31 36 96 570453 570768 22 1349
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk112 := witnessRule 31 35 0 580004 580130 32 2634
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk113 := witnessRule 31 35 32 580131 580261 32 2399
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk114 := witnessRule 31 35 64 580262 580453 32 2015
  0xffff7fdf 0x254504d025a89903 (by decide +kernel)
private def pack_E6970Receipt31_chunk115 := witnessRule 31 35 96 580454 580705 18 1082
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk116 := witnessRule 31 34 0 590003 590129 32 2578
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk117 := witnessRule 31 34 32 590130 590261 32 2324
  0xfffff7ff 0x6291a (by decide +kernel)
private def pack_E6970Receipt31_chunk118 := witnessRule 31 34 64 590262 590454 32 1936
  0xffffffef 0x528a09984 (by decide +kernel)
private def pack_E6970Receipt31_chunk119 := witnessRule 31 34 96 590512 590704 14 827
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk120 := witnessRule 31 33 0 600002 600128 32 2522
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk121 := witnessRule 31 33 32 600129 600261 32 2251
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk122 := witnessRule 31 33 64 600262 600513 32 1868
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk123 := witnessRule 31 33 96 600514 600704 10 581
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk124 := witnessRule 31 32 0 610001 610128 32 2458
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk125 := witnessRule 31 32 32 610129 610262 32 2144
  0xfefff7ff 0x2d45101e28a09884 (by decide +kernel)
private def pack_E6970Receipt31_chunk126 := witnessRule 31 32 64 610263 610516 32 1809
  0xfffffffb 0x4a9208a04 (by decide +kernel)
private def pack_E6970Receipt31_chunk127 := witnessRule 31 32 96 610576 610641 5 287
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk128 := witnessRule 31 31 0 620000 620128 32 2395
  0xdfffffff 0x6a8a09b (by decide +kernel)
private def pack_E6970Receipt31_chunk129 := witnessRule 31 31 32 620129 620263 32 2037
  0xffbfffff 0x529208984 (by decide +kernel)
private def pack_E6970Receipt31_chunk130 := witnessRule 31 31 64 620264 620640 32 1768
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk131 := witnessRule 31 30 0 630000 630129 32 2311
  0xffffbfff 0x6a922 (by decide +kernel)
private def pack_E6970Receipt31_chunk132 := witnessRule 31 30 32 630130 630265 32 1901
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk133 := witnessRule 31 30 64 630320 630640 27 1458
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk134 := witnessRule 31 29 0 640000 640130 32 2224
  0xf7ffbfff 0x314904442728a083 (by decide +kernel)
private def pack_E6970Receipt31_chunk135 := witnessRule 31 29 32 640131 640322 32 1809
  0xfffbfeff 0x25490484502da8a09204 (by decide +kernel)
private def pack_E6970Receipt31_chunk136 := witnessRule 31 29 64 640323 640577 21 1089
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk137 := witnessRule 31 28 0 650000 650131 32 2130
  0xffffdfff 0x6a9208b (by decide +kernel)
private def pack_E6970Receipt31_chunk138 := witnessRule 31 28 32 650132 650324 32 1704
  0xffffffbf 0x52920908985 (by decide +kernel)
private def pack_E6970Receipt31_chunk139 := witnessRule 31 28 64 650325 650576 16 813
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk140 := witnessRule 31 27 0 660000 660132 32 2031
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk141 := witnessRule 31 27 32 660133 660384 32 1618
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk142 := witnessRule 31 27 64 660385 660576 11 550
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk143 := witnessRule 31 26 0 670000 670133 32 1927
  0xfdffefff 0x2d450890262920908885 (by decide +kernel)
private def pack_E6970Receipt31_chunk144 := witnessRule 31 26 32 670134 670387 32 1553
  0xfffffff7 0x4a921108a05 (by decide +kernel)
private def pack_E6970Receipt31_chunk145 := witnessRule 31 26 64 670388 670513 6 295
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk146 := witnessRule 31 25 0 680000 680134 32 1821
  0xff7fffff 0x52921108985 (by decide +kernel)
private def pack_E6970Receipt31_chunk147 := witnessRule 31 25 32 680135 680450 32 1506
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk148 := witnessRule 31 25 64 680512 680512 1 49
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk149 := witnessRule 31 24 0 690000 690135 32 1715
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk150 := witnessRule 31 24 32 690136 690512 29 1326
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk151 := witnessRule 31 23 0 700000 700136 32 1619
  0xffdff7ff 0x25490c84502da8a19204 (by decide +kernel)
private def pack_E6970Receipt31_chunk152 := witnessRule 31 23 32 700192 700449 24 1068
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk153 := witnessRule 31 22 0 710000 710192 32 1537
  0xfffffbff 0x52921908985 (by decide +kernel)
private def pack_E6970Receipt31_chunk154 := witnessRule 31 22 32 710193 710448 20 856
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk155 := witnessRule 31 21 0 720000 720194 32 1456
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk156 := witnessRule 31 21 32 720195 720448 16 663
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk157 := witnessRule 31 20 0 730000 730195 32 1377
  0xfffffdff 0x4a922108a05 (by decide +kernel)
private def pack_E6970Receipt31_chunk158 := witnessRule 31 20 32 730196 730385 12 485
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk159 := witnessRule 31 19 0 740000 740197 32 1306
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk160 := witnessRule 31 19 32 740256 740384 8 317
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk161 := witnessRule 31 18 0 750000 750257 32 1241
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk162 := witnessRule 31 18 32 750258 750384 5 194
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk163 := witnessRule 31 17 0 760000 760320 32 1189
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk164 := witnessRule 31 17 32 760321 760321 1 38
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk165 := witnessRule 31 16 0 770000 770320 30 1066
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk166 := witnessRule 31 15 0 780000 780320 27 918
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk167 := witnessRule 31 14 0 790000 790257 24 780
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk168 := witnessRule 31 13 0 800000 800256 21 653
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk169 := witnessRule 31 12 0 810000 810256 19 564
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk170 := witnessRule 31 11 0 820000 820193 16 454
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk171 := witnessRule 31 10 0 830000 830192 14 379
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk172 := witnessRule 31 9 0 840000 840192 12 311
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk173 := witnessRule 31 8 0 850000 850129 10 247
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk174 := witnessRule 31 7 0 860000 860128 8 189
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk175 := witnessRule 31 6 0 870000 870128 7 158
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk176 := witnessRule 31 5 0 880000 880065 5 107
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk177 := witnessRule 31 4 0 890000 890064 4 81
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk178 := witnessRule 31 3 0 900000 900064 3 58
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk179 := witnessRule 31 2 0 910000 910001 2 36
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk180 := witnessRule 31 1 0 920000 920000 1 17
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt31_chunk181 := witnessRule 31 0 0 930000 930000 1 16
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt31_chunks : List (Chunk 31) := [pack_E6970Receipt31_chunk0, pack_E6970Receipt31_chunk1, pack_E6970Receipt31_chunk2, pack_E6970Receipt31_chunk3, pack_E6970Receipt31_chunk4, pack_E6970Receipt31_chunk5, pack_E6970Receipt31_chunk6, pack_E6970Receipt31_chunk7, pack_E6970Receipt31_chunk8, pack_E6970Receipt31_chunk9, pack_E6970Receipt31_chunk10, pack_E6970Receipt31_chunk11, pack_E6970Receipt31_chunk12, pack_E6970Receipt31_chunk13, pack_E6970Receipt31_chunk14, pack_E6970Receipt31_chunk15, pack_E6970Receipt31_chunk16, pack_E6970Receipt31_chunk17, pack_E6970Receipt31_chunk18, pack_E6970Receipt31_chunk19, pack_E6970Receipt31_chunk20, pack_E6970Receipt31_chunk21, pack_E6970Receipt31_chunk22, pack_E6970Receipt31_chunk23, pack_E6970Receipt31_chunk24, pack_E6970Receipt31_chunk25, pack_E6970Receipt31_chunk26, pack_E6970Receipt31_chunk27, pack_E6970Receipt31_chunk28, pack_E6970Receipt31_chunk29, pack_E6970Receipt31_chunk30, pack_E6970Receipt31_chunk31, pack_E6970Receipt31_chunk32, pack_E6970Receipt31_chunk33, pack_E6970Receipt31_chunk34, pack_E6970Receipt31_chunk35, pack_E6970Receipt31_chunk36, pack_E6970Receipt31_chunk37, pack_E6970Receipt31_chunk38, pack_E6970Receipt31_chunk39, pack_E6970Receipt31_chunk40, pack_E6970Receipt31_chunk41, pack_E6970Receipt31_chunk42, pack_E6970Receipt31_chunk43, pack_E6970Receipt31_chunk44, pack_E6970Receipt31_chunk45, pack_E6970Receipt31_chunk46, pack_E6970Receipt31_chunk47, pack_E6970Receipt31_chunk48, pack_E6970Receipt31_chunk49, pack_E6970Receipt31_chunk50, pack_E6970Receipt31_chunk51, pack_E6970Receipt31_chunk52, pack_E6970Receipt31_chunk53, pack_E6970Receipt31_chunk54, pack_E6970Receipt31_chunk55, pack_E6970Receipt31_chunk56, pack_E6970Receipt31_chunk57, pack_E6970Receipt31_chunk58, pack_E6970Receipt31_chunk59, pack_E6970Receipt31_chunk60, pack_E6970Receipt31_chunk61, pack_E6970Receipt31_chunk62, pack_E6970Receipt31_chunk63, pack_E6970Receipt31_chunk64, pack_E6970Receipt31_chunk65, pack_E6970Receipt31_chunk66, pack_E6970Receipt31_chunk67, pack_E6970Receipt31_chunk68, pack_E6970Receipt31_chunk69, pack_E6970Receipt31_chunk70, pack_E6970Receipt31_chunk71, pack_E6970Receipt31_chunk72, pack_E6970Receipt31_chunk73, pack_E6970Receipt31_chunk74, pack_E6970Receipt31_chunk75, pack_E6970Receipt31_chunk76, pack_E6970Receipt31_chunk77, pack_E6970Receipt31_chunk78, pack_E6970Receipt31_chunk79, pack_E6970Receipt31_chunk80, pack_E6970Receipt31_chunk81, pack_E6970Receipt31_chunk82, pack_E6970Receipt31_chunk83, pack_E6970Receipt31_chunk84, pack_E6970Receipt31_chunk85, pack_E6970Receipt31_chunk86, pack_E6970Receipt31_chunk87, pack_E6970Receipt31_chunk88, pack_E6970Receipt31_chunk89, pack_E6970Receipt31_chunk90, pack_E6970Receipt31_chunk91, pack_E6970Receipt31_chunk92, pack_E6970Receipt31_chunk93, pack_E6970Receipt31_chunk94, pack_E6970Receipt31_chunk95, pack_E6970Receipt31_chunk96, pack_E6970Receipt31_chunk97, pack_E6970Receipt31_chunk98, pack_E6970Receipt31_chunk99, pack_E6970Receipt31_chunk100, pack_E6970Receipt31_chunk101, pack_E6970Receipt31_chunk102, pack_E6970Receipt31_chunk103, pack_E6970Receipt31_chunk104, pack_E6970Receipt31_chunk105, pack_E6970Receipt31_chunk106, pack_E6970Receipt31_chunk107, pack_E6970Receipt31_chunk108, pack_E6970Receipt31_chunk109, pack_E6970Receipt31_chunk110, pack_E6970Receipt31_chunk111, pack_E6970Receipt31_chunk112, pack_E6970Receipt31_chunk113, pack_E6970Receipt31_chunk114, pack_E6970Receipt31_chunk115, pack_E6970Receipt31_chunk116, pack_E6970Receipt31_chunk117, pack_E6970Receipt31_chunk118, pack_E6970Receipt31_chunk119, pack_E6970Receipt31_chunk120, pack_E6970Receipt31_chunk121, pack_E6970Receipt31_chunk122, pack_E6970Receipt31_chunk123, pack_E6970Receipt31_chunk124, pack_E6970Receipt31_chunk125, pack_E6970Receipt31_chunk126, pack_E6970Receipt31_chunk127, pack_E6970Receipt31_chunk128, pack_E6970Receipt31_chunk129, pack_E6970Receipt31_chunk130, pack_E6970Receipt31_chunk131, pack_E6970Receipt31_chunk132, pack_E6970Receipt31_chunk133, pack_E6970Receipt31_chunk134, pack_E6970Receipt31_chunk135, pack_E6970Receipt31_chunk136, pack_E6970Receipt31_chunk137, pack_E6970Receipt31_chunk138, pack_E6970Receipt31_chunk139, pack_E6970Receipt31_chunk140, pack_E6970Receipt31_chunk141, pack_E6970Receipt31_chunk142, pack_E6970Receipt31_chunk143, pack_E6970Receipt31_chunk144, pack_E6970Receipt31_chunk145, pack_E6970Receipt31_chunk146, pack_E6970Receipt31_chunk147, pack_E6970Receipt31_chunk148, pack_E6970Receipt31_chunk149, pack_E6970Receipt31_chunk150, pack_E6970Receipt31_chunk151, pack_E6970Receipt31_chunk152, pack_E6970Receipt31_chunk153, pack_E6970Receipt31_chunk154, pack_E6970Receipt31_chunk155, pack_E6970Receipt31_chunk156, pack_E6970Receipt31_chunk157, pack_E6970Receipt31_chunk158, pack_E6970Receipt31_chunk159, pack_E6970Receipt31_chunk160, pack_E6970Receipt31_chunk161, pack_E6970Receipt31_chunk162, pack_E6970Receipt31_chunk163, pack_E6970Receipt31_chunk164, pack_E6970Receipt31_chunk165, pack_E6970Receipt31_chunk166, pack_E6970Receipt31_chunk167, pack_E6970Receipt31_chunk168, pack_E6970Receipt31_chunk169, pack_E6970Receipt31_chunk170, pack_E6970Receipt31_chunk171, pack_E6970Receipt31_chunk172, pack_E6970Receipt31_chunk173, pack_E6970Receipt31_chunk174, pack_E6970Receipt31_chunk175, pack_E6970Receipt31_chunk176, pack_E6970Receipt31_chunk177, pack_E6970Receipt31_chunk178, pack_E6970Receipt31_chunk179, pack_E6970Receipt31_chunk180, pack_E6970Receipt31_chunk181]
def rows31 := rowsFrom pack_E6970Receipt31_chunks
theorem good31 : ∀ r ∈ rows31, good 31 r = true := rowsFrom_good pack_E6970Receipt31_chunks
theorem sorted31 : rows31.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt31_chunks 0 (by decide +kernel)).1
theorem mass31 (i : Fin 61) :
    bandCount 31 (i.val : ℤ) 60 16 ≤ (rows31.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt31_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 31 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt31_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total31 : (rows31.map (price 31)).sum = 356668 :=
  (total_eq pack_E6970Receipt31_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt31

section Pack_E6970Receipt32

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt32_chunk0 := witnessA6966Final 32 60 0 360028 360463 32 3370
  0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk1 := witnessA6966Final 32 60 32 360464 360715 32 3325
  0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk2 := witnessA6966Final 32 60 64 360716 360961 32 3289
  0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk3 := witnessA6966Final 32 60 96 360962 361030 13 1303
  0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk4 := witnessRule 32 59 0 370027 370403 32 3298
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk5 := witnessRule 32 59 32 370404 370709 32 3247
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk6 := witnessRule 32 59 64 370710 370900 32 3207
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk7 := witnessRule 32 59 96 370901 371029 18 1754
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk8 := witnessRule 32 58 0 380026 380399 32 3259
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk9 := witnessRule 32 58 32 380400 380649 32 3183
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk10 := witnessRule 32 58 64 380650 380839 32 3135
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk11 := witnessRule 32 58 96 380840 381029 24 2284
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk12 := witnessRule 32 57 0 390025 390340 32 3217
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk13 := witnessRule 32 57 32 390341 390590 32 3133
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk14 := witnessRule 32 57 64 390591 390833 32 3091
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk15 := witnessRule 32 57 96 390834 391028 28 2598
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk16 := witnessRule 32 56 0 400024 400336 32 3193
  0xefffbfff 0x98550a91a (by decide +kernel)
private def pack_E6970Receipt32_chunk17 := witnessRule 32 56 32 400337 400584 32 3106
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk18 := witnessRule 32 56 64 400585 400773 32 3040
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk19 := witnessRule 32 56 96 400774 401027 32 2904
  0xfffbffff 0xb99a (by decide +kernel)
private def pack_E6970Receipt32_chunk20 := witnessRule 32 56 128 401028 401028 1 91
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk21 := witnessRule 32 55 0 410023 410333 32 3157
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk22 := witnessRule 32 55 32 410334 410526 32 3061
  0x7f5fefdf 0x1319a361542c8694c8b0a91b (by decide +kernel)
private def pack_E6970Receipt32_chunk23 := witnessRule 32 55 64 410527 410715 32 3001
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk24 := witnessRule 32 55 96 410768 410965 32 2868
  0xffbf7fff 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt32_chunk25 := witnessRule 32 55 128 411024 411027 4 352
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk26 := witnessRule 32 54 0 420022 420275 32 3122
  0xfdf9f7ef 0xb1289b262544a46858944d9291a (by decide +kernel)
private def pack_E6970Receipt32_chunk27 := witnessRule 32 54 32 420276 420521 32 3055
  0xfffbfdfc 0x36151064c2a2621098950b0a91884 (by decide +kernel)
private def pack_E6970Receipt32_chunk28 := witnessRule 32 54 64 420522 420708 32 2979
  0xfabfd7ef 0x118551321a175342ca68dc5441930a91b (by decide +kernel)
private def pack_E6970Receipt32_chunk29 := witnessRule 32 54 96 420709 420960 32 2797
  0xfbe7e9ea 0xba9a17164364e2c66c5c98cd93a1a471146c6685c590d9b8a09b (by decide +kernel)
private def pack_E6970Receipt32_chunk30 := witnessRule 32 54 128 420961 421027 8 690
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk31 := witnessRule 32 53 0 430021 430272 32 3104
  0xfbffffff 0xb1291b (by decide +kernel)
private def pack_E6970Receipt32_chunk32 := witnessRule 32 53 32 430273 430464 32 2979
  0x1fc7e3f5 0x6c4a898548c420b0aa1b26251362e4c4ac554d1b12a16252362e2c4a27098944d8b9291b (by decide +kernel)
private def pack_E6970Receipt32_chunk33 := witnessRule 32 53 64 430517 430651 32 2947
  0xbfebfc7f 0x5cd85442230a8831726151310a6c2a262109854cd8b8b0a91885 (by decide +kernel)
private def pack_E6970Receipt32_chunk34 := witnessRule 32 53 96 430704 430899 32 2779
  0xde797dff 0x2ec685c98cc420b8b29b36331064ca685d8d1b0a91b (by decide +kernel)
private def pack_E6970Receipt32_chunk35 := witnessRule 32 53 128 430900 431026 10 846
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk36 := witnessRule 32 52 0 440020 440269 32 3070
  0xdfcfdfdf 0xb1a89b263546a46858d44d9a91a (by decide +kernel)
private def pack_E6970Receipt32_chunk37 := witnessRule 32 52 32 440270 440459 32 2979
  0xfcff7f9f 0x1b1288326252364c4a2621098d50b1291884 (by decide +kernel)
private def pack_E6970Receipt32_chunk38 := witnessRule 32 52 64 440460 440645 32 2926
  0xfc3f8bf5 0xd8944d8b9b12b16155364e2c4a2711895131291b1726251384e4a46cd8944d8b8b1291c (by decide +kernel)
private def pack_E6970Receipt32_chunk39 := witnessRule 32 52 96 440646 440838 32 2709
  0xcf970fc1 0x994c418b39a26154362e4c2a6709c550da30a8988436153362e4c2a462145c58550e2312a3615231084c2a86c9c98958b8aa9b (by decide +kernel)
private def pack_E6970Receipt32_chunk40 := witnessRule 32 52 128 440896 441026 13 1077
  0x1ffe 0xbb9a (by decide +kernel)
private def pack_E6970Receipt32_chunk41 := witnessRule 32 51 0 450019 450213 32 3016
  0xbfffffff 0xb1a91b (by decide +kernel)
private def pack_E6970Receipt32_chunk42 := witnessRule 32 51 32 450267 450455 32 2979
  0xe3f8febf 0x26351362e4c6ac954d1b1aa16352362e2c6a27098d44d8b9a91b (by decide +kernel)
private def pack_E6970Receipt32_chunk43 := witnessRule 32 51 64 450456 450640 32 2860
  0x8ff8ff1f 0x231288336252362e4c4a26214d8944c42131299b1716252310a6c6a898948c420b12a1b (by decide +kernel)
private def pack_E6970Receipt32_chunk44 := witnessRule 32 51 96 450641 450835 32 2686
  0x38f87c7f 0x16156362e2c2aa70d854cc42130aa9b1716154310a6c4a46c98550c420b0ab1b2716252388c4a26c5cd894420b931291c (by decide +kernel)
private def pack_E6970Receipt32_chunk45 := witnessRule 32 51 128 450836 451025 14 1138
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk46 := witnessRule 32 50 0 460018 460210 32 3002
  0xfe7f7fbf 0x264548a46859144da291a (by decide +kernel)
private def pack_E6970Receipt32_chunk47 := witnessRule 32 50 32 460211 460399 32 2901
  0x7fdff3fd 0x131a91b2635131084c8a858d48c420b2289b (by decide +kernel)
private def pack_E6970Receipt32_chunk48 := witnessRule 32 50 64 460400 460583 32 2882
  0xff17f5fe 0x8c6a898d48d8b931a89c27352366c6a26c5c58d48e1b1a883 (by decide +kernel)
private def pack_E6970Receipt32_chunk49 := witnessRule 32 50 96 460584 460775 32 2629
  0xc7078bf0 0x26254362c2ac6210560d1b128990436253362e4c4a462145c58950e13929988446252066c4a4621098950d8b92a9b36351362e6c6ac58954d938b1a89c (by decide +kernel)
private def pack_E6970Receipt32_chunk50 := witnessRule 32 50 128 460832 461025 16 1276
  0xfff1 0x4c2aa62105855cd8b8ab1884 (by decide +kernel)
private def pack_E6970Receipt32_chunk51 := witnessRule 32 49 0 470017 470208 32 2989
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk52 := witnessRule 32 49 32 470209 470395 32 2884
  0xfe3fd7fb 0xd9150b2291b1716451384c8a26c5d148d8b2291b (by decide +kernel)
private def pack_E6970Receipt32_chunk53 := witnessRule 32 49 64 470396 470579 32 2824
  0xf1ff1ff1 0x1b1a8988426353362e2c6a46214d915131a9188416354364c8a26c5c99159aa9a (by decide +kernel)
private def pack_E6970Receipt32_chunk54 := witnessRule 32 49 96 470580 470772 32 2569
  0x1c5c5f1f 0x98954d8b8b12a188517256366c4a4641098950c420b12b1b2725143386c6a2621098d4cd8b931a91c27353368c6a20cd8d48d8b931a89885 (by decide +kernel)
private def pack_E6970Receipt32_chunk55 := witnessRule 32 49 128 470773 471024 16 1251
  0xffea 0x2c2ac641060518d931299904 (by decide +kernel)
private def pack_E6970Receipt32_chunk56 := witnessRule 32 48 0 480016 480205 32 2961
  0xf3fdff7f 0x26554aa46859544daa91a (by decide +kernel)
private def pack_E6970Receipt32_chunk57 := witnessRule 32 48 32 480206 480391 32 2862
  0xf7fe7fdf 0x2645131084caa859148c420b2a89b (by decide +kernel)
private def pack_E6970Receipt32_chunk58 := witnessRule 32 48 64 480392 480523 32 2752
  0x2ff5ff3f 0x4c8a46c5c99144e13a291b36451362e2c8a470d91441932291b (by decide +kernel)
private def pack_E6970Receipt32_chunk59 := witnessRule 32 48 96 480524 480769 32 2560
  0xe1e3f4fe 0x4c6a6621058d54d8b8b1aa1c2735331086c6a4621098d50d8b8b1a9988536451362c6aa6c9c59144e2322a (by decide +kernel)
private def pack_E6970Receipt32_chunk60 := witnessRule 32 48 128 480770 481024 17 1303
  0x1fff8 0x4c4a8641058958c4212c1a (by decide +kernel)
private def pack_E6970Receipt32_chunk61 := witnessRule 32 47 0 490015 490203 32 2933
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk62 := witnessRule 32 47 32 490204 490387 32 2796
  0x8ffaffbf 0xd9550b2a91b1716551384caa26c5d548d8b2a91b (by decide +kernel)
private def pack_E6970Receipt32_chunk63 := witnessRule 32 47 64 490388 490519 32 2770
  0xff1ff8ff 0xd95513229188416454364caa26c5c9955a2a9a (by decide +kernel)
private def pack_E6970Receipt32_chunk64 := witnessRule 32 47 96 490520 490711 32 2478
  0xc3a7c7f1 0x131aa188416356362e6aa62109c9450cc46932299b357344e8a66cd9148d8b9322898851716453386c8a262109914cd8b8b2291885 (by decide +kernel)
private def pack_E6970Receipt32_chunk65 := witnessRule 32 47 128 490768 490961 16 1205
  0xffe1 0x2625334082c4aa661095cc818c0a8a29885 (by decide +kernel)
private def pack_E6970Receipt32_chunk66 := witnessRule 32 46 0 500014 500200 32 2873
  0x9ff7feff 0x26654ca46859944db291a (by decide +kernel)
private def pack_E6970Receipt32_chunk67 := witnessRule 32 46 32 500201 500333 32 2800
  0xffcffdff 0x4cca859548c420b3289b (by decide +kernel)
private def pack_E6970Receipt32_chunk68 := witnessRule 32 46 64 500334 500515 32 2744
  0xf5ff9ffd 0x1b2a89b1716552386caa20c99548d932a89884 (by decide +kernel)
private def pack_E6970Receipt32_chunk69 := witnessRule 32 46 96 500516 500708 32 2420
  0x1e3c5f17 0x58d54c821ab98831825145384c8a86c5c5914cc428ba2a9b3645132084c8a6621059154d93a28a11c36551064caa46c5c99544e13aa91b (by decide +kernel)
private def pack_E6970Receipt32_chunk70 := witnessRule 32 46 128 500709 500960 16 1181
  0xffd6 0x2c4a86a106054510cc2931a99984 (by decide +kernel)
private def pack_E6970Receipt32_chunk71 := witnessRule 32 45 0 510013 510147 32 2829
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk72 := witnessRule 32 45 32 510199 510330 32 2820
  0xff5ffbff 0x4cca26c5d948d8b3291b (by decide +kernel)
private def pack_E6970Receipt32_chunk73 := witnessRule 32 45 64 510331 510512 32 2630
  0x8ffc7fe3 0x1b32a2655231082caa86c99944d8b9332b555346cca859948d8b8b3289c (by decide +kernel)
private def pack_E6970Receipt32_chunk74 := witnessRule 32 45 96 510513 510707 32 2391
  0x1878fc7f 0x1ab19831825144320a302e2a28664389914cc820b22a988445734302e6a6623499548c420b2aa1b1716553386caa262109954cd8b8b2a91885 (by decide +kernel)
private def pack_E6970Receipt32_chunk75 := witnessRule 32 45 128 510708 510960 15 1089
  0x7ffe 0xb1aa1a04 (by decide +kernel)
private def pack_E6970Receipt32_chunk76 := witnessRule 32 44 0 520012 520145 32 2820
  0xffdffdff 0x59d44dba91a (by decide +kernel)
private def pack_E6970Receipt32_chunk77 := witnessRule 32 44 32 520146 520326 32 2773
  0xf9ffdffc 0x133aa1665231082cea26c99d53a91a (by decide +kernel)
private def pack_E6970Receipt32_chunk78 := witnessRule 32 44 64 520327 520457 32 2593
  0x7fcfff7f 0x1716652386cca20c99948d933289884 (by decide +kernel)
private def pack_E6970Receipt32_chunk79 := witnessRule 32 44 96 520458 520705 32 2333
  0x71e1f5fd 0x502a664221459150cc222b19031835144310a4caa6621059554d8baaa18842745142311a4cca46d558d1b3289b (by decide +kernel)
private def pack_E6970Receipt32_chunk80 := witnessRule 32 44 128 520706 520897 14 997
  0x3ffa 0x58d4cd820c128a19a05 (by decide +kernel)
private def pack_E6970Receipt32_chunk81 := witnessRule 32 43 0 530011 530143 32 2811
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk82 := witnessRule 32 43 32 530144 530323 32 2714
  0xebffbfff 0x4cea26c5dd48d8b3a91b (by decide +kernel)
private def pack_E6970Receipt32_chunk83 := witnessRule 32 43 64 530324 530455 32 2555
  0xff1ff8ff 0x99d44d8b933ab655346cea859d48d8b8b3a89c (by decide +kernel)
private def pack_E6970Receipt32_chunk84 := witnessRule 32 43 96 530456 530705 32 2258
  0xa9e3ebf9 0x5028666305914cd420c1a8a199852825332182caa86411558c418c228a21c26653362eca86c99948c420b32a1b (by decide +kernel)
private def pack_E6970Receipt32_chunk85 := witnessRule 32 43 128 530706 530896 12 841
  0xffe 0xc128a11b05 (by decide +kernel)
private def pack_E6970Receipt32_chunk86 := witnessRule 32 42 0 540010 540141 32 2799
  0xff7ffbff 0x5a144dc291a (by decide +kernel)
private def pack_E6970Receipt32_chunk87 := witnessRule 32 42 32 540142 540271 32 2598
  0x3ffdffe7 0x1342a1675231082d0a26c9a154291a (by decide +kernel)
private def pack_E6970Receipt32_chunk88 := witnessRule 32 42 64 540320 540452 32 2580
  0xf9ffdfff 0x6cea20c99d48d933a89884 (by decide +kernel)
private def pack_E6970Receipt32_chunk89 := witnessRule 32 42 96 540453 540704 32 2197
  0xf7a7cfc7 0xc1a8a11a85165533408308a2866414605cd4508c870b32a1884656344cea2621059d4cd8b8b3a91c (by decide +kernel)
private def pack_E6970Receipt32_chunk90 := witnessRule 32 42 128 540705 540896 11 759
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk91 := witnessRule 32 41 0 550009 550139 32 2779
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk92 := witnessRule 32 41 32 550140 550268 32 2599
  0x7ffbffff 0x5e148d8b4291b (by decide +kernel)
private def pack_E6970Receipt32_chunk93 := witnessRule 32 41 64 550269 550451 32 2462
  0xf5ff1ffd 0x9a144dbaa9a368542d0a46c5c5a144e134289b (by decide +kernel)
private def pack_E6970Receipt32_chunk94 := witnessRule 32 41 96 550452 550705 32 2142
  0xfdefafc7 0x502a2846622186114508d028b32999841855143310a4cea4621059d50d8bba99884 (by decide +kernel)
private def pack_E6970Receipt32_chunk95 := witnessRule 32 41 128 550706 550833 8 543
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk96 := witnessRule 32 40 0 560008 560137 32 2755
  0xfdfff7ff 0x5a544dca91a (by decide +kernel)
private def pack_E6970Receipt32_chunk97 := witnessRule 32 40 32 560138 560265 32 2603
  0xffdfff3f 0x2d2a26c9a554a91a (by decide +kernel)
private def pack_E6970Receipt32_chunk98 := witnessRule 32 40 64 560266 560449 32 2341
  0xebfdffe7 0x134291b17853364d0a262109a550b4291884 (by decide +kernel)
private def pack_E6970Receipt32_chunk99 := witnessRule 32 40 96 560450 560705 32 2103
  0xfff7dfaf 0x2825142331a30aa284661459d4cc820c328a19c (by decide +kernel)
private def pack_E6970Receipt32_chunk100 := witnessRule 32 40 128 560706 560832 6 401
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk101 := witnessRule 32 39 0 570007 570135 32 2723
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk102 := witnessRule 32 39 32 570136 570263 32 2565
  0xffbfffff 0xb4a91b (by decide +kernel)
private def pack_E6970Receipt32_chunk103 := witnessRule 32 39 64 570264 570449 32 2256
  0xeffcffd7 0xb429988416952362e2d2a2709a544d8bca91b (by decide +kernel)
private def pack_E6970Receipt32_chunk104 := witnessRule 32 39 96 570450 570707 32 2054
  0xffffffef 0xc328a11905 (by decide +kernel)
private def pack_E6970Receipt32_chunk105 := witnessRule 32 39 128 570768 570832 3 199
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk106 := witnessRule 32 38 0 580006 580133 32 2687
  0xf7ffefff 0x5a944dd291a (by decide +kernel)
private def pack_E6970Receipt32_chunk107 := witnessRule 32 38 32 580134 580261 32 2527
  0xfdfff9ff 0x2d4a26c9a955291a (by decide +kernel)
private def pack_E6970Receipt32_chunk108 := witnessRule 32 38 64 580262 580448 32 2173
  0xd7f3ff3f 0x5a148cc20c3a8a118852695131082d2a66c9a950b4a91884 (by decide +kernel)
private def pack_E6970Receipt32_chunk109 := witnessRule 32 38 96 580449 580769 32 2020
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk110 := witnessRule 32 37 0 590005 590131 32 2643
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk111 := witnessRule 32 37 32 590132 590260 32 2465
  0xfdffffff 0xb5291b (by decide +kernel)
private def pack_E6970Receipt32_chunk112 := witnessRule 32 37 64 590261 590449 32 2106
  0xfffaff5f 0x169523208310a284709a944d8bd291b (by decide +kernel)
private def pack_E6970Receipt32_chunk113 := witnessRule 32 37 96 590450 590768 28 1718
  0xfffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk114 := witnessRule 32 36 0 600004 600129 32 2595
  0xdfffdfff 0x5ad44dda91a (by decide +kernel)
private def pack_E6970Receipt32_chunk115 := witnessRule 32 36 32 600130 600259 32 2411
  0xf7ffcfff 0x2d6a26c9ad55a91a (by decide +kernel)
private def pack_E6970Receipt32_chunk116 := witnessRule 32 36 64 600260 600449 32 2036
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk117 := witnessRule 32 36 96 600450 600768 25 1502
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk118 := witnessRule 32 35 0 610003 610128 32 2535
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk119 := witnessRule 32 35 32 610129 610259 32 2341
  0xfbffffff 0xb5a91b (by decide +kernel)
private def pack_E6970Receipt32_chunk120 := witnessRule 32 35 64 610260 610451 32 1958
  0xfffdff5f 0x12a46a0c5a944cc20c4a8a09885 (by decide +kernel)
private def pack_E6970Receipt32_chunk121 := witnessRule 32 35 96 610452 610705 20 1175
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk122 := witnessRule 32 34 0 620002 620079 32 2479
  0x7fffbfff 0x5b144de291a (by decide +kernel)
private def pack_E6970Receipt32_chunk123 := witnessRule 32 34 32 620128 620259 32 2273
  0xfdff9fff 0x314a282709b156291a (by decide +kernel)
private def pack_E6970Receipt32_chunk124 := witnessRule 32 34 64 620260 620452 32 1880
  0xffffffbf 0x5291a03 (by decide +kernel)
private def pack_E6970Receipt32_chunk125 := witnessRule 32 34 96 620453 620704 16 923
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk126 := witnessRule 32 33 0 630001 630079 32 2415
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk127 := witnessRule 32 33 32 630128 630260 32 2175
  0xfffff7ff 0xbda923 (by decide +kernel)
private def pack_E6970Receipt32_chunk128 := witnessRule 32 33 64 630261 630512 32 1808
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk129 := witnessRule 32 33 96 630513 630704 11 627
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk130 := witnessRule 32 32 0 640000 640078 32 2355
  0x7fff7fff 0x5b544dea91a (by decide +kernel)
private def pack_E6970Receipt32_chunk131 := witnessRule 32 32 32 640128 640261 32 2073
  0xfd7fe7ff 0xb513506312a4822217148c818c5a8a084 (by decide +kernel)
private def pack_E6970Receipt32_chunk132 := witnessRule 32 32 64 640262 640515 32 1751
  0xfffffff7 0x4a92303 (by decide +kernel)
private def pack_E6970Receipt32_chunk133 := witnessRule 32 32 96 640516 640641 6 337
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk134 := witnessRule 32 31 0 650000 650128 32 2276
  0xcfffffff 0x3548c418c628a3 (by decide +kernel)
private def pack_E6970Receipt32_chunk135 := witnessRule 32 31 32 650129 650263 32 1933
  0xffbffdff 0x29491418c529208c (by decide +kernel)
private def pack_E6970Receipt32_chunk136 := witnessRule 32 31 64 650264 650640 32 1717
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk137 := witnessRule 32 30 0 660000 660129 32 2194
  0xf7ffffff 0xbda92094 (by decide +kernel)
private def pack_E6970Receipt32_chunk138 := witnessRule 32 30 32 660130 660265 32 1809
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk139 := witnessRule 32 30 64 660320 660640 27 1419
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk140 := witnessRule 32 29 0 670000 670130 32 2108
  0xf3ffbfff 0x18a4860c62d4504842f289903 (by decide +kernel)
private def pack_E6970Receipt32_chunk141 := witnessRule 32 29 32 670131 670322 32 1720
  0xfffbfebf 0x12a4824c12d45045420c4a920908886 (by decide +kernel)
private def pack_E6970Receipt32_chunk142 := witnessRule 32 29 64 670323 670577 21 1064
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk143 := witnessRule 32 28 0 680000 680131 32 2015
  0xfdffcfff 0x314a48242375490818c628a094 (by decide +kernel)
private def pack_E6970Receipt32_chunk144 := witnessRule 32 28 32 680132 680324 32 1624
  0xffffffbf 0x529209284 (by decide +kernel)
private def pack_E6970Receipt32_chunk145 := witnessRule 32 28 64 680325 680576 16 795
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk146 := witnessRule 32 27 0 690000 690132 32 1919
  0xfffff7ff 0xbda92114 (by decide +kernel)
private def pack_E6970Receipt32_chunk147 := witnessRule 32 27 32 690133 690384 32 1552
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk148 := witnessRule 32 27 64 690385 690576 11 539
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk149 := witnessRule 32 26 0 700000 700133 32 1817
  0xfd7fe7ff 0xb514121150a312a48442221b149048c20c5a8a11085 (by decide +kernel)
private def pack_E6970Receipt32_chunk150 := witnessRule 32 26 32 700134 700387 32 1495
  0xfffffff7 0x4a9211304 (by decide +kernel)
private def pack_E6970Receipt32_chunk151 := witnessRule 32 26 64 700388 700513 6 289
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk152 := witnessRule 32 25 0 710000 710134 32 1714
  0xff7ffbff 0x2949089420c52921108d (by decide +kernel)
private def pack_E6970Receipt32_chunk153 := witnessRule 32 25 32 710135 710450 32 1455
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk154 := witnessRule 32 25 64 710512 710512 1 48
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk155 := witnessRule 32 24 0 720000 720135 32 1617
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk156 := witnessRule 32 24 32 720136 720512 29 1285
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk157 := witnessRule 32 23 0 730000 730136 32 1527
  0xffdff5ff 0x12a4864c12d4508845428c4a921908886 (by decide +kernel)
private def pack_E6970Receipt32_chunk158 := witnessRule 32 23 32 730192 730449 24 1034
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk159 := witnessRule 32 22 0 740000 740192 32 1449
  0xfffffbff 0x529219284 (by decide +kernel)
private def pack_E6970Receipt32_chunk160 := witnessRule 32 22 32 740193 740448 20 830
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk161 := witnessRule 32 21 0 750000 750194 32 1375
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk162 := witnessRule 32 21 32 750195 750448 16 647
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk163 := witnessRule 32 20 0 760000 760195 32 1302
  0xfffffdff 0x4a9221304 (by decide +kernel)
private def pack_E6970Receipt32_chunk164 := witnessRule 32 20 32 760196 760385 12 473
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk165 := witnessRule 32 19 0 770000 770197 32 1237
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk166 := witnessRule 32 19 32 770256 770384 8 309
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk167 := witnessRule 32 18 0 780000 780257 32 1182
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk168 := witnessRule 32 18 32 780258 780384 5 189
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk169 := witnessRule 32 17 0 790000 790320 32 1134
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk170 := witnessRule 32 17 32 790321 790321 1 37
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk171 := witnessRule 32 16 0 800000 800320 30 1017
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk172 := witnessRule 32 15 0 810000 810320 27 879
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk173 := witnessRule 32 14 0 820000 820257 24 746
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk174 := witnessRule 32 13 0 830000 830256 21 624
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk175 := witnessRule 32 12 0 840000 840256 19 541
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk176 := witnessRule 32 11 0 850000 850193 16 435
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk177 := witnessRule 32 10 0 860000 860192 14 363
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk178 := witnessRule 32 9 0 870000 870192 12 299
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk179 := witnessRule 32 8 0 880000 880129 10 237
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk180 := witnessRule 32 7 0 890000 890128 8 181
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk181 := witnessRule 32 6 0 900000 900128 7 151
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk182 := witnessRule 32 5 0 910000 910065 5 102
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk183 := witnessRule 32 4 0 920000 920064 4 77
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk184 := witnessRule 32 3 0 930000 930064 3 55
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk185 := witnessRule 32 2 0 940000 940001 2 34
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk186 := witnessRule 32 1 0 950000 950000 1 16
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt32_chunk187 := witnessRule 32 0 0 960000 960000 1 15
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt32_chunks : List (Chunk 32) := [pack_E6970Receipt32_chunk0, pack_E6970Receipt32_chunk1, pack_E6970Receipt32_chunk2, pack_E6970Receipt32_chunk3, pack_E6970Receipt32_chunk4, pack_E6970Receipt32_chunk5, pack_E6970Receipt32_chunk6, pack_E6970Receipt32_chunk7, pack_E6970Receipt32_chunk8, pack_E6970Receipt32_chunk9, pack_E6970Receipt32_chunk10, pack_E6970Receipt32_chunk11, pack_E6970Receipt32_chunk12, pack_E6970Receipt32_chunk13, pack_E6970Receipt32_chunk14, pack_E6970Receipt32_chunk15, pack_E6970Receipt32_chunk16, pack_E6970Receipt32_chunk17, pack_E6970Receipt32_chunk18, pack_E6970Receipt32_chunk19, pack_E6970Receipt32_chunk20, pack_E6970Receipt32_chunk21, pack_E6970Receipt32_chunk22, pack_E6970Receipt32_chunk23, pack_E6970Receipt32_chunk24, pack_E6970Receipt32_chunk25, pack_E6970Receipt32_chunk26, pack_E6970Receipt32_chunk27, pack_E6970Receipt32_chunk28, pack_E6970Receipt32_chunk29, pack_E6970Receipt32_chunk30, pack_E6970Receipt32_chunk31, pack_E6970Receipt32_chunk32, pack_E6970Receipt32_chunk33, pack_E6970Receipt32_chunk34, pack_E6970Receipt32_chunk35, pack_E6970Receipt32_chunk36, pack_E6970Receipt32_chunk37, pack_E6970Receipt32_chunk38, pack_E6970Receipt32_chunk39, pack_E6970Receipt32_chunk40, pack_E6970Receipt32_chunk41, pack_E6970Receipt32_chunk42, pack_E6970Receipt32_chunk43, pack_E6970Receipt32_chunk44, pack_E6970Receipt32_chunk45, pack_E6970Receipt32_chunk46, pack_E6970Receipt32_chunk47, pack_E6970Receipt32_chunk48, pack_E6970Receipt32_chunk49, pack_E6970Receipt32_chunk50, pack_E6970Receipt32_chunk51, pack_E6970Receipt32_chunk52, pack_E6970Receipt32_chunk53, pack_E6970Receipt32_chunk54, pack_E6970Receipt32_chunk55, pack_E6970Receipt32_chunk56, pack_E6970Receipt32_chunk57, pack_E6970Receipt32_chunk58, pack_E6970Receipt32_chunk59, pack_E6970Receipt32_chunk60, pack_E6970Receipt32_chunk61, pack_E6970Receipt32_chunk62, pack_E6970Receipt32_chunk63, pack_E6970Receipt32_chunk64, pack_E6970Receipt32_chunk65, pack_E6970Receipt32_chunk66, pack_E6970Receipt32_chunk67, pack_E6970Receipt32_chunk68, pack_E6970Receipt32_chunk69, pack_E6970Receipt32_chunk70, pack_E6970Receipt32_chunk71, pack_E6970Receipt32_chunk72, pack_E6970Receipt32_chunk73, pack_E6970Receipt32_chunk74, pack_E6970Receipt32_chunk75, pack_E6970Receipt32_chunk76, pack_E6970Receipt32_chunk77, pack_E6970Receipt32_chunk78, pack_E6970Receipt32_chunk79, pack_E6970Receipt32_chunk80, pack_E6970Receipt32_chunk81, pack_E6970Receipt32_chunk82, pack_E6970Receipt32_chunk83, pack_E6970Receipt32_chunk84, pack_E6970Receipt32_chunk85, pack_E6970Receipt32_chunk86, pack_E6970Receipt32_chunk87, pack_E6970Receipt32_chunk88, pack_E6970Receipt32_chunk89, pack_E6970Receipt32_chunk90, pack_E6970Receipt32_chunk91, pack_E6970Receipt32_chunk92, pack_E6970Receipt32_chunk93, pack_E6970Receipt32_chunk94, pack_E6970Receipt32_chunk95, pack_E6970Receipt32_chunk96, pack_E6970Receipt32_chunk97, pack_E6970Receipt32_chunk98, pack_E6970Receipt32_chunk99, pack_E6970Receipt32_chunk100, pack_E6970Receipt32_chunk101, pack_E6970Receipt32_chunk102, pack_E6970Receipt32_chunk103, pack_E6970Receipt32_chunk104, pack_E6970Receipt32_chunk105, pack_E6970Receipt32_chunk106, pack_E6970Receipt32_chunk107, pack_E6970Receipt32_chunk108, pack_E6970Receipt32_chunk109, pack_E6970Receipt32_chunk110, pack_E6970Receipt32_chunk111, pack_E6970Receipt32_chunk112, pack_E6970Receipt32_chunk113, pack_E6970Receipt32_chunk114, pack_E6970Receipt32_chunk115, pack_E6970Receipt32_chunk116, pack_E6970Receipt32_chunk117, pack_E6970Receipt32_chunk118, pack_E6970Receipt32_chunk119, pack_E6970Receipt32_chunk120, pack_E6970Receipt32_chunk121, pack_E6970Receipt32_chunk122, pack_E6970Receipt32_chunk123, pack_E6970Receipt32_chunk124, pack_E6970Receipt32_chunk125, pack_E6970Receipt32_chunk126, pack_E6970Receipt32_chunk127, pack_E6970Receipt32_chunk128, pack_E6970Receipt32_chunk129, pack_E6970Receipt32_chunk130, pack_E6970Receipt32_chunk131, pack_E6970Receipt32_chunk132, pack_E6970Receipt32_chunk133, pack_E6970Receipt32_chunk134, pack_E6970Receipt32_chunk135, pack_E6970Receipt32_chunk136, pack_E6970Receipt32_chunk137, pack_E6970Receipt32_chunk138, pack_E6970Receipt32_chunk139, pack_E6970Receipt32_chunk140, pack_E6970Receipt32_chunk141, pack_E6970Receipt32_chunk142, pack_E6970Receipt32_chunk143, pack_E6970Receipt32_chunk144, pack_E6970Receipt32_chunk145, pack_E6970Receipt32_chunk146, pack_E6970Receipt32_chunk147, pack_E6970Receipt32_chunk148, pack_E6970Receipt32_chunk149, pack_E6970Receipt32_chunk150, pack_E6970Receipt32_chunk151, pack_E6970Receipt32_chunk152, pack_E6970Receipt32_chunk153, pack_E6970Receipt32_chunk154, pack_E6970Receipt32_chunk155, pack_E6970Receipt32_chunk156, pack_E6970Receipt32_chunk157, pack_E6970Receipt32_chunk158, pack_E6970Receipt32_chunk159, pack_E6970Receipt32_chunk160, pack_E6970Receipt32_chunk161, pack_E6970Receipt32_chunk162, pack_E6970Receipt32_chunk163, pack_E6970Receipt32_chunk164, pack_E6970Receipt32_chunk165, pack_E6970Receipt32_chunk166, pack_E6970Receipt32_chunk167, pack_E6970Receipt32_chunk168, pack_E6970Receipt32_chunk169, pack_E6970Receipt32_chunk170, pack_E6970Receipt32_chunk171, pack_E6970Receipt32_chunk172, pack_E6970Receipt32_chunk173, pack_E6970Receipt32_chunk174, pack_E6970Receipt32_chunk175, pack_E6970Receipt32_chunk176, pack_E6970Receipt32_chunk177, pack_E6970Receipt32_chunk178, pack_E6970Receipt32_chunk179, pack_E6970Receipt32_chunk180, pack_E6970Receipt32_chunk181, pack_E6970Receipt32_chunk182, pack_E6970Receipt32_chunk183, pack_E6970Receipt32_chunk184, pack_E6970Receipt32_chunk185, pack_E6970Receipt32_chunk186, pack_E6970Receipt32_chunk187]
def rows32 := rowsFrom pack_E6970Receipt32_chunks
theorem good32 : ∀ r ∈ rows32, good 32 r = true := rowsFrom_good pack_E6970Receipt32_chunks
theorem sorted32 : rows32.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt32_chunks 0 (by decide +kernel)).1
theorem mass32 (i : Fin 61) :
    bandCount 32 (i.val : ℤ) 60 16 ≤ (rows32.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt32_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 32 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt32_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total32 : (rows32.map (price 32)).sum = 368850 :=
  (total_eq pack_E6970Receipt32_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt32

section Pack_E6970Receipt33

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt33_chunk0 := witnessA6966Final 33 60 0 390027 390400 32 3361
  0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk1 := witnessA6966Final 33 60 32 390401 390650 32 3321
  0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk2 := witnessA6966Final 33 60 64 390651 390840 32 3285
  0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk3 := witnessA6966Final 33 60 96 390841 391030 27 2709
  0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk4 := witnessRule 33 59 0 400026 400341 32 3283
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk5 := witnessRule 33 59 32 400342 400591 32 3235
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk6 := witnessRule 33 59 64 400592 400833 32 3210
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk7 := witnessRule 33 59 96 400834 401029 32 3120
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk8 := witnessRule 33 58 0 410025 410337 32 3235
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk9 := witnessRule 33 58 32 410338 410585 32 3173
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk10 := witnessRule 33 58 64 410586 410774 32 3134
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk11 := witnessRule 33 58 96 410775 411024 32 3039
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk12 := witnessRule 33 58 128 411025 411029 5 467
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk13 := witnessRule 33 57 0 420024 420334 32 3196
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk14 := witnessRule 33 57 32 420335 420527 32 3112
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk15 := witnessRule 33 57 64 420528 420716 32 3068
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk16 := witnessRule 33 57 96 420768 420962 32 2993
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk17 := witnessRule 33 57 128 420963 421028 9 820
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk18 := witnessRule 33 56 0 430023 430276 32 3158
  0xfffbffef 0x98550a91a (by decide +kernel)
private def pack_E6970Receipt33_chunk19 := witnessRule 33 56 32 430277 430522 32 3094
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk20 := witnessRule 33 56 64 430523 430709 32 3027
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk21 := witnessRule 33 56 96 430710 430901 32 2905
  0xbfffffff 0xb99a (by decide +kernel)
private def pack_E6970Receipt33_chunk22 := witnessRule 33 56 128 430902 431028 13 1159
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk23 := witnessRule 33 55 0 440022 440273 32 3134
  0xfbffffff 0xb0a91b (by decide +kernel)
private def pack_E6970Receipt33_chunk24 := witnessRule 33 55 32 440274 440465 32 3026
  0xffefebfd 0x263346c2a8590d299 (by decide +kernel)
private def pack_E6970Receipt33_chunk25 := witnessRule 33 55 64 440518 440652 32 2990
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk26 := witnessRule 33 55 96 440704 440896 32 2883
  0xf7ffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt33_chunk27 := witnessRule 33 55 128 440897 441027 16 1393
  0xfffb 0xba1a (by decide +kernel)
private def pack_E6970Receipt33_chunk28 := witnessRule 33 54 0 450021 450270 32 3100
  0xdfcfdf9f 0x98544c421312a1615231082c4a26c98951291a (by decide +kernel)
private def pack_E6970Receipt33_chunk29 := witnessRule 33 54 32 450271 450460 32 3014
  0x7effffbf 0x6e2a20c98548d9b0a883 (by decide +kernel)
private def pack_E6970Receipt33_chunk30 := witnessRule 33 54 64 450461 450646 32 2966
  0xfeafabfd 0x6c6685c590d9b8a09b461544c8685d4d0b29a (by decide +kernel)
private def pack_E6970Receipt33_chunk31 := witnessRule 33 54 96 450647 450836 32 2805
  0x3f6febfa 0x17164364e2c66c5c98cd9b99a27163368e2885c98cd93a1a (by decide +kernel)
private def pack_E6970Receipt33_chunk32 := witnessRule 33 54 128 450837 451027 19 1617
  0x7ffdf 0xba9a (by decide +kernel)
private def pack_E6970Receipt33_chunk33 := witnessRule 33 53 0 460020 460214 32 3046
  0x1fafdfff 0xd8950b1291b1716251384c4a26c5c948d8b1291b (by decide +kernel)
private def pack_E6970Receipt33_chunk34 := witnessRule 33 53 32 460268 460456 32 3012
  0xe3f8fe3f 0x1b0a8988426153362e2c2a46214d895130a9188416154364c4a26c5c98958aa9a (by decide +kernel)
private def pack_E6970Receipt33_chunk35 := witnessRule 33 53 64 460457 460640 32 2906
  0xdffdff5f 0x36152362e6c2a2111854418b930a89885 (by decide +kernel)
private def pack_E6970Receipt33_chunk36 := witnessRule 33 53 96 460641 460832 32 2786
  0xf0f57eff 0x17264364e2c662109d4d238988b364342e2ca6d1c54419329a (by decide +kernel)
private def pack_E6970Receipt33_chunk37 := witnessRule 33 53 128 460833 461026 21 1749
  0x1ffef9 0x2ec685c594d938b21b (by decide +kernel)
private def pack_E6970Receipt33_chunk38 := witnessRule 33 52 0 470019 470211 32 3026
  0xfe7f7f3f 0x131aa1625231082c6a26c98d51a91a (by decide +kernel)
private def pack_E6970Receipt33_chunk39 := witnessRule 33 52 32 470212 470400 32 2938
  0x2fd7f3fd 0x26252362e4c4a2709c948d9b1289b1716252386c4a20c98948d931289884 (by decide +kernel)
private def pack_E6970Receipt33_chunk40 := witnessRule 33 52 64 470401 470584 32 2914
  0xff07f0fe 0x118951b0a9188426154364e4c4ac5c554d9b1289b17362562c2aa6c9c58944e2312a (by decide +kernel)
private def pack_E6970Receipt33_chunk41 := witnessRule 33 52 96 470585 470773 32 2727
  0x4e9f47f0 0x998d0bb9a37153366c2a66c9c98544c42938b0a99c56151062e6c2a262145c9854ce138b0a918854615131086c2a66c5c98548c428b8b0aa1c (by decide +kernel)
private def pack_E6970Receipt33_chunk42 := witnessRule 33 52 128 470774 471026 23 1878
  0x7ffb9e 0x177342e4c862105c598d9b21883 (by decide +kernel)
private def pack_E6970Receipt33_chunk43 := witnessRule 33 51 0 480018 480209 32 3010
  0xfd7f7fff 0x4c6a26c5cd48d8b1a91b (by decide +kernel)
private def pack_E6970Receipt33_chunk44 := witnessRule 33 51 32 480210 480396 32 2914
  0xfe3fc7f1 0x1b1aa2625231082c4a86c98d44d8b931ab255346c6a858d48d8b8b1a89c (by decide +kernel)
private def pack_E6970Receipt33_chunk45 := witnessRule 33 51 64 480397 480579 32 2879
  0xf1ff1ff1 0x231289b1736251082e4c4a4711894419b1291b1726251310a6c4a262109894cd8b8b1291885 (by decide +kernel)
private def pack_E6970Receipt33_chunk46 := witnessRule 33 51 96 480580 480769 32 2669
  0xe1f0be2f 0x230a9188436154362e4c2a662145c58554e231289b3615331084c2aa6c9c98944e1b9291b562546c4a46c5cd8944e138b1291c (by decide +kernel)
private def pack_E6970Receipt33_chunk47 := witnessRule 33 51 128 480770 481025 24 1919
  0xfffcf2 0x1331883168344c2aa6c5c98550e138aa9b (by decide +kernel)
private def pack_E6970Receipt33_chunk48 := witnessRule 33 50 0 490017 490206 32 2982
  0xf3fdfe7f 0x1322a1635231082c8a26c99152291a (by decide +kernel)
private def pack_E6970Receipt33_chunk49 := witnessRule 33 50 32 490207 490392 32 2892
  0xf5fe7fdf 0x1b1a89b1716352386c6a20c98d48d931a89884 (by decide +kernel)
private def pack_E6970Receipt33_chunk50 := witnessRule 33 50 64 490393 490524 32 2788
  0xff0ff17 0x3625231084c4a86c9c98d58b92a9b36351362e6c6ac58954d938b1a89c463544c6a46c5c98d44e139a91b (by decide +kernel)
private def pack_E6970Receipt33_chunk51 := witnessRule 33 50 96 490525 490711 32 2656
  0xf07e1fe 0xd894cd930aa988416157364e2c4a671189481a31291b1736251310a2e4c4a6709c58948c42a3128988436253362e4c4a462145c58950e231aa (by decide +kernel)
private def pack_E6970Receipt33_chunk52 := witnessRule 33 50 128 490712 491025 25 1964
  0x1fff78f 0x16157366c2a8621098558d8b8b0aa9885 (by decide +kernel)
private def pack_E6970Receipt33_chunk53 := witnessRule 33 49 0 500016 500204 32 2954
  0xebfdffff 0x4c8a26c5d148d8b2291b (by decide +kernel)
private def pack_E6970Receipt33_chunk54 := witnessRule 33 49 32 500205 500388 32 2826
  0x8ff8ff1f 0x1b22a2635231082c6a86c99144d8b9322b355346c8a859148d8b8b2289c (by decide +kernel)
private def pack_E6970Receipt33_chunk55 := witnessRule 33 49 64 500389 500519 32 2828
  0xff1ff8ff 0x118d4419b1a91b1726351310a6c6a2621098d4cd8b8b1a91885 (by decide +kernel)
private def pack_E6970Receipt33_chunk56 := witnessRule 33 49 96 500520 500708 32 2576
  0x38be2fe3 0xb8b12a9c2725431088c4a26410d894cc421312a9b17256368c6a20cd8d48d8b9b1a89c2716352388c6a26c5cd8d4420b931a91c (by decide +kernel)
private def pack_E6970Receipt33_chunk57 := witnessRule 33 49 128 500709 501024 25 1921
  0x1fffe38 0x98954d8b0ab9884159346c4a46410d8950d8b931299885 (by decide +kernel)
private def pack_E6970Receipt33_chunk58 := witnessRule 33 48 0 510015 510201 32 2894
  0x9ff7fcff 0x132aa1645231082caa26c99552a91a (by decide +kernel)
private def pack_E6970Receipt33_chunk59 := witnessRule 33 48 32 510202 510334 32 2825
  0x7fcffdff 0x1716452386c8a20c99148d932289884 (by decide +kernel)
private def pack_E6970Receipt33_chunk60 := witnessRule 33 48 64 510335 510515 32 2789
  0xf0ff8bfd 0x1b2289b17364562c6aa6c9c59144e2322a26452362e4c8a2709d148d9b2289b (by decide +kernel)
private def pack_E6970Receipt33_chunk61 := witnessRule 33 48 96 510516 510705 32 2518
  0xe2f0fe0f 0x1b1a9188426354362e4c6a6709cd50da31a8988436353362e4c6a462145c58d50e2322a3635231084c6a86c9c99158b9aa9b (by decide +kernel)
private def pack_E6970Receipt33_chunk62 := witnessRule 33 48 128 510706 511024 25 1883
  0x1fff860 0x1312a1904162563108302c2aa62146055cd9b12999042625531082c4ae6c5c958c4213928a21c (by decide +kernel)
private def pack_E6970Receipt33_chunk63 := witnessRule 33 47 0 520014 520148 32 2850
  0x5ff7ffff 0x4caa26c5d548d8b2a91b (by decide +kernel)
private def pack_E6970Receipt33_chunk64 := witnessRule 33 47 32 520200 520331 32 2838
  0xff1ff1ff 0x99544d8b932ab455346caa859548d8b8b2a89c (by decide +kernel)
private def pack_E6970Receipt33_chunk65 := witnessRule 33 47 64 520332 520461 32 2680
  0x1ffc7fe3 0x232288336452362e4c8a26214d9144c42132299b1716452310a6caa899148c420b22a1b (by decide +kernel)
private def pack_E6970Receipt33_chunk66 := witnessRule 33 47 96 520512 520648 32 2506
  0x87c3f1ff 0x6c6a6621098d54d8b8b1aa188517356366c8a46c98d50c420b1ab1b2716452388c8a26c5cd914420b932291c (by decide +kernel)
private def pack_E6970Receipt33_chunk67 := witnessRule 33 47 128 520704 520961 24 1776
  0xfff5c3 0x58954cc20c0ab19042635431082c6ac6c6058954e0c0b92a1885 (by decide +kernel)
private def pack_E6970Receipt33_chunk68 := witnessRule 33 46 0 530013 530146 32 2835
  0xffdff9ff 0x2cca26c99953291a (by decide +kernel)
private def pack_E6970Receipt33_chunk69 := witnessRule 33 46 32 530147 530327 32 2799
  0xf9ffdffc 0x1b2a88326552364caa2621099950b2a91884 (by decide +kernel)
private def pack_E6970Receipt33_chunk70 := witnessRule 33 46 64 530328 530457 32 2653
  0x7fc5ff5f 0x4e2caa2711955132a91b1726551384eaa46cd9544d8b8b2a91c (by decide +kernel)
private def pack_E6970Receipt33_chunk71 := witnessRule 33 46 96 530458 530646 32 2420
  0xe0f8bf8 0x26454362c6ac6210d60d0c0b9aa1c3645132086c8a66c5c99148c428b8b22a1c2745331088c8a40cd9148c421322a1b17455366caa26c5cd9558b22a9b (by decide +kernel)
private def pack_E6970Receipt33_chunk72 := witnessRule 33 46 128 530647 530960 23 1668
  0x7fff07 0x131a99984163553208302c4a8641460958c420c0b8a8a2188e (by decide +kernel)
private def pack_E6970Receipt33_chunk73 := witnessRule 33 45 0 540012 540144 32 2825
  0xffdfffff 0xb3291b (by decide +kernel)
private def pack_E6970Receipt33_chunk74 := witnessRule 33 45 32 540145 540324 32 2739
  0xe3ff1ffa 0x26651362e4ccad554d1b32a16652362e2cca27099944d8bb291b (by decide +kernel)
private def pack_E6970Receipt33_chunk75 := witnessRule 33 45 64 540325 540454 32 2646
  0xfe3ff8ff 0xd9544c42132a99b1716552310a6cca899548c420b2aa1b (by decide +kernel)
private def pack_E6970Receipt33_chunk76 := witnessRule 33 45 96 540455 540644 32 2342
  0x3c5e2fc7 0xc0b1aa188518356366c8a4641099150c420b22b1b2745143386caa262109954cd8b932a91c27553368caa20cd9548d8b932a89885 (by decide +kernel)
private def pack_E6970Receipt33_chunk77 := witnessRule 33 45 128 540645 540960 22 1564
  0x3fff0c 0x58d50d020c0b1299a05182553308502a86222149914cc820b22a9884 (by decide +kernel)
private def pack_E6970Receipt33_chunk78 := witnessRule 33 44 0 550011 550142 32 2811
  0xff7ff3ff 0x2cea26c99d53a91a (by decide +kernel)
private def pack_E6970Receipt33_chunk79 := witnessRule 33 44 32 550143 550272 32 2627
  0x3ffdffe7 0x1b3288326652364cca2621099d50b3291884 (by decide +kernel)
private def pack_E6970Receipt33_chunk80 := witnessRule 33 44 64 550321 550451 32 2646
  0xf17fd7ff 0x11995133291b1726651384eca46cd9944d8b8b3291c (by decide +kernel)
private def pack_E6970Receipt33_chunk81 := witnessRule 33 44 96 550452 550643 32 2284
  0x387c7f4f 0x183553208504a862309954cc420b2aa9b181645438302e8a66214d9548c42132aa1b1716553310a6cca26c59554d938b3289c (by decide +kernel)
private def pack_E6970Receipt33_chunk82 := witnessRule 33 44 128 550644 550897 20 1394
  0xffeac 0xb1a99b0418254350850288643059150cc20c0b1a99985 (by decide +kernel)
private def pack_E6970Receipt33_chunk83 := witnessRule 33 43 0 560010 560140 32 2793
  0xff7fffff 0xb3a91b (by decide +kernel)
private def pack_E6970Receipt33_chunk84 := witnessRule 33 43 32 560141 560269 32 2619
  0x7ff1ffd7 0x1954d1b3aa16752362e2cea27099d44d8bba91b (by decide +kernel)
private def pack_E6970Receipt33_chunk85 := witnessRule 33 43 64 560270 560449 32 2550
  0xc7fe3ffc 0x3665131084cca66c5c59948c429b3aa2665231082cca86c99d44d8b933ab (by decide +kernel)
private def pack_E6970Receipt33_chunk86 := witnessRule 33 43 96 560450 560642 32 2236
  0x787a7e3f 0x504a662241459550c820c0b2299905184553108302e6a28662389994cdaab9a1817553386cca46c5c99944c428b8b3299c (by decide +kernel)
private def pack_E6970Receipt33_chunk87 := witnessRule 33 43 128 560643 560896 18 1233
  0x3fffa 0x5914cd420c1aa1a04 (by decide +kernel)
private def pack_E6970Receipt33_chunk88 := witnessRule 33 42 0 570009 570138 32 2767
  0xfdffe7ff 0x2d0a26c9a154291a (by decide +kernel)
private def pack_E6970Receipt33_chunk89 := witnessRule 33 42 32 570139 570266 32 2621
  0xffdfff3f 0x4cea262109a150b3a91884 (by decide +kernel)
private def pack_E6970Receipt33_chunk90 := witnessRule 33 42 64 570267 570396 32 2409
  0x17faffe7 0x36751064cea46c5c99d44e13ba91b36751362e2cea470d9d441933a91b (by decide +kernel)
private def pack_E6970Receipt33_chunk91 := witnessRule 33 42 96 570448 570642 32 2202
  0xb4f8f8bf 0x502a2866422185954cd020c22a19842835331110a2cca86210605954cc428c2aa9b3665132084cca6621059954d93b28a11c (by decide +kernel)
private def pack_E6970Receipt33_chunk92 := witnessRule 33 42 128 570643 570896 16 1079
  0xfffe 0xc1a99b04 (by decide +kernel)
private def pack_E6970Receipt33_chunk93 := witnessRule 33 41 0 580008 580136 32 2737
  0xfdffffff 0xb4291b (by decide +kernel)
private def pack_E6970Receipt33_chunk94 := witnessRule 33 41 32 580137 580263 32 2613
  0xff1ffebf 0x1b42a16852362e2d0a2709a144d8bc291b (by decide +kernel)
private def pack_E6970Receipt33_chunk95 := witnessRule 33 41 64 580264 580394 32 2334
  0x3fe3ff8f 0x26753362e2cea46214da15133a9188416754364d0a26c5c9a15baa9a (by decide +kernel)
private def pack_E6970Receipt33_chunk96 := witnessRule 33 41 96 580395 580642 32 2128
  0xbd74f8fe 0xa054508c84c30c2299a842825143321a2cca6661061550c8214229988c2675231082cea86c605994ce1b3a89884 (by decide +kernel)
private def pack_E6970Receipt33_chunk97 := witnessRule 33 41 128 580643 580833 13 862
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk98 := witnessRule 33 40 0 590007 590134 32 2699
  0xf7ffcfff 0x2d2a26c9a554a91a (by decide +kernel)
private def pack_E6970Receipt33_chunk99 := witnessRule 33 40 32 590135 590261 32 2569
  0xfdfff9ff 0x4d0a262109a550b4291884 (by decide +kernel)
private def pack_E6970Receipt33_chunk100 := witnessRule 33 40 64 590262 590393 32 2265
  0xbfd7fe7f 0x3ab1a36851362e2d0a470da1441934291b (by decide +kernel)
private def pack_E6970Receipt33_chunk101 := witnessRule 33 40 96 590394 590643 32 2067
  0xff7dfa7e 0xa094508c84830c2a99a0416753320830ca86210605d54508c47134291b (by decide +kernel)
private def pack_E6970Receipt33_chunk102 := witnessRule 33 40 128 590644 590832 10 653
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk103 := witnessRule 33 39 0 600006 600132 32 2657
  0xf7ffffff 0xb4a91b (by decide +kernel)
private def pack_E6970Receipt33_chunk104 := witnessRule 33 39 32 600133 600259 32 2525
  0xf1fff5ff 0x1b4aa16952362e2d2a2709a544d8bca91b (by decide +kernel)
private def pack_E6970Receipt33_chunk105 := witnessRule 33 39 64 600260 600392 32 2207
  0xbfcffc7f 0x61d50d93429188416854364d2a26c5c9a55c2a9a (by decide +kernel)
private def pack_E6970Receipt33_chunk106 := witnessRule 33 39 96 600393 600644 32 2013
  0xffff7efe 0x506a2846422186194ccc20b4299884 (by decide +kernel)
private def pack_E6970Receipt33_chunk107 := witnessRule 33 39 128 600704 600832 7 452
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk108 := witnessRule 33 38 0 610005 610130 32 2607
  0xdfff9fff 0x2d4a26c9a955291a (by decide +kernel)
private def pack_E6970Receipt33_chunk109 := witnessRule 33 38 32 610131 610258 32 2465
  0xefffcfff 0x4d2a262109a950b4a91884 (by decide +kernel)
private def pack_E6970Receipt33_chunk110 := witnessRule 33 38 64 610259 610392 32 2132
  0xbf8ff9ff 0x61d4cc82134a898841695336302d0a470da5441934a91b (by decide +kernel)
private def pack_E6970Receipt33_chunk111 := witnessRule 33 38 96 610393 610705 32 1968
  0xffffffbe 0xa114508c868b4291984 (by decide +kernel)
private def pack_E6970Receipt33_chunk112 := witnessRule 33 38 128 610706 610769 3 191
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk113 := witnessRule 33 37 0 620004 620128 32 2553
  0xdfffffff 0xb5291b (by decide +kernel)
private def pack_E6970Receipt33_chunk114 := witnessRule 33 37 32 620129 620257 32 2413
  0xc7ffafff 0x1b52a16a52362e2d4a2709a944d8bd291b (by decide +kernel)
private def pack_E6970Receipt33_chunk115 := witnessRule 33 37 64 620258 620392 32 2066
  0xffd7faff 0x169523208310a662109a944dcaa9a (by decide +kernel)
private def pack_E6970Receipt33_chunk116 := witnessRule 33 37 96 620393 620768 31 1872
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk117 := witnessRule 33 36 0 630003 630080 32 2491
  0x7fff3fff 0x2d6a26c9ad55a91a (by decide +kernel)
private def pack_E6970Receipt33_chunk118 := witnessRule 33 36 32 630128 630257 32 2349
  0xdfff3fff 0x4d4a262109ad50b5291884 (by decide +kernel)
private def pack_E6970Receipt33_chunk119 := witnessRule 33 36 64 630258 630393 32 1979
  0xffffff7f 0xc4a99b (by decide +kernel)
private def pack_E6970Receipt33_chunk120 := witnessRule 33 36 96 630448 630768 27 1598
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk121 := witnessRule 33 35 0 640002 640079 32 2483
  0x7fffffff 0xb5a91b (by decide +kernel)
private def pack_E6970Receipt33_chunk122 := witnessRule 33 35 32 640080 640257 32 2236
  0xe7ff5fff 0x16b5236302d4a2709ad44d8bda91b (by decide +kernel)
private def pack_E6970Receipt33_chunk123 := witnessRule 33 35 64 640258 640449 32 1912
  0xfff7fd7f 0x12a46a0c5a944cc20c4a91904 (by decide +kernel)
private def pack_E6970Receipt33_chunk124 := witnessRule 33 35 96 640450 640705 22 1265
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk125 := witnessRule 33 34 0 650001 650078 32 2419
  0xfffe7fff 0x9b156291a (by decide +kernel)
private def pack_E6970Receipt33_chunk126 := witnessRule 33 34 32 650079 650258 32 2148
  0xfbff3ffe 0x18a5231084d8a85ad48c420b6289b (by decide +kernel)
private def pack_E6970Receipt33_chunk127 := witnessRule 33 34 64 650259 650451 32 1823
  0xffffff7f 0x5291a03 (by decide +kernel)
private def pack_E6970Receipt33_chunk128 := witnessRule 33 34 96 650452 650704 17 962
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk129 := witnessRule 33 33 0 660000 660078 32 2359
  0x7fffffff 0xb6291b (by decide +kernel)
private def pack_E6970Receipt33_chunk130 := witnessRule 33 33 32 660079 660259 32 2057
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk131 := witnessRule 33 33 64 660260 660454 32 1752
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk132 := witnessRule 33 33 96 660512 660704 12 671
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk133 := witnessRule 33 32 0 670000 670078 32 2239
  0x7ffe7fff 0x2daa26c9b556a91a (by decide +kernel)
private def pack_E6970Receipt33_chunk134 := witnessRule 33 32 32 670128 670261 32 1968
  0xfd7fe7ff 0xb513506312a48613148c818c5a89904 (by decide +kernel)
private def pack_E6970Receipt33_chunk135 := witnessRule 33 32 64 670262 670515 32 1698
  0xfffffff7 0x4a8a09b84 (by decide +kernel)
private def pack_E6970Receipt33_chunk136 := witnessRule 33 32 96 670516 670641 6 331
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk137 := witnessRule 33 31 0 680000 680128 32 2163
  0xdfffffff 0x6a91883 (by decide +kernel)
private def pack_E6970Receipt33_chunk138 := witnessRule 33 31 32 680129 680263 32 1838
  0xffbffdff 0x294504d820c5292104 (by decide +kernel)
private def pack_E6970Receipt33_chunk139 := witnessRule 33 31 64 680264 680640 32 1673
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk140 := witnessRule 33 30 0 690000 690129 32 2081
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk141 := witnessRule 33 30 32 690130 690265 32 1723
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk142 := witnessRule 33 30 64 690320 690640 27 1382
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk143 := witnessRule 33 29 0 700000 700130 32 1996
  0xf3ffafff 0xc51413408316a2822417944c818c62923 (by decide +kernel)
private def pack_E6970Receipt33_chunk144 := witnessRule 33 29 32 700131 700322 32 1637
  0xfffbfebf 0x12a4822e12d451c18c4a9209185 (by decide +kernel)
private def pack_E6970Receipt33_chunk145 := witnessRule 33 29 64 700323 700577 21 1041
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk146 := witnessRule 33 28 0 710000 710131 32 1906
  0xfdffdfff 0x6294904882ea8a09984 (by decide +kernel)
private def pack_E6970Receipt33_chunk147 := witnessRule 33 28 32 710132 710324 32 1555
  0xffffffbf 0x529208b04 (by decide +kernel)
private def pack_E6970Receipt33_chunk148 := witnessRule 33 28 64 710325 710576 16 779
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk149 := witnessRule 33 27 0 720000 720132 32 1811
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk150 := witnessRule 33 27 32 720133 720384 32 1492
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk151 := witnessRule 33 27 64 720385 720576 11 528
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk152 := witnessRule 33 26 0 730000 730133 32 1712
  0xfd7fe7ff 0xb51412708312a4844617149045020c5a8a0908906 (by decide +kernel)
private def pack_E6970Receipt33_chunk153 := witnessRule 33 26 32 730134 730387 32 1442
  0xfffffff7 0x4a920908b85 (by decide +kernel)
private def pack_E6970Receipt33_chunk154 := witnessRule 33 26 64 730388 730513 6 283
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk155 := witnessRule 33 25 0 740000 740134 32 1616
  0xff7ffbff 0x294904845828c529211105 (by decide +kernel)
private def pack_E6970Receipt33_chunk156 := witnessRule 33 25 32 740135 740450 32 1411
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk157 := witnessRule 33 25 64 740512 740512 1 47
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk158 := witnessRule 33 24 0 750000 750135 32 1525
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk159 := witnessRule 33 24 32 750136 750512 29 1246
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk160 := witnessRule 33 23 0 760000 760136 32 1441
  0xffdff5ff 0x12a484422e16d45089c20c4a9219185 (by decide +kernel)
private def pack_E6970Receipt33_chunk161 := witnessRule 33 23 32 760192 760449 24 1002
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk162 := witnessRule 33 22 0 770000 770192 32 1370
  0xfffffbff 0x52921108b05 (by decide +kernel)
private def pack_E6970Receipt33_chunk163 := witnessRule 33 22 32 770193 770448 20 808
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk164 := witnessRule 33 21 0 780000 780194 32 1300
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk165 := witnessRule 33 21 32 780195 780448 16 631
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk166 := witnessRule 33 20 0 790000 790195 32 1233
  0xfffffdff 0x4a921908b85 (by decide +kernel)
private def pack_E6970Receipt33_chunk167 := witnessRule 33 20 32 790196 790385 12 461
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk168 := witnessRule 33 19 0 800000 800197 32 1178
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk169 := witnessRule 33 19 32 800256 800384 8 301
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk170 := witnessRule 33 18 0 810000 810257 32 1127
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk171 := witnessRule 33 18 32 810258 810384 5 184
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk172 := witnessRule 33 17 0 820000 820320 32 1083
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk173 := witnessRule 33 17 32 820321 820321 1 36
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk174 := witnessRule 33 16 0 830000 830320 30 975
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk175 := witnessRule 33 15 0 840000 840320 27 842
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk176 := witnessRule 33 14 0 850000 850257 24 714
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk177 := witnessRule 33 13 0 860000 860256 21 599
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk178 := witnessRule 33 12 0 870000 870256 19 519
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk179 := witnessRule 33 11 0 880000 880193 16 417
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk180 := witnessRule 33 10 0 890000 890192 14 349
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk181 := witnessRule 33 9 0 900000 900192 12 287
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk182 := witnessRule 33 8 0 910000 910129 10 227
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk183 := witnessRule 33 7 0 920000 920128 8 173
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk184 := witnessRule 33 6 0 930000 930128 7 144
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk185 := witnessRule 33 5 0 940000 940065 5 97
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk186 := witnessRule 33 4 0 950000 950064 4 73
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk187 := witnessRule 33 3 0 960000 960064 3 52
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk188 := witnessRule 33 2 0 970000 970001 2 32
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk189 := witnessRule 33 1 0 980000 980000 1 15
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt33_chunk190 := witnessRule 33 0 0 990000 990000 1 14
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt33_chunks : List (Chunk 33) := [pack_E6970Receipt33_chunk0, pack_E6970Receipt33_chunk1, pack_E6970Receipt33_chunk2, pack_E6970Receipt33_chunk3, pack_E6970Receipt33_chunk4, pack_E6970Receipt33_chunk5, pack_E6970Receipt33_chunk6, pack_E6970Receipt33_chunk7, pack_E6970Receipt33_chunk8, pack_E6970Receipt33_chunk9, pack_E6970Receipt33_chunk10, pack_E6970Receipt33_chunk11, pack_E6970Receipt33_chunk12, pack_E6970Receipt33_chunk13, pack_E6970Receipt33_chunk14, pack_E6970Receipt33_chunk15, pack_E6970Receipt33_chunk16, pack_E6970Receipt33_chunk17, pack_E6970Receipt33_chunk18, pack_E6970Receipt33_chunk19, pack_E6970Receipt33_chunk20, pack_E6970Receipt33_chunk21, pack_E6970Receipt33_chunk22, pack_E6970Receipt33_chunk23, pack_E6970Receipt33_chunk24, pack_E6970Receipt33_chunk25, pack_E6970Receipt33_chunk26, pack_E6970Receipt33_chunk27, pack_E6970Receipt33_chunk28, pack_E6970Receipt33_chunk29, pack_E6970Receipt33_chunk30, pack_E6970Receipt33_chunk31, pack_E6970Receipt33_chunk32, pack_E6970Receipt33_chunk33, pack_E6970Receipt33_chunk34, pack_E6970Receipt33_chunk35, pack_E6970Receipt33_chunk36, pack_E6970Receipt33_chunk37, pack_E6970Receipt33_chunk38, pack_E6970Receipt33_chunk39, pack_E6970Receipt33_chunk40, pack_E6970Receipt33_chunk41, pack_E6970Receipt33_chunk42, pack_E6970Receipt33_chunk43, pack_E6970Receipt33_chunk44, pack_E6970Receipt33_chunk45, pack_E6970Receipt33_chunk46, pack_E6970Receipt33_chunk47, pack_E6970Receipt33_chunk48, pack_E6970Receipt33_chunk49, pack_E6970Receipt33_chunk50, pack_E6970Receipt33_chunk51, pack_E6970Receipt33_chunk52, pack_E6970Receipt33_chunk53, pack_E6970Receipt33_chunk54, pack_E6970Receipt33_chunk55, pack_E6970Receipt33_chunk56, pack_E6970Receipt33_chunk57, pack_E6970Receipt33_chunk58, pack_E6970Receipt33_chunk59, pack_E6970Receipt33_chunk60, pack_E6970Receipt33_chunk61, pack_E6970Receipt33_chunk62, pack_E6970Receipt33_chunk63, pack_E6970Receipt33_chunk64, pack_E6970Receipt33_chunk65, pack_E6970Receipt33_chunk66, pack_E6970Receipt33_chunk67, pack_E6970Receipt33_chunk68, pack_E6970Receipt33_chunk69, pack_E6970Receipt33_chunk70, pack_E6970Receipt33_chunk71, pack_E6970Receipt33_chunk72, pack_E6970Receipt33_chunk73, pack_E6970Receipt33_chunk74, pack_E6970Receipt33_chunk75, pack_E6970Receipt33_chunk76, pack_E6970Receipt33_chunk77, pack_E6970Receipt33_chunk78, pack_E6970Receipt33_chunk79, pack_E6970Receipt33_chunk80, pack_E6970Receipt33_chunk81, pack_E6970Receipt33_chunk82, pack_E6970Receipt33_chunk83, pack_E6970Receipt33_chunk84, pack_E6970Receipt33_chunk85, pack_E6970Receipt33_chunk86, pack_E6970Receipt33_chunk87, pack_E6970Receipt33_chunk88, pack_E6970Receipt33_chunk89, pack_E6970Receipt33_chunk90, pack_E6970Receipt33_chunk91, pack_E6970Receipt33_chunk92, pack_E6970Receipt33_chunk93, pack_E6970Receipt33_chunk94, pack_E6970Receipt33_chunk95, pack_E6970Receipt33_chunk96, pack_E6970Receipt33_chunk97, pack_E6970Receipt33_chunk98, pack_E6970Receipt33_chunk99, pack_E6970Receipt33_chunk100, pack_E6970Receipt33_chunk101, pack_E6970Receipt33_chunk102, pack_E6970Receipt33_chunk103, pack_E6970Receipt33_chunk104, pack_E6970Receipt33_chunk105, pack_E6970Receipt33_chunk106, pack_E6970Receipt33_chunk107, pack_E6970Receipt33_chunk108, pack_E6970Receipt33_chunk109, pack_E6970Receipt33_chunk110, pack_E6970Receipt33_chunk111, pack_E6970Receipt33_chunk112, pack_E6970Receipt33_chunk113, pack_E6970Receipt33_chunk114, pack_E6970Receipt33_chunk115, pack_E6970Receipt33_chunk116, pack_E6970Receipt33_chunk117, pack_E6970Receipt33_chunk118, pack_E6970Receipt33_chunk119, pack_E6970Receipt33_chunk120, pack_E6970Receipt33_chunk121, pack_E6970Receipt33_chunk122, pack_E6970Receipt33_chunk123, pack_E6970Receipt33_chunk124, pack_E6970Receipt33_chunk125, pack_E6970Receipt33_chunk126, pack_E6970Receipt33_chunk127, pack_E6970Receipt33_chunk128, pack_E6970Receipt33_chunk129, pack_E6970Receipt33_chunk130, pack_E6970Receipt33_chunk131, pack_E6970Receipt33_chunk132, pack_E6970Receipt33_chunk133, pack_E6970Receipt33_chunk134, pack_E6970Receipt33_chunk135, pack_E6970Receipt33_chunk136, pack_E6970Receipt33_chunk137, pack_E6970Receipt33_chunk138, pack_E6970Receipt33_chunk139, pack_E6970Receipt33_chunk140, pack_E6970Receipt33_chunk141, pack_E6970Receipt33_chunk142, pack_E6970Receipt33_chunk143, pack_E6970Receipt33_chunk144, pack_E6970Receipt33_chunk145, pack_E6970Receipt33_chunk146, pack_E6970Receipt33_chunk147, pack_E6970Receipt33_chunk148, pack_E6970Receipt33_chunk149, pack_E6970Receipt33_chunk150, pack_E6970Receipt33_chunk151, pack_E6970Receipt33_chunk152, pack_E6970Receipt33_chunk153, pack_E6970Receipt33_chunk154, pack_E6970Receipt33_chunk155, pack_E6970Receipt33_chunk156, pack_E6970Receipt33_chunk157, pack_E6970Receipt33_chunk158, pack_E6970Receipt33_chunk159, pack_E6970Receipt33_chunk160, pack_E6970Receipt33_chunk161, pack_E6970Receipt33_chunk162, pack_E6970Receipt33_chunk163, pack_E6970Receipt33_chunk164, pack_E6970Receipt33_chunk165, pack_E6970Receipt33_chunk166, pack_E6970Receipt33_chunk167, pack_E6970Receipt33_chunk168, pack_E6970Receipt33_chunk169, pack_E6970Receipt33_chunk170, pack_E6970Receipt33_chunk171, pack_E6970Receipt33_chunk172, pack_E6970Receipt33_chunk173, pack_E6970Receipt33_chunk174, pack_E6970Receipt33_chunk175, pack_E6970Receipt33_chunk176, pack_E6970Receipt33_chunk177, pack_E6970Receipt33_chunk178, pack_E6970Receipt33_chunk179, pack_E6970Receipt33_chunk180, pack_E6970Receipt33_chunk181, pack_E6970Receipt33_chunk182, pack_E6970Receipt33_chunk183, pack_E6970Receipt33_chunk184, pack_E6970Receipt33_chunk185, pack_E6970Receipt33_chunk186, pack_E6970Receipt33_chunk187, pack_E6970Receipt33_chunk188, pack_E6970Receipt33_chunk189, pack_E6970Receipt33_chunk190]
def rows33 := rowsFrom pack_E6970Receipt33_chunks
theorem good33 : ∀ r ∈ rows33, good 33 r = true := rowsFrom_good pack_E6970Receipt33_chunks
theorem sorted33 : rows33.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt33_chunks 0 (by decide +kernel)).1
theorem mass33 (i : Fin 61) :
    bandCount 33 (i.val : ℤ) 60 16 ≤ (rows33.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt33_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 33 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt33_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total33 : (rows33.map (price 33)).sum = 379472 :=
  (total_eq pack_E6970Receipt33_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt33

section Pack_E6970Receipt34

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt34_chunk0 := witnessA6966Final 34 60 0 420026 420338 32 3350
  0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk1 := witnessA6966Final 34 60 32 420339 420586 32 3311
  0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk2 := witnessA6966Final 34 60 64 420587 420775 32 3286
  0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk3 := witnessA6966Final 34 60 96 420776 420965 32 3225
  0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk4 := witnessA6966Final 34 60 128 420966 421030 9 879
  0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk5 := witnessRule 34 59 0 430025 430335 32 3271
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk6 := witnessRule 34 59 32 430336 430528 32 3222
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk7 := witnessRule 34 59 64 430529 430717 32 3190
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk8 := witnessRule 34 59 96 430769 430960 32 3146
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk9 := witnessRule 34 59 128 430961 431029 13 1240
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk10 := witnessRule 34 58 0 440024 440277 32 3209
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk11 := witnessRule 34 58 32 440278 440523 32 3166
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk12 := witnessRule 34 58 64 440524 440710 32 3124
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk13 := witnessRule 34 58 96 440711 440899 32 3056
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk14 := witnessRule 34 58 128 440900 441029 18 1670
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk15 := witnessRule 34 57 0 450023 450274 32 3171
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk16 := witnessRule 34 57 32 450275 450466 32 3087
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk17 := witnessRule 34 57 64 450519 450653 32 3061
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk18 := witnessRule 34 57 96 450705 450840 32 2993
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk19 := witnessRule 34 57 128 450841 451028 21 1905
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk20 := witnessRule 34 56 0 460022 460271 32 3139
  0xffffffbf 0x130aa (by decide +kernel)
private def pack_E6970Receipt34_chunk21 := witnessRule 34 56 32 460272 460461 32 3056
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk22 := witnessRule 34 56 64 460462 460647 32 3017
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk23 := witnessRule 34 56 96 460648 460834 32 2919
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk24 := witnessRule 34 56 128 460835 461028 25 2209
  0x1fffbff 0xb99a (by decide +kernel)
private def pack_E6970Receipt34_chunk25 := witnessRule 34 55 0 470021 470215 32 3083
  0x5fefdfff 0x361542c8694c8b0a91b (by decide +kernel)
private def pack_E6970Receipt34_chunk26 := witnessRule 34 55 32 470269 470457 32 3051
  0xffffff7f 0x1319a (by decide +kernel)
private def pack_E6970Receipt34_chunk27 := witnessRule 34 55 64 470458 470641 32 2954
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk28 := witnessRule 34 55 96 470642 470776 32 2870
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk29 := witnessRule 34 55 128 470777 471027 27 2330
  0x7ffdfbf 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt34_chunk30 := witnessRule 34 54 0 480020 480212 32 3060
  0xfeff7f3f 0x36151064c2a2621098950b0a91884 (by decide +kernel)
private def pack_E6970Receipt34_chunk31 := witnessRule 34 54 32 480213 480401 32 2979
  0xaff5fbff 0x1321a175342ca68dc5441930a91b (by decide +kernel)
private def pack_E6970Receipt34_chunk32 := witnessRule 34 54 64 480402 480585 32 2955
  0x5febfabe 0x27163368e2885c98cd93a1a363342e2c86cdc504da30aa (by decide +kernel)
private def pack_E6970Receipt34_chunk33 := witnessRule 34 54 96 480586 480771 32 2827
  0x7ffff9ff 0x6e668dccd238a2 (by decide +kernel)
private def pack_E6970Receipt34_chunk34 := witnessRule 34 54 128 480772 481027 30 2526
  0x3ffef9fb 0x175342e2c86c9c58cd8b9319b (by decide +kernel)
private def pack_E6970Receipt34_chunk35 := witnessRule 34 53 0 490019 490210 32 3036
  0xfc7e3f5f 0x26251362e4c4ac554d1b12a16252362e2c4a27098944d8b9291b (by decide +kernel)
private def pack_E6970Receipt34_chunk36 := witnessRule 34 53 32 490211 490397 32 2954
  0xfebfc7f1 0x46151062e4c2a26214d8544c42130a99b1716152310a6c4a898548c420b0aa1b (by decide +kernel)
private def pack_E6970Receipt34_chunk37 := witnessRule 34 53 64 490398 490580 32 2919
  0xfdffbffb 0x4ca68d8548d8b9b0a884 (by decide +kernel)
private def pack_E6970Receipt34_chunk38 := witnessRule 34 53 96 490581 490714 32 2752
  0xe8f57eab 0x2e6c66c9c590d9b9988347141368c6685c990d93a9a561546c8685c594da38a883 (by decide +kernel)
private def pack_E6970Receipt34_chunk39 := witnessRule 34 53 128 490768 491026 31 2559
  0x7ffbe7cb 0x5d8d0b8b29b27164362e4c86c9c98cd9ba1a (by decide +kernel)
private def pack_E6970Receipt34_chunk40 := witnessRule 34 52 0 500018 500207 32 3011
  0xf3fdfe7f 0x1b1288326252364c4a2621098d50b1291884 (by decide +kernel)
private def pack_E6970Receipt34_chunk41 := witnessRule 34 52 32 500208 500393 32 2926
  0xf0fe2fd7 0xd8944d8b9b12b16155364e2c4a2711895131291b1726251384e4a46cd8944d8b8b1291c (by decide +kernel)
private def pack_E6970Receipt34_chunk42 := witnessRule 34 52 64 500394 500525 32 2832
  0x8ff0ff07 0x1736151310a2e4c2a6709c58548c42a30a8988436153362e4c2a462145c58550e2312a3615231084c2a86c9c98958b8aa9b (by decide +kernel)
private def pack_E6970Receipt34_chunk43 := witnessRule 34 52 96 500526 500709 32 2762
  0x5ebfebfe 0x2e2cc6d1c544c42230a91b2736151082e8c2a2109c98544c42ab0a883 (by decide +kernel)
private def pack_E6970Receipt34_chunk44 := witnessRule 34 52 128 500710 501025 32 2579
  0xffef3c18 0x2ee685c598d938b29b1736331082e4ca6c9c590c4213b1a47231168c6620cd94d0b9321884 (by decide +kernel)
private def pack_E6970Receipt34_chunk45 := witnessRule 34 52 160 501026 501026 1 83
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk46 := witnessRule 34 51 0 510017 510205 32 2979
  0xe3f8febf 0x26351362e4c6ac954d1b1aa16352362e2c6a27098d44d8b9a91b (by decide +kernel)
private def pack_E6970Receipt34_chunk47 := witnessRule 34 51 32 510206 510389 32 2864
  0x8ff8ff1f 0x231288336252362e4c4a26214d8944c42131299b1716252310a6c6a898948c420b12a1b (by decide +kernel)
private def pack_E6970Receipt34_chunk48 := witnessRule 34 51 64 510390 510520 32 2858
  0x7f17f8ff 0x3725236ac4a8d8948d8b9b1289c2716252388c4a26c5cd894420b931291c (by decide +kernel)
private def pack_E6970Receipt34_chunk49 := witnessRule 34 51 96 510521 510706 32 2675
  0xe13c07e1 0x2b0a8988446153362e6c2a462145c98550e138aa9b4725136ac4a918548c421b0aa1b27362562e2c2aa70dc58944e239288346251362e8c4ac98554d93931289c (by decide +kernel)
private def pack_E6970Receipt34_chunk50 := witnessRule 34 51 128 510707 511024 32 2524
  0xfffee4e1 0xb8b39b36531064ce685e0d1b8aa1b36154362e6c2a6709c98548c42938b0aa1c (by decide +kernel)
private def pack_E6970Receipt34_chunk51 := witnessRule 34 51 160 511025 511025 1 81
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk52 := witnessRule 34 50 0 520016 520202 32 2923
  0x9ff7fcff 0x1b1a88326352364c6a2621099150b1a91884 (by decide +kernel)
private def pack_E6970Receipt34_chunk53 := witnessRule 34 50 32 520203 520335 32 2854
  0x3fc5fd7f 0x16255364e2c6a27118d5131a91b1726351384e6a46cd8d44d8b8b1a91c (by decide +kernel)
private def pack_E6970Receipt34_chunk54 := witnessRule 34 50 64 520336 520515 32 2840
  0xf0ff83fc 0x8c4a26210d894cd8b9312918851716254388c6a8d8948c421312a1b27263562e4aa6cd8d44d8b9b1ab (by decide +kernel)
private def pack_E6970Receipt34_chunk55 := witnessRule 34 50 96 520516 520649 32 2611
  0xbc3fc1f 0x118948d9b0aa188426156364e4c4a470dc94cdab1289b1746251082e6c4a4709c98944c42ab1288346252362e6c4a262145c9894ce138b1291885 (by decide +kernel)
private def pack_E6970Receipt34_chunk56 := witnessRule 34 50 128 520650 520962 32 2480
  0xffff961f 0x4c2ac6c5c98554e138ab1b4615331086c2aa6c5c98550c428b8b0ab1c (by decide +kernel)
private def pack_E6970Receipt34_chunk57 := witnessRule 34 50 160 521024 521025 2 159
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk58 := witnessRule 34 49 0 530015 530149 32 2875
  0x1fe3fd7f 0x26451362e4c8acd54d1b22a16452362e2c8a27099144d8ba291b (by decide +kernel)
private def pack_E6970Receipt34_chunk59 := witnessRule 34 49 32 530201 530332 32 2862
  0xff1ff1ff 0xd8d44c42131a99b1716352310a6c8a898d48c420b1aa1b (by decide +kernel)
private def pack_E6970Receipt34_chunk60 := witnessRule 34 49 64 530333 530462 32 2722
  0x17fc7fe3 0x158d51b1a91b1736351384e2c6a47118d44d8b9b1a8841726352388c6a20cd8d48d8b931a89885 (by decide +kernel)
private def pack_E6970Receipt34_chunk61 := witnessRule 34 49 96 530512 530646 32 2612
  0x3e27e17f 0x1726254384e2c4a66215589481a3129188436254362e2c4aa70dc58d44e231a89b17463564c4aa6c9c98d44e1b9a91b (by decide +kernel)
private def pack_E6970Receipt34_chunk62 := witnessRule 34 49 128 530647 530962 32 2424
  0xfffe3c38 0xd8554c42130ab9b1716156310a6c4a86c98558c420b0ac1b2716254388c4a264111894cd8b9b1291885 (by decide +kernel)
private def pack_E6970Receipt34_chunk63 := witnessRule 34 49 160 531024 531024 1 78
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk64 := witnessRule 34 48 0 540014 540147 32 2859
  0xffdff9ff 0x4c8a2621099550b2291884 (by decide +kernel)
private def pack_E6970Receipt34_chunk65 := witnessRule 34 48 32 540148 540328 32 2826
  0xf8bfd7fc 0x464544c8a46c5c99144e13a291b36451362e2c8a470d91441932291b (by decide +kernel)
private def pack_E6970Receipt34_chunk66 := witnessRule 34 48 64 540329 540457 32 2718
  0xffc1ff0f 0x2322a3635231084c6a86c9c99158b9aa9b36451362e6c8ac58d54d938b2289c (by decide +kernel)
private def pack_E6970Receipt34_chunk67 := witnessRule 34 48 96 540458 540643 32 2523
  0xf07e0ff0 0x118d44c421b1a99b1736352384e4c6a262149c58d4ce2b1a88346352362e6c6a262145c98d4ce138b1a918854635131086c6a66c5c98d48c428b8b1aa1c (by decide +kernel)
private def pack_E6970Receipt34_chunk68 := witnessRule 34 48 128 540644 540961 32 2371
  0xfffd60e2 0x4c2ac6410568d1b129990436255362e4c4a862145c58958e1392a98844625232086c4a8621098958d8b92b9b (by decide +kernel)
private def pack_E6970Receipt34_chunk69 := witnessRule 34 48 160 541024 541024 1 77
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk70 := witnessRule 34 47 0 550013 550145 32 2842
  0xff8ffaff 0x1b2aa16552362e2caa27099544d8baa91b (by decide +kernel)
private def pack_E6970Receipt34_chunk71 := witnessRule 34 47 32 550146 550325 32 2771
  0xe3ff1ff8 0x1b228988426453362e2c8a46214d95513229188416454364caa26c5c9955a2a9a (by decide +kernel)
private def pack_E6970Receipt34_chunk72 := witnessRule 34 47 64 550326 550454 32 2701
  0xfe3ff8ff 0x119144d8b9b228841726452388c8a20cd9148d8b932289885 (by decide +kernel)
private def pack_E6970Receipt34_chunk73 := witnessRule 34 47 96 550455 550641 32 2439
  0xe1785f8b 0x118d48c421b1aa1b1726353310a2e2c6aa70dcd4508e232289b3635331084c6aa6c9c99144e1ba291b564546c8a46c5cd9144e138b2291c (by decide +kernel)
private def pack_E6970Receipt34_chunk74 := witnessRule 34 47 128 550642 550961 31 2251
  0x7fffe0c1 0xd8950c821312b188416258362e4ae6210605c54514e9b1a9988426355362e4c6a8709c58d4cc42939aa9b (by decide +kernel)
private def pack_E6970Receipt34_chunk75 := witnessRule 34 46 0 560012 560143 32 2829
  0xff7ff3ff 0x4caa2621099950b2a91884 (by decide +kernel)
private def pack_E6970Receipt34_chunk76 := witnessRule 34 46 32 560144 560273 32 2660
  0x17fd7fe7 0x465544caa46c5c99544e13aa91b36551362e2caa470d95441932a91b (by decide +kernel)
private def pack_E6970Receipt34_chunk77 := witnessRule 34 46 64 560322 560450 32 2709
  0xe0ffc3ff 0x232aa3645231084c8a86c9c99558ba2a9b36551362e6caac59154d938b2a89c (by decide +kernel)
private def pack_E6970Receipt34_chunk78 := witnessRule 34 46 96 560451 560585 32 2388
  0x7c1fc3f 0x118d44cc21b2299b2635531082c6ae6c9c5914ce232290346452362e6c8a262145c9914ce138b22918854645131086c8a66c5c99148c428b8b22a1c (by decide +kernel)
private def pack_E6970Receipt34_chunk79 := witnessRule 34 46 128 560640 560960 30 2142
  0x3fff8387 0x1b1299a042625533082c4ae6410964c41940aa98843635431084c6ac6c5c58d54c428b9ab9b (by decide +kernel)
private def pack_E6970Receipt34_chunk80 := witnessRule 34 45 0 570011 570141 32 2809
  0xfe3ff5ff 0x1b32a16652362e2cca27099944d8bb291b (by decide +kernel)
private def pack_E6970Receipt34_chunk81 := witnessRule 34 45 32 570142 570270 32 2646
  0x7ff1ffc7 0x2e2caa46214d995132a9188416554364cca26c5c9995aaa9a (by decide +kernel)
private def pack_E6970Receipt34_chunk82 := witnessRule 34 45 64 570271 570448 32 2603
  0x8ffe3ffc 0x46551362e6caa2105c99548e232a88336552362e4caa26214d9544c42132a99b (by decide +kernel)
private def pack_E6970Receipt34_chunk83 := witnessRule 34 45 96 570449 570584 32 2343
  0x38bf17f 0xd9148c821b22a1b1726453310a2e2c8aa709d150c421b9a8a1188d4645132086c8a6621099154d8ba2b1b46551066caa46c5cd9544e138b2a91c (by decide +kernel)
private def pack_E6970Receipt34_chunk84 := witnessRule 34 45 128 570585 570960 28 1958
  0xfffd507 0x2625435084b0660ca0514c461b1a999842635532082c6ae6210d64d1412a9b (by decide +kernel)
private def pack_E6970Receipt34_chunk85 := witnessRule 34 44 0 580010 580139 32 2785
  0xfdffe7ff 0x4cca2621099d50b3291884 (by decide +kernel)
private def pack_E6970Receipt34_chunk86 := witnessRule 34 44 32 580140 580267 32 2642
  0xffd7ff3f 0x36651362e2cca470d99441933291b (by decide +kernel)
private def pack_E6970Receipt34_chunk87 := witnessRule 34 44 64 580268 580395 32 2520
  0x1ff0ffe2 0x4caa86c9c99958baaa9b36651362e6ccac59554d938b3289c466544cca46c5c99944e13b291b (by decide +kernel)
private def pack_E6970Receipt34_chunk88 := witnessRule 34 44 96 580396 580582 32 2283
  0xf17c3fc 0x99154c420b22b9b174563108302e6a28874d9548c42132aa1b1726553384eaa86d19544c421b2a99b1726552310a2e2caa87119951b2a91884 (by decide +kernel)
private def pack_E6970Receipt34_chunk89 := witnessRule 34 44 128 580583 580897 26 1780
  0x3ffff0e 0x131aa1a041635633086b0640ca0950c821b2299904 (by decide +kernel)
private def pack_E6970Receipt34_chunk90 := witnessRule 34 43 0 590009 590137 32 2753
  0xf8ffebff 0x1b3aa16752362e2cea27099d44d8bba91b (by decide +kernel)
private def pack_E6970Receipt34_chunk91 := witnessRule 34 43 32 590138 590264 32 2634
  0xff1ffe3f 0xd9d513329188416654364cea26c5c99d5b2a9a (by decide +kernel)
private def pack_E6970Receipt34_chunk92 := witnessRule 34 43 64 590265 590393 32 2438
  0xffc7ff8f 0x11994419b3291b1726651310a6cca262109994cd8b8b3291885 (by decide +kernel)
private def pack_E6970Receipt34_chunk93 := witnessRule 34 43 96 590394 590582 32 2201
  0x70fc3f8 0x2645433082c8ac6411160c41941aa1884182725142321c6caa6621099554d8b8b2aa188517556366cca46c99550c420b2ab1b2716652388cca26c5cd994420b933291c (by decide +kernel)
private def pack_E6970Receipt34_chunk94 := witnessRule 34 43 128 590583 590896 23 1546
  0x7fff47 0x2635336086ae680ca094cd02140a8a2188886 (by decide +kernel)
private def pack_E6970Receipt34_chunk95 := witnessRule 34 42 0 600008 600135 32 2717
  0xf7ffcfff 0x4cea262109a150b3a91884 (by decide +kernel)
private def pack_E6970Receipt34_chunk96 := witnessRule 34 42 32 600136 600261 32 2614
  0xfd7ff9ff 0x36751362e2cea470d9d441933a91b (by decide +kernel)
private def pack_E6970Receipt34_chunk97 := witnessRule 34 42 64 600262 600391 32 2379
  0xff0ffc5f 0x36751362e6ceac59954d938b3a89c467544cea46c5c99d44e13ba91b (by decide +kernel)
private def pack_E6970Receipt34_chunk98 := witnessRule 34 42 96 600392 600581 32 2127
  0x8f0f07e2 0x4573306506a66610a094510c46932aa1904165563108ab068a1150d9b328990436653362e4cca462145c59950e13b29988446652066cca4621099950d8bb2a9b (by decide +kernel)
private def pack_E6970Receipt34_chunk99 := witnessRule 34 42 128 600582 600896 21 1386
  0x1fffd6 0x6ac6c0ca05450cc44c3132299a84 (by decide +kernel)
private def pack_E6970Receipt34_chunk100 := witnessRule 34 41 0 610007 610133 32 2673
  0xe3ffd7ff 0x1b42a16852362e2d0a2709a144d8bc291b (by decide +kernel)
private def pack_E6970Receipt34_chunk101 := witnessRule 34 41 32 610134 610259 32 2562
  0xf1fff1ff 0xda15133a9188416754364d0a26c5c9a15baa9a (by decide +kernel)
private def pack_E6970Receipt34_chunk102 := witnessRule 34 41 64 610260 610390 32 2321
  0xfe3ff8ff 0x119d4419b3a91b1726751310a6cea2621099d4cd8b8b3a91885 (by decide +kernel)
private def pack_E6970Receipt34_chunk103 := witnessRule 34 41 96 610391 610582 32 2060
  0xd34f8be2 0x1158d4194128a1988906281715142331c4caa6681155cc819422999043665232084cca8621059958d8c0baa8a19d3675131084cea66c5c99d48e13ba99b (by decide +kernel)
private def pack_E6970Receipt34_chunk104 := witnessRule 34 41 128 610583 610833 17 1104
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk105 := witnessRule 34 40 0 620006 620131 32 2625
  0xdfff9fff 0x4d0a262109a550b4291884 (by decide +kernel)
private def pack_E6970Receipt34_chunk106 := witnessRule 34 40 32 620132 620257 32 2514
  0xd7ffcfff 0x36851362e2d0a470da1441934291b (by decide +kernel)
private def pack_E6970Receipt34_chunk107 := witnessRule 34 40 64 620258 620389 32 2272
  0xfd3fe2ff 0x6d0a26c59d54d938b4289c468544d0a46c5c9a144e13c291b (by decide +kernel)
private def pack_E6970Receipt34_chunk108 := witnessRule 34 40 96 620390 620582 32 2000
  0xf7d7a7e3 0x14128a1188a065563406506a2866222189994ccc232b98832855331086cea4621099d50d8b8b3a99885 (by decide +kernel)
private def pack_E6970Receipt34_chunk109 := witnessRule 34 40 128 620640 620832 14 895
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk110 := witnessRule 34 39 0 630005 630129 32 2569
  0x8fffafff 0x1b4aa16952362e2d2a2709a544d8bca91b (by decide +kernel)
private def pack_E6970Receipt34_chunk111 := witnessRule 34 39 32 630130 630256 32 2454
  0x8fff8fff 0xda5513429188416854364d2a26c5c9a55c2a9a (by decide +kernel)
private def pack_E6970Receipt34_chunk112 := witnessRule 34 39 64 630257 630389 32 2201
  0xfe3fe3ff 0xda148d8b9342898851716853386d0a262109a14cd8b8b4291885 (by decide +kernel)
private def pack_E6970Receipt34_chunk113 := witnessRule 34 39 96 630390 630641 32 1950
  0xff7bf5f4 0x702846830a0d4508c44c332b19832845143311a4cea66411d5cd143299b (by decide +kernel)
private def pack_E6970Receipt34_chunk114 := witnessRule 34 39 128 630642 630832 10 631
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk115 := witnessRule 34 38 0 640004 640081 32 2509
  0x7fff3fff 0x4d2a262109a950b4a91884 (by decide +kernel)
private def pack_E6970Receipt34_chunk116 := witnessRule 34 38 32 640128 640206 32 2406
  0x5ffe7fff 0x36951362e2d2a470da5441934a91b (by decide +kernel)
private def pack_E6970Receipt34_chunk117 := witnessRule 34 38 64 640256 640389 32 2133
  0xfc5fc5ff 0x3685132084d0a662105a154d8c0bba8a11d36951064d2a46c5c9a544e13ca91b (by decide +kernel)
private def pack_E6970Receipt34_chunk118 := witnessRule 34 38 96 640390 640643 32 1910
  0xfffffdf5 0x508a28462241899d48d023ab1903 (by decide +kernel)
private def pack_E6970Receipt34_chunk119 := witnessRule 34 38 128 640644 640769 6 373
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk120 := witnessRule 34 37 0 650003 650080 32 2497
  0x3fff5fff 0x16a52362e2d4a2709a944d8bd291b (by decide +kernel)
private def pack_E6970Receipt34_chunk121 := witnessRule 34 37 32 650081 650206 32 2294
  0x1ffe3ffe 0x6d4a89a548c420b4aa1b26a51362e4d4ae554d1b52a (by decide +kernel)
private def pack_E6970Receipt34_chunk122 := witnessRule 34 37 64 650256 650390 32 2038
  0xbf5fe3ff 0xa154508c444313429198485631066d2a262109a54cd8b8b4a91885 (by decide +kernel)
private def pack_E6970Receipt34_chunk123 := witnessRule 34 37 96 650391 650706 32 1881
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk124 := witnessRule 34 37 128 650768 650768 1 62
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk125 := witnessRule 34 36 0 660002 660078 32 2487
  0xfffe7fff 0x9ad50b5291884 (by decide +kernel)
private def pack_E6970Receipt34_chunk126 := witnessRule 34 36 32 660079 660205 32 2188
  0x5ffcfffd 0x1b5289b1716a52386d4a20c9a948d935289884 (by decide +kernel)
private def pack_E6970Receipt34_chunk127 := witnessRule 34 36 64 660256 660391 32 1951
  0xfff7fdff 0xa194508c46cab1a (by decide +kernel)
private def pack_E6970Receipt34_chunk128 := witnessRule 34 36 96 660392 660768 29 1673
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk129 := witnessRule 34 35 0 670001 670078 32 2424
  0x7ffebfff 0x2e2d6a2709ad44d8bda91b (by decide +kernel)
private def pack_E6970Receipt34_chunk130 := witnessRule 34 35 32 670079 670256 32 2109
  0xcffe3ffc 0x4d4a462105a950d935a89b1726b574aa68dad50b5a91b (by decide +kernel)
private def pack_E6970Receipt34_chunk131 := witnessRule 34 35 64 670257 670448 32 1856
  0xffeffaff 0x2d0a46c109a544d024aa9903 (by decide +kernel)
private def pack_E6970Receipt34_chunk132 := witnessRule 34 35 96 670449 670705 23 1299
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk133 := witnessRule 34 34 0 680000 680077 32 2363
  0xfffcffff 0x9b150b5a91884 (by decide +kernel)
private def pack_E6970Receipt34_chunk134 := witnessRule 34 34 32 680078 680257 32 2029
  0xf7fe7ffd 0xa5531066d6a20c9ad48d935a89884 (by decide +kernel)
private def pack_E6970Receipt34_chunk135 := witnessRule 34 34 64 680258 680450 32 1770
  0xfffffeff 0xb4a91a84 (by decide +kernel)
private def pack_E6970Receipt34_chunk136 := witnessRule 34 34 96 680451 680704 18 999
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk137 := witnessRule 34 33 0 690000 690078 32 2245
  0x3ffebfff 0x16c52362e2d8a2709b144d8be291b (by decide +kernel)
private def pack_E6970Receipt34_chunk138 := witnessRule 34 33 32 690079 690259 32 1955
  0xfffffffe 0x1b62a (by decide +kernel)
private def pack_E6970Receipt34_chunk139 := witnessRule 34 33 64 690260 690454 32 1695
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk140 := witnessRule 34 33 96 690512 690704 12 659
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk141 := witnessRule 34 32 0 700000 700078 32 2129
  0x7ffe7fff 0x4d8a262109b550b6291884 (by decide +kernel)
private def pack_E6970Receipt34_chunk142 := witnessRule 34 32 32 700128 700261 32 1870
  0xfd7fe7ff 0x16a513608312a28268145ad48cc25aa1903 (by decide +kernel)
private def pack_E6970Receipt34_chunk143 := witnessRule 34 32 64 700262 700515 32 1654
  0xfffffff7 0x4a91c03 (by decide +kernel)
private def pack_E6970Receipt34_chunk144 := witnessRule 34 32 96 700516 700641 6 325
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk145 := witnessRule 34 31 0 710000 710128 32 2053
  0xdfff5fff 0x2d8a464109b544d8bea91b (by decide +kernel)
private def pack_E6970Receipt34_chunk146 := witnessRule 34 31 32 710129 710263 32 1749
  0xffbffdff 0x2948dc18c528a09985 (by decide +kernel)
private def pack_E6970Receipt34_chunk147 := witnessRule 34 31 64 710264 710640 32 1631
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk148 := witnessRule 34 30 0 720000 720129 32 1972
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk149 := witnessRule 34 30 32 720130 720265 32 1643
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk150 := witnessRule 34 30 64 720320 720640 27 1347
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk151 := witnessRule 34 29 0 730000 730130 32 1890
  0xf3ffafff 0xc523506316a288105b544cc20c628a09885 (by decide +kernel)
private def pack_E6970Receipt34_chunk152 := witnessRule 34 29 32 730131 730322 32 1565
  0xfffbfebf 0x12a4920ed44e018c4a9208a05 (by decide +kernel)
private def pack_E6970Receipt34_chunk153 := witnessRule 34 29 64 730323 730577 21 1020
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk154 := witnessRule 34 28 0 740000 740131 32 1801
  0xfdffdfff 0x62949044c2ea91a03 (by decide +kernel)
private def pack_E6970Receipt34_chunk155 := witnessRule 34 28 32 740132 740324 32 1492
  0xffffffbf 0x5292403 (by decide +kernel)
private def pack_E6970Receipt34_chunk156 := witnessRule 34 28 64 740325 740576 16 763
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk157 := witnessRule 34 27 0 750000 750132 32 1708
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk158 := witnessRule 34 27 32 750133 750384 32 1437
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk159 := witnessRule 34 27 64 750385 750576 11 517
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk160 := witnessRule 34 26 0 760000 760133 32 1614
  0xfd7fe7ff 0xb51411808312a48242281b1491818c5a8a09205 (by decide +kernel)
private def pack_E6970Receipt34_chunk161 := witnessRule 34 26 32 760134 760387 32 1398
  0xfffffff7 0x4a9209484 (by decide +kernel)
private def pack_E6970Receipt34_chunk162 := witnessRule 34 26 64 760388 760513 6 277
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk163 := witnessRule 34 25 0 770000 770134 32 1524
  0xff7ffbff 0x294904a020c52920908986 (by decide +kernel)
private def pack_E6970Receipt34_chunk164 := witnessRule 34 25 32 770135 770450 32 1369
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk165 := witnessRule 34 25 64 770512 770512 1 46
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk166 := witnessRule 34 24 0 780000 780135 32 1439
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk167 := witnessRule 34 24 32 780136 780512 29 1209
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk168 := witnessRule 34 23 0 790000 790136 32 1364
  0xffdff5ff 0x12a4845212d4504846028c4a921108a06 (by decide +kernel)
private def pack_E6970Receipt34_chunk169 := witnessRule 34 23 32 790192 790449 24 974
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk170 := witnessRule 34 22 0 800000 800192 32 1296
  0xfffffbff 0x529211404 (by decide +kernel)
private def pack_E6970Receipt34_chunk171 := witnessRule 34 22 32 800193 800448 20 787
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk172 := witnessRule 34 21 0 810000 810194 32 1231
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk173 := witnessRule 34 21 32 810195 810448 16 615
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk174 := witnessRule 34 20 0 820000 820195 32 1174
  0xfffffdff 0x4a9219484 (by decide +kernel)
private def pack_E6970Receipt34_chunk175 := witnessRule 34 20 32 820196 820385 12 449
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk176 := witnessRule 34 19 0 830000 830197 32 1123
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk177 := witnessRule 34 19 32 830256 830384 8 293
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk178 := witnessRule 34 18 0 840000 840257 32 1076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk179 := witnessRule 34 18 32 840258 840384 5 179
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk180 := witnessRule 34 17 0 850000 850320 32 1039
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk181 := witnessRule 34 17 32 850321 850321 1 35
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk182 := witnessRule 34 16 0 860000 860320 30 935
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk183 := witnessRule 34 15 0 870000 870320 27 807
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk184 := witnessRule 34 14 0 880000 880257 24 686
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk185 := witnessRule 34 13 0 890000 890256 21 575
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk186 := witnessRule 34 12 0 900000 900256 19 498
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk187 := witnessRule 34 11 0 910000 910193 16 401
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk188 := witnessRule 34 10 0 920000 920192 14 335
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk189 := witnessRule 34 9 0 930000 930192 12 275
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk190 := witnessRule 34 8 0 940000 940129 10 217
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk191 := witnessRule 34 7 0 950000 950128 8 165
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk192 := witnessRule 34 6 0 960000 960128 7 137
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk193 := witnessRule 34 5 0 970000 970065 5 92
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk194 := witnessRule 34 4 0 980000 980064 4 69
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk195 := witnessRule 34 3 0 990000 990064 3 49
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk196 := witnessRule 34 2 0 1000000 1000001 2 30
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk197 := witnessRule 34 1 0 1010000 1010000 1 14
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt34_chunk198 := witnessRule 34 0 0 1020000 1020000 1 13
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt34_chunks : List (Chunk 34) := [pack_E6970Receipt34_chunk0, pack_E6970Receipt34_chunk1, pack_E6970Receipt34_chunk2, pack_E6970Receipt34_chunk3, pack_E6970Receipt34_chunk4, pack_E6970Receipt34_chunk5, pack_E6970Receipt34_chunk6, pack_E6970Receipt34_chunk7, pack_E6970Receipt34_chunk8, pack_E6970Receipt34_chunk9, pack_E6970Receipt34_chunk10, pack_E6970Receipt34_chunk11, pack_E6970Receipt34_chunk12, pack_E6970Receipt34_chunk13, pack_E6970Receipt34_chunk14, pack_E6970Receipt34_chunk15, pack_E6970Receipt34_chunk16, pack_E6970Receipt34_chunk17, pack_E6970Receipt34_chunk18, pack_E6970Receipt34_chunk19, pack_E6970Receipt34_chunk20, pack_E6970Receipt34_chunk21, pack_E6970Receipt34_chunk22, pack_E6970Receipt34_chunk23, pack_E6970Receipt34_chunk24, pack_E6970Receipt34_chunk25, pack_E6970Receipt34_chunk26, pack_E6970Receipt34_chunk27, pack_E6970Receipt34_chunk28, pack_E6970Receipt34_chunk29, pack_E6970Receipt34_chunk30, pack_E6970Receipt34_chunk31, pack_E6970Receipt34_chunk32, pack_E6970Receipt34_chunk33, pack_E6970Receipt34_chunk34, pack_E6970Receipt34_chunk35, pack_E6970Receipt34_chunk36, pack_E6970Receipt34_chunk37, pack_E6970Receipt34_chunk38, pack_E6970Receipt34_chunk39, pack_E6970Receipt34_chunk40, pack_E6970Receipt34_chunk41, pack_E6970Receipt34_chunk42, pack_E6970Receipt34_chunk43, pack_E6970Receipt34_chunk44, pack_E6970Receipt34_chunk45, pack_E6970Receipt34_chunk46, pack_E6970Receipt34_chunk47, pack_E6970Receipt34_chunk48, pack_E6970Receipt34_chunk49, pack_E6970Receipt34_chunk50, pack_E6970Receipt34_chunk51, pack_E6970Receipt34_chunk52, pack_E6970Receipt34_chunk53, pack_E6970Receipt34_chunk54, pack_E6970Receipt34_chunk55, pack_E6970Receipt34_chunk56, pack_E6970Receipt34_chunk57, pack_E6970Receipt34_chunk58, pack_E6970Receipt34_chunk59, pack_E6970Receipt34_chunk60, pack_E6970Receipt34_chunk61, pack_E6970Receipt34_chunk62, pack_E6970Receipt34_chunk63, pack_E6970Receipt34_chunk64, pack_E6970Receipt34_chunk65, pack_E6970Receipt34_chunk66, pack_E6970Receipt34_chunk67, pack_E6970Receipt34_chunk68, pack_E6970Receipt34_chunk69, pack_E6970Receipt34_chunk70, pack_E6970Receipt34_chunk71, pack_E6970Receipt34_chunk72, pack_E6970Receipt34_chunk73, pack_E6970Receipt34_chunk74, pack_E6970Receipt34_chunk75, pack_E6970Receipt34_chunk76, pack_E6970Receipt34_chunk77, pack_E6970Receipt34_chunk78, pack_E6970Receipt34_chunk79, pack_E6970Receipt34_chunk80, pack_E6970Receipt34_chunk81, pack_E6970Receipt34_chunk82, pack_E6970Receipt34_chunk83, pack_E6970Receipt34_chunk84, pack_E6970Receipt34_chunk85, pack_E6970Receipt34_chunk86, pack_E6970Receipt34_chunk87, pack_E6970Receipt34_chunk88, pack_E6970Receipt34_chunk89, pack_E6970Receipt34_chunk90, pack_E6970Receipt34_chunk91, pack_E6970Receipt34_chunk92, pack_E6970Receipt34_chunk93, pack_E6970Receipt34_chunk94, pack_E6970Receipt34_chunk95, pack_E6970Receipt34_chunk96, pack_E6970Receipt34_chunk97, pack_E6970Receipt34_chunk98, pack_E6970Receipt34_chunk99, pack_E6970Receipt34_chunk100, pack_E6970Receipt34_chunk101, pack_E6970Receipt34_chunk102, pack_E6970Receipt34_chunk103, pack_E6970Receipt34_chunk104, pack_E6970Receipt34_chunk105, pack_E6970Receipt34_chunk106, pack_E6970Receipt34_chunk107, pack_E6970Receipt34_chunk108, pack_E6970Receipt34_chunk109, pack_E6970Receipt34_chunk110, pack_E6970Receipt34_chunk111, pack_E6970Receipt34_chunk112, pack_E6970Receipt34_chunk113, pack_E6970Receipt34_chunk114, pack_E6970Receipt34_chunk115, pack_E6970Receipt34_chunk116, pack_E6970Receipt34_chunk117, pack_E6970Receipt34_chunk118, pack_E6970Receipt34_chunk119, pack_E6970Receipt34_chunk120, pack_E6970Receipt34_chunk121, pack_E6970Receipt34_chunk122, pack_E6970Receipt34_chunk123, pack_E6970Receipt34_chunk124, pack_E6970Receipt34_chunk125, pack_E6970Receipt34_chunk126, pack_E6970Receipt34_chunk127, pack_E6970Receipt34_chunk128, pack_E6970Receipt34_chunk129, pack_E6970Receipt34_chunk130, pack_E6970Receipt34_chunk131, pack_E6970Receipt34_chunk132, pack_E6970Receipt34_chunk133, pack_E6970Receipt34_chunk134, pack_E6970Receipt34_chunk135, pack_E6970Receipt34_chunk136, pack_E6970Receipt34_chunk137, pack_E6970Receipt34_chunk138, pack_E6970Receipt34_chunk139, pack_E6970Receipt34_chunk140, pack_E6970Receipt34_chunk141, pack_E6970Receipt34_chunk142, pack_E6970Receipt34_chunk143, pack_E6970Receipt34_chunk144, pack_E6970Receipt34_chunk145, pack_E6970Receipt34_chunk146, pack_E6970Receipt34_chunk147, pack_E6970Receipt34_chunk148, pack_E6970Receipt34_chunk149, pack_E6970Receipt34_chunk150, pack_E6970Receipt34_chunk151, pack_E6970Receipt34_chunk152, pack_E6970Receipt34_chunk153, pack_E6970Receipt34_chunk154, pack_E6970Receipt34_chunk155, pack_E6970Receipt34_chunk156, pack_E6970Receipt34_chunk157, pack_E6970Receipt34_chunk158, pack_E6970Receipt34_chunk159, pack_E6970Receipt34_chunk160, pack_E6970Receipt34_chunk161, pack_E6970Receipt34_chunk162, pack_E6970Receipt34_chunk163, pack_E6970Receipt34_chunk164, pack_E6970Receipt34_chunk165, pack_E6970Receipt34_chunk166, pack_E6970Receipt34_chunk167, pack_E6970Receipt34_chunk168, pack_E6970Receipt34_chunk169, pack_E6970Receipt34_chunk170, pack_E6970Receipt34_chunk171, pack_E6970Receipt34_chunk172, pack_E6970Receipt34_chunk173, pack_E6970Receipt34_chunk174, pack_E6970Receipt34_chunk175, pack_E6970Receipt34_chunk176, pack_E6970Receipt34_chunk177, pack_E6970Receipt34_chunk178, pack_E6970Receipt34_chunk179, pack_E6970Receipt34_chunk180, pack_E6970Receipt34_chunk181, pack_E6970Receipt34_chunk182, pack_E6970Receipt34_chunk183, pack_E6970Receipt34_chunk184, pack_E6970Receipt34_chunk185, pack_E6970Receipt34_chunk186, pack_E6970Receipt34_chunk187, pack_E6970Receipt34_chunk188, pack_E6970Receipt34_chunk189, pack_E6970Receipt34_chunk190, pack_E6970Receipt34_chunk191, pack_E6970Receipt34_chunk192, pack_E6970Receipt34_chunk193, pack_E6970Receipt34_chunk194, pack_E6970Receipt34_chunk195, pack_E6970Receipt34_chunk196, pack_E6970Receipt34_chunk197, pack_E6970Receipt34_chunk198]
def rows34 := rowsFrom pack_E6970Receipt34_chunks
theorem good34 : ∀ r ∈ rows34, good 34 r = true := rowsFrom_good pack_E6970Receipt34_chunks
theorem sorted34 : rows34.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt34_chunks 0 (by decide +kernel)).1
theorem mass34 (i : Fin 61) :
    bandCount 34 (i.val : ℤ) 60 16 ≤ (rows34.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt34_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 34 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt34_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total34 : (rows34.map (price 34)).sum = 388652 :=
  (total_eq pack_E6970Receipt34_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt34

section Pack_E6970Receipt35

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt35_chunk0 := witnessA6966Final 35 60 0 450025 450278 32 3337
  0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk1 := witnessA6966Final 35 60 32 450279 450524 32 3305
  0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk2 := witnessA6966Final 35 60 64 450525 450711 32 3275
  0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk3 := witnessA6966Final 35 60 96 450712 450898 32 3235
  0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk4 := witnessA6966Final 35 60 128 450899 451030 22 2153
  0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk5 := witnessRule 35 59 0 460024 460275 32 3258
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk6 := witnessRule 35 59 32 460276 460467 32 3204
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk7 := witnessRule 35 59 64 460520 460654 32 3186
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk8 := witnessRule 35 59 96 460706 460839 32 3161
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk9 := witnessRule 35 59 128 460840 461029 26 2471
  0x3ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk10 := witnessRule 35 58 0 470023 470272 32 3196
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk11 := witnessRule 35 58 32 470273 470462 32 3142
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk12 := witnessRule 35 58 64 470463 470648 32 3117
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk13 := witnessRule 35 58 96 470649 470833 32 3056
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk14 := witnessRule 35 58 128 470834 471029 30 2774
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk15 := witnessRule 35 57 0 480022 480216 32 3131
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk16 := witnessRule 35 57 32 480270 480458 32 3105
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk17 := witnessRule 35 57 64 480459 480642 32 3036
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk18 := witnessRule 35 57 96 480643 480775 32 2997
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk19 := witnessRule 35 57 128 480776 481027 32 2880
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk20 := witnessRule 35 57 160 481028 481028 1 89
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk21 := witnessRule 35 56 0 490021 490213 32 3100
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk22 := witnessRule 35 56 32 490214 490402 32 3029
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk23 := witnessRule 35 56 64 490403 490586 32 3007
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk24 := witnessRule 35 56 96 490587 490770 32 2927
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk25 := witnessRule 35 56 128 490771 491024 32 2806
  0xffdfffff 0xb99a (by decide +kernel)
private def pack_E6970Receipt35_chunk26 := witnessRule 35 56 160 491025 491028 4 348
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk27 := witnessRule 35 55 0 500020 500211 32 3072
  0xfefebfdf 0x263346c2a8590d299 (by decide +kernel)
private def pack_E6970Receipt35_chunk28 := witnessRule 35 55 32 500212 500398 32 2998
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk29 := witnessRule 35 55 64 500399 500581 32 2965
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk30 := witnessRule 35 55 96 500582 500713 32 2854
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk31 := witnessRule 35 55 128 500714 500963 32 2740
  0xfefdffff 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt35_chunk32 := witnessRule 35 55 160 500964 501027 6 511
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk33 := witnessRule 35 54 0 510019 510208 32 3044
  0xfbfffeff 0x98548d9b0a883 (by decide +kernel)
private def pack_E6970Receipt35_chunk34 := witnessRule 35 54 32 510209 510394 32 2968
  0xfabeaff5 0x363342e2c86cdc504da30aa264342ea68594d1b8a883 (by decide +kernel)
private def pack_E6970Receipt35_chunk35 := witnessRule 35 54 64 510395 510526 32 2881
  0xf9ff5feb 0xdccd238a227163368e2885c98cd93a1a (by decide +kernel)
private def pack_E6970Receipt35_chunk36 := witnessRule 35 54 96 510527 510708 32 2841
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk37 := witnessRule 35 54 128 510709 510960 32 2670
  0xfbe7edff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt35_chunk38 := witnessRule 35 54 160 510961 511027 8 666
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk39 := witnessRule 35 53 0 520018 520206 32 3012
  0xe3f8fe3f 0x1b0a8988426153362e2c2a46214d895130a9188416154364c4a26c5c98958aa9a (by decide +kernel)
private def pack_E6970Receipt35_chunk40 := witnessRule 35 53 32 520207 520390 32 2906
  0xdffdff5f 0x36152362e6c2a2111854418b930a89885 (by decide +kernel)
private def pack_E6970Receipt35_chunk41 := witnessRule 35 53 64 520391 520521 32 2895
  0x7f55feff 0x9d4d2b0aa364342e2ca6d1c54419329a (by decide +kernel)
private def pack_E6970Receipt35_chunk42 := witnessRule 35 53 96 520522 520704 32 2772
  0xfaff57f5 0x4e4c66cdd0d0b9b19b27164368e2826d18cd0b9321b (by decide +kernel)
private def pack_E6970Receipt35_chunk43 := witnessRule 35 53 128 520705 520900 32 2611
  0xef9f2fb7 0x176342e2ca6c9c590d8b9321b27263366e8685cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt35_chunk44 := witnessRule 35 53 160 520901 521026 9 735
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk45 := witnessRule 35 52 0 530017 530203 32 2956
  0x8bf5fcff 0x462544c4a46c5c98944e139291b36251362e2c4a470d89441931291b (by decide +kernel)
private def pack_E6970Receipt35_chunk46 := witnessRule 35 52 32 530204 530336 32 2890
  0x3fc1fc3f 0x2e4c2a462145c58550e2312a3615231084c2a86c9c98958b8aa9b36251362e6c4ac58554d938b1289c (by decide +kernel)
private def pack_E6970Receipt35_chunk47 := witnessRule 35 52 64 530337 530516 32 2879
  0xfaffa3fc 0x1746151084e4c2a262155854418b9b0a898851726153384e2c2a4621518544c421b0a99b (by decide +kernel)
private def pack_E6970Receipt35_chunk48 := witnessRule 35 52 96 530517 530648 32 2704
  0x3feffebf 0xb9b1988417265366ca6918548d939b0a884 (by decide +kernel)
private def pack_E6970Receipt35_chunk49 := witnessRule 35 52 128 530649 530898 32 2551
  0xde7c3c1e 0xbb9a17166364e2ca6c5c994d939321b3716331086ea685cd90d93931988427165366e8620d1c508da321a (by decide +kernel)
private def pack_E6970Receipt35_chunk50 := witnessRule 35 52 160 530899 531026 10 802
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk51 := witnessRule 35 51 0 540016 540150 32 2908
  0x1fe3fc7f 0x1b128988426253362e2c4a46214d8d513129188416254364c6a26c5c98d592a9a (by decide +kernel)
private def pack_E6970Receipt35_chunk52 := witnessRule 35 51 32 540202 540333 32 2892
  0xff1ff1ff 0x118944d8b9b128841726252388c4a20cd8948d8b931289885 (by decide +kernel)
private def pack_E6970Receipt35_chunk53 := witnessRule 35 51 64 540334 540463 32 2767
  0x1fc2fe2 0x562548c2a46210d8550d939b12b1716155386e2c4a2711c9441a31289b17462564c2aa6c9c98944e1b9291b562546c4a46c5cd8944e138b1291c (by decide +kernel)
private def pack_E6970Receipt35_chunk54 := witnessRule 35 51 96 540512 540644 32 2720
  0x3a07c07f 0x3715436ae2a22d9854418ba30a898851736153384e4c2a462149c58550e238b12b471514138ac2a262111854cd8b9b0a918851726154386e4c4ac9c554da39289b (by decide +kernel)
private def pack_E6970Receipt35_chunk55 := witnessRule 35 51 128 540645 540896 32 2492
  0xfde0c0e8 0x17167362e6c862105c998d938b29884277348e6622d190c419b31a1726531082e2ce6cdc5854ce238a9188446153364e6c2a262149c9854ce1b8b0a91885 (by decide +kernel)
private def pack_E6970Receipt35_chunk56 := witnessRule 35 51 160 540897 541025 10 785
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk57 := witnessRule 35 50 0 550015 550148 32 2887
  0x5fd7f9ff 0x5c98d44e139a91b36351362e2c6a470d8d441931a91b (by decide +kernel)
private def pack_E6970Receipt35_chunk58 := witnessRule 35 50 32 550149 550329 32 2858
  0xf83fc3fc 0x8c6a8d8948c421312a1b27263562e4aa6cd8d44d8b9b1ab16255364e2c6a27118d5131a91b (by decide +kernel)
private def pack_E6970Receipt35_chunk59 := witnessRule 35 50 64 550330 550458 32 2756
  0xffc1ff0f 0x2b1288346252362e6c4a262145c9894ce138b12918854625131086c4a66c5c98948c428b8b12a1c (by decide +kernel)
private def pack_E6970Receipt35_chunk60 := witnessRule 35 50 96 550459 550641 32 2622
  0xc2fc1ff0 0x158944da30a9988436155364e6c4a270dc58948e3312a46252362e8c4a2709cd8944213931291c56251362e8c4a2105cd8948e13931289885 (by decide +kernel)
private def pack_E6970Receipt35_chunk61 := witnessRule 35 50 128 550642 550837 32 2438
  0xff930f09 0xd98c419341a17934304ea6cd8554d8b9b0aa1c2726153310a4e2c2aa7158548c42230aa1b1736153310a2e4c2aa709c558da39291b (by decide +kernel)
private def pack_E6970Receipt35_chunk62 := witnessRule 35 50 160 550896 551025 10 772
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk63 := witnessRule 35 49 0 560014 560146 32 2866
  0xff8ff8ff 0xd915131a9188416354364c8a26c5c99159aa9a (by decide +kernel)
private def pack_E6970Receipt35_chunk64 := witnessRule 35 49 32 560147 560326 32 2807
  0xe3ff1ff8 0x231a89b1736351082e4c6a47118d4419b1a91b1726351310a6c6a2621098d4cd8b8b1a91885 (by decide +kernel)
private def pack_E6970Receipt35_chunk65 := witnessRule 35 49 64 560327 560454 32 2759
  0xfe17f8bf 0x231a89b17463564c4aa6c9c98d44e1b9a91b563546c6a46c5cd8d44e138b1a91c (by decide +kernel)
private def pack_E6970Receipt35_chunk66 := witnessRule 35 49 96 560455 560586 32 2529
  0x7e07f03 0x2b1291b1746251310a2e6c4a6709c98948c42938b12a1c5625131088c4a66c5cd8948c428b9312a1c37263564e4aa6d58d523129188436254364e6c6ac5c58954e1b8b1a89c (by decide +kernel)
private def pack_E6970Receipt35_chunk67 := witnessRule 35 49 128 560587 560836 32 2391
  0xff6c3c2e 0x2615736302ee6d18550c421b0ab1b1726155310a2e2c2ae711894cd9b0aa988426157364e4c4a670dc950dab12903 (by decide +kernel)
private def pack_E6970Receipt35_chunk68 := witnessRule 35 49 160 560837 561024 9 683
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk69 := witnessRule 35 48 0 570013 570144 32 2850
  0xff5ff3ff 0x36451362e2c8a470d91441932291b (by decide +kernel)
private def pack_E6970Receipt35_chunk70 := witnessRule 35 48 32 570145 570274 32 2699
  0x7fc3fe2 0x2322a3635231084c6a86c9c99158b9aa9b36451362e6c8ac58d54d938b2289c464544c8a46c5c99144e13a291b (by decide +kernel)
private def pack_E6970Receipt35_chunk71 := witnessRule 35 48 64 570323 570450 32 2753
  0xe0ffc3ff 0x2b1a88346352362e6c6a262145c98d4ce138b1a918854635131086c6a66c5c98d48c428b8b1aa1c (by decide +kernel)
private def pack_E6970Receipt35_chunk72 := witnessRule 35 48 96 570451 570583 32 2494
  0x1f07f87f 0x1726254310a2e2c4ac70dc58d48e2b1a88346352362e8c6a2709cd8d44213931a91c56351362e8c6a2105cd8d48e13931a89885 (by decide +kernel)
private def pack_E6970Receipt35_chunk73 := witnessRule 35 48 128 570584 570835 32 2332
  0xfff87078 0x36255364c2ae621058564d8c0b8b0aa9d4625232088c4a86c5cd894cc428b9312a9c2716254310aac4a264111894cc421b12a9b (by decide +kernel)
private def pack_E6970Receipt35_chunk74 := witnessRule 35 48 160 570836 571024 8 597
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk75 := witnessRule 35 47 0 580012 580142 32 2830
  0xfe3ff1ff 0xd95513229188416454364caa26c5c9955a2a9a (by decide +kernel)
private def pack_E6970Receipt35_chunk76 := witnessRule 35 47 32 580143 580271 32 2680
  0x7ff1ffc7 0x2e4c8a4711914419b2291b1726451310a6c8a262109914cd8b8b2291885 (by decide +kernel)
private def pack_E6970Receipt35_chunk77 := witnessRule 35 47 64 580272 580398 32 2650
  0xbfe2ffc 0x8c8a26c5d1915931aa9b2726451386e8a46d59151b2291b1736451384e2c8a47119144d8b9b22884 (by decide +kernel)
private def pack_E6970Receipt35_chunk78 := witnessRule 35 47 96 580448 580581 32 2476
  0x3c2fc0ff 0x138b1aa1c373533108ac6a2621118d4cd8b9b1a918851726354384e6aa6d5915231a9188436354364e6c8ac5c58d54e1b8b2289c (by decide +kernel)
private def pack_E6970Receipt35_chunk79 := witnessRule 35 47 128 580582 580835 32 2278
  0xfff060f0 0xd8950c821312b18841826155310a302c2ae70605c558c42a312999043625531084c4ae6c5c58958c428b92c1b4635231086c6a86c5cd8d4ce13931a91885 (by decide +kernel)
private def pack_E6970Receipt35_chunk80 := witnessRule 35 47 160 580836 580961 6 440
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk81 := witnessRule 35 46 0 590011 590140 32 2806
  0xfd7fe7ff 0x36551362e2caa470d95441932a91b (by decide +kernel)
private def pack_E6970Receipt35_chunk82 := witnessRule 35 46 32 590141 590268 32 2667
  0xffc3ff17 0x36551362e6caac59154d938b2a89c465544caa46c5c99544e13aa91b (by decide +kernel)
private def pack_E6970Receipt35_chunk83 := witnessRule 35 46 64 590269 590395 32 2594
  0x3ff0ffe0 0x2e4c8a6709c59148c42a3228988436453362e4c8a462145c59150e232aa3645231084c8a86c9c99558ba2a9b (by decide +kernel)
private def pack_E6970Receipt35_chunk84 := witnessRule 35 46 96 590396 590579 32 2384
  0x705f0ff8 0xdcd450ce2b1a98346452366c6a8621098d58d93932291c3745336ac8a26c5d1914420b9b2291c2726451310aac8a20d19148d8b9b2289885 (by decide +kernel)
private def pack_E6970Receipt35_chunk85 := witnessRule 35 46 128 590580 590835 32 2228
  0xfff560c1 0x1312a99841816156320a5028c6cd8d50c42131ab1b182625538302e2c4a86218605c958e231a899844635331086c6aa6c5c98d50c428b8b1ab1c (by decide +kernel)
private def pack_E6970Receipt35_chunk86 := witnessRule 35 46 160 590896 590960 4 289
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk87 := witnessRule 35 45 0 600010 600138 32 2774
  0xf8ffe3ff 0xd995132a9188416554364cca26c5c9995aaa9a (by decide +kernel)
private def pack_E6970Receipt35_chunk88 := witnessRule 35 45 32 600139 600265 32 2660
  0xff1ffe3f 0x11954419b2a91b1726551310a6caa262109954cd8b8b2a91885 (by decide +kernel)
private def pack_E6970Receipt35_chunk89 := witnessRule 35 45 64 600266 600392 32 2542
  0x7f8bff8f 0x3755236acaa8d9548d8b9b2a89c2716552388caa26c5cd954420b932a91c (by decide +kernel)
private def pack_E6970Receipt35_chunk90 := witnessRule 35 45 96 600393 600578 32 2299
  0xe0fc4fe1 0x119144c82232299b1736452310a2e4c8a8709c5914cc42ab229034645231086c8a86c5c59154e1b8b2a89c46551362e8caac99154d93932a89c (by decide +kernel)
private def pack_E6970Receipt35_chunk91 := witnessRule 35 45 128 600579 600896 32 2185
  0xffffc1c0 0x6c6a6661098d54c820c1312a19051816256310a304b06d18d48cc21b22a1b2635631082c6b06c605c58d50e8c139a99885 (by decide +kernel)
private def pack_E6970Receipt35_chunk92 := witnessRule 35 45 160 600897 600960 2 143
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk93 := witnessRule 35 44 0 610009 610136 32 2738
  0xf5ffcfff 0x36651362e2cca470d99441933291b (by decide +kernel)
private def pack_E6970Receipt35_chunk94 := witnessRule 35 44 32 610137 610262 32 2638
  0xfc3ff8bf 0x36651362e6ccac59554d938b3289c466544cca46c5c99944e13b291b (by decide +kernel)
private def pack_E6970Receipt35_chunk95 := witnessRule 35 44 64 610263 610390 32 2476
  0xfe1ffc1f 0x232a8988436553362e4caa462145c59550e2332a3655231084caa86c9c99958baaa9b (by decide +kernel)
private def pack_E6970Receipt35_chunk96 := witnessRule 35 44 96 610391 610577 32 2217
  0xe2783f83 0x8c8a46410d9150c421322b1b1745736304e8a67119544c421b2a99b1736552384e4caa262149c5954ce2b2a88346552362e6caa262145c9954ce138b2a91885 (by decide +kernel)
private def pack_E6970Receipt35_chunk97 := witnessRule 35 44 128 610578 610897 31 2079
  0x7fffe0c0 0x4c6a86810609894cd028c0b12a9985182573208502a28a6214d914cc821322a98841826354310a302c6ac70605cd54c428c13928a1988e (by decide +kernel)
private def pack_E6970Receipt35_chunk98 := witnessRule 35 43 0 620008 620134 32 2694
  0xe3ffc7ff 0xd9d513329188416654364cea26c5c99d5b2a9a (by decide +kernel)
private def pack_E6970Receipt35_chunk99 := witnessRule 35 43 32 620135 620259 32 2604
  0xf1fff1ff 0x11994419b3291b1726651310a6cca262109994cd8b8b3291885 (by decide +kernel)
private def pack_E6970Receipt35_chunk100 := witnessRule 35 43 64 620260 620388 32 2428
  0xf8bff1ff 0xacca8d9948d8b9b3289c2716652388cca26c5cd994420b933291c (by decide +kernel)
private def pack_E6970Receipt35_chunk101 := witnessRule 35 43 96 620389 620577 32 2147
  0xe0f85f0b 0x6caa6621099554d8c1322a1c181716453310c302e8aa7119548c421b2aa1b1726553310a2e2caaa70dd54508e233289b3655331084caaa6c9c99944e1bb291b (by decide +kernel)
private def pack_E6970Receipt35_chunk102 := witnessRule 35 43 128 620578 620896 28 1841
  0xfffeae0 0x263533608302c4a86a14a054510cc29322a19841826353330a302c6aa641460d5cc4214128a29c (by decide +kernel)
private def pack_E6970Receipt35_chunk103 := witnessRule 35 42 0 630007 630132 32 2646
  0xd7ff9fff 0x36751362e2cea470d9d441933a91b (by decide +kernel)
private def pack_E6970Receipt35_chunk104 := witnessRule 35 42 32 630133 630257 32 2546
  0xc3ffc5ff 0x36751362e6ceac59954d938b3a89c467544cea46c5c99d44e13ba91b (by decide +kernel)
private def pack_E6970Receipt35_chunk105 := witnessRule 35 42 64 630258 630387 32 2376
  0xf0ffc1ff 0x23328988436653362e4cca462145c59950e233aa3665231084cca86c9c99d58bb2a9b (by decide +kernel)
private def pack_E6970Receipt35_chunk106 := witnessRule 35 42 96 630388 630577 32 2079
  0x70707e0f 0x281715143321c4caa86410609914cc828c0b22a98851845736502e6a6623519544cc21b3299b2655531082caae6c605c5954cea33290346652362e6cca262145c9994ce138b3291885 (by decide +kernel)
private def pack_E6970Receipt35_chunk107 := witnessRule 35 42 128 630578 630896 25 1617
  0x1ffffe8 0x264533508302c6a8681460d58cc214128a21905 (by decide +kernel)
private def pack_E6970Receipt35_chunk108 := witnessRule 35 41 0 640006 640130 32 2590
  0x8fff8fff 0xda15133a9188416754364d0a26c5c9a15baa9a (by decide +kernel)
private def pack_E6970Receipt35_chunk109 := witnessRule 35 41 32 640131 640208 32 2492
  0x1fff8fff 0x119d4419b3a91b1726751310a6cea2621099d4cd8b8b3a91885 (by decide +kernel)
private def pack_E6970Receipt35_chunk110 := witnessRule 35 41 64 640256 640386 32 2333
  0xe2ff8fff 0x8cea20cd9d48d8b9b3a89c2716752388cea26c5cd9d4420b933a91c (by decide +kernel)
private def pack_E6970Receipt35_chunk111 := witnessRule 35 41 96 640387 640578 32 2020
  0x34781e2f 0x2825143340a702a66422149954cd020c0b22a1985184563208506a2886214d9948c821332a18841826553310a302caaa70605d550c428c13a28a1188e4665132086cca6621099954d8bb2b1b (by decide +kernel)
private def pack_E6970Receipt35_chunk112 := witnessRule 35 41 128 640579 640833 21 1335
  0x1ffffd 0xc0b1a99b05 (by decide +kernel)
private def pack_E6970Receipt35_chunk113 := witnessRule 35 40 0 650005 650082 32 2530
  0x5fff3fff 0x36851362e2d0a470da1441934291b (by decide +kernel)
private def pack_E6970Receipt35_chunk114 := witnessRule 35 40 32 650129 650206 32 2474
  0x1ffe2fff 0x2e6d0ac59d54d938b4289c468544d0a46c5c9a144e13c291b (by decide +kernel)
private def pack_E6970Receipt35_chunk115 := witnessRule 35 40 64 650207 650386 32 2229
  0xe1ff07fe 0x119d44c421b3a99b1726752310a2e2cea8711a151b3a9188426754364e4d0ac5dd54d9b4289b (by decide +kernel)
private def pack_E6970Receipt35_chunk116 := witnessRule 35 40 96 650387 650579 32 1956
  0xae9d1f17 0x14128a11b05381433318302c8a66a14a0d450ccc29c129990c266533308302caa8641461558c4214228a21c3675231084cea86c609994ce0c0bb2a1c (by decide +kernel)
private def pack_E6970Receipt35_chunk117 := witnessRule 35 40 128 650580 650832 17 1064
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk118 := witnessRule 35 39 0 660004 660081 32 2515
  0x3fff1fff 0x13429188416854364d2a26c5c9a55c2a9a (by decide +kernel)
private def pack_E6970Receipt35_chunk119 := witnessRule 35 39 32 660082 660205 32 2415
  0x7ffc7ffe 0xb9342898853685131084d0a66c5c5a148c429b4aa (by decide +kernel)
private def pack_E6970Receipt35_chunk120 := witnessRule 35 39 64 660206 660386 32 2128
  0xf0ff1ffc 0x1b4291b2675431082ceac6c605c59d48ea34289b1736851082e4d0a4711a14419b4291b (by decide +kernel)
private def pack_E6970Receipt35_chunk121 := witnessRule 35 39 96 660387 660581 32 1907
  0xffdfa7a7 0x506a2846a14605954cd0294228a19905281735142321c4cea664106059950c428c32b1b (by decide +kernel)
private def pack_E6970Receipt35_chunk122 := witnessRule 35 39 128 660582 660832 13 803
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk123 := witnessRule 35 38 0 670003 670079 32 2503
  0x7ffe7fff 0x2e2d2a470da5441934a91b (by decide +kernel)
private def pack_E6970Receipt35_chunk124 := witnessRule 35 38 32 670080 670204 32 2305
  0x3ff8bffd 0x2d0aa6c9c5a544e234aa26952362e4d2a2709e548d9b4a89b (by decide +kernel)
private def pack_E6970Receipt35_chunk125 := witnessRule 35 38 64 670205 670387 32 2038
  0xf07f17fc 0x6d0a264109a14cc420c133a91885181675438302eea662151a14819b429188426854362f0aa6cda544d8b9b4ab (by decide +kernel)
private def pack_E6970Receipt35_chunk126 := witnessRule 35 38 96 670388 670641 32 1862
  0xfffdf7d5 0x1c0a8a11988862845142340a4cea46810605994ccc2942a8a19885 (by decide +kernel)
private def pack_E6970Receipt35_chunk127 := witnessRule 35 38 128 670642 670769 8 487
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk128 := witnessRule 35 37 0 680002 680078 32 2491
  0xfffe3fff 0x4d4a26c5c9a95caa9a (by decide +kernel)
private def pack_E6970Receipt35_chunk129 := witnessRule 35 37 32 680079 680204 32 2199
  0x7ff8fff8 0x2e4d2a26214da544c42134a99b1716952310a6d4a89a548c420b4aa1b (by decide +kernel)
private def pack_E6970Receipt35_chunk130 := witnessRule 35 37 64 680205 680388 32 1948
  0xfd5f8bfc 0x1342919841816753320a50ca28670da544c42134a99b182685238302f0a6711a54419b4a91b (by decide +kernel)
private def pack_E6970Receipt35_chunk131 := witnessRule 35 37 96 680389 680704 32 1831
  0xffffff7e 0xe094508cc6942a8a11985 (by decide +kernel)
private def pack_E6970Receipt35_chunk132 := witnessRule 35 37 128 680705 680768 3 181
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk133 := witnessRule 35 36 0 690001 690077 32 2429
  0xfffcffff 0xda9441935291b (by decide +kernel)
private def pack_E6970Receipt35_chunk134 := witnessRule 35 36 32 690078 690204 32 2092
  0x9ff8bffa 0x1695536302e2d2a2751a95135291b1726a51384f4a46cda944d8b8b5291c (by decide +kernel)
private def pack_E6970Receipt35_chunk135 := witnessRule 35 36 64 690205 690390 32 1871
  0xffeffbfe 0x50ca2846414605a14cc429b5289b (by decide +kernel)
private def pack_E6970Receipt35_chunk136 := witnessRule 35 36 96 690391 690768 30 1694
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk137 := witnessRule 35 35 0 700000 700077 32 2367
  0xfffc7fff 0x4d6a26c5c9ad5d2a9a (by decide +kernel)
private def pack_E6970Receipt35_chunk138 := witnessRule 35 35 32 700078 700205 32 1990
  0x8ffc7ff8 0x1352918841826951310a302d2a670da944c42135299b1716a52310a6d6a89a948c420b52a1b (by decide +kernel)
private def pack_E6970Receipt35_chunk139 := witnessRule 35 35 64 700256 700392 32 1804
  0xffdff57f 0x1685236084d2a26810605a148cc2943a8a11885 (by decide +kernel)
private def pack_E6970Receipt35_chunk140 := witnessRule 35 35 96 700448 700705 24 1331
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk141 := witnessRule 35 34 0 710000 710077 32 2251
  0x7ffcffff 0x2e2d6a470dad441935a91b (by decide +kernel)
private def pack_E6970Receipt35_chunk142 := witnessRule 35 34 32 710078 710257 32 1933
  0xf5fe2ffd 0x302d2a46414a214508e1b5a88326b5236304d4a270605e948e1b5a89b (by decide +kernel)
private def pack_E6970Receipt35_chunk143 := witnessRule 35 34 64 710258 710450 32 1707
  0xfffffeff 0xb4a91a84 (by decide +kernel)
private def pack_E6970Receipt35_chunk144 := witnessRule 35 34 96 710451 710704 18 981
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk145 := witnessRule 35 33 0 720000 720078 32 2135
  0x3ffe3fff 0x135a9188416b54364d8a26c5c9b15daa9a (by decide +kernel)
private def pack_E6970Receipt35_chunk146 := witnessRule 35 33 32 720079 720259 32 1861
  0xfffffffe 0x1b62a (by decide +kernel)
private def pack_E6970Receipt35_chunk147 := witnessRule 35 33 64 720260 720454 32 1647
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk148 := witnessRule 35 33 96 720512 720704 12 647
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk149 := witnessRule 35 32 0 730000 730078 32 2023
  0x5ffe7fff 0x26c513108302d6a470db1441936291b (by decide +kernel)
private def pack_E6970Receipt35_chunk150 := witnessRule 35 32 32 730128 730261 32 1778
  0xfd7fe5ff 0xb5289b041895235082d6a46610605a944cc2944a8a09885 (by decide +kernel)
private def pack_E6970Receipt35_chunk151 := witnessRule 35 32 64 730262 730515 32 1612
  0xfffffff7 0x4a91c03 (by decide +kernel)
private def pack_E6970Receipt35_chunk152 := witnessRule 35 32 96 730516 730641 6 319
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk153 := witnessRule 35 31 0 740000 740128 32 1947
  0xdbff1fff 0xb629190428a5141384daa26c609b15e2a9a (by decide +kernel)
private def pack_E6970Receipt35_chunk154 := witnessRule 35 31 32 740129 740263 32 1666
  0xffbffdff 0x2948dc18c5291a04 (by decide +kernel)
private def pack_E6970Receipt35_chunk155 := witnessRule 35 31 64 740264 740640 32 1591
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk156 := witnessRule 35 30 0 750000 750129 32 1869
  0xfffff7ff 0xc0bda924 (by decide +kernel)
private def pack_E6970Receipt35_chunk157 := witnessRule 35 30 32 750130 750265 32 1572
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk158 := witnessRule 35 30 64 750320 750640 27 1316
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk159 := witnessRule 35 29 0 760000 760130 32 1788
  0xf2ffa7ff 0x3148d418c5a89a842895241110a2daa2661063148c82145a8a084 (by decide +kernel)
private def pack_E6970Receipt35_chunk160 := witnessRule 35 29 32 760131 760322 32 1499
  0xfffbfebf 0x12a2827412d44e018c4a92304 (by decide +kernel)
private def pack_E6970Receipt35_chunk161 := witnessRule 35 29 64 760323 760577 21 999
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk162 := witnessRule 35 28 0 770000 770131 32 1700
  0xfdffdbff 0x314a48a13548d0194529208c (by decide +kernel)
private def pack_E6970Receipt35_chunk163 := witnessRule 35 28 32 770132 770324 32 1435
  0xffffffbf 0x528a09c84 (by decide +kernel)
private def pack_E6970Receipt35_chunk164 := witnessRule 35 28 64 770325 770576 16 747
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk165 := witnessRule 35 27 0 780000 780132 32 1612
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk166 := witnessRule 35 27 32 780133 780384 32 1391
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk167 := witnessRule 35 27 64 780385 780576 11 506
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk168 := witnessRule 35 26 0 790000 790133 32 1522
  0xfd7fe5ff 0x5a8a5031895241260b8a2826e1062d4504542944a920908886 (by decide +kernel)
private def pack_E6970Receipt35_chunk169 := witnessRule 35 26 32 790134 790387 32 1356
  0xfffffff7 0x4a9208d04 (by decide +kernel)
private def pack_E6970Receipt35_chunk170 := witnessRule 35 26 64 790388 790513 6 271
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk171 := witnessRule 35 25 0 800000 800134 32 1438
  0xff7ffbff 0x2949046420c529209285 (by decide +kernel)
private def pack_E6970Receipt35_chunk172 := witnessRule 35 25 32 800135 800450 32 1329
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk173 := witnessRule 35 25 64 800512 800512 1 45
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk174 := witnessRule 35 24 0 810000 810135 32 1362
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk175 := witnessRule 35 24 32 810136 810512 29 1176
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk176 := witnessRule 35 23 0 820000 820136 32 1292
  0xffdff5ff 0x12a482423416d4504a820c4a9211305 (by decide +kernel)
private def pack_E6970Receipt35_chunk177 := witnessRule 35 23 32 820192 820449 24 947
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk178 := witnessRule 35 22 0 830000 830192 32 1227
  0xfffffbff 0x52920908c85 (by decide +kernel)
private def pack_E6970Receipt35_chunk179 := witnessRule 35 22 32 830193 830448 20 767
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk180 := witnessRule 35 21 0 840000 840194 32 1172
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk181 := witnessRule 35 21 32 840195 840448 16 599
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk182 := witnessRule 35 20 0 850000 850195 32 1119
  0xfffffdff 0x4a921108d05 (by decide +kernel)
private def pack_E6970Receipt35_chunk183 := witnessRule 35 20 32 850196 850385 12 437
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk184 := witnessRule 35 19 0 860000 860197 32 1072
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk185 := witnessRule 35 19 32 860256 860384 8 285
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk186 := witnessRule 35 18 0 870000 870257 32 1032
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk187 := witnessRule 35 18 32 870258 870384 5 174
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk188 := witnessRule 35 17 0 880000 880320 32 997
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk189 := witnessRule 35 17 32 880321 880321 1 34
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk190 := witnessRule 35 16 0 890000 890320 30 897
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk191 := witnessRule 35 15 0 900000 900320 27 776
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk192 := witnessRule 35 14 0 910000 910257 24 659
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk193 := witnessRule 35 13 0 920000 920256 21 552
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk194 := witnessRule 35 12 0 930000 930256 19 479
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk195 := witnessRule 35 11 0 940000 940193 16 385
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk196 := witnessRule 35 10 0 950000 950192 14 321
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk197 := witnessRule 35 9 0 960000 960192 12 263
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk198 := witnessRule 35 8 0 970000 970129 10 207
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk199 := witnessRule 35 7 0 980000 980128 8 157
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk200 := witnessRule 35 6 0 990000 990128 7 130
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk201 := witnessRule 35 5 0 1000000 1000065 5 87
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk202 := witnessRule 35 4 0 1010000 1010064 4 65
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk203 := witnessRule 35 3 0 1020000 1020064 3 46
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk204 := witnessRule 35 2 0 1030000 1030001 2 28
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk205 := witnessRule 35 1 0 1040000 1040000 1 13
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt35_chunk206 := witnessRule 35 0 0 1050000 1050000 1 12
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt35_chunks : List (Chunk 35) := [pack_E6970Receipt35_chunk0, pack_E6970Receipt35_chunk1, pack_E6970Receipt35_chunk2, pack_E6970Receipt35_chunk3, pack_E6970Receipt35_chunk4, pack_E6970Receipt35_chunk5, pack_E6970Receipt35_chunk6, pack_E6970Receipt35_chunk7, pack_E6970Receipt35_chunk8, pack_E6970Receipt35_chunk9, pack_E6970Receipt35_chunk10, pack_E6970Receipt35_chunk11, pack_E6970Receipt35_chunk12, pack_E6970Receipt35_chunk13, pack_E6970Receipt35_chunk14, pack_E6970Receipt35_chunk15, pack_E6970Receipt35_chunk16, pack_E6970Receipt35_chunk17, pack_E6970Receipt35_chunk18, pack_E6970Receipt35_chunk19, pack_E6970Receipt35_chunk20, pack_E6970Receipt35_chunk21, pack_E6970Receipt35_chunk22, pack_E6970Receipt35_chunk23, pack_E6970Receipt35_chunk24, pack_E6970Receipt35_chunk25, pack_E6970Receipt35_chunk26, pack_E6970Receipt35_chunk27, pack_E6970Receipt35_chunk28, pack_E6970Receipt35_chunk29, pack_E6970Receipt35_chunk30, pack_E6970Receipt35_chunk31, pack_E6970Receipt35_chunk32, pack_E6970Receipt35_chunk33, pack_E6970Receipt35_chunk34, pack_E6970Receipt35_chunk35, pack_E6970Receipt35_chunk36, pack_E6970Receipt35_chunk37, pack_E6970Receipt35_chunk38, pack_E6970Receipt35_chunk39, pack_E6970Receipt35_chunk40, pack_E6970Receipt35_chunk41, pack_E6970Receipt35_chunk42, pack_E6970Receipt35_chunk43, pack_E6970Receipt35_chunk44, pack_E6970Receipt35_chunk45, pack_E6970Receipt35_chunk46, pack_E6970Receipt35_chunk47, pack_E6970Receipt35_chunk48, pack_E6970Receipt35_chunk49, pack_E6970Receipt35_chunk50, pack_E6970Receipt35_chunk51, pack_E6970Receipt35_chunk52, pack_E6970Receipt35_chunk53, pack_E6970Receipt35_chunk54, pack_E6970Receipt35_chunk55, pack_E6970Receipt35_chunk56, pack_E6970Receipt35_chunk57, pack_E6970Receipt35_chunk58, pack_E6970Receipt35_chunk59, pack_E6970Receipt35_chunk60, pack_E6970Receipt35_chunk61, pack_E6970Receipt35_chunk62, pack_E6970Receipt35_chunk63, pack_E6970Receipt35_chunk64, pack_E6970Receipt35_chunk65, pack_E6970Receipt35_chunk66, pack_E6970Receipt35_chunk67, pack_E6970Receipt35_chunk68, pack_E6970Receipt35_chunk69, pack_E6970Receipt35_chunk70, pack_E6970Receipt35_chunk71, pack_E6970Receipt35_chunk72, pack_E6970Receipt35_chunk73, pack_E6970Receipt35_chunk74, pack_E6970Receipt35_chunk75, pack_E6970Receipt35_chunk76, pack_E6970Receipt35_chunk77, pack_E6970Receipt35_chunk78, pack_E6970Receipt35_chunk79, pack_E6970Receipt35_chunk80, pack_E6970Receipt35_chunk81, pack_E6970Receipt35_chunk82, pack_E6970Receipt35_chunk83, pack_E6970Receipt35_chunk84, pack_E6970Receipt35_chunk85, pack_E6970Receipt35_chunk86, pack_E6970Receipt35_chunk87, pack_E6970Receipt35_chunk88, pack_E6970Receipt35_chunk89, pack_E6970Receipt35_chunk90, pack_E6970Receipt35_chunk91, pack_E6970Receipt35_chunk92, pack_E6970Receipt35_chunk93, pack_E6970Receipt35_chunk94, pack_E6970Receipt35_chunk95, pack_E6970Receipt35_chunk96, pack_E6970Receipt35_chunk97, pack_E6970Receipt35_chunk98, pack_E6970Receipt35_chunk99, pack_E6970Receipt35_chunk100, pack_E6970Receipt35_chunk101, pack_E6970Receipt35_chunk102, pack_E6970Receipt35_chunk103, pack_E6970Receipt35_chunk104, pack_E6970Receipt35_chunk105, pack_E6970Receipt35_chunk106, pack_E6970Receipt35_chunk107, pack_E6970Receipt35_chunk108, pack_E6970Receipt35_chunk109, pack_E6970Receipt35_chunk110, pack_E6970Receipt35_chunk111, pack_E6970Receipt35_chunk112, pack_E6970Receipt35_chunk113, pack_E6970Receipt35_chunk114, pack_E6970Receipt35_chunk115, pack_E6970Receipt35_chunk116, pack_E6970Receipt35_chunk117, pack_E6970Receipt35_chunk118, pack_E6970Receipt35_chunk119, pack_E6970Receipt35_chunk120, pack_E6970Receipt35_chunk121, pack_E6970Receipt35_chunk122, pack_E6970Receipt35_chunk123, pack_E6970Receipt35_chunk124, pack_E6970Receipt35_chunk125, pack_E6970Receipt35_chunk126, pack_E6970Receipt35_chunk127, pack_E6970Receipt35_chunk128, pack_E6970Receipt35_chunk129, pack_E6970Receipt35_chunk130, pack_E6970Receipt35_chunk131, pack_E6970Receipt35_chunk132, pack_E6970Receipt35_chunk133, pack_E6970Receipt35_chunk134, pack_E6970Receipt35_chunk135, pack_E6970Receipt35_chunk136, pack_E6970Receipt35_chunk137, pack_E6970Receipt35_chunk138, pack_E6970Receipt35_chunk139, pack_E6970Receipt35_chunk140, pack_E6970Receipt35_chunk141, pack_E6970Receipt35_chunk142, pack_E6970Receipt35_chunk143, pack_E6970Receipt35_chunk144, pack_E6970Receipt35_chunk145, pack_E6970Receipt35_chunk146, pack_E6970Receipt35_chunk147, pack_E6970Receipt35_chunk148, pack_E6970Receipt35_chunk149, pack_E6970Receipt35_chunk150, pack_E6970Receipt35_chunk151, pack_E6970Receipt35_chunk152, pack_E6970Receipt35_chunk153, pack_E6970Receipt35_chunk154, pack_E6970Receipt35_chunk155, pack_E6970Receipt35_chunk156, pack_E6970Receipt35_chunk157, pack_E6970Receipt35_chunk158, pack_E6970Receipt35_chunk159, pack_E6970Receipt35_chunk160, pack_E6970Receipt35_chunk161, pack_E6970Receipt35_chunk162, pack_E6970Receipt35_chunk163, pack_E6970Receipt35_chunk164, pack_E6970Receipt35_chunk165, pack_E6970Receipt35_chunk166, pack_E6970Receipt35_chunk167, pack_E6970Receipt35_chunk168, pack_E6970Receipt35_chunk169, pack_E6970Receipt35_chunk170, pack_E6970Receipt35_chunk171, pack_E6970Receipt35_chunk172, pack_E6970Receipt35_chunk173, pack_E6970Receipt35_chunk174, pack_E6970Receipt35_chunk175, pack_E6970Receipt35_chunk176, pack_E6970Receipt35_chunk177, pack_E6970Receipt35_chunk178, pack_E6970Receipt35_chunk179, pack_E6970Receipt35_chunk180, pack_E6970Receipt35_chunk181, pack_E6970Receipt35_chunk182, pack_E6970Receipt35_chunk183, pack_E6970Receipt35_chunk184, pack_E6970Receipt35_chunk185, pack_E6970Receipt35_chunk186, pack_E6970Receipt35_chunk187, pack_E6970Receipt35_chunk188, pack_E6970Receipt35_chunk189, pack_E6970Receipt35_chunk190, pack_E6970Receipt35_chunk191, pack_E6970Receipt35_chunk192, pack_E6970Receipt35_chunk193, pack_E6970Receipt35_chunk194, pack_E6970Receipt35_chunk195, pack_E6970Receipt35_chunk196, pack_E6970Receipt35_chunk197, pack_E6970Receipt35_chunk198, pack_E6970Receipt35_chunk199, pack_E6970Receipt35_chunk200, pack_E6970Receipt35_chunk201, pack_E6970Receipt35_chunk202, pack_E6970Receipt35_chunk203, pack_E6970Receipt35_chunk204, pack_E6970Receipt35_chunk205, pack_E6970Receipt35_chunk206]
def rows35 := rowsFrom pack_E6970Receipt35_chunks
theorem good35 : ∀ r ∈ rows35, good 35 r = true := rowsFrom_good pack_E6970Receipt35_chunks
theorem sorted35 : rows35.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt35_chunks 0 (by decide +kernel)).1
theorem mass35 (i : Fin 61) :
    bandCount 35 (i.val : ℤ) 60 16 ≤ (rows35.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt35_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 35 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt35_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total35 : (rows35.map (price 35)).sum = 396432 :=
  (total_eq pack_E6970Receipt35_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt35

section Pack_E6970Receipt36

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt36_chunk0 := witnessA6966Final 36 60 0 480024 480273 32 3325
  0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk1 := witnessA6966Final 36 60 32 480274 480463 32 3293
  0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk2 := witnessA6966Final 36 60 64 480464 480649 32 3269
  0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk3 := witnessA6966Final 36 60 96 480650 480832 32 3227
  0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk4 := witnessA6966Final 36 60 128 480833 481027 32 3150
  0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk5 := witnessRule 36 60 160 481028 481030 3 282
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk6 := witnessRule 36 59 0 490023 490217 32 3233
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk7 := witnessRule 36 59 32 490271 490459 32 3215
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk8 := witnessRule 36 59 64 490460 490643 32 3169
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk9 := witnessRule 36 59 96 490644 490775 32 3154
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk10 := witnessRule 36 59 128 490776 490967 32 3039
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk11 := witnessRule 36 59 160 491024 491029 6 561
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk12 := witnessRule 36 58 0 500022 500214 32 3170
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk13 := witnessRule 36 58 32 500215 500403 32 3124
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk14 := witnessRule 36 58 64 500404 500587 32 3111
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk15 := witnessRule 36 58 96 500588 500769 32 3064
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk16 := witnessRule 36 58 128 500770 500962 32 2962
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk17 := witnessRule 36 58 160 500963 501029 10 905
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk18 := witnessRule 36 57 0 510021 510212 32 3120
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk19 := witnessRule 36 57 32 510213 510399 32 3066
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk20 := witnessRule 36 57 64 510400 510582 32 3044
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk21 := witnessRule 36 57 96 510583 510713 32 2978
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk22 := witnessRule 36 57 128 510714 510903 32 2872
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk23 := witnessRule 36 57 160 510960 511028 12 1063
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk24 := witnessRule 36 56 0 520020 520209 32 3083
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk25 := witnessRule 36 56 32 520210 520395 32 3019
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk26 := witnessRule 36 56 64 520396 520527 32 2950
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk27 := witnessRule 36 56 96 520528 520707 32 2948
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk28 := witnessRule 36 56 128 520708 520899 32 2794
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk29 := witnessRule 36 56 160 520900 521028 15 1292
  0x7ffe 0xb99a (by decide +kernel)
private def pack_E6970Receipt36_chunk30 := witnessRule 36 55 0 530019 530207 32 3051
  0xffffff7f 0x1319a (by decide +kernel)
private def pack_E6970Receipt36_chunk31 := witnessRule 36 55 32 530208 530391 32 2954
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk32 := witnessRule 36 55 64 530392 530522 32 2940
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk33 := witnessRule 36 55 96 530523 530652 32 2850
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk34 := witnessRule 36 55 128 530704 530896 32 2734
  0xf7ffffff 0xb8b19b (by decide +kernel)
private def pack_E6970Receipt36_chunk35 := witnessRule 36 55 160 530897 531027 16 1345
  0xfffb 0xba1a (by decide +kernel)
private def pack_E6970Receipt36_chunk36 := witnessRule 36 54 0 540018 540204 32 2995
  0xabfd7eff 0x118551321a175342ca68dc5441930a91b (by decide +kernel)
private def pack_E6970Receipt36_chunk37 := witnessRule 36 54 32 540205 540337 32 2933
  0xd7fafeaf 0x4e2c66d1c510b9319b274346c6685c590d9b8a09b (by decide +kernel)
private def pack_E6970Receipt36_chunk38 := witnessRule 36 54 64 540338 540517 32 2920
  0xfffffe7f 0xdccd238a2 (by decide +kernel)
private def pack_E6970Receipt36_chunk39 := witnessRule 36 54 96 540518 540647 32 2801
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk40 := witnessRule 36 54 128 540648 540837 32 2655
  0x9fb7ffff 0x17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt36_chunk41 := witnessRule 36 54 160 540838 541027 18 1478
  0x3ffef 0xba9a (by decide +kernel)
private def pack_E6970Receipt36_chunk42 := witnessRule 36 53 0 550017 550151 32 2947
  0xbfebfc7f 0x5cd85442230a8831726151310a6c2a262109854cd8b8b0a91885 (by decide +kernel)
private def pack_E6970Receipt36_chunk43 := witnessRule 36 53 32 550203 550334 32 2926
  0xbfdffbff 0x8e2a20c994d1b0a91b (by decide +kernel)
private def pack_E6970Receipt36_chunk44 := witnessRule 36 53 64 550335 550464 32 2819
  0xeafeafea 0xb9b19b27164368e2826d18cd0b9321b27534ac2a8d90d0b8b29b (by decide +kernel)
private def pack_E6970Receipt36_chunk45 := witnessRule 36 53 96 550513 550643 32 2799
  0x7fd7fd7f 0x2b8a23716336ae2889c98cd9ba1a (by decide +kernel)
private def pack_E6970Receipt36_chunk46 := witnessRule 36 53 128 550644 550835 32 2586
  0x3e5f6ffe 0x17165364e2c86c5c990d939319b374342e6c66cdc58cda399a (by decide +kernel)
private def pack_E6970Receipt36_chunk47 := witnessRule 36 53 160 550836 551026 18 1445
  0x3ffdf 0xbb1a (by decide +kernel)
private def pack_E6970Receipt36_chunk48 := witnessRule 36 52 0 560016 560149 32 2920
  0x1fc3f8bf 0x4c2a86c9c98958b8aa9b36251362e6c4ac58554d938b1289c462544c4a46c5c98944e139291b (by decide +kernel)
private def pack_E6970Receipt36_chunk49 := witnessRule 36 52 32 560150 560330 32 2896
  0xfa3fc3fc 0x15854418b9b0a898851726153384e2c2a4621518544c421b0a99b1726152310a2e2c2a87118951b0a91884 (by decide +kernel)
private def pack_E6970Receipt36_chunk50 := witnessRule 36 52 64 560331 560459 32 2798
  0xffebffaf 0x46152364e6c2a2105d18544213930a89885 (by decide +kernel)
private def pack_E6970Receipt36_chunk51 := witnessRule 36 52 96 560460 560588 32 2709
  0xaafabffd 0x563342e6c86c9c594dab8a883661548c8685c994d9b29a (by decide +kernel)
private def pack_E6970Receipt36_chunk52 := witnessRule 36 52 128 560640 560832 32 2546
  0xf8793eaf 0x2e4ca6c9c990d9b8b19884375342e6c86c9cd8cd9b8b21b47331062e8c66c9c990d9ba9a (by decide +kernel)
private def pack_E6970Receipt36_chunk53 := witnessRule 36 52 160 560833 561026 19 1493
  0x7ffbc 0x2ee685c598d938b29b (by decide +kernel)
private def pack_E6970Receipt36_chunk54 := witnessRule 36 51 0 570015 570147 32 2898
  0xff8ff8ff 0x11894419b1291b1726251310a6c4a262109894cd8b8b1291885 (by decide +kernel)
private def pack_E6970Receipt36_chunk55 := witnessRule 36 51 32 570148 570327 32 2844
  0xe17f17f8 0x46251362e8c4ac98554d93931289c3725236ac4a8d8948d8b9b1289c2716252388c4a26c5cd894420b931291c (by decide +kernel)
private def pack_E6970Receipt36_chunk56 := witnessRule 36 51 64 570328 570455 32 2795
  0xfe03f80f 0x158544c42230a99b1736152310a2e4c2a870dc9895938aa9b4725136ac4a918548c421b0aa1b27362562e2c2aa70dc58944e2392883 (by decide +kernel)
private def pack_E6970Receipt36_chunk57 := witnessRule 36 51 96 570456 570585 32 2632
  0x43e83f40 0x9d1854421b930a898853716153388e2a462115c54518bab0a8842736151310a4e4c2a670dc58548c429b8aa1b57254cc2a20c5d18544c428b9b0a99c2726152310a4e2c2a8711c5895a38a8a09c (by decide +kernel)
private def pack_E6970Receipt36_chunk58 := witnessRule 36 51 128 570586 570775 32 2474
  0xf0e0611d 0x5c998d939329b3716431086ec685d18cc420b9b29b2726431084e2cc6cdd4c41a38a19b56331068ca685cd90c420b9331b4716151310a8e2a66d5c5045ab0a91b (by decide +kernel)
private def pack_E6970Receipt36_chunk59 := witnessRule 36 51 160 570832 571025 18 1386
  0x3fffd 0xb8b39b (by decide +kernel)
private def pack_E6970Receipt36_chunk60 := witnessRule 36 50 0 580014 580145 32 2875
  0xff0ff17f 0x36351362e6c6ac58954d938b1a89c463544c6a46c5c98d44e139a91b (by decide +kernel)
private def pack_E6970Receipt36_chunk61 := witnessRule 36 50 32 580146 580275 32 2745
  0x7fc3fe0 0x1589441a31291b1736251310a2e4c4a6709c58948c42a3128988436253362e4c4a462145c58950e231aa3625231084c4a86c9c98d58b92a9b (by decide +kernel)
private def pack_E6970Receipt36_chunk62 := witnessRule 36 50 64 580324 580450 32 2799
  0xe0ffc3ff 0x3312a46252362e8c4a2709cd8944213931291c56251362e8c4a2105cd8948e13931289885 (by decide +kernel)
private def pack_E6970Receipt36_chunk63 := witnessRule 36 50 96 580451 580581 32 2601
  0x3c0bf0bf 0x11c58944e2b9288366254ac2a4621118550d93a312b1726155386e4c4a2711c948dab1289b17562566c2aa6c9cd8944e1b8b1291c (by decide +kernel)
private def pack_E6970Receipt36_chunk64 := witnessRule 36 50 128 580582 580773 32 2410
  0xe30380c2 0xb9339b2716631084f069194c419b39a1726631082e2d06cdc58550e238a9988446154362e8c2a6709cd8548c4293930aa1c3716153310a6e2aa6d5c544c46330a8988456153362e8c2a462145cd8550e138b0aa9c (by decide +kernel)
private def pack_E6970Receipt36_chunk65 := witnessRule 36 50 160 580774 581025 18 1361
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk66 := witnessRule 36 49 0 590013 590143 32 2856
  0xfe3ff1ff 0x118d4419b1a91b1726351310a6c6a2621098d4cd8b8b1a91885 (by decide +kernel)
private def pack_E6970Receipt36_chunk67 := witnessRule 36 49 32 590144 590272 32 2718
  0x2ff17fc7 0x98954d93931a89c3735236ac6a8d8d48d8b9b1a89c2716352388c6a26c5cd8d4420b931a91c (by decide +kernel)
private def pack_E6970Receipt36_chunk68 := witnessRule 36 49 64 590273 590399 32 2691
  0x3fe07fc 0x158944c42231299b1736252310a2e4c4a870dc98d59392a9b563548c4a46210d8950d939b1ab1716255386e2c6a27118d44d8ba31ab (by decide +kernel)
private def pack_E6970Receipt36_chunk69 := witnessRule 36 49 96 590448 590579 32 2583
  0xf03f81ff 0x66251362eac4a2105d18948e139b12898852726253386e2c4a46215989441ab1291b1746251310a2e6c4a6709c98948c42938b12a1c (by decide +kernel)
private def pack_E6970Receipt36_chunk70 := witnessRule 36 49 128 590580 590772 32 2349
  0xf70e1381 0xbd1a36156362e6c2aa709c98550c42938b0ab1c5615331088c2aa6c5cd8550c428b930ab1c27157368e4a66d58948da30aa188436156364e6c4a470dc98944c429b8b1299c (by decide +kernel)
private def pack_E6970Receipt36_chunk71 := witnessRule 36 49 160 590773 591024 16 1187
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk72 := witnessRule 36 48 0 600012 600141 32 2830
  0xfc3fe2ff 0x36451362e6c8ac58d54d938b2289c464544c8a46c5c99144e13a291b (by decide +kernel)
private def pack_E6970Receipt36_chunk73 := witnessRule 36 48 32 600142 600269 32 2700
  0xffc3ff07 0x231a8988436353362e4c6a462145c58d50e2322a3635231084c6a86c9c99158b9aa9b (by decide +kernel)
private def pack_E6970Receipt36_chunk74 := witnessRule 36 48 64 600270 600395 32 2669
  0x7ff0ffe0 0x9c98d48e2b1a89b1746351082e6c6a4709c98d44c42ab1a88346352362e6c6a262145c98d4ce138b1a91885 (by decide +kernel)
private def pack_E6970Receipt36_chunk75 := witnessRule 36 48 96 600396 600576 32 2476
  0x817c2ff0 0x6625206ac4a4621118950d8b9b12998851726255386e4c6a2711cd48dab1a89b17563566c4aa6c9cd8d44e1b8b1a91c663548c6a46c5d18d44e139b1a884 (by decide +kernel)
private def pack_E6970Receipt36_chunk76 := witnessRule 36 48 128 600577 600771 32 2302
  0xfc3c2c0f 0x8c2aa6210d855cd8b930ab18851716158388c4a86cd8558c42130ac1b2726254386e4aa6d58944c822b1299b1746252310a2e6c4a8709c9894cc42938b12a9c (by decide +kernel)
private def pack_E6970Receipt36_chunk77 := witnessRule 36 48 160 600772 601024 15 1093
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk78 := witnessRule 36 47 0 610011 610139 32 2800
  0xf8ffe3ff 0x11914419b2291b1726451310a6c8a262109914cd8b8b2291885 (by decide +kernel)
private def pack_E6970Receipt36_chunk79 := witnessRule 36 47 32 610140 610266 32 2688
  0xff17fe3f 0xac8a8d9148d8b9b2289c2716452388c8a26c5cd914420b932291c (by decide +kernel)
private def pack_E6970Receipt36_chunk80 := witnessRule 36 47 64 610267 610392 32 2610
  0xff81ff85 0xac8a918d48c421b1aa1b27364562e2c6aa70dc59144e232289b17464564c6aa6c9c99144e1ba291b (by decide +kernel)
private def pack_E6970Receipt36_chunk81 := witnessRule 36 47 96 610393 610523 32 2383
  0x3f03fc0 0x158d44c42231a99b1746352384e6c6a262149c98d4ce1b8b1a918856635106ac6a46c5d18d44c428b9b1a99c2726352310a4e2c6a87158d44c42231a99b1736352310a2e4c6a870dc9915939aa9b (by decide +kernel)
private def pack_E6970Receipt36_chunk82 := witnessRule 36 47 128 610576 610771 32 2252
  0xfeb83c0f 0x1b0ab19041615a368c4a6641118954d8b9b12a18851726256384e2c4aa621558948c822312a188436256362e4c4aa62145c5895ce1b8b1a99c (by decide +kernel)
private def pack_E6970Receipt36_chunk83 := witnessRule 36 47 160 610772 610961 12 859
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk84 := witnessRule 36 46 0 620010 620137 32 2762
  0xf0ffc5ff 0x36551362e6caac59154d938b2a89c465544caa46c5c99544e13aa91b (by decide +kernel)
private def pack_E6970Receipt36_chunk85 := witnessRule 36 46 32 620138 620263 32 2668
  0xfc3ff83f 0x23228988436453362e4c8a462145c59150e232aa3645231084c8a86c9c99558ba2a9b (by decide +kernel)
private def pack_E6970Receipt36_chunk86 := witnessRule 36 46 64 620264 620389 32 2569
  0xfc3ffc1f 0x2b2289b1746451082e6c8a4709c99144c42ab2288346452362e6c8a262145c9914ce138b2291885 (by decide +kernel)
private def pack_E6970Receipt36_chunk87 := witnessRule 36 46 96 620390 620521 32 2311
  0x17c2fe0f 0x118d50d8b9b1a998851726355384e6ac6d59144da31a9988436355364e6c8a270dc59148e3322a46452362e8c8a2709cd9144213932291c (by decide +kernel)
private def pack_E6970Receipt36_chunk88 := witnessRule 36 46 128 620522 620771 32 2194
  0xfff8301c 0x118950c821b12b188426258362e2c4ae62145c964dab1289a044635331086c6aa6c5cd8d50e13931a998852716355386e6a8621158d4c1ab1a91884 (by decide +kernel)
private def pack_E6970Receipt36_chunk89 := witnessRule 36 46 160 620772 620960 10 704
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk90 := witnessRule 36 45 0 630009 630135 32 2720
  0xe3ffc7ff 0x11954419b2a91b1726551310a6caa262109954cd8b8b2a91885 (by decide +kernel)
private def pack_E6970Receipt36_chunk91 := witnessRule 36 45 32 630136 630260 32 2632
  0xf17ff1ff 0xacaa8d9548d8b9b2a89c2716552388caa26c5cd954420b932a91c (by decide +kernel)
private def pack_E6970Receipt36_chunk92 := witnessRule 36 45 64 630261 630387 32 2505
  0xf03ff0bf 0xacaa919148c421b22a1b27365562e2c8aa70dc59544e232a89b17465564c8aa6c9c99544e1baa91b (by decide +kernel)
private def pack_E6970Receipt36_chunk93 := witnessRule 36 45 96 630388 630520 32 2249
  0x1781fc0f 0x3635531084c6ae6c9c9914ce1ba2a1b5645206ac8a46c5d19144c428b9b2299c2726452310a4e2c8a87159144c42232299b1736452310a2e4c8a870dc995593a2a9b (by decide +kernel)
private def pack_E6970Receipt36_chunk94 := witnessRule 36 45 128 630521 630772 32 2144
  0xfff8180c 0x8c4a66810d8954cc21312b9904162593108502c2aa6214a055cda31a919844635431086c6ac6c5c98d54c428b8b1ab9c273563108304e4a2887558d44cc2232299b (by decide +kernel)
private def pack_E6970Receipt36_chunk95 := witnessRule 36 45 160 630832 630960 7 487
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk96 := witnessRule 36 44 0 640008 640133 32 2670
  0xc3ff8bff 0x36651362e6ccac59554d938b3289c466544cca46c5c99944e13b291b (by decide +kernel)
private def pack_E6970Receipt36_chunk97 := witnessRule 36 44 32 640134 640257 32 2584
  0xc3ffc1ff 0x232a8988436553362e4caa462145c59550e2332a3655231084caa86c9c99958baaa9b (by decide +kernel)
private def pack_E6970Receipt36_chunk98 := witnessRule 36 44 64 640258 640385 32 2461
  0xc3ff83ff 0x2b2a89b1746551082e6caa4709c99544c42ab2a88346552362e6caa262145c9954ce138b2a91885 (by decide +kernel)
private def pack_E6970Receipt36_chunk99 := witnessRule 36 44 96 640386 640519 32 2198
  0xf03f07f 0x2e6c8a662145c99154e138b22a18852745636ac8a264111914cc421b22a9b1726454310a2e2c8ac70dc59548e2b2a88346552362e8caa2709cd9544213932a91c (by decide +kernel)
private def pack_E6970Receipt36_chunk100 := witnessRule 36 44 128 640520 640832 32 2099
  0xfffd581c 0x6c4a86a1058960cc2140ab19044635333086c6aa641098d5cc420b1ac9b281625538502e4a8621519148c822322a1b (by decide +kernel)
private def pack_E6970Receipt36_chunk101 := witnessRule 36 44 160 640833 640897 4 274
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk102 := witnessRule 36 43 0 650007 650131 32 2616
  0x8fff8fff 0x11994419b3291b1726651310a6cca262109994cd8b8b3291885 (by decide +kernel)
private def pack_E6970Receipt36_chunk103 := witnessRule 36 43 32 650132 650209 32 2520
  0x17ff8fff 0xacca8d9948d8b9b3289c2716652388cca26c5cd994420b933291c (by decide +kernel)
private def pack_E6970Receipt36_chunk104 := witnessRule 36 43 64 650256 650384 32 2413
  0x81ff0bff 0xacca919548c421b2aa1b27366562e2caaa70dc59944e233289b17466564caaa6c9c99944e1bb291b (by decide +kernel)
private def pack_E6970Receipt36_chunk105 := witnessRule 36 43 96 650385 650519 32 2134
  0x781f0bf 0x3645531084c8ae6c5c59158c428ba2c1b2817354388caa46210d9550d8b9b2a99c2726552310a4e2caa870dd54cc422b2a8988446553362e6caa462145c99550e13aaa9b (by decide +kernel)
private def pack_E6970Receipt36_chunk106 := witnessRule 36 43 128 650520 650896 32 2069
  0xfffffe06 0x6c6a8681098d58cc20b1ac19042816254320a504ac6210a05c54510c47232299904 (by decide +kernel)
private def pack_E6970Receipt36_chunk107 := witnessRule 36 42 0 660006 660083 32 2554
  0xfff17ff 0x36751362e6ceac59954d938b3a89c467544cea46c5c99d44e13ba91b (by decide +kernel)
private def pack_E6970Receipt36_chunk108 := witnessRule 36 42 32 660130 660206 32 2546
  0x3ffe0fff 0x2e4cca462145c59950e233aa3665231084cca86c9c99d58bb2a9b (by decide +kernel)
private def pack_E6970Receipt36_chunk109 := witnessRule 36 42 64 660207 660333 32 2291
  0xffc1ffc 0xacca26c5d1994420b9b3291c2726651310aacca20d19948d8b9b32898851726653384e2cca4621519944c421b3299b (by decide +kernel)
private def pack_E6970Receipt36_chunk110 := witnessRule 36 42 96 660384 660519 32 2076
  0x705e0bf 0x1b22a19842645632082c8b06210a058d50c42941ab1b4655133088caa66210d9554d8b932aa1885171655638304e8a286755954c1a33291b3655431084caac6c9c99948e1bb299b (by decide +kernel)
private def pack_E6970Receipt36_chunk111 := witnessRule 36 42 128 660520 660896 29 1841
  0x1ffffe87 0x1b1a99b04163573408502c4a66814a0954cc21c0aa188885 (by decide +kernel)
private def pack_E6970Receipt36_chunk112 := witnessRule 36 41 0 670005 670082 32 2538
  0x3fff1fff 0x1b3a91b1726751310a6cea2621099d4cd8b8b3a91885 (by decide +kernel)
private def pack_E6970Receipt36_chunk113 := witnessRule 36 41 32 670083 670205 32 2484
  0xbffc7ffe 0x138b3a91c46751362e6cea2105c99d48e233a883 (by decide +kernel)
private def pack_E6970Receipt36_chunk114 := witnessRule 36 41 64 670206 670333 32 2193
  0x13fc2ff8 0x2b329034665231086cca86c5c59954e1b8b3a89c46751362e8ceac99954d93933a89c3775236acea8d9d48d8b9b3a89c (by decide +kernel)
private def pack_E6970Receipt36_chunk115 := witnessRule 36 41 96 670384 670520 32 2002
  0xa1c0f07f 0x3645335082c8ae6610a058d4ccc2941aa99043825431188caa46610d9550c82132ab18841655836502c8a870a05d14cc42a3328990446653362e6cca462145c99950e138b3299885 (by decide +kernel)
private def pack_E6970Receipt36_chunk116 := witnessRule 36 41 128 670576 670833 24 1497
  0xffffea 0x2c6ac6c10a0950d421c0a2190c (by decide +kernel)
private def pack_E6970Receipt36_chunk117 := witnessRule 36 40 0 680004 680080 32 2522
  0x3ffe2fff 0x59d54d938b4289c468544d0a46c5c9a144e13c291b (by decide +kernel)
private def pack_E6970Receipt36_chunk118 := witnessRule 36 40 32 680081 680203 32 2422
  0xfff07ffc 0x8d0a8d9d48c42133aa1b27268562eeaa6cda144d8b9b42b (by decide +kernel)
private def pack_E6970Receipt36_chunk119 := witnessRule 36 40 64 680204 680332 32 2101
  0x7f83ff0 0x119d44c421b3a99b1736752384e4cea262149c59d4ce2b3a88346752362e6cea262145c99d4ce138b3a918854675131086cea66c5c99d48c428b8b3aa1c (by decide +kernel)
private def pack_E6970Receipt36_chunk120 := witnessRule 36 40 96 680384 680576 32 1939
  0xf4e8789f 0xb22b1a84283543408704a6622414d954cd020b2ab99042816453320a508aa6210a05cd450cc472332919043665431084ccac6c5d95cd940baa99c (by decide +kernel)
private def pack_E6970Receipt36_chunk121 := witnessRule 36 40 128 680577 680832 20 1227
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk122 := witnessRule 36 39 0 690003 690079 32 2509
  0xfffe3fff 0x6d0a262109a14cd8b8b4291885 (by decide +kernel)
private def pack_E6970Receipt36_chunk123 := witnessRule 36 39 32 690080 690203 32 2315
  0x7ff1fff8 0x4e2d0a4711a144d8b9b428841726852388d0a20cda148d8b934289885 (by decide +kernel)
private def pack_E6970Receipt36_chunk124 := witnessRule 36 39 64 690204 690384 32 2023
  0xc2fc2ff1 0x233a9188436754362e4cea662145c59d54e0c13b28a11d46851366cea6621099d54d93934289c3785236ad0a8da148d8b9b4289c (by decide +kernel)
private def pack_E6970Receipt36_chunk125 := witnessRule 36 39 96 690385 690579 32 1873
  0xff5e9e8f 0x141a99b04381514332110c2caac6810a1150cc21c1a99888853665333082ccae6210a05954cc42942aa9b (by decide +kernel)
private def pack_E6970Receipt36_chunk126 := witnessRule 36 39 128 690580 690832 15 908
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk127 := witnessRule 36 38 0 700002 700077 32 2496
  0xfffc5fff 0x469544d2a46c5c9a544e13ca91b (by decide +kernel)
private def pack_E6970Receipt36_chunk128 := witnessRule 36 38 32 700078 700202 32 2208
  0xffe0fff0 0x234aa3685231084d0a86c9c9a558bc2a9b36951362e6d2ac5a154d938b4a89c (by decide +kernel)
private def pack_E6970Receipt36_chunk129 := witnessRule 36 38 64 700203 700385 32 1945
  0xc1fc1ff0 0x119d44cc21b3a999042675531082ceae6ca05994ce234290346852362e6d0a262145c9a14ce138b42918854685131086d0a66c5c9a148c428b8b42a1c (by decide +kernel)
private def pack_E6970Receipt36_chunk130 := witnessRule 36 38 96 700386 700581 32 1821
  0xfff7d753 0x702a284642618a114cd421c128a1990d3665235082ccac6610a1550c821c229988c (by decide +kernel)
private def pack_E6970Receipt36_chunk131 := witnessRule 36 38 128 700640 700769 10 597
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk132 := witnessRule 36 37 0 710001 710077 32 2434
  0xfffc7fff 0x6d2a262109a54cd8b8b4a91885 (by decide +kernel)
private def pack_E6970Receipt36_chunk133 := witnessRule 36 37 32 710078 710203 32 2104
  0xbff1fff1 0x4e2d2a4711a544d8b9b4a8841726952388d2a20cda548d8b934a89885 (by decide +kernel)
private def pack_E6970Receipt36_chunk134 := witnessRule 36 37 64 710204 710387 32 1869
  0xfa9f17f8 0x6cea4681059d58c821432a1884281755142311c8d0a26410da14cc421342a9b17856368d2a20cda548d8b9b4a89c (by decide +kernel)
private def pack_E6970Receipt36_chunk135 := witnessRule 36 37 96 710388 710643 32 1790
  0xfffffefd 0xe094508c8483142a99a04 (by decide +kernel)
private def pack_E6970Receipt36_chunk136 := witnessRule 36 37 128 710704 710768 4 237
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk137 := witnessRule 36 36 0 720000 720076 32 2372
  0xfff8bfff 0x46a544d4a46c5c9a944e13d291b (by decide +kernel)
private def pack_E6970Receipt36_chunk138 := witnessRule 36 36 32 720077 720203 32 2001
  0x3ff07ff0 0x2e4d2a462145c5a550e2352a3695231084d2a86c9c9a958bcaa9b36a51362e6d4ac5a554d938b5289c (by decide +kernel)
private def pack_E6970Receipt36_chunk139 := witnessRule 36 36 64 720204 720389 32 1796
  0xdfdff5fc 0xe0d4508c844314329998416856310850ea86d1a544c421b4a99b (by decide +kernel)
private def pack_E6970Receipt36_chunk140 := witnessRule 36 36 96 720390 720768 31 1714
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk141 := witnessRule 36 35 0 730000 730077 32 2257
  0xfffc7fff 0x6d4a262109a94cd8b8b5291885 (by decide +kernel)
private def pack_E6970Receipt36_chunk142 := witnessRule 36 35 32 730078 730205 32 1900
  0x87fc7ff8 0xda548c82134aa18841695636502d0a4711a944d8b9b528841726a52388d4a20cda948d8b935289885 (by decide +kernel)
private def pack_E6970Receipt36_chunk143 := witnessRule 36 35 64 730256 730392 32 1737
  0xffdef57f 0x133a91b843845142321a6d0a26a105a154cc2143a99904 (by decide +kernel)
private def pack_E6970Receipt36_chunk144 := witnessRule 36 35 96 730448 730705 24 1305
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk145 := witnessRule 36 34 0 740000 740077 32 2142
  0x3ffc5fff 0x5a954d938b5a89c46b544d6a46c5c9ad44e13da91b (by decide +kernel)
private def pack_E6970Receipt36_chunk146 := witnessRule 36 34 32 740078 740257 32 1843
  0xf5fe2ffc 0x169553208510a662111a94819b529188426a54362f4aa6cdad44d8b9b5ab (by decide +kernel)
private def pack_E6970Receipt36_chunk147 := witnessRule 36 34 64 740258 740450 32 1654
  0xfffffeff 0x134291b04 (by decide +kernel)
private def pack_E6970Receipt36_chunk148 := witnessRule 36 34 96 740451 740704 18 963
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk149 := witnessRule 36 33 0 750000 750078 32 2030
  0x3ffe3fff 0x1b5a91b1726b51310a6d6a262109ad4cd8b8b5a91885 (by decide +kernel)
private def pack_E6970Receipt36_chunk150 := witnessRule 36 33 32 750079 750259 32 1772
  0xfffffbfe 0xa254cda35a883 (by decide +kernel)
private def pack_E6970Receipt36_chunk151 := witnessRule 36 33 64 750260 750454 32 1602
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk152 := witnessRule 36 33 96 750512 750704 12 635
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk153 := witnessRule 36 32 0 760000 760078 32 1920
  0x4ffe2fff 0x6d6a264105ad54d940b5289c46c544d8a46c5c9b144e13e291b (by decide +kernel)
private def pack_E6970Receipt36_chunk154 := witnessRule 36 32 32 760128 760261 32 1692
  0xfd7fe5ff 0x134a89b8495535064d4a468105a950cc2144a91904 (by decide +kernel)
private def pack_E6970Receipt36_chunk155 := witnessRule 36 32 64 760262 760515 32 1572
  0xfffffff7 0xb4291c84 (by decide +kernel)
private def pack_E6970Receipt36_chunk156 := witnessRule 36 32 96 760516 760641 6 313
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk157 := witnessRule 36 31 0 770000 770128 32 1847
  0xdbff1fff 0x135a9198428a5231086d8a262109b14cd8b8b6291885 (by decide +kernel)
private def pack_E6970Receipt36_chunk158 := witnessRule 36 31 32 770129 770263 32 1592
  0xffbffdff 0x5a548e0252a9a03 (by decide +kernel)
private def pack_E6970Receipt36_chunk159 := witnessRule 36 31 64 770264 770640 32 1555
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk160 := witnessRule 36 30 0 780000 780129 32 1770
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk161 := witnessRule 36 30 32 780130 780265 32 1506
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk162 := witnessRule 36 30 64 780320 780640 27 1286
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk163 := witnessRule 36 29 0 790000 790130 32 1690
  0xf2ffa7ff 0x5ad48d825aa1a832895243084d8a26813154c81945a89904 (by decide +kernel)
private def pack_E6970Receipt36_chunk164 := witnessRule 36 29 32 790131 790322 32 1439
  0xfffbfebf 0x12a4760c5a944e420c4a8a09b85 (by decide +kernel)
private def pack_E6970Receipt36_chunk165 := witnessRule 36 29 64 790323 790577 21 978
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk166 := witnessRule 36 28 0 800000 800131 32 1606
  0xfdffdbff 0x314a2826c145b148d42145292104 (by decide +kernel)
private def pack_E6970Receipt36_chunk167 := witnessRule 36 28 32 800132 800324 32 1387
  0xffffffbf 0x5291d03 (by decide +kernel)
private def pack_E6970Receipt36_chunk168 := witnessRule 36 28 64 800325 800576 16 731
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk169 := witnessRule 36 27 0 810000 810132 32 1521
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk170 := witnessRule 36 27 32 810133 810384 32 1348
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk171 := witnessRule 36 27 64 810385 810576 11 495
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk172 := witnessRule 36 26 0 820000 820133 32 1436
  0xfd7fe5ff 0x5a89d831895241170b8a4700c62d451c2144a9209185 (by decide +kernel)
private def pack_E6970Receipt36_chunk173 := witnessRule 36 26 32 820134 820387 32 1316
  0xfffffff7 0x4a92603 (by decide +kernel)
private def pack_E6970Receipt36_chunk174 := witnessRule 36 26 64 820388 820513 6 265
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk175 := witnessRule 36 25 0 830000 830134 32 1361
  0xff7ffbff 0x29492c18c529208b05 (by decide +kernel)
private def pack_E6970Receipt36_chunk176 := witnessRule 36 25 32 830135 830450 32 1293
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk177 := witnessRule 36 25 64 830512 830512 1 44
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk178 := witnessRule 36 24 0 840000 840135 32 1290
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk179 := witnessRule 36 24 32 840136 840512 29 1144
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk180 := witnessRule 36 23 0 850000 850136 32 1225
  0xffdff5ff 0x12a4825812d45046c20c4a920908b86 (by decide +kernel)
private def pack_E6970Receipt36_chunk181 := witnessRule 36 23 32 850192 850449 24 921
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk182 := witnessRule 36 22 0 860000 860192 32 1168
  0xfffffbff 0x529209584 (by decide +kernel)
private def pack_E6970Receipt36_chunk183 := witnessRule 36 22 32 860193 860448 20 747
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk184 := witnessRule 36 21 0 870000 870194 32 1117
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk185 := witnessRule 36 21 32 870195 870448 16 583
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk186 := witnessRule 36 20 0 880000 880195 32 1068
  0xfffffdff 0x4a9211604 (by decide +kernel)
private def pack_E6970Receipt36_chunk187 := witnessRule 36 20 32 880196 880385 12 425
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk188 := witnessRule 36 19 0 890000 890197 32 1028
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk189 := witnessRule 36 19 32 890256 890384 8 277
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk190 := witnessRule 36 18 0 900000 900257 32 990
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk191 := witnessRule 36 18 32 900258 900384 5 169
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk192 := witnessRule 36 17 0 910000 910320 32 957
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk193 := witnessRule 36 17 32 910321 910321 1 33
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk194 := witnessRule 36 16 0 920000 920320 30 863
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk195 := witnessRule 36 15 0 930000 930320 27 746
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk196 := witnessRule 36 14 0 940000 940257 24 633
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk197 := witnessRule 36 13 0 950000 950256 21 531
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk198 := witnessRule 36 12 0 960000 960256 19 460
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk199 := witnessRule 36 11 0 970000 970193 16 369
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk200 := witnessRule 36 10 0 980000 980192 14 307
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk201 := witnessRule 36 9 0 990000 990192 12 251
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk202 := witnessRule 36 8 0 1000000 1000129 10 197
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk203 := witnessRule 36 7 0 1010000 1010128 8 149
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk204 := witnessRule 36 6 0 1020000 1020128 7 123
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk205 := witnessRule 36 5 0 1030000 1030065 5 82
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk206 := witnessRule 36 4 0 1040000 1040064 4 61
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk207 := witnessRule 36 3 0 1050000 1050064 3 43
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk208 := witnessRule 36 2 0 1060000 1060001 2 26
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk209 := witnessRule 36 1 0 1070000 1070000 1 12
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt36_chunk210 := witnessRule 36 0 0 1080000 1080000 1 11
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt36_chunks : List (Chunk 36) := [pack_E6970Receipt36_chunk0, pack_E6970Receipt36_chunk1, pack_E6970Receipt36_chunk2, pack_E6970Receipt36_chunk3, pack_E6970Receipt36_chunk4, pack_E6970Receipt36_chunk5, pack_E6970Receipt36_chunk6, pack_E6970Receipt36_chunk7, pack_E6970Receipt36_chunk8, pack_E6970Receipt36_chunk9, pack_E6970Receipt36_chunk10, pack_E6970Receipt36_chunk11, pack_E6970Receipt36_chunk12, pack_E6970Receipt36_chunk13, pack_E6970Receipt36_chunk14, pack_E6970Receipt36_chunk15, pack_E6970Receipt36_chunk16, pack_E6970Receipt36_chunk17, pack_E6970Receipt36_chunk18, pack_E6970Receipt36_chunk19, pack_E6970Receipt36_chunk20, pack_E6970Receipt36_chunk21, pack_E6970Receipt36_chunk22, pack_E6970Receipt36_chunk23, pack_E6970Receipt36_chunk24, pack_E6970Receipt36_chunk25, pack_E6970Receipt36_chunk26, pack_E6970Receipt36_chunk27, pack_E6970Receipt36_chunk28, pack_E6970Receipt36_chunk29, pack_E6970Receipt36_chunk30, pack_E6970Receipt36_chunk31, pack_E6970Receipt36_chunk32, pack_E6970Receipt36_chunk33, pack_E6970Receipt36_chunk34, pack_E6970Receipt36_chunk35, pack_E6970Receipt36_chunk36, pack_E6970Receipt36_chunk37, pack_E6970Receipt36_chunk38, pack_E6970Receipt36_chunk39, pack_E6970Receipt36_chunk40, pack_E6970Receipt36_chunk41, pack_E6970Receipt36_chunk42, pack_E6970Receipt36_chunk43, pack_E6970Receipt36_chunk44, pack_E6970Receipt36_chunk45, pack_E6970Receipt36_chunk46, pack_E6970Receipt36_chunk47, pack_E6970Receipt36_chunk48, pack_E6970Receipt36_chunk49, pack_E6970Receipt36_chunk50, pack_E6970Receipt36_chunk51, pack_E6970Receipt36_chunk52, pack_E6970Receipt36_chunk53, pack_E6970Receipt36_chunk54, pack_E6970Receipt36_chunk55, pack_E6970Receipt36_chunk56, pack_E6970Receipt36_chunk57, pack_E6970Receipt36_chunk58, pack_E6970Receipt36_chunk59, pack_E6970Receipt36_chunk60, pack_E6970Receipt36_chunk61, pack_E6970Receipt36_chunk62, pack_E6970Receipt36_chunk63, pack_E6970Receipt36_chunk64, pack_E6970Receipt36_chunk65, pack_E6970Receipt36_chunk66, pack_E6970Receipt36_chunk67, pack_E6970Receipt36_chunk68, pack_E6970Receipt36_chunk69, pack_E6970Receipt36_chunk70, pack_E6970Receipt36_chunk71, pack_E6970Receipt36_chunk72, pack_E6970Receipt36_chunk73, pack_E6970Receipt36_chunk74, pack_E6970Receipt36_chunk75, pack_E6970Receipt36_chunk76, pack_E6970Receipt36_chunk77, pack_E6970Receipt36_chunk78, pack_E6970Receipt36_chunk79, pack_E6970Receipt36_chunk80, pack_E6970Receipt36_chunk81, pack_E6970Receipt36_chunk82, pack_E6970Receipt36_chunk83, pack_E6970Receipt36_chunk84, pack_E6970Receipt36_chunk85, pack_E6970Receipt36_chunk86, pack_E6970Receipt36_chunk87, pack_E6970Receipt36_chunk88, pack_E6970Receipt36_chunk89, pack_E6970Receipt36_chunk90, pack_E6970Receipt36_chunk91, pack_E6970Receipt36_chunk92, pack_E6970Receipt36_chunk93, pack_E6970Receipt36_chunk94, pack_E6970Receipt36_chunk95, pack_E6970Receipt36_chunk96, pack_E6970Receipt36_chunk97, pack_E6970Receipt36_chunk98, pack_E6970Receipt36_chunk99, pack_E6970Receipt36_chunk100, pack_E6970Receipt36_chunk101, pack_E6970Receipt36_chunk102, pack_E6970Receipt36_chunk103, pack_E6970Receipt36_chunk104, pack_E6970Receipt36_chunk105, pack_E6970Receipt36_chunk106, pack_E6970Receipt36_chunk107, pack_E6970Receipt36_chunk108, pack_E6970Receipt36_chunk109, pack_E6970Receipt36_chunk110, pack_E6970Receipt36_chunk111, pack_E6970Receipt36_chunk112, pack_E6970Receipt36_chunk113, pack_E6970Receipt36_chunk114, pack_E6970Receipt36_chunk115, pack_E6970Receipt36_chunk116, pack_E6970Receipt36_chunk117, pack_E6970Receipt36_chunk118, pack_E6970Receipt36_chunk119, pack_E6970Receipt36_chunk120, pack_E6970Receipt36_chunk121, pack_E6970Receipt36_chunk122, pack_E6970Receipt36_chunk123, pack_E6970Receipt36_chunk124, pack_E6970Receipt36_chunk125, pack_E6970Receipt36_chunk126, pack_E6970Receipt36_chunk127, pack_E6970Receipt36_chunk128, pack_E6970Receipt36_chunk129, pack_E6970Receipt36_chunk130, pack_E6970Receipt36_chunk131, pack_E6970Receipt36_chunk132, pack_E6970Receipt36_chunk133, pack_E6970Receipt36_chunk134, pack_E6970Receipt36_chunk135, pack_E6970Receipt36_chunk136, pack_E6970Receipt36_chunk137, pack_E6970Receipt36_chunk138, pack_E6970Receipt36_chunk139, pack_E6970Receipt36_chunk140, pack_E6970Receipt36_chunk141, pack_E6970Receipt36_chunk142, pack_E6970Receipt36_chunk143, pack_E6970Receipt36_chunk144, pack_E6970Receipt36_chunk145, pack_E6970Receipt36_chunk146, pack_E6970Receipt36_chunk147, pack_E6970Receipt36_chunk148, pack_E6970Receipt36_chunk149, pack_E6970Receipt36_chunk150, pack_E6970Receipt36_chunk151, pack_E6970Receipt36_chunk152, pack_E6970Receipt36_chunk153, pack_E6970Receipt36_chunk154, pack_E6970Receipt36_chunk155, pack_E6970Receipt36_chunk156, pack_E6970Receipt36_chunk157, pack_E6970Receipt36_chunk158, pack_E6970Receipt36_chunk159, pack_E6970Receipt36_chunk160, pack_E6970Receipt36_chunk161, pack_E6970Receipt36_chunk162, pack_E6970Receipt36_chunk163, pack_E6970Receipt36_chunk164, pack_E6970Receipt36_chunk165, pack_E6970Receipt36_chunk166, pack_E6970Receipt36_chunk167, pack_E6970Receipt36_chunk168, pack_E6970Receipt36_chunk169, pack_E6970Receipt36_chunk170, pack_E6970Receipt36_chunk171, pack_E6970Receipt36_chunk172, pack_E6970Receipt36_chunk173, pack_E6970Receipt36_chunk174, pack_E6970Receipt36_chunk175, pack_E6970Receipt36_chunk176, pack_E6970Receipt36_chunk177, pack_E6970Receipt36_chunk178, pack_E6970Receipt36_chunk179, pack_E6970Receipt36_chunk180, pack_E6970Receipt36_chunk181, pack_E6970Receipt36_chunk182, pack_E6970Receipt36_chunk183, pack_E6970Receipt36_chunk184, pack_E6970Receipt36_chunk185, pack_E6970Receipt36_chunk186, pack_E6970Receipt36_chunk187, pack_E6970Receipt36_chunk188, pack_E6970Receipt36_chunk189, pack_E6970Receipt36_chunk190, pack_E6970Receipt36_chunk191, pack_E6970Receipt36_chunk192, pack_E6970Receipt36_chunk193, pack_E6970Receipt36_chunk194, pack_E6970Receipt36_chunk195, pack_E6970Receipt36_chunk196, pack_E6970Receipt36_chunk197, pack_E6970Receipt36_chunk198, pack_E6970Receipt36_chunk199, pack_E6970Receipt36_chunk200, pack_E6970Receipt36_chunk201, pack_E6970Receipt36_chunk202, pack_E6970Receipt36_chunk203, pack_E6970Receipt36_chunk204, pack_E6970Receipt36_chunk205, pack_E6970Receipt36_chunk206, pack_E6970Receipt36_chunk207, pack_E6970Receipt36_chunk208, pack_E6970Receipt36_chunk209, pack_E6970Receipt36_chunk210]
def rows36 := rowsFrom pack_E6970Receipt36_chunks
theorem good36 : ∀ r ∈ rows36, good 36 r = true := rowsFrom_good pack_E6970Receipt36_chunks
theorem sorted36 : rows36.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt36_chunks 0 (by decide +kernel)).1
theorem mass36 (i : Fin 61) :
    bandCount 36 (i.val : ℤ) 60 16 ≤ (rows36.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt36_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 36 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt36_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total36 : (rows36.map (price 36)).sum = 402925 :=
  (total_eq pack_E6970Receipt36_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt36

section Pack_E6970Receipt37

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt37_chunk0 := witnessA6966Final 37 60 0 510023 510215 32 3323
  0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk1 := witnessA6966Final 37 60 32 510216 510404 32 3283
  0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk2 := witnessA6966Final 37 60 64 510405 510588 32 3274
  0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk3 := witnessA6966Final 37 60 96 510589 510769 32 3234
  0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk4 := witnessA6966Final 37 60 128 510770 510905 32 3153
  0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk5 := witnessA6966Final 37 60 160 510960 511030 15 1437
  0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk6 := witnessRule 37 59 0 520022 520213 32 3237
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk7 := witnessRule 37 59 32 520214 520400 32 3197
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk8 := witnessRule 37 59 64 520401 520583 32 3175
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk9 := witnessRule 37 59 96 520584 520713 32 3146
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk10 := witnessRule 37 59 128 520714 520900 32 3058
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk11 := witnessRule 37 59 160 520901 521029 18 1664
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk12 := witnessRule 37 58 0 530021 530210 32 3167
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk13 := witnessRule 37 58 32 530211 530396 32 3123
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk14 := witnessRule 37 58 64 530397 530528 32 3074
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk15 := witnessRule 37 58 96 530529 530707 32 3077
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk16 := witnessRule 37 58 128 530708 530896 32 2960
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk17 := witnessRule 37 58 160 530897 531029 21 1892
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk18 := witnessRule 37 57 0 540020 540208 32 3113
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk19 := witnessRule 37 57 32 540209 540392 32 3042
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk20 := witnessRule 37 57 64 540393 540523 32 3031
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk21 := witnessRule 37 57 96 540524 540652 32 2980
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk22 := witnessRule 37 57 128 540653 540838 32 2883
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk23 := witnessRule 37 57 160 540839 541028 23 2016
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk24 := witnessRule 37 56 0 550019 550205 32 3051
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk25 := witnessRule 37 56 32 550206 550338 32 2993
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk26 := witnessRule 37 56 64 550339 550518 32 2990
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk27 := witnessRule 37 56 96 550519 550647 32 2908
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk28 := witnessRule 37 56 128 550648 550834 32 2787
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk29 := witnessRule 37 56 160 550835 551028 25 2134
  0x1fffbff 0xb99a (by decide +kernel)
private def pack_E6970Receipt37_chunk30 := witnessRule 37 55 0 560018 560152 32 2996
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk31 := witnessRule 37 55 32 560204 560335 32 2974
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk32 := witnessRule 37 55 64 560336 560465 32 2884
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk33 := witnessRule 37 55 96 560514 560642 32 2896
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk34 := witnessRule 37 55 128 560643 560777 32 2704
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk35 := witnessRule 37 55 160 560832 561027 26 2167
  0x3ffefdf 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt37_chunk36 := witnessRule 37 54 0 570017 570150 32 2968
  0xafeafabf 0x17263364e868d8cd0b8b21b37141368c2a8990d0ba9a (by decide +kernel)
private def pack_E6970Receipt37_chunk37 := witnessRule 37 54 32 570151 570331 32 2941
  0xffe7fd7f 0x373348e2889c58cda38a2 (by decide +kernel)
private def pack_E6970Receipt37_chunk38 := witnessRule 37 54 64 570332 570460 32 2850
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk39 := witnessRule 37 54 96 570461 570588 32 2793
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk40 := witnessRule 37 54 128 570589 570774 32 2653
  0x6fffffff 0x5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt37_chunk41 := witnessRule 37 54 160 570775 571027 27 2192
  0x7ffdf3f 0x2ea685c590d938b19b (by decide +kernel)
private def pack_E6970Receipt37_chunk42 := witnessRule 37 53 0 580016 580148 32 2939
  0xffdffdff 0xd8548d8b9b0a884 (by decide +kernel)
private def pack_E6970Receipt37_chunk43 := witnessRule 37 53 32 580149 580328 32 2894
  0xf57f55fe 0x463342e4c86c9d4d2b0aa364342e2ca6d1c54419329a (by decide +kernel)
private def pack_E6970Receipt37_chunk44 := witnessRule 37 53 64 580329 580456 32 2838
  0x7febff57 0x15c51139319b374342e6c66c9c590da38a09b (by decide +kernel)
private def pack_E6970Receipt37_chunk45 := witnessRule 37 53 96 580457 580584 32 2738
  0xffff3ffd 0x8e6695c511b8b19b (by decide +kernel)
private def pack_E6970Receipt37_chunk46 := witnessRule 37 53 128 580585 580771 32 2574
  0xbedfffff 0x6e8685cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt37_chunk47 := witnessRule 37 53 160 580772 581026 27 2139
  0x7ffbe7c 0xbb1a17165364e2c86c5c990d939319b (by decide +kernel)
private def pack_E6970Receipt37_chunk48 := witnessRule 37 52 0 590015 590146 32 2914
  0xff0ff07f 0x230a8988436153362e4c2a462145c58550e2312a3615231084c2a86c9c98958b8aa9b (by decide +kernel)
private def pack_E6970Receipt37_chunk49 := witnessRule 37 52 32 590147 590276 32 2797
  0xaffebfe8 0x46152364e6c2a2105d18544213930a8988556151062e6c2a262145c9854ce138b0a91885 (by decide +kernel)
private def pack_E6970Receipt37_chunk50 := witnessRule 37 52 64 590325 590451 32 2844
  0xeafff7ff 0x661548c8685c994d9b29a (by decide +kernel)
private def pack_E6970Receipt37_chunk51 := witnessRule 37 52 96 590452 590580 32 2691
  0x7f57faaf 0x57141362e8c66c9c990d9ba9a563342e6c86c9c594dab8a883 (by decide +kernel)
private def pack_E6970Receipt37_chunk52 := witnessRule 37 52 128 590581 590769 32 2505
  0x793ed3f5 0x6ea685cd90d939b19b37164368e2c66c5d18cd9b9319b47434ce2289cd8cd9b8b21b (by decide +kernel)
private def pack_E6970Receipt37_chunk53 := witnessRule 37 52 160 590770 591026 27 2092
  0x7ffbcf8 0x5dcd0b8b31b27165362e4ca6c9c990d9b8b19884 (by decide +kernel)
private def pack_E6970Receipt37_chunk54 := witnessRule 37 51 0 600014 600144 32 2890
  0xfe2ff1ff 0xac4a8d8948d8b9b1289c2716252388c4a26c5cd894420b931291c (by decide +kernel)
private def pack_E6970Receipt37_chunk55 := witnessRule 37 51 32 600145 600273 32 2767
  0x7f01fc2 0xb9b0a918851726154386e4c4ac9c554da39289b562548c2a46210d8550d939b12b1716155386e2c4a2711c9441a31289b17462564c2aa6c9c98944e1b9291b (by decide +kernel)
private def pack_E6970Receipt37_chunk56 := witnessRule 37 51 64 600274 600400 32 2740
  0xa0fe81fc 0x2eac2a2109cd8544c4293930a99c3716152310a6e2a86d5c95330a8831746151310a2e6c2a6709c98548c42938b0aa1c47162568e2a2827158544c42230a99b (by decide +kernel)
private def pack_E6970Receipt37_chunk57 := witnessRule 37 51 96 600448 600577 32 2686
  0xf51fa87f 0x8ca68dcd85442238b0a898854715336ae48958548d93a30a8843726151310a6e2c2a6711c548c422b8a8a3 (by decide +kernel)
private def pack_E6970Receipt37_chunk58 := witnessRule 37 51 128 600578 600713 32 2449
  0xf0783e2b 0x2e6ca6c9cd90d9b931988437165368e8620c5d190d939b1988427265366e2c86210dd8d2b21a1746331082e6ca6d1c9854422b8a89884 (by decide +kernel)
private def pack_E6970Receipt37_chunk59 := witnessRule 37 51 160 600768 601025 26 1970
  0x3fffdf0 0xb8b39b17266364e4ca6cdc590c421bb1a (by decide +kernel)
private def pack_E6970Receipt37_chunk60 := witnessRule 37 50 0 610013 610142 32 2866
  0xfc3fe0ff 0x23128988436253362e4c4a462145c58950e231aa3625231084c4a86c9c98d58b92a9b (by decide +kernel)
private def pack_E6970Receipt37_chunk61 := witnessRule 37 50 32 610143 610270 32 2743
  0xffc3ff07 0x2b1289b1746251082e6c4a4709c98944c42ab1288346252362e6c4a262145c9894ce138b1291885 (by decide +kernel)
private def pack_E6970Receipt37_chunk62 := witnessRule 37 50 64 610271 610396 32 2713
  0x2ff0bfe0 0xb930aa9c3726251388e4a46d58944d8bab12b36155364e6c4a270dc58948e3312a46252362e8c4a2709cd8944213931291c (by decide +kernel)
private def pack_E6970Receipt37_chunk63 := witnessRule 37 50 96 610397 610524 32 2571
  0x80f807f0 0x2eac2a262145d1854ce139b0a918852726154388e4c4acdc554dab9289b661513108ac2a66c5d18548c428b9b0aa1c37362564e2c2aa711c58944e2b9288366254ac2a4621118550d93a312b (by decide +kernel)
private def pack_E6970Receipt37_chunk64 := witnessRule 37 50 128 610525 610711 32 2402
  0xc0c0340e 0x5d190c420b9b31b2726531084e2ce6cdd8c41a38a21b56431068cc685cd94c420b9339b3726153388e2c2a462151c550db390a56153364e8c2a262149cd854ce1b930a918853716154388e2a662115c54504e3b0a883 (by decide +kernel)
private def pack_E6970Receipt37_chunk65 := witnessRule 37 50 160 610712 611025 25 1856
  0x1fffff1 0x2e4ce6c9c598c4213c1a (by decide +kernel)
private def pack_E6970Receipt37_chunk66 := witnessRule 37 49 0 620012 620140 32 2834
  0xf8bfe3ff 0xac6a8d8d48d8b9b1a89c2716352388c6a26c5cd8d4420b931a91c (by decide +kernel)
private def pack_E6970Receipt37_chunk67 := witnessRule 37 49 32 620141 620267 32 2725
  0xff03fe17 0xac6a918948c421b12a1b27363562e2c4aa70dc58d44e231a89b17463564c4aa6c9c98d44e1b9a91b (by decide +kernel)
private def pack_E6970Receipt37_chunk68 := witnessRule 37 49 64 620268 620392 32 2687
  0xff81ff81 0x6625106ac4a46c5d18944c428b9b1299c2726252310a4e2c4a87158944c42231299b1736252310a2e4c4a870dc98d59392a9b (by decide +kernel)
private def pack_E6970Receipt37_chunk69 := witnessRule 37 49 96 620393 620521 32 2490
  0x1fc0ff81 0x4e8c4a270dcd894421b931291c76254ac4a46c5d58944e13a3128842736252386e4c4a2621598944d8bab128841746252384e6c4a262149c9894ce1b8b1291885 (by decide +kernel)
private def pack_E6970Receipt37_chunk70 := witnessRule 37 49 128 620522 620710 32 2332
  0x9180c038 0x8cc620cda0d0b8b49b182716538306e8621118554d8ba30aa1c2736153310a4e4c2aa70dc58550c429b8ab1b571523118cc2a4621158550d8ba30a998851736155384e4c2a862149c58558e238b1291c572513108cc4a26d5854cc42230aa9b (by decide +kernel)
private def pack_E6970Receipt37_chunk71 := witnessRule 37 49 160 620711 621024 23 1673
  0x7ffffb 0xbd1a (by decide +kernel)
private def pack_E6970Receipt37_chunk72 := witnessRule 37 48 0 630011 630138 32 2798
  0xf0ffc1ff 0x231a8988436353362e4c6a462145c58d50e2322a3635231084c6a86c9c99158b9aa9b (by decide +kernel)
private def pack_E6970Receipt37_chunk73 := witnessRule 37 48 32 630139 630264 32 2705
  0xfc3ff83f 0x2b1a89b1746351082e6c6a4709c98d44c42ab1a88346352362e6c6a262145c98d4ce138b1a91885 (by decide +kernel)
private def pack_E6970Receipt37_chunk74 := witnessRule 37 48 64 630265 630389 32 2631
  0xfc2ffc1f 0x158d44d8bab1ab36255364e6c6a270dc58d48e331aa46352362e8c6a2709cd8d44213931a91c (by decide +kernel)
private def pack_E6970Receipt37_chunk75 := witnessRule 37 48 96 630390 630519 32 2418
  0x4f00fc0b 0x9c98950e1b92a9b5735136cc4a262115894cd8ba312918851736254386e6c6ac9c58954e238b1a89c5735106cc6a958948c422312a1b27463562e4c4aa70dc98d44e239a91b (by decide +kernel)
private def pack_E6970Receipt37_chunk76 := witnessRule 37 48 128 630520 630709 32 2265
  0xb70981e0 0x6c2ae6c605c59ce2b0aa188446156362e6c2aa62145c9855ce138ac1b183715438ac4a66d18554c421b0ab9b2736253386e4c4a46214dc58950e331290366252362eac4a262145d1894ce139b1291885 (by decide +kernel)
private def pack_E6970Receipt37_chunk77 := witnessRule 37 48 160 630710 631024 21 1499
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk78 := witnessRule 37 47 0 640010 640136 32 2754
  0xe2ffc7ff 0xac8a8d9148d8b9b2289c2716452388c8a26c5cd914420b932291c (by decide +kernel)
private def pack_E6970Receipt37_chunk79 := witnessRule 37 47 32 640137 640261 32 2669
  0xf03ff0bf 0xac8a918d48c421b1aa1b27364562e2c6aa70dc59144e232289b17464564c6aa6c9c99144e1ba291b (by decide +kernel)
private def pack_E6970Receipt37_chunk80 := witnessRule 37 47 64 640262 640386 32 2581
  0xe07ff03f 0x6635106ac6a46c5d18d44c428b9b1a99c2726352310a4e2c6a87158d44c42231a99b1736352310a2e4c6a870dc9915939aa9b (by decide +kernel)
private def pack_E6970Receipt37_chunk81 := witnessRule 37 47 96 640387 640517 32 2371
  0xbc0ff03f 0x239a99b6635106ac6a46c5d58d44e13a31a8842736352386e4c6a2621598d44d8bab1a8841746352384e6c6a262149c98d4ce1b8b1a91885 (by decide +kernel)
private def pack_E6970Receipt37_chunk82 := witnessRule 37 47 128 640518 640709 32 2204
  0xff0b03c0 0x2312a9b3615731084c2b26c605c98554e8c138ab1c562523208ac4a86c5d1894cc428b9b12a9c2726254310a4e2c4ac7198944c822b129988446255362e6c4a862145c98958e1b931a91c (by decide +kernel)
private def pack_E6970Receipt37_chunk83 := witnessRule 37 47 160 640710 640961 18 1262
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk84 := witnessRule 37 46 0 650009 650134 32 2706
  0xc3ff83ff 0x23228988436453362e4c8a462145c59150e232aa3645231084c8a86c9c99558ba2a9b (by decide +kernel)
private def pack_E6970Receipt37_chunk85 := witnessRule 37 46 32 650135 650258 32 2621
  0xc3ffc1ff 0x2b2289b1746451082e6c8a4709c99144c42ab2288346452362e6c8a262145c9914ce138b2291885 (by decide +kernel)
private def pack_E6970Receipt37_chunk86 := witnessRule 37 46 64 650259 650384 32 2517
  0x85ff83ff 0x159144d8bab22b36355364e6c8a270dc59148e3322a46452362e8c8a2709cd9144213932291c (by decide +kernel)
private def pack_E6970Receipt37_chunk87 := witnessRule 37 46 96 650385 650516 32 2324
  0xf84fc0bf 0x331a8988456353362e8c6a462145cd8d50e138b1aa9c471645138cc8a958d48c42231aa1b27464562e4c6aa70dc99144e23a291b (by decide +kernel)
private def pack_E6970Receipt37_chunk88 := witnessRule 37 46 128 650517 650709 32 2147
  0xff070380 0x118950c821b12b18841836155310a304c2ae70605c58558c432b12999044625531086c4ae6c5c98958c428b8b12c1c1827162543acc4a80d58d48c42231aa1b1746353384e6c6a462149c98d50e1b8b1a99885 (by decide +kernel)
private def pack_E6970Receipt37_chunk89 := witnessRule 37 46 160 650710 650960 15 1034
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk90 := witnessRule 37 45 0 660008 660132 32 2650
  0x8bff8fff 0xacaa8d9548d8b9b2a89c2716552388caa26c5cd954420b932a91c (by decide +kernel)
private def pack_E6970Receipt37_chunk91 := witnessRule 37 45 32 660133 660210 32 2555
  0x3ff85ff 0xacaa919148c421b22a1b27365562e2c8aa70dc59544e232a89b17465564c8aa6c9c99544e1baa91b (by decide +kernel)
private def pack_E6970Receipt37_chunk92 := witnessRule 37 45 64 660256 660334 32 2507
  0x7fe07ff 0xac8a46c5d19144c428b9b2299c2726452310a4e2c8a87159144c42232299b1736452310a2e4c8a870dc995593a2a9b (by decide +kernel)
private def pack_E6970Receipt37_chunk93 := witnessRule 37 45 96 660335 660515 32 2259
  0xf01f81fe 0x198d4c1ab2291b4635431086c6ac6c9cd9148e1b932289885371645338cc8a26c5d5914420ba32291c2736451310a4e4c8a670dc59148c42b322883 (by decide +kernel)
private def pack_E6970Receipt37_chunk94 := witnessRule 37 45 128 660516 660710 32 2095
  0xffab0182 0x362553308304c2ac641460568dab1291a044635431086c6ac6c60d8954e0c0b9312a18861817162563a304e4aa621558d44cc22b1a9988446355362e6c6a862145c98d58e139ab9b (by decide +kernel)
private def pack_E6970Receipt37_chunk95 := witnessRule 37 45 160 660768 660960 12 815
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk96 := witnessRule 37 44 0 670007 670084 32 2588
  0xfff07ff 0x232a8988436553362e4caa462145c59550e2332a3655231084caa86c9c99958baaa9b (by decide +kernel)
private def pack_E6970Receipt37_chunk97 := witnessRule 37 44 32 670131 670207 32 2578
  0x3ffe0fff 0x2e6caa4709c99544c42ab2a88346552362e6caa262145c9954ce138b2a91885 (by decide +kernel)
private def pack_E6970Receipt37_chunk98 := witnessRule 37 44 64 670208 670332 32 2404
  0x2ff83ffc 0xd9154d939b2a89c371655238ccaa919548d8ba32a89c2736551084e4caa47159544d8ba32a884 (by decide +kernel)
private def pack_E6970Receipt37_chunk99 := witnessRule 37 44 96 670333 670515 32 2172
  0x702f02fc 0xc139aa9c564513208ac8a66c5d19148c428b9b22a1c2726453310a4e2c8aa711d14508e33229035645231088c8a86c5cd914cc428b9322a9c3726551388eaa46d59544d8bab2ab (by decide +kernel)
private def pack_E6970Receipt37_chunk100 := witnessRule 37 44 128 670516 670769 32 2051
  0xffff80c0 0x231a99984363553208306c4a864146098958c428c0b12c1c1817257310a502e2a28a7558d48cc22322a1b3635631084c6b06c605c98d50e8c138b1a99886 (by decide +kernel)
private def pack_E6970Receipt37_chunk101 := witnessRule 37 44 160 670770 670897 8 535
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk102 := witnessRule 37 43 0 680006 680083 32 2568
  0x2fff1fff 0xd9948d8b9b3289c2716652388cca26c5cd994420b933291c (by decide +kernel)
private def pack_E6970Receipt37_chunk103 := witnessRule 37 43 32 680084 680205 32 2558
  0x3ffc2ffe 0x1716555386e2cca27119944d8ba332b26555364e4cca270dd948dab32a (by decide +kernel)
private def pack_E6970Receipt37_chunk104 := witnessRule 37 43 64 680206 680331 32 2307
  0x1ff03ff0 0xb9b2a99c2726552310a4e2caa87159544c42232a99b1736552310a2e4caa870dc999593aaa9b566548caa46210d9550d939b32b (by decide +kernel)
private def pack_E6970Receipt37_chunk105 := witnessRule 37 43 96 680332 680515 32 2089
  0x781f03f8 0x181735738ac8a4641119150c421b22b1b1726455310a2e2c8ae70609c5914ceab2a8988446553362e8caa4709cd9544c4293932a99c3716552310accaa20d59548d8ba32a89885 (by decide +kernel)
private def pack_E6970Receipt37_chunk106 := witnessRule 37 43 128 680516 680771 32 2014
  0xffffe060 0x6c6a8681060d894cd028c1312a99851816257320a304b26210e0554c42232299904364553108306c6a862146098d58e0c0b8b1aa9886 (by decide +kernel)
private def pack_E6970Receipt37_chunk107 := witnessRule 37 43 160 680832 680896 4 265
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk108 := witnessRule 37 42 0 690005 690081 32 2550
  0x3ffe0fff 0x2e4cca462145c59950e233aa3665231084cca86c9c99d58bb2a9b (by decide +kernel)
private def pack_E6970Receipt37_chunk109 := witnessRule 37 42 32 690082 690203 32 2494
  0xfff07ffc 0xacca20d19948d8b9b32898851726653384e2cca4621519944c421b3299b (by decide +kernel)
private def pack_E6970Receipt37_chunk110 := witnessRule 37 42 64 690204 690330 32 2211
  0x5fe0ffe1 0x4e6cca270dc59948e3332a46652362e8cca2709cd9944213933291c56651362e8cca2105cd9948e13933289885 (by decide +kernel)
private def pack_E6970Receipt37_chunk111 := witnessRule 37 42 96 690331 690516 32 2009
  0x180705f8 0x1816357310a306b26ce0954dab2289a044655331086caaa6c60d9150e0c0b9322998861817164553a304e8a8621460dcd4508c472b2a9835655231088caa86c5cd954cc428b932aa9c2755636acca26d1954cc421b2aa9b (by decide +kernel)
private def pack_E6970Receipt37_chunk112 := witnessRule 37 42 128 690517 690896 32 1990
  0xfffff558 0x6c6a66c106098950d428c12c19843814531186c8a8661060d8d4ccc28c131aa9905 (by decide +kernel)
private def pack_E6970Receipt37_chunk113 := witnessRule 37 41 0 700004 700080 32 2534
  0xbffe3fff 0x2716752388cea26c5cd9d4420b933a91c (by decide +kernel)
private def pack_E6970Receipt37_chunk114 := witnessRule 37 41 32 700081 700202 32 2432
  0xffe17ff8 0x46751362e8ceac99954d93933a89c3775236acea8d9d48d8b9b3a89c (by decide +kernel)
private def pack_E6970Receipt37_chunk115 := witnessRule 37 41 64 700203 700330 32 2118
  0x1fe07fc0 0x2e6cca6709c99948c42938b32a1c5665131088cca66c5cd9948c428b9332a1c37267564ecaa6d59d523329188436654364e6ceac5c59954e1b8b3a89c (by decide +kernel)
private def pack_E6970Receipt37_chunk116 := witnessRule 37 41 96 700331 700517 32 1939
  0xe0382f8 0x1826354340a302c6ac661460d60c821c12a19044655233086caa8641060d914cc828c1322a9885181645738302e8ac6214a05cd4510eab2a8998446653366caaa62109955cd8c0b932a99d182755438acca40d59948d8ba33289885 (by decide +kernel)
private def pack_E6970Receipt37_chunk117 := witnessRule 37 41 128 700518 700833 27 1650
  0x7fffffd 0x1b2299a84 (by decide +kernel)
private def pack_E6970Receipt37_chunk118 := witnessRule 37 40 0 710003 710078 32 2518
  0xfffc1fff 0x2342a3675231084cea86c9c9a158bbaa9b (by decide +kernel)
private def pack_E6970Receipt37_chunk119 := witnessRule 37 40 32 710079 710201 32 2324
  0xffc1fff0 0x2b3a88346752362e6cea262145c99d4ce138b3a918854675131086cea66c5c99d48c428b8b3aa1c (by decide +kernel)
private def pack_E6970Receipt37_chunk120 := witnessRule 37 40 64 710202 710330 32 2027
  0xfe0ffc3 0x1b32a9b1726654310a2e2ccac70609c59948eab3a88346752362e8cea2709cd9d44213933a91c56751362e8cea2105cd9d48e13933a89885 (by decide +kernel)
private def pack_E6970Receipt37_chunk121 := witnessRule 37 40 96 710331 710519 32 1879
  0xd1a0e07c 0x6098d4cd828c1ab9a04382533408702a288622218d954cd020c1322a19851816456320a308b06210e0d50c421413928a1190e4665232086cca8621060d954cc428c132aa9c181716554310c302eaac7159944c82233299884 (by decide +kernel)
private def pack_E6970Receipt37_chunk122 := witnessRule 37 40 128 710520 710832 22 1324
  0x3fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk123 := witnessRule 37 39 0 720002 720077 32 2506
  0xfffc7fff 0x8d0a26c5cda14420b934291c (by decide +kernel)
private def pack_E6970Receipt37_chunk124 := witnessRule 37 39 32 720078 720201 32 2218
  0xffc2ffe2 0x234289b17468564ceaa6c9c9a144e1bc291b568546d0a46c5cda144e138b4291c (by decide +kernel)
private def pack_E6970Receipt37_chunk125 := witnessRule 37 39 64 720202 720331 32 1935
  0x3f0bfc0 0x233a918843675436306cca670605c99948c430c0b8b32a1d1827653310aacea2621119d4cd8b9b3a918851726754384eeaa6d5a15233a9188436754364e6d0ac5c59d54e1b8b4289c (by decide +kernel)
private def pack_E6970Receipt37_chunk126 := witnessRule 37 39 96 720332 720577 32 1831
  0xfd7a3a1f 0x306ac6c10e05450cc44c30c132299a85184573308706a66610e094510c469b32999841826554320a302caac621461560d9c22a1b (by decide +kernel)
private def pack_E6970Receipt37_chunk127 := witnessRule 37 39 128 720578 720832 17 1009
  0x1ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk128 := witnessRule 37 38 0 730001 730076 32 2440
  0xfff83fff 0x234aa3685231084d0a86c9c9a558bc2a9b (by decide +kernel)
private def pack_E6970Receipt37_chunk129 := witnessRule 37 38 32 730077 730201 32 2116
  0xffc1ffe1 0x2b4288346852362e6d0a262145c9a14ce138b42918854685131086d0a66c5c9a148c428b8b42a1c (by decide +kernel)
private def pack_E6970Receipt37_chunk130 := witnessRule 37 38 64 730202 730384 32 1863
  0x82f82fe1 0x4675133086cea6641060d9948c828c1332a1885181665638502eaa2867559d4c1a34291b3675431084ceac6c605c99d48e8c13ba99c56851362e8d0a2105cda148e13934289885 (by decide +kernel)
private def pack_E6970Receipt37_chunk131 := witnessRule 37 38 96 730385 730580 32 1785
  0xffffa6a7 0x308ac6a10e09450cc44831c0b8a8a1198e366523508304caa668146155cc821c2299904 (by decide +kernel)
private def pack_E6970Receipt37_chunk132 := witnessRule 37 38 128 730581 730769 11 644
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk133 := witnessRule 37 37 0 740000 740076 32 2380
  0xfff8ffff 0x8d2a26c5cda54420b934a91c (by decide +kernel)
private def pack_E6970Receipt37_chunk134 := witnessRule 37 37 32 740077 740202 32 2012
  0x3fe17fe2 0x2e2d0aa70609c5a144ea34a89b17469564d0aa6c9c9a544e1bca91b569546d2a46c5cda544e138b4a91c (by decide +kernel)
private def pack_E6970Receipt37_chunk135 := witnessRule 37 37 64 740203 740386 32 1796
  0xf53e0ff1 0x367523408304cca666146195cc421c2a998844685132086d0a6621060d9d48c428c133aa1c181716753310cad0a40d1a148c421b42a1b (by decide +kernel)
private def pack_E6970Receipt37_chunk136 := witnessRule 37 37 96 740387 740642 32 1751
  0xfffffdfa 0x704a28462281861558d021c1a8a1988886 (by decide +kernel)
private def pack_E6970Receipt37_chunk137 := witnessRule 37 37 128 740643 740768 5 290
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk138 := witnessRule 37 36 0 750000 750076 32 2262
  0xfff83fff 0x2352a3695231084d2a86c9c9a958bcaa9b (by decide +kernel)
private def pack_E6970Receipt37_chunk139 := witnessRule 37 36 32 750077 750203 32 1913
  0x1ff07ff0 0x183685238302e4d0a26218605c5a14ceab4a88346952362e6d2a262145c9a54ce138b4a918854695131086d2a66c5c9a548c428b8b4aa1c (by decide +kernel)
private def pack_E6970Receipt37_chunk140 := witnessRule 37 36 64 750204 750389 32 1729
  0xdfd7f4fc 0x383514231130c30cac6610e11450cc468c133a99905187573670ca66d1a544c421b4a99b (by decide +kernel)
private def pack_E6970Receipt37_chunk141 := witnessRule 37 36 96 750390 750768 31 1681
  0x7fffffef 0x240a11a0c (by decide +kernel)
private def pack_E6970Receipt37_chunk142 := witnessRule 37 35 0 760000 760077 32 2150
  0xbffc7fff 0x2716a52388d4a26c5cda94420b935291c (by decide +kernel)
private def pack_E6970Receipt37_chunk143 := witnessRule 37 35 32 760078 760205 32 1815
  0x85fc2ff8 0x1b4a919041836851320a304d0a66214605a154e140bba8a11d46a51366d2a662109a554d8c0b934a89d182795238ad4a8da948d8b9b5289c (by decide +kernel)
private def pack_E6970Receipt37_chunk144 := witnessRule 37 35 64 760256 760392 32 1678
  0xffdef57f 0x133a91b84384514231120c6d0a26a106099d48d028c3ab1904 (by decide +kernel)
private def pack_E6970Receipt37_chunk145 := witnessRule 37 35 96 760448 760705 24 1281
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk146 := witnessRule 37 34 0 770000 770077 32 2038
  0x3ffc1fff 0x2e4d4a462145c5a950e235aa36a5231084d4a86c9c9ad58bd2a9b (by decide +kernel)
private def pack_E6970Receipt37_chunk147 := witnessRule 37 34 32 770078 770257 32 1758
  0xf5fe0ffc 0xc1342919851885631088d4a40cda948c420c1b4a89885182695338302e2d2a462191a944c421b5299b (by decide +kernel)
private def pack_E6970Receipt37_chunk148 := witnessRule 37 34 64 770258 770450 32 1605
  0xfffffef7 0x9a148d821c2a8a1188886 (by decide +kernel)
private def pack_E6970Receipt37_chunk149 := witnessRule 37 34 96 770451 770704 18 945
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk150 := witnessRule 37 33 0 780000 780078 32 1928
  0x2ffe3fff 0xdad48d8c1b5289c181716a523a8d6a26c5cdad4420b935a91c (by decide +kernel)
private def pack_E6970Receipt37_chunk151 := witnessRule 37 33 32 780079 780259 32 1688
  0xffdffbfe 0x70ca284623462558da35a883 (by decide +kernel)
private def pack_E6970Receipt37_chunk152 := witnessRule 37 33 64 780260 780454 32 1560
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk153 := witnessRule 37 33 96 780512 780704 12 623
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk154 := witnessRule 37 32 0 790000 790078 32 1823
  0x4ffe0fff 0x36b513208304d4a46214605a950e2362a36b5231084d6a86c605c9ad60bdaa9b (by decide +kernel)
private def pack_E6970Receipt37_chunk155 := witnessRule 37 32 32 790128 790261 32 1615
  0xfd7fe5ff 0x134a89b841816852360a4d4a46810609a544d028c4aa9904 (by decide +kernel)
private def pack_E6970Receipt37_chunk156 := witnessRule 37 32 64 790262 790515 32 1536
  0xfffffff7 0xb4291c84 (by decide +kernel)
private def pack_E6970Receipt37_chunk157 := witnessRule 37 32 96 790516 790641 6 307
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk158 := witnessRule 37 31 0 800000 800128 32 1751
  0xdbff1fff 0x135a9198418a5531086d8a2621060dad4420c135a91c (by decide +kernel)
private def pack_E6970Receipt37_chunk159 := witnessRule 37 31 32 800129 800263 32 1523
  0xffbffdff 0x5a548e020c0b4a91a85 (by decide +kernel)
private def pack_E6970Receipt37_chunk160 := witnessRule 37 31 64 800264 800640 32 1520
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk161 := witnessRule 37 30 0 810000 810129 32 1675
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk162 := witnessRule 37 30 32 810130 810265 32 1445
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk163 := witnessRule 37 30 64 810320 810640 27 1257
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk164 := witnessRule 37 29 0 820000 820130 32 1598
  0xf2ffa7ff 0x5ad48d820c0b5289b052895141340a4d8a26810605ad48cc28c5aa1904 (by decide +kernel)
private def pack_E6970Receipt37_chunk165 := witnessRule 37 29 32 820131 820322 32 1389
  0xfffbfebf 0x12a4760c5a944e420c4a91c04 (by decide +kernel)
private def pack_E6970Receipt37_chunk166 := witnessRule 37 29 64 820323 820577 21 957
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk167 := witnessRule 37 28 0 830000 830131 32 1517
  0xfdffdbff 0x314a46e105b148d4214528a09985 (by decide +kernel)
private def pack_E6970Receipt37_chunk168 := witnessRule 37 28 32 830132 830324 32 1342
  0xffffffbf 0x5291d03 (by decide +kernel)
private def pack_E6970Receipt37_chunk169 := witnessRule 37 28 64 830325 830576 16 715
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk170 := witnessRule 37 27 0 840000 840132 32 1435
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk171 := witnessRule 37 27 32 840133 840384 32 1308
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk172 := witnessRule 37 27 64 840385 840576 11 484
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk173 := witnessRule 37 26 0 850000 850133 32 1359
  0xfd7fe5ff 0x5a89d831895249098a4700c62d44e02144a9208a05 (by decide +kernel)
private def pack_E6970Receipt37_chunk174 := witnessRule 37 26 32 850134 850387 32 1280
  0xfffffff7 0x4a8a09e84 (by decide +kernel)
private def pack_E6970Receipt37_chunk175 := witnessRule 37 26 64 850388 850513 6 259
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk176 := witnessRule 37 25 0 860000 860134 32 1289
  0xff7ffbff 0x294504f020c5292404 (by decide +kernel)
private def pack_E6970Receipt37_chunk177 := witnessRule 37 25 32 860135 860450 32 1258
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk178 := witnessRule 37 25 64 860512 860512 1 43
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk179 := witnessRule 37 24 0 870000 870135 32 1223
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk180 := witnessRule 37 24 32 870136 870512 29 1113
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk181 := witnessRule 37 23 0 880000 880136 32 1166
  0xffdff5ff 0x12a4823a12d453418c4a9209485 (by decide +kernel)
private def pack_E6970Receipt37_chunk182 := witnessRule 37 23 32 880192 880449 24 897
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk183 := witnessRule 37 22 0 890000 890192 32 1113
  0xfffffbff 0x529208e04 (by decide +kernel)
private def pack_E6970Receipt37_chunk184 := witnessRule 37 22 32 890193 890448 20 727
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk185 := witnessRule 37 21 0 900000 900194 32 1066
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk186 := witnessRule 37 21 32 900195 900448 16 567
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk187 := witnessRule 37 20 0 910000 910195 32 1024
  0xfffffdff 0x4a920908e85 (by decide +kernel)
private def pack_E6970Receipt37_chunk188 := witnessRule 37 20 32 910196 910385 12 413
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk189 := witnessRule 37 19 0 920000 920197 32 986
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk190 := witnessRule 37 19 32 920256 920384 8 269
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk191 := witnessRule 37 18 0 930000 930257 32 950
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk192 := witnessRule 37 18 32 930258 930384 5 164
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk193 := witnessRule 37 17 0 940000 940320 32 921
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk194 := witnessRule 37 17 32 940321 940321 1 32
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk195 := witnessRule 37 16 0 950000 950320 30 830
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk196 := witnessRule 37 15 0 960000 960320 27 717
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk197 := witnessRule 37 14 0 970000 970257 24 609
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk198 := witnessRule 37 13 0 980000 980256 21 510
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk199 := witnessRule 37 12 0 990000 990256 19 441
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk200 := witnessRule 37 11 0 1000000 1000193 16 353
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk201 := witnessRule 37 10 0 1010000 1010192 14 293
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk202 := witnessRule 37 9 0 1020000 1020192 12 239
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk203 := witnessRule 37 8 0 1030000 1030129 10 187
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk204 := witnessRule 37 7 0 1040000 1040128 8 141
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk205 := witnessRule 37 6 0 1050000 1050128 7 116
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk206 := witnessRule 37 5 0 1060000 1060065 5 77
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk207 := witnessRule 37 4 0 1070000 1070064 4 57
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk208 := witnessRule 37 3 0 1080000 1080064 3 40
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk209 := witnessRule 37 2 0 1090000 1090001 2 24
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk210 := witnessRule 37 1 0 1100000 1100000 1 11
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt37_chunk211 := witnessRule 37 0 0 1110000 1110000 1 10
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt37_chunks : List (Chunk 37) := [pack_E6970Receipt37_chunk0, pack_E6970Receipt37_chunk1, pack_E6970Receipt37_chunk2, pack_E6970Receipt37_chunk3, pack_E6970Receipt37_chunk4, pack_E6970Receipt37_chunk5, pack_E6970Receipt37_chunk6, pack_E6970Receipt37_chunk7, pack_E6970Receipt37_chunk8, pack_E6970Receipt37_chunk9, pack_E6970Receipt37_chunk10, pack_E6970Receipt37_chunk11, pack_E6970Receipt37_chunk12, pack_E6970Receipt37_chunk13, pack_E6970Receipt37_chunk14, pack_E6970Receipt37_chunk15, pack_E6970Receipt37_chunk16, pack_E6970Receipt37_chunk17, pack_E6970Receipt37_chunk18, pack_E6970Receipt37_chunk19, pack_E6970Receipt37_chunk20, pack_E6970Receipt37_chunk21, pack_E6970Receipt37_chunk22, pack_E6970Receipt37_chunk23, pack_E6970Receipt37_chunk24, pack_E6970Receipt37_chunk25, pack_E6970Receipt37_chunk26, pack_E6970Receipt37_chunk27, pack_E6970Receipt37_chunk28, pack_E6970Receipt37_chunk29, pack_E6970Receipt37_chunk30, pack_E6970Receipt37_chunk31, pack_E6970Receipt37_chunk32, pack_E6970Receipt37_chunk33, pack_E6970Receipt37_chunk34, pack_E6970Receipt37_chunk35, pack_E6970Receipt37_chunk36, pack_E6970Receipt37_chunk37, pack_E6970Receipt37_chunk38, pack_E6970Receipt37_chunk39, pack_E6970Receipt37_chunk40, pack_E6970Receipt37_chunk41, pack_E6970Receipt37_chunk42, pack_E6970Receipt37_chunk43, pack_E6970Receipt37_chunk44, pack_E6970Receipt37_chunk45, pack_E6970Receipt37_chunk46, pack_E6970Receipt37_chunk47, pack_E6970Receipt37_chunk48, pack_E6970Receipt37_chunk49, pack_E6970Receipt37_chunk50, pack_E6970Receipt37_chunk51, pack_E6970Receipt37_chunk52, pack_E6970Receipt37_chunk53, pack_E6970Receipt37_chunk54, pack_E6970Receipt37_chunk55, pack_E6970Receipt37_chunk56, pack_E6970Receipt37_chunk57, pack_E6970Receipt37_chunk58, pack_E6970Receipt37_chunk59, pack_E6970Receipt37_chunk60, pack_E6970Receipt37_chunk61, pack_E6970Receipt37_chunk62, pack_E6970Receipt37_chunk63, pack_E6970Receipt37_chunk64, pack_E6970Receipt37_chunk65, pack_E6970Receipt37_chunk66, pack_E6970Receipt37_chunk67, pack_E6970Receipt37_chunk68, pack_E6970Receipt37_chunk69, pack_E6970Receipt37_chunk70, pack_E6970Receipt37_chunk71, pack_E6970Receipt37_chunk72, pack_E6970Receipt37_chunk73, pack_E6970Receipt37_chunk74, pack_E6970Receipt37_chunk75, pack_E6970Receipt37_chunk76, pack_E6970Receipt37_chunk77, pack_E6970Receipt37_chunk78, pack_E6970Receipt37_chunk79, pack_E6970Receipt37_chunk80, pack_E6970Receipt37_chunk81, pack_E6970Receipt37_chunk82, pack_E6970Receipt37_chunk83, pack_E6970Receipt37_chunk84, pack_E6970Receipt37_chunk85, pack_E6970Receipt37_chunk86, pack_E6970Receipt37_chunk87, pack_E6970Receipt37_chunk88, pack_E6970Receipt37_chunk89, pack_E6970Receipt37_chunk90, pack_E6970Receipt37_chunk91, pack_E6970Receipt37_chunk92, pack_E6970Receipt37_chunk93, pack_E6970Receipt37_chunk94, pack_E6970Receipt37_chunk95, pack_E6970Receipt37_chunk96, pack_E6970Receipt37_chunk97, pack_E6970Receipt37_chunk98, pack_E6970Receipt37_chunk99, pack_E6970Receipt37_chunk100, pack_E6970Receipt37_chunk101, pack_E6970Receipt37_chunk102, pack_E6970Receipt37_chunk103, pack_E6970Receipt37_chunk104, pack_E6970Receipt37_chunk105, pack_E6970Receipt37_chunk106, pack_E6970Receipt37_chunk107, pack_E6970Receipt37_chunk108, pack_E6970Receipt37_chunk109, pack_E6970Receipt37_chunk110, pack_E6970Receipt37_chunk111, pack_E6970Receipt37_chunk112, pack_E6970Receipt37_chunk113, pack_E6970Receipt37_chunk114, pack_E6970Receipt37_chunk115, pack_E6970Receipt37_chunk116, pack_E6970Receipt37_chunk117, pack_E6970Receipt37_chunk118, pack_E6970Receipt37_chunk119, pack_E6970Receipt37_chunk120, pack_E6970Receipt37_chunk121, pack_E6970Receipt37_chunk122, pack_E6970Receipt37_chunk123, pack_E6970Receipt37_chunk124, pack_E6970Receipt37_chunk125, pack_E6970Receipt37_chunk126, pack_E6970Receipt37_chunk127, pack_E6970Receipt37_chunk128, pack_E6970Receipt37_chunk129, pack_E6970Receipt37_chunk130, pack_E6970Receipt37_chunk131, pack_E6970Receipt37_chunk132, pack_E6970Receipt37_chunk133, pack_E6970Receipt37_chunk134, pack_E6970Receipt37_chunk135, pack_E6970Receipt37_chunk136, pack_E6970Receipt37_chunk137, pack_E6970Receipt37_chunk138, pack_E6970Receipt37_chunk139, pack_E6970Receipt37_chunk140, pack_E6970Receipt37_chunk141, pack_E6970Receipt37_chunk142, pack_E6970Receipt37_chunk143, pack_E6970Receipt37_chunk144, pack_E6970Receipt37_chunk145, pack_E6970Receipt37_chunk146, pack_E6970Receipt37_chunk147, pack_E6970Receipt37_chunk148, pack_E6970Receipt37_chunk149, pack_E6970Receipt37_chunk150, pack_E6970Receipt37_chunk151, pack_E6970Receipt37_chunk152, pack_E6970Receipt37_chunk153, pack_E6970Receipt37_chunk154, pack_E6970Receipt37_chunk155, pack_E6970Receipt37_chunk156, pack_E6970Receipt37_chunk157, pack_E6970Receipt37_chunk158, pack_E6970Receipt37_chunk159, pack_E6970Receipt37_chunk160, pack_E6970Receipt37_chunk161, pack_E6970Receipt37_chunk162, pack_E6970Receipt37_chunk163, pack_E6970Receipt37_chunk164, pack_E6970Receipt37_chunk165, pack_E6970Receipt37_chunk166, pack_E6970Receipt37_chunk167, pack_E6970Receipt37_chunk168, pack_E6970Receipt37_chunk169, pack_E6970Receipt37_chunk170, pack_E6970Receipt37_chunk171, pack_E6970Receipt37_chunk172, pack_E6970Receipt37_chunk173, pack_E6970Receipt37_chunk174, pack_E6970Receipt37_chunk175, pack_E6970Receipt37_chunk176, pack_E6970Receipt37_chunk177, pack_E6970Receipt37_chunk178, pack_E6970Receipt37_chunk179, pack_E6970Receipt37_chunk180, pack_E6970Receipt37_chunk181, pack_E6970Receipt37_chunk182, pack_E6970Receipt37_chunk183, pack_E6970Receipt37_chunk184, pack_E6970Receipt37_chunk185, pack_E6970Receipt37_chunk186, pack_E6970Receipt37_chunk187, pack_E6970Receipt37_chunk188, pack_E6970Receipt37_chunk189, pack_E6970Receipt37_chunk190, pack_E6970Receipt37_chunk191, pack_E6970Receipt37_chunk192, pack_E6970Receipt37_chunk193, pack_E6970Receipt37_chunk194, pack_E6970Receipt37_chunk195, pack_E6970Receipt37_chunk196, pack_E6970Receipt37_chunk197, pack_E6970Receipt37_chunk198, pack_E6970Receipt37_chunk199, pack_E6970Receipt37_chunk200, pack_E6970Receipt37_chunk201, pack_E6970Receipt37_chunk202, pack_E6970Receipt37_chunk203, pack_E6970Receipt37_chunk204, pack_E6970Receipt37_chunk205, pack_E6970Receipt37_chunk206, pack_E6970Receipt37_chunk207, pack_E6970Receipt37_chunk208, pack_E6970Receipt37_chunk209, pack_E6970Receipt37_chunk210, pack_E6970Receipt37_chunk211]
def rows37 := rowsFrom pack_E6970Receipt37_chunks
theorem good37 : ∀ r ∈ rows37, good 37 r = true := rowsFrom_good pack_E6970Receipt37_chunks
theorem sorted37 : rows37.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt37_chunks 0 (by decide +kernel)).1
theorem mass37 (i : Fin 61) :
    bandCount 37 (i.val : ℤ) 60 16 ≤ (rows37.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt37_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 37 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt37_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total37 : (rows37.map (price 37)).sum = 408495 :=
  (total_eq pack_E6970Receipt37_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt37

section Pack_E6970Receipt38

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt38_chunk0 := witnessA6966Final 38 60 0 540022 540211 32 3341
  0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk1 := witnessA6966Final 38 60 32 540212 540397 32 3299
  0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk2 := witnessA6966Final 38 60 64 540398 540529 32 3252
  0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk3 := witnessA6966Final 38 60 96 540530 540707 32 3267
  0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk4 := witnessA6966Final 38 60 128 540708 540840 32 3166
  0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk5 := witnessA6966Final 38 60 160 540841 541030 27 2574
  0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk6 := witnessRule 38 59 0 550021 550209 32 3231
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk7 := witnessRule 38 59 32 550210 550393 32 3181
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk8 := witnessRule 38 59 64 550394 550524 32 3173
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk9 := witnessRule 38 59 96 550525 550653 32 3126
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk10 := witnessRule 38 59 128 550654 550836 32 3077
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk11 := witnessRule 38 59 160 550837 551029 29 2672
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk12 := witnessRule 38 58 0 560020 560206 32 3150
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk13 := witnessRule 38 58 32 560207 560339 32 3105
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk14 := witnessRule 38 58 64 560340 560519 32 3100
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk15 := witnessRule 38 58 96 560520 560647 32 3063
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk16 := witnessRule 38 58 128 560648 560779 32 2951
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk17 := witnessRule 38 58 160 560832 561029 32 2873
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk18 := witnessRule 38 57 0 570019 570153 32 3073
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk19 := witnessRule 38 57 32 570205 570336 32 3060
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk20 := witnessRule 38 57 64 570337 570466 32 2989
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk21 := witnessRule 38 57 96 570515 570642 32 3005
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk22 := witnessRule 38 57 128 570643 570775 32 2871
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk23 := witnessRule 38 57 160 570776 571027 32 2784
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk24 := witnessRule 38 57 192 571028 571028 1 86
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk25 := witnessRule 38 56 0 580018 580151 32 3025
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk26 := witnessRule 38 56 32 580152 580332 32 3005
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk27 := witnessRule 38 56 64 580333 580461 32 2936
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk28 := witnessRule 38 56 96 580462 580588 32 2914
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk29 := witnessRule 38 56 128 580589 580771 32 2796
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk30 := witnessRule 38 56 160 580772 581025 32 2708
  0xffefffff 0xb99a (by decide +kernel)
private def pack_E6970Receipt38_chunk31 := witnessRule 38 56 192 581026 581028 3 252
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk32 := witnessRule 38 55 0 590017 590149 32 2987
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk33 := witnessRule 38 55 32 590150 590329 32 2951
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk34 := witnessRule 38 55 64 590330 590457 32 2896
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk35 := witnessRule 38 55 96 590458 590584 32 2836
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk36 := witnessRule 38 55 128 590585 590768 32 2696
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk37 := witnessRule 38 55 160 590769 591024 32 2640
  0xffdfbfff 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt38_chunk38 := witnessRule 38 55 192 591025 591027 3 246
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk39 := witnessRule 38 54 0 600016 600147 32 2959
  0x9ff5febf 0xdccd238a227163368e2885c98cd93a1a (by decide +kernel)
private def pack_E6970Receipt38_chunk40 := witnessRule 38 54 32 600148 600277 32 2852
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk41 := witnessRule 38 54 64 600326 600452 32 2895
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk42 := witnessRule 38 54 96 600453 600579 32 2790
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk43 := witnessRule 38 54 128 600580 600712 32 2618
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk44 := witnessRule 38 54 160 600713 600964 32 2570
  0xffbe7edf 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt38_chunk45 := witnessRule 38 54 192 601024 601027 4 322
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk46 := witnessRule 38 53 0 610015 610145 32 2930
  0xfeabfdff 0x2b0aa364342e2ca6d1c54419329a (by decide +kernel)
private def pack_E6970Receipt38_chunk47 := witnessRule 38 53 32 610146 610274 32 2822
  0xd7feafea 0x27263366e8685cd8cd938b21b47141368c6685c990d93a9a (by decide +kernel)
private def pack_E6970Receipt38_chunk48 := witnessRule 38 53 64 610275 610401 32 2791
  0xfe7ffaff 0x47334ae288dc58cdab8a2 (by decide +kernel)
private def pack_E6970Receipt38_chunk49 := witnessRule 38 53 96 610449 610576 32 2756
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk50 := witnessRule 38 53 128 610577 610710 32 2564
  0xdfffffff 0x1b8b19b (by decide +kernel)
private def pack_E6970Receipt38_chunk51 := witnessRule 38 53 160 610711 610964 32 2503
  0xffbe7cbe 0x2ec685c594d938b21b17264364e4c66cdd0d0b9b19b (by decide +kernel)
private def pack_E6970Receipt38_chunk52 := witnessRule 38 53 192 611024 611026 3 237
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk53 := witnessRule 38 52 0 620014 620143 32 2905
  0xfebfe8ff 0x5d18544213930a8988556151062e6c2a262145c9854ce138b0a91885 (by decide +kernel)
private def pack_E6970Receipt38_chunk54 := witnessRule 38 52 32 620144 620271 32 2790
  0xfff7ffaf 0x6ca6918548d939b0a884 (by decide +kernel)
private def pack_E6970Receipt38_chunk55 := witnessRule 38 52 64 620272 620397 32 2764
  0xaffaafea 0x139321b37534ac6685cd90d938b29b5715106cc2a9190d0b9329b (by decide +kernel)
private def pack_E6970Receipt38_chunk56 := witnessRule 38 52 96 620398 620523 32 2684
  0xebff57fe 0xdc98cda3a1a27363366e2c86d5c504d8ba319b (by decide +kernel)
private def pack_E6970Receipt38_chunk57 := witnessRule 38 52 128 620524 620707 32 2498
  0x3edbfebf 0x6e2c86d1c58cd8ba319b3726336ae6691c58cdb38a2 (by decide +kernel)
private def pack_E6970Receipt38_chunk58 := witnessRule 38 52 160 620708 620963 32 2441
  0xffbcf879 0xbb9a17166364e2ca6c5c994d939321b3716331086ea685cd90d939b19b (by decide +kernel)
private def pack_E6970Receipt38_chunk59 := witnessRule 38 52 192 621024 621026 3 234
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk60 := witnessRule 38 51 0 630013 630141 32 2873
  0xf80fe17f 0x562548c2a46210d8550d939b12b1716155386e2c4a2711c9441a31289b17462564c2aa6c9c98944e1b9291b (by decide +kernel)
private def pack_E6970Receipt38_chunk61 := witnessRule 38 51 32 630142 630268 32 2767
  0x7f40fe03 0xae4a99854418ba30a898851736153384e4c2a462149c58550e238b12b471514138ac2a262111854cd8b9b0a918851726154386e4c4ac9c554da39289b (by decide +kernel)
private def pack_E6970Receipt38_chunk62 := witnessRule 38 51 64 630269 630393 32 2734
  0x3fd43fd0 0x238a99b57244ac2a46c9d1854421b930a898853716153388e2a462115c54518bab0a8842736151310a4e4c2a670dc58548c429b8aa1b (by decide +kernel)
private def pack_E6970Receipt38_chunk63 := witnessRule 38 51 96 630394 630520 32 2595
  0x57aabfea 0x4e4ca6d5c5854423389276154ac8685cd94da3930a8845715131088ca68dcd85442238b0a89885 (by decide +kernel)
private def pack_E6970Receipt38_chunk64 := witnessRule 38 51 128 630521 630706 32 2426
  0x3c87a275 0x37165368e2c86c5d190d93a319b37264368e2c662111d4d338988b17563364e6c86cdc98cc421b8b29b6715106ce24998cd0ba321b (by decide +kernel)
private def pack_E6970Receipt38_chunk65 := witnessRule 38 51 160 630707 631024 32 2386
  0xfffef878 0x17167362e4cc6c9c994d9b8b21884376342e6ca6c9cd90d9b9319884 (by decide +kernel)
private def pack_E6970Receipt38_chunk66 := witnessRule 38 51 192 631025 631025 1 77
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk67 := witnessRule 38 50 0 640012 640139 32 2837
  0xf0ffc1ff 0x2b1289b1746251082e6c4a4709c98944c42ab1288346252362e6c4a262145c9894ce138b1291885 (by decide +kernel)
private def pack_E6970Receipt38_chunk68 := witnessRule 38 50 32 640140 640265 32 2745
  0xfc2ff83f 0x158944d8bab12b36155364e6c4a270dc58948e3312a46252362e8c4a2709cd8944213931291c (by decide +kernel)
private def pack_E6970Receipt38_chunk69 := witnessRule 38 50 64 640266 640389 32 2703
  0xfc03fc0b 0xcc2a262115854cd8ba30a918851736154386e6c4ac9c58554e238b1289c5725106cc4a958548c42230aa1b27462562e4c2aa70dc98944e239291b (by decide +kernel)
private def pack_E6970Receipt38_chunk70 := witnessRule 38 50 96 640390 640517 32 2524
  0x3e81fa03 0x238aa1b672542ecc2a2109d18544c42939b0a99c3726152310a6e2c2a8715c5895ab8a8a09c76151062eac2a262145d1854ce139b0a918852726154388e4c4acdc554dab9289b (by decide +kernel)
private def pack_E6970Receipt38_chunk71 := witnessRule 38 50 128 640518 640704 32 2360
  0x701847a8 0x47531062eac662105d194d939b2188427266366e2ca6210ddcd2b8a99b6633106aca685d190c420b9b31b4726151310a8e2c2a6715c548c42330a91b2756151086e6c2a26214dc9854ce238b0a91885 (by decide +kernel)
private def pack_E6970Receipt38_chunk72 := witnessRule 38 50 160 640705 641025 32 2336
  0xfffff8f0 0x2e4ce6c9c598c4213c1a17366364e6ca6cdc990c421b8b31b (by decide +kernel)
private def pack_E6970Receipt38_chunk73 := witnessRule 38 49 0 650011 650137 32 2793
  0xe07fc2ff 0xac6a918948c421b12a1b27363562e2c4aa70dc58d44e231a89b17463564c4aa6c9c98d44e1b9a91b (by decide +kernel)
private def pack_E6970Receipt38_chunk74 := witnessRule 38 49 32 650138 650262 32 2711
  0xf03ff03f 0x6625106ac4a46c5d18944c428b9b1299c2726252310a4e2c4a87158944c42231299b1736252310a2e4c4a870dc98d59392a9b (by decide +kernel)
private def pack_E6970Receipt38_chunk75 := witnessRule 38 49 64 650263 650386 32 2635
  0xe07ff03f 0x76254ac4a46c5d58944e13a3128842736252386e4c4a2621598944d8bab128841746252384e6c4a262149c9894ce1b8b1291885 (by decide +kernel)
private def pack_E6970Receipt38_chunk76 := witnessRule 38 49 96 650387 650515 32 2476
  0xf02fe07f 0x3b12a661523108ac2a86c9d58958b9b0aa9c3736251388e2c4a47198944d8bb312b46155364e8c4a270dcd894421b931291c (by decide +kernel)
private def pack_E6970Receipt38_chunk77 := witnessRule 38 49 128 650516 650704 32 2296
  0x60180602 0x1bb988356531068ce685cd98c420b9341b3726154388e2c2a662151c554db38990b56154362eac2a6709d18548c42939b0aa1c3726153310a6e2c2aa711c550c422b8a8a11c761513108cc2a66c5d58548c428ba30aa1c2736153310a4e4c2aa711c98944e2b9291b (by decide +kernel)
private def pack_E6970Receipt38_chunk78 := witnessRule 38 49 160 650705 651024 29 2071
  0x1ffffef8 0x17a342e6ce6c9c998c42138b41b (by decide +kernel)
private def pack_E6970Receipt38_chunk79 := witnessRule 38 48 0 660010 660135 32 2745
  0xc3ff83ff 0x2b1a89b1746351082e6c6a4709c98d44c42ab1a88346352362e6c6a262145c98d4ce138b1a91885 (by decide +kernel)
private def pack_E6970Receipt38_chunk80 := witnessRule 38 48 32 660136 660259 32 2661
  0xc2ffc1ff 0x158d44d8bab1ab36255364e6c6a270dc58d48e331aa46352362e8c6a2709cd8d44213931a91c (by decide +kernel)
private def pack_E6970Receipt38_chunk81 := witnessRule 38 48 64 660260 660336 32 2575
  0xff817f 0xcc4a262115894cd8ba312918851736254386e6c6ac9c58954e238b1a89c5735106cc6a958948c422312a1b27463562e4c4aa70dc98d44e239a91b (by decide +kernel)
private def pack_E6970Receipt38_chunk82 := witnessRule 38 48 96 660384 660513 32 2452
  0xc01f007f 0x1d8944d8bb3128841756252384e8c4a262149cd894ce1b931291885371625438ae2c6ad5c94504e3b1288366252362eac4a262145d1894ce139b12918852726254388e4c6acdc954dab9a89b (by decide +kernel)
private def pack_E6970Receipt38_chunk83 := witnessRule 38 48 128 660514 660649 32 2238
  0xe0201c01 0x46156362e8c2aa709cd8550c4293930ab1c3716155310a6e2ae6c611ccc46330a9988456155362e8c2a862145cd8558e13930aa98852716157388e2c4a6715c948c42331291b5615431088c2ac6c9d18948e1b9b12898853726253388e2c4a462151c950db39288b (by decide +kernel)
private def pack_E6970Receipt38_chunk84 := witnessRule 38 48 160 660704 661024 27 1890
  0x7fffffd 0xb8b51b (by decide +kernel)
private def pack_E6970Receipt38_chunk85 := witnessRule 38 47 0 670009 670133 32 2689
  0x81ff85ff 0xac8a918d48c421b1aa1b27364562e2c6aa70dc59144e232289b17464564c6aa6c9c99144e1ba291b (by decide +kernel)
private def pack_E6970Receipt38_chunk86 := witnessRule 38 47 32 670134 670211 32 2595
  0x3ff81ff 0x6635106ac6a46c5d18d44c428b9b1a99c2726352310a4e2c6a87158d44c42231a99b1736352310a2e4c6a870dc9915939aa9b (by decide +kernel)
private def pack_E6970Receipt38_chunk87 := witnessRule 38 47 64 670257 670334 32 2582
  0xffe07ff 0x5d58d44e13a31a8842736352386e4c6a2621598d44d8bab1a8841746352384e6c6a262149c98d4ce1b8b1a91885 (by decide +kernel)
private def pack_E6970Receipt38_chunk88 := witnessRule 38 47 96 670335 670512 32 2351
  0x817e07fc 0xec4a40d98948c422b12a1b1746253310a2e6c4aa70dcd8d44e238b1a91c66351362ecc6ad18954d93a31a89c3736351086e4c6a471d8d52b1a91b (by decide +kernel)
private def pack_E6970Receipt38_chunk89 := witnessRule 38 47 128 670513 670704 32 2180
  0xe1303813 0x5615531088c2ae6c5cd8558c428b930ac1c2715936504ea6d58950da30ab188436158364e6c4a870dc9894cc429b8b12a9c662513208cc4a66c5d58948c428ba312a1c2736253310a4e4c4aa70dc958dab9a91b (by decide +kernel)
private def pack_E6970Receipt38_chunk90 := witnessRule 38 47 160 670705 670961 23 1579
  0x7fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk91 := witnessRule 38 46 0 680008 680085 32 2625
  0xfff07ff 0x2b2289b1746451082e6c8a4709c99144c42ab2288346452362e6c8a262145c9914ce138b2291885 (by decide +kernel)
private def pack_E6970Receipt38_chunk92 := witnessRule 38 46 32 680132 680208 32 2613
  0x2ffe0fff 0x36355364e6c8a270dc59148e3322a46452362e8c8a2709cd9144213932291c (by decide +kernel)
private def pack_E6970Receipt38_chunk93 := witnessRule 38 46 64 680209 680331 32 2521
  0x1ff02ffc 0x37364564e2c6aa711c59144e3322a5635231088c6a86c9d19158b931aa9c3726451388e8a46d59144d8bab22b (by decide +kernel)
private def pack_E6970Receipt38_chunk94 := witnessRule 38 46 96 680332 680460 32 2256
  0x1f807f0 0xcc6a2621158d4cd8bab1a91c2746351310a4e6c6a670dc98d48c429b8b1aa1c7635106cc6a46c5d58d44c428ba31a99c2736352310a4e4c6a8711c99159b9aa9b663513108ac6a66c5d18d48c428b9b1aa1c (by decide +kernel)
private def pack_E6970Receipt38_chunk95 := witnessRule 38 46 128 680512 680704 32 2126
  0xf5a07817 0x4615632084c2b46ca05dcdab129990456255362e8c4a862145cd8958e139312a9885271625738cc4a4641158950c422312b1b1736255310a2e4c4ae70dc98d4ce239aa1b (by decide +kernel)
private def pack_E6970Receipt38_chunk96 := witnessRule 38 46 160 680705 680960 20 1349
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk97 := witnessRule 38 45 0 690007 690084 32 2602
  0x7ff0bff 0x119148c421b22a1b27365562e2c8aa70dc59544e232a89b17465564c8aa6c9c99544e1baa91b (by decide +kernel)
private def pack_E6970Receipt38_chunk98 := witnessRule 38 45 32 690085 690206 32 2592
  0x3ffc0ffe 0x13932291885271645438ac8a262111914cd8b9b22918851726454386e4caac9d154dab2aa (by decide +kernel)
private def pack_E6970Receipt38_chunk99 := witnessRule 38 45 64 690207 690330 32 2419
  0x7fe07ff0 0x6e4c8a2621599144d8bab228841746452384e6c8a262149c9914ce1b8b22918856645106ac8a46c5d19144c428b9b2299c (by decide +kernel)
private def pack_E6970Receipt38_chunk100 := witnessRule 38 45 96 690331 690460 32 2172
  0xf81fe0 0xcc6a60d98d48c422b1aa1b1746353310a2e6c6aa709c98d50c42938b1ab1c471645238cc8a26d58d4cc42231aa9b2746451386e6c8a210dc99148e3b22a56452362eac8a2709d191442139b2291c (by decide +kernel)
private def pack_E6970Receipt38_chunk101 := witnessRule 38 45 128 690512 690706 32 2068
  0xfff8180f 0x2b12a19044625631086c4b06c5c9895cc428b8b12c9c2817161553acc4a2681158d4cc42231aa9b1746354384e6c6a662149c98d54e1b8b1aa1885 (by decide +kernel)
private def pack_E6970Receipt38_chunk102 := witnessRule 38 45 160 690707 690960 16 1064
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk103 := witnessRule 38 44 0 700006 700082 32 2582
  0x3ffe0fff 0x2e6caa4709c99544c42ab2a88346552362e6caa262145c9954ce138b2a91885 (by decide +kernel)
private def pack_E6970Receipt38_chunk104 := witnessRule 38 44 32 700083 700203 32 2570
  0xfff07ffc 0xccaa919548d8ba32a89c2736551084e4caa47159544d8ba32a884 (by decide +kernel)
private def pack_E6970Receipt38_chunk105 := witnessRule 38 44 64 700204 700328 32 2322
  0x7f817fc2 0x238b2a89c66554ac8a4621119150d93a32ab1726455386e4caa2711d548dab2a89b17565566c8aa6c9cd9544e1b8b2a91c (by decide +kernel)
private def pack_E6970Receipt38_chunk106 := witnessRule 38 44 96 700329 700459 32 2095
  0xf02fc0 0x331a8998456453368c6aa6210d8d5cd939b2299c3726452310a6e2c8a8711d14cc42332290366452362eac8a262145d1914ce139b22918852726454386e8aa6d99144c422b2299b1746452310a2e6c8a870dcd955938b22a9c (by decide +kernel)
private def pack_E6970Receipt38_chunk107 := witnessRule 38 44 128 700512 700707 32 2018
  0xfff80c07 0x15894cd022312a99843625732084c4b26210a098554c42940b0ab9c2817156310aac6a4661158d50c42231ab1b1736355310a2e4c6ae709c58d58c42939ac1b (by decide +kernel)
private def pack_E6970Receipt38_chunk108 := witnessRule 38 44 160 700708 700897 12 785
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk109 := witnessRule 38 43 0 710005 710081 32 2562
  0x1ffe17ff 0x27366562e2caaa70dc59944e233289b17466564caaa6c9c99944e1bb291b (by decide +kernel)
private def pack_E6970Receipt38_chunk110 := witnessRule 38 43 32 710082 710202 32 2504
  0xffe07ff8 0x2b2a8988446553362e6caa462145c99550e1b9332b2755536acca919548c421b2aa1b (by decide +kernel)
private def pack_E6970Receipt38_chunk111 := witnessRule 38 43 64 710203 710328 32 2228
  0xff81ff81 0x66551362eacaa2105d19548e139b2a898852726553386e2caa46215995441ab2a91b1746551310a2e6caa6709c99548c42938b2aa1c (by decide +kernel)
private def pack_E6970Receipt38_chunk112 := witnessRule 38 43 96 710329 710512 32 2023
  0xc0b817c0 0x564523208ac8a86c5d1914cc428b9b22a9c2726454310a4e2c8ac7060dcd450ceb322899045645331088c8aa6c5cd9150c428b9322b1c3726552388eaa66d995441ab2a91b1756551384e8caa2109cd9548e1b932a89885 (by decide +kernel)
private def pack_E6970Receipt38_chunk113 := witnessRule 38 43 128 710513 710768 32 1972
  0xffff5501 0x8c4a86a1098960cc2140b0ab19053814636ac6a6661118d54c821b1ab98842635936504c4aa70a05c58950c43140b92b1c (by decide +kernel)
private def pack_E6970Receipt38_chunk114 := witnessRule 38 43 160 710769 710896 7 453
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk115 := witnessRule 38 42 0 720004 720079 32 2545
  0xfffc1fff 0x2b3288346652362e6cca262145c9994ce138b3291885 (by decide +kernel)
private def pack_E6970Receipt38_chunk116 := witnessRule 38 42 32 720080 720200 32 2440
  0xff83fff0 0x3332a46652362e8cca2709cd9944213933291c56651362e8cca2105cd9948e13933289885 (by decide +kernel)
private def pack_E6970Receipt38_chunk117 := witnessRule 38 42 64 720201 720327 32 2137
  0x7f02ff0b 0x238b3289c66654acaa4621119550d93a332b1726555386e4cca2711d948dab3289b17566566caaa6c9cd9944e1b8b3291c (by decide +kernel)
private def pack_E6970Receipt38_chunk118 := witnessRule 38 42 96 720328 720513 32 1951
  0xc0380fc2 0x564513408ac8a6641119154c421b22b9b1726456310a2e2c8b070a05c58d50e94139a998856645406acaa4621119550d8ba32a99c2736552310a4e4caa870dc5954cc42b32a8988456553362e8caa462145cd9550e138b2aa9c (by decide +kernel)
private def pack_E6970Receipt38_chunk119 := witnessRule 38 42 128 720514 720771 32 1942
  0xffffffc0 0x118d50d021b1ab1984263583208504c4a86414a058958c429412c1b (by decide +kernel)
private def pack_E6970Receipt38_chunk120 := witnessRule 38 42 160 720832 720896 3 193
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk121 := witnessRule 38 41 0 730003 730078 32 2529
  0x7ffc2fff 0xdc59d44e233a89b17467564ccaa6c9c99d44e1bba91b (by decide +kernel)
private def pack_E6970Receipt38_chunk122 := witnessRule 38 41 32 730079 730200 32 2332
  0xff81ffe0 0xacca262111994cd8b9b32918851726654386e4ceac9d954dab3aa4665231086cca86c9cd9d58b8b32a9c (by decide +kernel)
private def pack_E6970Receipt38_chunk123 := witnessRule 38 41 64 730201 730328 32 2045
  0x3f81ff03 0xdc99944c429b8b3299c66651362eacca2105d19948e139b32898852726653386e2cca46215999441ab3291b1746651310a2e6cca6709c99948c42938b32a1c (by decide +kernel)
private def pack_E6970Receipt38_chunk124 := witnessRule 38 41 96 730329 730515 32 1882
  0x180609e0 0x502c4aa6614a095cc821c0a8a298855645234088c8a86610d9158c821322c18842826354310a502c6ac70a05cd54c429413928a1988e565513308acaa6621119554d8b9b2aa18851726556384eaae6ca09d14ce332a98356652368caa86210d9558d939b3291c (by decide +kernel)
private def pack_E6970Receipt38_chunk125 := witnessRule 38 41 128 730516 730833 29 1739
  0x1ffffff4 0x8c6a66c1098d5cd0214131299a05 (by decide +kernel)
private def pack_E6970Receipt38_chunk126 := witnessRule 38 40 0 740002 740076 32 2514
  0xfff83fff 0x2b3a88346752362e6cea262145c99d4ce138b3a91885 (by decide +kernel)
private def pack_E6970Receipt38_chunk127 := witnessRule 38 40 32 740077 740199 32 2227
  0xff07ffc3 0x333aa46752362e8cea2709cd9d44213933a91c56751362e8cea2105cd9d48e13933a89885 (by decide +kernel)
private def pack_E6970Receipt38_chunk128 := witnessRule 38 40 64 740200 740328 32 1959
  0x2f817f0b 0x4e4cca662149c59954e0c1baa8a11d6665206acca4621119950d8b9b32998851726655386e4cea2711dd48dab3a89b17567566ccaa6c9cd9d44e1b8b3a91c (by decide +kernel)
private def pack_E6970Receipt38_chunk129 := witnessRule 38 40 96 740329 740517 32 1823
  0x568380f0 0x263563608502c4a86a14e054510cc2a32299a84264573308504c6a66614a058d54c82941ab9884382514538acaa4661119550c821b2ab18842655836504c8a870a05c5914cc43140ba2a9c566513208acca66c5d19948c428b9b32a1c (by decide +kernel)
private def pack_E6970Receipt38_chunk130 := witnessRule 38 40 128 740518 740832 24 1416
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk131 := witnessRule 38 39 0 750001 750076 32 2448
  0xfff85fff 0x234289b17468564ceaa6c9c9a144e1bc291b (by decide +kernel)
private def pack_E6970Receipt38_chunk132 := witnessRule 38 39 32 750077 750200 32 2126
  0xff81ffc0 0x5675131088cea66c5cd9d48c428b933aa1c37268564eeaa6d5a15233a9188436754364e6d0ac5c59d54e1b8b4289c (by decide +kernel)
private def pack_E6970Receipt38_chunk133 := witnessRule 38 39 64 750201 750330 32 1867
  0x7e07f81 0x2332a188436656362e4ccaa62145c5995ce140b8b2a99d5675131088cea66c5d19d48e139b3a898852726753386e2cea4621599d441ab3a91b1746751310a2e6cea6709c99d48c42938b3aa1c (by decide +kernel)
private def pack_E6970Receipt38_chunk134 := witnessRule 38 39 96 750331 750576 32 1783
  0xfff4341e 0x264563508502c6a86814a0d58cc21c128a21905381715143321c8caa668109955cc82141322999052816455310a508ae6ce05cd4cc46ab3291904 (by decide +kernel)
private def pack_E6970Receipt38_chunk135 := witnessRule 38 39 128 750577 750832 18 1049
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk136 := witnessRule 38 38 0 760000 760075 32 2386
  0xfff07fff 0x2b4288346852362e6d0a262145c9a14ce138b4291885 (by decide +kernel)
private def pack_E6970Receipt38_chunk137 := witnessRule 38 38 32 760076 760200 32 2026
  0xff83ffc3 0x3342a46852362e8d0a2709cda144213934291c56851362e8d0a2105cda148e13934289885 (by decide +kernel)
private def pack_E6970Receipt38_chunk138 := witnessRule 38 38 64 760201 760331 32 1787
  0xf05fc2 0xacca268111994ccc21b32a9904266573108504caa66214a059554e140baaa1885282745142311cacea60d59d48c42233aa1b1736753310a2e4ceaa709dd58dab4289b4675331086ceaa6c9cda144e1b8b4291c (by decide +kernel)
private def pack_E6970Receipt38_chunk139 := witnessRule 38 38 96 760384 760579 32 1750
  0xffff4d47 0x2816353360a704a28668152054cc8442a32a91b04265563408502c8a86614a1158c821c1a8a21885 (by decide +kernel)
private def pack_E6970Receipt38_chunk140 := witnessRule 38 38 128 760580 760769 12 689
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk141 := witnessRule 38 37 0 770000 770076 32 2269
  0x7ff85fff 0xdc5a544e234a89b17469564d0aa6c9c9a544e1bca91b (by decide +kernel)
private def pack_E6970Receipt38_chunk142 := witnessRule 38 37 32 770077 770202 32 1926
  0x3fe07fe0 0x13934291885271685438ad0a262111a14cd8b9b42918851726854386e4d2ac9e154dab4aa4685231086d0a86c9cda558b8b42a9c (by decide +kernel)
private def pack_E6970Receipt38_chunk143 := witnessRule 38 37 64 770203 770386 32 1727
  0x751e0bf0 0x4825332188cca46a1099958cc2140b2aa1905285563108708a2887159d44cc2233a999043675531084ceae6ca09994ce140bb2a1c5685206ad0a46c5d1a144c428b9b4299c (by decide +kernel)
private def pack_E6970Receipt38_chunk144 := witnessRule 38 37 96 770387 770642 32 1717
  0xfffffd7a 0x3825142360a902866630a05914cd429c1a8a19985 (by decide +kernel)
private def pack_E6970Receipt38_chunk145 := witnessRule 38 37 128 770643 770768 5 285
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk146 := witnessRule 38 36 0 780000 780076 32 2157
  0xfff83fff 0x2b4a88346952362e6d2a262145c9a54ce138b4a91885 (by decide +kernel)
private def pack_E6970Receipt38_chunk147 := witnessRule 38 36 32 780077 780203 32 1828
  0xff07ff0 0x1b42a9b1726854310a2e2d0ac70a05c59d48eab4a88346952362e8d2a2709cda544213934a91c56951362e8d2a2105cda548e13934a89885 (by decide +kernel)
private def pack_E6970Receipt38_chunk148 := witnessRule 38 36 64 780204 780389 32 1670
  0xdfd3f4fc 0x1c1a8a11a852816553340a708a2866414e05cd4508c87133ab19042816654310a50cac6d5a144c82234299884 (by decide +kernel)
private def pack_E6970Receipt38_chunk149 := witnessRule 38 36 96 780390 780768 31 1650
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk150 := witnessRule 38 35 0 790000 790077 32 2046
  0x1ffc2fff 0x2736a562e2d2aa70dc5a944e235289b1746a564d2aa6c9c9a944e1bd291b (by decide +kernel)
private def pack_E6970Receipt38_chunk151 := witnessRule 38 35 32 790078 790205 32 1736
  0x81fc2ff8 0x11a148cc21b42a1904268563108504cea46214a059d50e140bba998855695131088d2a66c5cda548c428b934aa1c2795536ad4a91a548c421b4aa1b (by decide +kernel)
private def pack_E6970Receipt38_chunk152 := witnessRule 38 35 64 790256 790392 32 1623
  0xfedef55f 0x902a284662218d9948e021c228a11a054675136084ceaa6810a05994ccc29c2a8a19885 (by decide +kernel)
private def pack_E6970Receipt38_chunk153 := witnessRule 38 35 96 790448 790705 24 1257
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk154 := witnessRule 38 34 0 800000 800077 32 1938
  0x3ffc1fff 0x2e6d4a4709c9a944c42ab5288346a52362e6d4a262145c9a94ce138b5291885 (by decide +kernel)
private def pack_E6970Receipt38_chunk155 := witnessRule 38 34 32 800078 800257 32 1677
  0xf57e0bfc 0x4d0aa6610a059d4cc829c328a19c56953068d2a46410da550c42134ab1b282685238502f0a6715a944d8ba352884 (by decide +kernel)
private def pack_E6970Receipt38_chunk156 := witnessRule 38 34 64 800258 800450 32 1559
  0xffffeef7 0x904a2846634d9d48dc21c2a8a11985 (by decide +kernel)
private def pack_E6970Receipt38_chunk157 := witnessRule 38 34 96 800451 800704 18 927
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk158 := witnessRule 38 33 0 810000 810078 32 1831
  0x27fe17ff 0x23529188436a54362e2d4aa70a05c5a544ea35a89b1746b564d4aa6c9c9ad44e1bda91b (by decide +kernel)
private def pack_E6970Receipt38_chunk159 := witnessRule 38 33 32 810079 810259 32 1611
  0xffdffbfe 0x70ca2846414a05a14cc42ab52903 (by decide +kernel)
private def pack_E6970Receipt38_chunk160 := witnessRule 38 33 64 810260 810454 32 1524
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk161 := witnessRule 38 33 96 810512 810704 12 611
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk162 := witnessRule 38 32 0 820000 820078 32 1730
  0x47fe0fff 0x23528998426a553108504d2a26214a05a54ce2b5a88346b52362e6d6a262145c9ad4ce138b5a91885 (by decide +kernel)
private def pack_E6970Receipt38_chunk163 := witnessRule 38 32 32 820128 820261 32 1543
  0xfd7fe57f 0xda144e020b42a9b043695235084d2a86810a05a148cc29c3a8a11885 (by decide +kernel)
private def pack_E6970Receipt38_chunk164 := witnessRule 38 32 64 820262 820515 32 1501
  0xfffffff7 0x133a91d04 (by decide +kernel)
private def pack_E6970Receipt38_chunk165 := witnessRule 38 32 96 820516 820641 6 301
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk166 := witnessRule 38 31 0 830000 830128 32 1659
  0xdaff0bff 0x36a523408502d2a46414e214508e235a8990436b5331084d6aa6ca09a944e140bd291c (by decide +kernel)
private def pack_E6970Receipt38_chunk167 := witnessRule 38 31 32 830129 830263 32 1459
  0xffbffdff 0x9a148e420b4aa9a84 (by decide +kernel)
private def pack_E6970Receipt38_chunk168 := witnessRule 38 31 64 830264 830640 32 1486
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk169 := witnessRule 38 30 0 840000 840129 32 1586
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk170 := witnessRule 38 30 32 840130 840265 32 1392
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk171 := witnessRule 38 30 64 840320 840640 27 1230
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk172 := witnessRule 38 29 0 850000 850130 32 1511
  0xf2ffa5ff 0x4d4a46e105a950d82144a91a8436b5135082d6aa6610a05a944cc29c4a8a09885 (by decide +kernel)
private def pack_E6970Receipt38_chunk173 := witnessRule 38 29 32 850131 850322 32 1342
  0xfffbfebf 0x2d0a478109a544e824aa9c03 (by decide +kernel)
private def pack_E6970Receipt38_chunk174 := witnessRule 38 29 64 850323 850577 21 936
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk175 := witnessRule 38 28 0 860000 860131 32 1433
  0xfdffdbff 0x14aa6e0c9ad48d82145291a04 (by decide +kernel)
private def pack_E6970Receipt38_chunk176 := witnessRule 38 28 32 860132 860324 32 1300
  0xffffffbf 0xb4a91d84 (by decide +kernel)
private def pack_E6970Receipt38_chunk177 := witnessRule 38 28 64 860325 860576 16 699
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk178 := witnessRule 38 27 0 870000 870132 32 1358
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk179 := witnessRule 38 27 32 870133 870384 32 1272
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk180 := witnessRule 38 27 64 870385 870576 11 473
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk181 := witnessRule 38 26 0 880000 880133 32 1287
  0xfd7fe5ff 0xb5289e0418951413a0a2d6a47212d50e01944a92304 (by decide +kernel)
private def pack_E6970Receipt38_chunk182 := witnessRule 38 26 32 880134 880387 32 1245
  0xfffffff7 0x4a91f03 (by decide +kernel)
private def pack_E6970Receipt38_chunk183 := witnessRule 38 26 64 880388 880513 6 253
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk184 := witnessRule 38 25 0 890000 890134 32 1222
  0xff7ffbff 0x2948f418c528a09c85 (by decide +kernel)
private def pack_E6970Receipt38_chunk185 := witnessRule 38 25 32 890135 890450 32 1224
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk186 := witnessRule 38 25 64 890512 890512 1 42
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk187 := witnessRule 38 24 0 900000 900135 32 1164
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk188 := witnessRule 38 24 32 900136 900512 29 1084
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk189 := witnessRule 38 23 0 910000 910136 32 1111
  0xffdff5ff 0x12a49e0ed44f818c4a9208d05 (by decide +kernel)
private def pack_E6970Receipt38_chunk190 := witnessRule 38 23 32 910192 910449 24 873
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk191 := witnessRule 38 22 0 920000 920192 32 1062
  0xfffffbff 0x5292703 (by decide +kernel)
private def pack_E6970Receipt38_chunk192 := witnessRule 38 22 32 920193 920448 20 707
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk193 := witnessRule 38 21 0 930000 930194 32 1022
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk194 := witnessRule 38 21 32 930195 930448 16 551
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk195 := witnessRule 38 20 0 940000 940195 32 982
  0xfffffdff 0x4a9209784 (by decide +kernel)
private def pack_E6970Receipt38_chunk196 := witnessRule 38 20 32 940196 940385 12 401
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk197 := witnessRule 38 19 0 950000 950197 32 946
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk198 := witnessRule 38 19 32 950256 950384 8 261
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk199 := witnessRule 38 18 0 960000 960257 32 914
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk200 := witnessRule 38 18 32 960258 960384 5 159
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk201 := witnessRule 38 17 0 970000 970320 32 886
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk202 := witnessRule 38 17 32 970321 970321 1 31
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk203 := witnessRule 38 16 0 980000 980320 30 798
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk204 := witnessRule 38 15 0 990000 990320 27 690
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk205 := witnessRule 38 14 0 1000000 1000257 24 585
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk206 := witnessRule 38 13 0 1010000 1010256 21 489
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk207 := witnessRule 38 12 0 1020000 1020256 19 422
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk208 := witnessRule 38 11 0 1030000 1030193 16 337
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk209 := witnessRule 38 10 0 1040000 1040192 14 279
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk210 := witnessRule 38 9 0 1050000 1050192 12 227
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk211 := witnessRule 38 8 0 1060000 1060129 10 177
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk212 := witnessRule 38 7 0 1070000 1070128 8 133
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk213 := witnessRule 38 6 0 1080000 1080128 7 109
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk214 := witnessRule 38 5 0 1090000 1090065 5 72
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk215 := witnessRule 38 4 0 1100000 1100064 4 53
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk216 := witnessRule 38 3 0 1110000 1110064 3 37
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk217 := witnessRule 38 2 0 1120000 1120001 2 22
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk218 := witnessRule 38 1 0 1130000 1130000 1 10
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt38_chunk219 := witnessRule 38 0 0 1140000 1140000 1 9
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt38_chunks : List (Chunk 38) := [pack_E6970Receipt38_chunk0, pack_E6970Receipt38_chunk1, pack_E6970Receipt38_chunk2, pack_E6970Receipt38_chunk3, pack_E6970Receipt38_chunk4, pack_E6970Receipt38_chunk5, pack_E6970Receipt38_chunk6, pack_E6970Receipt38_chunk7, pack_E6970Receipt38_chunk8, pack_E6970Receipt38_chunk9, pack_E6970Receipt38_chunk10, pack_E6970Receipt38_chunk11, pack_E6970Receipt38_chunk12, pack_E6970Receipt38_chunk13, pack_E6970Receipt38_chunk14, pack_E6970Receipt38_chunk15, pack_E6970Receipt38_chunk16, pack_E6970Receipt38_chunk17, pack_E6970Receipt38_chunk18, pack_E6970Receipt38_chunk19, pack_E6970Receipt38_chunk20, pack_E6970Receipt38_chunk21, pack_E6970Receipt38_chunk22, pack_E6970Receipt38_chunk23, pack_E6970Receipt38_chunk24, pack_E6970Receipt38_chunk25, pack_E6970Receipt38_chunk26, pack_E6970Receipt38_chunk27, pack_E6970Receipt38_chunk28, pack_E6970Receipt38_chunk29, pack_E6970Receipt38_chunk30, pack_E6970Receipt38_chunk31, pack_E6970Receipt38_chunk32, pack_E6970Receipt38_chunk33, pack_E6970Receipt38_chunk34, pack_E6970Receipt38_chunk35, pack_E6970Receipt38_chunk36, pack_E6970Receipt38_chunk37, pack_E6970Receipt38_chunk38, pack_E6970Receipt38_chunk39, pack_E6970Receipt38_chunk40, pack_E6970Receipt38_chunk41, pack_E6970Receipt38_chunk42, pack_E6970Receipt38_chunk43, pack_E6970Receipt38_chunk44, pack_E6970Receipt38_chunk45, pack_E6970Receipt38_chunk46, pack_E6970Receipt38_chunk47, pack_E6970Receipt38_chunk48, pack_E6970Receipt38_chunk49, pack_E6970Receipt38_chunk50, pack_E6970Receipt38_chunk51, pack_E6970Receipt38_chunk52, pack_E6970Receipt38_chunk53, pack_E6970Receipt38_chunk54, pack_E6970Receipt38_chunk55, pack_E6970Receipt38_chunk56, pack_E6970Receipt38_chunk57, pack_E6970Receipt38_chunk58, pack_E6970Receipt38_chunk59, pack_E6970Receipt38_chunk60, pack_E6970Receipt38_chunk61, pack_E6970Receipt38_chunk62, pack_E6970Receipt38_chunk63, pack_E6970Receipt38_chunk64, pack_E6970Receipt38_chunk65, pack_E6970Receipt38_chunk66, pack_E6970Receipt38_chunk67, pack_E6970Receipt38_chunk68, pack_E6970Receipt38_chunk69, pack_E6970Receipt38_chunk70, pack_E6970Receipt38_chunk71, pack_E6970Receipt38_chunk72, pack_E6970Receipt38_chunk73, pack_E6970Receipt38_chunk74, pack_E6970Receipt38_chunk75, pack_E6970Receipt38_chunk76, pack_E6970Receipt38_chunk77, pack_E6970Receipt38_chunk78, pack_E6970Receipt38_chunk79, pack_E6970Receipt38_chunk80, pack_E6970Receipt38_chunk81, pack_E6970Receipt38_chunk82, pack_E6970Receipt38_chunk83, pack_E6970Receipt38_chunk84, pack_E6970Receipt38_chunk85, pack_E6970Receipt38_chunk86, pack_E6970Receipt38_chunk87, pack_E6970Receipt38_chunk88, pack_E6970Receipt38_chunk89, pack_E6970Receipt38_chunk90, pack_E6970Receipt38_chunk91, pack_E6970Receipt38_chunk92, pack_E6970Receipt38_chunk93, pack_E6970Receipt38_chunk94, pack_E6970Receipt38_chunk95, pack_E6970Receipt38_chunk96, pack_E6970Receipt38_chunk97, pack_E6970Receipt38_chunk98, pack_E6970Receipt38_chunk99, pack_E6970Receipt38_chunk100, pack_E6970Receipt38_chunk101, pack_E6970Receipt38_chunk102, pack_E6970Receipt38_chunk103, pack_E6970Receipt38_chunk104, pack_E6970Receipt38_chunk105, pack_E6970Receipt38_chunk106, pack_E6970Receipt38_chunk107, pack_E6970Receipt38_chunk108, pack_E6970Receipt38_chunk109, pack_E6970Receipt38_chunk110, pack_E6970Receipt38_chunk111, pack_E6970Receipt38_chunk112, pack_E6970Receipt38_chunk113, pack_E6970Receipt38_chunk114, pack_E6970Receipt38_chunk115, pack_E6970Receipt38_chunk116, pack_E6970Receipt38_chunk117, pack_E6970Receipt38_chunk118, pack_E6970Receipt38_chunk119, pack_E6970Receipt38_chunk120, pack_E6970Receipt38_chunk121, pack_E6970Receipt38_chunk122, pack_E6970Receipt38_chunk123, pack_E6970Receipt38_chunk124, pack_E6970Receipt38_chunk125, pack_E6970Receipt38_chunk126, pack_E6970Receipt38_chunk127, pack_E6970Receipt38_chunk128, pack_E6970Receipt38_chunk129, pack_E6970Receipt38_chunk130, pack_E6970Receipt38_chunk131, pack_E6970Receipt38_chunk132, pack_E6970Receipt38_chunk133, pack_E6970Receipt38_chunk134, pack_E6970Receipt38_chunk135, pack_E6970Receipt38_chunk136, pack_E6970Receipt38_chunk137, pack_E6970Receipt38_chunk138, pack_E6970Receipt38_chunk139, pack_E6970Receipt38_chunk140, pack_E6970Receipt38_chunk141, pack_E6970Receipt38_chunk142, pack_E6970Receipt38_chunk143, pack_E6970Receipt38_chunk144, pack_E6970Receipt38_chunk145, pack_E6970Receipt38_chunk146, pack_E6970Receipt38_chunk147, pack_E6970Receipt38_chunk148, pack_E6970Receipt38_chunk149, pack_E6970Receipt38_chunk150, pack_E6970Receipt38_chunk151, pack_E6970Receipt38_chunk152, pack_E6970Receipt38_chunk153, pack_E6970Receipt38_chunk154, pack_E6970Receipt38_chunk155, pack_E6970Receipt38_chunk156, pack_E6970Receipt38_chunk157, pack_E6970Receipt38_chunk158, pack_E6970Receipt38_chunk159, pack_E6970Receipt38_chunk160, pack_E6970Receipt38_chunk161, pack_E6970Receipt38_chunk162, pack_E6970Receipt38_chunk163, pack_E6970Receipt38_chunk164, pack_E6970Receipt38_chunk165, pack_E6970Receipt38_chunk166, pack_E6970Receipt38_chunk167, pack_E6970Receipt38_chunk168, pack_E6970Receipt38_chunk169, pack_E6970Receipt38_chunk170, pack_E6970Receipt38_chunk171, pack_E6970Receipt38_chunk172, pack_E6970Receipt38_chunk173, pack_E6970Receipt38_chunk174, pack_E6970Receipt38_chunk175, pack_E6970Receipt38_chunk176, pack_E6970Receipt38_chunk177, pack_E6970Receipt38_chunk178, pack_E6970Receipt38_chunk179, pack_E6970Receipt38_chunk180, pack_E6970Receipt38_chunk181, pack_E6970Receipt38_chunk182, pack_E6970Receipt38_chunk183, pack_E6970Receipt38_chunk184, pack_E6970Receipt38_chunk185, pack_E6970Receipt38_chunk186, pack_E6970Receipt38_chunk187, pack_E6970Receipt38_chunk188, pack_E6970Receipt38_chunk189, pack_E6970Receipt38_chunk190, pack_E6970Receipt38_chunk191, pack_E6970Receipt38_chunk192, pack_E6970Receipt38_chunk193, pack_E6970Receipt38_chunk194, pack_E6970Receipt38_chunk195, pack_E6970Receipt38_chunk196, pack_E6970Receipt38_chunk197, pack_E6970Receipt38_chunk198, pack_E6970Receipt38_chunk199, pack_E6970Receipt38_chunk200, pack_E6970Receipt38_chunk201, pack_E6970Receipt38_chunk202, pack_E6970Receipt38_chunk203, pack_E6970Receipt38_chunk204, pack_E6970Receipt38_chunk205, pack_E6970Receipt38_chunk206, pack_E6970Receipt38_chunk207, pack_E6970Receipt38_chunk208, pack_E6970Receipt38_chunk209, pack_E6970Receipt38_chunk210, pack_E6970Receipt38_chunk211, pack_E6970Receipt38_chunk212, pack_E6970Receipt38_chunk213, pack_E6970Receipt38_chunk214, pack_E6970Receipt38_chunk215, pack_E6970Receipt38_chunk216, pack_E6970Receipt38_chunk217, pack_E6970Receipt38_chunk218, pack_E6970Receipt38_chunk219]
def rows38 := rowsFrom pack_E6970Receipt38_chunks
theorem good38 : ∀ r ∈ rows38, good 38 r = true := rowsFrom_good pack_E6970Receipt38_chunks
theorem sorted38 : rows38.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt38_chunks 0 (by decide +kernel)).1
theorem mass38 (i : Fin 61) :
    bandCount 38 (i.val : ℤ) 60 16 ≤ (rows38.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt38_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 38 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt38_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total38 : (rows38.map (price 38)).sum = 412926 :=
  (total_eq pack_E6970Receipt38_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt38

section Pack_E6970Receipt39

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt39_chunk0 := witnessA6966Final 39 60 0 570021 570207 32 3348
  0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk1 := witnessA6966Final 39 60 32 570208 570340 32 3315
  0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk2 := witnessA6966Final 39 60 64 570341 570520 32 3301
  0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk3 := witnessA6966Final 39 60 96 570521 570648 32 3265
  0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk4 := witnessA6966Final 39 60 128 570649 570778 32 3175
  0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk5 := witnessA6966Final 39 60 160 570779 571024 32 3060
  0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk6 := witnessRule 39 60 192 571025 571030 6 555
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk7 := witnessRule 39 59 0 580020 580154 32 3213
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk8 := witnessRule 39 59 32 580206 580337 32 3207
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk9 := witnessRule 39 59 64 580338 580467 32 3138
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk10 := witnessRule 39 59 96 580516 580642 32 3168
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk11 := witnessRule 39 59 128 580643 580773 32 3072
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk12 := witnessRule 39 59 160 580774 580965 32 2953
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk13 := witnessRule 39 59 192 580966 581029 8 720
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk14 := witnessRule 39 58 0 590019 590152 32 3138
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk15 := witnessRule 39 58 32 590153 590333 32 3121
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk16 := witnessRule 39 58 64 590334 590462 32 3071
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk17 := witnessRule 39 58 96 590463 590589 32 3047
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk18 := witnessRule 39 58 128 590590 590769 32 2974
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk19 := witnessRule 39 58 160 590770 590962 32 2866
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk20 := witnessRule 39 58 192 590963 591029 10 875
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk21 := witnessRule 39 57 0 600018 600150 32 3076
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk22 := witnessRule 39 57 32 600151 600330 32 3050
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk23 := witnessRule 39 57 64 600331 600458 32 3006
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk24 := witnessRule 39 57 96 600459 600584 32 2981
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk25 := witnessRule 39 57 128 600585 600714 32 2859
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk26 := witnessRule 39 57 160 600715 600960 32 2778
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk27 := witnessRule 39 57 192 600961 601028 11 939
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk28 := witnessRule 39 56 0 610017 610148 32 3025
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk29 := witnessRule 39 56 32 610149 610278 32 2942
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk30 := witnessRule 39 56 64 610327 610453 32 2982
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk31 := witnessRule 39 56 96 610454 610579 32 2899
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk32 := witnessRule 39 56 128 610580 610710 32 2775
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk33 := witnessRule 39 56 160 610711 610902 32 2690
  0xdfffffff 0xb99a (by decide +kernel)
private def pack_E6970Receipt39_chunk34 := witnessRule 39 56 192 610903 611028 12 999
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk35 := witnessRule 39 55 0 620016 620146 32 2984
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk36 := witnessRule 39 55 32 620147 620275 32 2892
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk37 := witnessRule 39 55 64 620276 620402 32 2869
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk38 := witnessRule 39 55 96 620450 620527 32 2855
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk39 := witnessRule 39 55 128 620576 620707 32 2715
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk40 := witnessRule 39 55 160 620708 620900 32 2616
  0xbf7fffff 0x5d0d0b8b19b (by decide +kernel)
private def pack_E6970Receipt39_chunk41 := witnessRule 39 55 192 620901 621027 12 972
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk42 := witnessRule 39 54 0 630015 630144 32 2953
  0xffffff9f 0xdccd238a2 (by decide +kernel)
private def pack_E6970Receipt39_chunk43 := witnessRule 39 54 32 630145 630272 32 2849
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk44 := witnessRule 39 54 64 630273 630398 32 2826
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk45 := witnessRule 39 54 96 630399 630523 32 2777
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk46 := witnessRule 39 54 128 630524 630704 32 2613
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk47 := witnessRule 39 54 160 630705 630899 32 2548
  0xbe7edfff 0xba9a17164364e2c66c5c98cd9b99a (by decide +kernel)
private def pack_E6970Receipt39_chunk48 := witnessRule 39 54 192 630900 631027 12 950
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk49 := witnessRule 39 53 0 640014 640142 32 2923
  0xff57f57f 0x5cd8cd938b21b47141368c6685c990d93a9a (by decide +kernel)
private def pack_E6970Receipt39_chunk50 := witnessRule 39 53 32 640143 640269 32 2818
  0x3ffd7feb 0x11ccd2b8a23716336ae2889c98cd9ba1a (by decide +kernel)
private def pack_E6970Receipt39_chunk51 := witnessRule 39 53 64 640270 640394 32 2789
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk52 := witnessRule 39 53 96 640395 640519 32 2709
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk53 := witnessRule 39 53 128 640520 640650 32 2530
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk54 := witnessRule 39 53 160 640651 640898 32 2478
  0xbe7cbedf 0x176342e2ca6c9c590d8b9321b27263366e8685cd8cd9b8b19b (by decide +kernel)
private def pack_E6970Receipt39_chunk55 := witnessRule 39 53 192 640899 641026 11 852
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk56 := witnessRule 39 52 0 650013 650140 32 2885
  0xfdffebff 0x6ca6918548d939b0a884 (by decide +kernel)
private def pack_E6970Receipt39_chunk57 := witnessRule 39 52 32 650141 650266 32 2795
  0xfeabfabf 0xac6685cd90d938b29b5715106cc2a9190d0b9329b (by decide +kernel)
private def pack_E6970Receipt39_chunk58 := witnessRule 39 52 64 650267 650390 32 2756
  0xffd5ffab 0x9cd8cd9b8b21b57141362e8c66c9c990d9ba9a (by decide +kernel)
private def pack_E6970Receipt39_chunk59 := witnessRule 39 52 96 650391 650516 32 2622
  0x7ff5ffeb 0x338a24716336ce288dc98cda3a1a (by decide +kernel)
private def pack_E6970Receipt39_chunk60 := witnessRule 39 52 128 650517 650648 32 2458
  0x6dfffffe 0x17463366e4c66d5ccd2b99a (by decide +kernel)
private def pack_E6970Receipt39_chunk61 := witnessRule 39 52 160 650649 650898 32 2408
  0xde7c3c9f 0x2ee685c598d938b29b17265364e4c86cdc58cc421ba9a17364364e6c66cdc590da38b19b (by decide +kernel)
private def pack_E6970Receipt39_chunk62 := witnessRule 39 52 192 650899 651026 10 762
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk63 := witnessRule 39 51 0 660012 660138 32 2843
  0xe81fc07f 0x19854418ba30a898851736153384e4c2a462149c58550e238b12b471514138ac2a262111854cd8b9b0a918851726154386e4c4ac9c554da39289b (by decide +kernel)
private def pack_E6970Receipt39_chunk64 := witnessRule 39 51 32 660139 660263 32 2759
  0xfa87fa0f 0x56152364e8c2a210dc98544c429b8b0a99c471523108ae2a28c5d585442139b0a898852726153386e2c2a46214dc550dab92a (by decide +kernel)
private def pack_E6970Receipt39_chunk65 := witnessRule 39 51 64 660264 660386 32 2704
  0xeaaffd47 0x1d8552b21a17365368e4c2a2115c544c422329a3736151088e2c2a262151c54cdab922 (by decide +kernel)
private def pack_E6970Receipt39_chunk66 := witnessRule 39 51 96 660387 660513 32 2574
  0xfaa7eaaf 0x5d58cd939b21b3716536ce2a20d9c493319a17464364e4ca6d5c58544233892 (by decide +kernel)
private def pack_E6970Receipt39_chunk67 := witnessRule 39 51 128 660514 660646 32 2403
  0x4bda3f57 0x27463366e4c86d1c98cdaba1a17563366e6c66d1c590dab9988367141364e8c66cdc990da3a9a (by decide +kernel)
private def pack_E6970Receipt39_chunk68 := witnessRule 39 51 160 660647 660898 32 2345
  0xff7c3c1e 0x2e2ce6c5c998d939329b3716431086ec685cd94d939b21b3726331086e2ca6d1c590d8ba321b (by decide +kernel)
private def pack_E6970Receipt39_chunk69 := witnessRule 39 51 192 660899 661025 8 599
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk70 := witnessRule 39 50 0 670011 670136 32 2793
  0xc2ff83ff 0x158944d8bab12b36155364e6c4a270dc58948e3312a46252362e8c4a2709cd8944213931291c (by decide +kernel)
private def pack_E6970Receipt39_chunk71 := witnessRule 39 50 32 670137 670260 32 2711
  0xc03fc0bf 0xcc2a262115854cd8ba30a918851736154386e6c4ac9c58554e238b1289c5725106cc4a958548c42230aa1b27462562e4c2aa70dc98944e239291b (by decide +kernel)
private def pack_E6970Receipt39_chunk72 := witnessRule 39 50 64 670261 670337 32 2624
  0xa07fa03f 0x2ecc2a2109d18544c42939b0a99c3726152310a6e2c2a8715c5895ab8a8a09c76151062eac2a262145d1854ce139b0a918852726154388e4c4acdc554dab9289b (by decide +kernel)
private def pack_E6970Receipt39_chunk73 := witnessRule 39 50 96 670384 670462 32 2538
  0xd43f507f 0x2b29a3746151088e4c2a262151c5854ce2b8a918846715146cc2a46c9d5854421b9b0a898853726153388e2c2a462151c550db392a (by decide +kernel)
private def pack_E6970Receipt39_chunk74 := witnessRule 39 50 128 670512 670645 32 2357
  0x3827147 0x27464366e6c66210dc994da38b2188447634ce4622c5d590d93a31988427365366e4c86210dc598db38a898846714116cc8685d58cc420ba329b473615108ae2c2a262155c54cdb3922 (by decide +kernel)
private def pack_E6970Receipt39_chunk75 := witnessRule 39 50 160 670646 670899 32 2289
  0xfffe3c1e 0xb9339b2716631084f0685cd98d939b29b3726431086e2cc6d1d4c418ba329b (by decide +kernel)
private def pack_E6970Receipt39_chunk76 := witnessRule 39 50 192 670900 671025 6 443
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk77 := witnessRule 39 49 0 680010 680134 32 2737
  0x81ff81ff 0x6625106ac4a46c5d18944c428b9b1299c2726252310a4e2c4a87158944c42231299b1736252310a2e4c4a870dc98d59392a9b (by decide +kernel)
private def pack_E6970Receipt39_chunk78 := witnessRule 39 49 32 680135 680212 32 2641
  0x3ff81ff 0x76254ac4a46c5d58944e13a3128842736252386e4c4a2621598944d8bab128841746252384e6c4a262149c9894ce1b8b1291885 (by decide +kernel)
private def pack_E6970Receipt39_chunk79 := witnessRule 39 49 64 680258 680334 32 2669
  0x17fe07ff 0x9d58958b9b0aa9c3736251388e2c4a47198944d8bb312b46155364e8c4a270dcd894421b931291c (by decide +kernel)
private def pack_E6970Receipt39_chunk80 := witnessRule 39 49 96 680335 680460 32 2449
  0xf80bf8 0x2ecc2a262145d5854ce13a30a918852736154388e6c4acdc58554e2b8b1289c6725106ec2a262119854cd8bab0a918851746154386e8c4ac9c98554e23931289c5725236ec4a998548c422b0aa1b (by decide +kernel)
private def pack_E6970Receipt39_chunk81 := witnessRule 39 49 128 680461 680644 32 2283
  0x601d09d 0x139b2988427267366e2cc6210de0d0c23a1b6643106acc685d194c420b9b39b3736153388e4c2a462151c58550e2b8a9988466153364eac2a262149d1854ce1b9b0a918853726154388e2aa6d9c944dc30a883 (by decide +kernel)
private def pack_E6970Receipt39_chunk82 := witnessRule 39 49 160 680645 680960 32 2240
  0xffffbe1c 0x2f4685cd9cd93933188427168366ee620c5d590c420ba331b (by decide +kernel)
private def pack_E6970Receipt39_chunk83 := witnessRule 39 49 192 680961 681024 3 218
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk84 := witnessRule 39 48 0 690009 690086 32 2669
  0xbff07ff 0x158d44d8bab1ab36255364e6c6a270dc58d48e331aa46352362e8c6a2709cd8d44213931a91c (by decide +kernel)
private def pack_E6970Receipt39_chunk85 := witnessRule 39 48 32 690133 690209 32 2657
  0x3fe05ff 0xba312918851736254386e6c6ac9c58954e238b1a89c5735106cc6a958948c422312a1b27463562e4c4aa70dc98d44e239a91b (by decide +kernel)
private def pack_E6970Receipt39_chunk86 := witnessRule 39 48 64 690210 690331 32 2601
  0xff007fc 0x6e4c4a46214dc58950e2b8b1ab572514138ec4a20d98948d8bab12898851746253384e6c4a462149c98950e23931ab3725536ae6a26d98944c422b1299b (by decide +kernel)
private def pack_E6970Receipt39_chunk87 := witnessRule 39 48 96 690332 690458 32 2362
  0x1e007e0 0x9d58944e1ba3128843736252388e4c4a262151c5894ce2b929188467251470c4a998948d8bb31289c2756251084e8c4a470dcd8944c429b931299c4716252310a8e4a86d9cd53b1289b1766251082eac4a4709d18944c42939b1299c (by decide +kernel)
private def pack_E6970Receipt39_chunk88 := witnessRule 39 48 128 690459 690644 32 2212
  0x86018018 0xb9349b182726538306e2c8621460dd8dab0aa9b1756154384e8c2a662149cd8554e1b930aa18853716156388e2aa62115c5450ce3b0a9188466154362eac2a662145d18554e139b0aa18852726156388e4c4a4715c58944c42ab9299b6724116ec4a26d9854cc422b0aa9b (by decide +kernel)
private def pack_E6970Receipt39_chunk89 := witnessRule 39 48 160 690645 691024 32 2201
  0xffffffbc 0x2e2d46d598c41a341a (by decide +kernel)
private def pack_E6970Receipt39_chunk90 := witnessRule 39 47 0 700008 700085 32 2645
  0x7ff03ff 0xac6a46c5d18d44c428b9b1a99c2726352310a4e2c6a87158d44c42231a99b1736352310a2e4c6a870dc9915939aa9b (by decide +kernel)
private def pack_E6970Receipt39_chunk91 := witnessRule 39 47 32 700086 700207 32 2633
  0x3ffc0ffe 0x139b1a91c3726351310acc6a26c5d58d4420ba31a91c2736351310a4e4c6a670dc58d48c42b31a883 (by decide +kernel)
private def pack_E6970Receipt39_chunk92 := witnessRule 39 47 64 700208 700329 32 2537
  0x7fc0fff0 0x8e2c6a47198d44d8bb31ab46255364e8c6a270dcd8d4421b931a91c76354ac6a46c5d58d44e13a31a884 (by decide +kernel)
private def pack_E6970Receipt39_chunk93 := witnessRule 39 47 96 700330 700457 32 2280
  0x23c05f81 0x4e8c4a462149cd8950e1b8b12a9c571635138ce6a20dd8944c42331299b1756252310a2e8c4a870dd18d5939312a9c472635138ae6a46dd8d533129188456254364eac6ac5cd8954e1b9b1a89c (by decide +kernel)
private def pack_E6970Receipt39_chunk94 := witnessRule 39 47 128 700458 700644 32 2143
  0xc6018030 0x181726738304e2cc6214609e0db30aa188456156362e8c2aa62145cd855ce13930ab1885271615838306e2c2a874611c54cc42b31299b5615531088c2ae6c9d1894ce1b9b12918853726254388e2c4a662151c954db3928988c7625206ec4a46c5d98944c428bab1299c (by decide +kernel)
private def pack_E6970Receipt39_chunk95 := witnessRule 39 47 160 700645 700961 28 1886
  0xffffffe 0x230ab9b (by decide +kernel)
private def pack_E6970Receipt39_chunk96 := witnessRule 39 46 0 710007 710083 32 2621
  0x2ffe0fff 0x36355364e6c8a270dc59148e3322a46452362e8c8a2709cd9144213932291c (by decide +kernel)
private def pack_E6970Receipt39_chunk97 := witnessRule 39 46 32 710084 710204 32 2608
  0x7ff02ffc 0x11c59144e3322a5635231088c6a86c9d19158b931aa9c3726451388e8a46d59144d8bab22b (by decide +kernel)
private def pack_E6970Receipt39_chunk98 := witnessRule 39 46 64 710205 710327 32 2434
  0xff00ffc0 0x1d8d441b31a91b1756351310a2e8c6a6709cd8d48c4293931aa1c47264566e6aa6d98d44c422b1a99b1746352310a2e6c6a870dcd915938b1aa9c (by decide +kernel)
private def pack_E6970Receipt39_chunk99 := witnessRule 39 46 96 710328 710456 32 2199
  0xf807f01 0x2e6c4ac70dcd8d48e23931a89885471635338ec6a20d98d48d8bb31a89c2756351084e8c6a470dcd8d44c429b931a99c4716352310aec6a26c5d98d4420bab1a91c2746351310a4e6c6a670dc98d48c429b8b1aa1c (by decide +kernel)
private def pack_E6970Receipt39_chunk100 := witnessRule 39 46 128 710457 710645 32 2079
  0xfb038130 0x302f46d58954da30ab98843615936302e6c2aa74609c98550c430c138b0ab1d662523208cc4a86c5d5894cc428ba312a9c2736254310a4e4c4ac70dc95cd8c239299c762513208cc4a6621158954d8ba312a1885 (by decide +kernel)
private def pack_E6970Receipt39_chunk101 := witnessRule 39 46 160 710646 710960 24 1589
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk102 := witnessRule 39 45 0 720006 720082 32 2600
  0x1ffe07ff 0xb9b2299c2726452310a4e2c8a87159144c42232299b1736452310a2e4c8a870dc995593a2a9b (by decide +kernel)
private def pack_E6970Receipt39_chunk103 := witnessRule 39 45 32 720083 720202 32 2586
  0xffe07ff8 0x332289b1756451082e8c8a4709cd9144c4293932299c3716452310acc8a20d59148d8ba32289885 (by decide +kernel)
private def pack_E6970Receipt39_chunk104 := witnessRule 39 45 64 720203 720326 32 2336
  0xfe07ff03 0x66451362ecc8ad18d54d93a32289c3736451086e4c8a471d9152b2291b1756451384e8c8a2109cd9148e1b932289885 (by decide +kernel)
private def pack_E6970Receipt39_chunk105 := witnessRule 39 45 96 720327 720456 32 2120
  0xf80be05 0x4e8c6a462149cd8d50e1b931a99885371635538ec6a2621198d4cd8bab1a918851746354384e6c6a662149c98d54e23932289c5745236ec8a998d48c422b1aa1b27564562e6c6aa70dcd9144e238b2291c (by decide +kernel)
private def pack_E6970Receipt39_chunk106 := witnessRule 39 45 128 720457 720646 32 2020
  0xff81c0b0 0x2b12a1904462563108308c2aa621460d855ce0c0b930ab18861817161583acc4a6641158954c422312b9b1736256310a2e4c4b070609c98950e8c1b92a9c7625406cc6a4621158d50d8bab1a99c (by decide +kernel)
private def pack_E6970Receipt39_chunk107 := witnessRule 39 45 160 720647 720960 20 1304
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk108 := witnessRule 39 44 0 730005 730080 32 2579
  0xbffc1fff 0xdc59548e332aa46552362e8caa2709cd9544213932a91c (by decide +kernel)
private def pack_E6970Receipt39_chunk109 := witnessRule 39 44 32 730081 730200 32 2513
  0xff817ff0 0xccaa959148c422322a1b27465562e4c8aa70dc99544e23aa91b56551362eacaacd9154d939b2a89c (by decide +kernel)
private def pack_E6970Receipt39_chunk110 := witnessRule 39 44 64 730201 730325 32 2246
  0xfc03fe03 0xec8a20d99148d8bab22898851746453384e6c8a462149c99150e23932ab3745536cc8a262115914cd8ba322918851736454386e6caac9c59154e238b2a89c (by decide +kernel)
private def pack_E6970Receipt39_chunk111 := witnessRule 39 44 96 730326 730456 32 2044
  0x7807e03 0x1746354310a2e6c6ac709c98d54c42938b1ab9c1837163533aec6a60d99148dab1aa188446356364e8c8a470dcd9144c429b932299c4716452310aec8a26c5d9914420bab2291c2746451310a4e6c8a670dc99148c429b8b22a1c (by decide +kernel)
private def pack_E6970Receipt39_chunk112 := witnessRule 39 44 128 730457 730704 32 1970
  0xffeae038 0x2312a99841836156320a302c2b47198948d022b1aa18844635636308c4aa70605cd8950c430c0b9312b1d182716255310ccc6a2661198d4cc422b1aa9b (by decide +kernel)
private def pack_E6970Receipt39_chunk113 := witnessRule 39 44 160 730705 730897 15 962
  0x7fff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk114 := witnessRule 39 43 0 740004 740079 32 2561
  0x7ffc0fff 0x4e2caa87159544c42232a99b1736552310a2e4caa870dc999593aaa9b (by decide +kernel)
private def pack_E6970Receipt39_chunk115 := witnessRule 39 43 32 740080 740199 32 2449
  0xff03ffe0 0xccaa26c5d5954420ba32a91c2736551310a4e4caa670dc59548c42b32a88356552362e8caa262145cd954ce13932a91885 (by decide +kernel)
private def pack_E6970Receipt39_chunk116 := witnessRule 39 43 64 740200 740325 32 2156
  0xfc0ffc0f 0x66551362eccaad19154d93a32a89c3736551086e4caa471d9552b2a91b1756551384e8caa2109cd9548e1b932a89885 (by decide +kernel)
private def pack_E6970Receipt39_chunk117 := witnessRule 39 43 96 740326 740457 32 1967
  0x1c0be05 0x2b22a1b4635631086c6b06c605cd8d50e8c13931a998861827163553a306e6a8621599144c82332299b1756452310a2e8c8a8709cd914cc42939322a9c3745636ec8a40d99148c422b22a1b1746453310a2e6c8aa70dcd9544e238b2a91c (by decide +kernel)
private def pack_E6970Receipt39_chunk118 := witnessRule 39 43 128 740458 740707 32 1933
  0xfffff80e 0x5635333088c6aa64106118950c828c1b12b1885182625838302e2c4ae6218605c964e331a91984 (by decide +kernel)
private def pack_E6970Receipt39_chunk119 := witnessRule 39 43 160 740708 740896 10 633
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk120 := witnessRule 39 42 0 750003 750077 32 2543
  0xfff83fff 0x3332a46652362e8cca2709cd9944213933291c (by decide +kernel)
private def pack_E6970Receipt39_chunk121 := witnessRule 39 42 32 750078 750198 32 2333
  0xfe05ffc2 0x66654acaa4621119550d93a332b1726555386e4cca2711d948dab3289b17566566caaa6c9cd9944e1b8b3291c (by decide +kernel)
private def pack_E6970Receipt39_chunk122 := witnessRule 39 42 64 750199 750325 32 2071
  0xfc03fc07 0xecaa20d99548d8bab2a898851746553384e6caa462149c99550e239332b3755536ccaa262115954cd8ba32a918851736554386e6ccac9c59554e238b3289c (by decide +kernel)
private def pack_E6970Receipt39_chunk123 := witnessRule 39 42 96 750326 750458 32 1896
  0x602f01 0x663513508ac8a6641119154c420c231aa1885183635638302e4c6aa6218605c58d5ce8c139ab18852827251443acc8a80d99148c822b22a188446456362e6c8aa62145c9915ce0c13932299d183745438ccaa262115954cd8bab2a91c2746551310a4e6caa670dc99548c429b8b2aa1c (by decide +kernel)
private def pack_E6970Receipt39_chunk124 := witnessRule 39 42 128 750512 750769 32 1904
  0xffffff01 0x8c6a86810611894cd028c1b12a99851826257320a302c4b26214e058554c429c0ab9b (by decide +kernel)
private def pack_E6970Receipt39_chunk125 := witnessRule 39 42 160 750770 750896 5 314
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk126 := witnessRule 39 41 0 760002 760076 32 2529
  0xfff81fff 0x159944c42233299b1736652310a2e4cca870dc99d593b2a9b (by decide +kernel)
private def pack_E6970Receipt39_chunk127 := witnessRule 39 41 32 760077 760198 32 2233
  0xfe07ff81 0x66651362eacca2105d19948e139b32898852726653386e2cca46215999441ab3291b1746651310a2e6cca6709c99948c42938b32a1c (by decide +kernel)
private def pack_E6970Receipt39_chunk128 := witnessRule 39 41 64 760199 760326 32 1979
  0x7e07fc0f 0xc1b8b2a91d6665136acaa6621119554d93a33289c3736651086e4cca471d9952b3291b1756651384e8cca2109cd9948e1b933289885 (by decide +kernel)
private def pack_E6970Receipt39_chunk129 := witnessRule 39 41 96 760327 760513 32 1830
  0x60180780 0x381563208ac8a4681119150cc20c231a999851836355320a304c6ae62146058d64e1c0b12a9c3817254310acc8a268115954cc42232aa9b184645438302e6c8a66218605c99154e8c138b22a1886182745638ccaa60d99548c422b2aa1b1746553310a2e6caaa709c99550c42938b2ab1c (by decide +kernel)
private def pack_E6970Receipt39_chunk130 := witnessRule 39 41 128 760514 760833 31 1824
  0x7fffffd5 0x8c6a66c1060d8950d428c0b12c1985 (by decide +kernel)
private def pack_E6970Receipt39_chunk131 := witnessRule 39 40 0 770001 770075 32 2458
  0xfff07fff 0x333aa46752362e8cea2709cd9d44213933a91c (by decide +kernel)
private def pack_E6970Receipt39_chunk132 := witnessRule 39 40 32 770076 770198 32 2134
  0xfe05ff85 0x66754acca4621119950d93a33ab1726655386e4cea2711dd48dab3a89b17567566ccaa6c9cd9d44e1b8b3a91c (by decide +kernel)
private def pack_E6970Receipt39_chunk133 := witnessRule 39 40 64 770199 770327 32 1892
  0x1f02fe03 0xc13932a918861827165543a306eaa66215999481b33291b1756651310a2e8cca6709cd9948c42939332a1c3765536ccca262115994cd8ba332918851736654386e6ceac9c59954e238b3a89c (by decide +kernel)
private def pack_E6970Receipt39_chunk134 := witnessRule 39 40 96 770328 770516 32 1777
  0xfd0300e0 0x464533508306c6a868146098d58cc28c0b1ac19053816254320a704ac6210e05c54510c472b2a91984465543208308c8a6641460d9154c428c1322b9c181716456310c302e8b070e05cd50e332a8998456653368caaa6210d955cd8c0b9b2a99d (by decide +kernel)
private def pack_E6970Receipt39_chunk135 := witnessRule 39 40 128 770517 770832 25 1448
  0x1ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk136 := witnessRule 39 39 0 780000 780075 32 2397
  0xfff03fff 0x159d44c42233a99b1736752310a2e4cea870dc9a1593baa9b (by decide +kernel)
private def pack_E6970Receipt39_chunk137 := witnessRule 39 39 32 780076 780199 32 2037
  0xff03ff81 0x66751362eacea2105d19d48e139b3a898852726753386e2cea4621599d441ab3a91b1746751310a2e6cea6709c99d48c42938b3aa1c (by decide +kernel)
private def pack_E6970Receipt39_chunk138 := witnessRule 39 39 64 780200 780329 32 1804
  0xbc0bf03 0x611954cc428c1b2aa9c181726554310c302e2caac74a09d1450ceb332899045665331088ccaa6c5cd9950c428b9332b1c1827266523a306eca67199d441ab3a91b1756751384e8cea2109cd9d48e1b933a89885 (by decide +kernel)
private def pack_E6970Receipt39_chunk139 := witnessRule 39 39 96 780330 780519 32 1737
  0xffe8683c 0xc1b1a99b051816357340a702c4a66814e0954cc2240aa188885465533408306c8a866146099158c828c0b22c18853816354310a706ac6d59948c822332a1884 (by decide +kernel)
private def pack_E6970Receipt39_chunk140 := witnessRule 39 39 128 780576 780832 19 1087
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk141 := witnessRule 39 38 0 790000 790075 32 2277
  0xfff07fff 0x3342a46852362e8d0a2709cda144213934291c (by decide +kernel)
private def pack_E6970Receipt39_chunk142 := witnessRule 39 38 32 790076 790200 32 1938
  0x7f817fc2 0xc1b8b3a89d66854acea4621119d50d93a342b1726755386e4d0a2711e148dab4289b17568566ceaa6c9cda144e1b8b4291c (by decide +kernel)
private def pack_E6970Receipt39_chunk143 := witnessRule 39 38 64 790201 790331 32 1725
  0xf01fc2 0x5665134088cca666106119548cc28c1b2aa19051826556310a302cab070e059150e1c0ba2998856665406acea4621119d50d8c233299c181736652310c302e4cca874609c5994cc43333a8988456753362e8cea462145cd9d50e138b3aa9c (by decide +kernel)
private def pack_E6970Receipt39_chunk144 := witnessRule 39 38 96 790384 790579 32 1710
  0xffff5543 0xc0b1ab1b0538254350890288643119548d820c1b2299a851816457330a702c6a66614e0d54c822412a188c (by decide +kernel)
private def pack_E6970Receipt39_chunk145 := witnessRule 39 38 128 790580 790769 12 677
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk146 := witnessRule 39 37 0 800000 800076 32 2165
  0x7ff81fff 0x4e2d0a8715a144c42234299b1736852310a2e4d0a870dc9a5593c2a9b (by decide +kernel)
private def pack_E6970Receipt39_chunk147 := witnessRule 39 37 32 800077 800202 32 1842
  0x1fe07fe0 0x605cd9d48e8c13933a898861827167533acd0a26c5d5a14420ba34291c2736851310a4e4d0a670dc5a148c42b34288356852362e8d0a262145cda14ce13934291885 (by decide +kernel)
private def pack_E6970Receipt39_chunk148 := witnessRule 39 37 64 800203 800386 32 1668
  0x750e09f0 0x12094cc4482a33291a841836553340a302caae6414e05914cc829c22a9884381735143311cacea2661119d4cc820c2332919051836654310a304ccac70605d95ce1c0baa99c6675306ad0a46d19d50c421b3ab1b (by decide +kernel)
private def pack_E6970Receipt39_chunk149 := witnessRule 39 37 96 800387 800642 32 1685
  0xfffffffa 0x6059158d429c1aa1a04 (by decide +kernel)
private def pack_E6970Receipt39_chunk150 := witnessRule 39 37 128 800643 800768 5 280
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk151 := witnessRule 39 36 0 810000 810076 32 2055
  0xbff83fff 0xdc5a548e334aa46952362e8d2a2709cda544213934a91c (by decide +kernel)
private def pack_E6970Receipt39_chunk152 := witnessRule 39 36 32 810077 810203 32 1748
  0xbf02ff0 0x1846752310a306cea870605c99d4cc430c0b8b3aa9d2827651423acd0a40d5a148c422342a1b1736853310a2e4d0aa70609c9a144e8c1bc291c56951362ead2acda154d939b4a89c (by decide +kernel)
private def pack_E6970Receipt39_chunk153 := witnessRule 39 36 64 810204 810389 32 1615
  0xd7d3f47c 0x706a66c11205450cc84430c0b2ab1a05384543308906a662221460d994ccc28c0b32b98853816553310a70aaa6d5a144c82234299884 (by decide +kernel)
private def pack_E6970Receipt39_chunk154 := witnessRule 39 36 96 810390 810768 31 1619
  0x7fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk155 := witnessRule 39 35 0 820000 820077 32 1948
  0x1ffc0fff 0xb9b4a99c2726952310a4e2d2a8715a544c42234a99b1736952310a2e4d2a870dc9a9593caa9b (by decide +kernel)
private def pack_E6970Receipt39_chunk156 := witnessRule 39 35 32 820078 820205 32 1660
  0x81fc0ff8 0x8d0a466106119d44cc28c1b3a999051826755310a302ceae70e05994ce2b4a898844695336308d0a470605cda144c430c0b934299d182716852310ccd2a20d5a548d8ba34a89885 (by decide +kernel)
private def pack_E6970Receipt39_chunk157 := witnessRule 39 35 64 820256 820392 32 1572
  0xfedeb54f 0x240a8a1190986366523808708a66a11209450cc86a33a89b041836652350a302ccac6614e1550c8224229988c (by decide +kernel)
private def pack_E6970Receipt39_chunk158 := witnessRule 39 35 96 820448 820705 24 1233
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk159 := witnessRule 39 34 0 830000 830077 32 1841
  0x2ffc1fff 0x3695536302e6d2a274609c5a548eb352a46a52362e8d4a2709cda944213935291c (by decide +kernel)
private def pack_E6970Receipt39_chunk160 := witnessRule 39 34 32 830078 830257 32 1604
  0xf53e0bfc 0x1836752340a302ceac6414e1950c421c0baa8a1188e56953068d2a46410611a144c828c1b4299885182685538302f0ac715a944da34a99884 (by decide +kernel)
private def pack_E6970Receipt39_chunk161 := witnessRule 39 34 64 830258 830450 32 1519
  0xffffeef7 0x904a284642418d9d48dc21c2a99a04 (by decide +kernel)
private def pack_E6970Receipt39_chunk162 := witnessRule 39 34 96 830451 830704 18 909
  0x3ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk163 := witnessRule 39 33 0 840000 840078 32 1739
  0x7fe07ff 0x8d4a46210611a544c428c1b4a99c181726952310c302e2d2a8755a944c42235299b1736a52310a2e4d4a870609c9a9613d2a9b (by decide +kernel)
private def pack_E6970Receipt39_chunk164 := witnessRule 39 33 32 840079 840259 32 1539
  0x7fdffafe 0x241a8a1190886386533308302d0ac6214e1d50dab52903 (by decide +kernel)
private def pack_E6970Receipt39_chunk165 := witnessRule 39 33 64 840260 840454 32 1489
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk166 := witnessRule 39 33 96 840512 840704 12 599
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk167 := witnessRule 39 32 0 850000 850078 32 1641
  0x43fe0fff 0x11a944cc20c1b4a919051826954310a302d2ac70e05a148e2b5a88346b5236308d4a270605cda94428c0b935291d (by decide +kernel)
private def pack_E6970Receipt39_chunk168 := witnessRule 39 32 32 850128 850261 32 1476
  0xfd7be57f 0x6d0a270106099d48dc2a4228a1190d369523508306d0a26a14605a154cc29c3a99904 (by decide +kernel)
private def pack_E6970Receipt39_chunk169 := witnessRule 39 32 64 850262 850515 32 1467
  0xfffffff7 0x133a91d04 (by decide +kernel)
private def pack_E6970Receipt39_chunk170 := witnessRule 39 32 96 850516 850641 6 295
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk171 := witnessRule 39 31 0 860000 860128 32 1573
  0xdaff0bff 0x36a523408302d2aa6414e214cc42235a899041846a5208306d4a46214609a950e0c0bd2a9c (by decide +kernel)
private def pack_E6970Receipt39_chunk172 := witnessRule 39 31 32 860129 860263 32 1403
  0xffbffdff 0x9a148e420c134291b05 (by decide +kernel)
private def pack_E6970Receipt39_chunk173 := witnessRule 39 31 64 860264 860640 32 1454
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk174 := witnessRule 39 30 0 870000 870129 32 1501
  0xfffffdff 0x1c4a99b (by decide +kernel)
private def pack_E6970Receipt39_chunk175 := witnessRule 39 30 32 870130 870265 32 1343
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk176 := witnessRule 39 30 64 870320 870640 27 1203
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk177 := witnessRule 39 29 0 880000 880130 32 1429
  0xf2ffa5ff 0x4d4a46e10609a544dc28c4aa9a8436b513508304d4a46814605a950cc29c4a91904 (by decide +kernel)
private def pack_E6970Receipt39_chunk178 := witnessRule 39 29 32 880131 880322 32 1298
  0xfffbfebf 0x2d0a478109a544e820c0b4291c85 (by decide +kernel)
private def pack_E6970Receipt39_chunk179 := witnessRule 39 29 64 880323 880577 21 915
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk180 := witnessRule 39 28 0 890000 890131 32 1356
  0xfdffdbff 0x302d2a470149ad48d820c52a9a04 (by decide +kernel)
private def pack_E6970Receipt39_chunk181 := witnessRule 39 28 32 890132 890324 32 1264
  0xffffffbf 0xb4a91d84 (by decide +kernel)
private def pack_E6970Receipt39_chunk182 := witnessRule 39 28 64 890325 890576 16 683
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk183 := witnessRule 39 27 0 900000 900132 32 1286
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk184 := witnessRule 39 27 32 900133 900384 32 1237
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk185 := witnessRule 39 27 64 900385 900576 11 462
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk186 := witnessRule 39 26 0 910000 910133 32 1220
  0xfd7fe5ff 0xb5289e04189523b082d6a47210605a944e42944a8a09b85 (by decide +kernel)
private def pack_E6970Receipt39_chunk187 := witnessRule 39 26 32 910134 910387 32 1211
  0xfffffff7 0x4a91f03 (by decide +kernel)
private def pack_E6970Receipt39_chunk188 := witnessRule 39 26 64 910388 910513 6 247
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk189 := witnessRule 39 25 0 920000 920134 32 1163
  0xff7ffbff 0x2948f418c5291d04 (by decide +kernel)
private def pack_E6970Receipt39_chunk190 := witnessRule 39 25 32 920135 920450 32 1192
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk191 := witnessRule 39 25 64 920512 920512 1 41
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk192 := witnessRule 39 24 0 930000 930135 32 1109
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk193 := witnessRule 39 24 32 930136 930512 29 1055
  0x1fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk194 := witnessRule 39 23 0 940000 940136 32 1060
  0xffdff5ff 0x4a8a09a0012d44f818c4a92604 (by decide +kernel)
private def pack_E6970Receipt39_chunk195 := witnessRule 39 23 32 940192 940449 24 849
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk196 := witnessRule 39 22 0 950000 950192 32 1018
  0xfffffbff 0x528a09f84 (by decide +kernel)
private def pack_E6970Receipt39_chunk197 := witnessRule 39 22 32 950193 950448 20 687
  0xfffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk198 := witnessRule 39 21 0 960000 960194 32 980
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk199 := witnessRule 39 21 32 960195 960448 16 535
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk200 := witnessRule 39 20 0 970000 970195 32 942
  0xfffffdff 0x12a48228004 (by decide +kernel)
private def pack_E6970Receipt39_chunk201 := witnessRule 39 20 32 970196 970385 12 389
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk202 := witnessRule 39 19 0 980000 980197 32 910
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk203 := witnessRule 39 19 32 980256 980384 8 253
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk204 := witnessRule 39 18 0 990000 990257 32 879
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk205 := witnessRule 39 18 32 990258 990384 5 154
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk206 := witnessRule 39 17 0 1000000 1000320 32 852
  0xffffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk207 := witnessRule 39 17 32 1000321 1000321 1 30
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk208 := witnessRule 39 16 0 1010000 1010320 30 768
  0x3fffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk209 := witnessRule 39 15 0 1020000 1020320 27 663
  0x7ffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk210 := witnessRule 39 14 0 1030000 1030257 24 561
  0xffffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk211 := witnessRule 39 13 0 1040000 1040256 21 468
  0x1fffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk212 := witnessRule 39 12 0 1050000 1050256 19 403
  0x7ffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk213 := witnessRule 39 11 0 1060000 1060193 16 321
  0xffff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk214 := witnessRule 39 10 0 1070000 1070192 14 265
  0x3fff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk215 := witnessRule 39 9 0 1080000 1080192 12 215
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk216 := witnessRule 39 8 0 1090000 1090129 10 167
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk217 := witnessRule 39 7 0 1100000 1100128 8 125
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk218 := witnessRule 39 6 0 1110000 1110128 7 102
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt39_chunk219 := witnessRule 39 5 0 1120000 1120065 5 67
  0x1f 0x0 (by decide +kernel)
private def chunk220 := witnessRule 39 4 0 1130000 1130064 4 49
  0xf 0x0 (by decide +kernel)
private def chunk221 := witnessRule 39 3 0 1140000 1140064 3 34
  0x7 0x0 (by decide +kernel)
private def chunk222 := witnessRule 39 2 0 1150000 1150001 2 20
  0x3 0x0 (by decide +kernel)
private def chunk223 := witnessRule 39 1 0 1160000 1160000 1 9
  0x1 0x0 (by decide +kernel)
private def chunk224 := witnessRule 39 0 0 1170000 1170000 1 8
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt39_chunks : List (Chunk 39) := [pack_E6970Receipt39_chunk0, pack_E6970Receipt39_chunk1, pack_E6970Receipt39_chunk2, pack_E6970Receipt39_chunk3, pack_E6970Receipt39_chunk4, pack_E6970Receipt39_chunk5, pack_E6970Receipt39_chunk6, pack_E6970Receipt39_chunk7, pack_E6970Receipt39_chunk8, pack_E6970Receipt39_chunk9, pack_E6970Receipt39_chunk10, pack_E6970Receipt39_chunk11, pack_E6970Receipt39_chunk12, pack_E6970Receipt39_chunk13, pack_E6970Receipt39_chunk14, pack_E6970Receipt39_chunk15, pack_E6970Receipt39_chunk16, pack_E6970Receipt39_chunk17, pack_E6970Receipt39_chunk18, pack_E6970Receipt39_chunk19, pack_E6970Receipt39_chunk20, pack_E6970Receipt39_chunk21, pack_E6970Receipt39_chunk22, pack_E6970Receipt39_chunk23, pack_E6970Receipt39_chunk24, pack_E6970Receipt39_chunk25, pack_E6970Receipt39_chunk26, pack_E6970Receipt39_chunk27, pack_E6970Receipt39_chunk28, pack_E6970Receipt39_chunk29, pack_E6970Receipt39_chunk30, pack_E6970Receipt39_chunk31, pack_E6970Receipt39_chunk32, pack_E6970Receipt39_chunk33, pack_E6970Receipt39_chunk34, pack_E6970Receipt39_chunk35, pack_E6970Receipt39_chunk36, pack_E6970Receipt39_chunk37, pack_E6970Receipt39_chunk38, pack_E6970Receipt39_chunk39, pack_E6970Receipt39_chunk40, pack_E6970Receipt39_chunk41, pack_E6970Receipt39_chunk42, pack_E6970Receipt39_chunk43, pack_E6970Receipt39_chunk44, pack_E6970Receipt39_chunk45, pack_E6970Receipt39_chunk46, pack_E6970Receipt39_chunk47, pack_E6970Receipt39_chunk48, pack_E6970Receipt39_chunk49, pack_E6970Receipt39_chunk50, pack_E6970Receipt39_chunk51, pack_E6970Receipt39_chunk52, pack_E6970Receipt39_chunk53, pack_E6970Receipt39_chunk54, pack_E6970Receipt39_chunk55, pack_E6970Receipt39_chunk56, pack_E6970Receipt39_chunk57, pack_E6970Receipt39_chunk58, pack_E6970Receipt39_chunk59, pack_E6970Receipt39_chunk60, pack_E6970Receipt39_chunk61, pack_E6970Receipt39_chunk62, pack_E6970Receipt39_chunk63, pack_E6970Receipt39_chunk64, pack_E6970Receipt39_chunk65, pack_E6970Receipt39_chunk66, pack_E6970Receipt39_chunk67, pack_E6970Receipt39_chunk68, pack_E6970Receipt39_chunk69, pack_E6970Receipt39_chunk70, pack_E6970Receipt39_chunk71, pack_E6970Receipt39_chunk72, pack_E6970Receipt39_chunk73, pack_E6970Receipt39_chunk74, pack_E6970Receipt39_chunk75, pack_E6970Receipt39_chunk76, pack_E6970Receipt39_chunk77, pack_E6970Receipt39_chunk78, pack_E6970Receipt39_chunk79, pack_E6970Receipt39_chunk80, pack_E6970Receipt39_chunk81, pack_E6970Receipt39_chunk82, pack_E6970Receipt39_chunk83, pack_E6970Receipt39_chunk84, pack_E6970Receipt39_chunk85, pack_E6970Receipt39_chunk86, pack_E6970Receipt39_chunk87, pack_E6970Receipt39_chunk88, pack_E6970Receipt39_chunk89, pack_E6970Receipt39_chunk90, pack_E6970Receipt39_chunk91, pack_E6970Receipt39_chunk92, pack_E6970Receipt39_chunk93, pack_E6970Receipt39_chunk94, pack_E6970Receipt39_chunk95, pack_E6970Receipt39_chunk96, pack_E6970Receipt39_chunk97, pack_E6970Receipt39_chunk98, pack_E6970Receipt39_chunk99, pack_E6970Receipt39_chunk100, pack_E6970Receipt39_chunk101, pack_E6970Receipt39_chunk102, pack_E6970Receipt39_chunk103, pack_E6970Receipt39_chunk104, pack_E6970Receipt39_chunk105, pack_E6970Receipt39_chunk106, pack_E6970Receipt39_chunk107, pack_E6970Receipt39_chunk108, pack_E6970Receipt39_chunk109, pack_E6970Receipt39_chunk110, pack_E6970Receipt39_chunk111, pack_E6970Receipt39_chunk112, pack_E6970Receipt39_chunk113, pack_E6970Receipt39_chunk114, pack_E6970Receipt39_chunk115, pack_E6970Receipt39_chunk116, pack_E6970Receipt39_chunk117, pack_E6970Receipt39_chunk118, pack_E6970Receipt39_chunk119, pack_E6970Receipt39_chunk120, pack_E6970Receipt39_chunk121, pack_E6970Receipt39_chunk122, pack_E6970Receipt39_chunk123, pack_E6970Receipt39_chunk124, pack_E6970Receipt39_chunk125, pack_E6970Receipt39_chunk126, pack_E6970Receipt39_chunk127, pack_E6970Receipt39_chunk128, pack_E6970Receipt39_chunk129, pack_E6970Receipt39_chunk130, pack_E6970Receipt39_chunk131, pack_E6970Receipt39_chunk132, pack_E6970Receipt39_chunk133, pack_E6970Receipt39_chunk134, pack_E6970Receipt39_chunk135, pack_E6970Receipt39_chunk136, pack_E6970Receipt39_chunk137, pack_E6970Receipt39_chunk138, pack_E6970Receipt39_chunk139, pack_E6970Receipt39_chunk140, pack_E6970Receipt39_chunk141, pack_E6970Receipt39_chunk142, pack_E6970Receipt39_chunk143, pack_E6970Receipt39_chunk144, pack_E6970Receipt39_chunk145, pack_E6970Receipt39_chunk146, pack_E6970Receipt39_chunk147, pack_E6970Receipt39_chunk148, pack_E6970Receipt39_chunk149, pack_E6970Receipt39_chunk150, pack_E6970Receipt39_chunk151, pack_E6970Receipt39_chunk152, pack_E6970Receipt39_chunk153, pack_E6970Receipt39_chunk154, pack_E6970Receipt39_chunk155, pack_E6970Receipt39_chunk156, pack_E6970Receipt39_chunk157, pack_E6970Receipt39_chunk158, pack_E6970Receipt39_chunk159, pack_E6970Receipt39_chunk160, pack_E6970Receipt39_chunk161, pack_E6970Receipt39_chunk162, pack_E6970Receipt39_chunk163, pack_E6970Receipt39_chunk164, pack_E6970Receipt39_chunk165, pack_E6970Receipt39_chunk166, pack_E6970Receipt39_chunk167, pack_E6970Receipt39_chunk168, pack_E6970Receipt39_chunk169, pack_E6970Receipt39_chunk170, pack_E6970Receipt39_chunk171, pack_E6970Receipt39_chunk172, pack_E6970Receipt39_chunk173, pack_E6970Receipt39_chunk174, pack_E6970Receipt39_chunk175, pack_E6970Receipt39_chunk176, pack_E6970Receipt39_chunk177, pack_E6970Receipt39_chunk178, pack_E6970Receipt39_chunk179, pack_E6970Receipt39_chunk180, pack_E6970Receipt39_chunk181, pack_E6970Receipt39_chunk182, pack_E6970Receipt39_chunk183, pack_E6970Receipt39_chunk184, pack_E6970Receipt39_chunk185, pack_E6970Receipt39_chunk186, pack_E6970Receipt39_chunk187, pack_E6970Receipt39_chunk188, pack_E6970Receipt39_chunk189, pack_E6970Receipt39_chunk190, pack_E6970Receipt39_chunk191, pack_E6970Receipt39_chunk192, pack_E6970Receipt39_chunk193, pack_E6970Receipt39_chunk194, pack_E6970Receipt39_chunk195, pack_E6970Receipt39_chunk196, pack_E6970Receipt39_chunk197, pack_E6970Receipt39_chunk198, pack_E6970Receipt39_chunk199, pack_E6970Receipt39_chunk200, pack_E6970Receipt39_chunk201, pack_E6970Receipt39_chunk202, pack_E6970Receipt39_chunk203, pack_E6970Receipt39_chunk204, pack_E6970Receipt39_chunk205, pack_E6970Receipt39_chunk206, pack_E6970Receipt39_chunk207, pack_E6970Receipt39_chunk208, pack_E6970Receipt39_chunk209, pack_E6970Receipt39_chunk210, pack_E6970Receipt39_chunk211, pack_E6970Receipt39_chunk212, pack_E6970Receipt39_chunk213, pack_E6970Receipt39_chunk214, pack_E6970Receipt39_chunk215, pack_E6970Receipt39_chunk216, pack_E6970Receipt39_chunk217, pack_E6970Receipt39_chunk218, pack_E6970Receipt39_chunk219, chunk220, chunk221, chunk222, chunk223, chunk224]
def rows39 := rowsFrom pack_E6970Receipt39_chunks
theorem good39 : ∀ r ∈ rows39, good 39 r = true := rowsFrom_good pack_E6970Receipt39_chunks
theorem sorted39 : rows39.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt39_chunks 0 (by decide +kernel)).1
theorem mass39 (i : Fin 61) :
    bandCount 39 (i.val : ℤ) 60 16 ≤ (rows39.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt39_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 39 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt39_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total39 : (rows39.map (price 39)).sum = 416531 :=
  (total_eq pack_E6970Receipt39_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt39

section Pack_E6970Receipt4

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt4_chunk0 := witnessRule 4 12 0 256 256 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt4_chunk1 := witnessRule 4 11 0 10193 10193 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt4_chunk2 := witnessRule 4 10 0 20130 20192 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt4_chunk3 := witnessRule 4 9 0 30067 30192 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt4_chunk4 := witnessRule 4 8 0 40004 40129 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt4_chunk5 := witnessRule 4 7 0 50003 50128 4 420
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt4_chunk6 := witnessRule 4 6 0 60002 60128 5 519
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt4_chunk7 := witnessRule 4 5 0 70001 70065 4 412
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt4_chunk8 := witnessRule 4 4 0 80000 80064 4 408
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt4_chunk9 := witnessRule 4 3 0 90000 90064 3 297
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt4_chunk10 := witnessRule 4 2 0 100000 100001 2 194
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt4_chunk11 := witnessRule 4 1 0 110000 110000 1 95
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt4_chunk12 := witnessRule 4 0 0 120000 120000 1 91
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt4_chunks : List (Chunk 4) := [pack_E6970Receipt4_chunk0, pack_E6970Receipt4_chunk1, pack_E6970Receipt4_chunk2, pack_E6970Receipt4_chunk3, pack_E6970Receipt4_chunk4, pack_E6970Receipt4_chunk5, pack_E6970Receipt4_chunk6, pack_E6970Receipt4_chunk7, pack_E6970Receipt4_chunk8, pack_E6970Receipt4_chunk9, pack_E6970Receipt4_chunk10, pack_E6970Receipt4_chunk11, pack_E6970Receipt4_chunk12]
def rows4 := rowsFrom pack_E6970Receipt4_chunks
theorem good4 : ∀ r ∈ rows4, good 4 r = true := rowsFrom_good pack_E6970Receipt4_chunks
theorem sorted4 : rows4.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt4_chunks 0 (by decide +kernel)).1
theorem mass4 (i : Fin 61) :
    bandCount 4 (i.val : ℤ) 60 16 ≤ (rows4.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt4_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 4 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt4_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total4 : (rows4.map (price 4)).sum = 3605 :=
  (total_eq pack_E6970Receipt4_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt4

section Pack_E6970Receipt5

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt5_chunk0 := witnessRule 5 15 0 320 320 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk1 := witnessRule 5 14 0 10257 10257 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk2 := witnessRule 5 13 0 20194 20256 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk3 := witnessRule 5 12 0 30131 30256 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk4 := witnessRule 5 11 0 40068 40193 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk5 := witnessRule 5 10 0 50005 50192 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk6 := witnessRule 5 9 0 60004 60192 6 626
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk7 := witnessRule 5 8 0 70003 70129 6 622
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk8 := witnessRule 5 7 0 80002 80128 6 618
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk9 := witnessRule 5 6 0 90001 90128 6 606
  0x3f 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk10 := witnessRule 5 5 0 100000 100065 5 503
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk11 := witnessRule 5 4 0 110000 110064 4 392
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk12 := witnessRule 5 3 0 120000 120064 3 285
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk13 := witnessRule 5 2 0 130000 130001 2 186
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk14 := witnessRule 5 1 0 140000 140000 1 91
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt5_chunk15 := witnessRule 5 0 0 150000 150000 1 87
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt5_chunks : List (Chunk 5) := [pack_E6970Receipt5_chunk0, pack_E6970Receipt5_chunk1, pack_E6970Receipt5_chunk2, pack_E6970Receipt5_chunk3, pack_E6970Receipt5_chunk4, pack_E6970Receipt5_chunk5, pack_E6970Receipt5_chunk6, pack_E6970Receipt5_chunk7, pack_E6970Receipt5_chunk8, pack_E6970Receipt5_chunk9, pack_E6970Receipt5_chunk10, pack_E6970Receipt5_chunk11, pack_E6970Receipt5_chunk12, pack_E6970Receipt5_chunk13, pack_E6970Receipt5_chunk14, pack_E6970Receipt5_chunk15]
def rows5 := rowsFrom pack_E6970Receipt5_chunks
theorem good5 : ∀ r ∈ rows5, good 5 r = true := rowsFrom_good pack_E6970Receipt5_chunks
theorem sorted5 : rows5.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt5_chunks 0 (by decide +kernel)).1
theorem mass5 (i : Fin 61) :
    bandCount 5 (i.val : ℤ) 60 16 ≤ (rows5.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt5_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 5 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt5_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total5 : (rows5.map (price 5)).sum = 5712 :=
  (total_eq pack_E6970Receipt5_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt5

section Pack_E6970Receipt6

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt6_chunk0 := witnessRule 6 18 0 384 384 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk1 := witnessRule 6 17 0 10321 10321 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk2 := witnessRule 6 16 0 20258 20320 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk3 := witnessRule 6 15 0 30195 30320 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk4 := witnessRule 6 14 0 40132 40257 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk5 := witnessRule 6 13 0 50069 50256 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk6 := witnessRule 6 12 0 60006 60256 7 733
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk7 := witnessRule 6 11 0 70005 70193 7 729
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk8 := witnessRule 6 10 0 80004 80192 8 828
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk9 := witnessRule 6 9 0 90003 90192 8 816
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk10 := witnessRule 6 8 0 100002 100129 8 812
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk11 := witnessRule 6 7 0 110001 110128 7 701
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk12 := witnessRule 6 6 0 120000 120128 7 689
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk13 := witnessRule 6 5 0 130000 130065 5 483
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk14 := witnessRule 6 4 0 140000 140064 4 376
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk15 := witnessRule 6 3 0 150000 150064 3 273
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk16 := witnessRule 6 2 0 160000 160001 2 178
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk17 := witnessRule 6 1 0 170000 170000 1 87
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt6_chunk18 := witnessRule 6 0 0 180000 180000 1 83
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt6_chunks : List (Chunk 6) := [pack_E6970Receipt6_chunk0, pack_E6970Receipt6_chunk1, pack_E6970Receipt6_chunk2, pack_E6970Receipt6_chunk3, pack_E6970Receipt6_chunk4, pack_E6970Receipt6_chunk5, pack_E6970Receipt6_chunk6, pack_E6970Receipt6_chunk7, pack_E6970Receipt6_chunk8, pack_E6970Receipt6_chunk9, pack_E6970Receipt6_chunk10, pack_E6970Receipt6_chunk11, pack_E6970Receipt6_chunk12, pack_E6970Receipt6_chunk13, pack_E6970Receipt6_chunk14, pack_E6970Receipt6_chunk15, pack_E6970Receipt6_chunk16, pack_E6970Receipt6_chunk17, pack_E6970Receipt6_chunk18]
def rows6 := rowsFrom pack_E6970Receipt6_chunks
theorem good6 : ∀ r ∈ rows6, good 6 r = true := rowsFrom_good pack_E6970Receipt6_chunks
theorem sorted6 : rows6.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt6_chunks 0 (by decide +kernel)).1
theorem mass6 (i : Fin 61) :
    bandCount 6 (i.val : ℤ) 60 16 ≤ (rows6.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt6_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 6 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt6_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total6 : (rows6.map (price 6)).sum = 8484 :=
  (total_eq pack_E6970Receipt6_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt6

section Pack_E6970Receipt7

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt7_chunk0 := witnessRule 7 21 0 448 448 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk1 := witnessRule 7 20 0 10385 10385 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk2 := witnessRule 7 19 0 20322 20384 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk3 := witnessRule 7 18 0 30259 30384 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk4 := witnessRule 7 17 0 40196 40321 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk5 := witnessRule 7 16 0 50133 50320 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk6 := witnessRule 7 15 0 60070 60320 7 733
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk7 := witnessRule 7 14 0 70007 70257 8 836
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk8 := witnessRule 7 13 0 80006 80256 9 935
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk9 := witnessRule 7 12 0 90005 90256 10 1026
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk10 := witnessRule 7 11 0 100004 100193 10 1022
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk11 := witnessRule 7 10 0 110003 110192 10 1010
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk12 := witnessRule 7 9 0 120002 120192 10 998
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk13 := witnessRule 7 8 0 130001 130129 9 887
  0x1ff 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk14 := witnessRule 7 7 0 140000 140128 8 780
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk15 := witnessRule 7 6 0 150000 150128 7 661
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk16 := witnessRule 7 5 0 160000 160065 5 463
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk17 := witnessRule 7 4 0 170000 170064 4 360
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk18 := witnessRule 7 3 0 180000 180064 3 261
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk19 := witnessRule 7 2 0 190000 190001 2 170
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk20 := witnessRule 7 1 0 200000 200000 1 83
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt7_chunk21 := witnessRule 7 0 0 210000 210000 1 79
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt7_chunks : List (Chunk 7) := [pack_E6970Receipt7_chunk0, pack_E6970Receipt7_chunk1, pack_E6970Receipt7_chunk2, pack_E6970Receipt7_chunk3, pack_E6970Receipt7_chunk4, pack_E6970Receipt7_chunk5, pack_E6970Receipt7_chunk6, pack_E6970Receipt7_chunk7, pack_E6970Receipt7_chunk8, pack_E6970Receipt7_chunk9, pack_E6970Receipt7_chunk10, pack_E6970Receipt7_chunk11, pack_E6970Receipt7_chunk12, pack_E6970Receipt7_chunk13, pack_E6970Receipt7_chunk14, pack_E6970Receipt7_chunk15, pack_E6970Receipt7_chunk16, pack_E6970Receipt7_chunk17, pack_E6970Receipt7_chunk18, pack_E6970Receipt7_chunk19, pack_E6970Receipt7_chunk20, pack_E6970Receipt7_chunk21]
def rows7 := rowsFrom pack_E6970Receipt7_chunks
theorem good7 : ∀ r ∈ rows7, good 7 r = true := rowsFrom_good pack_E6970Receipt7_chunks
theorem sorted7 : rows7.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt7_chunks 0 (by decide +kernel)).1
theorem mass7 (i : Fin 61) :
    bandCount 7 (i.val : ℤ) 60 16 ≤ (rows7.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt7_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 7 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt7_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total7 : (rows7.map (price 7)).sum = 12000 :=
  (total_eq pack_E6970Receipt7_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt7

section Pack_E6970Receipt8

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace E6970FinalRankReceipt
open K1_13_1_1 (bandCount)

private def pack_E6970Receipt8_chunk0 := witnessRule 8 24 0 512 512 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk1 := witnessRule 8 23 0 10449 10449 1 107
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk2 := witnessRule 8 22 0 20386 20448 2 214
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk3 := witnessRule 8 21 0 30323 30448 3 317
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk4 := witnessRule 8 20 0 40260 40385 4 424
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk5 := witnessRule 8 19 0 50197 50384 5 527
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk6 := witnessRule 8 18 0 60134 60384 7 733
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk7 := witnessRule 8 17 0 70071 70321 8 836
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk8 := witnessRule 8 16 0 80008 80320 10 1042
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk9 := witnessRule 8 15 0 90007 90320 11 1133
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk10 := witnessRule 8 14 0 100006 100257 12 1232
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk11 := witnessRule 8 13 0 110005 110256 12 1220
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk12 := witnessRule 8 12 0 120004 120256 13 1307
  0x1fff 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk13 := witnessRule 8 11 0 130003 130193 12 1196
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk14 := witnessRule 8 10 0 140002 140192 12 1184
  0xfff 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk15 := witnessRule 8 9 0 150001 150192 11 1065
  0x7ff 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk16 := witnessRule 8 8 0 160000 160129 10 958
  0x3ff 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk17 := witnessRule 8 7 0 170000 170128 8 748
  0xff 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk18 := witnessRule 8 6 0 180000 180128 7 633
  0x7f 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk19 := witnessRule 8 5 0 190000 190065 5 443
  0x1f 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk20 := witnessRule 8 4 0 200000 200064 4 344
  0xf 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk21 := witnessRule 8 3 0 210000 210064 3 249
  0x7 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk22 := witnessRule 8 2 0 220000 220001 2 162
  0x3 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk23 := witnessRule 8 1 0 230000 230000 1 79
  0x1 0x0 (by decide +kernel)
private def pack_E6970Receipt8_chunk24 := witnessRule 8 0 0 240000 240000 1 75
  0x1 0x0 (by decide +kernel)

private def pack_E6970Receipt8_chunks : List (Chunk 8) := [pack_E6970Receipt8_chunk0, pack_E6970Receipt8_chunk1, pack_E6970Receipt8_chunk2, pack_E6970Receipt8_chunk3, pack_E6970Receipt8_chunk4, pack_E6970Receipt8_chunk5, pack_E6970Receipt8_chunk6, pack_E6970Receipt8_chunk7, pack_E6970Receipt8_chunk8, pack_E6970Receipt8_chunk9, pack_E6970Receipt8_chunk10, pack_E6970Receipt8_chunk11, pack_E6970Receipt8_chunk12, pack_E6970Receipt8_chunk13, pack_E6970Receipt8_chunk14, pack_E6970Receipt8_chunk15, pack_E6970Receipt8_chunk16, pack_E6970Receipt8_chunk17, pack_E6970Receipt8_chunk18, pack_E6970Receipt8_chunk19, pack_E6970Receipt8_chunk20, pack_E6970Receipt8_chunk21, pack_E6970Receipt8_chunk22, pack_E6970Receipt8_chunk23, pack_E6970Receipt8_chunk24]
def rows8 := rowsFrom pack_E6970Receipt8_chunks
theorem good8 : ∀ r ∈ rows8, good 8 r = true := rowsFrom_good pack_E6970Receipt8_chunks
theorem sorted8 : rows8.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux pack_E6970Receipt8_chunks 0 (by decide +kernel)).1
theorem mass8 (i : Fin 61) :
    bandCount 8 (i.val : ℤ) 60 16 ≤ (rows8.filter (fun r => decide (i.val ≤ r.index))).length := by
  change _ ≤ ((rowsFrom pack_E6970Receipt8_chunks).filter _).length
  rw [mass_eq]
  have h : (List.range 61).all
      (fun j => decide (bandCount 8 (j : ℤ) 60 16 ≤ mass j pack_E6970Receipt8_chunks)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))
theorem total8 : (rows8.map (price 8)).sum = 16335 :=
  (total_eq pack_E6970Receipt8_chunks).trans (by decide +kernel)
end E6970FinalRankReceipt
end Pack_E6970Receipt8

import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptGroup53
import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 5000000

namespace Low53At2389AnchorRankReceipt
open scoped BigOperators
open K1_13_1_1 (bandCount)
open Low53At2389AnchorSpace (cap)

def rows : ℕ → List Row
  | 0 => rows0
  | 1 => rows1
  | 2 => rows2
  | 3 => rows3
  | 4 => rows4
  | 5 => rows5
  | 6 => rows6
  | 7 => rows7
  | 8 => rows8
  | 9 => rows9
  | 10 => rows10
  | 11 => rows11
  | 12 => rows12
  | 13 => rows13
  | 14 => rows14
  | 15 => rows15
  | 16 => rows16
  | 17 => rows17
  | 18 => rows18
  | 19 => rows19
  | 20 => rows20
  | 21 => rows21
  | 22 => rows22
  | 23 => rows23
  | 24 => rows24
  | 25 => rows25
  | 26 => rows26
  | 27 => rows27
  | 28 => rows28
  | 29 => rows29
  | 30 => rows30
  | 31 => rows31
  | 32 => rows32
  | 33 => rows33
  | 34 => rows34
  | 35 => rows35
  | 36 => rows36
  | 37 => rows37
  | 38 => rows38
  | 39 => rows39
  | 40 => rows40
  | 41 => rows41
  | 42 => rows42
  | 43 => rows43
  | 44 => rows44
  | 45 => rows45
  | 46 => rows46
  | 47 => rows47
  | 48 => rows48
  | 49 => rows49
  | 50 => rows50
  | 51 => rows51
  | 52 => rows52
  | 53 => rows53
  | _ => []

theorem rows_good (d : Fin 54) : ∀ r ∈ rows d, good d r = true := by
  fin_cases d
  · exact good0
  · exact good1
  · exact good2
  · exact good3
  · exact good4
  · exact good5
  · exact good6
  · exact good7
  · exact good8
  · exact good9
  · exact good10
  · exact good11
  · exact good12
  · exact good13
  · exact good14
  · exact good15
  · exact good16
  · exact good17
  · exact good18
  · exact good19
  · exact good20
  · exact good21
  · exact good22
  · exact good23
  · exact good24
  · exact good25
  · exact good26
  · exact good27
  · exact good28
  · exact good29
  · exact good30
  · exact good31
  · exact good32
  · exact good33
  · exact good34
  · exact good35
  · exact good36
  · exact good37
  · exact good38
  · exact good39
  · exact good40
  · exact good41
  · exact good42
  · exact good43
  · exact good44
  · exact good45
  · exact good46
  · exact good47
  · exact good48
  · exact good49
  · exact good50
  · exact good51
  · exact good52
  · exact good53

theorem rows_sorted (d : Fin 54) : (rows d).Pairwise (fun a b => a.tag < b.tag) := by
  fin_cases d
  · exact sorted0
  · exact sorted1
  · exact sorted2
  · exact sorted3
  · exact sorted4
  · exact sorted5
  · exact sorted6
  · exact sorted7
  · exact sorted8
  · exact sorted9
  · exact sorted10
  · exact sorted11
  · exact sorted12
  · exact sorted13
  · exact sorted14
  · exact sorted15
  · exact sorted16
  · exact sorted17
  · exact sorted18
  · exact sorted19
  · exact sorted20
  · exact sorted21
  · exact sorted22
  · exact sorted23
  · exact sorted24
  · exact sorted25
  · exact sorted26
  · exact sorted27
  · exact sorted28
  · exact sorted29
  · exact sorted30
  · exact sorted31
  · exact sorted32
  · exact sorted33
  · exact sorted34
  · exact sorted35
  · exact sorted36
  · exact sorted37
  · exact sorted38
  · exact sorted39
  · exact sorted40
  · exact sorted41
  · exact sorted42
  · exact sorted43
  · exact sorted44
  · exact sorted45
  · exact sorted46
  · exact sorted47
  · exact sorted48
  · exact sorted49
  · exact sorted50
  · exact sorted51
  · exact sorted52
  · exact sorted53

theorem rows_cover (d : Fin 54) : ∀ i : Fin 54, bandCount d (i.val : ℤ) 53 13 ≤ (rows d |>.filter (fun r => decide (i.val ≤ r.index))).length := by
  fin_cases d
  · intro i
    exact mass0 i
  · intro i
    exact mass1 i
  · intro i
    exact mass2 i
  · intro i
    exact mass3 i
  · intro i
    exact mass4 i
  · intro i
    exact mass5 i
  · intro i
    exact mass6 i
  · intro i
    exact mass7 i
  · intro i
    exact mass8 i
  · intro i
    exact mass9 i
  · intro i
    exact mass10 i
  · intro i
    exact mass11 i
  · intro i
    exact mass12 i
  · intro i
    exact mass13 i
  · intro i
    exact mass14 i
  · intro i
    exact mass15 i
  · intro i
    exact mass16 i
  · intro i
    exact mass17 i
  · intro i
    exact mass18 i
  · intro i
    exact mass19 i
  · intro i
    exact mass20 i
  · intro i
    exact mass21 i
  · intro i
    exact mass22 i
  · intro i
    exact mass23 i
  · intro i
    exact mass24 i
  · intro i
    exact mass25 i
  · intro i
    exact mass26 i
  · intro i
    exact mass27 i
  · intro i
    exact mass28 i
  · intro i
    exact mass29 i
  · intro i
    exact mass30 i
  · intro i
    exact mass31 i
  · intro i
    exact mass32 i
  · intro i
    exact mass33 i
  · intro i
    exact mass34 i
  · intro i
    exact mass35 i
  · intro i
    exact mass36 i
  · intro i
    exact mass37 i
  · intro i
    exact mass38 i
  · intro i
    exact mass39 i
  · intro i
    exact mass40 i
  · intro i
    exact mass41 i
  · intro i
    exact mass42 i
  · intro i
    exact mass43 i
  · intro i
    exact mass44 i
  · intro i
    exact mass45 i
  · intro i
    exact mass46 i
  · intro i
    exact mass47 i
  · intro i
    exact mass48 i
  · intro i
    exact mass49 i
  · intro i
    exact mass50 i
  · intro i
    exact mass51 i
  · intro i
    exact mass52 i
  · intro i
    exact mass53 i

private def expected : ℕ → ℕ
  | 0 => 96
  | 1 => 380
  | 2 => 940
  | 3 => 1860
  | 4 => 3220
  | 5 => 5096
  | 6 => 7560
  | 7 => 10680
  | 8 => 14520
  | 9 => 19140
  | 10 => 24596
  | 11 => 30940
  | 12 => 38220
  | 13 => 46480
  | 14 => 55678
  | 15 => 65772
  | 16 => 76720
  | 17 => 88480
  | 18 => 101010
  | 19 => 114268
  | 20 => 128212
  | 21 => 142575
  | 22 => 157028
  | 23 => 171258
  | 24 => 184968
  | 25 => 197877
  | 26 => 209720
  | 27 => 220248
  | 28 => 229432
  | 29 => 237381
  | 30 => 244134
  | 31 => 249795
  | 32 => 254400
  | 33 => 258301
  | 34 => 261279
  | 35 => 263639
  | 36 => 265203
  | 37 => 266233
  | 38 => 266588
  | 39 => 266490
  | 40 => 265829
  | 41 => 264793
  | 42 => 263298
  | 43 => 261501
  | 44 => 259343
  | 45 => 256953
  | 46 => 254293
  | 47 => 251468
  | 48 => 248459
  | 49 => 245350
  | 50 => 242136
  | 51 => 238886
  | 52 => 235603
  | 53 => 5541742
  | _ => 0

theorem rows_price (d : Fin 54) : ((rows d).map (price d)).sum = (expected d) := by
  fin_cases d
  · exact total0
  · exact total1
  · exact total2
  · exact total3
  · exact total4
  · exact total5
  · exact total6
  · exact total7
  · exact total8
  · exact total9
  · exact total10
  · exact total11
  · exact total12
  · exact total13
  · exact total14
  · exact total15
  · exact total16
  · exact total17
  · exact total18
  · exact total19
  · exact total20
  · exact total21
  · exact total22
  · exact total23
  · exact total24
  · exact total25
  · exact total26
  · exact total27
  · exact total28
  · exact total29
  · exact total30
  · exact total31
  · exact total32
  · exact total33
  · exact total34
  · exact total35
  · exact total36
  · exact total37
  · exact total38
  · exact total39
  · exact total40
  · exact total41
  · exact total42
  · exact total43
  · exact total44
  · exact total45
  · exact total46
  · exact total47
  · exact total48
  · exact total49
  · exact total50
  · exact total51
  · exact total52
  · exact total53

theorem total_fees : (∑ s : Fin 130, ((rows (cap s)).map (fee s)).sum) = 14010071 := by
  rw [sum_fees]
  simp_rw [rows_price]
  rw [Fin.sum_univ_eq_sum_range expected 54]
  decide +kernel

end Low53At2389AnchorRankReceipt

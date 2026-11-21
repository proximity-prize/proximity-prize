import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptGroup0
import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptGroup5
import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptGroup10
import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptGroup15
import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptGroup20
import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptGroup25
import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptGroup30
import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptGroup35
import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptGroup40
import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptGroup45
import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptGroup50
import ProximityPrize.SubmissionLower.Low51EdgeRankReceiptSum

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000

namespace Low51EdgeRankReceipt
open scoped BigOperators
open K1_13_1_1 (bandCount)
open Low51EdgeAnchorSpace (cap)

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
theorem rows_cover (d i : Fin 54) :
    bandCount d (i.val : ℤ) 53 13 ≤ ((rows d).filter (fun r => decide (i.val ≤ r.index))).length := by
  fin_cases d
  · exact mass0 i
  · exact mass1 i
  · exact mass2 i
  · exact mass3 i
  · exact mass4 i
  · exact mass5 i
  · exact mass6 i
  · exact mass7 i
  · exact mass8 i
  · exact mass9 i
  · exact mass10 i
  · exact mass11 i
  · exact mass12 i
  · exact mass13 i
  · exact mass14 i
  · exact mass15 i
  · exact mass16 i
  · exact mass17 i
  · exact mass18 i
  · exact mass19 i
  · exact mass20 i
  · exact mass21 i
  · exact mass22 i
  · exact mass23 i
  · exact mass24 i
  · exact mass25 i
  · exact mass26 i
  · exact mass27 i
  · exact mass28 i
  · exact mass29 i
  · exact mass30 i
  · exact mass31 i
  · exact mass32 i
  · exact mass33 i
  · exact mass34 i
  · exact mass35 i
  · exact mass36 i
  · exact mass37 i
  · exact mass38 i
  · exact mass39 i
  · exact mass40 i
  · exact mass41 i
  · exact mass42 i
  · exact mass43 i
  · exact mass44 i
  · exact mass45 i
  · exact mass46 i
  · exact mass47 i
  · exact mass48 i
  · exact mass49 i
  · exact mass50 i
  · exact mass51 i
  · exact mass52 i
  · exact mass53 i

private def expected : ℕ → ℕ
  | 0 => 94
  | 1 => 372
  | 2 => 920
  | 3 => 1820
  | 4 => 3150
  | 5 => 4984
  | 6 => 7392
  | 7 => 10440
  | 8 => 14190
  | 9 => 18700
  | 10 => 24024
  | 11 => 30212
  | 12 => 37310
  | 13 => 45360
  | 14 => 54320
  | 15 => 64148
  | 16 => 74802
  | 17 => 86240
  | 18 => 98420
  | 19 => 111300
  | 20 => 124838
  | 21 => 138773
  | 22 => 152784
  | 23 => 166566
  | 24 => 179830
  | 25 => 192303
  | 26 => 203728
  | 27 => 213864
  | 28 => 222684
  | 29 => 230295
  | 30 => 236736
  | 31 => 242109
  | 32 => 246450
  | 33 => 250806
  | 34 => 252360
  | 35 => 256894
  | 36 => 254968
  | 37 => 260724
  | 38 => 254744
  | 39 => 262634
  | 40 => 252126
  | 41 => 262947
  | 42 => 247521
  | 43 => 261973
  | 44 => 241307
  | 45 => 260012
  | 46 => 233831
  | 47 => 242914
  | 48 => 239967
  | 49 => 236924
  | 50 => 233787
  | 51 => 230621
  | 52 => 227428
  | 53 => 5102496
  | _ => 0

theorem rows_price (d : Fin 54) :
    ((rows d).map (price d)).sum = expected d := by
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


theorem total_fees :
    (∑ s : Fin 127, ((rows (cap s)).map (fee s)).sum) = 13306142 := by
  rw [sum_fees]
  simp_rw [rows_price]
  rw [Fin.sum_univ_eq_sum_range expected 54]
  decide +kernel


end Low51EdgeRankReceipt

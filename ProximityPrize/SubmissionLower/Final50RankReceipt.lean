import ProximityPrize.SubmissionLower.Final50RankReceiptGroup0
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup5
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup10
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup15
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup20
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup25
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup30
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup35
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup40
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup45
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup50
import ProximityPrize.SubmissionLower.Final50RankReceiptGroup55
import ProximityPrize.SubmissionLower.Final50RankReceiptSum

set_option maxRecDepth 16000
set_option maxHeartbeats 5000000

namespace Final50RankReceipt
open scoped BigOperators
open K1_13_1_1 (bandCount)
open Final50AnchorSpace (cap)

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
  | 54 => rows54
  | 55 => rows55
  | _ => []

private def expected : ℕ → ℕ
  | 0 => 99
  | 1 => 392
  | 2 => 970
  | 3 => 1920
  | 4 => 3325
  | 5 => 5264
  | 6 => 7812
  | 7 => 11040
  | 8 => 15015
  | 9 => 19800
  | 10 => 25454
  | 11 => 32032
  | 12 => 39585
  | 13 => 48160
  | 14 => 57800
  | 15 => 68460
  | 16 => 80095
  | 17 => 92660
  | 18 => 106110
  | 19 => 120400
  | 20 => 135485
  | 21 => 151242
  | 22 => 167321
  | 23 => 183388
  | 24 => 199125
  | 25 => 214230
  | 26 => 228417
  | 27 => 241416
  | 28 => 252973
  | 29 => 263130
  | 30 => 271929
  | 31 => 279480
  | 32 => 285822
  | 33 => 291060
  | 34 => 295506
  | 35 => 298985
  | 36 => 301762
  | 37 => 303703
  | 38 => 305030
  | 39 => 305646
  | 40 => 305733
  | 41 => 305226
  | 42 => 304271
  | 43 => 302831
  | 44 => 301020
  | 45 => 298826
  | 46 => 296335
  | 47 => 293556
  | 48 => 290551
  | 49 => 287347
  | 50 => 283987
  | 51 => 280510
  | 52 => 276945
  | 53 => 273339
  | 54 => 269711
  | 55 => 6481793
  | _ => 0

theorem rows_good (d : Fin 56) : ∀ r ∈ rows d, good d r = true := by
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
  · exact good54
  · exact good55
theorem rows_sorted (d : Fin 56) : (rows d).Pairwise (fun a b => a.tag < b.tag) := by
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
  · exact sorted54
  · exact sorted55
theorem rows_cover (d i : Fin 56) :
    bandCount d (i.val : ℤ) 55 14 ≤ ((rows d).filter (fun r => decide (i.val ≤ r.index))).length := by
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
  · exact mass54 i
  · exact mass55 i

private theorem rows_price (d : Fin 56) :
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
  · exact total54
  · exact total55


theorem total_fees :
    (∑ s : Fin 133, ((rows (cap s)).map (fee s)).sum) = 16564024 := by
  rw [sum_fees]
  simp_rw [rows_price]
  rw [Fin.sum_univ_eq_sum_range expected 56]
  decide +kernel

#print axioms rows_good
#print axioms rows_sorted
#print axioms rows_cover
#print axioms total_fees

end Final50RankReceipt

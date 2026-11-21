import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceipt0
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceipt20
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceipt34
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceipt43
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceipt50
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceipt53

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

namespace Cutter53AnchorRankReceipt
open Low51EdgeRankReceipt (rows)
open Cutter53AnchorSpace (cap)
open scoped BigOperators

private def total : ℕ → ℕ
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
  | 33 => 258048
  | 34 => 261642
  | 35 => 262666
  | 36 => 266356
  | 37 => 264143
  | 38 => 263842
  | 39 => 268441
  | 40 => 261464
  | 41 => 268069
  | 42 => 257040
  | 43 => 266355
  | 44 => 250953
  | 45 => 263612
  | 46 => 243557
  | 47 => 260141
  | 48 => 235175
  | 49 => 256238
  | 50 => 226101
  | 51 => 252195
  | 52 => 216598
  | 53 => 5578281
  | _ => 0

theorem price_rows (d : Fin 54) : ((rows d).map (price d)).sum = total d := by
  fin_cases d
  · exact row_total0
  · exact row_total1
  · exact row_total2
  · exact row_total3
  · exact row_total4
  · exact row_total5
  · exact row_total6
  · exact row_total7
  · exact row_total8
  · exact row_total9
  · exact row_total10
  · exact row_total11
  · exact row_total12
  · exact row_total13
  · exact row_total14
  · exact row_total15
  · exact row_total16
  · exact row_total17
  · exact row_total18
  · exact row_total19
  · exact row_total20
  · exact row_total21
  · exact row_total22
  · exact row_total23
  · exact row_total24
  · exact row_total25
  · exact row_total26
  · exact row_total27
  · exact row_total28
  · exact row_total29
  · exact row_total30
  · exact row_total31
  · exact row_total32
  · exact row_total33
  · exact row_total34
  · exact row_total35
  · exact row_total36
  · exact row_total37
  · exact row_total38
  · exact row_total39
  · exact row_total40
  · exact row_total41
  · exact row_total42
  · exact row_total43
  · exact row_total44
  · exact row_total45
  · exact row_total46
  · exact row_total47
  · exact row_total48
  · exact row_total49
  · exact row_total50
  · exact row_total51
  · exact row_total52
  · exact row_total53

theorem total_fees :
    (∑ s : Fin 130, ((rows (cap s)).map (fee s)).sum) = 14013601 := by
  rw [sum_fees]
  simp_rw [price_rows]
  rw [Fin.sum_univ_eq_sum_range total 54]
  decide +kernel

end Cutter53AnchorRankReceipt

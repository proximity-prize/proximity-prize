import ProximityPrize.SubmissionLower.Low51At2403AnchorRankReceipt0
import ProximityPrize.SubmissionLower.Low51At2403AnchorRankReceipt20
import ProximityPrize.SubmissionLower.Low51At2403AnchorRankReceipt34
import ProximityPrize.SubmissionLower.Low51At2403AnchorRankReceipt43
import ProximityPrize.SubmissionLower.Low51At2403AnchorRankReceipt50
import ProximityPrize.SubmissionLower.Low51At2403AnchorRankReceipt53

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

namespace Low51At2403AnchorRankReceipt
open Low51EdgeRankReceipt (rows)
open Low51At2403AnchorSpace (cap)
open scoped BigOperators

private def total : ℕ → ℕ
  | 0 => 95
  | 1 => 376
  | 2 => 930
  | 3 => 1840
  | 4 => 3185
  | 5 => 5040
  | 6 => 7476
  | 7 => 10560
  | 8 => 14355
  | 9 => 18920
  | 10 => 24310
  | 11 => 30576
  | 12 => 37765
  | 13 => 45920
  | 14 => 54999
  | 15 => 64960
  | 16 => 75761
  | 17 => 87360
  | 18 => 99715
  | 19 => 112784
  | 20 => 126525
  | 21 => 140674
  | 22 => 154906
  | 23 => 168912
  | 24 => 182399
  | 25 => 195090
  | 26 => 206724
  | 27 => 217056
  | 28 => 226058
  | 29 => 233838
  | 30 => 240435
  | 31 => 245952
  | 32 => 250557
  | 33 => 254349
  | 34 => 257339
  | 35 => 259623
  | 36 => 261211
  | 37 => 262196
  | 38 => 262586
  | 39 => 262469
  | 40 => 261853
  | 41 => 260820
  | 42 => 259377
  | 43 => 257603
  | 44 => 255503
  | 45 => 253153
  | 46 => 250556
  | 47 => 247787
  | 48 => 244846
  | 49 => 241806
  | 50 => 238666
  | 51 => 235495
  | 52 => 232292
  | 53 => 5309396
  | _ => 0

private theorem price_rows (d : Fin 54) : ((rows d).map (price d)).sum = total d := by
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
    (∑ s : Fin 128, ((rows (cap s)).map (fee s)).sum) = 13654979 := by
  rw [sum_fees]
  simp_rw [price_rows]
  rw [Fin.sum_univ_eq_sum_range total 54]
  decide +kernel

end Low51At2403AnchorRankReceipt

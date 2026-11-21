import ProximityPrize.SubmissionLower.RankGrades82190G0
import ProximityPrize.SubmissionLower.RankGrades82190G1
import ProximityPrize.SubmissionLower.RankGrades82190G2
import ProximityPrize.SubmissionLower.RankGrades82190G3
import ProximityPrize.SubmissionLower.RankGrades82190G4
import ProximityPrize.SubmissionLower.RankGrades82190G5
import ProximityPrize.SubmissionLower.RankGrades82190G6
import ProximityPrize.SubmissionLower.RankGrades82190G7
import ProximityPrize.SubmissionLower.RankGrades82190G8
import ProximityPrize.SubmissionLower.RankGrades82190G9
import ProximityPrize.SubmissionLower.RankGrades82190G10
import ProximityPrize.SubmissionLower.RankGrades82190G11
import ProximityPrize.SubmissionLower.RankGrades82190G12
import ProximityPrize.SubmissionLower.RankGrades82190G13
import ProximityPrize.SubmissionLower.RankGrades82190G14
import ProximityPrize.SubmissionLower.RankGrades82190G15
import ProximityPrize.SubmissionLower.RankGrades82190G16
import ProximityPrize.SubmissionLower.RankGrades82190G17
import ProximityPrize.SubmissionLower.RankGrades82190G18
import ProximityPrize.SubmissionLower.RankGrades82190G19
import ProximityPrize.SubmissionLower.RankGrades82190G20
import ProximityPrize.SubmissionLower.RankGrades82190G21
import ProximityPrize.SubmissionLower.RankGrades82190G22
import ProximityPrize.SubmissionLower.RankGrades82190G23
import ProximityPrize.SubmissionLower.RankGrades82190G24

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace RankCharge82190
open K1_13 (Geom)
open K1_13_1_1 (offset sumRange sumRange_eq_fin)
open Pascal82190 (block)
open scoped BigOperators
private def plan : ℕ → ℕ → Method
  | 0 => schedule0
  | 1 => schedule1
  | 2 => schedule2
  | 3 => schedule3
  | 4 => schedule4
  | 5 => schedule5
  | 6 => schedule6
  | 7 => schedule7
  | 8 => schedule8
  | 9 => schedule9
  | 10 => schedule10
  | 11 => schedule11
  | 12 => schedule12
  | 13 => schedule13
  | 14 => schedule14
  | 15 => schedule15
  | 16 => schedule16
  | 17 => schedule17
  | 18 => schedule18
  | 19 => schedule19
  | 20 => schedule20
  | 21 => schedule21
  | 22 => schedule22
  | 23 => schedule23
  | 24 => schedule24
  | 25 => schedule25
  | 26 => schedule26
  | 27 => schedule27
  | 28 => schedule28
  | 29 => schedule29
  | 30 => schedule30
  | 31 => schedule31
  | 32 => schedule32
  | 33 => schedule33
  | 34 => schedule34
  | 35 => schedule35
  | 36 => schedule36
  | 37 => schedule37
  | 38 => schedule38
  | 39 => schedule39
  | 40 => schedule40
  | 41 => schedule41
  | 42 => schedule42
  | 43 => schedule43
  | 44 => schedule44
  | 45 => schedule45
  | 46 => schedule46
  | 47 => schedule47
  | 48 => schedule48
  | 49 => schedule49
  | 50 => schedule50
  | 51 => schedule51
  | 52 => schedule52
  | 53 => schedule53
  | 54 => schedule54
  | 55 => schedule55
  | 56 => schedule56
  | 57 => schedule57
  | 58 => schedule58
  | 59 => schedule59
  | 60 => schedule60
  | 61 => schedule61
  | 62 => schedule62
  | 63 => schedule63
  | 64 => schedule64
  | 65 => schedule65
  | 66 => schedule66
  | 67 => schedule67
  | 68 => schedule68
  | 69 => schedule69
  | 70 => schedule70
  | 71 => schedule71
  | 72 => schedule72
  | 73 => schedule73
  | 74 => schedule74
  | 75 => schedule75
  | 76 => schedule76
  | 77 => schedule77
  | 78 => schedule78
  | 79 => schedule79
  | 80 => schedule80
  | 81 => schedule81
  | 82 => schedule82
  | 83 => schedule83
  | 84 => schedule84
  | 85 => schedule85
  | 86 => schedule86
  | 87 => schedule87
  | 88 => schedule88
  | 89 => schedule89
  | 90 => schedule90
  | 91 => schedule91
  | 92 => schedule92
  | 93 => schedule93
  | 94 => schedule94
  | 95 => schedule95
  | 96 => schedule96
  | 97 => schedule97
  | 98 => schedule98
  | 99 => schedule99
  | 100 => schedule100
  | 101 => schedule101
  | 102 => schedule102
  | 103 => schedule103
  | 104 => schedule104
  | 105 => schedule105
  | 106 => schedule106
  | 107 => schedule107
  | 108 => schedule108
  | 109 => schedule109
  | 110 => schedule110
  | 111 => schedule111
  | 112 => schedule112
  | 113 => schedule113
  | 114 => schedule114
  | 115 => schedule115
  | 116 => schedule116
  | 117 => schedule117
  | 118 => schedule118
  | 119 => schedule119
  | 120 => schedule120
  | _ => fun _ => .source
private def cap : ℕ → ℕ
  | 0 => 90
  | 1 => 356
  | 2 => 880
  | 3 => 1740
  | 4 => 3010
  | 5 => 4760
  | 6 => 7056
  | 7 => 9960
  | 8 => 13530
  | 9 => 17820
  | 10 => 22880
  | 11 => 28756
  | 12 => 35490
  | 13 => 43043
  | 14 => 51376
  | 15 => 60450
  | 16 => 70226
  | 17 => 80665
  | 18 => 91728
  | 19 => 103163
  | 20 => 114660
  | 21 => 125925
  | 22 => 136680
  | 23 => 146663
  | 24 => 155628
  | 25 => 163410
  | 26 => 170112
  | 27 => 175770
  | 28 => 180482
  | 29 => 184281
  | 30 => 187260
  | 31 => 189449
  | 32 => 190936
  | 33 => 191748
  | 34 => 191968
  | 35 => 191620
  | 36 => 190782
  | 37 => 189475
  | 38 => 187772
  | 39 => 185691
  | 40 => 183300
  | 41 => 180614
  | 42 => 177696
  | 43 => 174559
  | 44 => 171261
  | 45 => 167812
  | 46 => 164266
  | 47 => 160630
  | 48 => 156949
  | 49 => 153233
  | 50 => 149524
  | 51 => 145824
  | 52 => 142130
  | 53 => 138450
  | 54 => 134783
  | 55 => 131132
  | 56 => 127494
  | 57 => 123878
  | 58 => 120283
  | 59 => 116713
  | 60 => 113165
  | 61 => 109649
  | 62 => 106164
  | 63 => 102715
  | 64 => 99299
  | 65 => 95927
  | 66 => 92598
  | 67 => 89318
  | 68 => 86082
  | 69 => 82901
  | 70 => 79772
  | 71 => 76699
  | 72 => 73677
  | 73 => 70714
  | 74 => 67808
  | 75 => 64960
  | 76 => 62168
  | 77 => 59437
  | 78 => 56767
  | 79 => 54158
  | 80 => 51608
  | 81 => 49121
  | 82 => 46700
  | 83 => 44340
  | 84 => 42048
  | 85 => 39812
  | 86 => 37649
  | 87 => 35549
  | 88 => 33522
  | 89 => 31546
  | 90 => 29650
  | 91 => 27810
  | 92 => 26046
  | 93 => 24339
  | 94 => 22707
  | 95 => 21132
  | 96 => 19628
  | 97 => 18186
  | 98 => 16811
  | 99 => 15497
  | 100 => 14248
  | 101 => 13072
  | 102 => 11952
  | 103 => 10878
  | 104 => 9893
  | 105 => 8945
  | 106 => 8043
  | 107 => 7173
  | 108 => 6297
  | 109 => 5577
  | 110 => 4755
  | 111 => 4151
  | 112 => 3387
  | 113 => 2895
  | 114 => 2208
  | 115 => 1827
  | 116 => 1245
  | 117 => 967
  | 118 => 525
  | 119 => 343
  | 120 => 0
  | _ => 0
private theorem grade_eq (s : Fin 121) : grade s (plan s) = cap s := by
  fin_cases s
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
  · exact total56
  · exact total57
  · exact total58
  · exact total59
  · exact total60
  · exact total61
  · exact total62
  · exact total63
  · exact total64
  · exact total65
  · exact total66
  · exact total67
  · exact total68
  · exact total69
  · exact total70
  · exact total71
  · exact total72
  · exact total73
  · exact total74
  · exact total75
  · exact total76
  · exact total77
  · exact total78
  · exact total79
  · exact total80
  · exact total81
  · exact total82
  · exact total83
  · exact total84
  · exact total85
  · exact total86
  · exact total87
  · exact total88
  · exact total89
  · exact total90
  · exact total91
  · exact total92
  · exact total93
  · exact total94
  · exact total95
  · exact total96
  · exact total97
  · exact total98
  · exact total99
  · exact total100
  · exact total101
  · exact total102
  · exact total103
  · exact total104
  · exact total105
  · exact total106
  · exact total107
  · exact total108
  · exact total109
  · exact total110
  · exact total111
  · exact total112
  · exact total113
  · exact total114
  · exact total115
  · exact total116
  · exact total117
  · exact total118
  · exact total119
  · exact total120
theorem total_rank :
    (∑ s : Fin 121, ∑ r : Fin 138, Module.finrank Geom (LinearMap.range (block s (offset r)))) ≤ 9513882 := by
  calc
    _ ≤ ∑ s : Fin 121, cap s := Finset.sum_le_sum fun s _ =>
      (grade_bound s (plan s)).trans_eq (grade_eq s)
    _ = _ := by rw [← sumRange_eq_fin]; decide +kernel
#print axioms total_rank
end RankCharge82190

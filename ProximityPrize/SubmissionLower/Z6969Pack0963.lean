import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0671
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0960
import ProximityPrize.SubmissionLower.Z6969Pack0949
import ProximityPrize.SubmissionLower.Z6969Pack0950
import ProximityPrize.SubmissionLower.Z6969Pack0951
import ProximityPrize.SubmissionLower.Z6969Pack0952
import ProximityPrize.SubmissionLower.Z6969Pack0953
import ProximityPrize.SubmissionLower.Z6969Pack0954
import ProximityPrize.SubmissionLower.Z6969Pack0959
import ProximityPrize.SubmissionLower.Z6969Pack0962
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0672
import ProximityPrize.SubmissionLower.Z6969Pack0668

set_option Elab.async false

-- Source: Research6969.HardFit3At180
section Z6969Source2896
set_option autoImplicit true
namespace Research6969.HardFit3At180
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3400 18)
theorem case180: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,17,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route3400 17)
theorem case181: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,21,some 22⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route3400 15)
private def leaf3 := (PairReceipts.route3400 16)
private def weight4 := PairRoute.weight 304158 leaf2 leaf3
theorem case182: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,23,some 24⟩:=PairRoute.start _ weight4
private def leaf5 := (PairReceipts.route3400 13)
private def leaf6 := (PairReceipts.route3400 14)
private def weight7 := PairRoute.weight 304553 leaf5 leaf6
theorem case183: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,25,some 28⟩:=PairRoute.start _ weight7
private def leaf8 := (PairReceipts.route3400 11)
private def leaf9 := (PairReceipts.route3400 12)
private def weight10 := PairRoute.weight 300842 leaf8 leaf9
theorem case184: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,29,some 32⟩:=PairRoute.start _ weight10
private def leaf11 := (PairReceipts.route3400 10)
theorem case185: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,33,some 36⟩:=PairRoute.start _ leaf11
private def leaf12 := (PairReceipts.route3400 9)
theorem case186: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,37,some 40⟩:=PairRoute.start _ leaf12
private def leaf13 := (PairReceipts.route3400 7)
private def leaf14 := (PairReceipts.route3400 8)
private def weight15 := PairRoute.weight 294092 leaf13 leaf14
theorem case187: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,41,some 44⟩:=PairRoute.start _ weight15
private def leaf16 := (PairReceipts.route3400 6)
theorem case188: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,45,some 48⟩:=PairRoute.start _ leaf16
private def leaf17 := (PairReceipts.route3400 4)
private def leaf18 := (PairReceipts.route3400 5)
private def weight19 := PairRoute.weight 289917 leaf17 leaf18
theorem case189: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,49,some 50⟩:=PairRoute.start _ weight19
end Research6969.HardFit3At180
end Z6969Source2896

-- Source: Research6969.HardFit3At190
section Z6969Source2897
set_option autoImplicit true
namespace Research6969.HardFit3At190
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3400 3)
theorem case190: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,51,some 51⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route3400 2)
private theorem leaf2:PairRoute.Done (2:Fin 18) ⟨⟨64,722,12,2,52,some 52⟩,0,none,288407,none⟩:=PairLeaves.excluded PairReceipts.cell3403 PairReceipts.check3403 (none)
private def weight3 := PairRoute.weight 288407 leaf1 leaf2
theorem case191: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,52,some 52⟩:=PairRoute.start _ weight3
end Research6969.HardFit3At190
end Z6969Source2897

-- Source: Research6969.HardComplete3
section Z6969Source2898
set_option autoImplicit true
namespace Research6969.HardComplete3
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_6 (j:Fin HighPendingSeed3.regions.size) (l:0≤j.val) (h:j.val<6):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At000.case0
  · exact HardFit3At000.case1
  · exact HardFit3At000.case2
  · exact HardFit3At000.case3
  · exact HardFit3At000.case4
  · exact HardFit3At000.case5
private theorem covered6_12 (j:Fin HighPendingSeed3.regions.size) (l:6≤j.val) (h:j.val<12):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At000.case6
  · exact HardFit3At000.case7
  · exact HardFit3At000.case8
  · exact HardFit3At000.case9
  · exact HardFit3At010.case10
  · exact HardFit3At010.case11
private theorem covered0_12 (j:Fin HighPendingSeed3.regions.size) (l:0≤j.val) (h:j.val<12):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<6
  · exact covered0_6 j l low
  · exact covered6_12 j (by omega) h
private theorem covered12_18 (j:Fin HighPendingSeed3.regions.size) (l:12≤j.val) (h:j.val<18):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At010.case12
  · exact HardFit3At010.case13
  · exact HardFit3At010.case14
  · exact HardFit3At010.case15
  · exact HardFit3At010.case16
  · exact HardFit3At010.case17
private theorem covered18_24 (j:Fin HighPendingSeed3.regions.size) (l:18≤j.val) (h:j.val<24):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At010.case18
  · exact HardFit3At010.case19
  · exact HardFit3At020.case20
  · exact HardFit3At020.case21
  · exact HardFit3At020.case22
  · exact HardFit3At020.case23
private theorem covered12_24 (j:Fin HighPendingSeed3.regions.size) (l:12≤j.val) (h:j.val<24):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<18
  · exact covered12_18 j l low
  · exact covered18_24 j (by omega) h
private theorem covered0_24 (j:Fin HighPendingSeed3.regions.size) (l:0≤j.val) (h:j.val<24):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<12
  · exact covered0_12 j l low
  · exact covered12_24 j (by omega) h
private theorem covered24_30 (j:Fin HighPendingSeed3.regions.size) (l:24≤j.val) (h:j.val<30):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At020.case24
  · exact HardFit3At020.case25
  · exact HardFit3At020.case26
  · exact HardFit3At020.case27
  · exact HardFit3At020.case28
  · exact HardFit3At020.case29
private theorem covered30_36 (j:Fin HighPendingSeed3.regions.size) (l:30≤j.val) (h:j.val<36):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At030.case30
  · exact HardFit3At030.case31
  · exact HardFit3At030.case32
  · exact HardFit3At030.case33
  · exact HardFit3At030.case34
  · exact HardFit3At030.case35
private theorem covered24_36 (j:Fin HighPendingSeed3.regions.size) (l:24≤j.val) (h:j.val<36):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<30
  · exact covered24_30 j l low
  · exact covered30_36 j (by omega) h
private theorem covered36_42 (j:Fin HighPendingSeed3.regions.size) (l:36≤j.val) (h:j.val<42):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At030.case36
  · exact HardFit3At030.case37
  · exact HardFit3At030.case38
  · exact HardFit3At030.case39
  · exact HardFit3At040.case40
  · exact HardFit3At040.case41
private theorem covered42_48 (j:Fin HighPendingSeed3.regions.size) (l:42≤j.val) (h:j.val<48):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At040.case42
  · exact HardFit3At040.case43
  · exact HardFit3At040.case44
  · exact HardFit3At040.case45
  · exact HardFit3At040.case46
  · exact HardFit3At040.case47
private theorem covered36_48 (j:Fin HighPendingSeed3.regions.size) (l:36≤j.val) (h:j.val<48):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<42
  · exact covered36_42 j l low
  · exact covered42_48 j (by omega) h
private theorem covered24_48 (j:Fin HighPendingSeed3.regions.size) (l:24≤j.val) (h:j.val<48):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<36
  · exact covered24_36 j l low
  · exact covered36_48 j (by omega) h
private theorem covered0_48 (j:Fin HighPendingSeed3.regions.size) (l:0≤j.val) (h:j.val<48):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<24
  · exact covered0_24 j l low
  · exact covered24_48 j (by omega) h
private theorem covered48_54 (j:Fin HighPendingSeed3.regions.size) (l:48≤j.val) (h:j.val<54):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At040.case48
  · exact HardFit3At040.case49
  · exact HardFit3At050.case50
  · exact HardFit3At050.case51
  · exact HardFit3At050.case52
  · exact HardFit3At050.case53
private theorem covered54_60 (j:Fin HighPendingSeed3.regions.size) (l:54≤j.val) (h:j.val<60):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At050.case54
  · exact HardFit3At050.case55
  · exact HardFit3At050.case56
  · exact HardFit3At050.case57
  · exact HardFit3At050.case58
  · exact HardFit3At050.case59
private theorem covered48_60 (j:Fin HighPendingSeed3.regions.size) (l:48≤j.val) (h:j.val<60):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<54
  · exact covered48_54 j l low
  · exact covered54_60 j (by omega) h
private theorem covered60_66 (j:Fin HighPendingSeed3.regions.size) (l:60≤j.val) (h:j.val<66):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At060.case60
  · exact HardFit3At060.case61
  · exact HardFit3At060.case62
  · exact HardFit3At060.case63
  · exact HardFit3At060.case64
  · exact HardFit3At060.case65
private theorem covered66_72 (j:Fin HighPendingSeed3.regions.size) (l:66≤j.val) (h:j.val<72):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At060.case66
  · exact HardFit3At060.case67
  · exact HardFit3At060.case68
  · exact HardFit3At060.case69
  · exact HardFit3At070.case70
  · exact HardFit3At070.case71
private theorem covered60_72 (j:Fin HighPendingSeed3.regions.size) (l:60≤j.val) (h:j.val<72):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<66
  · exact covered60_66 j l low
  · exact covered66_72 j (by omega) h
private theorem covered48_72 (j:Fin HighPendingSeed3.regions.size) (l:48≤j.val) (h:j.val<72):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<60
  · exact covered48_60 j l low
  · exact covered60_72 j (by omega) h
private theorem covered72_78 (j:Fin HighPendingSeed3.regions.size) (l:72≤j.val) (h:j.val<78):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At070.case72
  · exact HardFit3At070.case73
  · exact HardFit3At070.case74
  · exact HardFit3At070.case75
  · exact HardFit3At070.case76
  · exact HardFit3At070.case77
private theorem covered78_84 (j:Fin HighPendingSeed3.regions.size) (l:78≤j.val) (h:j.val<84):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At070.case78
  · exact HardFit3At070.case79
  · exact HardFit3At080.case80
  · exact HardFit3At080.case81
  · exact HardFit3At080.case82
  · exact HardFit3At080.case83
private theorem covered72_84 (j:Fin HighPendingSeed3.regions.size) (l:72≤j.val) (h:j.val<84):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<78
  · exact covered72_78 j l low
  · exact covered78_84 j (by omega) h
private theorem covered84_90 (j:Fin HighPendingSeed3.regions.size) (l:84≤j.val) (h:j.val<90):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At080.case84
  · exact HardFit3At080.case85
  · exact HardFit3At080.case86
  · exact HardFit3At080.case87
  · exact HardFit3At080.case88
  · exact HardFit3At080.case89
private theorem covered90_96 (j:Fin HighPendingSeed3.regions.size) (l:90≤j.val) (h:j.val<96):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At090.case90
  · exact HardFit3At090.case91
  · exact HardFit3At090.case92
  · exact HardFit3At090.case93
  · exact HardFit3At090.case94
  · exact HardFit3At090.case95
private theorem covered84_96 (j:Fin HighPendingSeed3.regions.size) (l:84≤j.val) (h:j.val<96):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<90
  · exact covered84_90 j l low
  · exact covered90_96 j (by omega) h
private theorem covered72_96 (j:Fin HighPendingSeed3.regions.size) (l:72≤j.val) (h:j.val<96):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<84
  · exact covered72_84 j l low
  · exact covered84_96 j (by omega) h
private theorem covered48_96 (j:Fin HighPendingSeed3.regions.size) (l:48≤j.val) (h:j.val<96):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<72
  · exact covered48_72 j l low
  · exact covered72_96 j (by omega) h
private theorem covered0_96 (j:Fin HighPendingSeed3.regions.size) (l:0≤j.val) (h:j.val<96):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<48
  · exact covered0_48 j l low
  · exact covered48_96 j (by omega) h
private theorem covered96_102 (j:Fin HighPendingSeed3.regions.size) (l:96≤j.val) (h:j.val<102):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At090.case96
  · exact HardFit3At090.case97
  · exact HardFit3At090.case98
  · exact HardFit3At090.case99
  · exact HardFit3At100.case100
  · exact HardFit3At100.case101
private theorem covered102_108 (j:Fin HighPendingSeed3.regions.size) (l:102≤j.val) (h:j.val<108):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At100.case102
  · exact HardFit3At100.case103
  · exact HardFit3At100.case104
  · exact HardFit3At100.case105
  · exact HardFit3At100.case106
  · exact HardFit3At100.case107
private theorem covered96_108 (j:Fin HighPendingSeed3.regions.size) (l:96≤j.val) (h:j.val<108):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<102
  · exact covered96_102 j l low
  · exact covered102_108 j (by omega) h
private theorem covered108_114 (j:Fin HighPendingSeed3.regions.size) (l:108≤j.val) (h:j.val<114):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At100.case108
  · exact HardFit3At100.case109
  · exact HardFit3At110.case110
  · exact HardFit3At110.case111
  · exact HardFit3At110.case112
  · exact HardFit3At110.case113
private theorem covered114_120 (j:Fin HighPendingSeed3.regions.size) (l:114≤j.val) (h:j.val<120):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At110.case114
  · exact HardFit3At110.case115
  · exact HardFit3At110.case116
  · exact HardFit3At110.case117
  · exact HardFit3At110.case118
  · exact HardFit3At110.case119
private theorem covered108_120 (j:Fin HighPendingSeed3.regions.size) (l:108≤j.val) (h:j.val<120):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<114
  · exact covered108_114 j l low
  · exact covered114_120 j (by omega) h
private theorem covered96_120 (j:Fin HighPendingSeed3.regions.size) (l:96≤j.val) (h:j.val<120):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<108
  · exact covered96_108 j l low
  · exact covered108_120 j (by omega) h
private theorem covered120_126 (j:Fin HighPendingSeed3.regions.size) (l:120≤j.val) (h:j.val<126):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At120.case120
  · exact HardFit3At120.case121
  · exact HardFit3At120.case122
  · exact HardFit3At120.case123
  · exact HardFit3At120.case124
  · exact HardFit3At120.case125
private theorem covered126_132 (j:Fin HighPendingSeed3.regions.size) (l:126≤j.val) (h:j.val<132):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At120.case126
  · exact HardFit3At120.case127
  · exact HardFit3At120.case128
  · exact HardFit3At120.case129
  · exact HardFit3At130.case130
  · exact HardFit3At130.case131
private theorem covered120_132 (j:Fin HighPendingSeed3.regions.size) (l:120≤j.val) (h:j.val<132):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<126
  · exact covered120_126 j l low
  · exact covered126_132 j (by omega) h
private theorem covered132_138 (j:Fin HighPendingSeed3.regions.size) (l:132≤j.val) (h:j.val<138):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At130.case132
  · exact HardFit3At130.case133
  · exact HardFit3At130.case134
  · exact HardFit3At130.case135
  · exact HardFit3At130.case136
  · exact HardFit3At130.case137
private theorem covered138_144 (j:Fin HighPendingSeed3.regions.size) (l:138≤j.val) (h:j.val<144):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At130.case138
  · exact HardFit3At130.case139
  · exact HardFit3At140.case140
  · exact HardFit3At140.case141
  · exact HardFit3At140.case142
  · exact HardFit3At140.case143
private theorem covered132_144 (j:Fin HighPendingSeed3.regions.size) (l:132≤j.val) (h:j.val<144):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<138
  · exact covered132_138 j l low
  · exact covered138_144 j (by omega) h
private theorem covered120_144 (j:Fin HighPendingSeed3.regions.size) (l:120≤j.val) (h:j.val<144):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<132
  · exact covered120_132 j l low
  · exact covered132_144 j (by omega) h
private theorem covered96_144 (j:Fin HighPendingSeed3.regions.size) (l:96≤j.val) (h:j.val<144):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<120
  · exact covered96_120 j l low
  · exact covered120_144 j (by omega) h
private theorem covered144_150 (j:Fin HighPendingSeed3.regions.size) (l:144≤j.val) (h:j.val<150):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At140.case144
  · exact HardFit3At140.case145
  · exact HardFit3At140.case146
  · exact HardFit3At140.case147
  · exact HardFit3At140.case148
  · exact HardFit3At140.case149
private theorem covered150_156 (j:Fin HighPendingSeed3.regions.size) (l:150≤j.val) (h:j.val<156):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At150.case150
  · exact HardFit3At150.case151
  · exact HardFit3At150.case152
  · exact HardFit3At150.case153
  · exact HardFit3At150.case154
  · exact HardFit3At150.case155
private theorem covered144_156 (j:Fin HighPendingSeed3.regions.size) (l:144≤j.val) (h:j.val<156):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<150
  · exact covered144_150 j l low
  · exact covered150_156 j (by omega) h
private theorem covered156_162 (j:Fin HighPendingSeed3.regions.size) (l:156≤j.val) (h:j.val<162):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At150.case156
  · exact HardFit3At150.case157
  · exact HardFit3At150.case158
  · exact HardFit3At150.case159
  · exact HardFit3At160.case160
  · exact HardFit3At160.case161
private theorem covered162_168 (j:Fin HighPendingSeed3.regions.size) (l:162≤j.val) (h:j.val<168):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At160.case162
  · exact HardFit3At160.case163
  · exact HardFit3At160.case164
  · exact HardFit3At160.case165
  · exact HardFit3At160.case166
  · exact HardFit3At160.case167
private theorem covered156_168 (j:Fin HighPendingSeed3.regions.size) (l:156≤j.val) (h:j.val<168):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<162
  · exact covered156_162 j l low
  · exact covered162_168 j (by omega) h
private theorem covered144_168 (j:Fin HighPendingSeed3.regions.size) (l:144≤j.val) (h:j.val<168):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<156
  · exact covered144_156 j l low
  · exact covered156_168 j (by omega) h
private theorem covered168_174 (j:Fin HighPendingSeed3.regions.size) (l:168≤j.val) (h:j.val<174):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At160.case168
  · exact HardFit3At160.case169
  · exact HardFit3At170.case170
  · exact HardFit3At170.case171
  · exact HardFit3At170.case172
  · exact HardFit3At170.case173
private theorem covered174_180 (j:Fin HighPendingSeed3.regions.size) (l:174≤j.val) (h:j.val<180):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At170.case174
  · exact HardFit3At170.case175
  · exact HardFit3At170.case176
  · exact HardFit3At170.case177
  · exact HardFit3At170.case178
  · exact HardFit3At170.case179
private theorem covered168_180 (j:Fin HighPendingSeed3.regions.size) (l:168≤j.val) (h:j.val<180):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<174
  · exact covered168_174 j l low
  · exact covered174_180 j (by omega) h
private theorem covered180_186 (j:Fin HighPendingSeed3.regions.size) (l:180≤j.val) (h:j.val<186):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At180.case180
  · exact HardFit3At180.case181
  · exact HardFit3At180.case182
  · exact HardFit3At180.case183
  · exact HardFit3At180.case184
  · exact HardFit3At180.case185
private theorem covered186_192 (j:Fin HighPendingSeed3.regions.size) (l:186≤j.val) (h:j.val<192):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit3At180.case186
  · exact HardFit3At180.case187
  · exact HardFit3At180.case188
  · exact HardFit3At180.case189
  · exact HardFit3At190.case190
  · exact HardFit3At190.case191
private theorem covered180_192 (j:Fin HighPendingSeed3.regions.size) (l:180≤j.val) (h:j.val<192):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<186
  · exact covered180_186 j l low
  · exact covered186_192 j (by omega) h
private theorem covered168_192 (j:Fin HighPendingSeed3.regions.size) (l:168≤j.val) (h:j.val<192):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<180
  · exact covered168_180 j l low
  · exact covered180_192 j (by omega) h
private theorem covered144_192 (j:Fin HighPendingSeed3.regions.size) (l:144≤j.val) (h:j.val<192):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<168
  · exact covered144_168 j l low
  · exact covered168_192 j (by omega) h
private theorem covered96_192 (j:Fin HighPendingSeed3.regions.size) (l:96≤j.val) (h:j.val<192):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<144
  · exact covered96_144 j l low
  · exact covered144_192 j (by omega) h
private theorem covered0_192 (j:Fin HighPendingSeed3.regions.size) (l:0≤j.val) (h:j.val<192):Done (2:Fin 18) (HighPendingSeed3.atIndex j):=by
  by_cases low:j.val<96
  · exact covered0_96 j l low
  · exact covered96_192 j (by omega) h
theorem required:HighPendingSeed3.Required:=fun j=>covered0_192 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete3
end Z6969Source2898

-- Source: Research6969.PairReceipts172
section Z6969Source2899
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3440 : List StockPairs.Receipt := [
  ⟨⟨23,24,9,3,17,some 20,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,18,some 18,385979,[MeasuredChoices.test821],[AxisChoices.test1839]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,19,some 19,385979,[MeasuredChoices.test821],[AxisChoices.test1840]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,20,some 20,385979,[MeasuredChoices.test821],[AxisChoices.test1841]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,0,some 0,385979,[MeasuredChoices.test770],[AxisChoices.test1821]⟩,3,separateIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,1,some 1,385979,[MeasuredChoices.test770],[AxisChoices.test1822]⟩,3,separateIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,2,some 2,385979,[MeasuredChoices.test770],[AxisChoices.test1823]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,3,some 3,385979,[MeasuredChoices.test770],[AxisChoices.test1824]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,4,some 4,385979,[MeasuredChoices.test770],[AxisChoices.test1825]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,5,some 5,385979,[MeasuredChoices.test770],[AxisChoices.test1826]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,6,some 6,385979,[MeasuredChoices.test770],[AxisChoices.test1827]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,7,some 7,385979,[MeasuredChoices.test770],[AxisChoices.test1828]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,8,some 8,385979,[MeasuredChoices.test770],[AxisChoices.test1829]⟩,3,markedAxisIntersection⟩]
private theorem paid3440 : StockPairs.checked rows3440 = true := by decide +kernel
theorem route3440 (i : Fin 20) : (rows3440.get i).Done :=
  StockPairs.doneAt paid3440 i

end Research6969.PairReceipts
end Z6969Source2899

-- Source: Research6969.PairReceipts173
section Z6969Source2900
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3460 : List StockPairs.Receipt := [
  ⟨⟨23,24,9,3,13,some 16,9,some 9,385979,[MeasuredChoices.test770],[AxisChoices.test1830]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,10,some 10,385979,[MeasuredChoices.test770],[AxisChoices.test1831]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,11,some 11,385979,[MeasuredChoices.test770],[AxisChoices.test1832]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,12,some 12,385979,[MeasuredChoices.test770],[AxisChoices.test1833]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,13,some 13,385979,[MeasuredChoices.test770],[AxisChoices.test1834]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,14,some 14,385979,[MeasuredChoices.test770],[AxisChoices.test1835]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,15,some 15,385979,[MeasuredChoices.test770],[AxisChoices.test1836]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 16,16,some 16,385979,[MeasuredChoices.test770],[AxisChoices.test1837]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,3,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,4,some 8,0,none,257319,[],[]⟩,3,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨25,27,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,3,markedIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,0,none,385979,[MeasuredChoices.test843],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,0,none,385979,[MeasuredChoices.test831],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,0,none,385979,[MeasuredChoices.test821],[]⟩,3,surfaceIntersection⟩]
private theorem paid3460 : StockPairs.checked rows3460 = true := by decide +kernel
theorem route3460 (i : Fin 20) : (rows3460.get i).Done :=
  StockPairs.doneAt paid3460 i

end Research6969.PairReceipts
end Z6969Source2900

-- Source: Research6969.HardFit4At000
section Z6969Source2901
set_option autoImplicit true
namespace Research6969.HardFit4At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3420 9)
theorem case0: NormalRoute.Done (3:Fin 18) ⟨23,24,9,2,4,some 8⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route3420 8)
theorem case1: NormalRoute.Done (3:Fin 18) ⟨23,24,9,2,9,some 12⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route3420 7)
theorem case2: NormalRoute.Done (3:Fin 18) ⟨23,24,9,2,13,some 16⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route3420 6)
theorem case3: NormalRoute.Done (3:Fin 18) ⟨23,24,9,2,17,some 20⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route3420 5)
theorem case4: NormalRoute.Done (3:Fin 18) ⟨23,24,9,2,21,some 24⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route3420 3)
private def leaf6 := (PairReceipts.route3420 4)
private def weight7 := PairRoute.weight 302619 leaf5 leaf6
theorem case5: NormalRoute.Done (3:Fin 18) ⟨23,24,9,2,25,some 28⟩:=PairRoute.start _ weight7
private def leaf8 := (PairReceipts.route3460 8)
theorem case6: NormalRoute.Done (3:Fin 18) ⟨23,24,9,3,9,some 12⟩:=PairRoute.start _ leaf8
private theorem allAxes42:PairRoute.Done (3:Fin 18) ⟨⟨23,24,9,3,13,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route3440 11),
    (PairReceipts.route3440 12),
    (PairReceipts.route3440 13),
    (PairReceipts.route3440 14),
    (PairReceipts.route3440 15),
    (PairReceipts.route3440 16),
    (PairReceipts.route3440 17),
    (PairReceipts.route3440 18),
    (PairReceipts.route3440 19),
    (PairReceipts.route3460 0),
    (PairReceipts.route3460 1),
    (PairReceipts.route3460 2),
    (PairReceipts.route3460 3),
    (PairReceipts.route3460 4),
    (PairReceipts.route3460 5),
    (PairReceipts.route3460 6),
    (PairReceipts.route3460 7),
    trivial⟩)
theorem case7: NormalRoute.Done (3:Fin 18) ⟨23,24,9,3,13,some 16⟩:=PairRoute.start _ allAxes42
private theorem allAxes84:PairRoute.Done (3:Fin 18) ⟨⟨23,24,9,3,17,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route3420 10),
    (PairReceipts.route3420 11),
    (PairReceipts.route3420 12),
    (PairReceipts.route3420 13),
    (PairReceipts.route3420 14),
    (PairReceipts.route3420 15),
    (PairReceipts.route3420 16),
    (PairReceipts.route3420 17),
    (PairReceipts.route3420 18),
    (PairReceipts.route3420 19),
    (PairReceipts.route3440 0),
    (PairReceipts.route3440 1),
    (PairReceipts.route3440 2),
    (PairReceipts.route3440 3),
    (PairReceipts.route3440 4),
    (PairReceipts.route3440 5),
    (PairReceipts.route3440 6),
    (PairReceipts.route3440 7),
    (PairReceipts.route3440 8),
    (PairReceipts.route3440 9),
    (PairReceipts.route3440 10),
    trivial⟩)
theorem case8: NormalRoute.Done (3:Fin 18) ⟨23,24,9,3,17,some 20⟩:=PairRoute.start _ allAxes84
private def leaf85 := (PairReceipts.route3460 15)
theorem case9: NormalRoute.Done (3:Fin 18) ⟨25,27,9,2,4,some 8⟩:=PairRoute.start _ leaf85
end Research6969.HardFit4At000
end Z6969Source2901

-- Source: Research6969.PairReceipts174
section Z6969Source2902
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3480 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,15,some 16,0,none,385979,[MeasuredChoices.test797],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,3,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,4,some 8,0,none,257319,[],[]⟩,3,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨28,32,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,23,some 24,0,none,385979,[MeasuredChoices.test896],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,21,some 22,0,none,385979,[MeasuredChoices.test869],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,19,some 20,0,none,385979,[MeasuredChoices.test843],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,17,some 18,0,none,385979,[MeasuredChoices.test821],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,15,some 16,0,none,385979,[MeasuredChoices.test797],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,49,some 64,0,none,257319,[MeasuredChoices.test62],[]⟩,3,markedIntersection⟩]
private theorem paid3480 : StockPairs.checked rows3480 = true := by decide +kernel
theorem route3480 (i : Fin 20) : (rows3480.get i).Done :=
  StockPairs.doneAt paid3480 i

end Research6969.PairReceipts
end Z6969Source2902

-- Source: Research6969.HardFit4At010
section Z6969Source2903
set_option autoImplicit true
namespace Research6969.HardFit4At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3460 14)
theorem case10: NormalRoute.Done (3:Fin 18) ⟨25,27,9,2,9,some 12⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route3460 13)
theorem case11: NormalRoute.Done (3:Fin 18) ⟨25,27,9,2,13,some 16⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route3460 12)
theorem case12: NormalRoute.Done (3:Fin 18) ⟨25,27,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route3460 11)
theorem case13: NormalRoute.Done (3:Fin 18) ⟨25,27,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route3460 9)
private def leaf5 := (PairReceipts.route3460 10)
private def weight6 := PairRoute.weight 302619 leaf4 leaf5
theorem case14: NormalRoute.Done (3:Fin 18) ⟨25,27,9,2,25,some 28⟩:=PairRoute.start _ weight6
private def leaf7 := (PairReceipts.route3480 2)
theorem case15: NormalRoute.Done (3:Fin 18) ⟨25,27,9,3,9,some 12⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route3480 1)
theorem case16: NormalRoute.Done (3:Fin 18) ⟨25,27,9,3,13,some 14⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route3480 0)
theorem case17: NormalRoute.Done (3:Fin 18) ⟨25,27,9,3,15,some 16⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route3460 19)
theorem case18: NormalRoute.Done (3:Fin 18) ⟨25,27,9,3,17,some 17⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route3460 18)
theorem case19: NormalRoute.Done (3:Fin 18) ⟨25,27,9,3,18,some 18⟩:=PairRoute.start _ leaf11
end Research6969.HardFit4At010
end Z6969Source2903

-- Source: Research6969.HardFit4At020
section Z6969Source2904
set_option autoImplicit true
namespace Research6969.HardFit4At020
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3460 17)
theorem case20: NormalRoute.Done (3:Fin 18) ⟨25,27,9,3,19,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route3460 16)
theorem case21: NormalRoute.Done (3:Fin 18) ⟨25,27,9,3,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route3480 10)
theorem case22: NormalRoute.Done (3:Fin 18) ⟨28,32,9,2,4,some 8⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route3480 9)
theorem case23: NormalRoute.Done (3:Fin 18) ⟨28,32,9,2,9,some 12⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route3480 8)
theorem case24: NormalRoute.Done (3:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route3480 7)
theorem case25: NormalRoute.Done (3:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route3480 6)
theorem case26: NormalRoute.Done (3:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route3480 4)
private def leaf8 := (PairReceipts.route3480 5)
private def weight9 := PairRoute.weight 302619 leaf7 leaf8
theorem case27: NormalRoute.Done (3:Fin 18) ⟨28,32,9,2,25,some 28⟩:=PairRoute.start _ weight9
private def leaf10 := (PairReceipts.route3480 3)
theorem case28: NormalRoute.Done (3:Fin 18) ⟨28,32,9,2,29,some 32⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route3480 18)
theorem case29: NormalRoute.Done (3:Fin 18) ⟨28,32,9,3,9,some 12⟩:=PairRoute.start _ leaf11
end Research6969.HardFit4At020
end Z6969Source2904

-- Source: Research6969.PairReceipts175
section Z6969Source2905
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3500 : List StockPairs.Receipt := [
  ⟨⟨33,40,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,3,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,4,some 8,0,none,257319,[],[]⟩,3,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨33,40,9,3,33,some 39,0,none,385979,[MeasuredChoices.test1029],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,40,some 40,0,none,385979,[MeasuredChoices.test1120],[]⟩,3,markedIntersection⟩,
  ⟨⟨33,40,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,23,some 24,0,none,385979,[MeasuredChoices.test896],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,21,some 22,0,none,385979,[MeasuredChoices.test869],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,19,some 20,0,none,385979,[MeasuredChoices.test843],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,17,some 18,0,none,385979,[MeasuredChoices.test821],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,15,some 16,0,none,385979,[MeasuredChoices.test797],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,0,some 0,257319,[MeasuredChoices.test62],[]⟩,3,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,1,some 1,257319,[MeasuredChoices.test62],[]⟩,3,separateIntersection⟩]
private theorem paid3500 : StockPairs.checked rows3500 = true := by decide +kernel
theorem route3500 (i : Fin 21) : (rows3500.get i).Done :=
  StockPairs.doneAt paid3500 i

end Research6969.PairReceipts
end Z6969Source2905

-- Source: Research6969.HardFit4At030
section Z6969Source2906
set_option autoImplicit true
namespace Research6969.HardFit4At030
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3480 17)
theorem case30: NormalRoute.Done (3:Fin 18) ⟨28,32,9,3,13,some 14⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route3480 16)
theorem case31: NormalRoute.Done (3:Fin 18) ⟨28,32,9,3,15,some 16⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route3480 15)
theorem case32: NormalRoute.Done (3:Fin 18) ⟨28,32,9,3,17,some 18⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route3480 14)
theorem case33: NormalRoute.Done (3:Fin 18) ⟨28,32,9,3,19,some 20⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route3480 13)
theorem case34: NormalRoute.Done (3:Fin 18) ⟨28,32,9,3,21,some 22⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route3480 12)
theorem case35: NormalRoute.Done (3:Fin 18) ⟨28,32,9,3,23,some 24⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route3480 11)
theorem case36: NormalRoute.Done (3:Fin 18) ⟨28,32,9,3,25,some 28⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route3500 7)
theorem case37: NormalRoute.Done (3:Fin 18) ⟨33,40,9,2,4,some 8⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route3500 6)
theorem case38: NormalRoute.Done (3:Fin 18) ⟨33,40,9,2,9,some 12⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route3500 5)
theorem case39: NormalRoute.Done (3:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf9
end Research6969.HardFit4At030
end Z6969Source2906

-- Source: Research6969.HardFit4At040
section Z6969Source2907
set_option autoImplicit true
namespace Research6969.HardFit4At040
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3500 4)
theorem case40: NormalRoute.Done (3:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route3500 3)
theorem case41: NormalRoute.Done (3:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route3500 1)
private def leaf3 := (PairReceipts.route3500 2)
private def weight4 := PairRoute.weight 302619 leaf2 leaf3
theorem case42: NormalRoute.Done (3:Fin 18) ⟨33,40,9,2,25,some 28⟩:=PairRoute.start _ weight4
private def leaf5 := (PairReceipts.route3500 0)
theorem case43: NormalRoute.Done (3:Fin 18) ⟨33,40,9,2,29,some 32⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route3480 19)
theorem case44: NormalRoute.Done (3:Fin 18) ⟨33,40,9,2,49,some 64⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route3500 18)
theorem case45: NormalRoute.Done (3:Fin 18) ⟨33,40,9,3,9,some 12⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route3500 17)
theorem case46: NormalRoute.Done (3:Fin 18) ⟨33,40,9,3,13,some 14⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route3500 16)
theorem case47: NormalRoute.Done (3:Fin 18) ⟨33,40,9,3,15,some 16⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route3500 15)
theorem case48: NormalRoute.Done (3:Fin 18) ⟨33,40,9,3,17,some 18⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route3500 14)
theorem case49: NormalRoute.Done (3:Fin 18) ⟨33,40,9,3,19,some 20⟩:=PairRoute.start _ leaf11
end Research6969.HardFit4At040
end Z6969Source2907

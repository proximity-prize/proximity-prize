import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0940
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0935
import ProximityPrize.SubmissionLower.Z6969Pack0936
import ProximityPrize.SubmissionLower.Z6969Pack0937
import ProximityPrize.SubmissionLower.Z6969Pack0938
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0669

set_option Elab.async false

-- Source: Research6969.HardFit1At210
section Z6969Source2651
set_option autoImplicit true
namespace Research6969.HardFit1At210
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route940 10)
theorem case210: NormalRoute.Done (0:Fin 18) ⟨64,721,12,1,2,some 3⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route940 9)
theorem case211: NormalRoute.Done (0:Fin 18) ⟨64,721,12,1,4,some 8⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route940 8)
theorem case212: NormalRoute.Done (0:Fin 18) ⟨64,721,12,1,9,some 12⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route940 7)
theorem case213: NormalRoute.Done (0:Fin 18) ⟨64,721,12,1,13,some 16⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route940 6)
theorem case214: NormalRoute.Done (0:Fin 18) ⟨64,721,12,1,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route940 5)
theorem case215: NormalRoute.Done (0:Fin 18) ⟨64,721,12,1,21,some 24⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route940 4)
theorem case216: NormalRoute.Done (0:Fin 18) ⟨64,721,12,1,25,some 28⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route940 3)
theorem case217: NormalRoute.Done (0:Fin 18) ⟨64,721,12,1,29,some 32⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route940 2)
theorem case218: NormalRoute.Done (0:Fin 18) ⟨64,721,12,1,33,some 40⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route940 1)
theorem case219: NormalRoute.Done (0:Fin 18) ⟨64,721,12,1,41,some 48⟩:=PairRoute.start _ leaf9
end Research6969.HardFit1At210
end Z6969Source2651

-- Source: Research6969.PairReceipts048
section Z6969Source2652
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows960 : List StockPairs.Receipt := [
  ⟨⟨64,721,12,2,25,some 28,0,none,302619,[MeasuredChoices.test166,MeasuredChoices.test167],[]⟩,0,surfaceWhole⟩,
  ⟨⟨64,721,12,2,21,some 24,0,none,257319,[MeasuredChoices.test25,MeasuredChoices.test26],[]⟩,0,surfaceWhole⟩,
  ⟨⟨64,721,12,2,17,some 20,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨64,721,12,2,13,some 16,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨64,721,12,2,9,some 12,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨64,721,12,2,4,some 8,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨64,721,12,2,2,some 3,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨64,721,12,2,1,some 1,0,none,257319,[],[]⟩,0,⟨.surface,.whole,.surface,0⟩⟩,
  ⟨⟨64,721,12,2,0,some 0,0,none,257319,[],[]⟩,0,surfaceWhole⟩,
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,9,some 12,0,none,257319,[],[]⟩,9,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,9,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,9,surfaceIntersection⟩]
private theorem paid960 : StockPairs.checked rows960 = true := by decide +kernel
theorem route960 (i : Fin 20) : (rows960.get i).Done :=
  StockPairs.doneAt paid960 i

end Research6969.PairReceipts
end Z6969Source2652

-- Source: Research6969.HardFit1At220
section Z6969Source2653
set_option autoImplicit true
namespace Research6969.HardFit1At220
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route940 0)
theorem case220: NormalRoute.Done (0:Fin 18) ⟨64,721,12,1,49,some 64⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route960 8)
theorem case221: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,0,some 0⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route960 7)
theorem case222: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,1,some 1⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route960 6)
theorem case223: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,2,some 3⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route960 5)
theorem case224: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,4,some 8⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route960 4)
theorem case225: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,9,some 12⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route960 3)
theorem case226: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,13,some 16⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route960 2)
theorem case227: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,17,some 20⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route960 1)
theorem case228: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,21,some 24⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route940 19)
private def leaf10 := (PairReceipts.route960 0)
private def weight11 := PairRoute.weight 302619 leaf9 leaf10
theorem case229: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,25,some 28⟩:=PairRoute.start _ weight11
end Research6969.HardFit1At220
end Z6969Source2653

-- Source: Research6969.HardFit1At230
section Z6969Source2654
set_option autoImplicit true
namespace Research6969.HardFit1At230
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route940 18)
theorem case230: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,29,some 32⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route940 17)
theorem case231: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,33,some 36⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route940 16)
theorem case232: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,37,some 40⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route940 14)
private def leaf4 := (PairReceipts.route940 15)
private def weight5 := PairRoute.weight 291368 leaf3 leaf4
theorem case233: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,41,some 48⟩:=PairRoute.start _ weight5
private def leaf6 := (PairReceipts.route940 13)
theorem case234: NormalRoute.Done (0:Fin 18) ⟨64,721,12,2,49,some 52⟩:=PairRoute.start _ leaf6
end Research6969.HardFit1At230
end Z6969Source2654

-- Source: Research6969.HardComplete1
section Z6969Source2655
set_option autoImplicit true
namespace Research6969.HardComplete1
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_7 (j:Fin HighPendingSeed1.regions.size) (l:0≤j.val) (h:j.val<7):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At000.case0
  · exact HardFit1At000.case1
  · exact HardFit1At000.case2
  · exact HardFit1At000.case3
  · exact HardFit1At000.case4
  · exact HardFit1At000.case5
  · exact HardFit1At000.case6
private theorem covered7_14 (j:Fin HighPendingSeed1.regions.size) (l:7≤j.val) (h:j.val<14):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At000.case7
  · exact HardFit1At000.case8
  · exact HardFit1At000.case9
  · exact HardFit1At010.case10
  · exact HardFit1At010.case11
  · exact HardFit1At010.case12
  · exact HardFit1At010.case13
private theorem covered0_14 (j:Fin HighPendingSeed1.regions.size) (l:0≤j.val) (h:j.val<14):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<7
  · exact covered0_7 j l low
  · exact covered7_14 j (by omega) h
private theorem covered14_21 (j:Fin HighPendingSeed1.regions.size) (l:14≤j.val) (h:j.val<21):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At010.case14
  · exact HardFit1At010.case15
  · exact HardFit1At010.case16
  · exact HardFit1At010.case17
  · exact HardFit1At010.case18
  · exact HardFit1At010.case19
  · exact HardFit1At020.case20
private theorem covered21_29 (j:Fin HighPendingSeed1.regions.size) (l:21≤j.val) (h:j.val<29):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At020.case21
  · exact HardFit1At020.case22
  · exact HardFit1At020.case23
  · exact HardFit1At020.case24
  · exact HardFit1At020.case25
  · exact HardFit1At020.case26
  · exact HardFit1At020.case27
  · exact HardFit1At020.case28
private theorem covered14_29 (j:Fin HighPendingSeed1.regions.size) (l:14≤j.val) (h:j.val<29):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<21
  · exact covered14_21 j l low
  · exact covered21_29 j (by omega) h
private theorem covered0_29 (j:Fin HighPendingSeed1.regions.size) (l:0≤j.val) (h:j.val<29):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<14
  · exact covered0_14 j l low
  · exact covered14_29 j (by omega) h
private theorem covered29_36 (j:Fin HighPendingSeed1.regions.size) (l:29≤j.val) (h:j.val<36):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At020.case29
  · exact HardFit1At030.case30
  · exact HardFit1At030.case31
  · exact HardFit1At030.case32
  · exact HardFit1At030.case33
  · exact HardFit1At030.case34
  · exact HardFit1At030.case35
private theorem covered36_43 (j:Fin HighPendingSeed1.regions.size) (l:36≤j.val) (h:j.val<43):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At030.case36
  · exact HardFit1At030.case37
  · exact HardFit1At030.case38
  · exact HardFit1At030.case39
  · exact HardFit1At040.case40
  · exact HardFit1At040.case41
  · exact HardFit1At040.case42
private theorem covered29_43 (j:Fin HighPendingSeed1.regions.size) (l:29≤j.val) (h:j.val<43):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<36
  · exact covered29_36 j l low
  · exact covered36_43 j (by omega) h
private theorem covered43_50 (j:Fin HighPendingSeed1.regions.size) (l:43≤j.val) (h:j.val<50):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At040.case43
  · exact HardFit1At040.case44
  · exact HardFit1At040.case45
  · exact HardFit1At040.case46
  · exact HardFit1At040.case47
  · exact HardFit1At040.case48
  · exact HardFit1At040.case49
private theorem covered50_58 (j:Fin HighPendingSeed1.regions.size) (l:50≤j.val) (h:j.val<58):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At050.case50
  · exact HardFit1At050.case51
  · exact HardFit1At050.case52
  · exact HardFit1At050.case53
  · exact HardFit1At050.case54
  · exact HardFit1At050.case55
  · exact HardFit1At050.case56
  · exact HardFit1At050.case57
private theorem covered43_58 (j:Fin HighPendingSeed1.regions.size) (l:43≤j.val) (h:j.val<58):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<50
  · exact covered43_50 j l low
  · exact covered50_58 j (by omega) h
private theorem covered29_58 (j:Fin HighPendingSeed1.regions.size) (l:29≤j.val) (h:j.val<58):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<43
  · exact covered29_43 j l low
  · exact covered43_58 j (by omega) h
private theorem covered0_58 (j:Fin HighPendingSeed1.regions.size) (l:0≤j.val) (h:j.val<58):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<29
  · exact covered0_29 j l low
  · exact covered29_58 j (by omega) h
private theorem covered58_65 (j:Fin HighPendingSeed1.regions.size) (l:58≤j.val) (h:j.val<65):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At050.case58
  · exact HardFit1At050.case59
  · exact HardFit1At060.case60
  · exact HardFit1At060.case61
  · exact HardFit1At060.case62
  · exact HardFit1At060.case63
  · exact HardFit1At060.case64
private theorem covered65_72 (j:Fin HighPendingSeed1.regions.size) (l:65≤j.val) (h:j.val<72):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At060.case65
  · exact HardFit1At060.case66
  · exact HardFit1At060.case67
  · exact HardFit1At060.case68
  · exact HardFit1At060.case69
  · exact HardFit1At070.case70
  · exact HardFit1At070.case71
private theorem covered58_72 (j:Fin HighPendingSeed1.regions.size) (l:58≤j.val) (h:j.val<72):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<65
  · exact covered58_65 j l low
  · exact covered65_72 j (by omega) h
private theorem covered72_79 (j:Fin HighPendingSeed1.regions.size) (l:72≤j.val) (h:j.val<79):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At070.case72
  · exact HardFit1At070.case73
  · exact HardFit1At070.case74
  · exact HardFit1At070.case75
  · exact HardFit1At070.case76
  · exact HardFit1At070.case77
  · exact HardFit1At070.case78
private theorem covered79_87 (j:Fin HighPendingSeed1.regions.size) (l:79≤j.val) (h:j.val<87):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At070.case79
  · exact HardFit1At080.case80
  · exact HardFit1At080.case81
  · exact HardFit1At080.case82
  · exact HardFit1At080.case83
  · exact HardFit1At080.case84
  · exact HardFit1At080.case85
  · exact HardFit1At080.case86
private theorem covered72_87 (j:Fin HighPendingSeed1.regions.size) (l:72≤j.val) (h:j.val<87):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<79
  · exact covered72_79 j l low
  · exact covered79_87 j (by omega) h
private theorem covered58_87 (j:Fin HighPendingSeed1.regions.size) (l:58≤j.val) (h:j.val<87):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<72
  · exact covered58_72 j l low
  · exact covered72_87 j (by omega) h
private theorem covered87_94 (j:Fin HighPendingSeed1.regions.size) (l:87≤j.val) (h:j.val<94):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At080.case87
  · exact HardFit1At080.case88
  · exact HardFit1At080.case89
  · exact HardFit1At090.case90
  · exact HardFit1At090.case91
  · exact HardFit1At090.case92
  · exact HardFit1At090.case93
private theorem covered94_102 (j:Fin HighPendingSeed1.regions.size) (l:94≤j.val) (h:j.val<102):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At090.case94
  · exact HardFit1At090.case95
  · exact HardFit1At090.case96
  · exact HardFit1At090.case97
  · exact HardFit1At090.case98
  · exact HardFit1At090.case99
  · exact HardFit1At100.case100
  · exact HardFit1At100.case101
private theorem covered87_102 (j:Fin HighPendingSeed1.regions.size) (l:87≤j.val) (h:j.val<102):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<94
  · exact covered87_94 j l low
  · exact covered94_102 j (by omega) h
private theorem covered102_109 (j:Fin HighPendingSeed1.regions.size) (l:102≤j.val) (h:j.val<109):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At100.case102
  · exact HardFit1At100.case103
  · exact HardFit1At100.case104
  · exact HardFit1At100.case105
  · exact HardFit1At100.case106
  · exact HardFit1At100.case107
  · exact HardFit1At100.case108
private theorem covered109_117 (j:Fin HighPendingSeed1.regions.size) (l:109≤j.val) (h:j.val<117):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At100.case109
  · exact HardFit1At110.case110
  · exact HardFit1At110.case111
  · exact HardFit1At110.case112
  · exact HardFit1At110.case113
  · exact HardFit1At110.case114
  · exact HardFit1At110.case115
  · exact HardFit1At110.case116
private theorem covered102_117 (j:Fin HighPendingSeed1.regions.size) (l:102≤j.val) (h:j.val<117):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<109
  · exact covered102_109 j l low
  · exact covered109_117 j (by omega) h
private theorem covered87_117 (j:Fin HighPendingSeed1.regions.size) (l:87≤j.val) (h:j.val<117):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<102
  · exact covered87_102 j l low
  · exact covered102_117 j (by omega) h
private theorem covered58_117 (j:Fin HighPendingSeed1.regions.size) (l:58≤j.val) (h:j.val<117):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<87
  · exact covered58_87 j l low
  · exact covered87_117 j (by omega) h
private theorem covered0_117 (j:Fin HighPendingSeed1.regions.size) (l:0≤j.val) (h:j.val<117):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<58
  · exact covered0_58 j l low
  · exact covered58_117 j (by omega) h
private theorem covered117_124 (j:Fin HighPendingSeed1.regions.size) (l:117≤j.val) (h:j.val<124):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At110.case117
  · exact HardFit1At110.case118
  · exact HardFit1At110.case119
  · exact HardFit1At120.case120
  · exact HardFit1At120.case121
  · exact HardFit1At120.case122
  · exact HardFit1At120.case123
private theorem covered124_131 (j:Fin HighPendingSeed1.regions.size) (l:124≤j.val) (h:j.val<131):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At120.case124
  · exact HardFit1At120.case125
  · exact HardFit1At120.case126
  · exact HardFit1At120.case127
  · exact HardFit1At120.case128
  · exact HardFit1At120.case129
  · exact HardFit1At130.case130
private theorem covered117_131 (j:Fin HighPendingSeed1.regions.size) (l:117≤j.val) (h:j.val<131):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<124
  · exact covered117_124 j l low
  · exact covered124_131 j (by omega) h
private theorem covered131_138 (j:Fin HighPendingSeed1.regions.size) (l:131≤j.val) (h:j.val<138):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At130.case131
  · exact HardFit1At130.case132
  · exact HardFit1At130.case133
  · exact HardFit1At130.case134
  · exact HardFit1At130.case135
  · exact HardFit1At130.case136
  · exact HardFit1At130.case137
private theorem covered138_146 (j:Fin HighPendingSeed1.regions.size) (l:138≤j.val) (h:j.val<146):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At130.case138
  · exact HardFit1At130.case139
  · exact HardFit1At140.case140
  · exact HardFit1At140.case141
  · exact HardFit1At140.case142
  · exact HardFit1At140.case143
  · exact HardFit1At140.case144
  · exact HardFit1At140.case145
private theorem covered131_146 (j:Fin HighPendingSeed1.regions.size) (l:131≤j.val) (h:j.val<146):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<138
  · exact covered131_138 j l low
  · exact covered138_146 j (by omega) h
private theorem covered117_146 (j:Fin HighPendingSeed1.regions.size) (l:117≤j.val) (h:j.val<146):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<131
  · exact covered117_131 j l low
  · exact covered131_146 j (by omega) h
private theorem covered146_153 (j:Fin HighPendingSeed1.regions.size) (l:146≤j.val) (h:j.val<153):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At140.case146
  · exact HardFit1At140.case147
  · exact HardFit1At140.case148
  · exact HardFit1At140.case149
  · exact HardFit1At150.case150
  · exact HardFit1At150.case151
  · exact HardFit1At150.case152
private theorem covered153_161 (j:Fin HighPendingSeed1.regions.size) (l:153≤j.val) (h:j.val<161):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At150.case153
  · exact HardFit1At150.case154
  · exact HardFit1At150.case155
  · exact HardFit1At150.case156
  · exact HardFit1At150.case157
  · exact HardFit1At150.case158
  · exact HardFit1At150.case159
  · exact HardFit1At160.case160
private theorem covered146_161 (j:Fin HighPendingSeed1.regions.size) (l:146≤j.val) (h:j.val<161):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<153
  · exact covered146_153 j l low
  · exact covered153_161 j (by omega) h
private theorem covered161_168 (j:Fin HighPendingSeed1.regions.size) (l:161≤j.val) (h:j.val<168):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At160.case161
  · exact HardFit1At160.case162
  · exact HardFit1At160.case163
  · exact HardFit1At160.case164
  · exact HardFit1At160.case165
  · exact HardFit1At160.case166
  · exact HardFit1At160.case167
private theorem covered168_176 (j:Fin HighPendingSeed1.regions.size) (l:168≤j.val) (h:j.val<176):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At160.case168
  · exact HardFit1At160.case169
  · exact HardFit1At170.case170
  · exact HardFit1At170.case171
  · exact HardFit1At170.case172
  · exact HardFit1At170.case173
  · exact HardFit1At170.case174
  · exact HardFit1At170.case175
private theorem covered161_176 (j:Fin HighPendingSeed1.regions.size) (l:161≤j.val) (h:j.val<176):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<168
  · exact covered161_168 j l low
  · exact covered168_176 j (by omega) h
private theorem covered146_176 (j:Fin HighPendingSeed1.regions.size) (l:146≤j.val) (h:j.val<176):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<161
  · exact covered146_161 j l low
  · exact covered161_176 j (by omega) h
private theorem covered117_176 (j:Fin HighPendingSeed1.regions.size) (l:117≤j.val) (h:j.val<176):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<146
  · exact covered117_146 j l low
  · exact covered146_176 j (by omega) h
private theorem covered176_183 (j:Fin HighPendingSeed1.regions.size) (l:176≤j.val) (h:j.val<183):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At170.case176
  · exact HardFit1At170.case177
  · exact HardFit1At170.case178
  · exact HardFit1At170.case179
  · exact HardFit1At180.case180
  · exact HardFit1At180.case181
  · exact HardFit1At180.case182
private theorem covered183_190 (j:Fin HighPendingSeed1.regions.size) (l:183≤j.val) (h:j.val<190):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At180.case183
  · exact HardFit1At180.case184
  · exact HardFit1At180.case185
  · exact HardFit1At180.case186
  · exact HardFit1At180.case187
  · exact HardFit1At180.case188
  · exact HardFit1At180.case189
private theorem covered176_190 (j:Fin HighPendingSeed1.regions.size) (l:176≤j.val) (h:j.val<190):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<183
  · exact covered176_183 j l low
  · exact covered183_190 j (by omega) h
private theorem covered190_197 (j:Fin HighPendingSeed1.regions.size) (l:190≤j.val) (h:j.val<197):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At190.case190
  · exact HardFit1At190.case191
  · exact HardFit1At190.case192
  · exact HardFit1At190.case193
  · exact HardFit1At190.case194
  · exact HardFit1At190.case195
  · exact HardFit1At190.case196
private theorem covered197_205 (j:Fin HighPendingSeed1.regions.size) (l:197≤j.val) (h:j.val<205):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At190.case197
  · exact HardFit1At190.case198
  · exact HardFit1At190.case199
  · exact HardFit1At200.case200
  · exact HardFit1At200.case201
  · exact HardFit1At200.case202
  · exact HardFit1At200.case203
  · exact HardFit1At200.case204
private theorem covered190_205 (j:Fin HighPendingSeed1.regions.size) (l:190≤j.val) (h:j.val<205):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<197
  · exact covered190_197 j l low
  · exact covered197_205 j (by omega) h
private theorem covered176_205 (j:Fin HighPendingSeed1.regions.size) (l:176≤j.val) (h:j.val<205):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<190
  · exact covered176_190 j l low
  · exact covered190_205 j (by omega) h
private theorem covered205_212 (j:Fin HighPendingSeed1.regions.size) (l:205≤j.val) (h:j.val<212):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At200.case205
  · exact HardFit1At200.case206
  · exact HardFit1At200.case207
  · exact HardFit1At200.case208
  · exact HardFit1At200.case209
  · exact HardFit1At210.case210
  · exact HardFit1At210.case211
private theorem covered212_220 (j:Fin HighPendingSeed1.regions.size) (l:212≤j.val) (h:j.val<220):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At210.case212
  · exact HardFit1At210.case213
  · exact HardFit1At210.case214
  · exact HardFit1At210.case215
  · exact HardFit1At210.case216
  · exact HardFit1At210.case217
  · exact HardFit1At210.case218
  · exact HardFit1At210.case219
private theorem covered205_220 (j:Fin HighPendingSeed1.regions.size) (l:205≤j.val) (h:j.val<220):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<212
  · exact covered205_212 j l low
  · exact covered212_220 j (by omega) h
private theorem covered220_227 (j:Fin HighPendingSeed1.regions.size) (l:220≤j.val) (h:j.val<227):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At220.case220
  · exact HardFit1At220.case221
  · exact HardFit1At220.case222
  · exact HardFit1At220.case223
  · exact HardFit1At220.case224
  · exact HardFit1At220.case225
  · exact HardFit1At220.case226
private theorem covered227_235 (j:Fin HighPendingSeed1.regions.size) (l:227≤j.val) (h:j.val<235):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit1At220.case227
  · exact HardFit1At220.case228
  · exact HardFit1At220.case229
  · exact HardFit1At230.case230
  · exact HardFit1At230.case231
  · exact HardFit1At230.case232
  · exact HardFit1At230.case233
  · exact HardFit1At230.case234
private theorem covered220_235 (j:Fin HighPendingSeed1.regions.size) (l:220≤j.val) (h:j.val<235):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<227
  · exact covered220_227 j l low
  · exact covered227_235 j (by omega) h
private theorem covered205_235 (j:Fin HighPendingSeed1.regions.size) (l:205≤j.val) (h:j.val<235):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<220
  · exact covered205_220 j l low
  · exact covered220_235 j (by omega) h
private theorem covered176_235 (j:Fin HighPendingSeed1.regions.size) (l:176≤j.val) (h:j.val<235):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<205
  · exact covered176_205 j l low
  · exact covered205_235 j (by omega) h
private theorem covered117_235 (j:Fin HighPendingSeed1.regions.size) (l:117≤j.val) (h:j.val<235):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<176
  · exact covered117_176 j l low
  · exact covered176_235 j (by omega) h
private theorem covered0_235 (j:Fin HighPendingSeed1.regions.size) (l:0≤j.val) (h:j.val<235):Done (0:Fin 18) (HighPendingSeed1.atIndex j):=by
  by_cases low:j.val<117
  · exact covered0_117 j l low
  · exact covered117_235 j (by omega) h
theorem required:HighPendingSeed1.Required:=fun j=>covered0_235 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete1
end Z6969Source2655

-- Source: Research6969.PairReceipts055
section Z6969Source2656
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1100 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,15,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,15,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,15,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,17,some 20,0,none,257319,[],[]⟩,15,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,13,some 16,0,none,257319,[],[]⟩,15,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,16,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,16,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,16,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,16,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,16,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,16,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,17,some 20,0,none,257319,[],[]⟩,16,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,17,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,17,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,17,surfaceIntersection⟩,
  ⟨⟨64,581,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,17,surfaceIntersection⟩,
  ⟨⟨64,581,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,17,surfaceIntersection⟩,
  ⟨⟨64,581,12,2,17,some 20,0,none,257319,[],[]⟩,17,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨23,24,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,1,surfaceWhole⟩,
  ⟨⟨23,24,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,1,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩]
private theorem paid1100 : StockPairs.checked rows1100 = true := by decide +kernel
theorem route1100 (i : Fin 20) : (rows1100.get i).Done :=
  StockPairs.doneAt paid1100 i

end Research6969.PairReceipts
end Z6969Source2656

-- Source: Research6969.PairReceipts056
section Z6969Source2657
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1120 : List StockPairs.Receipt := [
  ⟨⟨23,24,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,1,surfaceWhole⟩,
  ⟨⟨23,24,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,1,surfaceWhole⟩,
  ⟨⟨23,24,9,2,17,some 20,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨23,24,9,2,13,some 16,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨23,24,9,2,9,some 12,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨23,24,9,2,4,some 8,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨23,24,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,1,markedWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩]
private theorem paid1120 : StockPairs.checked rows1120 = true := by decide +kernel
theorem route1120 (i : Fin 20) : (rows1120.get i).Done :=
  StockPairs.doneAt paid1120 i

end Research6969.PairReceipts
end Z6969Source2657

-- Source: Research6969.PairReceipts059
section Z6969Source2658
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1180 : List StockPairs.Receipt := [
  ⟨⟨23,24,9,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,0,some 0,385979,[MeasuredChoices.test785],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,1,some 1,385979,[MeasuredChoices.test785],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,2,some 2,385979,[MeasuredChoices.test785],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,3,some 3,385979,[MeasuredChoices.test785],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,4,some 4,385979,[MeasuredChoices.test785],[AxisChoices.test1825]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,5,some 5,385979,[MeasuredChoices.test785],[AxisChoices.test1826]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,6,some 6,385979,[MeasuredChoices.test785],[AxisChoices.test1827]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,7,some 7,385979,[MeasuredChoices.test785],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,8,some 8,385979,[MeasuredChoices.test785],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,9,some 9,385979,[MeasuredChoices.test785],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,10,some 10,385979,[MeasuredChoices.test785],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,11,some 11,385979,[MeasuredChoices.test785],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,12,some 12,385979,[MeasuredChoices.test785],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,13,some 13,385979,[MeasuredChoices.test785],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,14,some 14,14,some 14,385979,[MeasuredChoices.test785],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,1,surfaceWhole⟩,
  ⟨⟨23,24,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,1,surfaceWhole⟩,
  ⟨⟨23,24,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,1,surfaceWhole⟩,
  ⟨⟨25,27,9,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,1,markedWhole⟩]
private theorem paid1180 : StockPairs.checked rows1180 = true := by decide +kernel
theorem route1180 (i : Fin 20) : (rows1180.get i).Done :=
  StockPairs.doneAt paid1180 i

end Research6969.PairReceipts
end Z6969Source2658

-- Source: Research6969.HardFit2At000
section Z6969Source2659
set_option autoImplicit true
namespace Research6969.HardFit2At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1120 5)
theorem case0: NormalRoute.Done (1:Fin 18) ⟨23,24,9,2,4,some 8⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1120 4)
theorem case1: NormalRoute.Done (1:Fin 18) ⟨23,24,9,2,9,some 12⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1120 3)
theorem case2: NormalRoute.Done (1:Fin 18) ⟨23,24,9,2,13,some 16⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1120 2)
theorem case3: NormalRoute.Done (1:Fin 18) ⟨23,24,9,2,17,some 20⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1120 1)
theorem case4: NormalRoute.Done (1:Fin 18) ⟨23,24,9,2,21,some 24⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1100 19)
private def leaf6 := (PairReceipts.route1120 0)
private def weight7 := PairRoute.weight 302619 leaf5 leaf6
theorem case5: NormalRoute.Done (1:Fin 18) ⟨23,24,9,2,25,some 28⟩:=PairRoute.start _ weight7
private def leaf8 := (PairReceipts.route1100 18)
theorem case6: NormalRoute.Done (1:Fin 18) ⟨23,24,9,2,29,some 32⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route1180 18)
theorem case7: NormalRoute.Done (1:Fin 18) ⟨23,24,9,3,4,some 8⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route1180 17)
theorem case8: NormalRoute.Done (1:Fin 18) ⟨23,24,9,3,9,some 12⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route1180 16)
theorem case9: NormalRoute.Done (1:Fin 18) ⟨23,24,9,3,13,some 13⟩:=PairRoute.start _ leaf11
end Research6969.HardFit2At000
end Z6969Source2659

-- Source: Research6969.PairReceipts057
section Z6969Source2660
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1140 : List StockPairs.Receipt := [
  ⟨⟨23,24,9,3,17,some 20,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,18,some 18,385979,[MeasuredChoices.test821],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,19,some 19,385979,[MeasuredChoices.test821],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,17,some 20,20,some 20,385979,[MeasuredChoices.test821],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩]
private theorem paid1140 : StockPairs.checked rows1140 = true := by decide +kernel
theorem route1140 (i : Fin 20) : (rows1140.get i).Done :=
  StockPairs.doneAt paid1140 i

end Research6969.PairReceipts
end Z6969Source2660

-- Source: Research6969.PairReceipts058
section Z6969Source2661
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1160 : List StockPairs.Receipt := [
  ⟨⟨23,24,9,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨23,24,9,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩]
private theorem paid1160 : StockPairs.checked rows1160 = true := by decide +kernel
theorem route1160 (i : Fin 20) : (rows1160.get i).Done :=
  StockPairs.doneAt paid1160 i

end Research6969.PairReceipts
end Z6969Source2661

-- Source: Research6969.PairReceipts060
section Z6969Source2662
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1200 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,1,surfaceWhole⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,1,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,1,surfaceWhole⟩,
  ⟨⟨25,27,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,1,surfaceWhole⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨25,27,9,2,4,some 8,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨25,27,9,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,1,markedWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,0,some 0,385979,[MeasuredChoices.test856],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,1,some 1,385979,[MeasuredChoices.test856],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,2,some 2,385979,[MeasuredChoices.test856],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,3,some 3,385979,[MeasuredChoices.test856],[AxisChoices.test1824]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,4,some 4,385979,[MeasuredChoices.test856],[AxisChoices.test1825]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,5,some 5,385979,[MeasuredChoices.test856],[AxisChoices.test1826]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,6,some 6,385979,[MeasuredChoices.test856],[AxisChoices.test1827]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,7,some 7,385979,[MeasuredChoices.test856],[AxisChoices.test1828]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,8,some 8,385979,[MeasuredChoices.test856],[AxisChoices.test1829]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,9,some 9,385979,[MeasuredChoices.test856],[AxisChoices.test1830]⟩,1,markedAxisWhole⟩,
  ⟨⟨25,27,9,3,20,some 20,10,some 10,385979,[MeasuredChoices.test856],[AxisChoices.test1831]⟩,1,markedAxisWhole⟩]
private theorem paid1200 : StockPairs.checked rows1200 = true := by decide +kernel
theorem route1200 (i : Fin 20) : (rows1200.get i).Done :=
  StockPairs.doneAt paid1200 i

end Research6969.PairReceipts
end Z6969Source2662

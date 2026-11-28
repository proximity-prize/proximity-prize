import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0669
import ProximityPrize.SubmissionLower.Z6969Pack0947
import ProximityPrize.SubmissionLower.Z6969Pack0948
import ProximityPrize.SubmissionLower.Z6969Pack0941
import ProximityPrize.SubmissionLower.Z6969Pack0942
import ProximityPrize.SubmissionLower.Z6969Pack0943
import ProximityPrize.SubmissionLower.Z6969Pack0944
import ProximityPrize.SubmissionLower.Z6969Pack0945
import ProximityPrize.SubmissionLower.Z6969Pack0946
import ProximityPrize.SubmissionLower.Z6969Pack0671

set_option Elab.async false

-- Source: Research6969.PairReceipts117
section Z6969Source2747
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2340 : List StockPairs.Receipt := [
  ⟨⟨64,722,12,2,17,some 20,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨64,722,12,2,13,some 16,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨64,722,12,2,9,some 12,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨64,722,12,2,4,some 8,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨23,24,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨23,24,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,2,⟨(.node 10087576824704342),.intersection,.impossible,303779⟩⟩,
  ⟨⟨23,24,9,2,25,some 28,0,none,303779,[MeasuredChoices.test172],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨23,24,9,2,23,some 24,0,none,257319,[MeasuredChoices.test29],[]⟩,2,⟨(.node 16272920511362425),.intersection,.impossible,306290⟩⟩,
  ⟨⟨23,24,9,2,23,some 24,0,none,306290,[MeasuredChoices.test347],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨23,24,9,2,21,some 22,0,none,257319,[MeasuredChoices.test25],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨23,24,9,2,17,some 20,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨23,24,9,2,13,some 16,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨23,24,9,2,9,some 12,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨23,24,9,2,4,some 8,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,markedAxisIntersection⟩]
private theorem paid2340 : StockPairs.checked rows2340 = true := by decide +kernel
theorem route2340 (i : Fin 20) : (rows2340.get i).Done :=
  StockPairs.doneAt paid2340 i

end Research6969.PairReceipts
end Z6969Source2747

-- Source: Research6969.HardFit2At180
section Z6969Source2748
set_option autoImplicit true
namespace Research6969.HardFit2At180
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2320 3)
theorem case180: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,13,some 16⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route2320 2)
theorem case181: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,17,some 20⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route2320 1)
theorem case182: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,21,some 24⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route2320 0)
theorem case183: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,25,some 28⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route2300 19)
theorem case184: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,29,some 32⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route2300 18)
theorem case185: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,33,some 40⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route2300 17)
theorem case186: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,41,some 48⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route2300 16)
theorem case187: NormalRoute.Done (1:Fin 18) ⟨64,722,12,1,49,some 64⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route2340 3)
theorem case188: NormalRoute.Done (1:Fin 18) ⟨64,722,12,2,4,some 8⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route2340 2)
theorem case189: NormalRoute.Done (1:Fin 18) ⟨64,722,12,2,9,some 12⟩:=PairRoute.start _ leaf9
end Research6969.HardFit2At180
end Z6969Source2748

-- Source: Research6969.HardFit2At190
section Z6969Source2749
set_option autoImplicit true
namespace Research6969.HardFit2At190
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2340 1)
theorem case190: NormalRoute.Done (1:Fin 18) ⟨64,722,12,2,13,some 16⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route2340 0)
theorem case191: NormalRoute.Done (1:Fin 18) ⟨64,722,12,2,17,some 20⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route2320 19)
theorem case192: NormalRoute.Done (1:Fin 18) ⟨64,722,12,2,21,some 24⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route2320 17)
private def leaf4 := (PairReceipts.route2320 18)
private def weight5 := PairRoute.weight 302619 leaf3 leaf4
theorem case193: NormalRoute.Done (1:Fin 18) ⟨64,722,12,2,25,some 28⟩:=PairRoute.start _ weight5
private def leaf6 := (PairReceipts.route2320 15)
private def leaf7 := (PairReceipts.route2320 16)
private def weight8 := PairRoute.weight 300842 leaf6 leaf7
theorem case194: NormalRoute.Done (1:Fin 18) ⟨64,722,12,2,29,some 32⟩:=PairRoute.start _ weight8
private def leaf9 := (PairReceipts.route2320 14)
theorem case195: NormalRoute.Done (1:Fin 18) ⟨64,722,12,2,33,some 36⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route2320 13)
theorem case196: NormalRoute.Done (1:Fin 18) ⟨64,722,12,2,37,some 40⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route2320 12)
theorem case197: NormalRoute.Done (1:Fin 18) ⟨64,722,12,2,41,some 44⟩:=PairRoute.start _ leaf11
private def leaf12 := (PairReceipts.route2320 11)
theorem case198: NormalRoute.Done (1:Fin 18) ⟨64,722,12,2,45,some 48⟩:=PairRoute.start _ leaf12
private def leaf13 := (PairReceipts.route2320 9)
private def leaf14 := (PairReceipts.route2320 10)
private def weight15 := PairRoute.weight 288407 leaf13 leaf14
theorem case199: NormalRoute.Done (1:Fin 18) ⟨64,722,12,2,49,some 52⟩:=PairRoute.start _ weight15
end Research6969.HardFit2At190
end Z6969Source2749

-- Source: Research6969.HardComplete2
section Z6969Source2750
set_option autoImplicit true
namespace Research6969.HardComplete2
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_6 (j:Fin HighPendingSeed2.regions.size) (l:0≤j.val) (h:j.val<6):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At000.case0
  · exact HardFit2At000.case1
  · exact HardFit2At000.case2
  · exact HardFit2At000.case3
  · exact HardFit2At000.case4
  · exact HardFit2At000.case5
private theorem covered6_12 (j:Fin HighPendingSeed2.regions.size) (l:6≤j.val) (h:j.val<12):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At000.case6
  · exact HardFit2At000.case7
  · exact HardFit2At000.case8
  · exact HardFit2At000.case9
  · exact HardFit2At010.case10
  · exact HardFit2At010.case11
private theorem covered0_12 (j:Fin HighPendingSeed2.regions.size) (l:0≤j.val) (h:j.val<12):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<6
  · exact covered0_6 j l low
  · exact covered6_12 j (by omega) h
private theorem covered12_18 (j:Fin HighPendingSeed2.regions.size) (l:12≤j.val) (h:j.val<18):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At010.case12
  · exact HardFit2At010.case13
  · exact HardFit2At010.case14
  · exact HardFit2At010.case15
  · exact HardFit2At010.case16
  · exact HardFit2At010.case17
private theorem covered18_25 (j:Fin HighPendingSeed2.regions.size) (l:18≤j.val) (h:j.val<25):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At010.case18
  · exact HardFit2At010.case19
  · exact HardFit2At020.case20
  · exact HardFit2At020.case21
  · exact HardFit2At020.case22
  · exact HardFit2At020.case23
  · exact HardFit2At020.case24
private theorem covered12_25 (j:Fin HighPendingSeed2.regions.size) (l:12≤j.val) (h:j.val<25):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<18
  · exact covered12_18 j l low
  · exact covered18_25 j (by omega) h
private theorem covered0_25 (j:Fin HighPendingSeed2.regions.size) (l:0≤j.val) (h:j.val<25):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<12
  · exact covered0_12 j l low
  · exact covered12_25 j (by omega) h
private theorem covered25_31 (j:Fin HighPendingSeed2.regions.size) (l:25≤j.val) (h:j.val<31):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At020.case25
  · exact HardFit2At020.case26
  · exact HardFit2At020.case27
  · exact HardFit2At020.case28
  · exact HardFit2At020.case29
  · exact HardFit2At030.case30
private theorem covered31_37 (j:Fin HighPendingSeed2.regions.size) (l:31≤j.val) (h:j.val<37):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At030.case31
  · exact HardFit2At030.case32
  · exact HardFit2At030.case33
  · exact HardFit2At030.case34
  · exact HardFit2At030.case35
  · exact HardFit2At030.case36
private theorem covered25_37 (j:Fin HighPendingSeed2.regions.size) (l:25≤j.val) (h:j.val<37):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<31
  · exact covered25_31 j l low
  · exact covered31_37 j (by omega) h
private theorem covered37_43 (j:Fin HighPendingSeed2.regions.size) (l:37≤j.val) (h:j.val<43):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At030.case37
  · exact HardFit2At030.case38
  · exact HardFit2At030.case39
  · exact HardFit2At040.case40
  · exact HardFit2At040.case41
  · exact HardFit2At040.case42
private theorem covered43_50 (j:Fin HighPendingSeed2.regions.size) (l:43≤j.val) (h:j.val<50):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At040.case43
  · exact HardFit2At040.case44
  · exact HardFit2At040.case45
  · exact HardFit2At040.case46
  · exact HardFit2At040.case47
  · exact HardFit2At040.case48
  · exact HardFit2At040.case49
private theorem covered37_50 (j:Fin HighPendingSeed2.regions.size) (l:37≤j.val) (h:j.val<50):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<43
  · exact covered37_43 j l low
  · exact covered43_50 j (by omega) h
private theorem covered25_50 (j:Fin HighPendingSeed2.regions.size) (l:25≤j.val) (h:j.val<50):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<37
  · exact covered25_37 j l low
  · exact covered37_50 j (by omega) h
private theorem covered0_50 (j:Fin HighPendingSeed2.regions.size) (l:0≤j.val) (h:j.val<50):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<25
  · exact covered0_25 j l low
  · exact covered25_50 j (by omega) h
private theorem covered50_56 (j:Fin HighPendingSeed2.regions.size) (l:50≤j.val) (h:j.val<56):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At050.case50
  · exact HardFit2At050.case51
  · exact HardFit2At050.case52
  · exact HardFit2At050.case53
  · exact HardFit2At050.case54
  · exact HardFit2At050.case55
private theorem covered56_62 (j:Fin HighPendingSeed2.regions.size) (l:56≤j.val) (h:j.val<62):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At050.case56
  · exact HardFit2At050.case57
  · exact HardFit2At050.case58
  · exact HardFit2At050.case59
  · exact HardFit2At060.case60
  · exact HardFit2At060.case61
private theorem covered50_62 (j:Fin HighPendingSeed2.regions.size) (l:50≤j.val) (h:j.val<62):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<56
  · exact covered50_56 j l low
  · exact covered56_62 j (by omega) h
private theorem covered62_68 (j:Fin HighPendingSeed2.regions.size) (l:62≤j.val) (h:j.val<68):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At060.case62
  · exact HardFit2At060.case63
  · exact HardFit2At060.case64
  · exact HardFit2At060.case65
  · exact HardFit2At060.case66
  · exact HardFit2At060.case67
private theorem covered68_75 (j:Fin HighPendingSeed2.regions.size) (l:68≤j.val) (h:j.val<75):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At060.case68
  · exact HardFit2At060.case69
  · exact HardFit2At070.case70
  · exact HardFit2At070.case71
  · exact HardFit2At070.case72
  · exact HardFit2At070.case73
  · exact HardFit2At070.case74
private theorem covered62_75 (j:Fin HighPendingSeed2.regions.size) (l:62≤j.val) (h:j.val<75):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<68
  · exact covered62_68 j l low
  · exact covered68_75 j (by omega) h
private theorem covered50_75 (j:Fin HighPendingSeed2.regions.size) (l:50≤j.val) (h:j.val<75):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<62
  · exact covered50_62 j l low
  · exact covered62_75 j (by omega) h
private theorem covered75_81 (j:Fin HighPendingSeed2.regions.size) (l:75≤j.val) (h:j.val<81):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At070.case75
  · exact HardFit2At070.case76
  · exact HardFit2At070.case77
  · exact HardFit2At070.case78
  · exact HardFit2At070.case79
  · exact HardFit2At080.case80
private theorem covered81_87 (j:Fin HighPendingSeed2.regions.size) (l:81≤j.val) (h:j.val<87):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At080.case81
  · exact HardFit2At080.case82
  · exact HardFit2At080.case83
  · exact HardFit2At080.case84
  · exact HardFit2At080.case85
  · exact HardFit2At080.case86
private theorem covered75_87 (j:Fin HighPendingSeed2.regions.size) (l:75≤j.val) (h:j.val<87):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<81
  · exact covered75_81 j l low
  · exact covered81_87 j (by omega) h
private theorem covered87_93 (j:Fin HighPendingSeed2.regions.size) (l:87≤j.val) (h:j.val<93):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At080.case87
  · exact HardFit2At080.case88
  · exact HardFit2At080.case89
  · exact HardFit2At090.case90
  · exact HardFit2At090.case91
  · exact HardFit2At090.case92
private theorem covered93_100 (j:Fin HighPendingSeed2.regions.size) (l:93≤j.val) (h:j.val<100):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At090.case93
  · exact HardFit2At090.case94
  · exact HardFit2At090.case95
  · exact HardFit2At090.case96
  · exact HardFit2At090.case97
  · exact HardFit2At090.case98
  · exact HardFit2At090.case99
private theorem covered87_100 (j:Fin HighPendingSeed2.regions.size) (l:87≤j.val) (h:j.val<100):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<93
  · exact covered87_93 j l low
  · exact covered93_100 j (by omega) h
private theorem covered75_100 (j:Fin HighPendingSeed2.regions.size) (l:75≤j.val) (h:j.val<100):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<87
  · exact covered75_87 j l low
  · exact covered87_100 j (by omega) h
private theorem covered50_100 (j:Fin HighPendingSeed2.regions.size) (l:50≤j.val) (h:j.val<100):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<75
  · exact covered50_75 j l low
  · exact covered75_100 j (by omega) h
private theorem covered0_100 (j:Fin HighPendingSeed2.regions.size) (l:0≤j.val) (h:j.val<100):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<50
  · exact covered0_50 j l low
  · exact covered50_100 j (by omega) h
private theorem covered100_106 (j:Fin HighPendingSeed2.regions.size) (l:100≤j.val) (h:j.val<106):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At100.case100
  · exact HardFit2At100.case101
  · exact HardFit2At100.case102
  · exact HardFit2At100.case103
  · exact HardFit2At100.case104
  · exact HardFit2At100.case105
private theorem covered106_112 (j:Fin HighPendingSeed2.regions.size) (l:106≤j.val) (h:j.val<112):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At100.case106
  · exact HardFit2At100.case107
  · exact HardFit2At100.case108
  · exact HardFit2At100.case109
  · exact HardFit2At110.case110
  · exact HardFit2At110.case111
private theorem covered100_112 (j:Fin HighPendingSeed2.regions.size) (l:100≤j.val) (h:j.val<112):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<106
  · exact covered100_106 j l low
  · exact covered106_112 j (by omega) h
private theorem covered112_118 (j:Fin HighPendingSeed2.regions.size) (l:112≤j.val) (h:j.val<118):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At110.case112
  · exact HardFit2At110.case113
  · exact HardFit2At110.case114
  · exact HardFit2At110.case115
  · exact HardFit2At110.case116
  · exact HardFit2At110.case117
private theorem covered118_125 (j:Fin HighPendingSeed2.regions.size) (l:118≤j.val) (h:j.val<125):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At110.case118
  · exact HardFit2At110.case119
  · exact HardFit2At120.case120
  · exact HardFit2At120.case121
  · exact HardFit2At120.case122
  · exact HardFit2At120.case123
  · exact HardFit2At120.case124
private theorem covered112_125 (j:Fin HighPendingSeed2.regions.size) (l:112≤j.val) (h:j.val<125):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<118
  · exact covered112_118 j l low
  · exact covered118_125 j (by omega) h
private theorem covered100_125 (j:Fin HighPendingSeed2.regions.size) (l:100≤j.val) (h:j.val<125):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<112
  · exact covered100_112 j l low
  · exact covered112_125 j (by omega) h
private theorem covered125_131 (j:Fin HighPendingSeed2.regions.size) (l:125≤j.val) (h:j.val<131):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At120.case125
  · exact HardFit2At120.case126
  · exact HardFit2At120.case127
  · exact HardFit2At120.case128
  · exact HardFit2At120.case129
  · exact HardFit2At130.case130
private theorem covered131_137 (j:Fin HighPendingSeed2.regions.size) (l:131≤j.val) (h:j.val<137):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At130.case131
  · exact HardFit2At130.case132
  · exact HardFit2At130.case133
  · exact HardFit2At130.case134
  · exact HardFit2At130.case135
  · exact HardFit2At130.case136
private theorem covered125_137 (j:Fin HighPendingSeed2.regions.size) (l:125≤j.val) (h:j.val<137):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<131
  · exact covered125_131 j l low
  · exact covered131_137 j (by omega) h
private theorem covered137_143 (j:Fin HighPendingSeed2.regions.size) (l:137≤j.val) (h:j.val<143):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At130.case137
  · exact HardFit2At130.case138
  · exact HardFit2At130.case139
  · exact HardFit2At140.case140
  · exact HardFit2At140.case141
  · exact HardFit2At140.case142
private theorem covered143_150 (j:Fin HighPendingSeed2.regions.size) (l:143≤j.val) (h:j.val<150):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At140.case143
  · exact HardFit2At140.case144
  · exact HardFit2At140.case145
  · exact HardFit2At140.case146
  · exact HardFit2At140.case147
  · exact HardFit2At140.case148
  · exact HardFit2At140.case149
private theorem covered137_150 (j:Fin HighPendingSeed2.regions.size) (l:137≤j.val) (h:j.val<150):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<143
  · exact covered137_143 j l low
  · exact covered143_150 j (by omega) h
private theorem covered125_150 (j:Fin HighPendingSeed2.regions.size) (l:125≤j.val) (h:j.val<150):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<137
  · exact covered125_137 j l low
  · exact covered137_150 j (by omega) h
private theorem covered100_150 (j:Fin HighPendingSeed2.regions.size) (l:100≤j.val) (h:j.val<150):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<125
  · exact covered100_125 j l low
  · exact covered125_150 j (by omega) h
private theorem covered150_156 (j:Fin HighPendingSeed2.regions.size) (l:150≤j.val) (h:j.val<156):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At150.case150
  · exact HardFit2At150.case151
  · exact HardFit2At150.case152
  · exact HardFit2At150.case153
  · exact HardFit2At150.case154
  · exact HardFit2At150.case155
private theorem covered156_162 (j:Fin HighPendingSeed2.regions.size) (l:156≤j.val) (h:j.val<162):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At150.case156
  · exact HardFit2At150.case157
  · exact HardFit2At150.case158
  · exact HardFit2At150.case159
  · exact HardFit2At160.case160
  · exact HardFit2At160.case161
private theorem covered150_162 (j:Fin HighPendingSeed2.regions.size) (l:150≤j.val) (h:j.val<162):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<156
  · exact covered150_156 j l low
  · exact covered156_162 j (by omega) h
private theorem covered162_168 (j:Fin HighPendingSeed2.regions.size) (l:162≤j.val) (h:j.val<168):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At160.case162
  · exact HardFit2At160.case163
  · exact HardFit2At160.case164
  · exact HardFit2At160.case165
  · exact HardFit2At160.case166
  · exact HardFit2At160.case167
private theorem covered168_175 (j:Fin HighPendingSeed2.regions.size) (l:168≤j.val) (h:j.val<175):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At160.case168
  · exact HardFit2At160.case169
  · exact HardFit2At170.case170
  · exact HardFit2At170.case171
  · exact HardFit2At170.case172
  · exact HardFit2At170.case173
  · exact HardFit2At170.case174
private theorem covered162_175 (j:Fin HighPendingSeed2.regions.size) (l:162≤j.val) (h:j.val<175):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<168
  · exact covered162_168 j l low
  · exact covered168_175 j (by omega) h
private theorem covered150_175 (j:Fin HighPendingSeed2.regions.size) (l:150≤j.val) (h:j.val<175):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<162
  · exact covered150_162 j l low
  · exact covered162_175 j (by omega) h
private theorem covered175_181 (j:Fin HighPendingSeed2.regions.size) (l:175≤j.val) (h:j.val<181):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At170.case175
  · exact HardFit2At170.case176
  · exact HardFit2At170.case177
  · exact HardFit2At170.case178
  · exact HardFit2At170.case179
  · exact HardFit2At180.case180
private theorem covered181_187 (j:Fin HighPendingSeed2.regions.size) (l:181≤j.val) (h:j.val<187):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At180.case181
  · exact HardFit2At180.case182
  · exact HardFit2At180.case183
  · exact HardFit2At180.case184
  · exact HardFit2At180.case185
  · exact HardFit2At180.case186
private theorem covered175_187 (j:Fin HighPendingSeed2.regions.size) (l:175≤j.val) (h:j.val<187):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<181
  · exact covered175_181 j l low
  · exact covered181_187 j (by omega) h
private theorem covered187_193 (j:Fin HighPendingSeed2.regions.size) (l:187≤j.val) (h:j.val<193):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At180.case187
  · exact HardFit2At180.case188
  · exact HardFit2At180.case189
  · exact HardFit2At190.case190
  · exact HardFit2At190.case191
  · exact HardFit2At190.case192
private theorem covered193_200 (j:Fin HighPendingSeed2.regions.size) (l:193≤j.val) (h:j.val<200):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit2At190.case193
  · exact HardFit2At190.case194
  · exact HardFit2At190.case195
  · exact HardFit2At190.case196
  · exact HardFit2At190.case197
  · exact HardFit2At190.case198
  · exact HardFit2At190.case199
private theorem covered187_200 (j:Fin HighPendingSeed2.regions.size) (l:187≤j.val) (h:j.val<200):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<193
  · exact covered187_193 j l low
  · exact covered193_200 j (by omega) h
private theorem covered175_200 (j:Fin HighPendingSeed2.regions.size) (l:175≤j.val) (h:j.val<200):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<187
  · exact covered175_187 j l low
  · exact covered187_200 j (by omega) h
private theorem covered150_200 (j:Fin HighPendingSeed2.regions.size) (l:150≤j.val) (h:j.val<200):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<175
  · exact covered150_175 j l low
  · exact covered175_200 j (by omega) h
private theorem covered100_200 (j:Fin HighPendingSeed2.regions.size) (l:100≤j.val) (h:j.val<200):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<150
  · exact covered100_150 j l low
  · exact covered150_200 j (by omega) h
private theorem covered0_200 (j:Fin HighPendingSeed2.regions.size) (l:0≤j.val) (h:j.val<200):Done (1:Fin 18) (HighPendingSeed2.atIndex j):=by
  by_cases low:j.val<100
  · exact covered0_100 j l low
  · exact covered100_200 j (by omega) h
theorem required:HighPendingSeed2.Required:=fun j=>covered0_200 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete2
end Z6969Source2750

-- Source: Research6969.PairReceipts119
section Z6969Source2751
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2380 : List StockPairs.Receipt := [
  ⟨⟨23,24,9,3,15,some 16,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,16,some 16,385979,[MeasuredChoices.test797],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,13,some 14,0,none,385979,[MeasuredChoices.test770],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨23,24,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨23,24,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,2,⟨(.node 10087576824704342),.intersection,.impossible,303779⟩⟩,
  ⟨⟨25,27,9,2,25,some 28,0,none,303779,[MeasuredChoices.test172],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,23,some 24,0,none,257319,[MeasuredChoices.test29],[]⟩,2,⟨(.node 16272920511362425),.intersection,.impossible,306290⟩⟩,
  ⟨⟨25,27,9,2,23,some 24,0,none,306290,[MeasuredChoices.test347],[]⟩,2,surfaceIntersection⟩]
private theorem paid2380 : StockPairs.checked rows2380 = true := by decide +kernel
theorem route2380 (i : Fin 20) : (rows2380.get i).Done :=
  StockPairs.doneAt paid2380 i

end Research6969.PairReceipts
end Z6969Source2751

-- Source: Research6969.HardFit3At000
section Z6969Source2752
set_option autoImplicit true
namespace Research6969.HardFit3At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2340 13)
theorem case0: NormalRoute.Done (2:Fin 18) ⟨23,24,9,2,4,some 8⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route2340 12)
theorem case1: NormalRoute.Done (2:Fin 18) ⟨23,24,9,2,9,some 12⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route2340 11)
theorem case2: NormalRoute.Done (2:Fin 18) ⟨23,24,9,2,13,some 16⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route2340 10)
theorem case3: NormalRoute.Done (2:Fin 18) ⟨23,24,9,2,17,some 20⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route2340 9)
theorem case4: NormalRoute.Done (2:Fin 18) ⟨23,24,9,2,21,some 22⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route2340 7)
private def leaf6 := (PairReceipts.route2340 8)
private def weight7 := PairRoute.weight 306290 leaf5 leaf6
theorem case5: NormalRoute.Done (2:Fin 18) ⟨23,24,9,2,23,some 24⟩:=PairRoute.start _ weight7
private def leaf8 := (PairReceipts.route2340 5)
private def leaf9 := (PairReceipts.route2340 6)
private def weight10 := PairRoute.weight 303779 leaf8 leaf9
theorem case6: NormalRoute.Done (2:Fin 18) ⟨23,24,9,2,25,some 28⟩:=PairRoute.start _ weight10
private def leaf11 := (PairReceipts.route2340 4)
theorem case7: NormalRoute.Done (2:Fin 18) ⟨23,24,9,2,29,some 32⟩:=PairRoute.start _ leaf11
private def leaf12 := (PairReceipts.route2380 14)
theorem case8: NormalRoute.Done (2:Fin 18) ⟨23,24,9,3,4,some 8⟩:=PairRoute.start _ leaf12
private def leaf13 := (PairReceipts.route2380 13)
theorem case9: NormalRoute.Done (2:Fin 18) ⟨23,24,9,3,9,some 12⟩:=PairRoute.start _ leaf13
end Research6969.HardFit3At000
end Z6969Source2752

-- Source: Research6969.PairReceipts118
section Z6969Source2753
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2360 : List StockPairs.Receipt := [
  ⟨⟨23,24,9,3,17,some 20,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,18,some 18,385979,[MeasuredChoices.test821],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,19,some 19,385979,[MeasuredChoices.test821],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,20,some 20,385979,[MeasuredChoices.test821],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,2,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,15,some 16,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,2,markedAxisIntersection⟩]
private theorem paid2360 : StockPairs.checked rows2360 = true := by decide +kernel
theorem route2360 (i : Fin 20) : (rows2360.get i).Done :=
  StockPairs.doneAt paid2360 i

end Research6969.PairReceipts
end Z6969Source2753

-- Source: Research6969.PairReceipts120
section Z6969Source2754
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2400 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,2,21,some 22,0,none,257319,[MeasuredChoices.test25],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,17,some 20,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,13,some 16,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,9,some 12,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨25,27,9,2,4,some 8,0,none,257319,[],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,0,some 0,385979,[MeasuredChoices.test869],[AxisChoices.test1821]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,1,some 1,385979,[MeasuredChoices.test869],[AxisChoices.test1822]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,2,some 2,385979,[MeasuredChoices.test869],[AxisChoices.test1823]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,3,some 3,385979,[MeasuredChoices.test869],[AxisChoices.test1824]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,4,some 4,385979,[MeasuredChoices.test869],[AxisChoices.test1825]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,5,some 5,385979,[MeasuredChoices.test869],[AxisChoices.test1826]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,6,some 6,385979,[MeasuredChoices.test869],[AxisChoices.test1827]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,7,some 7,385979,[MeasuredChoices.test869],[AxisChoices.test1828]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,8,some 8,385979,[MeasuredChoices.test869],[AxisChoices.test1829]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,9,some 9,385979,[MeasuredChoices.test869],[AxisChoices.test1830]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,10,some 10,385979,[MeasuredChoices.test869],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,11,some 11,385979,[MeasuredChoices.test869],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,12,some 12,385979,[MeasuredChoices.test869],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,13,some 13,385979,[MeasuredChoices.test869],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,14,some 14,385979,[MeasuredChoices.test869],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩]
private theorem paid2400 : StockPairs.checked rows2400 = true := by decide +kernel
theorem route2400 (i : Fin 20) : (rows2400.get i).Done :=
  StockPairs.doneAt paid2400 i

end Research6969.PairReceipts
end Z6969Source2754

-- Source: Research6969.HardFit3At010
section Z6969Source2755
set_option autoImplicit true
namespace Research6969.HardFit3At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2380 12)
theorem case10: NormalRoute.Done (2:Fin 18) ⟨23,24,9,3,13,some 14⟩:=PairRoute.start _ leaf0
private theorem allAxes34:PairRoute.Done (2:Fin 18) ⟨⟨23,24,9,3,15,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route2360 15),
    (PairReceipts.route2360 16),
    (PairReceipts.route2360 17),
    (PairReceipts.route2360 18),
    (PairReceipts.route2360 19),
    (PairReceipts.route2380 0),
    (PairReceipts.route2380 1),
    (PairReceipts.route2380 2),
    (PairReceipts.route2380 3),
    (PairReceipts.route2380 4),
    (PairReceipts.route2380 5),
    (PairReceipts.route2380 6),
    (PairReceipts.route2380 7),
    (PairReceipts.route2380 8),
    (PairReceipts.route2380 9),
    (PairReceipts.route2380 10),
    (PairReceipts.route2380 11),
    trivial⟩)
theorem case11: NormalRoute.Done (2:Fin 18) ⟨23,24,9,3,15,some 16⟩:=PairRoute.start _ allAxes34
private theorem allAxes76:PairRoute.Done (2:Fin 18) ⟨⟨23,24,9,3,17,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route2340 14),
    (PairReceipts.route2340 15),
    (PairReceipts.route2340 16),
    (PairReceipts.route2340 17),
    (PairReceipts.route2340 18),
    (PairReceipts.route2340 19),
    (PairReceipts.route2360 0),
    (PairReceipts.route2360 1),
    (PairReceipts.route2360 2),
    (PairReceipts.route2360 3),
    (PairReceipts.route2360 4),
    (PairReceipts.route2360 5),
    (PairReceipts.route2360 6),
    (PairReceipts.route2360 7),
    (PairReceipts.route2360 8),
    (PairReceipts.route2360 9),
    (PairReceipts.route2360 10),
    (PairReceipts.route2360 11),
    (PairReceipts.route2360 12),
    (PairReceipts.route2360 13),
    (PairReceipts.route2360 14),
    trivial⟩)
theorem case12: NormalRoute.Done (2:Fin 18) ⟨23,24,9,3,17,some 20⟩:=PairRoute.start _ allAxes76
private def leaf77 := (PairReceipts.route2400 4)
theorem case13: NormalRoute.Done (2:Fin 18) ⟨25,27,9,2,4,some 8⟩:=PairRoute.start _ leaf77
private def leaf78 := (PairReceipts.route2400 3)
theorem case14: NormalRoute.Done (2:Fin 18) ⟨25,27,9,2,9,some 12⟩:=PairRoute.start _ leaf78
private def leaf79 := (PairReceipts.route2400 2)
theorem case15: NormalRoute.Done (2:Fin 18) ⟨25,27,9,2,13,some 16⟩:=PairRoute.start _ leaf79
private def leaf80 := (PairReceipts.route2400 1)
theorem case16: NormalRoute.Done (2:Fin 18) ⟨25,27,9,2,17,some 20⟩:=PairRoute.start _ leaf80
private def leaf81 := (PairReceipts.route2400 0)
theorem case17: NormalRoute.Done (2:Fin 18) ⟨25,27,9,2,21,some 22⟩:=PairRoute.start _ leaf81
private def leaf82 := (PairReceipts.route2380 18)
private def leaf83 := (PairReceipts.route2380 19)
private def weight84 := PairRoute.weight 306290 leaf82 leaf83
theorem case18: NormalRoute.Done (2:Fin 18) ⟨25,27,9,2,23,some 24⟩:=PairRoute.start _ weight84
private def leaf85 := (PairReceipts.route2380 16)
private def leaf86 := (PairReceipts.route2380 17)
private def weight87 := PairRoute.weight 303779 leaf85 leaf86
theorem case19: NormalRoute.Done (2:Fin 18) ⟨25,27,9,2,25,some 28⟩:=PairRoute.start _ weight87
end Research6969.HardFit3At010
end Z6969Source2755

-- Source: Research6969.PairReceipts121
section Z6969Source2756
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2420 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,21,some 24,15,some 15,385979,[MeasuredChoices.test869],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,16,some 16,385979,[MeasuredChoices.test869],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,17,some 17,385979,[MeasuredChoices.test869],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,18,some 18,385979,[MeasuredChoices.test869],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,19,some 19,385979,[MeasuredChoices.test869],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,20,some 20,385979,[MeasuredChoices.test869],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,21,some 21,385979,[MeasuredChoices.test869],[AxisChoices.test1842]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,22,some 22,385979,[MeasuredChoices.test869],[AxisChoices.test1843]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,23,some 23,385979,[MeasuredChoices.test869],[AxisChoices.test1844]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,21,some 24,24,some 24,385979,[MeasuredChoices.test869],[AxisChoices.test1845]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,2,some 2,385979,[MeasuredChoices.test843],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,3,some 3,385979,[MeasuredChoices.test843],[AxisChoices.test1824]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,4,some 4,385979,[MeasuredChoices.test843],[AxisChoices.test1825]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,5,some 5,385979,[MeasuredChoices.test843],[AxisChoices.test1826]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,6,some 6,385979,[MeasuredChoices.test843],[AxisChoices.test1827]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,7,some 7,385979,[MeasuredChoices.test843],[AxisChoices.test1828]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,8,some 8,385979,[MeasuredChoices.test843],[AxisChoices.test1829]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,9,some 9,385979,[MeasuredChoices.test843],[AxisChoices.test1830]⟩,2,markedAxisIntersection⟩]
private theorem paid2420 : StockPairs.checked rows2420 = true := by decide +kernel
theorem route2420 (i : Fin 20) : (rows2420.get i).Done :=
  StockPairs.doneAt paid2420 i

end Research6969.PairReceipts
end Z6969Source2756

-- Source: Research6969.PairReceipts122
section Z6969Source2757
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2440 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,19,some 20,10,some 10,385979,[MeasuredChoices.test843],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,11,some 11,385979,[MeasuredChoices.test843],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,12,some 12,385979,[MeasuredChoices.test843],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,13,some 13,385979,[MeasuredChoices.test843],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,14,some 14,385979,[MeasuredChoices.test843],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,15,some 15,385979,[MeasuredChoices.test843],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,16,some 16,385979,[MeasuredChoices.test843],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,17,some 17,385979,[MeasuredChoices.test843],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,18,some 18,385979,[MeasuredChoices.test843],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,19,some 20,20,some 20,385979,[MeasuredChoices.test843],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,0,some 0,385979,[MeasuredChoices.test831],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,1,some 1,385979,[MeasuredChoices.test831],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,2,some 2,385979,[MeasuredChoices.test831],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,3,some 3,385979,[MeasuredChoices.test831],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,4,some 4,385979,[MeasuredChoices.test831],[AxisChoices.test1825]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,5,some 5,385979,[MeasuredChoices.test831],[AxisChoices.test1826]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,6,some 6,385979,[MeasuredChoices.test831],[AxisChoices.test1827]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,7,some 7,385979,[MeasuredChoices.test831],[AxisChoices.test1828]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,8,some 8,385979,[MeasuredChoices.test831],[AxisChoices.test1829]⟩,2,markedAxisIntersection⟩]
private theorem paid2440 : StockPairs.checked rows2440 = true := by decide +kernel
theorem route2440 (i : Fin 20) : (rows2440.get i).Done :=
  StockPairs.doneAt paid2440 i

end Research6969.PairReceipts
end Z6969Source2757

-- Source: Research6969.PairReceipts123
section Z6969Source2758
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2460 : List StockPairs.Receipt := [
  ⟨⟨25,27,9,3,18,some 18,9,some 9,385979,[MeasuredChoices.test831],[AxisChoices.test1830]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,10,some 10,385979,[MeasuredChoices.test831],[AxisChoices.test1831]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,11,some 11,385979,[MeasuredChoices.test831],[AxisChoices.test1832]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,12,some 12,385979,[MeasuredChoices.test831],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,13,some 13,385979,[MeasuredChoices.test831],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,14,some 14,385979,[MeasuredChoices.test831],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,15,some 15,385979,[MeasuredChoices.test831],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,16,some 16,385979,[MeasuredChoices.test831],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,17,some 17,385979,[MeasuredChoices.test831],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,18,some 18,18,some 18,385979,[MeasuredChoices.test831],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,2,markedAxisIntersection⟩,
  ⟨⟨25,27,9,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,2,markedAxisIntersection⟩]
private theorem paid2460 : StockPairs.checked rows2460 = true := by decide +kernel
theorem route2460 (i : Fin 20) : (rows2460.get i).Done :=
  StockPairs.doneAt paid2460 i

end Research6969.PairReceipts
end Z6969Source2758

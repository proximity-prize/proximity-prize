import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0975
import ProximityPrize.SubmissionLower.Z6969Pack0683
import ProximityPrize.SubmissionLower.Z6969Pack0685

set_option Elab.async false

-- Source: Research6969.PairReceipts052
section Z6969Source3052
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1040 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,49,some 64,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,11,⟨(.node 8023872256819695),.intersection,.impossible,278103⟩⟩,
  ⟨⟨64,654,12,2,49,some 64,0,none,278103,[MeasuredChoices.test104],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,33,some 40,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,17,some 20,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,13,some 16,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,12,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,12,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,12,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,12,⟨.surface,.intersection,.surface,0⟩⟩]
private theorem paid1040 : StockPairs.checked rows1040 = true := by decide +kernel
theorem route1040 (i : Fin 20) : (rows1040.get i).Done :=
  StockPairs.doneAt paid1040 i

end Research6969.PairReceipts
end Z6969Source3052

-- Source: Research6969.HardFit12At010
section Z6969Source3053
set_option autoImplicit true
namespace Research6969.HardFit12At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1020 18)
theorem case10: NormalRoute.Done (11:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1020 17)
theorem case11: NormalRoute.Done (11:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1020 16)
theorem case12: NormalRoute.Done (11:Fin 18) ⟨50,63,10,2,25,some 28⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1020 15)
theorem case13: NormalRoute.Done (11:Fin 18) ⟨50,63,10,2,49,some 64⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1040 7)
theorem case14: NormalRoute.Done (11:Fin 18) ⟨64,654,12,2,13,some 16⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1040 6)
theorem case15: NormalRoute.Done (11:Fin 18) ⟨64,654,12,2,17,some 20⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1040 5)
theorem case16: NormalRoute.Done (11:Fin 18) ⟨64,654,12,2,21,some 24⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1040 4)
theorem case17: NormalRoute.Done (11:Fin 18) ⟨64,654,12,2,25,some 28⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route1040 3)
theorem case18: NormalRoute.Done (11:Fin 18) ⟨64,654,12,2,29,some 32⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route1040 2)
theorem case19: NormalRoute.Done (11:Fin 18) ⟨64,654,12,2,33,some 40⟩:=PairRoute.start _ leaf9
end Research6969.HardFit12At010
end Z6969Source3053

-- Source: Research6969.HardFit12At020
section Z6969Source3054
set_option autoImplicit true
namespace Research6969.HardFit12At020
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1040 0)
private def leaf1 := (PairReceipts.route1040 1)
private def weight2 := PairRoute.weight 278103 leaf0 leaf1
theorem case20: NormalRoute.Done (11:Fin 18) ⟨64,654,12,2,49,some 64⟩:=PairRoute.start _ weight2
end Research6969.HardFit12At020
end Z6969Source3054

-- Source: Research6969.HardComplete12
section Z6969Source3055
set_option autoImplicit true
namespace Research6969.HardComplete12
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_5 (j:Fin HighPendingSeed12.regions.size) (l:0≤j.val) (h:j.val<5):Done (11:Fin 18) (HighPendingSeed12.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit12At000.case0
  · exact HardFit12At000.case1
  · exact HardFit12At000.case2
  · exact HardFit12At000.case3
  · exact HardFit12At000.case4
private theorem covered5_10 (j:Fin HighPendingSeed12.regions.size) (l:5≤j.val) (h:j.val<10):Done (11:Fin 18) (HighPendingSeed12.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit12At000.case5
  · exact HardFit12At000.case6
  · exact HardFit12At000.case7
  · exact HardFit12At000.case8
  · exact HardFit12At000.case9
private theorem covered0_10 (j:Fin HighPendingSeed12.regions.size) (l:0≤j.val) (h:j.val<10):Done (11:Fin 18) (HighPendingSeed12.atIndex j):=by
  by_cases low:j.val<5
  · exact covered0_5 j l low
  · exact covered5_10 j (by omega) h
private theorem covered10_15 (j:Fin HighPendingSeed12.regions.size) (l:10≤j.val) (h:j.val<15):Done (11:Fin 18) (HighPendingSeed12.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit12At010.case10
  · exact HardFit12At010.case11
  · exact HardFit12At010.case12
  · exact HardFit12At010.case13
  · exact HardFit12At010.case14
private theorem covered15_21 (j:Fin HighPendingSeed12.regions.size) (l:15≤j.val) (h:j.val<21):Done (11:Fin 18) (HighPendingSeed12.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit12At010.case15
  · exact HardFit12At010.case16
  · exact HardFit12At010.case17
  · exact HardFit12At010.case18
  · exact HardFit12At010.case19
  · exact HardFit12At020.case20
private theorem covered10_21 (j:Fin HighPendingSeed12.regions.size) (l:10≤j.val) (h:j.val<21):Done (11:Fin 18) (HighPendingSeed12.atIndex j):=by
  by_cases low:j.val<15
  · exact covered10_15 j l low
  · exact covered15_21 j (by omega) h
private theorem covered0_21 (j:Fin HighPendingSeed12.regions.size) (l:0≤j.val) (h:j.val<21):Done (11:Fin 18) (HighPendingSeed12.atIndex j):=by
  by_cases low:j.val<10
  · exact covered0_10 j l low
  · exact covered10_21 j (by omega) h
theorem required:HighPendingSeed12.Required:=fun j=>covered0_21 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete12
end Z6969Source3055

-- Source: Research6969.HardFit13At000
section Z6969Source3056
set_option autoImplicit true
namespace Research6969.HardFit13At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1040 10)
theorem case0: NormalRoute.Done (12:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1040 9)
theorem case1: NormalRoute.Done (12:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1040 8)
theorem case2: NormalRoute.Done (12:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1040 13)
theorem case3: NormalRoute.Done (12:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1040 12)
theorem case4: NormalRoute.Done (12:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1040 11)
theorem case5: NormalRoute.Done (12:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1040 16)
theorem case6: NormalRoute.Done (12:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1040 15)
theorem case7: NormalRoute.Done (12:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route1040 14)
theorem case8: NormalRoute.Done (12:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route1040 19)
theorem case9: NormalRoute.Done (12:Fin 18) ⟨50,63,10,2,13,some 16⟩:=PairRoute.start _ leaf9
end Research6969.HardFit13At000
end Z6969Source3056

-- Source: Research6969.PairReceipts053
section Z6969Source3057
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1060 : List StockPairs.Receipt := [
  ⟨⟨64,591,12,2,49,some 64,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨64,591,12,2,33,some 40,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨64,591,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨64,591,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨64,591,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨64,591,12,2,17,some 20,0,none,257319,[],[]⟩,12,surfaceIntersection⟩,
  ⟨⟨64,591,12,2,13,some 16,0,none,257319,[],[]⟩,12,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,13,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,13,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,13,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,13,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,13,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,13,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,13,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,13,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,49,some 64,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,13,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,13,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,13,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,13,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,17,some 20,0,none,257319,[],[]⟩,13,surfaceIntersection⟩]
private theorem paid1060 : StockPairs.checked rows1060 = true := by decide +kernel
theorem route1060 (i : Fin 20) : (rows1060.get i).Done :=
  StockPairs.doneAt paid1060 i

end Research6969.PairReceipts
end Z6969Source3057

-- Source: Research6969.HardFit13At010
section Z6969Source3058
set_option autoImplicit true
namespace Research6969.HardFit13At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1040 18)
theorem case10: NormalRoute.Done (12:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1040 17)
theorem case11: NormalRoute.Done (12:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1060 6)
theorem case12: NormalRoute.Done (12:Fin 18) ⟨64,591,12,2,13,some 16⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1060 5)
theorem case13: NormalRoute.Done (12:Fin 18) ⟨64,591,12,2,17,some 20⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1060 4)
theorem case14: NormalRoute.Done (12:Fin 18) ⟨64,591,12,2,21,some 24⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1060 3)
theorem case15: NormalRoute.Done (12:Fin 18) ⟨64,591,12,2,25,some 28⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1060 2)
theorem case16: NormalRoute.Done (12:Fin 18) ⟨64,591,12,2,29,some 32⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1060 1)
theorem case17: NormalRoute.Done (12:Fin 18) ⟨64,591,12,2,33,some 40⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route1060 0)
theorem case18: NormalRoute.Done (12:Fin 18) ⟨64,591,12,2,49,some 64⟩:=PairRoute.start _ leaf8
end Research6969.HardFit13At010
end Z6969Source3058

-- Source: Research6969.HardComplete13
section Z6969Source3059
set_option autoImplicit true
namespace Research6969.HardComplete13
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_4 (j:Fin HighPendingSeed13.regions.size) (l:0≤j.val) (h:j.val<4):Done (12:Fin 18) (HighPendingSeed13.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit13At000.case0
  · exact HardFit13At000.case1
  · exact HardFit13At000.case2
  · exact HardFit13At000.case3
private theorem covered4_9 (j:Fin HighPendingSeed13.regions.size) (l:4≤j.val) (h:j.val<9):Done (12:Fin 18) (HighPendingSeed13.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit13At000.case4
  · exact HardFit13At000.case5
  · exact HardFit13At000.case6
  · exact HardFit13At000.case7
  · exact HardFit13At000.case8
private theorem covered0_9 (j:Fin HighPendingSeed13.regions.size) (l:0≤j.val) (h:j.val<9):Done (12:Fin 18) (HighPendingSeed13.atIndex j):=by
  by_cases low:j.val<4
  · exact covered0_4 j l low
  · exact covered4_9 j (by omega) h
private theorem covered9_14 (j:Fin HighPendingSeed13.regions.size) (l:9≤j.val) (h:j.val<14):Done (12:Fin 18) (HighPendingSeed13.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit13At000.case9
  · exact HardFit13At010.case10
  · exact HardFit13At010.case11
  · exact HardFit13At010.case12
  · exact HardFit13At010.case13
private theorem covered14_19 (j:Fin HighPendingSeed13.regions.size) (l:14≤j.val) (h:j.val<19):Done (12:Fin 18) (HighPendingSeed13.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit13At010.case14
  · exact HardFit13At010.case15
  · exact HardFit13At010.case16
  · exact HardFit13At010.case17
  · exact HardFit13At010.case18
private theorem covered9_19 (j:Fin HighPendingSeed13.regions.size) (l:9≤j.val) (h:j.val<19):Done (12:Fin 18) (HighPendingSeed13.atIndex j):=by
  by_cases low:j.val<14
  · exact covered9_14 j l low
  · exact covered14_19 j (by omega) h
private theorem covered0_19 (j:Fin HighPendingSeed13.regions.size) (l:0≤j.val) (h:j.val<19):Done (12:Fin 18) (HighPendingSeed13.atIndex j):=by
  by_cases low:j.val<9
  · exact covered0_9 j l low
  · exact covered9_19 j (by omega) h
theorem required:HighPendingSeed13.Required:=fun j=>covered0_19 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete13
end Z6969Source3059

-- Source: Research6969.PairReceipts054
section Z6969Source3060
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1080 : List StockPairs.Receipt := [
  ⟨⟨64,628,12,2,13,some 16,0,none,257319,[],[]⟩,13,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,14,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,14,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,14,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,14,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,14,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,14,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,14,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,14,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,14,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,14,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,17,some 20,0,none,257319,[],[]⟩,14,surfaceIntersection⟩,
  ⟨⟨64,628,12,2,13,some 16,0,none,257319,[],[]⟩,14,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,15,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,15,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,15,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,15,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,15,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,15,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,15,surfaceIntersection⟩]
private theorem paid1080 : StockPairs.checked rows1080 = true := by decide +kernel
theorem route1080 (i : Fin 20) : (rows1080.get i).Done :=
  StockPairs.doneAt paid1080 i

end Research6969.PairReceipts
end Z6969Source3060

-- Source: Research6969.HardFit14At000
section Z6969Source3061
set_option autoImplicit true
namespace Research6969.HardFit14At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1060 8)
theorem case0: NormalRoute.Done (13:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1060 7)
theorem case1: NormalRoute.Done (13:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1060 10)
theorem case2: NormalRoute.Done (13:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1060 9)
theorem case3: NormalRoute.Done (13:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1060 12)
theorem case4: NormalRoute.Done (13:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1060 11)
theorem case5: NormalRoute.Done (13:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1060 14)
theorem case6: NormalRoute.Done (13:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1060 13)
theorem case7: NormalRoute.Done (13:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route1080 0)
theorem case8: NormalRoute.Done (13:Fin 18) ⟨64,628,12,2,13,some 16⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route1060 19)
theorem case9: NormalRoute.Done (13:Fin 18) ⟨64,628,12,2,17,some 20⟩:=PairRoute.start _ leaf9
end Research6969.HardFit14At000
end Z6969Source3061

-- Source: Research6969.HardFit14At010
section Z6969Source3062
set_option autoImplicit true
namespace Research6969.HardFit14At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1060 18)
theorem case10: NormalRoute.Done (13:Fin 18) ⟨64,628,12,2,21,some 24⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1060 17)
theorem case11: NormalRoute.Done (13:Fin 18) ⟨64,628,12,2,25,some 28⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1060 16)
theorem case12: NormalRoute.Done (13:Fin 18) ⟨64,628,12,2,29,some 32⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1060 15)
theorem case13: NormalRoute.Done (13:Fin 18) ⟨64,628,12,2,49,some 64⟩:=PairRoute.start _ leaf3
end Research6969.HardFit14At010
end Z6969Source3062

-- Source: Research6969.HardComplete14
section Z6969Source3063
set_option autoImplicit true
namespace Research6969.HardComplete14
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_7 (j:Fin HighPendingSeed14.regions.size) (l:0≤j.val) (h:j.val<7):Done (13:Fin 18) (HighPendingSeed14.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit14At000.case0
  · exact HardFit14At000.case1
  · exact HardFit14At000.case2
  · exact HardFit14At000.case3
  · exact HardFit14At000.case4
  · exact HardFit14At000.case5
  · exact HardFit14At000.case6
private theorem covered7_14 (j:Fin HighPendingSeed14.regions.size) (l:7≤j.val) (h:j.val<14):Done (13:Fin 18) (HighPendingSeed14.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit14At000.case7
  · exact HardFit14At000.case8
  · exact HardFit14At000.case9
  · exact HardFit14At010.case10
  · exact HardFit14At010.case11
  · exact HardFit14At010.case12
  · exact HardFit14At010.case13
private theorem covered0_14 (j:Fin HighPendingSeed14.regions.size) (l:0≤j.val) (h:j.val<14):Done (13:Fin 18) (HighPendingSeed14.atIndex j):=by
  by_cases low:j.val<7
  · exact covered0_7 j l low
  · exact covered7_14 j (by omega) h
theorem required:HighPendingSeed14.Required:=fun j=>covered0_14 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete14
end Z6969Source3063

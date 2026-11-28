import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0680
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0941
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0681

set_option Elab.async false

-- Source: Research6969.HardFit10At000
section Z6969Source3040
set_option autoImplicit true
namespace Research6969.HardFit10At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route960 13)
theorem case0: NormalRoute.Done (9:Fin 18) ⟨28,32,9,2,9,some 12⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route960 12)
theorem case1: NormalRoute.Done (9:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route960 11)
theorem case2: NormalRoute.Done (9:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route960 10)
theorem case3: NormalRoute.Done (9:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route960 9)
theorem case4: NormalRoute.Done (9:Fin 18) ⟨28,32,9,2,25,some 28⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route960 18)
theorem case5: NormalRoute.Done (9:Fin 18) ⟨33,40,9,2,9,some 12⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route960 17)
theorem case6: NormalRoute.Done (9:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route960 16)
theorem case7: NormalRoute.Done (9:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route960 15)
theorem case8: NormalRoute.Done (9:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route960 14)
theorem case9: NormalRoute.Done (9:Fin 18) ⟨33,40,9,2,25,some 28⟩:=PairRoute.start _ leaf9
end Research6969.HardFit10At000
end Z6969Source3040

-- Source: Research6969.PairReceipts049
section Z6969Source3041
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows980 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,9,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨50,63,10,2,49,some 64,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,9,⟨(.node 8023872256819695),.intersection,.impossible,278103⟩⟩,
  ⟨⟨50,63,10,2,49,some 64,0,none,278103,[MeasuredChoices.test104],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩,9,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨64,650,12,2,49,some 56,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨64,650,12,2,41,some 48,0,none,257319,[MeasuredChoices.test49,MeasuredChoices.test50],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨64,650,12,2,33,some 40,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨64,650,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨64,650,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨64,650,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨64,650,12,2,17,some 20,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨64,650,12,2,13,some 16,0,none,257319,[],[]⟩,9,surfaceIntersection⟩,
  ⟨⟨64,650,12,2,9,some 12,0,none,257319,[],[]⟩,9,⟨.surface,.intersection,.surface,0⟩⟩]
private theorem paid980 : StockPairs.checked rows980 = true := by decide +kernel
theorem route980 (i : Fin 20) : (rows980.get i).Done :=
  StockPairs.doneAt paid980 i

end Research6969.PairReceipts
end Z6969Source3041

-- Source: Research6969.HardFit10At010
section Z6969Source3042
set_option autoImplicit true
namespace Research6969.HardFit10At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route980 3)
theorem case10: NormalRoute.Done (9:Fin 18) ⟨41,49,9,2,9,some 12⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route980 2)
theorem case11: NormalRoute.Done (9:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route980 1)
theorem case12: NormalRoute.Done (9:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route980 0)
theorem case13: NormalRoute.Done (9:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route960 19)
theorem case14: NormalRoute.Done (9:Fin 18) ⟨41,49,9,2,25,some 28⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route980 10)
theorem case15: NormalRoute.Done (9:Fin 18) ⟨50,63,10,2,9,some 12⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route980 9)
theorem case16: NormalRoute.Done (9:Fin 18) ⟨50,63,10,2,13,some 16⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route980 8)
theorem case17: NormalRoute.Done (9:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route980 7)
theorem case18: NormalRoute.Done (9:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route980 6)
theorem case19: NormalRoute.Done (9:Fin 18) ⟨50,63,10,2,25,some 28⟩:=PairRoute.start _ leaf9
end Research6969.HardFit10At010
end Z6969Source3042

-- Source: Research6969.HardFit10At020
section Z6969Source3043
set_option autoImplicit true
namespace Research6969.HardFit10At020
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route980 4)
private def leaf1 := (PairReceipts.route980 5)
private def weight2 := PairRoute.weight 278103 leaf0 leaf1
theorem case20: NormalRoute.Done (9:Fin 18) ⟨50,63,10,2,49,some 64⟩:=PairRoute.start _ weight2
private def leaf3 := (PairReceipts.route980 19)
theorem case21: NormalRoute.Done (9:Fin 18) ⟨64,650,12,2,9,some 12⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route980 18)
theorem case22: NormalRoute.Done (9:Fin 18) ⟨64,650,12,2,13,some 16⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route980 17)
theorem case23: NormalRoute.Done (9:Fin 18) ⟨64,650,12,2,17,some 20⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route980 16)
theorem case24: NormalRoute.Done (9:Fin 18) ⟨64,650,12,2,21,some 24⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route980 15)
theorem case25: NormalRoute.Done (9:Fin 18) ⟨64,650,12,2,25,some 28⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route980 14)
theorem case26: NormalRoute.Done (9:Fin 18) ⟨64,650,12,2,29,some 32⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route980 13)
theorem case27: NormalRoute.Done (9:Fin 18) ⟨64,650,12,2,33,some 40⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route980 12)
theorem case28: NormalRoute.Done (9:Fin 18) ⟨64,650,12,2,41,some 48⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route980 11)
theorem case29: NormalRoute.Done (9:Fin 18) ⟨64,650,12,2,49,some 56⟩:=PairRoute.start _ leaf11
end Research6969.HardFit10At020
end Z6969Source3043

-- Source: Research6969.HardComplete10
section Z6969Source3044
set_option autoImplicit true
namespace Research6969.HardComplete10
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_7 (j:Fin HighPendingSeed10.regions.size) (l:0≤j.val) (h:j.val<7):Done (9:Fin 18) (HighPendingSeed10.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit10At000.case0
  · exact HardFit10At000.case1
  · exact HardFit10At000.case2
  · exact HardFit10At000.case3
  · exact HardFit10At000.case4
  · exact HardFit10At000.case5
  · exact HardFit10At000.case6
private theorem covered7_15 (j:Fin HighPendingSeed10.regions.size) (l:7≤j.val) (h:j.val<15):Done (9:Fin 18) (HighPendingSeed10.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit10At000.case7
  · exact HardFit10At000.case8
  · exact HardFit10At000.case9
  · exact HardFit10At010.case10
  · exact HardFit10At010.case11
  · exact HardFit10At010.case12
  · exact HardFit10At010.case13
  · exact HardFit10At010.case14
private theorem covered0_15 (j:Fin HighPendingSeed10.regions.size) (l:0≤j.val) (h:j.val<15):Done (9:Fin 18) (HighPendingSeed10.atIndex j):=by
  by_cases low:j.val<7
  · exact covered0_7 j l low
  · exact covered7_15 j (by omega) h
private theorem covered15_22 (j:Fin HighPendingSeed10.regions.size) (l:15≤j.val) (h:j.val<22):Done (9:Fin 18) (HighPendingSeed10.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit10At010.case15
  · exact HardFit10At010.case16
  · exact HardFit10At010.case17
  · exact HardFit10At010.case18
  · exact HardFit10At010.case19
  · exact HardFit10At020.case20
  · exact HardFit10At020.case21
private theorem covered22_30 (j:Fin HighPendingSeed10.regions.size) (l:22≤j.val) (h:j.val<30):Done (9:Fin 18) (HighPendingSeed10.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit10At020.case22
  · exact HardFit10At020.case23
  · exact HardFit10At020.case24
  · exact HardFit10At020.case25
  · exact HardFit10At020.case26
  · exact HardFit10At020.case27
  · exact HardFit10At020.case28
  · exact HardFit10At020.case29
private theorem covered15_30 (j:Fin HighPendingSeed10.regions.size) (l:15≤j.val) (h:j.val<30):Done (9:Fin 18) (HighPendingSeed10.atIndex j):=by
  by_cases low:j.val<22
  · exact covered15_22 j l low
  · exact covered22_30 j (by omega) h
private theorem covered0_30 (j:Fin HighPendingSeed10.regions.size) (l:0≤j.val) (h:j.val<30):Done (9:Fin 18) (HighPendingSeed10.atIndex j):=by
  by_cases low:j.val<15
  · exact covered0_15 j l low
  · exact covered15_30 j (by omega) h
theorem required:HighPendingSeed10.Required:=fun j=>covered0_30 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete10
end Z6969Source3044

-- Source: Research6969.PairReceipts050
section Z6969Source3045
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1000 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,49,some 64,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,49,some 56,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,41,some 48,0,none,257319,[MeasuredChoices.test49,MeasuredChoices.test50],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,33,some 40,0,none,257319,[MeasuredChoices.test43,MeasuredChoices.test44],[]⟩,10,surfaceIntersection⟩]
private theorem paid1000 : StockPairs.checked rows1000 = true := by decide +kernel
theorem route1000 (i : Fin 20) : (rows1000.get i).Done :=
  StockPairs.doneAt paid1000 i

end Research6969.PairReceipts
end Z6969Source3045

-- Source: Research6969.HardFit11At000
section Z6969Source3046
set_option autoImplicit true
namespace Research6969.HardFit11At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1000 3)
theorem case0: NormalRoute.Done (10:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1000 2)
theorem case1: NormalRoute.Done (10:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1000 1)
theorem case2: NormalRoute.Done (10:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1000 0)
theorem case3: NormalRoute.Done (10:Fin 18) ⟨28,32,9,2,25,some 28⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1000 7)
theorem case4: NormalRoute.Done (10:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1000 6)
theorem case5: NormalRoute.Done (10:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1000 5)
theorem case6: NormalRoute.Done (10:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1000 4)
theorem case7: NormalRoute.Done (10:Fin 18) ⟨33,40,9,2,25,some 28⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route1000 11)
theorem case8: NormalRoute.Done (10:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route1000 10)
theorem case9: NormalRoute.Done (10:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf9
end Research6969.HardFit11At000
end Z6969Source3046

-- Source: Research6969.PairReceipts051
section Z6969Source3047
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1020 : List StockPairs.Receipt := [
  ⟨⟨64,654,12,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,25,some 28,0,none,257319,[MeasuredChoices.test35,MeasuredChoices.test36],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,21,some 24,0,none,257319,[MeasuredChoices.test26],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,17,some 20,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,13,some 16,0,none,257319,[],[]⟩,10,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,9,some 12,0,none,257319,[],[]⟩,10,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨28,32,9,2,21,some 24,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,17,some 20,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨28,32,9,2,13,some 16,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,49,some 64,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,11,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,11,surfaceIntersection⟩]
private theorem paid1020 : StockPairs.checked rows1020 = true := by decide +kernel
theorem route1020 (i : Fin 20) : (rows1020.get i).Done :=
  StockPairs.doneAt paid1020 i

end Research6969.PairReceipts
end Z6969Source3047

-- Source: Research6969.HardFit11At010
section Z6969Source3048
set_option autoImplicit true
namespace Research6969.HardFit11At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1000 9)
theorem case10: NormalRoute.Done (10:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1000 8)
theorem case11: NormalRoute.Done (10:Fin 18) ⟨41,49,9,2,25,some 28⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1000 16)
theorem case12: NormalRoute.Done (10:Fin 18) ⟨50,63,10,2,13,some 16⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1000 15)
theorem case13: NormalRoute.Done (10:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1000 14)
theorem case14: NormalRoute.Done (10:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1000 13)
theorem case15: NormalRoute.Done (10:Fin 18) ⟨50,63,10,2,25,some 28⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1000 12)
theorem case16: NormalRoute.Done (10:Fin 18) ⟨50,63,10,2,49,some 64⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1020 5)
theorem case17: NormalRoute.Done (10:Fin 18) ⟨64,654,12,2,9,some 12⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route1020 4)
theorem case18: NormalRoute.Done (10:Fin 18) ⟨64,654,12,2,13,some 16⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route1020 3)
theorem case19: NormalRoute.Done (10:Fin 18) ⟨64,654,12,2,17,some 20⟩:=PairRoute.start _ leaf9
end Research6969.HardFit11At010
end Z6969Source3048

-- Source: Research6969.HardFit11At020
section Z6969Source3049
set_option autoImplicit true
namespace Research6969.HardFit11At020
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1020 2)
theorem case20: NormalRoute.Done (10:Fin 18) ⟨64,654,12,2,21,some 24⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1020 1)
theorem case21: NormalRoute.Done (10:Fin 18) ⟨64,654,12,2,25,some 28⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1020 0)
theorem case22: NormalRoute.Done (10:Fin 18) ⟨64,654,12,2,29,some 32⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1000 19)
theorem case23: NormalRoute.Done (10:Fin 18) ⟨64,654,12,2,33,some 40⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1000 18)
theorem case24: NormalRoute.Done (10:Fin 18) ⟨64,654,12,2,41,some 48⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1000 17)
theorem case25: NormalRoute.Done (10:Fin 18) ⟨64,654,12,2,49,some 56⟩:=PairRoute.start _ leaf5
end Research6969.HardFit11At020
end Z6969Source3049

-- Source: Research6969.HardComplete11
section Z6969Source3050
set_option autoImplicit true
namespace Research6969.HardComplete11
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_6 (j:Fin HighPendingSeed11.regions.size) (l:0≤j.val) (h:j.val<6):Done (10:Fin 18) (HighPendingSeed11.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit11At000.case0
  · exact HardFit11At000.case1
  · exact HardFit11At000.case2
  · exact HardFit11At000.case3
  · exact HardFit11At000.case4
  · exact HardFit11At000.case5
private theorem covered6_13 (j:Fin HighPendingSeed11.regions.size) (l:6≤j.val) (h:j.val<13):Done (10:Fin 18) (HighPendingSeed11.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit11At000.case6
  · exact HardFit11At000.case7
  · exact HardFit11At000.case8
  · exact HardFit11At000.case9
  · exact HardFit11At010.case10
  · exact HardFit11At010.case11
  · exact HardFit11At010.case12
private theorem covered0_13 (j:Fin HighPendingSeed11.regions.size) (l:0≤j.val) (h:j.val<13):Done (10:Fin 18) (HighPendingSeed11.atIndex j):=by
  by_cases low:j.val<6
  · exact covered0_6 j l low
  · exact covered6_13 j (by omega) h
private theorem covered13_19 (j:Fin HighPendingSeed11.regions.size) (l:13≤j.val) (h:j.val<19):Done (10:Fin 18) (HighPendingSeed11.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit11At010.case13
  · exact HardFit11At010.case14
  · exact HardFit11At010.case15
  · exact HardFit11At010.case16
  · exact HardFit11At010.case17
  · exact HardFit11At010.case18
private theorem covered19_26 (j:Fin HighPendingSeed11.regions.size) (l:19≤j.val) (h:j.val<26):Done (10:Fin 18) (HighPendingSeed11.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit11At010.case19
  · exact HardFit11At020.case20
  · exact HardFit11At020.case21
  · exact HardFit11At020.case22
  · exact HardFit11At020.case23
  · exact HardFit11At020.case24
  · exact HardFit11At020.case25
private theorem covered13_26 (j:Fin HighPendingSeed11.regions.size) (l:13≤j.val) (h:j.val<26):Done (10:Fin 18) (HighPendingSeed11.atIndex j):=by
  by_cases low:j.val<19
  · exact covered13_19 j l low
  · exact covered19_26 j (by omega) h
private theorem covered0_26 (j:Fin HighPendingSeed11.regions.size) (l:0≤j.val) (h:j.val<26):Done (10:Fin 18) (HighPendingSeed11.atIndex j):=by
  by_cases low:j.val<13
  · exact covered0_13 j l low
  · exact covered13_26 j (by omega) h
theorem required:HighPendingSeed11.Required:=fun j=>covered0_26 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete11
end Z6969Source3050

-- Source: Research6969.HardFit12At000
section Z6969Source3051
set_option autoImplicit true
namespace Research6969.HardFit12At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1020 8)
theorem case0: NormalRoute.Done (11:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1020 7)
theorem case1: NormalRoute.Done (11:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1020 6)
theorem case2: NormalRoute.Done (11:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1020 11)
theorem case3: NormalRoute.Done (11:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1020 10)
theorem case4: NormalRoute.Done (11:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1020 9)
theorem case5: NormalRoute.Done (11:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1020 14)
theorem case6: NormalRoute.Done (11:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1020 13)
theorem case7: NormalRoute.Done (11:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route1020 12)
theorem case8: NormalRoute.Done (11:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route1020 19)
theorem case9: NormalRoute.Done (11:Fin 18) ⟨50,63,10,2,13,some 16⟩:=PairRoute.start _ leaf9
end Research6969.HardFit12At000
end Z6969Source3051

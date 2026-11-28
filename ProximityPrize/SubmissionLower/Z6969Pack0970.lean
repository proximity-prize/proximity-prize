import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0673
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0968
import ProximityPrize.SubmissionLower.Z6969Pack0969
import ProximityPrize.SubmissionLower.Z6969Pack0675
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0939

set_option Elab.async false

-- Source: Research6969.HardFit5At080
section Z6969Source2980
set_option autoImplicit true
namespace Research6969.HardFit5At080
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4522 11)
private def terminalLeaf7010 := (PairReceipts.route4522 12)
private def terminalLeaf7011 := (PairReceipts.route4522 13)
private def terminalLeaf7012 := (PairReceipts.route4522 14)
private def terminalLeaf7013 := (PairReceipts.route4522 15)
private def leaf1 := PairRoute.splitSeed 35 terminalLeaf7010 (PairRoute.axes_of_total (PairRoute.axis 13 terminalLeaf7011 (PairRoute.axis 19 terminalLeaf7012 terminalLeaf7013)))
private def weight2 := PairRoute.weight 298829 leaf0 leaf1
theorem case80: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,33,some 36⟩:=PairRoute.start _ weight2
private def leaf3 := (PairReceipts.route4522 9)
private def leaf4 := (PairReceipts.route4522 10)
private def weight5 := PairRoute.weight 296579 leaf3 leaf4
theorem case81: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,37,some 40⟩:=PairRoute.start _ weight5
private def leaf6 := (PairReceipts.route4522 6)
private def terminalLeaf7030 := (PairReceipts.route4522 7)
private def terminalLeaf7031 := (PairReceipts.route4522 8)
private def leaf7 := PairRoute.splitSeed 43 terminalLeaf7030 terminalLeaf7031
private def weight8 := PairRoute.weight 294092 leaf6 leaf7
theorem case82: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,41,some 44⟩:=PairRoute.start _ weight8
private def leaf9 := (PairReceipts.route4522 5)
theorem case83: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,45,some 46⟩:=PairRoute.start _ leaf9
private def leaf10 := (PairReceipts.route4522 4)
theorem case84: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,47,some 47⟩:=PairRoute.start _ leaf10
private def leaf11 := (PairReceipts.route4522 2)
private def leaf12 := (PairReceipts.route4522 3)
private def weight13 := PairRoute.weight 303874 leaf11 leaf12
theorem case85: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,48,some 48⟩:=PairRoute.start _ weight13
private def leaf14 := (PairReceipts.route4522 0)
private def leaf15 := (PairReceipts.route4522 1)
private def weight16 := PairRoute.weight 290650 leaf14 leaf15
theorem case86: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,49,some 49⟩:=PairRoute.start _ weight16
private theorem allAxes118:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,50,some 50⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 50 ⟨
    (PairReceipts.route4471 0),
    (PairReceipts.route4471 1),
    (PairReceipts.route4471 2),
    (PairReceipts.route4471 3),
    (PairReceipts.route4471 4),
    (PairReceipts.route4471 5),
    (PairReceipts.route4471 6),
    (PairReceipts.route4471 7),
    (PairReceipts.route4471 8),
    (PairReceipts.route4480 0),
    (PairReceipts.route4480 1),
    (PairReceipts.route4480 2),
    (PairReceipts.route4480 3),
    (PairReceipts.route4480 4),
    (PairReceipts.route4480 5),
    (PairReceipts.route4480 6),
    (PairReceipts.route4480 7),
    (PairReceipts.route4480 8),
    (PairReceipts.route4480 9),
    (PairReceipts.route4480 10),
    (PairReceipts.route4480 11),
    PairLeaves.excluded PairReceipts.cell4492 PairReceipts.check4492 (none),
    PairLeaves.excluded PairReceipts.cell4493 PairReceipts.check4493 (none),
    PairLeaves.excluded PairReceipts.cell4494 PairReceipts.check4494 (none),
    PairLeaves.excluded PairReceipts.cell4495 PairReceipts.check4495 (none),
    PairLeaves.excluded PairReceipts.cell4496 PairReceipts.check4496 (none),
    PairLeaves.excluded PairReceipts.cell4497 PairReceipts.check4497 (none),
    PairLeaves.excluded PairReceipts.cell4498 PairReceipts.check4498 (none),
    PairLeaves.excluded PairReceipts.cell4499 PairReceipts.check4499 (none),
    PairLeaves.excluded PairReceipts.cell4500 PairReceipts.check4500 (none),
    PairLeaves.excluded PairReceipts.cell4501 PairReceipts.check4501 (none),
    PairLeaves.excluded PairReceipts.cell4502 PairReceipts.check4502 (none),
    PairLeaves.excluded PairReceipts.cell4503 PairReceipts.check4503 (none),
    PairLeaves.excluded PairReceipts.cell4504 PairReceipts.check4504 (none),
    PairLeaves.excluded PairReceipts.cell4505 PairReceipts.check4505 (none),
    PairLeaves.excluded PairReceipts.cell4506 PairReceipts.check4506 (none),
    PairLeaves.excluded PairReceipts.cell4507 PairReceipts.check4507 (none),
    PairLeaves.excluded PairReceipts.cell4508 PairReceipts.check4508 (none),
    PairLeaves.excluded PairReceipts.cell4509 PairReceipts.check4509 (none),
    PairLeaves.excluded PairReceipts.cell4510 PairReceipts.check4510 (none),
    PairLeaves.excluded PairReceipts.cell4511 PairReceipts.check4511 (none),
    PairLeaves.excluded PairReceipts.cell4512 PairReceipts.check4512 (none),
    PairLeaves.excluded PairReceipts.cell4513 PairReceipts.check4513 (none),
    PairLeaves.excluded PairReceipts.cell4514 PairReceipts.check4514 (none),
    PairLeaves.excluded PairReceipts.cell4515 PairReceipts.check4515 (none),
    PairLeaves.excluded PairReceipts.cell4516 PairReceipts.check4516 (none),
    PairLeaves.excluded PairReceipts.cell4517 PairReceipts.check4517 (none),
    PairLeaves.excluded PairReceipts.cell4518 PairReceipts.check4518 (none),
    PairLeaves.excluded PairReceipts.cell4519 PairReceipts.check4519 (none),
    PairLeaves.excluded PairReceipts.cell4520 PairReceipts.check4520 (none),
    PairLeaves.excluded PairReceipts.cell4521 PairReceipts.check4521 (none),
    trivial⟩)
theorem case87: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,50,some 50⟩:=PairRoute.start _ allAxes118
private theorem allAxes222:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,51,some 51⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 51 ⟨
    (PairReceipts.route4400 18),
    (PairReceipts.route4420 0),
    (PairReceipts.route4420 1),
    (PairReceipts.route4420 2),
    (PairReceipts.route4420 3),
    (PairReceipts.route4420 4),
    (PairReceipts.route4420 5),
    (PairReceipts.route4420 6),
    (PairReceipts.route4420 7),
    (PairReceipts.route4420 8),
    (PairReceipts.route4420 9),
    (PairReceipts.route4420 10),
    (PairReceipts.route4420 11),
    (PairReceipts.route4420 12),
    (PairReceipts.route4420 13),
    (PairReceipts.route4420 14),
    (PairReceipts.route4420 15),
    (PairReceipts.route4420 16),
    (PairReceipts.route4420 17),
    (PairReceipts.route4420 18),
    (PairReceipts.route4420 19),
    PairLeaves.excluded PairReceipts.cell4440 PairReceipts.check4440 (none),
    PairLeaves.excluded PairReceipts.cell4441 PairReceipts.check4441 (none),
    PairLeaves.excluded PairReceipts.cell4442 PairReceipts.check4442 (none),
    PairLeaves.excluded PairReceipts.cell4443 PairReceipts.check4443 (none),
    PairLeaves.excluded PairReceipts.cell4444 PairReceipts.check4444 (none),
    PairLeaves.excluded PairReceipts.cell4445 PairReceipts.check4445 (none),
    PairLeaves.excluded PairReceipts.cell4446 PairReceipts.check4446 (none),
    PairLeaves.excluded PairReceipts.cell4447 PairReceipts.check4447 (none),
    PairLeaves.excluded PairReceipts.cell4448 PairReceipts.check4448 (none),
    PairLeaves.excluded PairReceipts.cell4449 PairReceipts.check4449 (none),
    PairLeaves.excluded PairReceipts.cell4450 PairReceipts.check4450 (none),
    PairLeaves.excluded PairReceipts.cell4451 PairReceipts.check4451 (none),
    PairLeaves.excluded PairReceipts.cell4452 PairReceipts.check4452 (none),
    PairLeaves.excluded PairReceipts.cell4453 PairReceipts.check4453 (none),
    PairLeaves.excluded PairReceipts.cell4454 PairReceipts.check4454 (none),
    PairLeaves.excluded PairReceipts.cell4455 PairReceipts.check4455 (none),
    PairLeaves.excluded PairReceipts.cell4456 PairReceipts.check4456 (none),
    PairLeaves.excluded PairReceipts.cell4457 PairReceipts.check4457 (none),
    PairLeaves.excluded PairReceipts.cell4458 PairReceipts.check4458 (none),
    PairLeaves.excluded PairReceipts.cell4459 PairReceipts.check4459 (none),
    PairLeaves.excluded PairReceipts.cell4460 PairReceipts.check4460 (none),
    PairLeaves.excluded PairReceipts.cell4461 PairReceipts.check4461 (none),
    PairLeaves.excluded PairReceipts.cell4462 PairReceipts.check4462 (none),
    PairLeaves.excluded PairReceipts.cell4463 PairReceipts.check4463 (none),
    PairLeaves.excluded PairReceipts.cell4464 PairReceipts.check4464 (none),
    PairLeaves.excluded PairReceipts.cell4465 PairReceipts.check4465 (none),
    PairLeaves.excluded PairReceipts.cell4466 PairReceipts.check4466 (none),
    PairLeaves.excluded PairReceipts.cell4467 PairReceipts.check4467 (none),
    PairLeaves.excluded PairReceipts.cell4468 PairReceipts.check4468 (none),
    PairLeaves.excluded PairReceipts.cell4469 PairReceipts.check4469 (none),
    PairLeaves.excluded PairReceipts.cell4470 PairReceipts.check4470 (none),
    trivial⟩)
theorem case88: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,51,some 51⟩:=PairRoute.start _ allAxes222
private def leaf223 := (PairReceipts.route4400 17)
private theorem leaf224:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,52,some 52⟩,0,none,288407,none⟩:=PairLeaves.excluded PairReceipts.cell4418 PairReceipts.check4418 (none)
private def weight225 := PairRoute.weight 288407 leaf223 leaf224
theorem case89: NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,52,some 52⟩:=PairRoute.start _ weight225
end Research6969.HardFit5At080
end Z6969Source2980

-- Source: Research6969.HardComplete5
section Z6969Source2981
set_option autoImplicit true
namespace Research6969.HardComplete5
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_5 (j:Fin HighPendingSeed5.regions.size) (l:0≤j.val) (h:j.val<5):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At000.case0
  · exact HardFit5At000.case1
  · exact HardFit5At000.case2
  · exact HardFit5At000.case3
  · exact HardFit5At000.case4
private theorem covered5_11 (j:Fin HighPendingSeed5.regions.size) (l:5≤j.val) (h:j.val<11):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At000.case5
  · exact HardFit5At000.case6
  · exact HardFit5At000.case7
  · exact HardFit5At000.case8
  · exact HardFit5At000.case9
  · exact HardFit5At010.case10
private theorem covered0_11 (j:Fin HighPendingSeed5.regions.size) (l:0≤j.val) (h:j.val<11):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<5
  · exact covered0_5 j l low
  · exact covered5_11 j (by omega) h
private theorem covered11_16 (j:Fin HighPendingSeed5.regions.size) (l:11≤j.val) (h:j.val<16):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At010.case11
  · exact HardFit5At010.case12
  · exact HardFit5At010.case13
  · exact HardFit5At010.case14
  · exact HardFit5At010.case15
private theorem covered16_22 (j:Fin HighPendingSeed5.regions.size) (l:16≤j.val) (h:j.val<22):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At010.case16
  · exact HardFit5At010.case17
  · exact HardFit5At010.case18
  · exact HardFit5At010.case19
  · exact HardFit5At020.case20
  · exact HardFit5At020.case21
private theorem covered11_22 (j:Fin HighPendingSeed5.regions.size) (l:11≤j.val) (h:j.val<22):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<16
  · exact covered11_16 j l low
  · exact covered16_22 j (by omega) h
private theorem covered0_22 (j:Fin HighPendingSeed5.regions.size) (l:0≤j.val) (h:j.val<22):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<11
  · exact covered0_11 j l low
  · exact covered11_22 j (by omega) h
private theorem covered22_27 (j:Fin HighPendingSeed5.regions.size) (l:22≤j.val) (h:j.val<27):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At020.case22
  · exact HardFit5At020.case23
  · exact HardFit5At020.case24
  · exact HardFit5At020.case25
  · exact HardFit5At020.case26
private theorem covered27_33 (j:Fin HighPendingSeed5.regions.size) (l:27≤j.val) (h:j.val<33):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At020.case27
  · exact HardFit5At020.case28
  · exact HardFit5At020.case29
  · exact HardFit5At030.case30
  · exact HardFit5At030.case31
  · exact HardFit5At030.case32
private theorem covered22_33 (j:Fin HighPendingSeed5.regions.size) (l:22≤j.val) (h:j.val<33):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<27
  · exact covered22_27 j l low
  · exact covered27_33 j (by omega) h
private theorem covered33_39 (j:Fin HighPendingSeed5.regions.size) (l:33≤j.val) (h:j.val<39):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At030.case33
  · exact HardFit5At030.case34
  · exact HardFit5At030.case35
  · exact HardFit5At030.case36
  · exact HardFit5At030.case37
  · exact HardFit5At030.case38
private theorem covered39_45 (j:Fin HighPendingSeed5.regions.size) (l:39≤j.val) (h:j.val<45):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At030.case39
  · exact HardFit5At040.case40
  · exact HardFit5At040.case41
  · exact HardFit5At040.case42
  · exact HardFit5At040.case43
  · exact HardFit5At040.case44
private theorem covered33_45 (j:Fin HighPendingSeed5.regions.size) (l:33≤j.val) (h:j.val<45):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<39
  · exact covered33_39 j l low
  · exact covered39_45 j (by omega) h
private theorem covered22_45 (j:Fin HighPendingSeed5.regions.size) (l:22≤j.val) (h:j.val<45):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<33
  · exact covered22_33 j l low
  · exact covered33_45 j (by omega) h
private theorem covered0_45 (j:Fin HighPendingSeed5.regions.size) (l:0≤j.val) (h:j.val<45):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<22
  · exact covered0_22 j l low
  · exact covered22_45 j (by omega) h
private theorem covered45_50 (j:Fin HighPendingSeed5.regions.size) (l:45≤j.val) (h:j.val<50):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At040.case45
  · exact HardFit5At040.case46
  · exact HardFit5At040.case47
  · exact HardFit5At040.case48
  · exact HardFit5At040.case49
private theorem covered50_56 (j:Fin HighPendingSeed5.regions.size) (l:50≤j.val) (h:j.val<56):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At050.case50
  · exact HardFit5At050.case51
  · exact HardFit5At050.case52
  · exact HardFit5At050.case53
  · exact HardFit5At050.case54
  · exact HardFit5At050.case55
private theorem covered45_56 (j:Fin HighPendingSeed5.regions.size) (l:45≤j.val) (h:j.val<56):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<50
  · exact covered45_50 j l low
  · exact covered50_56 j (by omega) h
private theorem covered56_61 (j:Fin HighPendingSeed5.regions.size) (l:56≤j.val) (h:j.val<61):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At050.case56
  · exact HardFit5At050.case57
  · exact HardFit5At050.case58
  · exact HardFit5At050.case59
  · exact HardFit5At060.case60
private theorem covered61_67 (j:Fin HighPendingSeed5.regions.size) (l:61≤j.val) (h:j.val<67):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At060.case61
  · exact HardFit5At060.case62
  · exact HardFit5At060.case63
  · exact HardFit5At060.case64
  · exact HardFit5At060.case65
  · exact HardFit5At060.case66
private theorem covered56_67 (j:Fin HighPendingSeed5.regions.size) (l:56≤j.val) (h:j.val<67):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<61
  · exact covered56_61 j l low
  · exact covered61_67 j (by omega) h
private theorem covered45_67 (j:Fin HighPendingSeed5.regions.size) (l:45≤j.val) (h:j.val<67):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<56
  · exact covered45_56 j l low
  · exact covered56_67 j (by omega) h
private theorem covered67_72 (j:Fin HighPendingSeed5.regions.size) (l:67≤j.val) (h:j.val<72):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At060.case67
  · exact HardFit5At060.case68
  · exact HardFit5At060.case69
  · exact HardFit5At070.case70
  · exact HardFit5At070.case71
private theorem covered72_78 (j:Fin HighPendingSeed5.regions.size) (l:72≤j.val) (h:j.val<78):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At070.case72
  · exact HardFit5At070.case73
  · exact HardFit5At070.case74
  · exact HardFit5At070.case75
  · exact HardFit5At070.case76
  · exact HardFit5At070.case77
private theorem covered67_78 (j:Fin HighPendingSeed5.regions.size) (l:67≤j.val) (h:j.val<78):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<72
  · exact covered67_72 j l low
  · exact covered72_78 j (by omega) h
private theorem covered78_84 (j:Fin HighPendingSeed5.regions.size) (l:78≤j.val) (h:j.val<84):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At070.case78
  · exact HardFit5At070.case79
  · exact HardFit5At080.case80
  · exact HardFit5At080.case81
  · exact HardFit5At080.case82
  · exact HardFit5At080.case83
private theorem covered84_90 (j:Fin HighPendingSeed5.regions.size) (l:84≤j.val) (h:j.val<90):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit5At080.case84
  · exact HardFit5At080.case85
  · exact HardFit5At080.case86
  · exact HardFit5At080.case87
  · exact HardFit5At080.case88
  · exact HardFit5At080.case89
private theorem covered78_90 (j:Fin HighPendingSeed5.regions.size) (l:78≤j.val) (h:j.val<90):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<84
  · exact covered78_84 j l low
  · exact covered84_90 j (by omega) h
private theorem covered67_90 (j:Fin HighPendingSeed5.regions.size) (l:67≤j.val) (h:j.val<90):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<78
  · exact covered67_78 j l low
  · exact covered78_90 j (by omega) h
private theorem covered45_90 (j:Fin HighPendingSeed5.regions.size) (l:45≤j.val) (h:j.val<90):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<67
  · exact covered45_67 j l low
  · exact covered67_90 j (by omega) h
private theorem covered0_90 (j:Fin HighPendingSeed5.regions.size) (l:0≤j.val) (h:j.val<90):Done (4:Fin 18) (HighPendingSeed5.atIndex j):=by
  by_cases low:j.val<45
  · exact covered0_45 j l low
  · exact covered45_90 j (by omega) h
theorem required:HighPendingSeed5.Required:=fun j=>covered0_90 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete5
end Z6969Source2981

-- Source: Research6969.HardFit6At000
section Z6969Source2982
set_option autoImplicit true
namespace Research6969.HardFit6At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4540 11)
theorem case0: NormalRoute.Done (5:Fin 18) ⟨25,27,9,2,9,some 12⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4540 10)
theorem case1: NormalRoute.Done (5:Fin 18) ⟨25,27,9,2,13,some 16⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4540 9)
theorem case2: NormalRoute.Done (5:Fin 18) ⟨25,27,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4540 8)
theorem case3: NormalRoute.Done (5:Fin 18) ⟨25,27,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4540 7)
theorem case4: NormalRoute.Done (5:Fin 18) ⟨25,27,9,2,25,some 28⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4540 14)
theorem case5: NormalRoute.Done (5:Fin 18) ⟨25,27,9,3,9,some 12⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4540 13)
theorem case6: NormalRoute.Done (5:Fin 18) ⟨25,27,9,3,13,some 16⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4540 12)
theorem case7: NormalRoute.Done (5:Fin 18) ⟨25,27,9,3,17,some 20⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4540 19)
theorem case8: NormalRoute.Done (5:Fin 18) ⟨28,32,9,2,9,some 12⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4540 18)
theorem case9: NormalRoute.Done (5:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf9
end Research6969.HardFit6At000
end Z6969Source2982

-- Source: Research6969.PairReceipts228
section Z6969Source2983
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4560 : List StockPairs.Receipt := [
  ⟨⟨28,32,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨28,32,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,21,some 24,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,17,some 20,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,13,some 16,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨33,40,9,2,9,some 12,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨33,40,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,0,some 0,257319,[MeasuredChoices.test62],[]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,1,some 1,257319,[MeasuredChoices.test62],[]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,2,some 2,257319,[MeasuredChoices.test62],[]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,3,some 3,257319,[MeasuredChoices.test62],[]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,4,some 4,257319,[MeasuredChoices.test62],[]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,5,some 5,257319,[MeasuredChoices.test62],[]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,6,some 6,257319,[MeasuredChoices.test62],[]⟩,5,separateIntersection⟩]
private theorem paid4560 : StockPairs.checked rows4560 = true := by decide +kernel
theorem route4560 (i : Fin 20) : (rows4560.get i).Done :=
  StockPairs.doneAt paid4560 i

end Research6969.PairReceipts
end Z6969Source2983

-- Source: Research6969.HardFit6At010
section Z6969Source2984
set_option autoImplicit true
namespace Research6969.HardFit6At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4540 17)
theorem case10: NormalRoute.Done (5:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4540 16)
theorem case11: NormalRoute.Done (5:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4540 15)
theorem case12: NormalRoute.Done (5:Fin 18) ⟨28,32,9,2,25,some 28⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4560 3)
theorem case13: NormalRoute.Done (5:Fin 18) ⟨28,32,9,3,9,some 12⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4560 2)
theorem case14: NormalRoute.Done (5:Fin 18) ⟨28,32,9,3,13,some 16⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4560 1)
theorem case15: NormalRoute.Done (5:Fin 18) ⟨28,32,9,3,17,some 20⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4560 0)
theorem case16: NormalRoute.Done (5:Fin 18) ⟨28,32,9,3,21,some 24⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4560 8)
theorem case17: NormalRoute.Done (5:Fin 18) ⟨33,40,9,2,9,some 12⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4560 7)
theorem case18: NormalRoute.Done (5:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4560 6)
theorem case19: NormalRoute.Done (5:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf9
end Research6969.HardFit6At010
end Z6969Source2984

-- Source: Research6969.PairReceipts231
section Z6969Source2985
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell4620:PairCell.Row:=⟨41,49,9,2,49,some 64,47,some 47,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4620:(cell4620.cap (5:Fin 18)).grade<cell4620.lowerGrade-cell4620.off:=by decide +kernel
def cell4621:PairCell.Row:=⟨41,49,9,2,49,some 64,48,some 48,257319,[MeasuredChoices.test62],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check4621:(cell4621.cap (5:Fin 18)).grade<cell4621.lowerGrade-cell4621.off:=by decide +kernel
def cell4622:PairCell.Row:=⟨41,49,9,2,49,some 64,49,some 49,257319,[MeasuredChoices.test62],[AxisChoices.test1812]⟩
theorem check4622:(cell4622.cap (5:Fin 18)).grade<cell4622.lowerGrade-cell4622.off:=by decide +kernel
def cell4623:PairCell.Row:=⟨41,49,9,2,49,some 64,50,some 50,257319,[MeasuredChoices.test62],[AxisChoices.test1813]⟩
theorem check4623:(cell4623.cap (5:Fin 18)).grade<cell4623.lowerGrade-cell4623.off:=by decide +kernel
def cell4624:PairCell.Row:=⟨41,49,9,2,49,some 64,51,some 51,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check4624:(cell4624.cap (5:Fin 18)).grade<cell4624.lowerGrade-cell4624.off:=by decide +kernel
def cell4625:PairCell.Row:=⟨41,49,9,2,49,some 64,52,some 52,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check4625:(cell4625.cap (5:Fin 18)).grade<cell4625.lowerGrade-cell4625.off:=by decide +kernel
def cell4626:PairCell.Row:=⟨41,49,9,2,49,some 64,53,some 53,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1816]⟩
theorem check4626:(cell4626.cap (5:Fin 18)).grade<cell4626.lowerGrade-cell4626.off:=by decide +kernel
def cell4627:PairCell.Row:=⟨41,49,9,2,49,some 64,54,some 54,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check4627:(cell4627.cap (5:Fin 18)).grade<cell4627.lowerGrade-cell4627.off:=by decide +kernel
def cell4628:PairCell.Row:=⟨41,49,9,2,49,some 64,55,some 55,257319,[MeasuredChoices.test62],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check4628:(cell4628.cap (5:Fin 18)).grade<cell4628.lowerGrade-cell4628.off:=by decide +kernel
def cell4629:PairCell.Row:=⟨41,49,9,2,49,some 64,56,some 56,257319,[MeasuredChoices.test62],[AxisChoices.test1819]⟩
theorem check4629:(cell4629.cap (5:Fin 18)).grade<cell4629.lowerGrade-cell4629.off:=by decide +kernel
def cell4630:PairCell.Row:=⟨41,49,9,2,49,some 64,57,some 57,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4630:(cell4630.cap (5:Fin 18)).grade<cell4630.lowerGrade-cell4630.off:=by decide +kernel
def cell4631:PairCell.Row:=⟨41,49,9,2,49,some 64,58,some 58,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4631:(cell4631.cap (5:Fin 18)).grade<cell4631.lowerGrade-cell4631.off:=by decide +kernel
def cell4632:PairCell.Row:=⟨41,49,9,2,49,some 64,59,some 59,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4632:(cell4632.cap (5:Fin 18)).grade<cell4632.lowerGrade-cell4632.off:=by decide +kernel
def cell4633:PairCell.Row:=⟨41,49,9,2,49,some 64,60,some 60,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4633:(cell4633.cap (5:Fin 18)).grade<cell4633.lowerGrade-cell4633.off:=by decide +kernel
def cell4634:PairCell.Row:=⟨41,49,9,2,49,some 64,61,some 61,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4634:(cell4634.cap (5:Fin 18)).grade<cell4634.lowerGrade-cell4634.off:=by decide +kernel
def cell4635:PairCell.Row:=⟨41,49,9,2,49,some 64,62,some 62,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4635:(cell4635.cap (5:Fin 18)).grade<cell4635.lowerGrade-cell4635.off:=by decide +kernel
def cell4636:PairCell.Row:=⟨41,49,9,2,49,some 64,63,some 63,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4636:(cell4636.cap (5:Fin 18)).grade<cell4636.lowerGrade-cell4636.off:=by decide +kernel
def cell4637:PairCell.Row:=⟨41,49,9,2,49,some 64,64,some 64,257319,[MeasuredChoices.test62],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check4637:(cell4637.cap (5:Fin 18)).grade<cell4637.lowerGrade-cell4637.off:=by decide +kernel
private def rows4638 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,21,some 24,0,none,257319,[],[]⟩,5,surfaceIntersection⟩]
private theorem paid4638 : StockPairs.checked rows4638 = true := by decide +kernel
theorem route4638 (i : Fin 2) : (rows4638.get i).Done :=
  StockPairs.doneAt paid4638 i

end Research6969.PairReceipts
end Z6969Source2985

-- Source: Research6969.PairReceipts232
section Z6969Source2986
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4640 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,17,some 20,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,13,some 16,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨41,49,9,2,9,some 12,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,41,some 48,0,none,385979,[MeasuredChoices.test1133],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,17,some 20,0,none,385979,[MeasuredChoices.test821],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,57,some 60,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,5,⟨(.node 12044597464245294),.intersection,.impossible,290657⟩⟩,
  ⟨⟨50,63,10,2,57,some 59,0,none,290657,[MeasuredChoices.test123],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,60,some 60,0,none,290657,[MeasuredChoices.test83],[]⟩,5,markedIntersection⟩,
  ⟨⟨50,63,10,2,49,some 56,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,5,⟨(.node 8026411704957730),.intersection,.impossible,285209⟩⟩,
  ⟨⟨50,63,10,2,49,some 56,0,none,285209,[MeasuredChoices.test104],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,5,surfaceIntersection⟩]
private theorem paid4640 : StockPairs.checked rows4640 = true := by decide +kernel
theorem route4640 (i : Fin 21) : (rows4640.get i).Done :=
  StockPairs.doneAt paid4640 i

end Research6969.PairReceipts
end Z6969Source2986

-- Source: Research6969.HardFit6At020
section Z6969Source2987
set_option autoImplicit true
namespace Research6969.HardFit6At020
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4560 5)
theorem case20: NormalRoute.Done (5:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route4560 4)
theorem case21: NormalRoute.Done (5:Fin 18) ⟨33,40,9,2,25,some 28⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route4560 12)
theorem case22: NormalRoute.Done (5:Fin 18) ⟨33,40,9,3,9,some 12⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route4560 11)
theorem case23: NormalRoute.Done (5:Fin 18) ⟨33,40,9,3,13,some 16⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route4560 10)
theorem case24: NormalRoute.Done (5:Fin 18) ⟨33,40,9,3,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route4560 9)
theorem case25: NormalRoute.Done (5:Fin 18) ⟨33,40,9,3,21,some 24⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route4640 2)
theorem case26: NormalRoute.Done (5:Fin 18) ⟨41,49,9,2,9,some 12⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route4640 1)
theorem case27: NormalRoute.Done (5:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route4640 0)
theorem case28: NormalRoute.Done (5:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route4638 1)
theorem case29: NormalRoute.Done (5:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf9
end Research6969.HardFit6At020
end Z6969Source2987

-- Source: Research6969.PairReceipts229
section Z6969Source2988
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4580 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,49,some 64,7,some 7,257319,[MeasuredChoices.test62],[]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,8,some 8,257319,[MeasuredChoices.test62],[]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,9,some 9,257319,[MeasuredChoices.test62],[]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,10,some 10,257319,[MeasuredChoices.test62],[]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,11,some 11,257319,[MeasuredChoices.test62],[AxisChoices.test1774]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,12,some 12,257319,[MeasuredChoices.test62],[AxisChoices.test1775]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,13,some 13,257319,[MeasuredChoices.test62],[AxisChoices.test1776]⟩,5,separateIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,14,some 14,257319,[MeasuredChoices.test62],[AxisChoices.test1777]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,15,some 15,257319,[MeasuredChoices.test62],[AxisChoices.test1778]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,16,some 16,257319,[MeasuredChoices.test62],[AxisChoices.test1779]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,17,some 17,257319,[MeasuredChoices.test62],[AxisChoices.test1780]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,18,some 18,257319,[MeasuredChoices.test62],[AxisChoices.test1781]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,19,some 19,257319,[MeasuredChoices.test62],[AxisChoices.test1782]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,20,some 20,257319,[MeasuredChoices.test62],[AxisChoices.test1783]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,21,some 21,257319,[MeasuredChoices.test62],[AxisChoices.test1784]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,22,some 22,257319,[MeasuredChoices.test62],[AxisChoices.test1785]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,23,some 23,257319,[MeasuredChoices.test62],[AxisChoices.test1786]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,24,some 24,257319,[MeasuredChoices.test62],[AxisChoices.test1787]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,25,some 25,257319,[MeasuredChoices.test62],[AxisChoices.test1788]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,26,some 26,257319,[MeasuredChoices.test62],[AxisChoices.test1788,AxisChoices.test1789]⟩,5,markedAxisIntersection⟩]
private theorem paid4580 : StockPairs.checked rows4580 = true := by decide +kernel
theorem route4580 (i : Fin 20) : (rows4580.get i).Done :=
  StockPairs.doneAt paid4580 i

end Research6969.PairReceipts
end Z6969Source2988

-- Source: Research6969.PairReceipts230
section Z6969Source2989
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4600 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,49,some 64,27,some 27,257319,[MeasuredChoices.test62],[AxisChoices.test1788,AxisChoices.test1790]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,28,some 28,257319,[MeasuredChoices.test62],[AxisChoices.test1791]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,29,some 29,257319,[MeasuredChoices.test62],[AxisChoices.test1791,AxisChoices.test1792]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,30,some 30,257319,[MeasuredChoices.test62],[AxisChoices.test1792,AxisChoices.test1793]⟩,5,markedAxisIntersection⟩,
  ⟨⟨41,49,9,2,49,some 64,31,some 31,257319,[MeasuredChoices.test62],[AxisChoices.test1793,AxisChoices.test1794]⟩,5,markedAxisIntersection⟩]
private theorem paid4600 : StockPairs.checked rows4600 = true := by decide +kernel
theorem route4600 (i : Fin 5) : (rows4600.get i).Done :=
  StockPairs.doneAt paid4600 i

def cell4605:PairCell.Row:=⟨41,49,9,2,49,some 64,32,some 32,257319,[MeasuredChoices.test62],[AxisChoices.test1795]⟩
theorem check4605:(cell4605.cap (5:Fin 18)).grade<cell4605.lowerGrade-cell4605.off:=by decide +kernel
def cell4606:PairCell.Row:=⟨41,49,9,2,49,some 64,33,some 33,257319,[MeasuredChoices.test62],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check4606:(cell4606.cap (5:Fin 18)).grade<cell4606.lowerGrade-cell4606.off:=by decide +kernel
def cell4607:PairCell.Row:=⟨41,49,9,2,49,some 64,34,some 34,257319,[MeasuredChoices.test62],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check4607:(cell4607.cap (5:Fin 18)).grade<cell4607.lowerGrade-cell4607.off:=by decide +kernel
def cell4608:PairCell.Row:=⟨41,49,9,2,49,some 64,35,some 35,257319,[MeasuredChoices.test62],[AxisChoices.test1798]⟩
theorem check4608:(cell4608.cap (5:Fin 18)).grade<cell4608.lowerGrade-cell4608.off:=by decide +kernel
def cell4609:PairCell.Row:=⟨41,49,9,2,49,some 64,36,some 36,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check4609:(cell4609.cap (5:Fin 18)).grade<cell4609.lowerGrade-cell4609.off:=by decide +kernel
def cell4610:PairCell.Row:=⟨41,49,9,2,49,some 64,37,some 37,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4610:(cell4610.cap (5:Fin 18)).grade<cell4610.lowerGrade-cell4610.off:=by decide +kernel
def cell4611:PairCell.Row:=⟨41,49,9,2,49,some 64,38,some 38,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check4611:(cell4611.cap (5:Fin 18)).grade<cell4611.lowerGrade-cell4611.off:=by decide +kernel
def cell4612:PairCell.Row:=⟨41,49,9,2,49,some 64,39,some 39,257319,[MeasuredChoices.test62],[AxisChoices.test1802]⟩
theorem check4612:(cell4612.cap (5:Fin 18)).grade<cell4612.lowerGrade-cell4612.off:=by decide +kernel
def cell4613:PairCell.Row:=⟨41,49,9,2,49,some 64,40,some 40,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check4613:(cell4613.cap (5:Fin 18)).grade<cell4613.lowerGrade-cell4613.off:=by decide +kernel
def cell4614:PairCell.Row:=⟨41,49,9,2,49,some 64,41,some 41,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4614:(cell4614.cap (5:Fin 18)).grade<cell4614.lowerGrade-cell4614.off:=by decide +kernel
def cell4615:PairCell.Row:=⟨41,49,9,2,49,some 64,42,some 42,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check4615:(cell4615.cap (5:Fin 18)).grade<cell4615.lowerGrade-cell4615.off:=by decide +kernel
def cell4616:PairCell.Row:=⟨41,49,9,2,49,some 64,43,some 43,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check4616:(cell4616.cap (5:Fin 18)).grade<cell4616.lowerGrade-cell4616.off:=by decide +kernel
def cell4617:PairCell.Row:=⟨41,49,9,2,49,some 64,44,some 44,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check4617:(cell4617.cap (5:Fin 18)).grade<cell4617.lowerGrade-cell4617.off:=by decide +kernel
def cell4618:PairCell.Row:=⟨41,49,9,2,49,some 64,45,some 45,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check4618:(cell4618.cap (5:Fin 18)).grade<cell4618.lowerGrade-cell4618.off:=by decide +kernel
def cell4619:PairCell.Row:=⟨41,49,9,2,49,some 64,46,some 46,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check4619:(cell4619.cap (5:Fin 18)).grade<cell4619.lowerGrade-cell4619.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2989

-- Source: Research6969.PairReceipts233
section Z6969Source2990
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows4660 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,33,some 40,0,none,385979,[MeasuredChoices.test1029],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,25,some 28,0,none,385979,[MeasuredChoices.test924],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,21,some 24,0,none,385979,[MeasuredChoices.test869],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,19,some 20,0,none,385979,[MeasuredChoices.test843],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,17,some 18,0,none,385979,[MeasuredChoices.test821],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,13,some 16,0,none,385979,[MeasuredChoices.test770],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨50,63,10,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,5,surfaceIntersection⟩,
  ⟨⟨64,654,12,2,52,some 52,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,5,⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨⟨64,654,12,2,51,some 51,0,some 0,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,1,some 1,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,2,some 2,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,3,some 3,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,4,some 4,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,5,some 5,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,6,some 6,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,7,some 7,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,5,separateWhole⟩,
  ⟨⟨64,654,12,2,51,some 51,8,some 8,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,5,separateWhole⟩]
private theorem paid4660 : StockPairs.checked rows4660 = true := by decide +kernel
theorem route4660 (i : Fin 19) : (rows4660.get i).Done :=
  StockPairs.doneAt paid4660 i

def cell4670:PairCell.Row:=⟨64,654,12,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩
theorem check4670:(cell4670.cap (5:Fin 18)).grade<cell4670.lowerGrade-cell4670.off:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2990

-- Source: Research6969.HardFit6At030
section Z6969Source2991
set_option autoImplicit true
namespace Research6969.HardFit6At030
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route4638 0)
theorem case30: NormalRoute.Done (5:Fin 18) ⟨41,49,9,2,25,some 28⟩:=PairRoute.start _ leaf0
private theorem allAxes130:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,49,some 64⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 64 ⟨
    (PairReceipts.route4560 13),
    (PairReceipts.route4560 14),
    (PairReceipts.route4560 15),
    (PairReceipts.route4560 16),
    (PairReceipts.route4560 17),
    (PairReceipts.route4560 18),
    (PairReceipts.route4560 19),
    (PairReceipts.route4580 0),
    (PairReceipts.route4580 1),
    (PairReceipts.route4580 2),
    (PairReceipts.route4580 3),
    (PairReceipts.route4580 4),
    (PairReceipts.route4580 5),
    (PairReceipts.route4580 6),
    (PairReceipts.route4580 7),
    (PairReceipts.route4580 8),
    (PairReceipts.route4580 9),
    (PairReceipts.route4580 10),
    (PairReceipts.route4580 11),
    (PairReceipts.route4580 12),
    (PairReceipts.route4580 13),
    (PairReceipts.route4580 14),
    (PairReceipts.route4580 15),
    (PairReceipts.route4580 16),
    (PairReceipts.route4580 17),
    (PairReceipts.route4580 18),
    (PairReceipts.route4580 19),
    (PairReceipts.route4600 0),
    (PairReceipts.route4600 1),
    (PairReceipts.route4600 2),
    (PairReceipts.route4600 3),
    (PairReceipts.route4600 4),
    PairLeaves.excluded PairReceipts.cell4605 PairReceipts.check4605 (none),
    PairLeaves.excluded PairReceipts.cell4606 PairReceipts.check4606 (none),
    PairLeaves.excluded PairReceipts.cell4607 PairReceipts.check4607 (none),
    PairLeaves.excluded PairReceipts.cell4608 PairReceipts.check4608 (none),
    PairLeaves.excluded PairReceipts.cell4609 PairReceipts.check4609 (none),
    PairLeaves.excluded PairReceipts.cell4610 PairReceipts.check4610 (none),
    PairLeaves.excluded PairReceipts.cell4611 PairReceipts.check4611 (none),
    PairLeaves.excluded PairReceipts.cell4612 PairReceipts.check4612 (none),
    PairLeaves.excluded PairReceipts.cell4613 PairReceipts.check4613 (none),
    PairLeaves.excluded PairReceipts.cell4614 PairReceipts.check4614 (none),
    PairLeaves.excluded PairReceipts.cell4615 PairReceipts.check4615 (none),
    PairLeaves.excluded PairReceipts.cell4616 PairReceipts.check4616 (none),
    PairLeaves.excluded PairReceipts.cell4617 PairReceipts.check4617 (none),
    PairLeaves.excluded PairReceipts.cell4618 PairReceipts.check4618 (none),
    PairLeaves.excluded PairReceipts.cell4619 PairReceipts.check4619 (none),
    PairLeaves.excluded PairReceipts.cell4620 PairReceipts.check4620 (none),
    PairLeaves.excluded PairReceipts.cell4621 PairReceipts.check4621 (none),
    PairLeaves.excluded PairReceipts.cell4622 PairReceipts.check4622 (none),
    PairLeaves.excluded PairReceipts.cell4623 PairReceipts.check4623 (none),
    PairLeaves.excluded PairReceipts.cell4624 PairReceipts.check4624 (none),
    PairLeaves.excluded PairReceipts.cell4625 PairReceipts.check4625 (none),
    PairLeaves.excluded PairReceipts.cell4626 PairReceipts.check4626 (none),
    PairLeaves.excluded PairReceipts.cell4627 PairReceipts.check4627 (none),
    PairLeaves.excluded PairReceipts.cell4628 PairReceipts.check4628 (none),
    PairLeaves.excluded PairReceipts.cell4629 PairReceipts.check4629 (none),
    PairLeaves.excluded PairReceipts.cell4630 PairReceipts.check4630 (none),
    PairLeaves.excluded PairReceipts.cell4631 PairReceipts.check4631 (none),
    PairLeaves.excluded PairReceipts.cell4632 PairReceipts.check4632 (none),
    PairLeaves.excluded PairReceipts.cell4633 PairReceipts.check4633 (none),
    PairLeaves.excluded PairReceipts.cell4634 PairReceipts.check4634 (none),
    PairLeaves.excluded PairReceipts.cell4635 PairReceipts.check4635 (none),
    PairLeaves.excluded PairReceipts.cell4636 PairReceipts.check4636 (none),
    PairLeaves.excluded PairReceipts.cell4637 PairReceipts.check4637 (none),
    trivial⟩)
theorem case31: NormalRoute.Done (5:Fin 18) ⟨41,49,9,2,49,some 64⟩:=PairRoute.start _ allAxes130
private def leaf131 := (PairReceipts.route4640 8)
theorem case32: NormalRoute.Done (5:Fin 18) ⟨41,49,9,3,9,some 12⟩:=PairRoute.start _ leaf131
private def leaf132 := (PairReceipts.route4640 7)
theorem case33: NormalRoute.Done (5:Fin 18) ⟨41,49,9,3,13,some 16⟩:=PairRoute.start _ leaf132
private def leaf133 := (PairReceipts.route4640 6)
theorem case34: NormalRoute.Done (5:Fin 18) ⟨41,49,9,3,17,some 20⟩:=PairRoute.start _ leaf133
private def leaf134 := (PairReceipts.route4640 5)
theorem case35: NormalRoute.Done (5:Fin 18) ⟨41,49,9,3,21,some 24⟩:=PairRoute.start _ leaf134
private def leaf135 := (PairReceipts.route4640 4)
theorem case36: NormalRoute.Done (5:Fin 18) ⟨41,49,9,3,33,some 40⟩:=PairRoute.start _ leaf135
private def leaf136 := (PairReceipts.route4640 3)
theorem case37: NormalRoute.Done (5:Fin 18) ⟨41,49,9,3,41,some 48⟩:=PairRoute.start _ leaf136
private def leaf137 := (PairReceipts.route4660 0)
theorem case38: NormalRoute.Done (5:Fin 18) ⟨50,63,10,2,9,some 12⟩:=PairRoute.start _ leaf137
private def leaf138 := (PairReceipts.route4640 20)
theorem case39: NormalRoute.Done (5:Fin 18) ⟨50,63,10,2,13,some 16⟩:=PairRoute.start _ leaf138
end Research6969.HardFit6At030
end Z6969Source2991

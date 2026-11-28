import ProximityPrize.SubmissionLower.R6970Height2313CompactRoute
import ProximityPrize.SubmissionLower.Bundle6970_14da7737160de1a0
import ProximityPrize.SubmissionLower.Bundle6970_14da7737160de1a0
import ProximityPrize.SubmissionLower.Bundle6970_14da7737160de1a0
import ProximityPrize.SubmissionLower.Bundle6970_14da7737160de1a0
import ProximityPrize.SubmissionLower.Bundle6970_748bd2481862afb9
import ProximityPrize.SubmissionLower.Bundle6970_14da7737160de1a0
import ProximityPrize.SubmissionLower.Bundle6970_14da7737160de1a0
import ProximityPrize.SubmissionLower.Bundle6970_2669b3692c4162b7
import ProximityPrize.SubmissionLower.Bundle6970_2669b3692c4162b7
import ProximityPrize.SubmissionLower.R6970Height2313Dispatch0673
import ProximityPrize.SubmissionLower.R6970Height2313Dispatch0968
import ProximityPrize.SubmissionLower.Bundle6970_238dfbafc3801848
import ProximityPrize.SubmissionLower.R6970Height2313ExplicitCore
import ProximityPrize.SubmissionLower.Bundle6970_282d89f7c7f62e8c
import ProximityPrize.SubmissionLower.Bundle6970_282d89f7c7f62e8c
import ProximityPrize.SubmissionLower.Bundle6970_282d89f7c7f62e8c
import ProximityPrize.SubmissionLower.Bundle6970_282d89f7c7f62e8c
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade

set_option Elab.async false

section Z6969Source2980
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardFit5At080
open _root_.Research6970.Height2313.Research6969
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem leaf0:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,33,some 36⟩,0,none,257319,some 298829⟩:=(PairReceipts.route4522 3)
private theorem terminalLeaf7010:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,33,some 35⟩,0,none,298829,none⟩:=PaidRows.p7010
private theorem terminalLeaf7011:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,36,some 36⟩,0,some 13,298829,none⟩:=PaidRows.p7011
private theorem terminalLeaf7012:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,36,some 36⟩,14,some 19,298829,none⟩:=PaidRows.p7012
private theorem terminalLeaf7013:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,36,some 36⟩,20,some 36,298829,none⟩:=(PairReceipts.route7013 0)
private theorem leaf1:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,33,some 36⟩,0,none,298829,none⟩:=PairRoute.splitSeed 35 terminalLeaf7010 (PairRoute.axes_of_total (PairRoute.axis 13 terminalLeaf7011 (PairRoute.axis 19 terminalLeaf7012 terminalLeaf7013)))
private theorem weight2:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,33,some 36⟩,0,none,257319,none⟩:=PairRoute.weight 298829 leaf0 leaf1
theorem case80: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,33,some 36⟩:=PairRoute.start _ weight2
private theorem leaf3:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,37,some 40⟩,0,none,257319,some 296579⟩:=(PairReceipts.route4522 2)
private theorem leaf4:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,37,some 40⟩,0,none,296579,none⟩:=PaidRows.p4531
private theorem weight5:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,37,some 40⟩,0,none,257319,none⟩:=PairRoute.weight 296579 leaf3 leaf4
theorem case81: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,37,some 40⟩:=PairRoute.start _ weight5
private theorem leaf6:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,41,some 44⟩,0,none,257319,some 294092⟩:=(PairReceipts.route4522 1)
private theorem terminalLeaf7030:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,41,some 43⟩,0,none,294092,none⟩:=PaidRows.p7030
private theorem terminalLeaf7031:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,44,some 44⟩,0,none,294092,none⟩:=PaidRows.p7031
private theorem leaf7:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,41,some 44⟩,0,none,294092,none⟩:=PairRoute.splitSeed 43 terminalLeaf7030 terminalLeaf7031
private theorem weight8:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,41,some 44⟩,0,none,257319,none⟩:=PairRoute.weight 294092 leaf6 leaf7
theorem case82: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,41,some 44⟩:=PairRoute.start _ weight8
private theorem leaf9:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,45,some 46⟩,0,none,257319,none⟩:=PaidRows.p4527
theorem case83: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,45,some 46⟩:=PairRoute.start _ leaf9
private theorem leaf10:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,47,some 47⟩,0,none,257319,none⟩:=PaidRows.p4526
theorem case84: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,47,some 47⟩:=PairRoute.start _ leaf10
private theorem leaf11:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,48,some 48⟩,0,none,257319,some 303874⟩:=PaidRows.p4524
private theorem leaf12:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,48,some 48⟩,0,none,303874,none⟩:=PaidRows.p4525
private theorem weight13:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,48,some 48⟩,0,none,257319,none⟩:=PairRoute.weight 303874 leaf11 leaf12
theorem case85: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,48,some 48⟩:=PairRoute.start _ weight13
private theorem leaf14:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,49,some 49⟩,0,none,257319,some 290650⟩:=(PairReceipts.route4522 0)
private theorem leaf15:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,49,some 49⟩,0,none,290650,none⟩:=PaidRows.p4523
private theorem weight16:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,49,some 49⟩,0,none,257319,none⟩:=PairRoute.weight 290650 leaf14 leaf15
theorem case86: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,49,some 49⟩:=PairRoute.start _ weight16
private theorem allAxes118:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,50,some 50⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 50 ⟨
    (PairReceipts.route4459 8),
    (PairReceipts.route4472 0),
    (PairReceipts.route4472 1),
    (PairReceipts.route4472 2),
    (PairReceipts.route4472 3),
    (PairReceipts.route4472 4),
    (PairReceipts.route4472 5),
    (PairReceipts.route4472 6),
    (PairReceipts.route4472 7),
    (PairReceipts.route4472 8),
    (PairReceipts.route4472 9),
    (PairReceipts.route4472 10),
    (PairReceipts.route4472 11),
    (PairReceipts.route4472 12),
    (PairReceipts.route4472 13),
    (PairReceipts.route4472 14),
    (PairReceipts.route4472 15),
    (PairReceipts.route4472 16),
    (PairReceipts.route4472 17),
    (PairReceipts.route4472 18),
    (PairReceipts.route4472 19),
    (PairReceipts.route4472 20),
    (PairReceipts.route4472 21),
    (PairReceipts.route4472 22),
    (PairReceipts.route4472 23),
    (PairReceipts.route4496 0),
    (PairReceipts.route4496 1),
    (PairReceipts.route4496 2),
    (PairReceipts.route4496 3),
    (PairReceipts.route4496 4),
    PaidRows.p4501,
    PaidRows.p4502,
    (PairReceipts.route4496 5),
    (PairReceipts.route4496 6),
    (PairReceipts.route4496 7),
    (PairReceipts.route4496 8),
    (PairReceipts.route4496 9),
    (PairReceipts.route4496 10),
    (PairReceipts.route4496 11),
    (PairReceipts.route4496 12),
    (PairReceipts.route4496 13),
    (PairReceipts.route4496 14),
    (PairReceipts.route4496 15),
    (PairReceipts.route4496 16),
    (PairReceipts.route4496 17),
    (PairReceipts.route4496 18),
    (PairReceipts.route4496 19),
    (PairReceipts.route4496 20),
    PaidRows.p4519,
    PaidRows.p4520,
    PaidRows.p4521,
    trivial⟩)
theorem case87: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,50,some 50⟩:=PairRoute.start _ allAxes118
private theorem allAxes222:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,51,some 51⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 51 ⟨
    (PairReceipts.route4417 1),
    (PairReceipts.route4522 11),
    (PairReceipts.route4522 12),
    (PairReceipts.route4522 13),
    (PairReceipts.route4522 14),
    (PairReceipts.route4522 15),
    (PairReceipts.route4522 16),
    (PairReceipts.route4522 17),
    (PairReceipts.route4522 18),
    (PairReceipts.route4522 19),
    (PairReceipts.route4522 20),
    (PairReceipts.route4522 21),
    (PairReceipts.route4522 22),
    (PairReceipts.route4522 23),
    (PairReceipts.route4433 0),
    (PairReceipts.route4433 1),
    (PairReceipts.route4433 2),
    (PairReceipts.route4433 3),
    (PairReceipts.route4433 4),
    (PairReceipts.route4433 5),
    (PairReceipts.route4433 6),
    (PairReceipts.route4433 7),
    (PairReceipts.route4433 8),
    (PairReceipts.route4433 9),
    (PairReceipts.route4433 10),
    (PairReceipts.route4433 11),
    (PairReceipts.route4433 12),
    (PairReceipts.route4433 13),
    (PairReceipts.route4433 14),
    (PairReceipts.route4433 15),
    PaidRows.p4449,
    PaidRows.p4450,
    (PairReceipts.route4433 16),
    (PairReceipts.route4433 17),
    (PairReceipts.route4433 18),
    (PairReceipts.route4433 19),
    (PairReceipts.route4433 20),
    (PairReceipts.route4433 21),
    (PairReceipts.route4433 22),
    (PairReceipts.route4433 23),
    (PairReceipts.route4459 0),
    (PairReceipts.route4459 1),
    (PairReceipts.route4459 2),
    (PairReceipts.route4459 3),
    (PairReceipts.route4459 4),
    (PairReceipts.route4459 5),
    (PairReceipts.route4459 6),
    (PairReceipts.route4459 7),
    PaidRows.p4467,
    PaidRows.p4468,
    PaidRows.p4469,
    PaidRows.p4470,
    trivial⟩)
theorem case88: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,51,some 51⟩:=PairRoute.start _ allAxes222
private theorem leaf223:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,52,some 52⟩,0,none,257319,some 288407⟩:=(PairReceipts.route4417 0)
private theorem leaf224:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,52,some 52⟩,0,none,288407,none⟩:=(PairReceipts.route4418 0)
private theorem weight225:PairRoute.Done (4:Fin 18) ⟨⟨64,654,12,2,52,some 52⟩,0,none,257319,none⟩:=PairRoute.weight 288407 leaf223 leaf224
theorem case89: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (4:Fin 18) ⟨64,654,12,2,52,some 52⟩:=PairRoute.start _ weight225
end Research6970.Height2313.Research6969.HardFit5At080
end Z6969Source2980

section Z6969Source2981
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardComplete5
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
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
theorem required:_root_.Research6970.Height2313.Research6969.HighPendingSeed5.Required:=fun j=>covered0_90 j (Nat.zero_le _) j.isLt
end Research6970.Height2313.Research6969.HardComplete5
end Z6969Source2981

section Z6969Source2982
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardFit6At000
open _root_.Research6970.Height2313.Research6969
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem leaf0:PairRoute.Done (5:Fin 18) ⟨⟨25,27,9,2,9,some 12⟩,0,none,257319,none⟩:=(PairReceipts.route4547 4)
theorem case0: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨25,27,9,2,9,some 12⟩:=PairRoute.start _ leaf0
private theorem leaf1:PairRoute.Done (5:Fin 18) ⟨⟨25,27,9,2,13,some 16⟩,0,none,257319,none⟩:=(PairReceipts.route4547 3)
theorem case1: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨25,27,9,2,13,some 16⟩:=PairRoute.start _ leaf1
private theorem leaf2:PairRoute.Done (5:Fin 18) ⟨⟨25,27,9,2,17,some 20⟩,0,none,257319,none⟩:=(PairReceipts.route4547 2)
theorem case2: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨25,27,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private theorem leaf3:PairRoute.Done (5:Fin 18) ⟨⟨25,27,9,2,21,some 24⟩,0,none,257319,none⟩:=(PairReceipts.route4547 1)
theorem case3: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨25,27,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private theorem leaf4:PairRoute.Done (5:Fin 18) ⟨⟨25,27,9,2,25,some 28⟩,0,none,257319,none⟩:=(PairReceipts.route4547 0)
theorem case4: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨25,27,9,2,25,some 28⟩:=PairRoute.start _ leaf4
private theorem leaf5:PairRoute.Done (5:Fin 18) ⟨⟨25,27,9,3,9,some 12⟩,0,none,385979,none⟩:=(PairReceipts.route4553 1)
theorem case5: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨25,27,9,3,9,some 12⟩:=PairRoute.start _ leaf5
private theorem leaf6:PairRoute.Done (5:Fin 18) ⟨⟨25,27,9,3,13,some 16⟩,0,none,385979,none⟩:=(PairReceipts.route4553 0)
theorem case6: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨25,27,9,3,13,some 16⟩:=PairRoute.start _ leaf6
private theorem leaf7:PairRoute.Done (5:Fin 18) ⟨⟨25,27,9,3,17,some 20⟩,0,none,385979,none⟩:=PaidRows.p4552
theorem case7: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨25,27,9,3,17,some 20⟩:=PairRoute.start _ leaf7
private theorem leaf8:PairRoute.Done (5:Fin 18) ⟨⟨28,32,9,2,9,some 12⟩,0,none,257319,none⟩:=(PairReceipts.route4555 4)
theorem case8: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨28,32,9,2,9,some 12⟩:=PairRoute.start _ leaf8
private theorem leaf9:PairRoute.Done (5:Fin 18) ⟨⟨28,32,9,2,13,some 16⟩,0,none,257319,none⟩:=(PairReceipts.route4555 3)
theorem case9: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨28,32,9,2,13,some 16⟩:=PairRoute.start _ leaf9
end Research6970.Height2313.Research6969.HardFit6At000
end Z6969Source2982

section Z6969Source2984
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardFit6At010
open _root_.Research6970.Height2313.Research6969
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem leaf0:PairRoute.Done (5:Fin 18) ⟨⟨28,32,9,2,17,some 20⟩,0,none,257319,none⟩:=(PairReceipts.route4555 2)
theorem case10: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf0
private theorem leaf1:PairRoute.Done (5:Fin 18) ⟨⟨28,32,9,2,21,some 24⟩,0,none,257319,none⟩:=(PairReceipts.route4555 1)
theorem case11: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf1
private theorem leaf2:PairRoute.Done (5:Fin 18) ⟨⟨28,32,9,2,25,some 28⟩,0,none,257319,none⟩:=(PairReceipts.route4555 0)
theorem case12: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨28,32,9,2,25,some 28⟩:=PairRoute.start _ leaf2
private theorem leaf3:PairRoute.Done (5:Fin 18) ⟨⟨28,32,9,3,9,some 12⟩,0,none,385979,none⟩:=(PairReceipts.route4560 2)
theorem case13: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨28,32,9,3,9,some 12⟩:=PairRoute.start _ leaf3
private theorem leaf4:PairRoute.Done (5:Fin 18) ⟨⟨28,32,9,3,13,some 16⟩,0,none,385979,none⟩:=(PairReceipts.route4560 1)
theorem case14: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨28,32,9,3,13,some 16⟩:=PairRoute.start _ leaf4
private theorem leaf5:PairRoute.Done (5:Fin 18) ⟨⟨28,32,9,3,17,some 20⟩,0,none,385979,none⟩:=PaidRows.p4561
theorem case15: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨28,32,9,3,17,some 20⟩:=PairRoute.start _ leaf5
private theorem leaf6:PairRoute.Done (5:Fin 18) ⟨⟨28,32,9,3,21,some 24⟩,0,none,385979,none⟩:=(PairReceipts.route4560 0)
theorem case16: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨28,32,9,3,21,some 24⟩:=PairRoute.start _ leaf6
private theorem leaf7:PairRoute.Done (5:Fin 18) ⟨⟨33,40,9,2,9,some 12⟩,0,none,257319,none⟩:=(PairReceipts.route4564 4)
theorem case17: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨33,40,9,2,9,some 12⟩:=PairRoute.start _ leaf7
private theorem leaf8:PairRoute.Done (5:Fin 18) ⟨⟨33,40,9,2,13,some 16⟩,0,none,257319,none⟩:=(PairReceipts.route4564 3)
theorem case18: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨33,40,9,2,13,some 16⟩:=PairRoute.start _ leaf8
private theorem leaf9:PairRoute.Done (5:Fin 18) ⟨⟨33,40,9,2,17,some 20⟩,0,none,257319,none⟩:=(PairReceipts.route4564 2)
theorem case19: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf9
end Research6970.Height2313.Research6969.HardFit6At010
end Z6969Source2984

section Z6969Source2987
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardFit6At020
open _root_.Research6970.Height2313.Research6969
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem leaf0:PairRoute.Done (5:Fin 18) ⟨⟨33,40,9,2,21,some 24⟩,0,none,257319,none⟩:=(PairReceipts.route4564 1)
theorem case20: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf0
private theorem leaf1:PairRoute.Done (5:Fin 18) ⟨⟨33,40,9,2,25,some 28⟩,0,none,257319,none⟩:=(PairReceipts.route4564 0)
theorem case21: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨33,40,9,2,25,some 28⟩:=PairRoute.start _ leaf1
private theorem leaf2:PairRoute.Done (5:Fin 18) ⟨⟨33,40,9,3,9,some 12⟩,0,none,385979,none⟩:=(PairReceipts.route4569 2)
theorem case22: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨33,40,9,3,9,some 12⟩:=PairRoute.start _ leaf2
private theorem leaf3:PairRoute.Done (5:Fin 18) ⟨⟨33,40,9,3,13,some 16⟩,0,none,385979,none⟩:=(PairReceipts.route4569 1)
theorem case23: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨33,40,9,3,13,some 16⟩:=PairRoute.start _ leaf3
private theorem leaf4:PairRoute.Done (5:Fin 18) ⟨⟨33,40,9,3,17,some 20⟩,0,none,385979,none⟩:=PaidRows.p4570
theorem case24: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨33,40,9,3,17,some 20⟩:=PairRoute.start _ leaf4
private theorem leaf5:PairRoute.Done (5:Fin 18) ⟨⟨33,40,9,3,21,some 24⟩,0,none,385979,none⟩:=(PairReceipts.route4569 0)
theorem case25: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨33,40,9,3,21,some 24⟩:=PairRoute.start _ leaf5
private theorem leaf6:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,9,some 12⟩,0,none,257319,none⟩:=(PairReceipts.route4573 21)
theorem case26: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨41,49,9,2,9,some 12⟩:=PairRoute.start _ leaf6
private theorem leaf7:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,13,some 16⟩,0,none,257319,none⟩:=(PairReceipts.route4573 20)
theorem case27: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨41,49,9,2,13,some 16⟩:=PairRoute.start _ leaf7
private theorem leaf8:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,17,some 20⟩,0,none,257319,none⟩:=(PairReceipts.route4573 19)
theorem case28: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf8
private theorem leaf9:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,21,some 24⟩,0,none,257319,none⟩:=(PairReceipts.route4573 18)
theorem case29: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf9
end Research6970.Height2313.Research6969.HardFit6At020
end Z6969Source2987

section Z6969Source2991
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HardFit6At030
open _root_.Research6970.Height2313.Research6969
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem leaf0:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,25,some 28⟩,0,none,257319,none⟩:=(PairReceipts.route4573 17)
theorem case30: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨41,49,9,2,25,some 28⟩:=PairRoute.start _ leaf0
private theorem allAxes130:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,2,49,some 64⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 64 ⟨
    (PairReceipts.route4573 0),
    (PairReceipts.route4573 1),
    (PairReceipts.route4573 2),
    (PairReceipts.route4573 3),
    (PairReceipts.route4573 4),
    (PairReceipts.route4573 5),
    (PairReceipts.route4573 6),
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
    (PairReceipts.route4580 20),
    (PairReceipts.route4580 21),
    (PairReceipts.route4580 22),
    PaidRows.p4603,
    PaidRows.p4604,
    (PairReceipts.route4580 23),
    (PairReceipts.route4606 0),
    (PairReceipts.route4606 1),
    (PairReceipts.route4606 2),
    (PairReceipts.route4606 3),
    (PairReceipts.route4606 4),
    (PairReceipts.route4606 5),
    (PairReceipts.route4606 6),
    (PairReceipts.route4606 7),
    (PairReceipts.route4606 8),
    (PairReceipts.route4606 9),
    (PairReceipts.route4606 10),
    (PairReceipts.route4606 11),
    (PairReceipts.route4606 12),
    (PairReceipts.route4606 13),
    (PairReceipts.route4573 7),
    PaidRows.p4621,
    PaidRows.p4622,
    PaidRows.p4623,
    PaidRows.p4624,
    PaidRows.p4625,
    PaidRows.p4626,
    PaidRows.p4627,
    PaidRows.p4628,
    (PairReceipts.route4573 8),
    (PairReceipts.route4573 9),
    (PairReceipts.route4573 10),
    (PairReceipts.route4573 11),
    (PairReceipts.route4573 12),
    (PairReceipts.route4573 13),
    (PairReceipts.route4573 14),
    (PairReceipts.route4573 15),
    (PairReceipts.route4573 16),
    trivial⟩)
theorem case31: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨41,49,9,2,49,some 64⟩:=PairRoute.start _ allAxes130
private theorem leaf131:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,3,9,some 12⟩,0,none,385979,none⟩:=(PairReceipts.route4643 4)
theorem case32: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨41,49,9,3,9,some 12⟩:=PairRoute.start _ leaf131
private theorem leaf132:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,3,13,some 16⟩,0,none,385979,none⟩:=(PairReceipts.route4643 3)
theorem case33: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨41,49,9,3,13,some 16⟩:=PairRoute.start _ leaf132
private theorem leaf133:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,3,17,some 20⟩,0,none,385979,none⟩:=PaidRows.p4646
theorem case34: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨41,49,9,3,17,some 20⟩:=PairRoute.start _ leaf133
private theorem leaf134:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,3,21,some 24⟩,0,none,385979,none⟩:=(PairReceipts.route4643 2)
theorem case35: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨41,49,9,3,21,some 24⟩:=PairRoute.start _ leaf134
private theorem leaf135:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,3,33,some 40⟩,0,none,385979,none⟩:=(PairReceipts.route4643 1)
theorem case36: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨41,49,9,3,33,some 40⟩:=PairRoute.start _ leaf135
private theorem leaf136:PairRoute.Done (5:Fin 18) ⟨⟨41,49,9,3,41,some 48⟩,0,none,385979,none⟩:=(PairReceipts.route4643 0)
theorem case37: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨41,49,9,3,41,some 48⟩:=PairRoute.start _ leaf136
private theorem leaf137:PairRoute.Done (5:Fin 18) ⟨⟨50,63,10,2,9,some 12⟩,0,none,257319,none⟩:=(PairReceipts.route4651 7)
theorem case38: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨50,63,10,2,9,some 12⟩:=PairRoute.start _ leaf137
private theorem leaf138:PairRoute.Done (5:Fin 18) ⟨⟨50,63,10,2,13,some 16⟩,0,none,257319,none⟩:=(PairReceipts.route4651 6)
theorem case39: _root_.Research6970.Height2313.Research6969.NormalRoute.Done (5:Fin 18) ⟨50,63,10,2,13,some 16⟩:=PairRoute.start _ leaf138
end Research6970.Height2313.Research6969.HardFit6At030
end Z6969Source2991

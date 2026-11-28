import ProximityPrize.SubmissionLower.R6970Height2313CompactSeed
import ProximityPrize.SubmissionLower.R6970Height2313CompactRoute
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_fecaa47bf637388d
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.Bundle6970_83328c4578792f21
import ProximityPrize.SubmissionLower.R6970Height2313PowerRoute
import ProximityPrize.SubmissionLower.R6970Height2313Powers
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade

section Pack_R6970Height2313Dispatch0681

set_option Elab.async false

section Z6969Source1236
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch10Band6
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0681_tail1_0 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1527 CompressedReceipts.checked1527,
    entire CompressedReceipts.cell1528 CompressedReceipts.checked1528⟩
private theorem pack_R6970Height2313Dispatch0681_tail2_0 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 40, 48, 64] ⟨
    entire CompressedReceipts.cell1529 CompressedReceipts.checked1529,
    needed ⟨15,by decide⟩,
    needed ⟨16,by decide⟩,
    needed ⟨17,by decide⟩,
    needed ⟨18,by decide⟩,
    needed ⟨19,by decide⟩,
    entire CompressedReceipts.cell1530 CompressedReceipts.checked1530,
    entire CompressedReceipts.cell1531 CompressedReceipts.checked1531,
    entire CompressedReceipts.cell1532 CompressedReceipts.checked1532,
    needed ⟨20,by decide⟩,
    entire CompressedReceipts.cell1533 CompressedReceipts.checked1533⟩
private theorem leaf3_129:Done (9:Fin 18) ⟨50,63,10,3,129,none⟩:=entire CompressedReceipts.cell1544 CompressedReceipts.checked1544
private theorem tail3_129 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 129:=leaf3_129
private theorem leaf3_65:Done (9:Fin 18) ⟨50,63,10,3,65,some 128⟩:=entire CompressedReceipts.cell1543 CompressedReceipts.checked1543
private theorem tail3_65 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 65:=join (leaf3_65) (tail3_129 needed)
private theorem pack_R6970Height2313Dispatch0681_leaf3_49:Done (9:Fin 18) ⟨50,63,10,3,49,some 64⟩:=power _ 385979 (by decide) PowerReceipts.power48 (by decide) (by decide) (by decide)
private theorem tail3_49 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 49:=join (pack_R6970Height2313Dispatch0681_leaf3_49) (tail3_65 needed)
private theorem leaf3_41:Done (9:Fin 18) ⟨50,63,10,3,41,some 48⟩:=entire CompressedReceipts.cell1542 CompressedReceipts.checked1542
private theorem tail3_41 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 41:=join (leaf3_41) (tail3_49 needed)
private theorem leaf3_33:Done (9:Fin 18) ⟨50,63,10,3,33,some 40⟩:=entire CompressedReceipts.cell1541 CompressedReceipts.checked1541
private theorem tail3_33 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 33:=join (leaf3_33) (tail3_41 needed)
private theorem leaf3_25:Done (9:Fin 18) ⟨50,63,10,3,25,some 32⟩:=
  NormalRoute.splitSeed 31 (entire CompressedReceipts.cell1540 CompressedReceipts.checked1540) (entire CompressedReceipts.cell1540b CompressedReceipts.checked1540b)
private theorem tail3_25 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 25:=join (leaf3_25) (tail3_33 needed)
private theorem leaf3_21:Done (9:Fin 18) ⟨50,63,10,3,21,some 24⟩:=entire CompressedReceipts.cell1539 CompressedReceipts.checked1539
private theorem tail3_21 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 21:=join (leaf3_21) (tail3_25 needed)
private theorem leaf3_17:Done (9:Fin 18) ⟨50,63,10,3,17,some 20⟩:=PaidRows.c1538
private theorem tail3_17 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 17:=join (leaf3_17) (tail3_21 needed)
private theorem leaf3_13:Done (9:Fin 18) ⟨50,63,10,3,13,some 16⟩:=entire CompressedReceipts.cell1537 CompressedReceipts.checked1537
private theorem tail3_13 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 13:=join (leaf3_13) (tail3_17 needed)
private theorem leaf3_9:Done (9:Fin 18) ⟨50,63,10,3,9,some 12⟩:=entire CompressedReceipts.cell1536 CompressedReceipts.checked1536
private theorem tail3_9 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 9:=join (leaf3_9) (tail3_13 needed)
private theorem leaf3_4:Done (9:Fin 18) ⟨50,63,10,3,4,some 8⟩:=entire CompressedReceipts.cell1535 CompressedReceipts.checked1535
private theorem tail3_4 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 4:=join (leaf3_4) (tail3_9 needed)
private theorem leaf3_0:Done (9:Fin 18) ⟨50,63,10,3,0,some 3⟩:=entire CompressedReceipts.cell1534 CompressedReceipts.checked1534
private theorem pack_R6970Height2313Dispatch0681_tail3_0 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 50 63 10 3 0:=join (leaf3_0) (tail3_4 needed)
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed10.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (9:Fin 18) 50 63 10 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0681_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0681_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0681_tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch10Band6
end Z6969Source1236

section Z6969Source1237
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch10Band7
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0681_tail1_0 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 64 650 12 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1545 CompressedReceipts.checked1545,
    entire CompressedReceipts.cell1546 CompressedReceipts.checked1546⟩
private theorem pack_R6970Height2313Dispatch0681_tail2_0 (needed:HighPendingSeed10.Required):Tail (9:Fin 18) 64 650 12 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 40, 48, 56] ⟨
    entire CompressedReceipts.cell1547 CompressedReceipts.checked1547,
    needed ⟨21,by decide⟩,
    needed ⟨22,by decide⟩,
    needed ⟨23,by decide⟩,
    needed ⟨24,by decide⟩,
    needed ⟨25,by decide⟩,
    needed ⟨26,by decide⟩,
    needed ⟨27,by decide⟩,
    needed ⟨28,by decide⟩,
    needed ⟨29,by decide⟩,
    entire CompressedReceipts.cell1548 CompressedReceipts.checked1548⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed10.Required) (a:ℕ) (lo:0<a) (hi:a≤2):
    Tail (9:Fin 18) 64 650 12 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0681_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0681_tail2_0 needed
end Research6970.Height2313.Research6969.HighDispatch10Band7
end Z6969Source1237

section Z6969Source1238
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatchSeed10
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute _root_.Research6970.Height2313.Research6969.HighPackets
open _root_.Research6970.Height2313.Research6969.BookView
theorem count (need:_root_.Research6970.Height2313.Research6969.HighPendingSeed10.Required) (s:State (9:Fin 18)):s.labels.card≤_root_.Research6969.CertifiedCell.target:=by
  let b:=_root_.Research6969.TransitionClassification.band s.f.natDegree
  have first:=_root_.Research6969.TransitionClassification.lower_bound s.high
  have last:=_root_.Research6969.OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤_root_.Research6969.TransitionClassification.maxGraph b): Tail (9:Fin 18) (_root_.Research6969.TransitionClassification.grade b) (_root_.Research6969.OrdinaryComplete.upper (savedMainGrade 9+savedRescueGrade 9) b) (_root_.Research6969.TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch10Band0.allDegrees need a p h
    · exact HighDispatch10Band1.allDegrees need a p h
    · exact HighDispatch10Band2.allDegrees need a p h
    · exact HighDispatch10Band3.allDegrees need a p h
    · exact HighDispatch10Band4.allDegrees need a p h
    · exact HighDispatch10Band5.allDegrees need a p h
    · exact HighDispatch10Band6.allDegrees need a p h
    · exact HighDispatch10Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s.clearContent ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6970.Height2313.Research6969.HighDispatchSeed10
end Z6969Source1238

section Z6969Source1239
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighPendingSeed11
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
def regions:Array Region:=#[⟨28,32,9,2,13,some 16⟩,⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 24⟩,⟨28,32,9,2,25,some 28⟩,⟨33,40,9,2,13,some 16⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 24⟩,⟨33,40,9,2,25,some 28⟩,⟨41,49,9,2,13,some 16⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 24⟩,⟨41,49,9,2,25,some 28⟩,⟨50,63,10,2,13,some 16⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 24⟩,⟨50,63,10,2,25,some 28⟩,⟨50,63,10,2,49,some 64⟩,⟨64,654,12,2,9,some 12⟩,⟨64,654,12,2,13,some 16⟩,⟨64,654,12,2,17,some 20⟩,⟨64,654,12,2,21,some 24⟩,⟨64,654,12,2,25,some 28⟩,⟨64,654,12,2,29,some 32⟩,⟨64,654,12,2,33,some 40⟩,⟨64,654,12,2,41,some 48⟩,⟨64,654,12,2,49,some 56⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (10:Fin 18) (atIndex j)
end Research6970.Height2313.Research6969.HighPendingSeed11
end Z6969Source1239

section Z6969Source1241
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch11Band0
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed11.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (10 : Fin 18) 22 22 9 a 0 :=
  ExtendedJointBills.counted11 _ (by decide : 22 ≤ 27)
end Research6970.Height2313.Research6969.HighDispatch11Band0
end Z6969Source1241

section Z6969Source1242
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch11Band1
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed11.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (10 : Fin 18) 23 24 9 a 0 :=
  ExtendedJointBills.counted11 _ (by decide : 24 ≤ 27)
end Research6970.Height2313.Research6969.HighDispatch11Band1
end Z6969Source1242

section Z6969Source1243
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch11Band2
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed11.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 5) :
    Tail (10 : Fin 18) 25 27 9 a 0 :=
  ExtendedJointBills.counted11 _ (by decide : 27 ≤ 27)
end Research6970.Height2313.Research6969.HighDispatch11Band2
end Z6969Source1243

section Z6969Source1246
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch11Band3
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0681_tail1_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 28 32 9 1 0:=
  NormalRoute.tailOfRun [128, 1024] ⟨
    entire CompressedReceipts.cell1614 CompressedReceipts.checked1614,
    entire CompressedReceipts.cell1615 CompressedReceipts.checked1615,
    entire CompressedReceipts.cell1616 CompressedReceipts.checked1616⟩
private theorem pack_R6970Height2313Dispatch0681_tail2_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 28 32 9 2 0:=
  NormalRoute.tailOfRun [12, 16, 20, 24, 28, 40, 128, 1024] ⟨
    PaidRows.c1617,
    needed ⟨0,by decide⟩,
    needed ⟨1,by decide⟩,
    needed ⟨2,by decide⟩,
    needed ⟨3,by decide⟩,
    entire CompressedReceipts.cell1618 CompressedReceipts.checked1618,
    entire CompressedReceipts.cell1619 CompressedReceipts.checked1619,
    PaidRows.c1620,
    entire CompressedReceipts.cell1621 CompressedReceipts.checked1621⟩
private theorem pack_R6970Height2313Dispatch0681_tail3_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 28 32 9 3 0:=
  NormalRoute.tailOfRun [3, 12, 16, 20, 28, 64, 256, 1024] ⟨
    entire CompressedReceipts.cell1622 CompressedReceipts.checked1622,
    PaidRows.c1623,
    entire CompressedReceipts.cell1624 CompressedReceipts.checked1624,
    entire CompressedReceipts.cell1625 CompressedReceipts.checked1625,
    PaidRows.c1626,
    entire CompressedReceipts.cell1627 CompressedReceipts.checked1627,
    entire CompressedReceipts.cell1628 CompressedReceipts.checked1628,
    entire CompressedReceipts.cell1629 CompressedReceipts.checked1629,
    entire CompressedReceipts.cell1630 CompressedReceipts.checked1630⟩
private theorem pack_R6970Height2313Dispatch0681_tail4_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 28 32 9 4 0:=
  NormalRoute.tailOfRun [3, 32, 128, 512, 1024] ⟨
    entire CompressedReceipts.cell1631 CompressedReceipts.checked1631,
    PaidRows.c1632,
    entire CompressedReceipts.cell1633 CompressedReceipts.checked1633,
    entire CompressedReceipts.cell1634 CompressedReceipts.checked1634,
    entire CompressedReceipts.cell1635 CompressedReceipts.checked1635,
    entire CompressedReceipts.cell1636 CompressedReceipts.checked1636⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed11.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (10:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0681_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0681_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0681_tail3_0 needed
  · exact pack_R6970Height2313Dispatch0681_tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch11Band3
end Z6969Source1246

section Z6969Source1247
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch11Band4
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0681_tail1_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 33 40 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1637 CompressedReceipts.checked1637,
    entire CompressedReceipts.cell1638 CompressedReceipts.checked1638⟩
private theorem pack_R6970Height2313Dispatch0681_tail2_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 33 40 9 2 0:=
  NormalRoute.tailOfRun [12, 16, 20, 24, 28, 40, 64, 128] ⟨
    PaidRows.c1639,
    needed ⟨4,by decide⟩,
    needed ⟨5,by decide⟩,
    needed ⟨6,by decide⟩,
    needed ⟨7,by decide⟩,
    entire CompressedReceipts.cell1640 CompressedReceipts.checked1640,
    entire CompressedReceipts.cell1641 CompressedReceipts.checked1641,
    entire CompressedReceipts.cell1642 CompressedReceipts.checked1642,
    PaidRows.c1643⟩
private theorem pack_R6970Height2313Dispatch0681_tail3_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 33 40 9 3 0:=
  NormalRoute.tailOfRun [3, 12, 16, 20, 24, 32, 64, 128, 512] ⟨
    entire CompressedReceipts.cell1644 CompressedReceipts.checked1644,
    PaidRows.c1645,
    entire CompressedReceipts.cell1646 CompressedReceipts.checked1646,
    entire CompressedReceipts.cell1647 CompressedReceipts.checked1647,
    entire CompressedReceipts.cell1648 CompressedReceipts.checked1648,
    entire CompressedReceipts.cell1649 CompressedReceipts.checked1649,
    entire CompressedReceipts.cell1650 CompressedReceipts.checked1650,
    entire CompressedReceipts.cell1651 CompressedReceipts.checked1651,
    entire CompressedReceipts.cell1652 CompressedReceipts.checked1652,
    entire CompressedReceipts.cell1653 CompressedReceipts.checked1653⟩
private theorem pack_R6970Height2313Dispatch0681_tail4_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 33 40 9 4 0:=
  NormalRoute.tailOfRun [3, 20, 48, 128, 512] ⟨
    entire CompressedReceipts.cell1654 CompressedReceipts.checked1654,
    entire CompressedReceipts.cell1655 CompressedReceipts.checked1655,
    entire CompressedReceipts.cell1656 CompressedReceipts.checked1656,
    entire CompressedReceipts.cell1657 CompressedReceipts.checked1657,
    entire CompressedReceipts.cell1658 CompressedReceipts.checked1658,
    entire CompressedReceipts.cell1659 CompressedReceipts.checked1659⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed11.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (10:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0681_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0681_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0681_tail3_0 needed
  · exact pack_R6970Height2313Dispatch0681_tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch11Band4
end Z6969Source1247
end Pack_R6970Height2313Dispatch0681

section Pack_R6970Height2313Dispatch0686

set_option Elab.async false

section Z6969Source1296
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch14Band6
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0686_tail1_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 50 63 10 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell2101 CompressedReceipts.checked2101,
    entire CompressedReceipts.cell2102 CompressedReceipts.checked2102⟩
private theorem pack_R6970Height2313Dispatch0686_tail2_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 50 63 10 2 0:=
  NormalRoute.tailOfRun [16, 20, 24, 28, 40, 48, 64] ⟨
    PaidRows.c2103,
    needed ⟨6,by decide⟩,
    needed ⟨7,by decide⟩,
    entire CompressedReceipts.cell2104 CompressedReceipts.checked2104,
    entire CompressedReceipts.cell2105 CompressedReceipts.checked2105,
    entire CompressedReceipts.cell2106 CompressedReceipts.checked2106,
    entire CompressedReceipts.cell2107 CompressedReceipts.checked2107,
    entire CompressedReceipts.cell2108 CompressedReceipts.checked2108⟩
private theorem pack_R6970Height2313Dispatch0686_leaf3_49:Done (13:Fin 18) ⟨50,63,10,3,49,some 64⟩:=power _ 385979 (by decide) PowerReceipts.power48 (by decide) (by decide) (by decide)
private theorem pack_R6970Height2313Dispatch0686_tail3_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 50 63 10 3 0:=
  NormalRoute.tailOfRun [8, 16, 24, 32, 48, 64, 128] ⟨
    PaidRows.c2109,
    entire CompressedReceipts.cell2110 CompressedReceipts.checked2110,
    PaidRows.c2111,
    entire CompressedReceipts.cell2112 CompressedReceipts.checked2112,
    entire CompressedReceipts.cell2113 CompressedReceipts.checked2113,
    pack_R6970Height2313Dispatch0686_leaf3_49,
    entire CompressedReceipts.cell2114 CompressedReceipts.checked2114,
    entire CompressedReceipts.cell2115 CompressedReceipts.checked2115⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed14.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (13:Fin 18) 50 63 10 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0686_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0686_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0686_tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch14Band6
end Z6969Source1296

section Z6969Source1297
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch14Band7
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0686_tail1_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 64 628 12 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell2116 CompressedReceipts.checked2116,
    entire CompressedReceipts.cell2117 CompressedReceipts.checked2117⟩
private theorem pack_R6970Height2313Dispatch0686_tail2_0 (needed:HighPendingSeed14.Required):Tail (13:Fin 18) 64 628 12 2 0:=
  NormalRoute.tailOfRun [12, 16, 20, 24, 28, 32, 40, 48, 64] ⟨
    entire CompressedReceipts.cell2118 CompressedReceipts.checked2118,
    needed ⟨8,by decide⟩,
    needed ⟨9,by decide⟩,
    needed ⟨10,by decide⟩,
    needed ⟨11,by decide⟩,
    needed ⟨12,by decide⟩,
    entire CompressedReceipts.cell2119 CompressedReceipts.checked2119,
    entire CompressedReceipts.cell2120 CompressedReceipts.checked2120,
    needed ⟨13,by decide⟩,
    entire CompressedReceipts.cell2121 CompressedReceipts.checked2121⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed14.Required) (a:ℕ) (lo:0<a) (hi:a≤2):
    Tail (13:Fin 18) 64 628 12 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0686_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0686_tail2_0 needed
end Research6970.Height2313.Research6969.HighDispatch14Band7
end Z6969Source1297

section Z6969Source1298
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatchSeed14
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute _root_.Research6970.Height2313.Research6969.HighPackets
open _root_.Research6970.Height2313.Research6969.BookView
theorem count (need:_root_.Research6970.Height2313.Research6969.HighPendingSeed14.Required) (s:State (13:Fin 18)):s.labels.card≤_root_.Research6969.CertifiedCell.target:=by
  let b:=_root_.Research6969.TransitionClassification.band s.f.natDegree
  have first:=_root_.Research6969.TransitionClassification.lower_bound s.high
  have last:=_root_.Research6969.OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤_root_.Research6969.TransitionClassification.maxGraph b): Tail (13:Fin 18) (_root_.Research6969.TransitionClassification.grade b) (_root_.Research6969.OrdinaryComplete.upper (savedMainGrade 13+savedRescueGrade 13) b) (_root_.Research6969.TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch14Band0.allDegrees need a p h
    · exact HighDispatch14Band1.allDegrees need a p h
    · exact HighDispatch14Band2.allDegrees need a p h
    · exact HighDispatch14Band3.allDegrees need a p h
    · exact HighDispatch14Band4.allDegrees need a p h
    · exact HighDispatch14Band5.allDegrees need a p h
    · exact HighDispatch14Band6.allDegrees need a p h
    · exact HighDispatch14Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s.clearContent ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6970.Height2313.Research6969.HighDispatchSeed14
end Z6969Source1298

section Z6969Source1299
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighPendingSeed15
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
def regions:Array Region:=#[⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 24⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 24⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 24⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 24⟩,⟨64,628,12,2,13,some 16⟩,⟨64,628,12,2,17,some 20⟩,⟨64,628,12,2,21,some 24⟩,⟨64,628,12,2,25,some 28⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (14:Fin 18) (atIndex j)
end Research6970.Height2313.Research6969.HighPendingSeed15
end Z6969Source1299

section Z6969Source1301
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch15Band0
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed15.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (14 : Fin 18) 22 22 9 a 0 :=
  ExtendedJointBills.counted15 _ (by decide : 22 ≤ 27)
end Research6970.Height2313.Research6969.HighDispatch15Band0
end Z6969Source1301

section Z6969Source1302
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch15Band1
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed15.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (14 : Fin 18) 23 24 9 a 0 :=
  ExtendedJointBills.counted15 _ (by decide : 24 ≤ 27)
end Research6970.Height2313.Research6969.HighDispatch15Band1
end Z6969Source1302

section Z6969Source1303
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch15Band2
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed15.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 5) :
    Tail (14 : Fin 18) 25 27 9 a 0 :=
  ExtendedJointBills.counted15 _ (by decide : 27 ≤ 27)
end Research6970.Height2313.Research6969.HighDispatch15Band2
end Z6969Source1303

section Z6969Source1305
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch15Band3
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0686_tail1_0 (needed:HighPendingSeed15.Required):Tail (14:Fin 18) 28 32 9 1 0:=
  NormalRoute.tailOfRun [128, 1024] ⟨
    entire CompressedReceipts.cell2181 CompressedReceipts.checked2181,
    entire CompressedReceipts.cell2182 CompressedReceipts.checked2182,
    entire CompressedReceipts.cell2183 CompressedReceipts.checked2183⟩
private theorem pack_R6970Height2313Dispatch0686_tail2_0 (needed:HighPendingSeed15.Required):Tail (14:Fin 18) 28 32 9 2 0:=
  NormalRoute.tailOfRun [16, 20, 24, 28, 48, 256] ⟨
    entire CompressedReceipts.cell2184 CompressedReceipts.checked2184,
    needed ⟨0,by decide⟩,
    needed ⟨1,by decide⟩,
    entire CompressedReceipts.cell2185 CompressedReceipts.checked2185,
    entire CompressedReceipts.cell2186 CompressedReceipts.checked2186,
    entire CompressedReceipts.cell2187 CompressedReceipts.checked2187,
    entire CompressedReceipts.cell2188 CompressedReceipts.checked2188⟩
private theorem pack_R6970Height2313Dispatch0686_tail3_0 (needed:HighPendingSeed15.Required):Tail (14:Fin 18) 28 32 9 3 0:=
  NormalRoute.tailOfRun [8, 16, 24, 64, 256, 2048] ⟨
    entire CompressedReceipts.cell2189 CompressedReceipts.checked2189,
    entire CompressedReceipts.cell2190 CompressedReceipts.checked2190,
    entire CompressedReceipts.cell2191 CompressedReceipts.checked2191,
    entire CompressedReceipts.cell2192 CompressedReceipts.checked2192,
    entire CompressedReceipts.cell2193 CompressedReceipts.checked2193,
    entire CompressedReceipts.cell2194 CompressedReceipts.checked2194,
    entire CompressedReceipts.cell2195 CompressedReceipts.checked2195⟩
private theorem pack_R6970Height2313Dispatch0686_tail4_0 (needed:HighPendingSeed15.Required):Tail (14:Fin 18) 28 32 9 4 0:=
  NormalRoute.tailOfRun [3, 64, 512, 2048] ⟨
    entire CompressedReceipts.cell2196 CompressedReceipts.checked2196,
    entire CompressedReceipts.cell2197 CompressedReceipts.checked2197,
    entire CompressedReceipts.cell2198 CompressedReceipts.checked2198,
    entire CompressedReceipts.cell2199 CompressedReceipts.checked2199,
    entire CompressedReceipts.cell2200 CompressedReceipts.checked2200⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed15.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (14:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0686_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0686_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0686_tail3_0 needed
  · exact pack_R6970Height2313Dispatch0686_tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch15Band3
end Z6969Source1305

section Z6969Source1307
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch15Band4
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0686_tail1_0 (needed:HighPendingSeed15.Required):Tail (14:Fin 18) 33 40 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell2201 CompressedReceipts.checked2201,
    entire CompressedReceipts.cell2202 CompressedReceipts.checked2202⟩
private theorem pack_R6970Height2313Dispatch0686_tail2_0 (needed:HighPendingSeed15.Required):Tail (14:Fin 18) 33 40 9 2 0:=
  NormalRoute.tailOfRun [16, 20, 24, 28, 48, 128] ⟨
    entire CompressedReceipts.cell2203 CompressedReceipts.checked2203,
    needed ⟨2,by decide⟩,
    needed ⟨3,by decide⟩,
    entire CompressedReceipts.cell2204 CompressedReceipts.checked2204,
    entire CompressedReceipts.cell2205 CompressedReceipts.checked2205,
    entire CompressedReceipts.cell2206 CompressedReceipts.checked2206,
    PaidRows.c2207⟩
private theorem pack_R6970Height2313Dispatch0686_tail3_0 (needed:HighPendingSeed15.Required):Tail (14:Fin 18) 33 40 9 3 0:=
  NormalRoute.tailOfRun [8, 16, 24, 40, 128, 512] ⟨
    entire CompressedReceipts.cell2208 CompressedReceipts.checked2208,
    entire CompressedReceipts.cell2209 CompressedReceipts.checked2209,
    entire CompressedReceipts.cell2210 CompressedReceipts.checked2210,
    entire CompressedReceipts.cell2211 CompressedReceipts.checked2211,
    entire CompressedReceipts.cell2212 CompressedReceipts.checked2212,
    entire CompressedReceipts.cell2213 CompressedReceipts.checked2213,
    entire CompressedReceipts.cell2214 CompressedReceipts.checked2214⟩
private theorem pack_R6970Height2313Dispatch0686_tail4_0 (needed:HighPendingSeed15.Required):Tail (14:Fin 18) 33 40 9 4 0:=
  NormalRoute.tailOfRun [3, 24, 64, 256] ⟨
    entire CompressedReceipts.cell2215 CompressedReceipts.checked2215,
    entire CompressedReceipts.cell2216 CompressedReceipts.checked2216,
    entire CompressedReceipts.cell2217 CompressedReceipts.checked2217,
    entire CompressedReceipts.cell2218 CompressedReceipts.checked2218,
    entire CompressedReceipts.cell2219 CompressedReceipts.checked2219⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed15.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (14:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0686_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0686_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0686_tail3_0 needed
  · exact pack_R6970Height2313Dispatch0686_tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch15Band4
end Z6969Source1307
end Pack_R6970Height2313Dispatch0686

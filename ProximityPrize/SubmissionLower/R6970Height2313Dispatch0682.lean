import ProximityPrize.SubmissionLower.R6970Height2313CompactSeed
import ProximityPrize.SubmissionLower.R6970Height2313CompactRoute
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.Bundle6970_64980975130957fe
import ProximityPrize.SubmissionLower.R6970Height2313PowerRoute
import ProximityPrize.SubmissionLower.R6970Height2313Powers
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade

set_option Elab.async false

section Z6969Source1249
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch11Band5
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 41 49 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1660 CompressedReceipts.checked1660,
    entire CompressedReceipts.cell1661 CompressedReceipts.checked1661⟩
private theorem tail2_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 41 49 9 2 0:=
  NormalRoute.tailOfRun [12, 16, 20, 24, 28, 40, 48, 64, 128] ⟨
    PaidRows.c1662,
    needed ⟨8,by decide⟩,
    needed ⟨9,by decide⟩,
    needed ⟨10,by decide⟩,
    needed ⟨11,by decide⟩,
    entire CompressedReceipts.cell1663 CompressedReceipts.checked1663,
    entire CompressedReceipts.cell1664 CompressedReceipts.checked1664,
    entire CompressedReceipts.cell1665 CompressedReceipts.checked1665,
    entire CompressedReceipts.cell1666 CompressedReceipts.checked1666,
    entire CompressedReceipts.cell1667 CompressedReceipts.checked1667⟩
private theorem tail3_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 41 49 9 3 0:=
  NormalRoute.tailOfRun [3, 12, 16, 20, 24, 32, 40, 64, 128] ⟨
    entire CompressedReceipts.cell1668 CompressedReceipts.checked1668,
    PaidRows.c1669,
    entire CompressedReceipts.cell1670 CompressedReceipts.checked1670,
    entire CompressedReceipts.cell1671 CompressedReceipts.checked1671,
    entire CompressedReceipts.cell1672 CompressedReceipts.checked1672,
    entire CompressedReceipts.cell1673 CompressedReceipts.checked1673,
    entire CompressedReceipts.cell1674 CompressedReceipts.checked1674,
    entire CompressedReceipts.cell1675 CompressedReceipts.checked1675,
    entire CompressedReceipts.cell1676 CompressedReceipts.checked1676,
    entire CompressedReceipts.cell1677 CompressedReceipts.checked1677⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed11.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (10:Fin 18) 41 49 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch11Band5
end Z6969Source1249

section Z6969Source1250
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch11Band6
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 50 63 10 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1678 CompressedReceipts.checked1678,
    entire CompressedReceipts.cell1679 CompressedReceipts.checked1679⟩
private theorem tail2_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 50 63 10 2 0:=
  NormalRoute.tailOfRun [12, 16, 20, 24, 28, 32, 48, 64] ⟨
    entire CompressedReceipts.cell1680 CompressedReceipts.checked1680,
    needed ⟨12,by decide⟩,
    needed ⟨13,by decide⟩,
    needed ⟨14,by decide⟩,
    needed ⟨15,by decide⟩,
    entire CompressedReceipts.cell1681 CompressedReceipts.checked1681,
    PaidRows.c1682,
    needed ⟨16,by decide⟩,
    entire CompressedReceipts.cell1683 CompressedReceipts.checked1683⟩
private theorem leaf3_49:Done (10:Fin 18) ⟨50,63,10,3,49,some 64⟩:=power _ 385979 (by decide) PowerReceipts.power48 (by decide) (by decide) (by decide)
private theorem tail3_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 50 63 10 3 0:=
  NormalRoute.tailOfRun [3, 12, 16, 20, 24, 32, 40, 48, 64, 128] ⟨
    entire CompressedReceipts.cell1684 CompressedReceipts.checked1684,
    PaidRows.c1685,
    entire CompressedReceipts.cell1686 CompressedReceipts.checked1686,
    entire CompressedReceipts.cell1687 CompressedReceipts.checked1687,
    entire CompressedReceipts.cell1688 CompressedReceipts.checked1688,
    PaidRows.c1689,
    entire CompressedReceipts.cell1690 CompressedReceipts.checked1690,
    entire CompressedReceipts.cell1691 CompressedReceipts.checked1691,
    leaf3_49,
    entire CompressedReceipts.cell1692 CompressedReceipts.checked1692,
    entire CompressedReceipts.cell1693 CompressedReceipts.checked1693⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed11.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (10:Fin 18) 50 63 10 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch11Band6
end Z6969Source1250

section Z6969Source1253
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch11Band7
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 64 654 12 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1694 CompressedReceipts.checked1694,
    entire CompressedReceipts.cell1695 CompressedReceipts.checked1695⟩
private theorem tail2_0 (needed:HighPendingSeed11.Required):Tail (10:Fin 18) 64 654 12 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 40, 48, 56] ⟨
    entire CompressedReceipts.cell1696 CompressedReceipts.checked1696,
    needed ⟨17,by decide⟩,
    needed ⟨18,by decide⟩,
    needed ⟨19,by decide⟩,
    needed ⟨20,by decide⟩,
    needed ⟨21,by decide⟩,
    needed ⟨22,by decide⟩,
    needed ⟨23,by decide⟩,
    needed ⟨24,by decide⟩,
    needed ⟨25,by decide⟩,
    entire CompressedReceipts.cell1697 CompressedReceipts.checked1697⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed11.Required) (a:ℕ) (lo:0<a) (hi:a≤2):
    Tail (10:Fin 18) 64 654 12 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
end Research6970.Height2313.Research6969.HighDispatch11Band7
end Z6969Source1253

section Z6969Source1254
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatchSeed11
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute _root_.Research6970.Height2313.Research6969.HighPackets
open _root_.Research6970.Height2313.Research6969.BookView
theorem count (need:_root_.Research6970.Height2313.Research6969.HighPendingSeed11.Required) (s:State (10:Fin 18)):s.labels.card≤_root_.Research6969.CertifiedCell.target:=by
  let b:=_root_.Research6969.TransitionClassification.band s.f.natDegree
  have first:=_root_.Research6969.TransitionClassification.lower_bound s.high
  have last:=_root_.Research6969.OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤_root_.Research6969.TransitionClassification.maxGraph b): Tail (10:Fin 18) (_root_.Research6969.TransitionClassification.grade b) (_root_.Research6969.OrdinaryComplete.upper (savedMainGrade 10+savedRescueGrade 10) b) (_root_.Research6969.TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch11Band0.allDegrees need a p h
    · exact HighDispatch11Band1.allDegrees need a p h
    · exact HighDispatch11Band2.allDegrees need a p h
    · exact HighDispatch11Band3.allDegrees need a p h
    · exact HighDispatch11Band4.allDegrees need a p h
    · exact HighDispatch11Band5.allDegrees need a p h
    · exact HighDispatch11Band6.allDegrees need a p h
    · exact HighDispatch11Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s.clearContent ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6970.Height2313.Research6969.HighDispatchSeed11
end Z6969Source1254

section Z6969Source1255
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighPendingSeed12
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
def regions:Array Region:=#[⟨28,32,9,2,13,some 16⟩,⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 24⟩,⟨33,40,9,2,13,some 16⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 24⟩,⟨41,49,9,2,13,some 16⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 24⟩,⟨50,63,10,2,13,some 16⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 24⟩,⟨50,63,10,2,25,some 28⟩,⟨50,63,10,2,49,some 64⟩,⟨64,654,12,2,13,some 16⟩,⟨64,654,12,2,17,some 20⟩,⟨64,654,12,2,21,some 24⟩,⟨64,654,12,2,25,some 28⟩,⟨64,654,12,2,29,some 32⟩,⟨64,654,12,2,33,some 40⟩,⟨64,654,12,2,49,some 64⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (11:Fin 18) (atIndex j)
end Research6970.Height2313.Research6969.HighPendingSeed12
end Z6969Source1255

section Z6969Source1257
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch12Band0
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed12.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (11 : Fin 18) 22 22 9 a 0 :=
  ExtendedJointBills.counted12 _ (by decide : 22 ≤ 27)
end Research6970.Height2313.Research6969.HighDispatch12Band0
end Z6969Source1257

section Z6969Source1258
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch12Band1
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed12.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (11 : Fin 18) 23 24 9 a 0 :=
  ExtendedJointBills.counted12 _ (by decide : 24 ≤ 27)
end Research6970.Height2313.Research6969.HighDispatch12Band1
end Z6969Source1258

section Z6969Source1259
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch12Band2
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed12.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 5) :
    Tail (11 : Fin 18) 25 27 9 a 0 :=
  ExtendedJointBills.counted12 _ (by decide : 27 ≤ 27)
end Research6970.Height2313.Research6969.HighDispatch12Band2
end Z6969Source1259

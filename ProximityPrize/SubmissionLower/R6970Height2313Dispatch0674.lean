import ProximityPrize.SubmissionLower.R6970Height2313CompactSeed
import ProximityPrize.SubmissionLower.R6970Height2313CompactRoute
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.R6970Height2308GradeReceipts
import ProximityPrize.SubmissionLower.R6970Height2308PowerReceipts
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.R6970Height2313Dispatch0673
import ProximityPrize.SubmissionLower.R6970Height2313PowerRoute
import ProximityPrize.SubmissionLower.R6970Height2313Powers
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade

set_option Elab.async false

section Z6969Source1152
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch5Band1
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed5.Required)
    (a : ℕ) (pos : 0 < a) (_ : a ≤ 6) :
    Tail (4:Fin 18) 23 24 9 a 0 := by
  intro s h
  obtain ⟨lo, hi, content, graph, seedFloor, seedCeil⟩ := h
  by_cases below : s.f.natDegree ≤ 23
  · exact ExtendedJointBills.counted5 ⟨23,23,9,a,0,none⟩
      (show 23 ≤ 23 by decide) s ⟨lo,below,content,graph,seedFloor,seedCeil⟩
  · have large : 24 ≤ s.f.natDegree := by omega
    have law : HighPackets.State.ControlAt s 9 := by
      change NormalGeometry.content s = 9 at content
      rw [← content]
      exact NormalGeometry.control s
    have cap := BandPowerBounds.degree24 s large law
    rw [graph] at cap
    exact BandGradeReceipts.count5 a pos cap s ⟨large,hi,content,graph,seedFloor,seedCeil⟩
end Research6970.Height2313.Research6969.HighDispatch5Band1
end Z6969Source1152

section Z6969Source1155
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch5Band2
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 25 27 9 1 0:=
  NormalRoute.tailOfRun [128, 512] ⟨
    entire CompressedReceipts.cell659 CompressedReceipts.checked659,
    entire CompressedReceipts.cell660 CompressedReceipts.checked660,
    entire CompressedReceipts.cell661 CompressedReceipts.checked661⟩
private theorem tail2_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 25 27 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 64, 256, 1024] ⟨
    PaidRows.c662,
    needed ⟨0,by decide⟩,
    needed ⟨1,by decide⟩,
    needed ⟨2,by decide⟩,
    needed ⟨3,by decide⟩,
    needed ⟨4,by decide⟩,
    entire CompressedReceipts.cell663 CompressedReceipts.checked663,
    entire CompressedReceipts.cell664 CompressedReceipts.checked664,
    entire CompressedReceipts.cell665 CompressedReceipts.checked665,
    entire CompressedReceipts.cell666 CompressedReceipts.checked666,
    entire CompressedReceipts.cell667 CompressedReceipts.checked667⟩
private theorem tail3_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 25 27 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 48, 256, 1024] ⟨
    entire CompressedReceipts.cell668 CompressedReceipts.checked668,
    entire CompressedReceipts.cell669 CompressedReceipts.checked669,
    needed ⟨5,by decide⟩,
    needed ⟨6,by decide⟩,
    needed ⟨7,by decide⟩,
    needed ⟨8,by decide⟩,
    entire CompressedReceipts.cell670 CompressedReceipts.checked670,
    entire CompressedReceipts.cell671 CompressedReceipts.checked671,
    entire CompressedReceipts.cell672 CompressedReceipts.checked672,
    entire CompressedReceipts.cell673 CompressedReceipts.checked673⟩
private theorem leaf4_1025:Done (4:Fin 18) ⟨25,27,9,4,1025,some 2048⟩:=power _ 514639 (by decide) PowerReceipts.power38 (by decide) (by decide) (by decide)
private theorem tail4_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 25 27 9 4 0:=
  NormalRoute.tailOfRun [1, 28, 128, 512, 1024, 2048] ⟨
    entire CompressedReceipts.cell674 CompressedReceipts.checked674,
    PaidRows.c675,
    entire CompressedReceipts.cell676 CompressedReceipts.checked676,
    entire CompressedReceipts.cell677 CompressedReceipts.checked677,
    entire CompressedReceipts.cell678 CompressedReceipts.checked678,
    leaf4_1025,
    entire CompressedReceipts.cell679 CompressedReceipts.checked679⟩
private theorem leaf5_2049:Done (4:Fin 18) ⟨25,27,9,5,2049,some 4096⟩:=power _ 643299 (by decide) PowerReceipts.power41 (by decide) (by decide) (by decide)
private theorem leaf5_1025:Done (4:Fin 18) ⟨25,27,9,5,1025,some 2048⟩:=power _ 643299 (by decide) PowerReceipts.power40 (by decide) (by decide) (by decide)
private theorem tail5_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 25 27 9 5 0:=
  NormalRoute.tailOfRun [1, 128, 512, 1024, 2048, 4096] ⟨
    entire CompressedReceipts.cell680 CompressedReceipts.checked680,
    entire CompressedReceipts.cell681 CompressedReceipts.checked681,
    entire CompressedReceipts.cell682 CompressedReceipts.checked682,
    entire CompressedReceipts.cell683 CompressedReceipts.checked683,
    leaf5_1025,
    leaf5_2049,
    PaidRows.c684⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed5.Required) (a:ℕ) (lo:0<a) (hi:a≤5):
    Tail (4:Fin 18) 25 27 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
  · exact tail5_0 needed
end Research6970.Height2313.Research6969.HighDispatch5Band2
end Z6969Source1155

section Z6969Source1157
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch5Band3
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 28 32 9 1 0:=
  NormalRoute.tailOfRun [128, 512] ⟨
    entire CompressedReceipts.cell685 CompressedReceipts.checked685,
    entire CompressedReceipts.cell686 CompressedReceipts.checked686,
    entire CompressedReceipts.cell687 CompressedReceipts.checked687⟩
private theorem tail2_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 28 32 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 40, 64, 128, 512] ⟨
    PaidRows.c688,
    needed ⟨9,by decide⟩,
    needed ⟨10,by decide⟩,
    needed ⟨11,by decide⟩,
    needed ⟨12,by decide⟩,
    needed ⟨13,by decide⟩,
    entire CompressedReceipts.cell689 CompressedReceipts.checked689,
    entire CompressedReceipts.cell690 CompressedReceipts.checked690,
    entire CompressedReceipts.cell691 CompressedReceipts.checked691,
    entire CompressedReceipts.cell692 CompressedReceipts.checked692,
    entire CompressedReceipts.cell693 CompressedReceipts.checked693,
    entire CompressedReceipts.cell694 CompressedReceipts.checked694⟩
private theorem leaf3_25:Done (4:Fin 18) ⟨28,32,9,3,25,some 28⟩:=by
  intro s eligible
  obtain ⟨gl,gh,ct,d,low,high⟩:=eligible
  by_cases first:K1_14_2_2_2_1.seedDegree s.native.poly≤27
  · exact PaidRows.c697 s ⟨gl,gh,ct,d,low,fun v eq=>by
      change some 27=some v at eq
      have same:27=v:=Option.some.inj eq
      simpa [←same] using first⟩
  · exact PaidRows.c10697 s ⟨gl,gh,ct,d,by
      change 28≤K1_14_2_2_2_1.seedDegree s.native.poly
      omega,high⟩
private theorem tail3_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 28 32 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 18, 20, 24, 28, 48, 128, 256, 1024] ⟨
    entire CompressedReceipts.cell695 CompressedReceipts.checked695,
    entire CompressedReceipts.cell696 CompressedReceipts.checked696,
    needed ⟨14,by decide⟩,
    needed ⟨15,by decide⟩,
    needed ⟨16,by decide⟩,
    needed ⟨17,by decide⟩,
    needed ⟨18,by decide⟩,
    leaf3_25,
    PaidRows.c698,
    entire CompressedReceipts.cell699 CompressedReceipts.checked699,
    entire CompressedReceipts.cell700 CompressedReceipts.checked700,
    entire CompressedReceipts.cell701 CompressedReceipts.checked701,
    entire CompressedReceipts.cell702 CompressedReceipts.checked702⟩
private theorem tail4_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 28 32 9 4 0:=
  NormalRoute.tailOfRun [1, 12, 32, 128, 256, 512, 1024] ⟨
    entire CompressedReceipts.cell703 CompressedReceipts.checked703,
    entire CompressedReceipts.cell704 CompressedReceipts.checked704,
    PaidRows.c705,
    PaidRows.c706,
    entire CompressedReceipts.cell707 CompressedReceipts.checked707,
    entire CompressedReceipts.cell708 CompressedReceipts.checked708,
    entire CompressedReceipts.cell709 CompressedReceipts.checked709,
    entire CompressedReceipts.cell710 CompressedReceipts.checked710⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed5.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (4:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch5Band3
end Z6969Source1157

section Z6969Source1159
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch5Band4
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 33 40 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell711 CompressedReceipts.checked711,
    entire CompressedReceipts.cell712 CompressedReceipts.checked712⟩
private theorem tail2_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 33 40 9 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 96, 256] ⟨
    entire CompressedReceipts.cell713 CompressedReceipts.checked713,
    needed ⟨19,by decide⟩,
    needed ⟨20,by decide⟩,
    needed ⟨21,by decide⟩,
    needed ⟨22,by decide⟩,
    needed ⟨23,by decide⟩,
    needed ⟨24,by decide⟩,
    entire CompressedReceipts.cell714 CompressedReceipts.checked714,
    entire CompressedReceipts.cell715 CompressedReceipts.checked715,
    entire CompressedReceipts.cell716 CompressedReceipts.checked716,
    entire CompressedReceipts.cell717 CompressedReceipts.checked717,
    entire CompressedReceipts.cell718 CompressedReceipts.checked718,
    entire CompressedReceipts.cell719 CompressedReceipts.checked719,
    entire CompressedReceipts.cell720 CompressedReceipts.checked720⟩
private theorem tail3_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 33 40 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 18, 20, 24, 28, 32, 40, 64, 128, 256] ⟨
    entire CompressedReceipts.cell721 CompressedReceipts.checked721,
    entire CompressedReceipts.cell722 CompressedReceipts.checked722,
    needed ⟨25,by decide⟩,
    needed ⟨26,by decide⟩,
    needed ⟨27,by decide⟩,
    needed ⟨28,by decide⟩,
    needed ⟨29,by decide⟩,
    needed ⟨30,by decide⟩,
    PaidRows.c723,
    needed ⟨31,by decide⟩,
    entire CompressedReceipts.cell724 CompressedReceipts.checked724,
    entire CompressedReceipts.cell725 CompressedReceipts.checked725,
    entire CompressedReceipts.cell726 CompressedReceipts.checked726,
    entire CompressedReceipts.cell727 CompressedReceipts.checked727⟩
private theorem tail4_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 33 40 9 4 0:=
  NormalRoute.tailOfRun [1, 12, 20, 24, 32, 64, 128, 256] ⟨
    entire CompressedReceipts.cell728 CompressedReceipts.checked728,
    entire CompressedReceipts.cell729 CompressedReceipts.checked729,
    entire CompressedReceipts.cell730 CompressedReceipts.checked730,
    entire CompressedReceipts.cell731 CompressedReceipts.checked731,
    PaidRows.c732,
    PaidRows.c733,
    entire CompressedReceipts.cell734 CompressedReceipts.checked734,
    entire CompressedReceipts.cell735 CompressedReceipts.checked735,
    entire CompressedReceipts.cell736 CompressedReceipts.checked736⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed5.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (4:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch5Band4
end Z6969Source1159

section Z6969Source1160
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch5Band5
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 41 49 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell737 CompressedReceipts.checked737,
    entire CompressedReceipts.cell738 CompressedReceipts.checked738⟩
private theorem tail2_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 41 49 9 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 96] ⟨
    entire CompressedReceipts.cell739 CompressedReceipts.checked739,
    needed ⟨32,by decide⟩,
    needed ⟨33,by decide⟩,
    needed ⟨34,by decide⟩,
    needed ⟨35,by decide⟩,
    needed ⟨36,by decide⟩,
    needed ⟨37,by decide⟩,
    PaidRows.c740,
    PaidRows.c741,
    PaidRows.c742,
    needed ⟨38,by decide⟩,
    entire CompressedReceipts.cell743 CompressedReceipts.checked743,
    entire CompressedReceipts.cell744 CompressedReceipts.checked744⟩
private theorem tail3_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 41 49 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 18, 20, 24, 28, 32, 40, 48, 64, 96] ⟨
    entire CompressedReceipts.cell745 CompressedReceipts.checked745,
    entire CompressedReceipts.cell746 CompressedReceipts.checked746,
    needed ⟨39,by decide⟩,
    needed ⟨40,by decide⟩,
    needed ⟨41,by decide⟩,
    needed ⟨42,by decide⟩,
    needed ⟨43,by decide⟩,
    needed ⟨44,by decide⟩,
    PaidRows.c747,
    needed ⟨45,by decide⟩,
    needed ⟨46,by decide⟩,
    needed ⟨47,by decide⟩,
    PaidRows.c748,
    entire CompressedReceipts.cell749 CompressedReceipts.checked749⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed5.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (4:Fin 18) 41 49 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch5Band5
end Z6969Source1160

section Z6969Source1161
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch5Band6
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 50 63 10 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell750 CompressedReceipts.checked750,
    entire CompressedReceipts.cell751 CompressedReceipts.checked751⟩
private theorem tail2_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 50 63 10 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 40, 48, 52, 56, 57, 58, 60, 64] ⟨
    PaidRows.c752,
    needed ⟨48,by decide⟩,
    needed ⟨49,by decide⟩,
    needed ⟨50,by decide⟩,
    needed ⟨51,by decide⟩,
    needed ⟨52,by decide⟩,
    needed ⟨53,by decide⟩,
    needed ⟨54,by decide⟩,
    needed ⟨55,by decide⟩,
    needed ⟨56,by decide⟩,
    needed ⟨57,by decide⟩,
    needed ⟨58,by decide⟩,
    needed ⟨59,by decide⟩,
    PaidRows.c753,
    PaidRows.c754,
    entire CompressedReceipts.cell755 CompressedReceipts.checked755⟩
private theorem leaf3_65:Done (4:Fin 18) ⟨50,63,10,3,65,some 96⟩:=power _ 385979 (by decide) PowerReceipts.power49 (by decide) (by decide) (by decide)
private theorem leaf3_49:Done (4:Fin 18) ⟨50,63,10,3,49,some 64⟩:=power _ 385979 (by decide) PowerReceipts.power48 (by decide) (by decide) (by decide)
private theorem tail3_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 50 63 10 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 14, 16, 18, 20, 22, 24, 28, 32, 36, 40, 48, 64, 96] ⟨
    entire CompressedReceipts.cell756 CompressedReceipts.checked756,
    PaidRows.c757,
    needed ⟨60,by decide⟩,
    needed ⟨61,by decide⟩,
    needed ⟨62,by decide⟩,
    needed ⟨63,by decide⟩,
    needed ⟨64,by decide⟩,
    needed ⟨65,by decide⟩,
    needed ⟨66,by decide⟩,
    needed ⟨67,by decide⟩,
    needed ⟨68,by decide⟩,
    needed ⟨69,by decide⟩,
    needed ⟨70,by decide⟩,
    BandPowerReceipts.cover5_41,
    leaf3_49,
    leaf3_65,
    entire CompressedReceipts.cell758 CompressedReceipts.checked758⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed5.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (4:Fin 18) 50 63 10 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch5Band6
end Z6969Source1161

section Z6969Source1162
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch5Band7
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 64 654 12 1 0:=
  NormalRoute.tailOfRun [64] ⟨
    entire CompressedReceipts.cell759 CompressedReceipts.checked759,
    entire CompressedReceipts.cell760 CompressedReceipts.checked760⟩
private theorem tail2_0 (needed:HighPendingSeed5.Required):Tail (4:Fin 18) 64 654 12 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 22, 24, 26, 28, 32, 36, 40, 44, 46, 47, 48, 49, 50, 51, 52] ⟨
    entire CompressedReceipts.cell761 CompressedReceipts.checked761,
    needed ⟨71,by decide⟩,
    needed ⟨72,by decide⟩,
    needed ⟨73,by decide⟩,
    needed ⟨74,by decide⟩,
    needed ⟨75,by decide⟩,
    needed ⟨76,by decide⟩,
    needed ⟨77,by decide⟩,
    needed ⟨78,by decide⟩,
    needed ⟨79,by decide⟩,
    needed ⟨80,by decide⟩,
    needed ⟨81,by decide⟩,
    needed ⟨82,by decide⟩,
    needed ⟨83,by decide⟩,
    needed ⟨84,by decide⟩,
    needed ⟨85,by decide⟩,
    needed ⟨86,by decide⟩,
    needed ⟨87,by decide⟩,
    needed ⟨88,by decide⟩,
    needed ⟨89,by decide⟩,
    entire CompressedReceipts.cell762 CompressedReceipts.checked762⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed5.Required) (a:ℕ) (lo:0<a) (hi:a≤2):
    Tail (4:Fin 18) 64 654 12 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
end Research6970.Height2313.Research6969.HighDispatch5Band7
end Z6969Source1162

section Z6969Source1163
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatchSeed5
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute _root_.Research6970.Height2313.Research6969.HighPackets
open _root_.Research6970.Height2313.Research6969.BookView
theorem count (need:_root_.Research6970.Height2313.Research6969.HighPendingSeed5.Required) (s:State (4:Fin 18)):s.labels.card≤_root_.Research6969.CertifiedCell.target:=by
  let b:=_root_.Research6969.TransitionClassification.band s.f.natDegree
  have first:=_root_.Research6969.TransitionClassification.lower_bound s.high
  have last:=_root_.Research6969.OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤_root_.Research6969.TransitionClassification.maxGraph b): Tail (4:Fin 18) (_root_.Research6969.TransitionClassification.grade b) (_root_.Research6969.OrdinaryComplete.upper (savedMainGrade 4+savedRescueGrade 4) b) (_root_.Research6969.TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch5Band0.allDegrees need a p h
    · exact HighDispatch5Band1.allDegrees need a p h
    · exact HighDispatch5Band2.allDegrees need a p h
    · exact HighDispatch5Band3.allDegrees need a p h
    · exact HighDispatch5Band4.allDegrees need a p h
    · exact HighDispatch5Band5.allDegrees need a p h
    · exact HighDispatch5Band6.allDegrees need a p h
    · exact HighDispatch5Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s.clearContent ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6970.Height2313.Research6969.HighDispatchSeed5
end Z6969Source1163

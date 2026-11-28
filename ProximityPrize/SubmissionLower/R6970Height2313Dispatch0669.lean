import ProximityPrize.SubmissionLower.R6970Height2313CompactSeed
import ProximityPrize.SubmissionLower.R6970Height2313CompactRoute
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.R6970Height2308PowerReceipts
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.R6970Height2313Dispatch0666
import ProximityPrize.SubmissionLower.R6970Height2313Dispatch0667
import ProximityPrize.SubmissionLower.R6970Height2313Dispatch0668
import ProximityPrize.SubmissionLower.R6970Height2313PowerRoute
import ProximityPrize.SubmissionLower.R6970Height2313Powers
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade

set_option Elab.async false

section Z6969Source1093
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch1Band3
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 28 32 9 1 0:=
  NormalRoute.tailOfRun [64, 96, 128, 256] ⟨
    entire CompressedReceipts.cell94 CompressedReceipts.checked94,
    needed ⟨64,by decide⟩,
    PaidRows.c95,
    needed ⟨65,by decide⟩,
    entire CompressedReceipts.cell96 CompressedReceipts.checked96⟩
private theorem tail2_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 28 32 9 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 96, 128, 256] ⟨
    entire CompressedReceipts.cell97 CompressedReceipts.checked97,
    needed ⟨66,by decide⟩,
    needed ⟨67,by decide⟩,
    needed ⟨68,by decide⟩,
    needed ⟨69,by decide⟩,
    needed ⟨70,by decide⟩,
    needed ⟨71,by decide⟩,
    needed ⟨72,by decide⟩,
    needed ⟨73,by decide⟩,
    needed ⟨74,by decide⟩,
    needed ⟨75,by decide⟩,
    needed ⟨76,by decide⟩,
    entire CompressedReceipts.cell98 CompressedReceipts.checked98,
    PaidRows.c99,
    entire CompressedReceipts.cell100 CompressedReceipts.checked100⟩
private theorem tail3_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 28 32 9 3 0:=
  NormalRoute.tailOfRun [1, 3, 8, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 26, 28, 32, 40, 48, 64, 128, 256, 512] ⟨
    entire CompressedReceipts.cell101 CompressedReceipts.checked101,
    entire CompressedReceipts.cell102 CompressedReceipts.checked102,
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
    needed ⟨90,by decide⟩,
    needed ⟨91,by decide⟩,
    needed ⟨92,by decide⟩,
    entire CompressedReceipts.cell103 CompressedReceipts.checked103,
    entire CompressedReceipts.cell104 CompressedReceipts.checked104,
    entire CompressedReceipts.cell105 CompressedReceipts.checked105,
    PaidRows.c106,
    entire CompressedReceipts.cell107 CompressedReceipts.checked107,
    entire CompressedReceipts.cell108 CompressedReceipts.checked108⟩
private theorem leaf4_513:Done (0:Fin 18) ⟨28,32,9,4,513,some 1024⟩:=power _ 514639 (by decide) PowerReceipts.power43 (by decide) (by decide) (by decide)
private theorem tail4_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 28 32 9 4 0:=
  NormalRoute.tailOfRun [1, 8, 12, 16, 20, 24, 32, 64, 128, 256, 512, 1024] ⟨
    entire CompressedReceipts.cell109 CompressedReceipts.checked109,
    entire CompressedReceipts.cell110 CompressedReceipts.checked110,
    entire CompressedReceipts.cell111 CompressedReceipts.checked111,
    needed ⟨93,by decide⟩,
    needed ⟨94,by decide⟩,
    needed ⟨95,by decide⟩,
    entire CompressedReceipts.cell112 CompressedReceipts.checked112,
    entire CompressedReceipts.cell113 CompressedReceipts.checked113,
    entire CompressedReceipts.cell114 CompressedReceipts.checked114,
    entire CompressedReceipts.cell115 CompressedReceipts.checked115,
    entire CompressedReceipts.cell116 CompressedReceipts.checked116,
    leaf4_513,
    entire CompressedReceipts.cell117 CompressedReceipts.checked117⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed1.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (0:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch1Band3
end Z6969Source1093

section Z6969Source1096
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch1Band4
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 33 40 9 1 0:=
  NormalRoute.tailOfRun [64, 96, 128] ⟨
    entire CompressedReceipts.cell118 CompressedReceipts.checked118,
    needed ⟨96,by decide⟩,
    PaidRows.c119,
    entire CompressedReceipts.cell120 CompressedReceipts.checked120⟩
private theorem tail2_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 33 40 9 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 96, 128] ⟨
    entire CompressedReceipts.cell121 CompressedReceipts.checked121,
    needed ⟨97,by decide⟩,
    needed ⟨98,by decide⟩,
    needed ⟨99,by decide⟩,
    needed ⟨100,by decide⟩,
    needed ⟨101,by decide⟩,
    needed ⟨102,by decide⟩,
    needed ⟨103,by decide⟩,
    needed ⟨104,by decide⟩,
    needed ⟨105,by decide⟩,
    needed ⟨106,by decide⟩,
    needed ⟨107,by decide⟩,
    entire CompressedReceipts.cell122 CompressedReceipts.checked122,
    PaidRows.c123⟩
private theorem tail3_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 33 40 9 3 0:=
  NormalRoute.tailOfRun [1, 3, 8, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 26, 28, 32, 36, 40, 48, 64, 96, 128, 256] ⟨
    entire CompressedReceipts.cell124 CompressedReceipts.checked124,
    entire CompressedReceipts.cell125 CompressedReceipts.checked125,
    needed ⟨108,by decide⟩,
    needed ⟨109,by decide⟩,
    needed ⟨110,by decide⟩,
    needed ⟨111,by decide⟩,
    needed ⟨112,by decide⟩,
    needed ⟨113,by decide⟩,
    needed ⟨114,by decide⟩,
    needed ⟨115,by decide⟩,
    needed ⟨116,by decide⟩,
    needed ⟨117,by decide⟩,
    needed ⟨118,by decide⟩,
    needed ⟨119,by decide⟩,
    needed ⟨120,by decide⟩,
    needed ⟨121,by decide⟩,
    needed ⟨122,by decide⟩,
    needed ⟨123,by decide⟩,
    needed ⟨124,by decide⟩,
    needed ⟨125,by decide⟩,
    needed ⟨126,by decide⟩,
    needed ⟨127,by decide⟩,
    entire CompressedReceipts.cell126 CompressedReceipts.checked126,
    PaidRows.c127,
    entire CompressedReceipts.cell128 CompressedReceipts.checked128⟩
private theorem leaf4_129:Done (0:Fin 18) ⟨33,40,9,4,129,some 256⟩:=power _ 514639 (by decide) PowerReceipts.power45 (by decide) (by decide) (by decide)
private theorem tail4_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 33 40 9 4 0:=
  NormalRoute.tailOfRun [1, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 96, 128, 256] ⟨
    entire CompressedReceipts.cell129 CompressedReceipts.checked129,
    entire CompressedReceipts.cell130 CompressedReceipts.checked130,
    entire CompressedReceipts.cell131 CompressedReceipts.checked131,
    needed ⟨128,by decide⟩,
    needed ⟨129,by decide⟩,
    needed ⟨130,by decide⟩,
    needed ⟨131,by decide⟩,
    needed ⟨132,by decide⟩,
    needed ⟨133,by decide⟩,
    entire CompressedReceipts.cell132 CompressedReceipts.checked132,
    entire CompressedReceipts.cell133 CompressedReceipts.checked133,
    entire CompressedReceipts.cell134 CompressedReceipts.checked134,
    entire CompressedReceipts.cell135 CompressedReceipts.checked135,
    leaf4_129,
    entire CompressedReceipts.cell136 CompressedReceipts.checked136⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed1.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (0:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch1Band4
end Z6969Source1096

section Z6969Source1097
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch1Band5
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 41 49 9 1 0:=
  NormalRoute.tailOfRun [64, 96] ⟨
    entire CompressedReceipts.cell137 CompressedReceipts.checked137,
    needed ⟨134,by decide⟩,
    entire CompressedReceipts.cell138 CompressedReceipts.checked138⟩
private theorem tail2_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 41 49 9 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 56, 64, 96] ⟨
    entire CompressedReceipts.cell139 CompressedReceipts.checked139,
    needed ⟨135,by decide⟩,
    needed ⟨136,by decide⟩,
    needed ⟨137,by decide⟩,
    needed ⟨138,by decide⟩,
    needed ⟨139,by decide⟩,
    needed ⟨140,by decide⟩,
    needed ⟨141,by decide⟩,
    needed ⟨142,by decide⟩,
    needed ⟨143,by decide⟩,
    needed ⟨144,by decide⟩,
    needed ⟨145,by decide⟩,
    needed ⟨146,by decide⟩,
    entire CompressedReceipts.cell140 CompressedReceipts.checked140⟩
private theorem tail3_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 41 49 9 3 0:=
  NormalRoute.tailOfRun [1, 3, 8, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 26, 28, 30, 32, 36, 40, 42, 44, 46, 48, 56, 64, 96] ⟨
    entire CompressedReceipts.cell141 CompressedReceipts.checked141,
    entire CompressedReceipts.cell142 CompressedReceipts.checked142,
    needed ⟨147,by decide⟩,
    needed ⟨148,by decide⟩,
    needed ⟨149,by decide⟩,
    needed ⟨150,by decide⟩,
    needed ⟨151,by decide⟩,
    needed ⟨152,by decide⟩,
    needed ⟨153,by decide⟩,
    needed ⟨154,by decide⟩,
    needed ⟨155,by decide⟩,
    needed ⟨156,by decide⟩,
    needed ⟨157,by decide⟩,
    needed ⟨158,by decide⟩,
    needed ⟨159,by decide⟩,
    needed ⟨160,by decide⟩,
    needed ⟨161,by decide⟩,
    needed ⟨162,by decide⟩,
    needed ⟨163,by decide⟩,
    needed ⟨164,by decide⟩,
    needed ⟨165,by decide⟩,
    needed ⟨166,by decide⟩,
    needed ⟨167,by decide⟩,
    needed ⟨168,by decide⟩,
    needed ⟨169,by decide⟩,
    needed ⟨170,by decide⟩,
    needed ⟨171,by decide⟩,
    entire CompressedReceipts.cell143 CompressedReceipts.checked143⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed1.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (0:Fin 18) 41 49 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch1Band5
end Z6969Source1097

section Z6969Source1098
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch1Band6
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 50 63 10 1 0:=
  NormalRoute.tailOfRun [40, 48, 64] ⟨
    PaidRows.c144,
    needed ⟨172,by decide⟩,
    needed ⟨173,by decide⟩,
    entire CompressedReceipts.cell145 CompressedReceipts.checked145⟩
private theorem tail2_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 50 63 10 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 52, 56, 57, 58, 60, 64] ⟨
    entire CompressedReceipts.cell146 CompressedReceipts.checked146,
    needed ⟨174,by decide⟩,
    needed ⟨175,by decide⟩,
    needed ⟨176,by decide⟩,
    needed ⟨177,by decide⟩,
    needed ⟨178,by decide⟩,
    needed ⟨179,by decide⟩,
    needed ⟨180,by decide⟩,
    needed ⟨181,by decide⟩,
    needed ⟨182,by decide⟩,
    needed ⟨183,by decide⟩,
    needed ⟨184,by decide⟩,
    needed ⟨185,by decide⟩,
    needed ⟨186,by decide⟩,
    needed ⟨187,by decide⟩,
    needed ⟨188,by decide⟩,
    entire CompressedReceipts.cell147 CompressedReceipts.checked147⟩
private theorem leaf3_65:Done (0:Fin 18) ⟨50,63,10,3,65,some 96⟩:=power _ 385979 (by decide) PowerReceipts.power49 (by decide) (by decide) (by decide)
private theorem leaf3_49:Done (0:Fin 18) ⟨50,63,10,3,49,some 64⟩:=power _ 385979 (by decide) PowerReceipts.power48 (by decide) (by decide) (by decide)
private theorem tail3_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 50 63 10 3 0:=
  NormalRoute.tailOfRun [1, 3, 8, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 26, 28, 30, 32, 36, 38, 40, 48, 64, 96] ⟨
    entire CompressedReceipts.cell148 CompressedReceipts.checked148,
    entire CompressedReceipts.cell149 CompressedReceipts.checked149,
    needed ⟨189,by decide⟩,
    needed ⟨190,by decide⟩,
    needed ⟨191,by decide⟩,
    needed ⟨192,by decide⟩,
    needed ⟨193,by decide⟩,
    needed ⟨194,by decide⟩,
    needed ⟨195,by decide⟩,
    needed ⟨196,by decide⟩,
    needed ⟨197,by decide⟩,
    needed ⟨198,by decide⟩,
    needed ⟨199,by decide⟩,
    needed ⟨200,by decide⟩,
    needed ⟨201,by decide⟩,
    needed ⟨202,by decide⟩,
    needed ⟨203,by decide⟩,
    needed ⟨204,by decide⟩,
    needed ⟨205,by decide⟩,
    needed ⟨206,by decide⟩,
    needed ⟨207,by decide⟩,
    BandPowerReceipts.cover1_41,
    leaf3_49,
    leaf3_65,
    entire CompressedReceipts.cell150 CompressedReceipts.checked150⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed1.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (0:Fin 18) 50 63 10 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch1Band6
end Z6969Source1098

section Z6969Source1099
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch1Band7
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 64 721 12 1 0:=
  NormalRoute.tailOfRun [0, 1, 3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64] ⟨
    needed ⟨208,by decide⟩,
    needed ⟨209,by decide⟩,
    needed ⟨210,by decide⟩,
    needed ⟨211,by decide⟩,
    needed ⟨212,by decide⟩,
    needed ⟨213,by decide⟩,
    needed ⟨214,by decide⟩,
    needed ⟨215,by decide⟩,
    needed ⟨216,by decide⟩,
    needed ⟨217,by decide⟩,
    needed ⟨218,by decide⟩,
    needed ⟨219,by decide⟩,
    needed ⟨220,by decide⟩,
    entire CompressedReceipts.cell151 CompressedReceipts.checked151⟩
private theorem tail2_0 (needed:HighPendingSeed1.Required):Tail (0:Fin 18) 64 721 12 2 0:=
  NormalRoute.tailOfRun [0, 1, 3, 8, 12, 16, 20, 24, 28, 32, 36, 40, 48, 52] ⟨
    needed ⟨221,by decide⟩,
    needed ⟨222,by decide⟩,
    needed ⟨223,by decide⟩,
    needed ⟨224,by decide⟩,
    needed ⟨225,by decide⟩,
    needed ⟨226,by decide⟩,
    needed ⟨227,by decide⟩,
    needed ⟨228,by decide⟩,
    needed ⟨229,by decide⟩,
    needed ⟨230,by decide⟩,
    needed ⟨231,by decide⟩,
    needed ⟨232,by decide⟩,
    needed ⟨233,by decide⟩,
    needed ⟨234,by decide⟩,
    entire CompressedReceipts.cell152 CompressedReceipts.checked152⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed1.Required) (a:ℕ) (lo:0<a) (hi:a≤2):
    Tail (0:Fin 18) 64 721 12 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
end Research6970.Height2313.Research6969.HighDispatch1Band7
end Z6969Source1099

section Z6969Source1100
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatchSeed1
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute _root_.Research6970.Height2313.Research6969.HighPackets
open _root_.Research6970.Height2313.Research6969.BookView
theorem count (need:_root_.Research6970.Height2313.Research6969.HighPendingSeed1.Required) (s:State (0:Fin 18)):s.labels.card≤_root_.Research6969.CertifiedCell.target:=by
  let b:=_root_.Research6969.TransitionClassification.band s.f.natDegree
  have first:=_root_.Research6969.TransitionClassification.lower_bound s.high
  have last:=_root_.Research6969.OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤_root_.Research6969.TransitionClassification.maxGraph b): Tail (0:Fin 18) (_root_.Research6969.TransitionClassification.grade b) (_root_.Research6969.OrdinaryComplete.upper (savedMainGrade 0+savedRescueGrade 0) b) (_root_.Research6969.TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch1Band0.allDegrees need a p h
    · exact HighDispatch1Band1.allDegrees need a p h
    · exact HighDispatch1Band2.allDegrees need a p h
    · exact HighDispatch1Band3.allDegrees need a p h
    · exact HighDispatch1Band4.allDegrees need a p h
    · exact HighDispatch1Band5.allDegrees need a p h
    · exact HighDispatch1Band6.allDegrees need a p h
    · exact HighDispatch1Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s.clearContent ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6970.Height2313.Research6969.HighDispatchSeed1
end Z6969Source1100

section Z6969Source1101
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighPendingSeed2
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
def regions:Array Region:=#[⟨23,24,9,2,4,some 8⟩,⟨23,24,9,2,9,some 12⟩,⟨23,24,9,2,13,some 16⟩,⟨23,24,9,2,17,some 20⟩,⟨23,24,9,2,21,some 24⟩,⟨23,24,9,2,25,some 28⟩,⟨23,24,9,2,29,some 32⟩,⟨23,24,9,3,4,some 8⟩,⟨23,24,9,3,9,some 12⟩,⟨23,24,9,3,13,some 13⟩,⟨23,24,9,3,14,some 14⟩,⟨23,24,9,3,15,some 15⟩,⟨23,24,9,3,16,some 16⟩,⟨23,24,9,3,17,some 20⟩,⟨23,24,9,3,21,some 24⟩,⟨25,27,9,2,4,some 8⟩,⟨25,27,9,2,9,some 12⟩,⟨25,27,9,2,13,some 16⟩,⟨25,27,9,2,17,some 20⟩,⟨25,27,9,2,21,some 24⟩,⟨25,27,9,2,25,some 28⟩,⟨25,27,9,2,29,some 32⟩,⟨25,27,9,2,33,some 40⟩,⟨25,27,9,3,4,some 8⟩,⟨25,27,9,3,9,some 12⟩,⟨25,27,9,3,13,some 13⟩,⟨25,27,9,3,14,some 14⟩,⟨25,27,9,3,15,some 15⟩,⟨25,27,9,3,16,some 16⟩,⟨25,27,9,3,17,some 17⟩,⟨25,27,9,3,18,some 18⟩,⟨25,27,9,3,19,some 19⟩,⟨25,27,9,3,20,some 20⟩,⟨25,27,9,3,21,some 24⟩,⟨25,27,9,3,25,some 28⟩,⟨28,32,9,2,4,some 8⟩,⟨28,32,9,2,9,some 12⟩,⟨28,32,9,2,13,some 16⟩,⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 24⟩,⟨28,32,9,2,25,some 28⟩,⟨28,32,9,2,29,some 32⟩,⟨28,32,9,2,33,some 40⟩,⟨28,32,9,3,4,some 8⟩,⟨28,32,9,3,9,some 12⟩,⟨28,32,9,3,13,some 13⟩,⟨28,32,9,3,14,some 14⟩,⟨28,32,9,3,15,some 15⟩,⟨28,32,9,3,16,some 16⟩,⟨28,32,9,3,17,some 17⟩,⟨28,32,9,3,18,some 18⟩,⟨28,32,9,3,19,some 19⟩,⟨28,32,9,3,20,some 20⟩,⟨28,32,9,3,21,some 21⟩,⟨28,32,9,3,22,some 22⟩,⟨28,32,9,3,23,some 23⟩,⟨28,32,9,3,24,some 24⟩,⟨28,32,9,3,25,some 28⟩,⟨28,32,9,3,29,some 32⟩,⟨33,40,9,2,4,some 8⟩,⟨33,40,9,2,9,some 12⟩,⟨33,40,9,2,13,some 16⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 24⟩,⟨33,40,9,2,25,some 28⟩,⟨33,40,9,2,29,some 32⟩,⟨33,40,9,2,33,some 40⟩,⟨33,40,9,2,41,some 48⟩,⟨33,40,9,2,49,some 64⟩,⟨33,40,9,2,65,some 96⟩,⟨33,40,9,3,4,some 8⟩,⟨33,40,9,3,9,some 12⟩,⟨33,40,9,3,13,some 13⟩,⟨33,40,9,3,14,some 14⟩,⟨33,40,9,3,15,some 15⟩,⟨33,40,9,3,16,some 16⟩,⟨33,40,9,3,17,some 17⟩,⟨33,40,9,3,18,some 18⟩,⟨33,40,9,3,19,some 19⟩,⟨33,40,9,3,20,some 20⟩,⟨33,40,9,3,21,some 21⟩,⟨33,40,9,3,22,some 22⟩,⟨33,40,9,3,23,some 23⟩,⟨33,40,9,3,24,some 24⟩,⟨33,40,9,3,25,some 25⟩,⟨33,40,9,3,26,some 26⟩,⟨33,40,9,3,27,some 28⟩,⟨33,40,9,3,29,some 30⟩,⟨33,40,9,3,31,some 32⟩,⟨33,40,9,3,33,some 40⟩,⟨33,40,9,3,41,some 48⟩,⟨33,40,9,3,49,some 64⟩,⟨33,40,9,4,17,some 20⟩,⟨33,40,9,4,21,some 24⟩,⟨33,40,9,4,25,some 28⟩,⟨33,40,9,4,29,some 32⟩,⟨41,49,9,2,4,some 8⟩,⟨41,49,9,2,9,some 12⟩,⟨41,49,9,2,13,some 16⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 24⟩,⟨41,49,9,2,25,some 28⟩,⟨41,49,9,2,29,some 32⟩,⟨41,49,9,2,33,some 40⟩,⟨41,49,9,2,41,some 48⟩,⟨41,49,9,2,49,some 56⟩,⟨41,49,9,2,57,some 64⟩,⟨41,49,9,2,65,some 96⟩,⟨41,49,9,3,4,some 8⟩,⟨41,49,9,3,9,some 12⟩,⟨41,49,9,3,13,some 13⟩,⟨41,49,9,3,14,some 14⟩,⟨41,49,9,3,15,some 15⟩,⟨41,49,9,3,16,some 16⟩,⟨41,49,9,3,17,some 17⟩,⟨41,49,9,3,18,some 18⟩,⟨41,49,9,3,19,some 19⟩,⟨41,49,9,3,20,some 20⟩,⟨41,49,9,3,21,some 21⟩,⟨41,49,9,3,22,some 22⟩,⟨41,49,9,3,23,some 23⟩,⟨41,49,9,3,24,some 24⟩,⟨41,49,9,3,25,some 25⟩,⟨41,49,9,3,26,some 26⟩,⟨41,49,9,3,27,some 28⟩,⟨41,49,9,3,29,some 30⟩,⟨41,49,9,3,31,some 32⟩,⟨41,49,9,3,33,some 34⟩,⟨41,49,9,3,35,some 36⟩,⟨41,49,9,3,37,some 38⟩,⟨41,49,9,3,39,some 40⟩,⟨41,49,9,3,41,some 44⟩,⟨41,49,9,3,45,some 48⟩,⟨41,49,9,3,49,some 64⟩,⟨41,49,9,3,65,some 96⟩,⟨50,63,10,2,4,some 8⟩,⟨50,63,10,2,9,some 12⟩,⟨50,63,10,2,13,some 16⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 24⟩,⟨50,63,10,2,25,some 28⟩,⟨50,63,10,2,29,some 32⟩,⟨50,63,10,2,33,some 40⟩,⟨50,63,10,2,41,some 48⟩,⟨50,63,10,2,49,some 52⟩,⟨50,63,10,2,53,some 54⟩,⟨50,63,10,2,55,some 55⟩,⟨50,63,10,2,56,some 56⟩,⟨50,63,10,2,57,some 57⟩,⟨50,63,10,2,58,some 58⟩,⟨50,63,10,2,59,some 60⟩,⟨50,63,10,2,61,some 64⟩,⟨50,63,10,3,4,some 8⟩,⟨50,63,10,3,9,some 12⟩,⟨50,63,10,3,13,some 13⟩,⟨50,63,10,3,14,some 14⟩,⟨50,63,10,3,15,some 15⟩,⟨50,63,10,3,16,some 16⟩,⟨50,63,10,3,17,some 17⟩,⟨50,63,10,3,18,some 18⟩,⟨50,63,10,3,19,some 19⟩,⟨50,63,10,3,20,some 20⟩,⟨50,63,10,3,21,some 21⟩,⟨50,63,10,3,22,some 22⟩,⟨50,63,10,3,23,some 23⟩,⟨50,63,10,3,24,some 24⟩,⟨50,63,10,3,25,some 25⟩,⟨50,63,10,3,26,some 26⟩,⟨50,63,10,3,27,some 28⟩,⟨50,63,10,3,29,some 30⟩,⟨50,63,10,3,31,some 32⟩,⟨50,63,10,3,33,some 34⟩,⟨50,63,10,3,35,some 36⟩,⟨50,63,10,3,37,some 38⟩,⟨50,63,10,3,39,some 39⟩,⟨64,722,12,1,0,some 0⟩,⟨64,722,12,1,1,some 1⟩,⟨64,722,12,1,2,some 3⟩,⟨64,722,12,1,4,some 8⟩,⟨64,722,12,1,9,some 12⟩,⟨64,722,12,1,13,some 16⟩,⟨64,722,12,1,17,some 20⟩,⟨64,722,12,1,21,some 24⟩,⟨64,722,12,1,25,some 28⟩,⟨64,722,12,1,29,some 32⟩,⟨64,722,12,1,33,some 40⟩,⟨64,722,12,1,41,some 48⟩,⟨64,722,12,1,49,some 64⟩,⟨64,722,12,2,4,some 8⟩,⟨64,722,12,2,9,some 12⟩,⟨64,722,12,2,13,some 16⟩,⟨64,722,12,2,17,some 20⟩,⟨64,722,12,2,21,some 24⟩,⟨64,722,12,2,25,some 28⟩,⟨64,722,12,2,29,some 32⟩,⟨64,722,12,2,33,some 36⟩,⟨64,722,12,2,37,some 40⟩,⟨64,722,12,2,41,some 44⟩,⟨64,722,12,2,45,some 48⟩,⟨64,722,12,2,49,some 52⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (1:Fin 18) (atIndex j)
end Research6970.Height2313.Research6969.HighPendingSeed2
end Z6969Source1101

section Z6969Source1103
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch2Band0
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed2.Required)
    (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (1:Fin 18) 22 22 9 a 0 :=
  ExtendedJointBills.counted2 _ (by decide : 22 ≤ 22)
end Research6970.Height2313.Research6969.HighDispatch2Band0
end Z6969Source1103

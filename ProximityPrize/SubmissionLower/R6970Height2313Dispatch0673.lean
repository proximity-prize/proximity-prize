import ProximityPrize.SubmissionLower.R6970Height2313CompactSeed
import ProximityPrize.SubmissionLower.R6970Height2313CompactRoute
import ProximityPrize.SubmissionLower.R6970Height2308Seed4HighGrade
import ProximityPrize.SubmissionLower.Bundle6970_fecaa47bf637388d
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.R6970Height2308PowerReceipts
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.R6970Height2313Dispatch0672
import ProximityPrize.SubmissionLower.R6970Height2313PowerRoute
import ProximityPrize.SubmissionLower.R6970Height2313Powers
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade

set_option Elab.async false

section Z6969Source1141
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch4Band3
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 28 32 9 1 0:=
  NormalRoute.tailOfRun [128, 512] ⟨
    entire CompressedReceipts.cell541 CompressedReceipts.checked541,
    entire CompressedReceipts.cell542 CompressedReceipts.checked542,
    entire CompressedReceipts.cell543 CompressedReceipts.checked543⟩
private theorem tail2_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 28 32 9 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 64, 128, 512] ⟨
    entire CompressedReceipts.cell544 CompressedReceipts.checked544,
    needed ⟨22,by decide⟩,
    needed ⟨23,by decide⟩,
    needed ⟨24,by decide⟩,
    needed ⟨25,by decide⟩,
    needed ⟨26,by decide⟩,
    needed ⟨27,by decide⟩,
    needed ⟨28,by decide⟩,
    PaidRows.c545,
    entire CompressedReceipts.cell546 CompressedReceipts.checked546,
    entire CompressedReceipts.cell547 CompressedReceipts.checked547,
    PaidRows.c548,
    entire CompressedReceipts.cell549 CompressedReceipts.checked549⟩
private theorem tail3_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 28 32 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 14, 16, 18, 20, 22, 24, 28, 40, 96, 256, 1024] ⟨
    entire CompressedReceipts.cell550 CompressedReceipts.checked550,
    PaidRows.c551,
    needed ⟨29,by decide⟩,
    needed ⟨30,by decide⟩,
    needed ⟨31,by decide⟩,
    needed ⟨32,by decide⟩,
    needed ⟨33,by decide⟩,
    needed ⟨34,by decide⟩,
    needed ⟨35,by decide⟩,
    needed ⟨36,by decide⟩,
    PaidRows.c552,
    entire CompressedReceipts.cell553 CompressedReceipts.checked553,
    entire CompressedReceipts.cell554 CompressedReceipts.checked554,
    PaidRows.c555,
    entire CompressedReceipts.cell556 CompressedReceipts.checked556⟩
private theorem tail4_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 28 32 9 4 0:=
  NormalRoute.tailOfRun [1, 12, 20, 48, 128, 256, 512, 1024] ⟨
    entire CompressedReceipts.cell557 CompressedReceipts.checked557,
    entire CompressedReceipts.cell558 CompressedReceipts.checked558,
    PaidRows.c559,
    entire CompressedReceipts.cell560 CompressedReceipts.checked560,
    entire CompressedReceipts.cell561 CompressedReceipts.checked561,
    entire CompressedReceipts.cell562 CompressedReceipts.checked562,
    entire CompressedReceipts.cell563 CompressedReceipts.checked563,
    entire CompressedReceipts.cell564 CompressedReceipts.checked564,
    entire CompressedReceipts.cell565 CompressedReceipts.checked565⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed4.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (3:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch4Band3
end Z6969Source1141

section Z6969Source1143
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch4Band4
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 33 40 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell566 CompressedReceipts.checked566,
    entire CompressedReceipts.cell567 CompressedReceipts.checked567⟩
private theorem tail2_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 33 40 9 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 96, 256] ⟨
    entire CompressedReceipts.cell568 CompressedReceipts.checked568,
    needed ⟨37,by decide⟩,
    needed ⟨38,by decide⟩,
    needed ⟨39,by decide⟩,
    needed ⟨40,by decide⟩,
    needed ⟨41,by decide⟩,
    needed ⟨42,by decide⟩,
    needed ⟨43,by decide⟩,
    PaidRows.c569,
    PaidRows.c570,
    needed ⟨44,by decide⟩,
    PaidRows.c571,
    PaidRows.c572,
    entire CompressedReceipts.cell573 CompressedReceipts.checked573⟩
private theorem tail3_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 33 40 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 14, 16, 18, 20, 22, 24, 28, 32, 40, 48, 64, 128, 256] ⟨
    entire CompressedReceipts.cell574 CompressedReceipts.checked574,
    PaidRows.c575,
    needed ⟨45,by decide⟩,
    needed ⟨46,by decide⟩,
    needed ⟨47,by decide⟩,
    needed ⟨48,by decide⟩,
    needed ⟨49,by decide⟩,
    needed ⟨50,by decide⟩,
    needed ⟨51,by decide⟩,
    needed ⟨52,by decide⟩,
    needed ⟨53,by decide⟩,
    needed ⟨54,by decide⟩,
    entire CompressedReceipts.cell576 CompressedReceipts.checked576,
    entire CompressedReceipts.cell577 CompressedReceipts.checked577,
    PaidRows.c578,
    entire CompressedReceipts.cell579 CompressedReceipts.checked579,
    entire CompressedReceipts.cell580 CompressedReceipts.checked580⟩
private theorem tail4_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 33 40 9 4 0:=
  NormalRoute.tailOfRun [1, 12, 20, 24, 28, 40, 64, 128, 256] ⟨
    entire CompressedReceipts.cell581 CompressedReceipts.checked581,
    entire CompressedReceipts.cell582 CompressedReceipts.checked582,
    PaidRows.c583,
    entire CompressedReceipts.cell584 CompressedReceipts.checked584,
    PaidRows.c585,
    PaidRows.c586,
    entire CompressedReceipts.cell587 CompressedReceipts.checked587,
    entire CompressedReceipts.cell588 CompressedReceipts.checked588,
    entire CompressedReceipts.cell589 CompressedReceipts.checked589,
    entire CompressedReceipts.cell590 CompressedReceipts.checked590⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed4.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (3:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch4Band4
end Z6969Source1143

section Z6969Source1144
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch4Band5
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 41 49 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell591 CompressedReceipts.checked591,
    entire CompressedReceipts.cell592 CompressedReceipts.checked592⟩
private theorem tail2_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 41 49 9 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 96] ⟨
    entire CompressedReceipts.cell593 CompressedReceipts.checked593,
    needed ⟨55,by decide⟩,
    needed ⟨56,by decide⟩,
    needed ⟨57,by decide⟩,
    needed ⟨58,by decide⟩,
    needed ⟨59,by decide⟩,
    needed ⟨60,by decide⟩,
    needed ⟨61,by decide⟩,
    needed ⟨62,by decide⟩,
    needed ⟨63,by decide⟩,
    needed ⟨64,by decide⟩,
    PaidRows.c594,
    entire CompressedReceipts.cell595 CompressedReceipts.checked595⟩
private theorem tail3_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 41 49 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 14, 16, 18, 20, 22, 24, 28, 32, 36, 40, 44, 48, 64, 96] ⟨
    entire CompressedReceipts.cell596 CompressedReceipts.checked596,
    PaidRows.c597,
    needed ⟨65,by decide⟩,
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
    needed ⟨77,by decide⟩,
    needed ⟨78,by decide⟩,
    needed ⟨79,by decide⟩,
    entire CompressedReceipts.cell598 CompressedReceipts.checked598⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed4.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (3:Fin 18) 41 49 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch4Band5
end Z6969Source1144

section Z6969Source1145
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch4Band6
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 50 63 10 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    PaidRows.c599,
    entire CompressedReceipts.cell600 CompressedReceipts.checked600⟩
private theorem tail2_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 50 63 10 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 22, 24, 26, 28, 32, 40, 44, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 60, 64] ⟨
    entire CompressedReceipts.cell601 CompressedReceipts.checked601,
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
    needed ⟨93,by decide⟩,
    needed ⟨94,by decide⟩,
    needed ⟨95,by decide⟩,
    needed ⟨96,by decide⟩,
    needed ⟨97,by decide⟩,
    needed ⟨98,by decide⟩,
    needed ⟨99,by decide⟩,
    needed ⟨100,by decide⟩,
    needed ⟨101,by decide⟩,
    needed ⟨102,by decide⟩,
    entire CompressedReceipts.cell602 CompressedReceipts.checked602⟩
private theorem leaf3_65:Done (3:Fin 18) ⟨50,63,10,3,65,some 96⟩:=power _ 385979 (by decide) PowerReceipts.power49 (by decide) (by decide) (by decide)
private theorem leaf3_49:Done (3:Fin 18) ⟨50,63,10,3,49,some 64⟩:=power _ 385979 (by decide) PowerReceipts.power48 (by decide) (by decide) (by decide)
private theorem tail3_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 50 63 10 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 26, 28, 30, 32, 36, 38, 40, 48, 64, 96] ⟨
    entire CompressedReceipts.cell603 CompressedReceipts.checked603,
    needed ⟨103,by decide⟩,
    needed ⟨104,by decide⟩,
    needed ⟨105,by decide⟩,
    needed ⟨106,by decide⟩,
    needed ⟨107,by decide⟩,
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
    BandPowerReceipts.cover4_41,
    leaf3_49,
    leaf3_65,
    entire CompressedReceipts.cell604 CompressedReceipts.checked604⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed4.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (3:Fin 18) 50 63 10 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch4Band6
end Z6969Source1145

section Z6969Source1147
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch4Band7
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 64 656 12 1 0:=
  NormalRoute.tailOfRun [40, 48, 64] ⟨
    SeedFourGrade656.billc605,
    needed ⟨122,by decide⟩,
    needed ⟨123,by decide⟩,
    SeedFourGrade656.billcell606⟩
private theorem tail2_0 (needed:HighPendingSeed4.Required):Tail (3:Fin 18) 64 656 12 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 22, 24, 26, 28, 32, 36, 40, 44, 46, 48, 49, 50, 51, 52] ⟨
    SeedFourGrade656.billcell607,
    needed ⟨124,by decide⟩,
    needed ⟨125,by decide⟩,
    needed ⟨126,by decide⟩,
    needed ⟨127,by decide⟩,
    needed ⟨128,by decide⟩,
    needed ⟨129,by decide⟩,
    needed ⟨130,by decide⟩,
    needed ⟨131,by decide⟩,
    needed ⟨132,by decide⟩,
    needed ⟨133,by decide⟩,
    needed ⟨134,by decide⟩,
    needed ⟨135,by decide⟩,
    needed ⟨136,by decide⟩,
    needed ⟨137,by decide⟩,
    needed ⟨138,by decide⟩,
    needed ⟨139,by decide⟩,
    needed ⟨140,by decide⟩,
    needed ⟨141,by decide⟩,
    SeedFourGrade656.billcell608⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed4.Required) (a:ℕ) (lo:0<a) (hi:a≤2):
    Tail (3:Fin 18) 64 656 12 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
end Research6970.Height2313.Research6969.HighDispatch4Band7
end Z6969Source1147

section Z6969Source1148
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatchSeed4
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute _root_.Research6970.Height2313.Research6969.HighPackets
open _root_.Research6970.Height2313.Research6969.BookView
theorem count (need:_root_.Research6970.Height2313.Research6969.HighPendingSeed4.Required) (s:State (3:Fin 18)):s.labels.card≤_root_.Research6969.CertifiedCell.target:=by
  let b:=_root_.Research6969.TransitionClassification.band s.f.natDegree
  have first:=_root_.Research6969.TransitionClassification.lower_bound s.high
  have last:=_root_.Research6969.OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤_root_.Research6969.TransitionClassification.maxGraph b): Tail (3:Fin 18) (_root_.Research6969.TransitionClassification.grade b) (_root_.Research6969.OrdinaryComplete.upper (savedMainGrade 3+savedRescueGrade 3) b) (_root_.Research6969.TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch4Band0.allDegrees need a p h
    · exact HighDispatch4Band1.allDegrees need a p h
    · exact HighDispatch4Band2.allDegrees need a p h
    · exact HighDispatch4Band3.allDegrees need a p h
    · exact HighDispatch4Band4.allDegrees need a p h
    · exact HighDispatch4Band5.allDegrees need a p h
    · exact HighDispatch4Band6.allDegrees need a p h
    · exact HighDispatch4Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s.clearContent ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6970.Height2313.Research6969.HighDispatchSeed4
end Z6969Source1148

section Z6969Source1149
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighPendingSeed5
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
def regions:Array Region:=#[⟨25,27,9,2,9,some 12⟩,⟨25,27,9,2,13,some 16⟩,⟨25,27,9,2,17,some 20⟩,⟨25,27,9,2,21,some 24⟩,⟨25,27,9,2,25,some 28⟩,⟨25,27,9,3,9,some 12⟩,⟨25,27,9,3,13,some 16⟩,⟨25,27,9,3,17,some 20⟩,⟨25,27,9,3,21,some 24⟩,⟨28,32,9,2,9,some 12⟩,⟨28,32,9,2,13,some 16⟩,⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 24⟩,⟨28,32,9,2,25,some 28⟩,⟨28,32,9,3,9,some 12⟩,⟨28,32,9,3,13,some 16⟩,⟨28,32,9,3,17,some 18⟩,⟨28,32,9,3,19,some 20⟩,⟨28,32,9,3,21,some 24⟩,⟨33,40,9,2,4,some 8⟩,⟨33,40,9,2,9,some 12⟩,⟨33,40,9,2,13,some 16⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 24⟩,⟨33,40,9,2,25,some 28⟩,⟨33,40,9,3,9,some 12⟩,⟨33,40,9,3,13,some 16⟩,⟨33,40,9,3,17,some 18⟩,⟨33,40,9,3,19,some 20⟩,⟨33,40,9,3,21,some 24⟩,⟨33,40,9,3,25,some 28⟩,⟨33,40,9,3,33,some 40⟩,⟨41,49,9,2,4,some 8⟩,⟨41,49,9,2,9,some 12⟩,⟨41,49,9,2,13,some 16⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 24⟩,⟨41,49,9,2,25,some 28⟩,⟨41,49,9,2,49,some 64⟩,⟨41,49,9,3,9,some 12⟩,⟨41,49,9,3,13,some 16⟩,⟨41,49,9,3,17,some 18⟩,⟨41,49,9,3,19,some 20⟩,⟨41,49,9,3,21,some 24⟩,⟨41,49,9,3,25,some 28⟩,⟨41,49,9,3,33,some 40⟩,⟨41,49,9,3,41,some 48⟩,⟨41,49,9,3,49,some 64⟩,⟨50,63,10,2,9,some 12⟩,⟨50,63,10,2,13,some 16⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 24⟩,⟨50,63,10,2,25,some 28⟩,⟨50,63,10,2,29,some 32⟩,⟨50,63,10,2,33,some 40⟩,⟨50,63,10,2,41,some 48⟩,⟨50,63,10,2,49,some 52⟩,⟨50,63,10,2,53,some 56⟩,⟨50,63,10,2,57,some 57⟩,⟨50,63,10,2,58,some 58⟩,⟨50,63,10,3,9,some 12⟩,⟨50,63,10,3,13,some 14⟩,⟨50,63,10,3,15,some 16⟩,⟨50,63,10,3,17,some 18⟩,⟨50,63,10,3,19,some 20⟩,⟨50,63,10,3,21,some 22⟩,⟨50,63,10,3,23,some 24⟩,⟨50,63,10,3,25,some 28⟩,⟨50,63,10,3,29,some 32⟩,⟨50,63,10,3,33,some 36⟩,⟨50,63,10,3,37,some 40⟩,⟨64,654,12,2,4,some 8⟩,⟨64,654,12,2,9,some 12⟩,⟨64,654,12,2,13,some 16⟩,⟨64,654,12,2,17,some 20⟩,⟨64,654,12,2,21,some 22⟩,⟨64,654,12,2,23,some 24⟩,⟨64,654,12,2,25,some 26⟩,⟨64,654,12,2,27,some 28⟩,⟨64,654,12,2,29,some 32⟩,⟨64,654,12,2,33,some 36⟩,⟨64,654,12,2,37,some 40⟩,⟨64,654,12,2,41,some 44⟩,⟨64,654,12,2,45,some 46⟩,⟨64,654,12,2,47,some 47⟩,⟨64,654,12,2,48,some 48⟩,⟨64,654,12,2,49,some 49⟩,⟨64,654,12,2,50,some 50⟩,⟨64,654,12,2,51,some 51⟩,⟨64,654,12,2,52,some 52⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (4:Fin 18) (atIndex j)
end Research6970.Height2313.Research6969.HighPendingSeed5
end Z6969Source1149

section Z6969Source1151
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch5Band0
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed5.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (4 : Fin 18) 22 22 9 a 0 :=
  ExtendedJointBills.counted5 _ (by decide : 22 ≤ 23)
end Research6970.Height2313.Research6969.HighDispatch5Band0
end Z6969Source1151

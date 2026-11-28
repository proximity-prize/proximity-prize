import ProximityPrize.SubmissionLower.R6970Height2313CompactSeed
import ProximityPrize.SubmissionLower.R6970Height2313CompactRoute
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_fecaa47bf637388d
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.R6970Height2308PowerReceipts
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.Bundle6970_01d5856c44b7c788
import ProximityPrize.SubmissionLower.R6970Height2313PowerRoute
import ProximityPrize.SubmissionLower.R6970Height2313Powers
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade

set_option Elab.async false

section Z6969Source1176
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch6Band6
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 50 63 10 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell906 CompressedReceipts.checked906,
    entire CompressedReceipts.cell907 CompressedReceipts.checked907⟩
private theorem tail2_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 50 63 10 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 40, 48, 56, 60, 64] ⟨
    entire CompressedReceipts.cell908 CompressedReceipts.checked908,
    needed ⟨38,by decide⟩,
    needed ⟨39,by decide⟩,
    needed ⟨40,by decide⟩,
    needed ⟨41,by decide⟩,
    needed ⟨42,by decide⟩,
    needed ⟨43,by decide⟩,
    needed ⟨44,by decide⟩,
    needed ⟨45,by decide⟩,
    needed ⟨46,by decide⟩,
    needed ⟨47,by decide⟩,
    entire CompressedReceipts.cell909 CompressedReceipts.checked909,
    entire CompressedReceipts.cell910 CompressedReceipts.checked910⟩
private theorem leaf3_49:Done (5:Fin 18) ⟨50,63,10,3,49,some 64⟩:=power _ 385979 (by decide) PowerReceipts.power48 (by decide) (by decide) (by decide)
private theorem tail3_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 50 63 10 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 18, 20, 24, 28, 32, 40, 48, 64, 96] ⟨
    entire CompressedReceipts.cell911 CompressedReceipts.checked911,
    entire CompressedReceipts.cell912 CompressedReceipts.checked912,
    needed ⟨48,by decide⟩,
    needed ⟨49,by decide⟩,
    needed ⟨50,by decide⟩,
    needed ⟨51,by decide⟩,
    needed ⟨52,by decide⟩,
    needed ⟨53,by decide⟩,
    needed ⟨54,by decide⟩,
    needed ⟨55,by decide⟩,
    BandPowerReceipts.cover6_41,
    leaf3_49,
    PaidRows.c913,
    entire CompressedReceipts.cell914 CompressedReceipts.checked914⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed6.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (5:Fin 18) 50 63 10 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch6Band6
end Z6969Source1176

section Z6969Source1177
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch6Band7
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 64 654 12 1 0:=
  NormalRoute.tailOfRun [96] ⟨
    PaidRows.c915,
    entire CompressedReceipts.cell916 CompressedReceipts.checked916⟩
private theorem tail2_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 64 654 12 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 22, 23, 24, 26, 28, 30, 32, 36, 38, 40, 42, 44, 46, 47, 48, 49, 50, 51, 52] ⟨
    entire CompressedReceipts.cell917 CompressedReceipts.checked917,
    needed ⟨56,by decide⟩,
    needed ⟨57,by decide⟩,
    needed ⟨58,by decide⟩,
    needed ⟨59,by decide⟩,
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
    needed ⟨71,by decide⟩,
    needed ⟨72,by decide⟩,
    needed ⟨73,by decide⟩,
    needed ⟨74,by decide⟩,
    needed ⟨75,by decide⟩,
    needed ⟨76,by decide⟩,
    needed ⟨77,by decide⟩,
    entire CompressedReceipts.cell918 CompressedReceipts.checked918⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed6.Required) (a:ℕ) (lo:0<a) (hi:a≤2):
    Tail (5:Fin 18) 64 654 12 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
end Research6970.Height2313.Research6969.HighDispatch6Band7
end Z6969Source1177

section Z6969Source1178
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatchSeed6
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute _root_.Research6970.Height2313.Research6969.HighPackets
open _root_.Research6970.Height2313.Research6969.BookView
theorem count (need:_root_.Research6970.Height2313.Research6969.HighPendingSeed6.Required) (s:State (5:Fin 18)):s.labels.card≤_root_.Research6969.CertifiedCell.target:=by
  let b:=_root_.Research6969.TransitionClassification.band s.f.natDegree
  have first:=_root_.Research6969.TransitionClassification.lower_bound s.high
  have last:=_root_.Research6969.OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤_root_.Research6969.TransitionClassification.maxGraph b): Tail (5:Fin 18) (_root_.Research6969.TransitionClassification.grade b) (_root_.Research6969.OrdinaryComplete.upper (savedMainGrade 5+savedRescueGrade 5) b) (_root_.Research6969.TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch6Band0.allDegrees need a p h
    · exact HighDispatch6Band1.allDegrees need a p h
    · exact HighDispatch6Band2.allDegrees need a p h
    · exact HighDispatch6Band3.allDegrees need a p h
    · exact HighDispatch6Band4.allDegrees need a p h
    · exact HighDispatch6Band5.allDegrees need a p h
    · exact HighDispatch6Band6.allDegrees need a p h
    · exact HighDispatch6Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s.clearContent ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6970.Height2313.Research6969.HighDispatchSeed6
end Z6969Source1178

section Z6969Source1179
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighPendingSeed7
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
def regions:Array Region:=#[⟨25,27,9,2,9,some 12⟩,⟨25,27,9,2,13,some 16⟩,⟨25,27,9,2,17,some 20⟩,⟨25,27,9,2,21,some 24⟩,⟨25,27,9,2,25,some 28⟩,⟨25,27,9,3,13,some 16⟩,⟨25,27,9,3,17,some 20⟩,⟨28,32,9,2,9,some 12⟩,⟨28,32,9,2,13,some 16⟩,⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 24⟩,⟨28,32,9,2,25,some 28⟩,⟨28,32,9,3,9,some 12⟩,⟨28,32,9,3,13,some 16⟩,⟨28,32,9,3,17,some 20⟩,⟨28,32,9,3,21,some 24⟩,⟨33,40,9,2,9,some 12⟩,⟨33,40,9,2,13,some 16⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 24⟩,⟨33,40,9,2,25,some 28⟩,⟨33,40,9,3,9,some 12⟩,⟨33,40,9,3,13,some 16⟩,⟨33,40,9,3,17,some 20⟩,⟨33,40,9,3,21,some 24⟩,⟨41,49,9,2,9,some 12⟩,⟨41,49,9,2,13,some 16⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 24⟩,⟨41,49,9,2,25,some 28⟩,⟨41,49,9,2,49,some 64⟩,⟨41,49,9,3,9,some 12⟩,⟨41,49,9,3,13,some 16⟩,⟨41,49,9,3,17,some 20⟩,⟨41,49,9,3,21,some 24⟩,⟨41,49,9,3,33,some 40⟩,⟨41,49,9,3,41,some 48⟩,⟨50,63,10,2,9,some 12⟩,⟨50,63,10,2,13,some 16⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 24⟩,⟨50,63,10,2,25,some 28⟩,⟨50,63,10,2,41,some 48⟩,⟨50,63,10,2,49,some 56⟩,⟨50,63,10,2,57,some 60⟩,⟨50,63,10,3,9,some 12⟩,⟨50,63,10,3,13,some 16⟩,⟨50,63,10,3,17,some 20⟩,⟨50,63,10,3,21,some 24⟩,⟨50,63,10,3,25,some 28⟩,⟨50,63,10,3,29,some 32⟩,⟨50,63,10,3,33,some 40⟩,⟨64,706,12,2,9,some 12⟩,⟨64,706,12,2,13,some 16⟩,⟨64,706,12,2,17,some 20⟩,⟨64,706,12,2,21,some 22⟩,⟨64,706,12,2,23,some 24⟩,⟨64,706,12,2,25,some 26⟩,⟨64,706,12,2,27,some 28⟩,⟨64,706,12,2,29,some 32⟩,⟨64,706,12,2,33,some 36⟩,⟨64,706,12,2,37,some 40⟩,⟨64,706,12,2,41,some 44⟩,⟨64,706,12,2,45,some 46⟩,⟨64,706,12,2,47,some 48⟩,⟨64,706,12,2,49,some 49⟩,⟨64,706,12,2,50,some 50⟩,⟨64,706,12,2,51,some 51⟩,⟨64,706,12,2,52,some 52⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (6:Fin 18) (atIndex j)
end Research6970.Height2313.Research6969.HighPendingSeed7
end Z6969Source1179

section Z6969Source1181
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch7Band0
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed7.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (6 : Fin 18) 22 22 9 a 0 :=
  ExtendedJointBills.counted7 _ (by decide : 22 ≤ 24)
end Research6970.Height2313.Research6969.HighDispatch7Band0
end Z6969Source1181

section Z6969Source1182
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch7Band1
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed7.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (6 : Fin 18) 23 24 9 a 0 :=
  ExtendedJointBills.counted7 _ (by decide : 24 ≤ 24)
end Research6970.Height2313.Research6969.HighDispatch7Band1
end Z6969Source1182

section Z6969Source1185
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch7Band2
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed7.Required):Tail (6:Fin 18) 25 27 9 1 0:=
  NormalRoute.tailOfRun [128, 512] ⟨
    entire CompressedReceipts.cell969 CompressedReceipts.checked969,
    entire CompressedReceipts.cell970 CompressedReceipts.checked970,
    entire CompressedReceipts.cell971 CompressedReceipts.checked971⟩
private theorem tail2_0 (needed:HighPendingSeed7.Required):Tail (6:Fin 18) 25 27 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 64, 256, 1024] ⟨
    entire CompressedReceipts.cell972 CompressedReceipts.checked972,
    needed ⟨0,by decide⟩,
    needed ⟨1,by decide⟩,
    needed ⟨2,by decide⟩,
    needed ⟨3,by decide⟩,
    needed ⟨4,by decide⟩,
    entire CompressedReceipts.cell973 CompressedReceipts.checked973,
    entire CompressedReceipts.cell974 CompressedReceipts.checked974,
    entire CompressedReceipts.cell975 CompressedReceipts.checked975,
    entire CompressedReceipts.cell976 CompressedReceipts.checked976,
    entire CompressedReceipts.cell977 CompressedReceipts.checked977⟩
private theorem tail3_0 (needed:HighPendingSeed7.Required):Tail (6:Fin 18) 25 27 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 28, 96, 512, 2048] ⟨
    entire CompressedReceipts.cell978 CompressedReceipts.checked978,
    entire CompressedReceipts.cell979 CompressedReceipts.checked979,
    PaidRows.c980,
    needed ⟨5,by decide⟩,
    needed ⟨6,by decide⟩,
    PaidRows.c981,
    PaidRows.c982,
    entire CompressedReceipts.cell983 CompressedReceipts.checked983,
    PaidRows.c984,
    entire CompressedReceipts.cell985 CompressedReceipts.checked985⟩
private theorem tail4_0 (needed:HighPendingSeed7.Required):Tail (6:Fin 18) 25 27 9 4 0:=
  NormalRoute.tailOfRun [1, 40, 256, 512, 1024, 2048] ⟨
    entire CompressedReceipts.cell986 CompressedReceipts.checked986,
    PaidRows.c987,
    entire CompressedReceipts.cell988 CompressedReceipts.checked988,
    entire CompressedReceipts.cell989 CompressedReceipts.checked989,
    entire CompressedReceipts.cell990 CompressedReceipts.checked990,
    PaidRows.c991,
    entire CompressedReceipts.cell992 CompressedReceipts.checked992⟩
private theorem leaf5_2049:Done (6:Fin 18) ⟨25,27,9,5,2049,some 4096⟩:=power _ 643299 (by decide) PowerReceipts.power41 (by decide) (by decide) (by decide)
private theorem leaf5_1025:Done (6:Fin 18) ⟨25,27,9,5,1025,some 2048⟩:=power _ 643299 (by decide) PowerReceipts.power40 (by decide) (by decide) (by decide)
private theorem tail5_0 (needed:HighPendingSeed7.Required):Tail (6:Fin 18) 25 27 9 5 0:=
  NormalRoute.tailOfRun [1, 128, 512, 1024, 2048, 4096] ⟨
    entire CompressedReceipts.cell993 CompressedReceipts.checked993,
    entire CompressedReceipts.cell994 CompressedReceipts.checked994,
    entire CompressedReceipts.cell995 CompressedReceipts.checked995,
    entire CompressedReceipts.cell996 CompressedReceipts.checked996,
    leaf5_1025,
    leaf5_2049,
    PaidRows.c997⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed7.Required) (a:ℕ) (lo:0<a) (hi:a≤5):
    Tail (6:Fin 18) 25 27 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
  · exact tail5_0 needed
end Research6970.Height2313.Research6969.HighDispatch7Band2
end Z6969Source1185

section Z6969Source1186
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch7Band3
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed7.Required):Tail (6:Fin 18) 28 32 9 1 0:=
  NormalRoute.tailOfRun [128, 512] ⟨
    entire CompressedReceipts.cell998 CompressedReceipts.checked998,
    entire CompressedReceipts.cell999 CompressedReceipts.checked999,
    entire CompressedReceipts.cell1000 CompressedReceipts.checked1000⟩
private theorem tail2_0 (needed:HighPendingSeed7.Required):Tail (6:Fin 18) 28 32 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 48, 128, 512] ⟨
    entire CompressedReceipts.cell1001 CompressedReceipts.checked1001,
    needed ⟨7,by decide⟩,
    needed ⟨8,by decide⟩,
    needed ⟨9,by decide⟩,
    needed ⟨10,by decide⟩,
    needed ⟨11,by decide⟩,
    entire CompressedReceipts.cell1002 CompressedReceipts.checked1002,
    PaidRows.c1003,
    entire CompressedReceipts.cell1004 CompressedReceipts.checked1004,
    entire CompressedReceipts.cell1005 CompressedReceipts.checked1005,
    entire CompressedReceipts.cell1006 CompressedReceipts.checked1006⟩
private theorem tail3_0 (needed:HighPendingSeed7.Required):Tail (6:Fin 18) 28 32 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 32, 64, 256, 1024] ⟨
    entire CompressedReceipts.cell1007 CompressedReceipts.checked1007,
    entire CompressedReceipts.cell1008 CompressedReceipts.checked1008,
    needed ⟨12,by decide⟩,
    needed ⟨13,by decide⟩,
    needed ⟨14,by decide⟩,
    needed ⟨15,by decide⟩,
    PaidRows.c1009,
    entire CompressedReceipts.cell1010 CompressedReceipts.checked1010,
    entire CompressedReceipts.cell1011 CompressedReceipts.checked1011,
    entire CompressedReceipts.cell1012 CompressedReceipts.checked1012,
    entire CompressedReceipts.cell1013 CompressedReceipts.checked1013⟩
private theorem tail4_0 (needed:HighPendingSeed7.Required):Tail (6:Fin 18) 28 32 9 4 0:=
  NormalRoute.tailOfRun [1, 16, 48, 128, 512, 1024] ⟨
    entire CompressedReceipts.cell1014 CompressedReceipts.checked1014,
    entire CompressedReceipts.cell1015 CompressedReceipts.checked1015,
    entire CompressedReceipts.cell1016 CompressedReceipts.checked1016,
    entire CompressedReceipts.cell1017 CompressedReceipts.checked1017,
    PaidRows.c1018,
    entire CompressedReceipts.cell1019 CompressedReceipts.checked1019,
    entire CompressedReceipts.cell1020 CompressedReceipts.checked1020⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed7.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (6:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch7Band3
end Z6969Source1186

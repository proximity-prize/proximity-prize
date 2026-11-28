import ProximityPrize.SubmissionLower.R6970Height2313CompactSeed
import ProximityPrize.SubmissionLower.R6970Height2313CompactRoute
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_fecaa47bf637388d
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.R6970Height2313Dispatch0669
import ProximityPrize.SubmissionLower.R6970Height2313Dispatch0670
import ProximityPrize.SubmissionLower.R6970Height2313PowerRoute
import ProximityPrize.SubmissionLower.R6970Height2313Powers
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade

section Pack_R6970Height2313Dispatch0671

set_option Elab.async false

section Z6969Source1116
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatchSeed2
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute _root_.Research6970.Height2313.Research6969.HighPackets
open _root_.Research6970.Height2313.Research6969.BookView
theorem count (need:_root_.Research6970.Height2313.Research6969.HighPendingSeed2.Required) (s:State (1:Fin 18)):s.labels.card≤_root_.Research6969.CertifiedCell.target:=by
  let b:=_root_.Research6969.TransitionClassification.band s.f.natDegree
  have first:=_root_.Research6969.TransitionClassification.lower_bound s.high
  have last:=_root_.Research6969.OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤_root_.Research6969.TransitionClassification.maxGraph b): Tail (1:Fin 18) (_root_.Research6969.TransitionClassification.grade b) (_root_.Research6969.OrdinaryComplete.upper (savedMainGrade 1+savedRescueGrade 1) b) (_root_.Research6969.TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch2Band0.allDegrees need a p h
    · exact HighDispatch2Band1.allDegrees need a p h
    · exact HighDispatch2Band2.allDegrees need a p h
    · exact HighDispatch2Band3.allDegrees need a p h
    · exact HighDispatch2Band4.allDegrees need a p h
    · exact HighDispatch2Band5.allDegrees need a p h
    · exact HighDispatch2Band6.allDegrees need a p h
    · exact HighDispatch2Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s.clearContent ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6970.Height2313.Research6969.HighDispatchSeed2
end Z6969Source1116

section Z6969Source1117
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighPendingSeed3
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
def regions:Array Region:=#[⟨23,24,9,2,4,some 8⟩,⟨23,24,9,2,9,some 12⟩,⟨23,24,9,2,13,some 16⟩,⟨23,24,9,2,17,some 20⟩,⟨23,24,9,2,21,some 22⟩,⟨23,24,9,2,23,some 24⟩,⟨23,24,9,2,25,some 28⟩,⟨23,24,9,2,29,some 32⟩,⟨23,24,9,3,4,some 8⟩,⟨23,24,9,3,9,some 12⟩,⟨23,24,9,3,13,some 14⟩,⟨23,24,9,3,15,some 16⟩,⟨23,24,9,3,17,some 20⟩,⟨25,27,9,2,4,some 8⟩,⟨25,27,9,2,9,some 12⟩,⟨25,27,9,2,13,some 16⟩,⟨25,27,9,2,17,some 20⟩,⟨25,27,9,2,21,some 22⟩,⟨25,27,9,2,23,some 24⟩,⟨25,27,9,2,25,some 28⟩,⟨25,27,9,2,29,some 32⟩,⟨25,27,9,3,4,some 8⟩,⟨25,27,9,3,9,some 12⟩,⟨25,27,9,3,13,some 14⟩,⟨25,27,9,3,15,some 15⟩,⟨25,27,9,3,16,some 16⟩,⟨25,27,9,3,17,some 17⟩,⟨25,27,9,3,18,some 18⟩,⟨25,27,9,3,19,some 20⟩,⟨25,27,9,3,21,some 24⟩,⟨28,32,9,2,4,some 8⟩,⟨28,32,9,2,9,some 12⟩,⟨28,32,9,2,13,some 16⟩,⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 22⟩,⟨28,32,9,2,23,some 24⟩,⟨28,32,9,2,25,some 28⟩,⟨28,32,9,2,29,some 32⟩,⟨28,32,9,2,33,some 40⟩,⟨28,32,9,3,4,some 8⟩,⟨28,32,9,3,9,some 12⟩,⟨28,32,9,3,13,some 14⟩,⟨28,32,9,3,15,some 15⟩,⟨28,32,9,3,16,some 16⟩,⟨28,32,9,3,17,some 17⟩,⟨28,32,9,3,18,some 18⟩,⟨28,32,9,3,19,some 19⟩,⟨28,32,9,3,20,some 20⟩,⟨28,32,9,3,21,some 21⟩,⟨28,32,9,3,22,some 22⟩,⟨28,32,9,3,23,some 24⟩,⟨28,32,9,3,25,some 28⟩,⟨33,40,9,2,4,some 8⟩,⟨33,40,9,2,9,some 12⟩,⟨33,40,9,2,13,some 16⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 22⟩,⟨33,40,9,2,23,some 24⟩,⟨33,40,9,2,25,some 28⟩,⟨33,40,9,2,29,some 32⟩,⟨33,40,9,2,33,some 40⟩,⟨33,40,9,2,41,some 48⟩,⟨33,40,9,2,49,some 64⟩,⟨33,40,9,2,65,some 96⟩,⟨33,40,9,3,4,some 8⟩,⟨33,40,9,3,9,some 12⟩,⟨33,40,9,3,13,some 14⟩,⟨33,40,9,3,15,some 15⟩,⟨33,40,9,3,16,some 16⟩,⟨33,40,9,3,17,some 17⟩,⟨33,40,9,3,18,some 18⟩,⟨33,40,9,3,19,some 19⟩,⟨33,40,9,3,20,some 20⟩,⟨33,40,9,3,21,some 21⟩,⟨33,40,9,3,22,some 22⟩,⟨33,40,9,3,23,some 24⟩,⟨33,40,9,3,25,some 26⟩,⟨33,40,9,3,27,some 28⟩,⟨33,40,9,3,29,some 32⟩,⟨33,40,9,3,33,some 40⟩,⟨33,40,9,4,25,some 28⟩,⟨41,49,9,2,4,some 8⟩,⟨41,49,9,2,9,some 12⟩,⟨41,49,9,2,13,some 16⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 22⟩,⟨41,49,9,2,23,some 24⟩,⟨41,49,9,2,25,some 28⟩,⟨41,49,9,2,29,some 32⟩,⟨41,49,9,2,33,some 40⟩,⟨41,49,9,2,41,some 48⟩,⟨41,49,9,2,49,some 64⟩,⟨41,49,9,2,65,some 96⟩,⟨41,49,9,3,4,some 8⟩,⟨41,49,9,3,9,some 12⟩,⟨41,49,9,3,13,some 14⟩,⟨41,49,9,3,15,some 15⟩,⟨41,49,9,3,16,some 16⟩,⟨41,49,9,3,17,some 17⟩,⟨41,49,9,3,18,some 18⟩,⟨41,49,9,3,19,some 19⟩,⟨41,49,9,3,20,some 20⟩,⟨41,49,9,3,21,some 21⟩,⟨41,49,9,3,22,some 22⟩,⟨41,49,9,3,23,some 24⟩,⟨41,49,9,3,25,some 26⟩,⟨41,49,9,3,27,some 28⟩,⟨41,49,9,3,29,some 32⟩,⟨41,49,9,3,33,some 36⟩,⟨41,49,9,3,37,some 40⟩,⟨41,49,9,3,41,some 44⟩,⟨41,49,9,3,45,some 48⟩,⟨41,49,9,3,49,some 64⟩,⟨41,49,9,3,65,some 96⟩,⟨50,63,10,2,4,some 8⟩,⟨50,63,10,2,9,some 12⟩,⟨50,63,10,2,13,some 16⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 22⟩,⟨50,63,10,2,23,some 24⟩,⟨50,63,10,2,25,some 28⟩,⟨50,63,10,2,29,some 32⟩,⟨50,63,10,2,33,some 40⟩,⟨50,63,10,2,41,some 44⟩,⟨50,63,10,2,45,some 48⟩,⟨50,63,10,2,49,some 50⟩,⟨50,63,10,2,51,some 51⟩,⟨50,63,10,2,52,some 52⟩,⟨50,63,10,2,53,some 53⟩,⟨50,63,10,2,54,some 54⟩,⟨50,63,10,2,55,some 55⟩,⟨50,63,10,2,56,some 56⟩,⟨50,63,10,2,57,some 57⟩,⟨50,63,10,2,58,some 58⟩,⟨50,63,10,2,59,some 60⟩,⟨50,63,10,2,61,some 64⟩,⟨50,63,10,3,4,some 8⟩,⟨50,63,10,3,9,some 12⟩,⟨50,63,10,3,13,some 13⟩,⟨50,63,10,3,14,some 14⟩,⟨50,63,10,3,15,some 15⟩,⟨50,63,10,3,16,some 16⟩,⟨50,63,10,3,17,some 17⟩,⟨50,63,10,3,18,some 18⟩,⟨50,63,10,3,19,some 19⟩,⟨50,63,10,3,20,some 20⟩,⟨50,63,10,3,21,some 21⟩,⟨50,63,10,3,22,some 22⟩,⟨50,63,10,3,23,some 23⟩,⟨50,63,10,3,24,some 24⟩,⟨50,63,10,3,25,some 25⟩,⟨50,63,10,3,26,some 26⟩,⟨50,63,10,3,27,some 27⟩,⟨50,63,10,3,28,some 28⟩,⟨50,63,10,3,29,some 29⟩,⟨50,63,10,3,30,some 30⟩,⟨50,63,10,3,31,some 32⟩,⟨50,63,10,3,33,some 33⟩,⟨50,63,10,3,34,some 34⟩,⟨50,63,10,3,35,some 35⟩,⟨50,63,10,3,36,some 36⟩,⟨50,63,10,3,37,some 37⟩,⟨50,63,10,3,38,some 38⟩,⟨50,63,10,3,39,some 39⟩,⟨64,722,12,1,0,some 0⟩,⟨64,722,12,1,1,some 1⟩,⟨64,722,12,1,2,some 3⟩,⟨64,722,12,1,4,some 8⟩,⟨64,722,12,1,9,some 12⟩,⟨64,722,12,1,13,some 16⟩,⟨64,722,12,1,17,some 20⟩,⟨64,722,12,1,21,some 24⟩,⟨64,722,12,1,25,some 28⟩,⟨64,722,12,1,29,some 32⟩,⟨64,722,12,1,33,some 40⟩,⟨64,722,12,1,41,some 48⟩,⟨64,722,12,1,49,some 64⟩,⟨64,722,12,2,4,some 8⟩,⟨64,722,12,2,9,some 12⟩,⟨64,722,12,2,13,some 16⟩,⟨64,722,12,2,17,some 20⟩,⟨64,722,12,2,21,some 22⟩,⟨64,722,12,2,23,some 24⟩,⟨64,722,12,2,25,some 28⟩,⟨64,722,12,2,29,some 32⟩,⟨64,722,12,2,33,some 36⟩,⟨64,722,12,2,37,some 40⟩,⟨64,722,12,2,41,some 44⟩,⟨64,722,12,2,45,some 48⟩,⟨64,722,12,2,49,some 50⟩,⟨64,722,12,2,51,some 51⟩,⟨64,722,12,2,52,some 52⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (2:Fin 18) (atIndex j)
end Research6970.Height2313.Research6969.HighPendingSeed3
end Z6969Source1117

section Z6969Source1119
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch3Band0
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed3.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (2 : Fin 18) 22 22 9 a 0 :=
  ExtendedJointBills.counted3 _ (by decide : 22 ≤ 22)
end Research6970.Height2313.Research6969.HighDispatch3Band0
end Z6969Source1119

section Z6969Source1122
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch3Band1
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0671_tail1_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 1 0:=
  NormalRoute.tailOfRun [128, 512] ⟨
    entire CompressedReceipts.cell339 CompressedReceipts.checked339,
    entire CompressedReceipts.cell340 CompressedReceipts.checked340,
    entire CompressedReceipts.cell341 CompressedReceipts.checked341⟩
private theorem pack_R6970Height2313Dispatch0671_tail2_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 22, 24, 28, 32, 64, 256, 1024] ⟨
    entire CompressedReceipts.cell342 CompressedReceipts.checked342,
    needed ⟨0,by decide⟩,
    needed ⟨1,by decide⟩,
    needed ⟨2,by decide⟩,
    needed ⟨3,by decide⟩,
    needed ⟨4,by decide⟩,
    needed ⟨5,by decide⟩,
    needed ⟨6,by decide⟩,
    needed ⟨7,by decide⟩,
    entire CompressedReceipts.cell343 CompressedReceipts.checked343,
    entire CompressedReceipts.cell344 CompressedReceipts.checked344,
    entire CompressedReceipts.cell345 CompressedReceipts.checked345,
    entire CompressedReceipts.cell346 CompressedReceipts.checked346⟩
private theorem leaf3_2049:Done (2:Fin 18) ⟨23,24,9,3,2049,some 4096⟩:=power _ 385979 (by decide) PowerReceipts.power20 (by decide) (by decide) (by decide)
private theorem pack_R6970Height2313Dispatch0671_tail3_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 14, 16, 20, 24, 64, 256, 512, 1024, 2048, 4096] ⟨
    entire CompressedReceipts.cell347 CompressedReceipts.checked347,
    needed ⟨8,by decide⟩,
    needed ⟨9,by decide⟩,
    needed ⟨10,by decide⟩,
    needed ⟨11,by decide⟩,
    needed ⟨12,by decide⟩,
    PaidRows.c348,
    entire CompressedReceipts.cell349 CompressedReceipts.checked349,
    entire CompressedReceipts.cell350 CompressedReceipts.checked350,
    entire CompressedReceipts.cell351 CompressedReceipts.checked351,
    entire CompressedReceipts.cell352 CompressedReceipts.checked352,
    entire CompressedReceipts.cell353 CompressedReceipts.checked353,
    leaf3_2049,
    entire CompressedReceipts.cell354 CompressedReceipts.checked354⟩
private theorem leaf4_32769:Done (2:Fin 18) ⟨23,24,9,4,32769,none⟩:=power _ 514639 (by decide) PowerReceipts.power25 (by decide) (by decide) (by decide)
private theorem leaf4_8193:Done (2:Fin 18) ⟨23,24,9,4,8193,some 32768⟩:=power _ 514639 (by decide) PowerReceipts.power24 (by decide) (by decide) (by decide)
private theorem leaf4_4097:Done (2:Fin 18) ⟨23,24,9,4,4097,some 8192⟩:=power _ 514639 (by decide) PowerReceipts.power23 (by decide) (by decide) (by decide)
private theorem leaf4_2049:Done (2:Fin 18) ⟨23,24,9,4,2049,some 4096⟩:=power _ 514639 (by decide) PowerReceipts.power22 (by decide) (by decide) (by decide)
private theorem leaf4_1025:Done (2:Fin 18) ⟨23,24,9,4,1025,some 2048⟩:=power _ 514639 (by decide) PowerReceipts.power21 (by decide) (by decide) (by decide)
private theorem pack_R6970Height2313Dispatch0671_tail4_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 4 0:=
  NormalRoute.tailOfRun [1, 40, 256, 512, 1024, 2048, 4096, 8192, 32768] ⟨
    entire CompressedReceipts.cell355 CompressedReceipts.checked355,
    PaidRows.c356,
    entire CompressedReceipts.cell357 CompressedReceipts.checked357,
    entire CompressedReceipts.cell358 CompressedReceipts.checked358,
    entire CompressedReceipts.cell359 CompressedReceipts.checked359,
    leaf4_1025,
    leaf4_2049,
    leaf4_4097,
    leaf4_8193,
    leaf4_32769⟩
private theorem leaf5_32769:Done (2:Fin 18) ⟨23,24,9,5,32769,none⟩:=power _ 643299 (by decide) PowerReceipts.power30 (by decide) (by decide) (by decide)
private theorem leaf5_8193:Done (2:Fin 18) ⟨23,24,9,5,8193,some 32768⟩:=power _ 643299 (by decide) PowerReceipts.power29 (by decide) (by decide) (by decide)
private theorem leaf5_4097:Done (2:Fin 18) ⟨23,24,9,5,4097,some 8192⟩:=power _ 643299 (by decide) PowerReceipts.power28 (by decide) (by decide) (by decide)
private theorem pack_R6970Height2313Dispatch0671_leaf5_2049:Done (2:Fin 18) ⟨23,24,9,5,2049,some 4096⟩:=power _ 643299 (by decide) PowerReceipts.power27 (by decide) (by decide) (by decide)
private theorem pack_R6970Height2313Dispatch0671_leaf5_1025:Done (2:Fin 18) ⟨23,24,9,5,1025,some 2048⟩:=power _ 643299 (by decide) PowerReceipts.power26 (by decide) (by decide) (by decide)
private theorem pack_R6970Height2313Dispatch0671_tail5_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 5 0:=
  NormalRoute.tailOfRun [1, 128, 512, 1024, 2048, 4096, 8192, 32768] ⟨
    entire CompressedReceipts.cell360 CompressedReceipts.checked360,
    entire CompressedReceipts.cell361 CompressedReceipts.checked361,
    entire CompressedReceipts.cell362 CompressedReceipts.checked362,
    entire CompressedReceipts.cell363 CompressedReceipts.checked363,
    pack_R6970Height2313Dispatch0671_leaf5_1025,
    pack_R6970Height2313Dispatch0671_leaf5_2049,
    leaf5_4097,
    leaf5_8193,
    leaf5_32769⟩
private theorem leaf6_32769:Done (2:Fin 18) ⟨23,24,9,6,32769,none⟩:=power _ 771959 (by decide) PowerReceipts.power35 (by decide) (by decide) (by decide)
private theorem leaf6_8193:Done (2:Fin 18) ⟨23,24,9,6,8193,some 32768⟩:=power _ 771959 (by decide) PowerReceipts.power34 (by decide) (by decide) (by decide)
private theorem leaf6_4097:Done (2:Fin 18) ⟨23,24,9,6,4097,some 8192⟩:=power _ 771959 (by decide) PowerReceipts.power33 (by decide) (by decide) (by decide)
private theorem leaf6_2049:Done (2:Fin 18) ⟨23,24,9,6,2049,some 4096⟩:=power _ 771959 (by decide) PowerReceipts.power32 (by decide) (by decide) (by decide)
private theorem leaf6_1025:Done (2:Fin 18) ⟨23,24,9,6,1025,some 2048⟩:=power _ 771959 (by decide) PowerReceipts.power31 (by decide) (by decide) (by decide)
private theorem tail6_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 23 24 9 6 0:=
  NormalRoute.tailOfRun [1, 256, 1024, 2048, 4096, 8192, 32768] ⟨
    entire CompressedReceipts.cell364 CompressedReceipts.checked364,
    entire CompressedReceipts.cell365 CompressedReceipts.checked365,
    entire CompressedReceipts.cell366 CompressedReceipts.checked366,
    leaf6_1025,
    leaf6_2049,
    leaf6_4097,
    leaf6_8193,
    leaf6_32769⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed3.Required) (a:ℕ) (lo:0<a) (hi:a≤6):
    Tail (2:Fin 18) 23 24 9 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0671_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail3_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail4_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail5_0 needed
  · exact tail6_0 needed
end Research6970.Height2313.Research6969.HighDispatch3Band1
end Z6969Source1122

section Z6969Source1124
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch3Band2
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0671_tail1_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 1 0:=
  NormalRoute.tailOfRun [128, 512] ⟨
    entire CompressedReceipts.cell367 CompressedReceipts.checked367,
    entire CompressedReceipts.cell368 CompressedReceipts.checked368,
    entire CompressedReceipts.cell369 CompressedReceipts.checked369⟩
private theorem pack_R6970Height2313Dispatch0671_tail2_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 22, 24, 28, 32, 48, 128, 256, 1024] ⟨
    entire CompressedReceipts.cell370 CompressedReceipts.checked370,
    needed ⟨13,by decide⟩,
    needed ⟨14,by decide⟩,
    needed ⟨15,by decide⟩,
    needed ⟨16,by decide⟩,
    needed ⟨17,by decide⟩,
    needed ⟨18,by decide⟩,
    needed ⟨19,by decide⟩,
    needed ⟨20,by decide⟩,
    PaidRows.c371,
    entire CompressedReceipts.cell372 CompressedReceipts.checked372,
    entire CompressedReceipts.cell373 CompressedReceipts.checked373,
    entire CompressedReceipts.cell374 CompressedReceipts.checked374,
    entire CompressedReceipts.cell375 CompressedReceipts.checked375⟩
private theorem pack_R6970Height2313Dispatch0671_tail3_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 14, 15, 16, 17, 18, 20, 24, 32, 96, 256, 512, 1024] ⟨
    entire CompressedReceipts.cell376 CompressedReceipts.checked376,
    needed ⟨21,by decide⟩,
    needed ⟨22,by decide⟩,
    needed ⟨23,by decide⟩,
    needed ⟨24,by decide⟩,
    needed ⟨25,by decide⟩,
    needed ⟨26,by decide⟩,
    needed ⟨27,by decide⟩,
    needed ⟨28,by decide⟩,
    needed ⟨29,by decide⟩,
    entire CompressedReceipts.cell377 CompressedReceipts.checked377,
    entire CompressedReceipts.cell378 CompressedReceipts.checked378,
    entire CompressedReceipts.cell379 CompressedReceipts.checked379,
    entire CompressedReceipts.cell380 CompressedReceipts.checked380,
    entire CompressedReceipts.cell381 CompressedReceipts.checked381,
    entire CompressedReceipts.cell382 CompressedReceipts.checked382⟩
private theorem leaf4_1025:Done (2:Fin 18) ⟨25,27,9,4,1025,some 2048⟩:=power _ 514639 (by decide) PowerReceipts.power38 (by decide) (by decide) (by decide)
private theorem pack_R6970Height2313Dispatch0671_tail4_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 4 0:=
  NormalRoute.tailOfRun [1, 12, 48, 256, 512, 1024, 2048] ⟨
    entire CompressedReceipts.cell383 CompressedReceipts.checked383,
    entire CompressedReceipts.cell384 CompressedReceipts.checked384,
    entire CompressedReceipts.cell385 CompressedReceipts.checked385,
    entire CompressedReceipts.cell386 CompressedReceipts.checked386,
    entire CompressedReceipts.cell387 CompressedReceipts.checked387,
    entire CompressedReceipts.cell388 CompressedReceipts.checked388,
    leaf4_1025,
    entire CompressedReceipts.cell389 CompressedReceipts.checked389⟩
private theorem pack_R6970Height2313Dispatch0671_leaf5_2049:Done (2:Fin 18) ⟨25,27,9,5,2049,some 4096⟩:=power _ 643299 (by decide) PowerReceipts.power41 (by decide) (by decide) (by decide)
private theorem pack_R6970Height2313Dispatch0671_leaf5_1025:Done (2:Fin 18) ⟨25,27,9,5,1025,some 2048⟩:=power _ 643299 (by decide) PowerReceipts.power40 (by decide) (by decide) (by decide)
private theorem leaf5_513:Done (2:Fin 18) ⟨25,27,9,5,513,some 1024⟩:=power _ 643299 (by decide) PowerReceipts.power39 (by decide) (by decide) (by decide)
private theorem pack_R6970Height2313Dispatch0671_tail5_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 25 27 9 5 0:=
  NormalRoute.tailOfRun [1, 96, 512, 1024, 2048, 4096] ⟨
    entire CompressedReceipts.cell390 CompressedReceipts.checked390,
    entire CompressedReceipts.cell391 CompressedReceipts.checked391,
    entire CompressedReceipts.cell392 CompressedReceipts.checked392,
    leaf5_513,
    pack_R6970Height2313Dispatch0671_leaf5_1025,
    pack_R6970Height2313Dispatch0671_leaf5_2049,
    PaidRows.c393⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed3.Required) (a:ℕ) (lo:0<a) (hi:a≤5):
    Tail (2:Fin 18) 25 27 9 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0671_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail3_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail4_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail5_0 needed
end Research6970.Height2313.Research6969.HighDispatch3Band2
end Z6969Source1124

section Z6969Source1126
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch3Band3
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0671_tail1_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 28 32 9 1 0:=
  NormalRoute.tailOfRun [128, 512] ⟨
    entire CompressedReceipts.cell394 CompressedReceipts.checked394,
    entire CompressedReceipts.cell395 CompressedReceipts.checked395,
    entire CompressedReceipts.cell396 CompressedReceipts.checked396⟩
private theorem pack_R6970Height2313Dispatch0671_tail2_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 28 32 9 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 22, 24, 28, 32, 40, 64, 128, 256] ⟨
    entire CompressedReceipts.cell397 CompressedReceipts.checked397,
    needed ⟨30,by decide⟩,
    needed ⟨31,by decide⟩,
    needed ⟨32,by decide⟩,
    needed ⟨33,by decide⟩,
    needed ⟨34,by decide⟩,
    needed ⟨35,by decide⟩,
    needed ⟨36,by decide⟩,
    needed ⟨37,by decide⟩,
    needed ⟨38,by decide⟩,
    PaidRows.c398,
    entire CompressedReceipts.cell399 CompressedReceipts.checked399,
    entire CompressedReceipts.cell400 CompressedReceipts.checked400,
    entire CompressedReceipts.cell401 CompressedReceipts.checked401⟩
private theorem pack_R6970Height2313Dispatch0671_tail3_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 28 32 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 28, 32, 48, 128, 256, 512] ⟨
    entire CompressedReceipts.cell402 CompressedReceipts.checked402,
    needed ⟨39,by decide⟩,
    needed ⟨40,by decide⟩,
    needed ⟨41,by decide⟩,
    needed ⟨42,by decide⟩,
    needed ⟨43,by decide⟩,
    needed ⟨44,by decide⟩,
    needed ⟨45,by decide⟩,
    needed ⟨46,by decide⟩,
    needed ⟨47,by decide⟩,
    needed ⟨48,by decide⟩,
    needed ⟨49,by decide⟩,
    needed ⟨50,by decide⟩,
    needed ⟨51,by decide⟩,
    entire CompressedReceipts.cell403 CompressedReceipts.checked403,
    entire CompressedReceipts.cell404 CompressedReceipts.checked404,
    entire CompressedReceipts.cell405 CompressedReceipts.checked405,
    entire CompressedReceipts.cell406 CompressedReceipts.checked406,
    entire CompressedReceipts.cell407 CompressedReceipts.checked407,
    entire CompressedReceipts.cell408 CompressedReceipts.checked408⟩
private theorem pack_R6970Height2313Dispatch0671_tail4_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 28 32 9 4 0:=
  NormalRoute.tailOfRun [1, 12, 16, 28, 64, 128, 256, 512, 1024] ⟨
    entire CompressedReceipts.cell409 CompressedReceipts.checked409,
    entire CompressedReceipts.cell410 CompressedReceipts.checked410,
    entire CompressedReceipts.cell411 CompressedReceipts.checked411,
    entire CompressedReceipts.cell412 CompressedReceipts.checked412,
    entire CompressedReceipts.cell413 CompressedReceipts.checked413,
    entire CompressedReceipts.cell414 CompressedReceipts.checked414,
    entire CompressedReceipts.cell415 CompressedReceipts.checked415,
    entire CompressedReceipts.cell416 CompressedReceipts.checked416,
    entire CompressedReceipts.cell417 CompressedReceipts.checked417,
    entire CompressedReceipts.cell418 CompressedReceipts.checked418⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed3.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (2:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0671_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail3_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch3Band3
end Z6969Source1126

section Z6969Source1127
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch3Band4
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0671_tail1_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 33 40 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell419 CompressedReceipts.checked419,
    entire CompressedReceipts.cell420 CompressedReceipts.checked420⟩
private theorem pack_R6970Height2313Dispatch0671_tail2_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 33 40 9 2 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 22, 24, 28, 32, 40, 48, 64, 96, 128] ⟨
    entire CompressedReceipts.cell421 CompressedReceipts.checked421,
    needed ⟨52,by decide⟩,
    needed ⟨53,by decide⟩,
    needed ⟨54,by decide⟩,
    needed ⟨55,by decide⟩,
    needed ⟨56,by decide⟩,
    needed ⟨57,by decide⟩,
    needed ⟨58,by decide⟩,
    needed ⟨59,by decide⟩,
    needed ⟨60,by decide⟩,
    needed ⟨61,by decide⟩,
    needed ⟨62,by decide⟩,
    needed ⟨63,by decide⟩,
    entire CompressedReceipts.cell422 CompressedReceipts.checked422,
    PaidRows.c423⟩
private theorem pack_R6970Height2313Dispatch0671_tail3_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 33 40 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 26, 28, 32, 40, 48, 64, 96, 128, 256] ⟨
    entire CompressedReceipts.cell424 CompressedReceipts.checked424,
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
    needed ⟨78,by decide⟩,
    needed ⟨79,by decide⟩,
    entire CompressedReceipts.cell425 CompressedReceipts.checked425,
    entire CompressedReceipts.cell426 CompressedReceipts.checked426,
    entire CompressedReceipts.cell427 CompressedReceipts.checked427,
    entire CompressedReceipts.cell428 CompressedReceipts.checked428,
    entire CompressedReceipts.cell429 CompressedReceipts.checked429,
    entire CompressedReceipts.cell430 CompressedReceipts.checked430⟩
private theorem pack_R6970Height2313Dispatch0671_tail4_0 (needed:HighPendingSeed3.Required):Tail (2:Fin 18) 33 40 9 4 0:=
  NormalRoute.tailOfRun [1, 12, 16, 20, 24, 28, 32, 48, 96, 128, 256] ⟨
    entire CompressedReceipts.cell431 CompressedReceipts.checked431,
    entire CompressedReceipts.cell432 CompressedReceipts.checked432,
    entire CompressedReceipts.cell433 CompressedReceipts.checked433,
    entire CompressedReceipts.cell434 CompressedReceipts.checked434,
    entire CompressedReceipts.cell435 CompressedReceipts.checked435,
    needed ⟨80,by decide⟩,
    entire CompressedReceipts.cell436 CompressedReceipts.checked436,
    entire CompressedReceipts.cell437 CompressedReceipts.checked437,
    entire CompressedReceipts.cell438 CompressedReceipts.checked438,
    entire CompressedReceipts.cell439 CompressedReceipts.checked439,
    entire CompressedReceipts.cell440 CompressedReceipts.checked440,
    entire CompressedReceipts.cell441 CompressedReceipts.checked441⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed3.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (2:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0671_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail3_0 needed
  · exact pack_R6970Height2313Dispatch0671_tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch3Band4
end Z6969Source1127
end Pack_R6970Height2313Dispatch0671

section Pack_R6970Height2313Dispatch0675

set_option Elab.async false

section Z6969Source1164
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighPendingSeed6
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
def regions:Array Region:=#[⟨25,27,9,2,9,some 12⟩,⟨25,27,9,2,13,some 16⟩,⟨25,27,9,2,17,some 20⟩,⟨25,27,9,2,21,some 24⟩,⟨25,27,9,2,25,some 28⟩,⟨25,27,9,3,9,some 12⟩,⟨25,27,9,3,13,some 16⟩,⟨25,27,9,3,17,some 20⟩,⟨28,32,9,2,9,some 12⟩,⟨28,32,9,2,13,some 16⟩,⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 24⟩,⟨28,32,9,2,25,some 28⟩,⟨28,32,9,3,9,some 12⟩,⟨28,32,9,3,13,some 16⟩,⟨28,32,9,3,17,some 20⟩,⟨28,32,9,3,21,some 24⟩,⟨33,40,9,2,9,some 12⟩,⟨33,40,9,2,13,some 16⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 24⟩,⟨33,40,9,2,25,some 28⟩,⟨33,40,9,3,9,some 12⟩,⟨33,40,9,3,13,some 16⟩,⟨33,40,9,3,17,some 20⟩,⟨33,40,9,3,21,some 24⟩,⟨41,49,9,2,9,some 12⟩,⟨41,49,9,2,13,some 16⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 24⟩,⟨41,49,9,2,25,some 28⟩,⟨41,49,9,2,49,some 64⟩,⟨41,49,9,3,9,some 12⟩,⟨41,49,9,3,13,some 16⟩,⟨41,49,9,3,17,some 20⟩,⟨41,49,9,3,21,some 24⟩,⟨41,49,9,3,33,some 40⟩,⟨41,49,9,3,41,some 48⟩,⟨50,63,10,2,9,some 12⟩,⟨50,63,10,2,13,some 16⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 24⟩,⟨50,63,10,2,25,some 28⟩,⟨50,63,10,2,29,some 32⟩,⟨50,63,10,2,33,some 40⟩,⟨50,63,10,2,41,some 48⟩,⟨50,63,10,2,49,some 56⟩,⟨50,63,10,2,57,some 60⟩,⟨50,63,10,3,9,some 12⟩,⟨50,63,10,3,13,some 16⟩,⟨50,63,10,3,17,some 18⟩,⟨50,63,10,3,19,some 20⟩,⟨50,63,10,3,21,some 24⟩,⟨50,63,10,3,25,some 28⟩,⟨50,63,10,3,29,some 32⟩,⟨50,63,10,3,33,some 40⟩,⟨64,654,12,2,9,some 12⟩,⟨64,654,12,2,13,some 16⟩,⟨64,654,12,2,17,some 20⟩,⟨64,654,12,2,21,some 22⟩,⟨64,654,12,2,23,some 23⟩,⟨64,654,12,2,24,some 24⟩,⟨64,654,12,2,25,some 26⟩,⟨64,654,12,2,27,some 28⟩,⟨64,654,12,2,29,some 30⟩,⟨64,654,12,2,31,some 32⟩,⟨64,654,12,2,33,some 36⟩,⟨64,654,12,2,37,some 38⟩,⟨64,654,12,2,39,some 40⟩,⟨64,654,12,2,41,some 42⟩,⟨64,654,12,2,43,some 44⟩,⟨64,654,12,2,45,some 46⟩,⟨64,654,12,2,47,some 47⟩,⟨64,654,12,2,48,some 48⟩,⟨64,654,12,2,49,some 49⟩,⟨64,654,12,2,50,some 50⟩,⟨64,654,12,2,51,some 51⟩,⟨64,654,12,2,52,some 52⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (5:Fin 18) (atIndex j)
end Research6970.Height2313.Research6969.HighPendingSeed6
end Z6969Source1164

section Z6969Source1166
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch6Band0
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed6.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (5 : Fin 18) 22 22 9 a 0 :=
  ExtendedJointBills.counted6 _ (by decide : 22 ≤ 24)
end Research6970.Height2313.Research6969.HighDispatch6Band0
end Z6969Source1166

section Z6969Source1167
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch6Band1
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed6.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (5 : Fin 18) 23 24 9 a 0 :=
  ExtendedJointBills.counted6 _ (by decide : 24 ≤ 24)
end Research6970.Height2313.Research6969.HighDispatch6Band1
end Z6969Source1167

section Z6969Source1170
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch6Band2
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0675_tail1_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 25 27 9 1 0:=
  NormalRoute.tailOfRun [128, 512] ⟨
    entire CompressedReceipts.cell814 CompressedReceipts.checked814,
    entire CompressedReceipts.cell815 CompressedReceipts.checked815,
    entire CompressedReceipts.cell816 CompressedReceipts.checked816⟩
private theorem pack_R6970Height2313Dispatch0675_tail2_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 25 27 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 64, 256, 1024] ⟨
    entire CompressedReceipts.cell817 CompressedReceipts.checked817,
    needed ⟨0,by decide⟩,
    needed ⟨1,by decide⟩,
    needed ⟨2,by decide⟩,
    needed ⟨3,by decide⟩,
    needed ⟨4,by decide⟩,
    entire CompressedReceipts.cell818 CompressedReceipts.checked818,
    entire CompressedReceipts.cell819 CompressedReceipts.checked819,
    entire CompressedReceipts.cell820 CompressedReceipts.checked820,
    entire CompressedReceipts.cell821 CompressedReceipts.checked821,
    entire CompressedReceipts.cell822 CompressedReceipts.checked822⟩
private theorem pack_R6970Height2313Dispatch0675_tail3_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 25 27 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 28, 96, 512, 1024] ⟨
    entire CompressedReceipts.cell823 CompressedReceipts.checked823,
    entire CompressedReceipts.cell824 CompressedReceipts.checked824,
    needed ⟨5,by decide⟩,
    needed ⟨6,by decide⟩,
    needed ⟨7,by decide⟩,
    PaidRows.c825,
    PaidRows.c826,
    entire CompressedReceipts.cell827 CompressedReceipts.checked827,
    entire CompressedReceipts.cell828 CompressedReceipts.checked828,
    entire CompressedReceipts.cell829 CompressedReceipts.checked829⟩
private theorem pack_R6970Height2313Dispatch0675_tail4_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 25 27 9 4 0:=
  NormalRoute.tailOfRun [1, 40, 256, 512, 1024, 2048] ⟨
    entire CompressedReceipts.cell830 CompressedReceipts.checked830,
    PaidRows.c831,
    entire CompressedReceipts.cell832 CompressedReceipts.checked832,
    entire CompressedReceipts.cell833 CompressedReceipts.checked833,
    entire CompressedReceipts.cell834 CompressedReceipts.checked834,
    PaidRows.c835,
    entire CompressedReceipts.cell836 CompressedReceipts.checked836⟩
private theorem pack_R6970Height2313Dispatch0675_leaf5_2049:Done (5:Fin 18) ⟨25,27,9,5,2049,some 4096⟩:=power _ 643299 (by decide) PowerReceipts.power41 (by decide) (by decide) (by decide)
private theorem pack_R6970Height2313Dispatch0675_leaf5_1025:Done (5:Fin 18) ⟨25,27,9,5,1025,some 2048⟩:=power _ 643299 (by decide) PowerReceipts.power40 (by decide) (by decide) (by decide)
private theorem pack_R6970Height2313Dispatch0675_tail5_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 25 27 9 5 0:=
  NormalRoute.tailOfRun [1, 128, 512, 1024, 2048, 4096] ⟨
    entire CompressedReceipts.cell837 CompressedReceipts.checked837,
    entire CompressedReceipts.cell838 CompressedReceipts.checked838,
    entire CompressedReceipts.cell839 CompressedReceipts.checked839,
    entire CompressedReceipts.cell840 CompressedReceipts.checked840,
    pack_R6970Height2313Dispatch0675_leaf5_1025,
    pack_R6970Height2313Dispatch0675_leaf5_2049,
    PaidRows.c841⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed6.Required) (a:ℕ) (lo:0<a) (hi:a≤5):
    Tail (5:Fin 18) 25 27 9 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0675_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0675_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0675_tail3_0 needed
  · exact pack_R6970Height2313Dispatch0675_tail4_0 needed
  · exact pack_R6970Height2313Dispatch0675_tail5_0 needed
end Research6970.Height2313.Research6969.HighDispatch6Band2
end Z6969Source1170

section Z6969Source1172
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch6Band3
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0675_tail1_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 28 32 9 1 0:=
  NormalRoute.tailOfRun [128, 512] ⟨
    entire CompressedReceipts.cell842 CompressedReceipts.checked842,
    entire CompressedReceipts.cell843 CompressedReceipts.checked843,
    entire CompressedReceipts.cell844 CompressedReceipts.checked844⟩
private theorem pack_R6970Height2313Dispatch0675_tail2_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 28 32 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 48, 128, 512] ⟨
    entire CompressedReceipts.cell845 CompressedReceipts.checked845,
    needed ⟨8,by decide⟩,
    needed ⟨9,by decide⟩,
    needed ⟨10,by decide⟩,
    needed ⟨11,by decide⟩,
    needed ⟨12,by decide⟩,
    entire CompressedReceipts.cell846 CompressedReceipts.checked846,
    PaidRows.c847,
    entire CompressedReceipts.cell848 CompressedReceipts.checked848,
    entire CompressedReceipts.cell849 CompressedReceipts.checked849,
    entire CompressedReceipts.cell850 CompressedReceipts.checked850⟩
private theorem pack_R6970Height2313Dispatch0675_tail3_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 28 32 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 32, 64, 256, 1024] ⟨
    entire CompressedReceipts.cell851 CompressedReceipts.checked851,
    entire CompressedReceipts.cell852 CompressedReceipts.checked852,
    needed ⟨13,by decide⟩,
    needed ⟨14,by decide⟩,
    needed ⟨15,by decide⟩,
    needed ⟨16,by decide⟩,
    PaidRows.c853,
    entire CompressedReceipts.cell854 CompressedReceipts.checked854,
    entire CompressedReceipts.cell855 CompressedReceipts.checked855,
    entire CompressedReceipts.cell856 CompressedReceipts.checked856,
    entire CompressedReceipts.cell857 CompressedReceipts.checked857⟩
private theorem pack_R6970Height2313Dispatch0675_tail4_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 28 32 9 4 0:=
  NormalRoute.tailOfRun [1, 16, 48, 128, 256, 512, 1024] ⟨
    entire CompressedReceipts.cell858 CompressedReceipts.checked858,
    PaidRows.c859,
    entire CompressedReceipts.cell860 CompressedReceipts.checked860,
    entire CompressedReceipts.cell861 CompressedReceipts.checked861,
    entire CompressedReceipts.cell862 CompressedReceipts.checked862,
    entire CompressedReceipts.cell863 CompressedReceipts.checked863,
    entire CompressedReceipts.cell864 CompressedReceipts.checked864,
    entire CompressedReceipts.cell865 CompressedReceipts.checked865⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed6.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (5:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0675_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0675_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0675_tail3_0 needed
  · exact pack_R6970Height2313Dispatch0675_tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch6Band3
end Z6969Source1172

section Z6969Source1173
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch6Band4
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0675_tail1_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 33 40 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell866 CompressedReceipts.checked866,
    entire CompressedReceipts.cell867 CompressedReceipts.checked867⟩
private theorem pack_R6970Height2313Dispatch0675_tail2_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 33 40 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 128] ⟨
    entire CompressedReceipts.cell868 CompressedReceipts.checked868,
    needed ⟨17,by decide⟩,
    needed ⟨18,by decide⟩,
    needed ⟨19,by decide⟩,
    needed ⟨20,by decide⟩,
    needed ⟨21,by decide⟩,
    entire CompressedReceipts.cell869 CompressedReceipts.checked869,
    entire CompressedReceipts.cell870 CompressedReceipts.checked870,
    entire CompressedReceipts.cell871 CompressedReceipts.checked871,
    entire CompressedReceipts.cell872 CompressedReceipts.checked872,
    entire CompressedReceipts.cell873 CompressedReceipts.checked873,
    PaidRows.c874⟩
private theorem pack_R6970Height2313Dispatch0675_tail3_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 33 40 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 64, 128, 512] ⟨
    entire CompressedReceipts.cell875 CompressedReceipts.checked875,
    entire CompressedReceipts.cell876 CompressedReceipts.checked876,
    needed ⟨22,by decide⟩,
    needed ⟨23,by decide⟩,
    needed ⟨24,by decide⟩,
    needed ⟨25,by decide⟩,
    PaidRows.c877,
    entire CompressedReceipts.cell878 CompressedReceipts.checked878,
    PaidRows.c879,
    entire CompressedReceipts.cell880 CompressedReceipts.checked880,
    entire CompressedReceipts.cell881 CompressedReceipts.checked881,
    PaidRows.c882,
    entire CompressedReceipts.cell883 CompressedReceipts.checked883⟩
private theorem pack_R6970Height2313Dispatch0675_tail4_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 33 40 9 4 0:=
  NormalRoute.tailOfRun [1, 16, 24, 40, 96, 256] ⟨
    entire CompressedReceipts.cell884 CompressedReceipts.checked884,
    PaidRows.c885,
    entire CompressedReceipts.cell886 CompressedReceipts.checked886,
    PaidRows.c887,
    entire CompressedReceipts.cell888 CompressedReceipts.checked888,
    entire CompressedReceipts.cell889 CompressedReceipts.checked889,
    entire CompressedReceipts.cell890 CompressedReceipts.checked890⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed6.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (5:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0675_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0675_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0675_tail3_0 needed
  · exact pack_R6970Height2313Dispatch0675_tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch6Band4
end Z6969Source1173

section Z6969Source1175
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch6Band5
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem pack_R6970Height2313Dispatch0675_tail1_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 41 49 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell891 CompressedReceipts.checked891,
    entire CompressedReceipts.cell892 CompressedReceipts.checked892⟩
private theorem pack_R6970Height2313Dispatch0675_tail2_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 41 49 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 128] ⟨
    entire CompressedReceipts.cell893 CompressedReceipts.checked893,
    needed ⟨26,by decide⟩,
    needed ⟨27,by decide⟩,
    needed ⟨28,by decide⟩,
    needed ⟨29,by decide⟩,
    needed ⟨30,by decide⟩,
    entire CompressedReceipts.cell894 CompressedReceipts.checked894,
    entire CompressedReceipts.cell895 CompressedReceipts.checked895,
    entire CompressedReceipts.cell896 CompressedReceipts.checked896,
    needed ⟨31,by decide⟩,
    entire CompressedReceipts.cell897 CompressedReceipts.checked897,
    entire CompressedReceipts.cell898 CompressedReceipts.checked898⟩
private theorem pack_R6970Height2313Dispatch0675_tail3_0 (needed:HighPendingSeed6.Required):Tail (5:Fin 18) 41 49 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 96] ⟨
    entire CompressedReceipts.cell899 CompressedReceipts.checked899,
    entire CompressedReceipts.cell900 CompressedReceipts.checked900,
    needed ⟨32,by decide⟩,
    needed ⟨33,by decide⟩,
    needed ⟨34,by decide⟩,
    needed ⟨35,by decide⟩,
    PaidRows.c901,
    entire CompressedReceipts.cell902 CompressedReceipts.checked902,
    needed ⟨36,by decide⟩,
    needed ⟨37,by decide⟩,
    PaidRows.c903,
    entire CompressedReceipts.cell904 CompressedReceipts.checked904,
    entire CompressedReceipts.cell905 CompressedReceipts.checked905⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed6.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (5:Fin 18) 41 49 9 a 0:=by
  interval_cases a
  · exact pack_R6970Height2313Dispatch0675_tail1_0 needed
  · exact pack_R6970Height2313Dispatch0675_tail2_0 needed
  · exact pack_R6970Height2313Dispatch0675_tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch6Band5
end Z6969Source1175
end Pack_R6970Height2313Dispatch0675

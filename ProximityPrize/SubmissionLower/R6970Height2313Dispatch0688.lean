import ProximityPrize.SubmissionLower.R6970Height2313CompactSeed
import ProximityPrize.SubmissionLower.R6970Height2313CompactRoute
import ProximityPrize.SubmissionLower.Bundle6970_fecaa47bf637388d
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.R6970Height2313Dispatch0687
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade

set_option Elab.async false

section Z6969Source1321
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch16Band4
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed16.Required):Tail (15:Fin 18) 33 40 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell2336 CompressedReceipts.checked2336,
    entire CompressedReceipts.cell2337 CompressedReceipts.checked2337⟩
private theorem tail2_0 (needed:HighPendingSeed16.Required):Tail (15:Fin 18) 33 40 9 2 0:=
  NormalRoute.tailOfRun [16, 20, 24, 32, 64, 256] ⟨
    entire CompressedReceipts.cell2338 CompressedReceipts.checked2338,
    needed ⟨2,by decide⟩,
    needed ⟨3,by decide⟩,
    entire CompressedReceipts.cell2339 CompressedReceipts.checked2339,
    PaidRows.c2340,
    entire CompressedReceipts.cell2341 CompressedReceipts.checked2341,
    entire CompressedReceipts.cell2342 CompressedReceipts.checked2342⟩
private theorem tail3_0 (needed:HighPendingSeed16.Required):Tail (15:Fin 18) 33 40 9 3 0:=
  NormalRoute.tailOfRun [8, 16, 24, 40, 128, 512] ⟨
    entire CompressedReceipts.cell2343 CompressedReceipts.checked2343,
    entire CompressedReceipts.cell2344 CompressedReceipts.checked2344,
    entire CompressedReceipts.cell2345 CompressedReceipts.checked2345,
    entire CompressedReceipts.cell2346 CompressedReceipts.checked2346,
    entire CompressedReceipts.cell2347 CompressedReceipts.checked2347,
    entire CompressedReceipts.cell2348 CompressedReceipts.checked2348,
    entire CompressedReceipts.cell2349 CompressedReceipts.checked2349⟩
private theorem tail4_0 (needed:HighPendingSeed16.Required):Tail (15:Fin 18) 33 40 9 4 0:=
  NormalRoute.tailOfRun [3, 24, 64, 256] ⟨
    entire CompressedReceipts.cell2350 CompressedReceipts.checked2350,
    entire CompressedReceipts.cell2351 CompressedReceipts.checked2351,
    entire CompressedReceipts.cell2352 CompressedReceipts.checked2352,
    entire CompressedReceipts.cell2353 CompressedReceipts.checked2353,
    entire CompressedReceipts.cell2354 CompressedReceipts.checked2354⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed16.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (15:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch16Band4
end Z6969Source1321

section Z6969Source1323
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch16Band5
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed16.Required):Tail (15:Fin 18) 41 49 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell2355 CompressedReceipts.checked2355,
    entire CompressedReceipts.cell2356 CompressedReceipts.checked2356⟩
private theorem tail2_0 (needed:HighPendingSeed16.Required):Tail (15:Fin 18) 41 49 9 2 0:=
  NormalRoute.tailOfRun [16, 20, 24, 32, 48, 96] ⟨
    entire CompressedReceipts.cell2357 CompressedReceipts.checked2357,
    needed ⟨4,by decide⟩,
    needed ⟨5,by decide⟩,
    PaidRows.c2358,
    entire CompressedReceipts.cell2359 CompressedReceipts.checked2359,
    entire CompressedReceipts.cell2360 CompressedReceipts.checked2360,
    entire CompressedReceipts.cell2361 CompressedReceipts.checked2361⟩
private theorem tail3_0 (needed:HighPendingSeed16.Required):Tail (15:Fin 18) 41 49 9 3 0:=
  NormalRoute.tailOfRun [8, 16, 24, 40, 64, 128] ⟨
    entire CompressedReceipts.cell2362 CompressedReceipts.checked2362,
    entire CompressedReceipts.cell2363 CompressedReceipts.checked2363,
    entire CompressedReceipts.cell2364 CompressedReceipts.checked2364,
    entire CompressedReceipts.cell2365 CompressedReceipts.checked2365,
    entire CompressedReceipts.cell2366 CompressedReceipts.checked2366,
    entire CompressedReceipts.cell2367 CompressedReceipts.checked2367,
    entire CompressedReceipts.cell2368 CompressedReceipts.checked2368⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed16.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (15:Fin 18) 41 49 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch16Band5
end Z6969Source1323

section Z6969Source1324
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch16Band6
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed16.Required):Tail (15:Fin 18) 50 63 10 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell2369 CompressedReceipts.checked2369,
    entire CompressedReceipts.cell2370 CompressedReceipts.checked2370⟩
private theorem tail2_0 (needed:HighPendingSeed16.Required):Tail (15:Fin 18) 50 63 10 2 0:=
  NormalRoute.tailOfRun [16, 20, 24, 28, 40, 64] ⟨
    entire CompressedReceipts.cell2371 CompressedReceipts.checked2371,
    needed ⟨6,by decide⟩,
    needed ⟨7,by decide⟩,
    entire CompressedReceipts.cell2372 CompressedReceipts.checked2372,
    entire CompressedReceipts.cell2373 CompressedReceipts.checked2373,
    entire CompressedReceipts.cell2374 CompressedReceipts.checked2374,
    entire CompressedReceipts.cell2375 CompressedReceipts.checked2375⟩
private theorem tail3_0 (needed:HighPendingSeed16.Required):Tail (15:Fin 18) 50 63 10 3 0:=
  NormalRoute.tailOfRun [8, 16, 24, 32, 48, 64, 128] ⟨
    entire CompressedReceipts.cell2376 CompressedReceipts.checked2376,
    entire CompressedReceipts.cell2377 CompressedReceipts.checked2377,
    entire CompressedReceipts.cell2378 CompressedReceipts.checked2378,
    entire CompressedReceipts.cell2379 CompressedReceipts.checked2379,
    entire CompressedReceipts.cell2380 CompressedReceipts.checked2380,
    entire CompressedReceipts.cell2381 CompressedReceipts.checked2381,
    entire CompressedReceipts.cell2382 CompressedReceipts.checked2382,
    entire CompressedReceipts.cell2383 CompressedReceipts.checked2383⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed16.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (15:Fin 18) 50 63 10 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch16Band6
end Z6969Source1324

section Z6969Source1325
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch16Band7
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed16.Required):Tail (15:Fin 18) 64 628 12 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell2384 CompressedReceipts.checked2384,
    entire CompressedReceipts.cell2385 CompressedReceipts.checked2385⟩
private theorem tail2_0 (needed:HighPendingSeed16.Required):Tail (15:Fin 18) 64 628 12 2 0:=
  NormalRoute.tailOfRun [12, 16, 20, 24, 28, 32, 40, 48, 64] ⟨
    entire CompressedReceipts.cell2386 CompressedReceipts.checked2386,
    needed ⟨8,by decide⟩,
    needed ⟨9,by decide⟩,
    needed ⟨10,by decide⟩,
    needed ⟨11,by decide⟩,
    entire CompressedReceipts.cell2387 CompressedReceipts.checked2387,
    entire CompressedReceipts.cell2388 CompressedReceipts.checked2388,
    entire CompressedReceipts.cell2389 CompressedReceipts.checked2389,
    entire CompressedReceipts.cell2390 CompressedReceipts.checked2390,
    entire CompressedReceipts.cell2391 CompressedReceipts.checked2391⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed16.Required) (a:ℕ) (lo:0<a) (hi:a≤2):
    Tail (15:Fin 18) 64 628 12 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
end Research6970.Height2313.Research6969.HighDispatch16Band7
end Z6969Source1325

section Z6969Source1326
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatchSeed16
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute _root_.Research6970.Height2313.Research6969.HighPackets
open _root_.Research6970.Height2313.Research6969.BookView
theorem count (need:_root_.Research6970.Height2313.Research6969.HighPendingSeed16.Required) (s:State (15:Fin 18)):s.labels.card≤_root_.Research6969.CertifiedCell.target:=by
  let b:=_root_.Research6969.TransitionClassification.band s.f.natDegree
  have first:=_root_.Research6969.TransitionClassification.lower_bound s.high
  have last:=_root_.Research6969.OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤_root_.Research6969.TransitionClassification.maxGraph b): Tail (15:Fin 18) (_root_.Research6969.TransitionClassification.grade b) (_root_.Research6969.OrdinaryComplete.upper (savedMainGrade 15+savedRescueGrade 15) b) (_root_.Research6969.TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch16Band0.allDegrees need a p h
    · exact HighDispatch16Band1.allDegrees need a p h
    · exact HighDispatch16Band2.allDegrees need a p h
    · exact HighDispatch16Band3.allDegrees need a p h
    · exact HighDispatch16Band4.allDegrees need a p h
    · exact HighDispatch16Band5.allDegrees need a p h
    · exact HighDispatch16Band6.allDegrees need a p h
    · exact HighDispatch16Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s.clearContent ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6970.Height2313.Research6969.HighDispatchSeed16
end Z6969Source1326

section Z6969Source1327
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighPendingSeed17
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
def regions:Array Region:=#[⟨28,32,9,2,21,some 24⟩,⟨33,40,9,2,21,some 24⟩,⟨41,49,9,2,21,some 24⟩,⟨50,63,10,2,21,some 24⟩,⟨64,628,12,2,17,some 20⟩,⟨64,628,12,2,21,some 24⟩,⟨64,628,12,2,25,some 28⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (16:Fin 18) (atIndex j)
end Research6970.Height2313.Research6969.HighPendingSeed17
end Z6969Source1327

section Z6969Source1329
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch17Band0
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed17.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (16 : Fin 18) 22 22 9 a 0 :=
  ExtendedJointBills.counted17 _ (by decide : 22 ≤ 27)
end Research6970.Height2313.Research6969.HighDispatch17Band0
end Z6969Source1329

section Z6969Source1330
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch17Band1
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed17.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (16 : Fin 18) 23 24 9 a 0 :=
  ExtendedJointBills.counted17 _ (by decide : 24 ≤ 27)
end Research6970.Height2313.Research6969.HighDispatch17Band1
end Z6969Source1330

section Z6969Source1331
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch17Band2
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed17.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 5) :
    Tail (16 : Fin 18) 25 27 9 a 0 :=
  ExtendedJointBills.counted17 _ (by decide : 27 ≤ 27)
end Research6970.Height2313.Research6969.HighDispatch17Band2
end Z6969Source1331

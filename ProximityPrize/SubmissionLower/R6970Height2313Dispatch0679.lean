import ProximityPrize.SubmissionLower.R6970Height2313CompactSeed
import ProximityPrize.SubmissionLower.R6970Height2313CompactRoute
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.R6970Height2308GradeReceipts
import ProximityPrize.SubmissionLower.R6970Height2308PowerReceipts
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.R6970Height2313Dispatch0678
import ProximityPrize.SubmissionLower.R6970Height2313PowerRoute
import ProximityPrize.SubmissionLower.R6970Height2313Powers
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade

set_option Elab.async false

section Z6969Source1212
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch9Band1
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed9.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (8 : Fin 18) 23 24 9 a 0 :=
  ExtendedJointBills.counted9 _ (by decide : 24 ≤ 26)
end Research6970.Height2313.Research6969.HighDispatch9Band1
end Z6969Source1212

section Z6969Source1213
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch9Band2
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed9.Required)
    (a : ℕ) (pos : 0 < a) (cap : a ≤ 5) :
    Tail (8:Fin 18) 25 27 9 a 0 := by
  intro s h
  obtain ⟨lo, hi, content, graph, seedFloor, seedCeil⟩ := h
  by_cases below : s.f.natDegree ≤ 26
  · exact ExtendedJointBills.counted9 ⟨25,26,9,a,0,none⟩
      (show 26 ≤ 26 by decide) s ⟨lo,below,content,graph,seedFloor,seedCeil⟩
  · have large : 27 ≤ s.f.natDegree := by omega
    exact BandGradeReceipts.count9 a pos cap s ⟨large,hi,content,graph,seedFloor,seedCeil⟩
end Research6970.Height2313.Research6969.HighDispatch9Band2
end Z6969Source1213

section Z6969Source1216
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch9Band3
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 28 32 9 1 0:=
  NormalRoute.tailOfRun [128, 1024] ⟨
    entire CompressedReceipts.cell1310 CompressedReceipts.checked1310,
    entire CompressedReceipts.cell1311 CompressedReceipts.checked1311,
    entire CompressedReceipts.cell1312 CompressedReceipts.checked1312⟩
private theorem tail2_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 28 32 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 40, 128, 512] ⟨
    entire CompressedReceipts.cell1313 CompressedReceipts.checked1313,
    needed ⟨0,by decide⟩,
    needed ⟨1,by decide⟩,
    needed ⟨2,by decide⟩,
    needed ⟨3,by decide⟩,
    needed ⟨4,by decide⟩,
    entire CompressedReceipts.cell1314 CompressedReceipts.checked1314,
    entire CompressedReceipts.cell1315 CompressedReceipts.checked1315,
    entire CompressedReceipts.cell1316 CompressedReceipts.checked1316,
    entire CompressedReceipts.cell1317 CompressedReceipts.checked1317⟩
private theorem tail3_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 28 32 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 48, 128, 512] ⟨
    entire CompressedReceipts.cell1318 CompressedReceipts.checked1318,
    entire CompressedReceipts.cell1319 CompressedReceipts.checked1319,
    entire CompressedReceipts.cell1320 CompressedReceipts.checked1320,
    entire CompressedReceipts.cell1321 CompressedReceipts.checked1321,
    PaidRows.c1322,
    entire CompressedReceipts.cell1323 CompressedReceipts.checked1323,
    PaidRows.c1324,
    entire CompressedReceipts.cell1325 CompressedReceipts.checked1325,
    entire CompressedReceipts.cell1326 CompressedReceipts.checked1326,
    entire CompressedReceipts.cell1327 CompressedReceipts.checked1327⟩
private theorem tail4_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 28 32 9 4 0:=
  NormalRoute.tailOfRun [3, 20, 96, 512, 1024] ⟨
    entire CompressedReceipts.cell1328 CompressedReceipts.checked1328,
    PaidRows.c1329,
    PaidRows.c1330,
    PaidRows.c1331,
    entire CompressedReceipts.cell1332 CompressedReceipts.checked1332,
    entire CompressedReceipts.cell1333 CompressedReceipts.checked1333⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed9.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (8:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch9Band3
end Z6969Source1216

section Z6969Source1218
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch9Band4
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 33 40 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1334 CompressedReceipts.checked1334,
    entire CompressedReceipts.cell1335 CompressedReceipts.checked1335⟩
private theorem tail2_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 33 40 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 40, 64, 128] ⟨
    entire CompressedReceipts.cell1336 CompressedReceipts.checked1336,
    needed ⟨5,by decide⟩,
    needed ⟨6,by decide⟩,
    needed ⟨7,by decide⟩,
    needed ⟨8,by decide⟩,
    needed ⟨9,by decide⟩,
    entire CompressedReceipts.cell1337 CompressedReceipts.checked1337,
    entire CompressedReceipts.cell1338 CompressedReceipts.checked1338,
    entire CompressedReceipts.cell1339 CompressedReceipts.checked1339,
    PaidRows.c1340⟩
private theorem tail3_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 33 40 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 32, 48, 128, 512] ⟨
    entire CompressedReceipts.cell1341 CompressedReceipts.checked1341,
    entire CompressedReceipts.cell1342 CompressedReceipts.checked1342,
    entire CompressedReceipts.cell1343 CompressedReceipts.checked1343,
    entire CompressedReceipts.cell1344 CompressedReceipts.checked1344,
    PaidRows.c1345,
    entire CompressedReceipts.cell1346 CompressedReceipts.checked1346,
    PaidRows.c1347,
    entire CompressedReceipts.cell1348 CompressedReceipts.checked1348,
    entire CompressedReceipts.cell1349 CompressedReceipts.checked1349,
    entire CompressedReceipts.cell1350 CompressedReceipts.checked1350,
    entire CompressedReceipts.cell1351 CompressedReceipts.checked1351⟩
private theorem tail4_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 33 40 9 4 0:=
  NormalRoute.tailOfRun [3, 20, 40, 128, 512] ⟨
    entire CompressedReceipts.cell1352 CompressedReceipts.checked1352,
    PaidRows.c1353,
    PaidRows.c1354,
    entire CompressedReceipts.cell1355 CompressedReceipts.checked1355,
    PaidRows.c1356,
    entire CompressedReceipts.cell1357 CompressedReceipts.checked1357⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed9.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (8:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch9Band4
end Z6969Source1218

section Z6969Source1220
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch9Band5
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 41 49 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1358 CompressedReceipts.checked1358,
    entire CompressedReceipts.cell1359 CompressedReceipts.checked1359⟩
private theorem tail2_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 41 49 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 48, 64, 128] ⟨
    entire CompressedReceipts.cell1360 CompressedReceipts.checked1360,
    needed ⟨10,by decide⟩,
    needed ⟨11,by decide⟩,
    needed ⟨12,by decide⟩,
    needed ⟨13,by decide⟩,
    needed ⟨14,by decide⟩,
    entire CompressedReceipts.cell1361 CompressedReceipts.checked1361,
    entire CompressedReceipts.cell1362 CompressedReceipts.checked1362,
    needed ⟨15,by decide⟩,
    entire CompressedReceipts.cell1363 CompressedReceipts.checked1363,
    entire CompressedReceipts.cell1364 CompressedReceipts.checked1364⟩
private theorem tail3_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 41 49 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 32, 40, 48, 64, 128] ⟨
    entire CompressedReceipts.cell1365 CompressedReceipts.checked1365,
    entire CompressedReceipts.cell1366 CompressedReceipts.checked1366,
    entire CompressedReceipts.cell1367 CompressedReceipts.checked1367,
    PaidRows.c1368,
    PaidRows.c1369,
    entire CompressedReceipts.cell1370 CompressedReceipts.checked1370,
    PaidRows.c1371,
    entire CompressedReceipts.cell1372 CompressedReceipts.checked1372,
    entire CompressedReceipts.cell1373 CompressedReceipts.checked1373,
    entire CompressedReceipts.cell1374 CompressedReceipts.checked1374,
    entire CompressedReceipts.cell1375 CompressedReceipts.checked1375,
    entire CompressedReceipts.cell1376 CompressedReceipts.checked1376⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed9.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (8:Fin 18) 41 49 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch9Band5
end Z6969Source1220

section Z6969Source1221
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch9Band6
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 50 63 10 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1377 CompressedReceipts.checked1377,
    entire CompressedReceipts.cell1378 CompressedReceipts.checked1378⟩
private theorem tail2_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 50 63 10 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 40, 48, 56, 64] ⟨
    entire CompressedReceipts.cell1379 CompressedReceipts.checked1379,
    needed ⟨16,by decide⟩,
    needed ⟨17,by decide⟩,
    needed ⟨18,by decide⟩,
    needed ⟨19,by decide⟩,
    needed ⟨20,by decide⟩,
    entire CompressedReceipts.cell1380 CompressedReceipts.checked1380,
    entire CompressedReceipts.cell1381 CompressedReceipts.checked1381,
    entire CompressedReceipts.cell1382 CompressedReceipts.checked1382,
    needed ⟨21,by decide⟩,
    PaidRows.c1383,
    entire CompressedReceipts.cell1384 CompressedReceipts.checked1384⟩
private theorem leaf3_49:Done (8:Fin 18) ⟨50,63,10,3,49,some 64⟩:=power _ 385979 (by decide) PowerReceipts.power48 (by decide) (by decide) (by decide)
private theorem tail3_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 50 63 10 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 96] ⟨
    entire CompressedReceipts.cell1385 CompressedReceipts.checked1385,
    entire CompressedReceipts.cell1386 CompressedReceipts.checked1386,
    entire CompressedReceipts.cell1387 CompressedReceipts.checked1387,
    PaidRows.c1388,
    needed ⟨22,by decide⟩,
    needed ⟨23,by decide⟩,
    entire CompressedReceipts.cell1389 CompressedReceipts.checked1389,
    entire CompressedReceipts.cell1390 CompressedReceipts.checked1390,
    needed ⟨24,by decide⟩,
    BandPowerReceipts.cover9_41,
    leaf3_49,
    entire CompressedReceipts.cell1391 CompressedReceipts.checked1391,
    entire CompressedReceipts.cell1392 CompressedReceipts.checked1392⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed9.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (8:Fin 18) 50 63 10 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch9Band6
end Z6969Source1221

section Z6969Source1222
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch9Band7
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 64 654 12 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1393 CompressedReceipts.checked1393,
    entire CompressedReceipts.cell1394 CompressedReceipts.checked1394⟩
private theorem tail2_0 (needed:HighPendingSeed9.Required):Tail (8:Fin 18) 64 654 12 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 36, 40, 48, 52] ⟨
    entire CompressedReceipts.cell1395 CompressedReceipts.checked1395,
    needed ⟨25,by decide⟩,
    needed ⟨26,by decide⟩,
    needed ⟨27,by decide⟩,
    needed ⟨28,by decide⟩,
    needed ⟨29,by decide⟩,
    needed ⟨30,by decide⟩,
    needed ⟨31,by decide⟩,
    needed ⟨32,by decide⟩,
    needed ⟨33,by decide⟩,
    needed ⟨34,by decide⟩,
    entire CompressedReceipts.cell1396 CompressedReceipts.checked1396⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed9.Required) (a:ℕ) (lo:0<a) (hi:a≤2):
    Tail (8:Fin 18) 64 654 12 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
end Research6970.Height2313.Research6969.HighDispatch9Band7
end Z6969Source1222

section Z6969Source1223
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatchSeed9
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute _root_.Research6970.Height2313.Research6969.HighPackets
open _root_.Research6970.Height2313.Research6969.BookView
theorem count (need:_root_.Research6970.Height2313.Research6969.HighPendingSeed9.Required) (s:State (8:Fin 18)):s.labels.card≤_root_.Research6969.CertifiedCell.target:=by
  let b:=_root_.Research6969.TransitionClassification.band s.f.natDegree
  have first:=_root_.Research6969.TransitionClassification.lower_bound s.high
  have last:=_root_.Research6969.OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤_root_.Research6969.TransitionClassification.maxGraph b): Tail (8:Fin 18) (_root_.Research6969.TransitionClassification.grade b) (_root_.Research6969.OrdinaryComplete.upper (savedMainGrade 8+savedRescueGrade 8) b) (_root_.Research6969.TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch9Band0.allDegrees need a p h
    · exact HighDispatch9Band1.allDegrees need a p h
    · exact HighDispatch9Band2.allDegrees need a p h
    · exact HighDispatch9Band3.allDegrees need a p h
    · exact HighDispatch9Band4.allDegrees need a p h
    · exact HighDispatch9Band5.allDegrees need a p h
    · exact HighDispatch9Band6.allDegrees need a p h
    · exact HighDispatch9Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s.clearContent ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6970.Height2313.Research6969.HighDispatchSeed9
end Z6969Source1223

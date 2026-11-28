import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0686
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0976
import ProximityPrize.SubmissionLower.Z6969Pack0687
import ProximityPrize.SubmissionLower.Z6969Pack0941
import ProximityPrize.SubmissionLower.Z6969Pack0688
import ProximityPrize.SubmissionLower.Z6969Pack0689
import ProximityPrize.SubmissionLower.Z6969Pack0931
import ProximityPrize.SubmissionLower.Z6969Pack0949
import ProximityPrize.SubmissionLower.Z6969Pack0963
import ProximityPrize.SubmissionLower.Z6969Pack0967
import ProximityPrize.SubmissionLower.Z6969Pack0970
import ProximityPrize.SubmissionLower.Z6969Pack0972
import ProximityPrize.SubmissionLower.Z6969Pack0973
import ProximityPrize.SubmissionLower.Z6969Pack0974
import ProximityPrize.SubmissionLower.Z6969Pack0975

set_option Elab.async false

-- Source: Research6969.HardFit15At000
section Z6969Source3064
set_option autoImplicit true
namespace Research6969.HardFit15At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1080 2)
theorem case0: NormalRoute.Done (14:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1080 1)
theorem case1: NormalRoute.Done (14:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1080 4)
theorem case2: NormalRoute.Done (14:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1080 3)
theorem case3: NormalRoute.Done (14:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1080 6)
theorem case4: NormalRoute.Done (14:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1080 5)
theorem case5: NormalRoute.Done (14:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1080 8)
theorem case6: NormalRoute.Done (14:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1080 7)
theorem case7: NormalRoute.Done (14:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route1080 12)
theorem case8: NormalRoute.Done (14:Fin 18) ⟨64,628,12,2,13,some 16⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route1080 11)
theorem case9: NormalRoute.Done (14:Fin 18) ⟨64,628,12,2,17,some 20⟩:=PairRoute.start _ leaf9
end Research6969.HardFit15At000
end Z6969Source3064

-- Source: Research6969.HardFit15At010
section Z6969Source3065
set_option autoImplicit true
namespace Research6969.HardFit15At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1080 10)
theorem case10: NormalRoute.Done (14:Fin 18) ⟨64,628,12,2,21,some 24⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1080 9)
theorem case11: NormalRoute.Done (14:Fin 18) ⟨64,628,12,2,25,some 28⟩:=PairRoute.start _ leaf1
end Research6969.HardFit15At010
end Z6969Source3065

-- Source: Research6969.HardComplete15
section Z6969Source3066
set_option autoImplicit true
namespace Research6969.HardComplete15
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_6 (j:Fin HighPendingSeed15.regions.size) (l:0≤j.val) (h:j.val<6):Done (14:Fin 18) (HighPendingSeed15.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit15At000.case0
  · exact HardFit15At000.case1
  · exact HardFit15At000.case2
  · exact HardFit15At000.case3
  · exact HardFit15At000.case4
  · exact HardFit15At000.case5
private theorem covered6_12 (j:Fin HighPendingSeed15.regions.size) (l:6≤j.val) (h:j.val<12):Done (14:Fin 18) (HighPendingSeed15.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit15At000.case6
  · exact HardFit15At000.case7
  · exact HardFit15At000.case8
  · exact HardFit15At000.case9
  · exact HardFit15At010.case10
  · exact HardFit15At010.case11
private theorem covered0_12 (j:Fin HighPendingSeed15.regions.size) (l:0≤j.val) (h:j.val<12):Done (14:Fin 18) (HighPendingSeed15.atIndex j):=by
  by_cases low:j.val<6
  · exact covered0_6 j l low
  · exact covered6_12 j (by omega) h
theorem required:HighPendingSeed15.Required:=fun j=>covered0_12 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete15
end Z6969Source3066

-- Source: Research6969.HardFit16At000
section Z6969Source3067
set_option autoImplicit true
namespace Research6969.HardFit16At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1080 14)
theorem case0: NormalRoute.Done (15:Fin 18) ⟨28,32,9,2,17,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1080 13)
theorem case1: NormalRoute.Done (15:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1080 16)
theorem case2: NormalRoute.Done (15:Fin 18) ⟨33,40,9,2,17,some 20⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1080 15)
theorem case3: NormalRoute.Done (15:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1080 18)
theorem case4: NormalRoute.Done (15:Fin 18) ⟨41,49,9,2,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1080 17)
theorem case5: NormalRoute.Done (15:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1100 0)
theorem case6: NormalRoute.Done (15:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1080 19)
theorem case7: NormalRoute.Done (15:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route1100 4)
theorem case8: NormalRoute.Done (15:Fin 18) ⟨64,628,12,2,13,some 16⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route1100 3)
theorem case9: NormalRoute.Done (15:Fin 18) ⟨64,628,12,2,17,some 20⟩:=PairRoute.start _ leaf9
end Research6969.HardFit16At000
end Z6969Source3067

-- Source: Research6969.HardFit16At010
section Z6969Source3068
set_option autoImplicit true
namespace Research6969.HardFit16At010
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1100 2)
theorem case10: NormalRoute.Done (15:Fin 18) ⟨64,628,12,2,21,some 24⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1100 1)
theorem case11: NormalRoute.Done (15:Fin 18) ⟨64,628,12,2,25,some 28⟩:=PairRoute.start _ leaf1
end Research6969.HardFit16At010
end Z6969Source3068

-- Source: Research6969.HardComplete16
section Z6969Source3069
set_option autoImplicit true
namespace Research6969.HardComplete16
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_6 (j:Fin HighPendingSeed16.regions.size) (l:0≤j.val) (h:j.val<6):Done (15:Fin 18) (HighPendingSeed16.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit16At000.case0
  · exact HardFit16At000.case1
  · exact HardFit16At000.case2
  · exact HardFit16At000.case3
  · exact HardFit16At000.case4
  · exact HardFit16At000.case5
private theorem covered6_12 (j:Fin HighPendingSeed16.regions.size) (l:6≤j.val) (h:j.val<12):Done (15:Fin 18) (HighPendingSeed16.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit16At000.case6
  · exact HardFit16At000.case7
  · exact HardFit16At000.case8
  · exact HardFit16At000.case9
  · exact HardFit16At010.case10
  · exact HardFit16At010.case11
private theorem covered0_12 (j:Fin HighPendingSeed16.regions.size) (l:0≤j.val) (h:j.val<12):Done (15:Fin 18) (HighPendingSeed16.atIndex j):=by
  by_cases low:j.val<6
  · exact covered0_6 j l low
  · exact covered6_12 j (by omega) h
theorem required:HighPendingSeed16.Required:=fun j=>covered0_12 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete16
end Z6969Source3069

-- Source: Research6969.HardFit17At000
section Z6969Source3070
set_option autoImplicit true
namespace Research6969.HardFit17At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1100 5)
theorem case0: NormalRoute.Done (16:Fin 18) ⟨28,32,9,2,21,some 24⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1100 6)
theorem case1: NormalRoute.Done (16:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1100 7)
theorem case2: NormalRoute.Done (16:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1100 8)
theorem case3: NormalRoute.Done (16:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1100 11)
theorem case4: NormalRoute.Done (16:Fin 18) ⟨64,628,12,2,17,some 20⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1100 10)
theorem case5: NormalRoute.Done (16:Fin 18) ⟨64,628,12,2,21,some 24⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1100 9)
theorem case6: NormalRoute.Done (16:Fin 18) ⟨64,628,12,2,25,some 28⟩:=PairRoute.start _ leaf6
end Research6969.HardFit17At000
end Z6969Source3070

-- Source: Research6969.HardComplete17
section Z6969Source3071
set_option autoImplicit true
namespace Research6969.HardComplete17
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_7 (j:Fin HighPendingSeed17.regions.size) (l:0≤j.val) (h:j.val<7):Done (16:Fin 18) (HighPendingSeed17.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit17At000.case0
  · exact HardFit17At000.case1
  · exact HardFit17At000.case2
  · exact HardFit17At000.case3
  · exact HardFit17At000.case4
  · exact HardFit17At000.case5
  · exact HardFit17At000.case6
theorem required:HighPendingSeed17.Required:=fun j=>covered0_7 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete17
end Z6969Source3071

-- Source: Research6969.HardFit18At000
section Z6969Source3072
set_option autoImplicit true
namespace Research6969.HardFit18At000
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1100 12)
theorem case0: NormalRoute.Done (17:Fin 18) ⟨33,40,9,2,21,some 24⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1100 13)
theorem case1: NormalRoute.Done (17:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1100 14)
theorem case2: NormalRoute.Done (17:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1100 17)
theorem case3: NormalRoute.Done (17:Fin 18) ⟨64,581,12,2,17,some 20⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1100 16)
theorem case4: NormalRoute.Done (17:Fin 18) ⟨64,581,12,2,21,some 24⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1100 15)
theorem case5: NormalRoute.Done (17:Fin 18) ⟨64,581,12,2,25,some 28⟩:=PairRoute.start _ leaf5
end Research6969.HardFit18At000
end Z6969Source3072

-- Source: Research6969.HardComplete18
section Z6969Source3073
set_option autoImplicit true
namespace Research6969.HardComplete18
open NormalRoute
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
private theorem covered0_6 (j:Fin HighPendingSeed18.regions.size) (l:0≤j.val) (h:j.val<6):Done (17:Fin 18) (HighPendingSeed18.atIndex j):=by
  rcases j with ⟨k,kFit⟩
  change _≤k at l
  change k<_ at h
  interval_cases k
  · exact HardFit18At000.case0
  · exact HardFit18At000.case1
  · exact HardFit18At000.case2
  · exact HardFit18At000.case3
  · exact HardFit18At000.case4
  · exact HardFit18At000.case5
theorem required:HighPendingSeed18.Required:=fun j=>covered0_6 j (Nat.zero_le _) j.isLt
end Research6969.HardComplete18
end Z6969Source3073

-- Source: Research6969.Completed6969
section Z6969Source3074
set_option autoImplicit true
namespace Research6969.Completed
open ProximityPrize.Benchmark
theorem count {u del} (M:Lower6960.Far6969RescueGeometry.Model u del) {Γ}
    (F:Lower6960.Far6969RescueGeometry.Family M Γ)
    (lo:2314≤M.overhead) (hi:M.overhead≤2557) : Γ.card≤274779381266040419 :=
  FinalCoverage.count ⟨HardComplete1.required,HardComplete2.required,HardComplete3.required,HardComplete4.required,HardComplete5.required,HardComplete6.required,HardComplete7.required,HardComplete8.required,HardComplete9.required,HardComplete10.required,HardComplete11.required,HardComplete12.required,HardComplete13.required,HardComplete14.required,HardComplete15.required,HardComplete16.required,HardComplete17.required,HardComplete18.required⟩ M F lo hi
end Research6969.Completed
end Z6969Source3074

import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0625
import ProximityPrize.SubmissionLower.Z6969Pack0626
import ProximityPrize.SubmissionLower.Z6969Pack0627
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound

set_option Elab.async false

-- Source: Research6969.PackedRanks387To387
section Z6969Source0749
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks387To387
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment13955_3070 : P1_7_1.groupedPoleMoment 13955 3070 ≤ 1052683166434338 :=
  _root_.PoleAffine6970.certified 13955 3070 1052683166434338 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks387To387

namespace Research6969.PackedRanks.PackedRanks387To387
open Research6969.TransitionBanks
theorem rank387 (u:ℕ) : P3_7_1.BankOK (bank387 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank387 u).shape (by change 2*3070≤10000;decide) (by change 10000+3070≤13955+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3070) 3070=6*30428373265940480:=by decide
  change 6*P1_7_1.nodeRows (bank387 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank387 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3070) 3070 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank387 u).shape=30428373265940480; omega, moment13955_3070,by change 13955<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks387To387
end Z6969Source0749

-- Source: Research6969.TransitionBankChecks21
section Z6969Source0750
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

theorem rank378 (u : ℕ) : P3_7_1.BankOK (bank378 u) :=
  PackedRanks.PackedRanks378To380.rank378 u
theorem rank379 (u : ℕ) : P3_7_1.BankOK (bank379 u) :=
  PackedRanks.PackedRanks378To380.rank379 u
theorem rank380 (u : ℕ) : P3_7_1.BankOK (bank380 u) :=
  PackedRanks.PackedRanks378To380.rank380 u
theorem rank381 (u : ℕ) : P3_7_1.BankOK (bank381 u) :=
  PackedRanks.PackedRanks381To383.rank381 u
theorem rank382 (u : ℕ) : P3_7_1.BankOK (bank382 u) :=
  PackedRanks.PackedRanks381To383.rank382 u
theorem rank383 (u : ℕ) : P3_7_1.BankOK (bank383 u) :=
  PackedRanks.PackedRanks381To383.rank383 u
theorem rank384 (u : ℕ) : P3_7_1.BankOK (bank384 u) :=
  PackedRanks.PackedRanks384To386.rank384 u
theorem rank385 (u : ℕ) : P3_7_1.BankOK (bank385 u) :=
  PackedRanks.PackedRanks384To386.rank385 u
theorem rank386 (u : ℕ) : P3_7_1.BankOK (bank386 u) :=
  PackedRanks.PackedRanks384To386.rank386 u
theorem rank387 (u : ℕ) : P3_7_1.BankOK (bank387 u) :=
  PackedRanks.PackedRanks387To387.rank387 u
end Research6969.TransitionBanks
end Z6969Source0750

-- Source: Research6969.PhysicalChecks047
section Z6969Source0751
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src416 : Request := ⟨⟨⟨1750,2442,537,45124⟩,163381988556800,989573241440⟩,2,2,1,307237,20⟩
theorem cover416 : PhysicalWindow.Cover (PhysicalWindow.Triangular src416) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src417 : Request := ⟨⟨⟨1750,2442,527,50764⟩,161065121873920,975196209190⟩,3,2,1,307237,20⟩
theorem cover417 : PhysicalWindow.Cover (PhysicalWindow.Triangular src417) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src418 : Request := ⟨⟨⟨2100,2930,632,64247⟩,278060332482560,2019119590628⟩,6,2,1,307237,20⟩
theorem cover418 : PhysicalWindow.Cover (PhysicalWindow.Triangular src418) 2411 2314 [2317, 2329, 2363, 2411] := triangleCover (by decide +kernel)
def src419 : Request := ⟨⟨⟨2600,3628,783,81311⟩,527755772952576,4745819470168⟩,10,2,1,307237,20⟩
theorem cover419 : PhysicalWindow.Cover (PhysicalWindow.Triangular src419) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src420 : Request := ⟨⟨⟨3950,5512,1189,115771⟩,1848744952463360,25255771038451⟩,20,2,1,307237,20⟩
theorem cover420 : PhysicalWindow.Cover (PhysicalWindow.Triangular src420) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src421 : Request := ⟨⟨⟨4800,6698,1445,475797⟩,3317023033262080,55058665830093⟩,40,2,1,307237,20⟩
theorem cover421 : PhysicalWindow.Cover (PhysicalWindow.Triangular src421) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src422 : Request := ⟨⟨⟨6900,9629,2077,185441⟩,9849424459857920,235044796335102⟩,40,2,1,307237,20⟩
theorem cover422 : PhysicalWindow.Cover (PhysicalWindow.Triangular src422) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src423 : Request := ⟨⟨⟨6900,9628,2077,1085143⟩,9849424459857920,234966243278304⟩,65,2,1,307237,20⟩
theorem cover423 : PhysicalWindow.Cover (PhysicalWindow.Triangular src423) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src424 : Request := ⟨⟨⟨10000,13955,3010,297039⟩,29974681586237440,1036603432174989⟩,65,2,1,307237,20⟩
theorem cover424 : PhysicalWindow.Cover (PhysicalWindow.Triangular src424) 2411 2314 [2320, 2339, 2391, 2411] := triangleCover (by decide +kernel)
def src433 : Request := ⟨⟨⟨1450,2023,436,45124⟩,91566841790464,459151377566⟩,0,2,1,307353,19⟩
theorem cover433 : PhysicalWindow.Cover (PhysicalWindow.Triangular src433) 2411 2314 [2317, 2329, 2364, 2411] := triangleCover (by decide +kernel)
def src434 : Request := ⟨⟨⟨1750,2442,527,50764⟩,161065121873920,975196209190⟩,1,2,1,307353,19⟩
theorem cover434 : PhysicalWindow.Cover (PhysicalWindow.Triangular src434) 2411 2314 [2323, 2352, 2411] := triangleCover (by decide +kernel)
def src435 : Request := ⟨⟨⟨2100,2930,632,57109⟩,278060332482560,2019119590628⟩,3,2,1,307353,19⟩
theorem cover435 : PhysicalWindow.Cover (PhysicalWindow.Triangular src435) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src436 : Request := ⟨⟨⟨2100,2930,632,64247⟩,278060332482560,2019119590628⟩,4,2,1,307353,19⟩
theorem cover436 : PhysicalWindow.Cover (PhysicalWindow.Triangular src436) 2411 2314 [2322, 2347, 2411] := triangleCover (by decide +kernel)
def src437 : Request := ⟨⟨⟨2600,3628,783,81311⟩,527755772952576,4745819470168⟩,8,2,1,307353,19⟩
theorem cover437 : PhysicalWindow.Cover (PhysicalWindow.Triangular src437) 2411 2314 [2320, 2340, 2396, 2411] := triangleCover (by decide +kernel)
def src438 : Request := ⟨⟨⟨3200,4465,963,102908⟩,983050615259136,10877088344236⟩,13,2,1,307353,19⟩
theorem cover438 : PhysicalWindow.Cover (PhysicalWindow.Triangular src438) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src439 : Request := ⟨⟨⟨5700,7954,1716,185441⟩,5553838907981824,109473260530676⟩,32,2,1,307353,19⟩
theorem cover439 : PhysicalWindow.Cover (PhysicalWindow.Triangular src439) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0751

-- Source: Research6969.PhysicalChecks048
section Z6969Source0752
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src440 : Request := ⟨⟨⟨6900,9628,2077,1220785⟩,9849424459857920,234966243278304⟩,65,2,1,307353,19⟩
theorem cover440 : PhysicalWindow.Cover (PhysicalWindow.Triangular src440) 2411 2314 [2315, 2321, 2337, 2381, 2411] := triangleCover (by decide +kernel)
def src441 : Request := ⟨⟨⟨8300,11582,2498,422931⟩,17139238515245056,491880571317053⟩,65,2,1,307353,19⟩
theorem cover441 : PhysicalWindow.Cover (PhysicalWindow.Triangular src441) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src442 : Request := ⟨⟨⟨10000,13955,3010,334168⟩,29974681586237440,1036603432174989⟩,65,2,1,307353,19⟩
theorem cover442 : PhysicalWindow.Cover (PhysicalWindow.Triangular src442) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src443 : Request := ⟨⟨⟨1450,2023,436,50764⟩,91566841790464,459151377566⟩,0,2,1,307462,18⟩
theorem cover443 : PhysicalWindow.Cover (PhysicalWindow.Triangular src443) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src444 : Request := ⟨⟨⟨1750,2442,527,57109⟩,161065121873920,975196209190⟩,1,2,1,307462,18⟩
theorem cover444 : PhysicalWindow.Cover (PhysicalWindow.Triangular src444) 2411 2314 [2322, 2348, 2411] := triangleCover (by decide +kernel)
def src445 : Request := ⟨⟨⟨1750,2442,527,64247⟩,161065121873920,975196209190⟩,2,2,1,307462,18⟩
theorem cover445 : PhysicalWindow.Cover (PhysicalWindow.Triangular src445) 2411 2314 [2322, 2347, 2411] := triangleCover (by decide +kernel)
def src446 : Request := ⟨⟨⟨2100,2930,632,64247⟩,278060332482560,2019119590628⟩,3,2,1,307462,18⟩
theorem cover446 : PhysicalWindow.Cover (PhysicalWindow.Triangular src446) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src447 : Request := ⟨⟨⟨1750,2442,527,81311⟩,161065121873920,975196209190⟩,4,2,1,307462,18⟩
theorem cover447 : PhysicalWindow.Cover (PhysicalWindow.Triangular src447) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src448 : Request := ⟨⟨⟨2100,2930,632,72277⟩,278060332482560,2019119590628⟩,4,2,1,307462,18⟩
theorem cover448 : PhysicalWindow.Cover (PhysicalWindow.Triangular src448) 2411 2314 [2320, 2340, 2397, 2411] := triangleCover (by decide +kernel)
def src449 : Request := ⟨⟨⟨2600,3628,783,91474⟩,527755772952576,4745819470168⟩,8,2,1,307462,18⟩
theorem cover449 : PhysicalWindow.Cover (PhysicalWindow.Triangular src449) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
def src450 : Request := ⟨⟨⟨3200,4465,963,102908⟩,983050615259136,10877088344236⟩,10,2,1,307462,18⟩
theorem cover450 : PhysicalWindow.Cover (PhysicalWindow.Triangular src450) 2411 2314 [2323, 2351, 2411] := triangleCover (by decide +kernel)
def src451 : Request := ⟨⟨⟨3200,4465,963,115771⟩,983050615259136,10877088344236⟩,13,2,1,307462,18⟩
theorem cover451 : PhysicalWindow.Cover (PhysicalWindow.Triangular src451) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src452 : Request := ⟨⟨⟨4800,6698,1445,264035⟩,3317023033262080,55058665830093⟩,32,2,1,307462,18⟩
theorem cover452 : PhysicalWindow.Cover (PhysicalWindow.Triangular src452) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src453 : Request := ⟨⟨⟨5700,7954,1716,208621⟩,5553838907981824,109473260530676⟩,32,2,1,307462,18⟩
theorem cover453 : PhysicalWindow.Cover (PhysicalWindow.Triangular src453) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src454 : Request := ⟨⟨⟨1750,2442,527,57109⟩,161065121873920,975196209190⟩,0,2,1,307566,17⟩
theorem cover454 : PhysicalWindow.Cover (PhysicalWindow.Triangular src454) 2411 2314 [2320, 2340, 2398, 2411] := triangleCover (by decide +kernel)
def src455 : Request := ⟨⟨⟨1750,2442,527,64247⟩,161065121873920,975196209190⟩,1,2,1,307566,17⟩
theorem cover455 : PhysicalWindow.Cover (PhysicalWindow.Triangular src455) 2411 2314 [2321, 2344, 2410, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0752

-- Source: Research6969.PrefixRescueDataQuadraticSingletons0
section Z6969Source0753
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons0
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,19⟩
  bank i := ![bank236 45124, bank245 50764, bank252 57109, bank252 64247, bank270 81311, bank303 102908, bank347 185441, bank373 422931, bank386 334168, bank359 1220785, bank386 334168] i
  reserve i := ![0, 1, 3, 4, 8, 13, 32, 65, 65, 65, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307353
  seedFloor := 19

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 45124
    · exact rank245 50764
    · exact rank252 57109
    · exact rank252 64247
    · exact rank270 81311
    · exact rank303 102908
    · exact rank347 185441
    · exact rank373 422931
    · exact rank386 334168
    · exact rank359 1220785
    · exact rank386 334168
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover433⟩
    · exact ⟨_, cover434⟩
    · exact ⟨_, cover435⟩
    · exact ⟨_, cover436⟩
    · exact ⟨_, cover437⟩
    · exact ⟨_, cover438⟩
    · exact ⟨_, cover439⟩
    · exact ⟨_, cover441⟩
    · exact ⟨_, cover442⟩
    · exact ⟨_, cover440⟩
    · exact ⟨_, cover442⟩

def price : EarlyPrice := ⟨2, 19, 10, 85/100, 80/100, ![9029616824310, 531103070366, 22263663660, 1171793000], 11519168003311936⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![11705/66, 17789/3, 933481/66, 3174596/33] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.QuadraticSingletons0
end Z6969Source0753

-- Source: Research6969.PrefixNearSavedQuadraticSingletons0
section Z6969Source0754
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedQuadraticSingletons0
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨336,4851,177,5929,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.QuadraticSingletons0.plan Lower6960.Prefix6969RescueData.QuadraticSingletons0.plan Lower6960.Prefix6969RescueData.QuadraticSingletons0.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 2 19 19 307353 :=
  ⟨Lower6960.Prefix6969MainCases.QuadraticSingletons0.plan, Lower6960.Prefix6969MainCases.QuadraticSingletons0.price, Lower6960.Prefix6969MainCases.QuadraticSingletons0.valid, Lower6960.Prefix6969MainCases.QuadraticSingletons0.priced, Lower6960.Prefix6969MainCases.QuadraticSingletons0.sources,
   Lower6960.Prefix6969RescueData.QuadraticSingletons0.plan, Lower6960.Prefix6969RescueData.QuadraticSingletons0.price, Lower6960.Prefix6969RescueData.QuadraticSingletons0.sources, Lower6960.Prefix6969RescueData.QuadraticSingletons0.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 232190986149640566 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedQuadraticSingletons0
end Z6969Source0754

-- Source: Research6969.PhysicalChecks100
section Z6969Source0755
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1424 : Request := ⟨⟨⟨556,772,170,5081⟩,5255817068544,9968090926⟩,10,4,2,514638,40⟩
theorem cover1424 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1424) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1425 : Request := ⟨⟨⟨556,772,170,5022⟩,5255817068544,9968090926⟩,10,4,2,514638,41⟩
theorem cover1425 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1425) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1426 : Request := ⟨⟨⟨556,772,170,4965⟩,5255817068544,9968090926⟩,10,4,2,514638,42⟩
theorem cover1426 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1426) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1427 : Request := ⟨⟨⟨400,558,123,12355⟩,1971918995456,2734096379⟩,0,5,1,643299,1⟩
theorem cover1427 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1427) 2411 2314 [2328, 2379, 2411] := triangleCover (by decide +kernel)
def src1428 : Request := ⟨⟨⟨470,655,141,13899⟩,3134317133824,5085275599⟩,1,5,1,643299,1⟩
theorem cover1428 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1428) 2411 2314 [2331, 2390, 2411] := triangleCover (by decide +kernel)
def src1429 : Request := ⟨⟨⟨470,655,141,15636⟩,3134317133824,5085275599⟩,2,5,1,643299,1⟩
theorem cover1429 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1429) 2411 2314 [2329, 2382, 2411] := triangleCover (by decide +kernel)
def src1430 : Request := ⟨⟨⟨560,781,169,17590⟩,5316921262080,10299257375⟩,4,5,1,643299,1⟩
theorem cover1430 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1430) 2411 2314 [2328, 2376, 2411] := triangleCover (by decide +kernel)
def src1431 : Request := ⟨⟨⟨690,962,212,22261⟩,10065769922560,23997864317⟩,8,5,1,643299,1⟩
theorem cover1431 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1431) 2411 2314 [2329, 2379, 2411] := triangleCover (by decide +kernel)
def src1432 : Request := ⟨⟨⟨1000,1395,301,28173⟩,30103476895744,104105680031⟩,13,5,1,643299,1⟩
theorem cover1432 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1432) 2411 2314 [2329, 2377, 2411] := triangleCover (by decide +kernel)
def src1433 : Request := ⟨⟨⟨1450,2022,445,40111⟩,92998964346880,465769321795⟩,25,5,1,643299,1⟩
theorem cover1433 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1433) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src1434 : Request := ⟨⟨⟨1450,2022,436,57109⟩,91566841790464,458421718666⟩,32,5,1,643299,1⟩
theorem cover1434 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1434) 2411 2314 [2321, 2345, 2411] := triangleCover (by decide +kernel)
def src1435 : Request := ⟨⟨⟨2100,2929,645,57109⟩,282396798484480,2049139102608⟩,40,5,1,643299,1⟩
theorem cover1435 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1435) 2411 2314 [2321, 2343, 2405, 2411] := triangleCover (by decide +kernel)
def src1438 : Request := ⟨⟨⟨8300,11577,2498,234698⟩,17139238515245056,491197457313663⟩,190,5,1,643299,1⟩
theorem cover1438 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1438) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src1439 : Request := ⟨⟨⟨400,558,120,12355⟩,1935519252480,2682384904⟩,0,5,1,643299,2⟩
theorem cover1439 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1439) 2411 2314 [2320, 2344, 2411] := triangleCover (by decide +kernel)
def src1440 : Request := ⟨⟨⟨400,558,123,13899⟩,1971918995456,2734096379⟩,1,5,1,643299,2⟩
theorem cover1440 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1440) 2411 2314 [2325, 2366, 2411] := triangleCover (by decide +kernel)
def src1441 : Request := ⟨⟨⟨560,781,169,13899⟩,5316921262080,10299257375⟩,2,5,1,643299,2⟩
theorem cover1441 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1441) 2411 2314 [2319, 2338, 2398, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0755

-- Source: Research6969.PrefixMainDataRepricedHelperCases0
section Z6969Source0756
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.RepricedHelperCases0
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 20, 21, 30, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank37 2039, bank44 2409, bank54 2755, bank66 3528, bank91 4262, bank116 3644, bank168 4492, bank130 22726, bank166 6058, bank199 9241, bank181 61748, bank214 10456, bank170 227095] i
  head := src1426
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15985, 158302, 729995, 3200236],
    ![25417/2, 447715/4, 521808, 2411809],
    ![54680/9, 488110/9, 521808, 8455395/4],
    ![29433/8, 525955/16, 2382146/9, 3041890/3],
    ![64334/25, 112121/5, 204050, 3705625/4],
    ![17323/9, 599845/36, 2701163/16, 10123635/16],
    ![18775/16, 682605/64, 3086103/25, 2392137/5],
    ![89110/121, 791075/121, 3586570/49, 303601],
    ![89110/121, 791075/121, 3586570/49, 303601],
    ![258784/441, 2418002/441, 892889/16, 42321660/169],
    ![258784/441, 626361/121, 2707414/49, 9046230/49],
    ![258784/441, 626361/121, 2707414/49, 20178064/121],
    ![33463/82, 626361/121, 2707414/49, 20178064/121],
    ![33463/82, 7793540/1681, 4369073/98, 36699364/225],
    ![33463/82, 5674090/1323, 21050998/529, 275289390/1849],
    ![474397/1369, 5674090/1323, 21050998/529, 275289390/1849],
    ![474397/1369, 5682530/1369, 102276559/2601, 18169914/125],
    ![920087/2738, 5682530/1369, 102276559/2601, 18169914/125]]

theorem valid : plan.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 41 385979 := by
  refine ⟨?_, rank154 4965, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1426⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free66_0
    · exact free91_0
    · exact free116_1
    · exact free168_0
    · exact free130_0
    · exact free166_0
    · exact free199_0
    · exact free181_0
    · exact free214_0
    · exact free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [298762479, 298625235, 297473215, 297733845, 298237450, 297990051, 297138544, 149124934, 149346789, 149369215, 99363361, 65001395, 66834179, 76861113, 90626280, 89326314, 142979734, 227399835], [1196919, 1197621, 1203516, 1202182, 1199605, 1200871, 1205228, 2581996, 2578307, 2577934, 3982399, 6185526, 6012761, 5203819, 4384716, 4450283, 2705206, 1634372],
  ![120708380414700, 1614147307980, 204659851500, 5306725440], 159930111880785159⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,7,7,7,11,17,16,14,12,12,8,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 5682530/1369, 102276559/2601, 18169914/125] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.RepricedHelperCases0
end Z6969Source0756

-- Source: Research6969.PhysicalChecks085
section Z6969Source0757
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1109 : Request := ⟨⟨⟨10000,13948,3150,102908⟩,31027650042265600,1072221490229155⟩,245,3,1,385979,39⟩
theorem cover1109 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1109) 2411 2314 [2323, 2350, 2411] := triangleCover (by decide +kernel)
def src1110 : Request := ⟨⟨⟨400,558,123,4282⟩,1971918995456,2734096379⟩,0,3,1,385979,40⟩
theorem cover1110 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1110) 2411 2314 [2337, 2411] := triangleCover (by decide +kernel)
def src1111 : Request := ⟨⟨⟨470,655,148,4282⟩,3250957582336,5279398867⟩,1,3,1,385979,40⟩
theorem cover1111 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1111) 2411 2314 [2325, 2364, 2411] := triangleCover (by decide +kernel)
def src1112 : Request := ⟨⟨⟨470,655,148,4817⟩,3250957582336,5279398867⟩,2,3,1,385979,40⟩
theorem cover1112 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1112) 2411 2314 [2325, 2364, 2411] := triangleCover (by decide +kernel)
def src1113 : Request := ⟨⟨⟨560,781,169,5419⟩,5316921262080,10299257375⟩,3,3,1,385979,40⟩
theorem cover1113 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1113) 2411 2314 [2326, 2367, 2411] := triangleCover (by decide +kernel)
def src1114 : Request := ⟨⟨⟨560,781,176,5419⟩,5482316038144,10627925923⟩,4,3,1,385979,40⟩
theorem cover1114 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1114) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1115 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,8,3,1,385979,40⟩
theorem cover1115 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1115) 2411 2314 [2333, 2395, 2411] := triangleCover (by decide +kernel)
def src1116 : Request := ⟨⟨⟨825,1151,253,10983⟩,17161575202816,49010625289⟩,13,3,1,385979,40⟩
theorem cover1116 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1116) 2411 2314 [2321, 2345, 2411] := triangleCover (by decide +kernel)
def src1117 : Request := ⟨⟨⟨1200,1674,368,12355⟩,52718727069696,218807905514⟩,20,3,1,385979,40⟩
theorem cover1117 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1117) 2411 2314 [2334, 2396, 2411] := triangleCover (by decide +kernel)
def src1118 : Request := ⟨⟨⟨1750,2441,551,22261⟩,166595992223744,1008217465165⟩,40,3,1,385979,40⟩
theorem cover1118 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1118) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src1121 : Request := ⟨⟨⟨5700,7950,1750,64247⟩,5637370734182400,110980791054694⟩,145,3,1,385979,40⟩
theorem cover1121 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1121) 2411 2314 [2321, 2343, 2404, 2411] := triangleCover (by decide +kernel)
def src1122 : Request := ⟨⟨⟨6900,9623,2174,91474⟩,10196763128627200,243058712908678⟩,190,3,1,385979,40⟩
theorem cover1122 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1122) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src1123 : Request := ⟨⟨⟨400,558,126,3807⟩,2007957766144,2785382344⟩,0,3,1,385979,41⟩
theorem cover1123 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1123) 2411 2314 [2323, 2357, 2411] := triangleCover (by decide +kernel)
def src1124 : Request := ⟨⟨⟨470,655,144,4282⟩,3184589537280,5168862572⟩,1,3,1,385979,41⟩
theorem cover1124 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1124) 2411 2314 [2335, 2407, 2411] := triangleCover (by decide +kernel)
def src1125 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,2,3,1,385979,41⟩
theorem cover1125 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1125) 2411 2314 [2337, 2411] := triangleCover (by decide +kernel)
def src1126 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,3,3,1,385979,41⟩
theorem cover1126 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1126) 2411 2314 [2323, 2355, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0757

-- Source: Research6969.PhysicalChecks086
section Z6969Source0758
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1127 : Request := ⟨⟨⟨560,781,172,5419⟩,5388141854720,10440670587⟩,4,3,1,385979,41⟩
theorem cover1127 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1127) 2411 2314 [2329, 2380, 2411] := triangleCover (by decide +kernel)
def src1128 : Request := ⟨⟨⟨560,781,176,6858⟩,5482316038144,10627925923⟩,6,3,1,385979,41⟩
theorem cover1128 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1128) 2411 2314 [2320, 2342, 2411] := triangleCover (by decide +kernel)
def src1129 : Request := ⟨⟨⟨690,962,217,8679⟩,10244384358400,24434817260⟩,10,3,1,385979,41⟩
theorem cover1129 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1129) 2411 2314 [2318, 2334, 2383, 2411] := triangleCover (by decide +kernel)
def src1130 : Request := ⟨⟨⟨1000,1395,307,9763⟩,30557599170560,105715278267⟩,16,3,1,385979,41⟩
theorem cover1130 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1130) 2411 2314 [2317, 2329, 2365, 2411] := triangleCover (by decide +kernel)
def src1131 : Request := ⟨⟨⟨1450,2022,457,17590⟩,94890063298560,475487789910⟩,32,3,1,385979,41⟩
theorem cover1131 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1131) 2411 2314 [2321, 2344, 2410, 2411] := triangleCover (by decide +kernel)
def src1134 : Request := ⟨⟨⟨2600,3626,798,31694⟩,535425056505856,4807957255301⟩,65,3,1,385979,41⟩
theorem cover1134 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1134) 2411 2314 [2319, 2336, 2384, 2411] := triangleCover (by decide +kernel)
def src1135 : Request := ⟨⟨⟨6900,9623,2174,81311⟩,10196763128627200,243058712908678⟩,190,3,1,385979,41⟩
theorem cover1135 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1135) 2411 2314 [2321, 2343, 2404, 2411] := triangleCover (by decide +kernel)
def src1164 : Request := ⟨⟨⟨556,772,170,4563⟩,5255817068544,9968090926⟩,10,3,2,421606,52⟩
theorem cover1164 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1164) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1165 : Request := ⟨⟨⟨556,772,170,5104⟩,5255817068544,9968090926⟩,10,3,2,424744,42⟩
theorem cover1165 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1165) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1166 : Request := ⟨⟨⟨556,772,170,5157⟩,5255817068544,9968090926⟩,10,3,2,432343,41⟩
theorem cover1166 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1166) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1167 : Request := ⟨⟨⟨556,772,170,5222⟩,5255817068544,9968090926⟩,10,3,2,432577,40⟩
theorem cover1167 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1167) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1168 : Request := ⟨⟨⟨556,772,170,5289⟩,5255817068544,9968090926⟩,10,3,2,432805,39⟩
theorem cover1168 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1168) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1169 : Request := ⟨⟨⟨556,772,170,5358⟩,5255817068544,9968090926⟩,10,3,2,433027,38⟩
theorem cover1169 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1169) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1170 : Request := ⟨⟨⟨556,772,170,5428⟩,5255817068544,9968090926⟩,10,3,2,433244,37⟩
theorem cover1170 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1170) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1171 : Request := ⟨⟨⟨556,772,170,5500⟩,5255817068544,9968090926⟩,10,3,2,433454,36⟩
theorem cover1171 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1171) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1172 : Request := ⟨⟨⟨556,772,170,5573⟩,5255817068544,9968090926⟩,10,3,2,433658,35⟩
theorem cover1172 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1172) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0758

-- Source: Research6969.PrefixRescueDataRepricedHelperCases0
section Z6969Source0759
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.RepricedHelperCases0
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,56⟩
  bank i := ![bank135 3807, bank142 4282, bank142 4817, bank142 5419, bank156 5419, bank157 6858, bank194 8679, bank222 9763, bank234 17590, bank264 31694, bank352 81311] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 16, 32, 65, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 41

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank135 3807
    · exact rank142 4282
    · exact rank142 4817
    · exact rank142 5419
    · exact rank156 5419
    · exact rank157 6858
    · exact rank194 8679
    · exact rank222 9763
    · exact rank234 17590
    · exact rank264 31694
    · exact rank352 81311
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1123⟩
    · exact ⟨_, cover1124⟩
    · exact ⟨_, cover1125⟩
    · exact ⟨_, cover1126⟩
    · exact ⟨_, cover1127⟩
    · exact ⟨_, cover1128⟩
    · exact ⟨_, cover1129⟩
    · exact ⟨_, cover1130⟩
    · exact ⟨_, cover1131⟩
    · exact ⟨_, cover1134⟩
    · exact ⟨_, cover1135⟩

def price : EarlyPrice := ⟨3, 56, 10, 60/100, 60/100, ![1772612161778, 225699340125, 47394065252, 1692661182], 1218730489785608⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![13971/191, 203055/191, 782821/191, 4553416/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.RepricedHelperCases0
end Z6969Source0759

-- Source: Research6969.PrefixNearSavedRepricedHelperCases0
section Z6969Source0760
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedRepricedHelperCases0
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨336,4150,73,1063,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.RepricedHelperCases0.plan Lower6960.Prefix6969RescueData.RepricedHelperCases0.plan Lower6960.Prefix6969RescueData.RepricedHelperCases0.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 41 56 385979 :=
  ⟨Lower6960.Prefix6969MainCases.RepricedHelperCases0.plan, Lower6960.Prefix6969MainCases.RepricedHelperCases0.price, Lower6960.Prefix6969MainCases.RepricedHelperCases0.valid, Lower6960.Prefix6969MainCases.RepricedHelperCases0.priced, Lower6960.Prefix6969MainCases.RepricedHelperCases0.sources,
   Lower6960.Prefix6969RescueData.RepricedHelperCases0.plan, Lower6960.Prefix6969RescueData.RepricedHelperCases0.price, Lower6960.Prefix6969RescueData.RepricedHelperCases0.sources, Lower6960.Prefix6969RescueData.RepricedHelperCases0.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 231590448761160043 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedRepricedHelperCases0
end Z6969Source0760

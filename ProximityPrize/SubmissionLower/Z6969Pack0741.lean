import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0740
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0739
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0741
section Merged_Z6969Pack0741

-- Source: Research6969.PrefixRescueDataMiddle36
section Z6969Source1940
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle36
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,11⟩
  bank i := ![bank221 17633, bank221 18592, bank221 19665, bank227 23146, bank245 33255, bank270 45711, bank315 65626, bank332 86194, bank382 195671, bank342 152669, bank355 196129] i
  reserve i := ![0, 1, 2, 4, 10, 16, 25, 40, 110, 85, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 11

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 17633
    · exact rank221 18592
    · exact rank221 19665
    · exact rank227 23146
    · exact rank245 33255
    · exact rank270 45711
    · exact rank315 65626
    · exact rank332 86194
    · exact rank382 195671
    · exact rank342 152669
    · exact rank355 196129
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2409⟩
    · exact ⟨_, cover2410⟩
    · exact ⟨_, cover2411⟩
    · exact ⟨_, cover2412⟩
    · exact ⟨_, cover2413⟩
    · exact ⟨_, cover2414⟩
    · exact ⟨_, cover2415⟩
    · exact ⟨_, cover2416⟩
    · exact ⟨_, cover2419⟩
    · exact ⟨_, cover2417⟩
    · exact ⟨_, cover2418⟩

def price : EarlyPrice := ⟨3, 11, 10, 95/100, 80/100, ![840780899133, 199424903580, 12903499770, 2346111390], 2163126560119784⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![13780/111, 72992/37, 694273/111, 2152381/111] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle36
end Z6969Source1940

-- Source: Research6969.PrefixMiddleSaved36
section Z6969Source1941
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved36
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle36.price Lower6960.Prefix6969RescueData.Middle36.price :=
  ⟨335, 3970, 124, 1972, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle36.plan Lower6960.Prefix6969RescueData.Middle36.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 11 11 :=
  ⟨Lower6960.Prefix6969MainCases.Middle36.plan, Lower6960.Prefix6969MainCases.Middle36.price, Lower6960.Prefix6969MainCases.Middle36.valid, Lower6960.Prefix6969MainCases.Middle36.priced, Lower6960.Prefix6969MainCases.Middle36.sources,
   Lower6960.Prefix6969RescueData.Middle36.plan, Lower6960.Prefix6969RescueData.Middle36.price, Lower6960.Prefix6969RescueData.Middle36.sources, Lower6960.Prefix6969RescueData.Middle36.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved36
end Z6969Source1941

-- Source: Research6969.PrefixMainDataMiddle37
section Z6969Source1942
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle37
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank61 2044, bank84 3942, bank85 2394, bank74 4330, bank113 3080, bank140 3403, bank150 5281, bank120 12477, bank198 7884, bank212 8810, bank183 20877, bank174 26788, bank169 29097] i
  head := src2934
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 126808, 589299, 2260854],
    ![12303, 101231, 457657, 1674035],
    ![53398/9, 440056/9, 457657, 1674035],
    ![29433/8, 238321/8, 2157484/9, 863304],
    ![16211/9, 136552/9, 1244543/8, 4656861/8],
    ![24292/27, 219884/27, 499559/6, 5962885/18],
    ![73478/121, 785376/121, 3543158/49, 8191044/25],
    ![73478/121, 785376/121, 3543158/49, 2670155/9],
    ![73478/121, 740394/121, 474454/7, 1615928/7],
    ![63754/121, 15668/3, 770661/16, 10907514/49],
    ![63754/121, 15668/3, 770661/16, 10907514/49],
    ![61324/121, 15668/3, 770661/16, 10907514/49],
    ![61324/121, 600338/121, 770661/16, 6817888/45],
    ![61324/121, 600338/121, 770661/16, 6817888/45],
    ![61324/121, 7332064/1681, 3987155/98, 27888961/196],
    ![667406/1681, 7332064/1681, 3987155/98, 27888961/196],
    ![667406/1681, 5359016/1323, 24115268/675, 3231856/25],
    ![667406/1681, 10800853/2738, 24115268/675, 3104644/25],
    ![954471/2738, 10800853/2738, 24115268/675, 3104644/25],
    ![462882/1369, 10800853/2738, 24115268/675, 3104644/25],
    ![459151/1369, 10800853/2738, 24115268/675, 3104644/25]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 12 385541 := by
  refine ⟨?_, rank154 5534, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2934⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free32_1
    · exact free41_1
    · exact free42_6
    · exact free48_1
    · exact free61_1
    · exact free84_1
    · exact free85_1
    · exact free74_5
    · exact free113_1
    · exact free140_1
    · exact free150_1
    · exact free120_1
    · exact free198_1
    · exact free212_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [257027878, 337203915, 336343554, 336973518, 337035968, 336473837, 336963882, 336056069, 167518851, 167678598, 167724165, 167978182, 65013774, 84196654, 65784139, 77178426, 102452891, 102308034, 125053890, 100000000, 223140933], [1412014, 1023675, 1026036, 1024307, 1024136, 1025678, 1024333, 1026825, 2278596, 2275936, 2275178, 2270949, 6191021, 4739004, 6114620, 5187567, 3856190, 3862311, 3126333, 3959851, 1671222],
  ![118447670055060, 1619710643592, 200826839700, 5290113720], 141486051551084250⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,3,7,7,7,7,17,13,16,14,11,11,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 10800853/2738, 24115268/675, 3104644/25] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle37
end Z6969Source1942

-- Source: Research6969.PrefixRescueDataMiddle37
section Z6969Source1943
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle37
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,12⟩
  bank i := ![bank220 17294, bank227 19165, bank227 19978, bank227 21839, bank236 27561, bank252 34079, bank270 43170, bank316 66909, bank359 119770, bank342 143704, bank384 161803] i
  reserve i := ![0, 1, 2, 4, 8, 10, 16, 32, 65, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 12

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank220 17294
    · exact rank227 19165
    · exact rank227 19978
    · exact rank227 21839
    · exact rank236 27561
    · exact rank252 34079
    · exact rank270 43170
    · exact rank316 66909
    · exact rank359 119770
    · exact rank342 143704
    · exact rank384 161803
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2420⟩
    · exact ⟨_, cover2421⟩
    · exact ⟨_, cover2422⟩
    · exact ⟨_, cover2423⟩
    · exact ⟨_, cover2424⟩
    · exact ⟨_, cover2425⟩
    · exact ⟨_, cover2426⟩
    · exact ⟨_, cover2427⟩
    · exact ⟨_, cover2428⟩
    · exact ⟨_, cover2429⟩
    · exact ⟨_, cover2430⟩

def price : EarlyPrice := ⟨3, 12, 10, 90/100, 80/100, ![756686777179, 177296202309, 14076544930, 2346111390], 2032152356551428⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5692/43, 82148/43, 263268/43, 862224/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle37
end Z6969Source1943

-- Source: Research6969.PrefixMiddleSaved37
section Z6969Source1944
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved37
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle37.price Lower6960.Prefix6969RescueData.Middle37.price :=
  ⟨335, 3944, 132, 1910, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle37.plan Lower6960.Prefix6969RescueData.Middle37.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 12 12 :=
  ⟨Lower6960.Prefix6969MainCases.Middle37.plan, Lower6960.Prefix6969MainCases.Middle37.price, Lower6960.Prefix6969MainCases.Middle37.valid, Lower6960.Prefix6969MainCases.Middle37.priced, Lower6960.Prefix6969MainCases.Middle37.sources,
   Lower6960.Prefix6969RescueData.Middle37.plan, Lower6960.Prefix6969RescueData.Middle37.price, Lower6960.Prefix6969RescueData.Middle37.sources, Lower6960.Prefix6969RescueData.Middle37.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved37
end Z6969Source1944

-- Source: Research6969.PrefixMainDataMiddle38
section Z6969Source1945
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle38
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank61 2044, bank84 3942, bank85 2394, bank74 4330, bank113 3080, bank140 3403, bank150 5281, bank120 12477, bank198 7884, bank212 8810, bank183 20877, bank174 26788, bank169 29097] i
  head := src2935
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 126607, 588227, 2252479],
    ![12303, 100628, 909887/2, 3307535/2],
    ![53398/9, 437443/9, 909887/2, 3307535/2],
    ![29433/8, 473761/16, 2144486/9, 852852],
    ![16211/9, 543059/36, 2474681/16, 9200961/16],
    ![24292/27, 656101/81, 2981207/36, 11781385/36],
    ![73478/121, 781758/121, 3527011/49, 11781385/36],
    ![73478/121, 781758/121, 3527011/49, 5275655/18],
    ![73478/121, 735637/121, 471439/7, 228052],
    ![63754/121, 763846/147, 770661/16, 1539351/7],
    ![63754/121, 763846/147, 770661/16, 1539351/7],
    ![61324/121, 763846/147, 770661/16, 1539351/7],
    ![61324/121, 54229/11, 770661/16, 6735344/45],
    ![61324/121, 54229/11, 770661/16, 6735344/45],
    ![61324/121, 7286772/1681, 3987155/98, 27888961/196],
    ![667406/1681, 7286772/1681, 3987155/98, 27888961/196],
    ![667406/1681, 5326588/1323, 23970682/675, 15539364/121],
    ![667406/1681, 21467103/5476, 23970682/675, 3104644/25],
    ![954471/2738, 21467103/5476, 23970682/675, 3104644/25],
    ![462882/1369, 21467103/5476, 23970682/675, 3104644/25],
    ![459151/1369, 21467103/5476, 23970682/675, 3104644/25]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 13 385541 := by
  refine ⟨?_, rank154 5467, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2935⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free32_1
    · exact free41_1
    · exact free42_6
    · exact free48_1
    · exact free61_1
    · exact free84_1
    · exact free85_1
    · exact free74_5
    · exact free113_1
    · exact free140_1
    · exact free150_1
    · exact free120_1
    · exact free198_1
    · exact free212_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [255749920, 334985949, 334873450, 335233376, 334204762, 335120347, 335028610, 334363921, 167871179, 167963321, 168198603, 168319668, 81915988, 83851345, 64285646, 88667432, 102667053, 102888670, 124914750, 100000000, 222867429], [1418560, 1029761, 1030070, 1029082, 1031905, 1029392, 1029644, 1031468, 2272730, 2271196, 2267279, 2265264, 4874607, 4759535, 6265751, 4488420, 3847139, 3837773, 3130228, 3959851, 1673473],
  ![118302488661780, 1620007332276, 200580686100, 4711149310], 140428195236880086⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,3,7,7,7,7,13,13,17,12,11,11,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 21467103/5476, 23970682/675, 3104644/25] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle38
end Z6969Source1945

-- Source: Research6969.PhysicalChecks152
section Z6969Source1946
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2432 : Request := ⟨⟨⟨1000,1395,301,16526⟩,30103476895744,104105680031⟩,1,3,1,385541,13⟩
theorem cover2432 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2432) 2557 2412 [2414, 2423, 2447, 2514, 2557] := triangleCover (by decide +kernel)
def src2433 : Request := ⟨⟨⟨1200,1674,368,18552⟩,52718727069696,218807905514⟩,2,3,1,385541,13⟩
theorem cover2433 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2433) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2434 : Request := ⟨⟨⟨1200,1674,361,19657⟩,51955677528064,215563369662⟩,3,3,1,385541,13⟩
theorem cover2434 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2434) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2435 : Request := ⟨⟨⟨1450,2023,436,24026⟩,91566841790464,459151377566⟩,6,3,1,385541,13⟩
theorem cover2435 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2435) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2436 : Request := ⟨⟨⟨1750,2442,527,29554⟩,161065121873920,975196209190⟩,10,3,1,385541,13⟩
theorem cover2436 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2436) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2437 : Request := ⟨⟨⟨2600,3628,783,44114⟩,527755772952576,4745819470168⟩,20,3,1,385541,13⟩
theorem cover2437 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2437) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2438 : Request := ⟨⟨⟨3200,4465,963,59521⟩,983050615259136,10877088344236⟩,32,3,1,385541,13⟩
theorem cover2438 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2438) 2557 2412 [2413, 2418, 2431, 2466, 2557] := triangleCover (by decide +kernel)
def src2439 : Request := ⟨⟨⟨4800,6698,1445,76718⟩,3317023033262080,55058665830093⟩,40,3,1,385541,13⟩
theorem cover2439 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2439) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2440 : Request := ⟨⟨⟨5700,7952,1716,134896⟩,5553838907981824,109384694947514⟩,85,3,1,385541,13⟩
theorem cover2440 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2440) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2441 : Request := ⟨⟨⟨10000,13953,3010,173865⟩,29974681586237440,1036125345444439⟩,110,3,1,385541,13⟩
theorem cover2441 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2441) 2557 2412 [2413, 2418, 2431, 2464, 2550, 2557] := triangleCover (by decide +kernel)
def src2442 : Request := ⟨⟨⟨1000,1395,301,14762⟩,30103476895744,104105680031⟩,0,3,1,385541,14⟩
theorem cover2442 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2442) 2557 2412 [2414, 2423, 2447, 2514, 2557] := triangleCover (by decide +kernel)
def src2443 : Request := ⟨⟨⟨1000,1395,301,15535⟩,30103476895744,104105680031⟩,1,3,1,385541,14⟩
theorem cover2443 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2443) 2557 2412 [2414, 2423, 2447, 2514, 2557] := triangleCover (by decide +kernel)
def src2444 : Request := ⟨⟨⟨1450,2023,445,19992⟩,92998964346880,466511127281⟩,3,3,1,385541,14⟩
theorem cover2444 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2444) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2445 : Request := ⟨⟨⟨1450,2023,445,22168⟩,92998964346880,466511127281⟩,6,3,1,385541,14⟩
theorem cover2445 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2445) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2446 : Request := ⟨⟨⟨1750,2442,527,27780⟩,161065121873920,975196209190⟩,10,3,1,385541,14⟩
theorem cover2446 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2446) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2447 : Request := ⟨⟨⟨2100,2930,632,32500⟩,278060332482560,2019119590628⟩,13,3,1,385541,14⟩
theorem cover2447 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2447) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1946

-- Source: Research6969.PrefixRescueDataMiddle38
section Z6969Source1947
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle38
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,13⟩
  bank i := ![bank221 15691, bank221 16526, bank228 18552, bank227 19657, bank236 24026, bank245 29554, bank270 44114, bank303 59521, bank332 76718, bank342 134896, bank382 173865] i
  reserve i := ![0, 1, 2, 3, 6, 10, 20, 32, 40, 85, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 13

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 15691
    · exact rank221 16526
    · exact rank228 18552
    · exact rank227 19657
    · exact rank236 24026
    · exact rank245 29554
    · exact rank270 44114
    · exact rank303 59521
    · exact rank332 76718
    · exact rank342 134896
    · exact rank382 173865
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2431⟩
    · exact ⟨_, cover2432⟩
    · exact ⟨_, cover2433⟩
    · exact ⟨_, cover2434⟩
    · exact ⟨_, cover2435⟩
    · exact ⟨_, cover2436⟩
    · exact ⟨_, cover2437⟩
    · exact ⟨_, cover2438⟩
    · exact ⟨_, cover2439⟩
    · exact ⟨_, cover2440⟩
    · exact ⟨_, cover2441⟩

def price : EarlyPrice := ⟨3, 13, 10, 90/100, 80/100, ![880853640420, 190957770179, 15249587080, 2346111390], 1907647367010481⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5692/43, 78602/43, 254032/43, 753415/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle38
end Z6969Source1947

-- Source: Research6969.PrefixMiddleSaved38
section Z6969Source1948
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved38
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle38.price Lower6960.Prefix6969RescueData.Middle38.price :=
  ⟨335, 3920, 132, 1827, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle38.plan Lower6960.Prefix6969RescueData.Middle38.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 13 13 :=
  ⟨Lower6960.Prefix6969MainCases.Middle38.plan, Lower6960.Prefix6969MainCases.Middle38.price, Lower6960.Prefix6969MainCases.Middle38.valid, Lower6960.Prefix6969MainCases.Middle38.priced, Lower6960.Prefix6969MainCases.Middle38.sources,
   Lower6960.Prefix6969RescueData.Middle38.plan, Lower6960.Prefix6969RescueData.Middle38.price, Lower6960.Prefix6969RescueData.Middle38.sources, Lower6960.Prefix6969RescueData.Middle38.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved38
end Z6969Source1948

-- Source: Research6969.PrefixMainDataMiddle39
section Z6969Source1949
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle39
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 13, 21, 18, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank58 2054, bank73 3927, bank74 2309, bank74 4330, bank104 2782, bank137 3019, bank150 5281, bank121 11999, bank199 7608, bank212 8810, bank183 20877, bank174 26788, bank169 29097] i
  head := src2936
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14513, 126459, 587427, 2253451],
    ![12303, 100025, 452230, 1633500],
    ![53398/9, 434830/9, 452230, 1633500],
    ![29433/8, 29430, 236832, 842400],
    ![16211/9, 29995/2, 615069/4, 1136025/2],
    ![24292/27, 652550/81, 741265/9, 323250],
    ![73478/121, 70740/11, 501552/7, 323250],
    ![73478/121, 70740/11, 501552/7, 289500],
    ![73478/121, 727180/121, 3270488/49, 11091600/49],
    ![77324/147, 767422/147, 2522922/49, 11091600/49],
    ![77324/147, 767422/147, 2522922/49, 11091600/49],
    ![61324/121, 767422/147, 807545/16, 11091600/49],
    ![61324/121, 767422/147, 807545/16, 2311200/13],
    ![61324/121, 614291/121, 807545/16, 144912],
    ![61324/121, 7241480/1681, 3987155/98, 27888961/196],
    ![671521/1681, 7241480/1681, 3987155/98, 27888961/196],
    ![671521/1681, 254320/63, 4332756/121, 121728],
    ![671521/1681, 5333125/1369, 5987765/169, 121728],
    ![954471/2738, 5333125/1369, 5987765/169, 121728],
    ![462882/1369, 5333125/1369, 5987765/169, 121728],
    ![459151/1369, 5333125/1369, 5987765/169, 121728]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 14 385541 := by
  refine ⟨?_, rank154 5400, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2936⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free32_1
    · exact free41_1
    · exact free42_6
    · exact free48_1
    · exact free58_1
    · exact free73_1
    · exact free74_3
    · exact free74_5
    · exact free104_1
    · exact free137_1
    · exact free150_1
    · exact free121_1
    · exact free199_1
    · exact free212_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [254361108, 332446591, 332653851, 333049493, 332388965, 333022292, 332623312, 332462737, 166874970, 167096211, 166965312, 166883337, 167120801, 69505862, 71417432, 89225427, 102844604, 102884774, 124777155, 100000000, 222713304], [1425674, 1036730, 1036161, 1035075, 1036888, 1035150, 1036245, 1036685, 2289315, 2285632, 2287811, 2289176, 2285222, 5776905, 5620835, 4460245, 3839636, 3837938, 3134079, 3959851, 1674742],
  ![118220676029280, 1620174796356, 200441973600, 4711149310], 139394924927282507⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,3,7,7,7,7,7,16,15,12,11,11,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5333125/1369, 5987765/169, 121728] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle39
end Z6969Source1949

-- Source: Research6969.PhysicalChecks153
section Z6969Source1950
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2448 : Request := ⟨⟨⟨2100,2930,632,39443⟩,278060332482560,2019119590628⟩,20,3,1,385541,14⟩
theorem cover2448 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2448) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2449 : Request := ⟨⟨⟨3200,4465,963,45754⟩,983050615259136,10877088344236⟩,20,3,1,385541,14⟩
theorem cover2449 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2449) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2450 : Request := ⟨⟨⟨5700,7953,1716,86116⟩,5553838907981824,109428971647179⟩,50,3,1,385541,14⟩
theorem cover2450 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2450) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2451 : Request := ⟨⟨⟨5700,7952,1716,126274⟩,5553838907981824,109384694947514⟩,85,3,1,385541,14⟩
theorem cover2451 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2451) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2452 : Request := ⟨⟨⟨8300,11581,2498,131625⟩,17139238515245056,491743896877039⟩,85,3,1,385541,14⟩
theorem cover2452 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2452) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2453 : Request := ⟨⟨⟨1000,1395,296,14495⟩,29722184515584,102755930405⟩,0,3,1,385541,15⟩
theorem cover2453 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2453) 2557 2412 [2415, 2426, 2456, 2540, 2557] := triangleCover (by decide +kernel)
def src2454 : Request := ⟨⟨⟨1200,1674,368,15667⟩,52718727069696,218807905514⟩,1,3,1,385541,15⟩
theorem cover2454 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2454) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2455 : Request := ⟨⟨⟨1200,1674,361,16647⟩,51955677528064,215563369662⟩,2,3,1,385541,15⟩
theorem cover2455 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2455) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2456 : Request := ⟨⟨⟨1200,1674,361,18127⟩,51955677528064,215563369662⟩,4,3,1,385541,15⟩
theorem cover2456 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2456) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2457 : Request := ⟨⟨⟨1450,2023,445,22351⟩,92998964346880,466511127281⟩,8,3,1,385541,15⟩
theorem cover2457 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2457) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2458 : Request := ⟨⟨⟨2100,2930,632,28440⟩,278060332482560,2019119590628⟩,10,3,1,385541,15⟩
theorem cover2458 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2458) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2459 : Request := ⟨⟨⟨2100,2930,632,32940⟩,278060332482560,2019119590628⟩,16,3,1,385541,15⟩
theorem cover2459 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2459) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2460 : Request := ⟨⟨⟨3200,4465,963,46443⟩,983050615259136,10877088344236⟩,25,3,1,385541,15⟩
theorem cover2460 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2460) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2461 : Request := ⟨⟨⟨4800,6697,1445,75627⟩,3317023033262080,55032215749682⟩,50,3,1,385541,15⟩
theorem cover2461 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2461) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2462 : Request := ⟨⟨⟨5700,7952,1716,117871⟩,5553838907981824,109384694947514⟩,85,3,1,385541,15⟩
theorem cover2462 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2462) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2463 : Request := ⟨⟨⟨10000,13954,3070,132019⟩,30428373265940480,1052440252760428⟩,85,3,1,385541,15⟩
theorem cover2463 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2463) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1950

-- Source: Research6969.PrefixRescueDataMiddle39
section Z6969Source1951
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle39
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,14⟩
  bank i := ![bank221 14762, bank221 15535, bank237 19992, bank237 22168, bank245 27780, bank252 32500, bank303 45754, bank252 39443, bank345 86116, bank342 126274, bank371 131625] i
  reserve i := ![0, 1, 3, 6, 10, 13, 20, 20, 50, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 14

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 14762
    · exact rank221 15535
    · exact rank237 19992
    · exact rank237 22168
    · exact rank245 27780
    · exact rank252 32500
    · exact rank303 45754
    · exact rank252 39443
    · exact rank345 86116
    · exact rank342 126274
    · exact rank371 131625
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2442⟩
    · exact ⟨_, cover2443⟩
    · exact ⟨_, cover2444⟩
    · exact ⟨_, cover2445⟩
    · exact ⟨_, cover2446⟩
    · exact ⟨_, cover2447⟩
    · exact ⟨_, cover2449⟩
    · exact ⟨_, cover2448⟩
    · exact ⟨_, cover2450⟩
    · exact ⟨_, cover2451⟩
    · exact ⟨_, cover2452⟩

def price : EarlyPrice := ⟨3, 14, 10, 90/100, 80/100, ![718149159000, 152150724367, 13629147952, 1947038622], 1781173166106520⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5692/43, 75149/43, 245075/43, 883918/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle39
end Z6969Source1951

end Merged_Z6969Pack0741

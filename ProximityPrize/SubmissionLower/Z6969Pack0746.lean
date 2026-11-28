import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0745
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0744
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0746
section Merged_Z6969Pack0746

-- Source: Research6969.PrefixMiddleSaved52
section Z6969Source2000
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved52
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle52.price Lower6960.Prefix6969RescueData.Middle52.price :=
  ⟨335, 3607, 114, 982, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle52.plan Lower6960.Prefix6969RescueData.Middle52.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 27 27 :=
  ⟨Lower6960.Prefix6969MainCases.Middle52.plan, Lower6960.Prefix6969MainCases.Middle52.price, Lower6960.Prefix6969MainCases.Middle52.valid, Lower6960.Prefix6969MainCases.Middle52.priced, Lower6960.Prefix6969MainCases.Middle52.sources,
   Lower6960.Prefix6969RescueData.Middle52.plan, Lower6960.Prefix6969RescueData.Middle52.price, Lower6960.Prefix6969RescueData.Middle52.sources, Lower6960.Prefix6969RescueData.Middle52.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved52
end Z6969Source2000

-- Source: Research6969.PrefixMainDataMiddle53
section Z6969Source2001
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle53
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 20, 25, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank31 1491, bank37 1587, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank109 2996, bank140 3403, bank129 10859, bank161 5142, bank212 8810, bank186 19684, bank174 26788, bank169 29097] i
  head := src2950
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15525, 123949, 573982, 1991552],
    ![25417/2, 184915/2, 419839, 1399489],
    ![54680/9, 402550/9, 419839, 1399489],
    ![29433/8, 54345/2, 656176/3, 711360],
    ![64334/25, 93558/5, 158046, 2223081/4],
    ![17323/9, 83725/6, 565071/4, 452295],
    ![18775/16, 17655/2, 304304/3, 1685376/5],
    ![89110/121, 661730/121, 428524/7, 1399920/7],
    ![89110/121, 661730/121, 116003/2, 1399920/7],
    ![63754/121, 237080/49, 770661/16, 191844],
    ![63754/121, 2012720/441, 2259976/49, 561001/4],
    ![63754/121, 2012720/441, 2259976/49, 561001/4],
    ![33263/82, 2012720/441, 2259976/49, 561001/4],
    ![33263/82, 6725040/1681, 1889586/49, 5861880/49],
    ![33263/82, 4911235/1369, 5616375/169, 93738400/867],
    ![481425/1369, 4911235/1369, 5616375/169, 93738400/867],
    ![462882/1369, 4911235/1369, 5616375/169, 93738400/867],
    ![459151/1369, 4911235/1369, 5616375/169, 93738400/867]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 28 385541 := by
  refine ⟨?_, rank154 4560, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2950⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free31_2
    · exact free37_1
    · exact free44_1
    · exact free54_1
    · exact free74_4
    · exact free84_1
    · exact free109_1
    · exact free140_1
    · exact free129_1
    · exact free161_1
    · exact free212_1
    · exact free186_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [242988238, 313056431, 313739106, 313423910, 312550243, 311771873, 312234714, 146566664, 146522235, 146798929, 104439358, 74576199, 75486602, 75696785, 94633016, 118850801, 125228441, 219723444], [1507827, 1125007, 1121510, 1123125, 1127600, 1131587, 1129216, 2629419, 2630395, 2624320, 3776009, 5369455, 5304563, 5290028, 4187198, 3299963, 3121447, 1699357],
  ![116633598544080, 1623419045496, 197751099600, 6293700560], 129809128413114069⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,8,8,8,10,15,14,14,12,9,9,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 4911235/1369, 5616375/169, 93738400/867] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle53
end Z6969Source2001

-- Source: Research6969.PhysicalChecks162
section Z6969Source2002
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2592 : Request := ⟨⟨⟨825,1151,248,6399⟩,16903818182656,48256472894⟩,2,3,1,385541,28⟩
theorem cover2592 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2592) 2557 2412 [2415, 2426, 2457, 2544, 2557] := triangleCover (by decide +kernel)
def src2593 : Request := ⟨⟨⟨825,1151,253,6387⟩,17161575202816,49010625289⟩,3,3,1,385541,28⟩
theorem cover2593 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2593) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
def src2594 : Request := ⟨⟨⟨825,1151,253,6640⟩,17161575202816,49010625289⟩,4,3,1,385541,28⟩
theorem cover2594 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2594) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
def src2595 : Request := ⟨⟨⟨1000,1395,307,7779⟩,30557599170560,105715278267⟩,6,3,1,385541,28⟩
theorem cover2595 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2595) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2596 : Request := ⟨⟨⟨1200,1674,368,9067⟩,52718727069696,218807905514⟩,8,3,1,385541,28⟩
theorem cover2596 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2596) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2597 : Request := ⟨⟨⟨1450,2023,445,11237⟩,92998964346880,466511127281⟩,13,3,1,385541,28⟩
theorem cover2597 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2597) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2598 : Request := ⟨⟨⟨2600,3627,798,20294⟩,535425056505856,4812227595495⟩,32,3,1,385541,28⟩
theorem cover2598 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2598) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2599 : Request := ⟨⟨⟨8300,11579,2548,70582⟩,17399709518790656,499124969898998⟩,145,3,1,385541,28⟩
theorem cover2599 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2599) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2600 : Request := ⟨⟨⟨10000,13952,3070,76493⟩,30428373265940480,1051954539834997⟩,145,3,1,385541,28⟩
theorem cover2600 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2600) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2601 : Request := ⟨⟨⟨690,963,212,4963⟩,10065769922560,24078187611⟩,0,3,1,385541,29⟩
theorem cover2601 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2601) 2557 2412 [2415, 2427, 2461, 2557] := triangleCover (by decide +kernel)
def src2602 : Request := ⟨⟨⟨690,963,212,5162⟩,10065769922560,24078187611⟩,1,3,1,385541,29⟩
theorem cover2602 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2602) 2557 2412 [2415, 2427, 2461, 2557] := triangleCover (by decide +kernel)
def src2603 : Request := ⟨⟨⟨825,1151,253,5938⟩,17161575202816,49010625289⟩,2,3,1,385541,29⟩
theorem cover2603 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2603) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
def src2604 : Request := ⟨⟨⟨825,1151,253,6136⟩,17161575202816,49010625289⟩,3,3,1,385541,29⟩
theorem cover2604 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2604) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
def src2605 : Request := ⟨⟨⟨1000,1395,307,7470⟩,30557599170560,105715278267⟩,6,3,1,385541,29⟩
theorem cover2605 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2605) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2606 : Request := ⟨⟨⟨1450,2023,445,11489⟩,92998964346880,466511127281⟩,16,3,1,385541,29⟩
theorem cover2606 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2606) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2607 : Request := ⟨⟨⟨2600,3627,798,19484⟩,535425056505856,4812227595495⟩,32,3,1,385541,29⟩
theorem cover2607 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2607) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source2002

-- Source: Research6969.PrefixRescueDataMiddle53
section Z6969Source2003
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle53
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,28⟩
  bank i := ![bank196 5150, bank204 5961, bank203 6399, bank204 6387, bank204 6640, bank222 7779, bank228 9067, bank237 11237, bank267 20294, bank368 70582, bank380 76493] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 13, 32, 145, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 28

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank196 5150
    · exact rank204 5961
    · exact rank203 6399
    · exact rank204 6387
    · exact rank204 6640
    · exact rank222 7779
    · exact rank228 9067
    · exact rank237 11237
    · exact rank267 20294
    · exact rank368 70582
    · exact rank380 76493
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2590⟩
    · exact ⟨_, cover2591⟩
    · exact ⟨_, cover2592⟩
    · exact ⟨_, cover2593⟩
    · exact ⟨_, cover2594⟩
    · exact ⟨_, cover2595⟩
    · exact ⟨_, cover2596⟩
    · exact ⟨_, cover2597⟩
    · exact ⟨_, cover2598⟩
    · exact ⟨_, cover2599⟩
    · exact ⟨_, cover2600⟩

def price : EarlyPrice := ⟨3, 28, 10, 75/100, 70/100, ![834694981692, 178366490235, 33499975080, 2392877730], 1104275738302190⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16675/146, 70963/73, 267979/73, 988148/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle53
end Z6969Source2003

-- Source: Research6969.PrefixMiddleSaved53
section Z6969Source2004
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved53
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle53.price Lower6960.Prefix6969RescueData.Middle53.price :=
  ⟨335, 3587, 114, 972, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle53.plan Lower6960.Prefix6969RescueData.Middle53.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 28 28 :=
  ⟨Lower6960.Prefix6969MainCases.Middle53.plan, Lower6960.Prefix6969MainCases.Middle53.price, Lower6960.Prefix6969MainCases.Middle53.valid, Lower6960.Prefix6969MainCases.Middle53.priced, Lower6960.Prefix6969MainCases.Middle53.sources,
   Lower6960.Prefix6969RescueData.Middle53.plan, Lower6960.Prefix6969RescueData.Middle53.price, Lower6960.Prefix6969RescueData.Middle53.sources, Lower6960.Prefix6969RescueData.Middle53.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved53
end Z6969Source2004

-- Source: Research6969.PrefixMainDataMiddle54
section Z6969Source2005
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle54
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank31 1491, bank37 1587, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank129 10859, bank161 5142, bank199 7608, bank181 21723, bank212 8810, bank174 26788, bank169 29097] i
  head := src2951
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15525, 123924, 573990, 1990623],
    ![25417/2, 183953/2, 417655, 1399489],
    ![54680/9, 133490/3, 417655, 1399489],
    ![29433/8, 108131/4, 1958440/9, 703248],
    ![64334/25, 465346/25, 158046, 2223081/4],
    ![17323/9, 27761/2, 140530, 1788549/4],
    ![18775/16, 140525/16, 304304/3, 8330784/25],
    ![89110/121, 59850/11, 426340/7, 197708],
    ![89110/121, 59850/11, 116003/2, 197708],
    ![63754/121, 708224/147, 770661/16, 191844],
    ![63754/121, 708224/147, 770661/16, 504896/3],
    ![63754/121, 557203/121, 770661/16, 138874],
    ![33263/82, 557203/121, 770661/16, 138874],
    ![33263/82, 6688224/1681, 1879355/49, 118266],
    ![33263/82, 1628600/441, 8255991/242, 57881664/529],
    ![474397/1369, 1628600/441, 8255991/242, 57881664/529],
    ![474397/1369, 4885118/1369, 5616375/169, 278008360/2601],
    ![462882/1369, 4885118/1369, 5616375/169, 278008360/2601],
    ![459151/1369, 4885118/1369, 5616375/169, 278008360/2601]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 29 385541 := by
  refine ⟨?_, rank154 4508, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2951⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free31_2
    · exact free37_1
    · exact free44_1
    · exact free54_1
    · exact free74_4
    · exact free84_1
    · exact free98_1
    · exact free137_1
    · exact free129_1
    · exact free161_1
    · exact free199_1
    · exact free181_1
    · exact free212_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [242167248, 311290955, 311650254, 312339869, 311170535, 310377337, 311187118, 146561426, 146501767, 146524901, 146663812, 68065000, 68213549, 82117313, 90408929, 95297204, 118637596, 100000000, 219660794], [1514586, 1134051, 1132210, 1128678, 1134667, 1138731, 1134583, 2629534, 2630844, 2630336, 2627287, 5907651, 5894171, 4862637, 4400486, 4158594, 3305930, 3959851, 1699872],
  ![116600342671080, 1623486675196, 197694714600, 5235385960], 129010581908710217⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,8,8,8,8,16,16,13,12,11,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 4885118/1369, 5616375/169, 278008360/2601] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle54
end Z6969Source2005

-- Source: Research6969.PhysicalChecks163
section Z6969Source2006
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2608 : Request := ⟨⟨⟨4800,6696,1474,40432⟩,3367547627110400,55864419956306⟩,85,3,1,385541,29⟩
theorem cover2608 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2608) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2609 : Request := ⟨⟨⟨5700,7952,1750,43331⟩,5637370734182400,111070724916873⟩,85,3,1,385541,29⟩
theorem cover2609 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2609) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2610 : Request := ⟨⟨⟨6900,9626,2118,53622⟩,9997036108906496,238415548481346⟩,110,3,1,385541,29⟩
theorem cover2610 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2610) 2557 2412 [2413, 2418, 2431, 2464, 2550, 2557] := triangleCover (by decide +kernel)
def src2611 : Request := ⟨⟨⟨10000,13952,3070,73566⟩,30428373265940480,1051954539834997⟩,145,3,1,385541,29⟩
theorem cover2611 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2611) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2612 : Request := ⟨⟨⟨560,781,169,4378⟩,5316921262080,10299257375⟩,0,3,1,385541,30⟩
theorem cover2612 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2612) 2557 2412 [2416, 2431, 2475, 2557] := triangleCover (by decide +kernel)
def src2613 : Request := ⟨⟨⟨690,963,208,5140⟩,9921631092736,23724874690⟩,1,3,1,385541,30⟩
theorem cover2613 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2613) 2557 2412 [2415, 2427, 2461, 2557] := triangleCover (by decide +kernel)
def src2614 : Request := ⟨⟨⟨690,962,208,5322⟩,9921631092736,23645774460⟩,2,3,1,385541,30⟩
theorem cover2614 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2614) 2557 2412 [2415, 2427, 2461, 2557] := triangleCover (by decide +kernel)
def src2615 : Request := ⟨⟨⟨825,1151,253,6119⟩,17161575202816,49010625289⟩,4,3,1,385541,30⟩
theorem cover2615 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2615) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
def src2616 : Request := ⟨⟨⟨1000,1395,315,7111⟩,31157463285760,107844841957⟩,6,3,1,385541,30⟩
theorem cover2616 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2616) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2617 : Request := ⟨⟨⟨1200,1674,378,8676⟩,53798525730816,223406703910⟩,10,3,1,385541,30⟩
theorem cover2617 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2617) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2618 : Request := ⟨⟨⟨2100,2930,645,15397⟩,282396798484480,2051392203643⟩,25,3,1,385541,30⟩
theorem cover2618 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2618) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2619 : Request := ⟨⟨⟨3950,5510,1213,30936⟩,1877062482395136,25622281045803⟩,65,3,1,385541,30⟩
theorem cover2619 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2619) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2620 : Request := ⟨⟨⟨5700,7952,1796,41078⟩,5749327563587584,113334118485107⟩,85,3,1,385541,30⟩
theorem cover2620 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2620) 2557 2412 [2413, 2418, 2431, 2465, 2552, 2557] := triangleCover (by decide +kernel)
def src2621 : Request := ⟨⟨⟨8300,11579,2548,64421⟩,17399709518790656,499124969898998⟩,145,3,1,385541,30⟩
theorem cover2621 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2621) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2622 : Request := ⟨⟨⟨10000,13950,3070,80985⟩,30428373265940480,1051468979452278⟩,190,3,1,385541,30⟩
theorem cover2622 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2622) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2623 : Request := ⟨⟨⟨560,781,172,4098⟩,5388141854720,10440670587⟩,0,3,1,385541,31⟩
theorem cover2623 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2623) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source2006

-- Source: Research6969.PrefixRescueDataMiddle54
section Z6969Source2007
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle54
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,29⟩
  bank i := ![bank196 4963, bank196 5162, bank204 5938, bank204 6136, bank222 7470, bank237 11489, bank267 19484, bank343 43331, bank326 40432, bank380 73566, bank356 53622] i
  reserve i := ![0, 1, 2, 3, 6, 16, 32, 85, 85, 145, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 29

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank196 4963
    · exact rank196 5162
    · exact rank204 5938
    · exact rank204 6136
    · exact rank222 7470
    · exact rank237 11489
    · exact rank267 19484
    · exact rank343 43331
    · exact rank326 40432
    · exact rank380 73566
    · exact rank356 53622
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2601⟩
    · exact ⟨_, cover2602⟩
    · exact ⟨_, cover2603⟩
    · exact ⟨_, cover2604⟩
    · exact ⟨_, cover2605⟩
    · exact ⟨_, cover2606⟩
    · exact ⟨_, cover2607⟩
    · exact ⟨_, cover2609⟩
    · exact ⟨_, cover2608⟩
    · exact ⟨_, cover2611⟩
    · exact ⟨_, cover2610⟩

def price : EarlyPrice := ⟨3, 29, 10, 70/100, 70/100, ![831425276160, 180325961794, 34696403200, 2392877730], 1043273837211026⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![4822/43, 41589/43, 157740/43, 586264/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle54
end Z6969Source2007

-- Source: Research6969.PrefixMiddleSaved54
section Z6969Source2008
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved54
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle54.price Lower6960.Prefix6969RescueData.Middle54.price :=
  ⟨335, 3568, 112, 967, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle54.plan Lower6960.Prefix6969RescueData.Middle54.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 29 29 :=
  ⟨Lower6960.Prefix6969MainCases.Middle54.plan, Lower6960.Prefix6969MainCases.Middle54.price, Lower6960.Prefix6969MainCases.Middle54.valid, Lower6960.Prefix6969MainCases.Middle54.priced, Lower6960.Prefix6969MainCases.Middle54.sources,
   Lower6960.Prefix6969RescueData.Middle54.plan, Lower6960.Prefix6969RescueData.Middle54.price, Lower6960.Prefix6969RescueData.Middle54.sources, Lower6960.Prefix6969RescueData.Middle54.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved54
end Z6969Source2008

-- Source: Research6969.PrefixMainDataMiddle55
section Z6969Source2009
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle55
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 20, 30, 30, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank31 1491, bank37 1587, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank115 2949, bank168 3916, bank94 7943, bank152 5208, bank199 7608, bank183 20877, bank212 8810, bank170 28384] i
  head := src2952
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15525, 124008, 574311, 1986012],
    ![25417/2, 366019/4, 415513, 1399489],
    ![54680/9, 44270, 415513, 1399489],
    ![29433/8, 430331/16, 1948546/9, 695292],
    ![64334/25, 462949/25, 158046, 2223081/4],
    ![17323/9, 55233/4, 2236903/16, 7073259/16],
    ![18775/16, 559295/64, 505507/5, 8236536/25],
    ![89110/121, 655035/121, 424198/7, 1368299/7],
    ![89110/121, 655035/121, 116003/2, 1368299/7],
    ![63754/121, 705266/147, 770661/16, 191844],
    ![63754/121, 2027770/441, 751995/16, 8696601/64],
    ![63754/121, 2027770/441, 751995/16, 126736],
    ![22029/50, 2027770/441, 751995/16, 126736],
    ![22029/50, 6625684/1681, 7448009/196, 3013696/25],
    ![22029/50, 1619930/441, 32849697/968, 57881664/529],
    ![954471/2738, 1619930/441, 32849697/968, 57881664/529],
    ![954471/2738, 19438013/5476, 5616375/169, 77616100/729],
    ![920087/2738, 19438013/5476, 5616375/169, 77616100/729]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 30 385541 := by
  refine ⟨?_, rank154 4457, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2952⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free31_2
    · exact free37_1
    · exact free44_1
    · exact free54_1
    · exact free74_4
    · exact free84_1
    · exact free115_1
    · exact free168_1
    · exact free94_1
    · exact free152_1
    · exact free199_1
    · exact free183_1
    · exact free212_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [241480611, 311746435, 310587576, 310690565, 310643824, 311272026, 309873456, 146715841, 146704182, 146247937, 103671694, 94406371, 55000000, 64778784, 87140696, 93422871, 130408446, 229460952], [1520239, 1131717, 1137654, 1137126, 1137366, 1134148, 1141312, 2626144, 2626400, 2636416, 3804682, 4198642, 7354007, 6215139, 4565510, 4248302, 2984150, 1619192],
  ![121802462540640, 1612853391228, 206514856800, 6337998480], 130869817262478067⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,8,8,8,11,12,20,17,12,12,8,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 19438013/5476, 5616375/169, 77616100/729] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle55
end Z6969Source2009

-- Source: Research6969.PrefixRescueDataMiddle55
section Z6969Source2010
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle55
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,30⟩
  bank i := ![bank155 4378, bank195 5140, bank192 5322, bank204 6119, bank223 7111, bank229 8676, bank253 15397, bank310 30936, bank344 41078, bank377 80985, bank368 64421] i
  reserve i := ![0, 1, 2, 4, 6, 10, 25, 65, 85, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 30

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank155 4378
    · exact rank195 5140
    · exact rank192 5322
    · exact rank204 6119
    · exact rank223 7111
    · exact rank229 8676
    · exact rank253 15397
    · exact rank310 30936
    · exact rank344 41078
    · exact rank377 80985
    · exact rank368 64421
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2612⟩
    · exact ⟨_, cover2613⟩
    · exact ⟨_, cover2614⟩
    · exact ⟨_, cover2615⟩
    · exact ⟨_, cover2616⟩
    · exact ⟨_, cover2617⟩
    · exact ⟨_, cover2618⟩
    · exact ⟨_, cover2619⟩
    · exact ⟨_, cover2620⟩
    · exact ⟨_, cover2622⟩
    · exact ⟨_, cover2621⟩

def price : EarlyPrice := ⟨3, 30, 10, 70/100, 70/100, ![946834102875, 190326115415, 35892828250, 2392877730], 961220077047682⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![20090/191, 173085/191, 661455/191, 2429550/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle55
end Z6969Source2010

-- Source: Research6969.PrefixMiddleSaved55
section Z6969Source2011
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved55
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle55.price Lower6960.Prefix6969RescueData.Middle55.price :=
  ⟨336, 3549, 105, 906, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle55.plan Lower6960.Prefix6969RescueData.Middle55.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 30 30 :=
  ⟨Lower6960.Prefix6969MainCases.Middle55.plan, Lower6960.Prefix6969MainCases.Middle55.price, Lower6960.Prefix6969MainCases.Middle55.valid, Lower6960.Prefix6969MainCases.Middle55.priced, Lower6960.Prefix6969MainCases.Middle55.sources,
   Lower6960.Prefix6969RescueData.Middle55.plan, Lower6960.Prefix6969RescueData.Middle55.price, Lower6960.Prefix6969RescueData.Middle55.sources, Lower6960.Prefix6969RescueData.Middle55.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved55
end Z6969Source2011

end Merged_Z6969Pack0746

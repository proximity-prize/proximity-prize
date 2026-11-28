import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0726
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0725
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0724
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0727
section Merged_Z6969Pack0727

-- Source: Research6969.PrefixMiddleSaved81
section Z6969Source1772
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved81
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle81.price Lower6960.Prefix6969RescueData.Middle81.price :=
  ⟨336, 3742, 163, 1728, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle81.plan Lower6960.Prefix6969RescueData.Middle81.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 24 24 :=
  ⟨Lower6960.Prefix6969MainCases.Middle81.plan, Lower6960.Prefix6969MainCases.Middle81.price, Lower6960.Prefix6969MainCases.Middle81.valid, Lower6960.Prefix6969MainCases.Middle81.priced, Lower6960.Prefix6969MainCases.Middle81.sources,
   Lower6960.Prefix6969RescueData.Middle81.plan, Lower6960.Prefix6969RescueData.Middle81.price, Lower6960.Prefix6969RescueData.Middle81.sources, Lower6960.Prefix6969RescueData.Middle81.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved81
end Z6969Source1772

-- Source: Research6969.PrefixMainDataMiddle82
section Z6969Source1773
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle82
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 16, 21, 41, 40, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank13 1183, bank18 1295, bank24 1404, bank29 1513, bank35 1600, bank44 1848, bank54 2149, bank65 2772, bank84 3942, bank95 2576, bank137 3019, bank126 11206, bank149 5119, bank199 7608, bank181 21723, bank212 8810, bank170 28384] i
  head := src2767
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15218, 124719, 580977, 2083781],
    ![25417/2, 95769, 434875, 2908997/2],
    ![54680/9, 416870/9, 434875, 2908997/2],
    ![29433/8, 225077/8, 2037980/9, 767208],
    ![63052/25, 483438/25, 157352, 2289169/4],
    ![5710/3, 129475/9, 586667/4, 491800],
    ![18775/16, 292325/32, 304304/3, 9088464/25],
    ![89110/121, 685000/121, 443560/7, 1509826/7],
    ![89110/121, 685000/121, 443560/7, 1509826/7],
    ![63754/121, 104572/21, 770661/16, 9693378/49],
    ![63754/121, 104572/21, 770661/16, 1658944/9],
    ![63754/121, 583443/121, 770661/16, 9114361/64],
    ![1355575/3362, 583443/121, 770661/16, 9114361/64],
    ![1355575/3362, 425343/100, 3844369/98, 26204161/196],
    ![1355575/3362, 188700/49, 17212467/484, 14031054/121],
    ![474397/1369, 188700/49, 17212467/484, 14031054/121],
    ![474397/1369, 10182081/2738, 45751195/1352, 19404025/169],
    ![920087/2738, 10182081/2738, 45751195/1352, 19404025/169]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 25 257027 := by
  refine ⟨?_, rank154 4918, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2767⟩⟩
  · intro i; fin_cases i
    · exact free5_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free29_1
    · exact free35_1
    · exact free44_1
    · exact free54_1
    · exact free65_1
    · exact free84_1
    · exact free95_1
    · exact free137_1
    · exact free126_1
    · exact free149_1
    · exact free199_1
    · exact free181_1
    · exact free212_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [248689052, 321561290, 321420303, 321368094, 321251202, 321057384, 320421087, 142222614, 140278143, 141015819, 140880920, 67964097, 65625901, 67273981, 93087887, 97011883, 148661497, 221046815], [1460894, 1081441, 1082163, 1082430, 1083029, 1084022, 1087281, 2724787, 2767475, 2751280, 2754242, 5916807, 6128978, 5979429, 4265217, 4086130, 2592536, 1688462],
  ![117336070338300, 1621982773600, 198942133500, 6097628340], 134158652935800299⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,8,8,8,8,16,16,16,12,11,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 10182081/2738, 45751195/1352, 19404025/169] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle82
end Z6969Source1773

-- Source: Research6969.PhysicalChecks133
section Z6969Source1774
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2128 : Request := ⟨⟨⟨4800,6698,1474,41651⟩,3367547627110400,55918169002031⟩,40,2,1,257027,25⟩
theorem cover2128 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2128) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2129 : Request := ⟨⟨⟨8300,11581,2498,80160⟩,17139238515245056,491743896877039⟩,85,2,1,257027,25⟩
theorem cover2129 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2129) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2130 : Request := ⟨⟨⟨10000,13954,3070,83252⟩,30428373265940480,1052440252760428⟩,85,2,1,257027,25⟩
theorem cover2130 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2130) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2131 : Request := ⟨⟨⟨1000,1395,307,7940⟩,30557599170560,105715278267⟩,0,2,1,257027,26⟩
theorem cover2131 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2131) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2132 : Request := ⟨⟨⟨1000,1395,307,8269⟩,30557599170560,105715278267⟩,1,2,1,257027,26⟩
theorem cover2132 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2132) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2133 : Request := ⟨⟨⟨1200,1674,368,9248⟩,52718727069696,218807905514⟩,1,2,1,257027,26⟩
theorem cover2133 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2133) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2134 : Request := ⟨⟨⟨1200,1674,368,9538⟩,52718727069696,218807905514⟩,2,2,1,257027,26⟩
theorem cover2134 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2134) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2135 : Request := ⟨⟨⟨1450,2023,445,11369⟩,92998964346880,466511127281⟩,4,2,1,257027,26⟩
theorem cover2135 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2135) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2136 : Request := ⟨⟨⟨1750,2442,537,14075⟩,163381988556800,989573241440⟩,8,2,1,257027,26⟩
theorem cover2136 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2136) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2137 : Request := ⟨⟨⟨2100,2930,645,17304⟩,282396798484480,2051392203643⟩,13,2,1,257027,26⟩
theorem cover2137 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2137) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2138 : Request := ⟨⟨⟨4800,6698,1474,38700⟩,3367547627110400,55918169002031⟩,40,2,1,257027,26⟩
theorem cover2138 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2138) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2139 : Request := ⟨⟨⟨8300,11581,2548,69838⟩,17399709518790656,499402661779949⟩,85,2,1,257027,26⟩
theorem cover2139 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2139) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2140 : Request := ⟨⟨⟨10000,13954,3070,77844⟩,30428373265940480,1052440252760428⟩,85,2,1,257027,26⟩
theorem cover2140 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2140) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2141 : Request := ⟨⟨⟨10000,13953,3070,86299⟩,30428373265940480,1052197377228338⟩,110,2,1,257027,26⟩
theorem cover2141 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2141) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2142 : Request := ⟨⟨⟨1000,1395,307,7487⟩,30557599170560,105715278267⟩,0,2,1,257027,27⟩
theorem cover2142 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2142) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2143 : Request := ⟨⟨⟨1200,1674,368,8756⟩,52718727069696,218807905514⟩,1,2,1,257027,27⟩
theorem cover2143 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2143) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1774

-- Source: Research6969.PrefixRescueDataMiddle82
section Z6969Source1775
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle82
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,25⟩
  bank i := ![bank222 8526, bank228 9876, bank237 11510, bank237 11827, bank237 12176, bank246 14397, bank253 17502, bank304 26529, bank333 41651, bank371 80160, bank385 83252] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 20, 40, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 25

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank222 8526
    · exact rank228 9876
    · exact rank237 11510
    · exact rank237 11827
    · exact rank237 12176
    · exact rank246 14397
    · exact rank253 17502
    · exact rank304 26529
    · exact rank333 41651
    · exact rank371 80160
    · exact rank385 83252
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2120⟩
    · exact ⟨_, cover2121⟩
    · exact ⟨_, cover2122⟩
    · exact ⟨_, cover2123⟩
    · exact ⟨_, cover2124⟩
    · exact ⟨_, cover2125⟩
    · exact ⟨_, cover2126⟩
    · exact ⟨_, cover2127⟩
    · exact ⟨_, cover2128⟩
    · exact ⟨_, cover2129⟩
    · exact ⟨_, cover2130⟩

def price : EarlyPrice := ⟨2, 25, 10, 75/100, 70/100, ![811115661044, 138486910144, 29910693790, 1196449610], 1591884341686286⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![14079/86, 71305/43, 449845/86, 1002000/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle82
end Z6969Source1775

-- Source: Research6969.PrefixMiddleSaved82
section Z6969Source1776
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved82
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle82.price Lower6960.Prefix6969RescueData.Middle82.price :=
  ⟨336, 3718, 163, 1658, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle82.plan Lower6960.Prefix6969RescueData.Middle82.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 25 25 :=
  ⟨Lower6960.Prefix6969MainCases.Middle82.plan, Lower6960.Prefix6969MainCases.Middle82.price, Lower6960.Prefix6969MainCases.Middle82.valid, Lower6960.Prefix6969MainCases.Middle82.priced, Lower6960.Prefix6969MainCases.Middle82.sources,
   Lower6960.Prefix6969RescueData.Middle82.plan, Lower6960.Prefix6969RescueData.Middle82.price, Lower6960.Prefix6969RescueData.Middle82.sources, Lower6960.Prefix6969RescueData.Middle82.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved82
end Z6969Source1776

-- Source: Research6969.PrefixMainDataMiddle83
section Z6969Source1777
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle83
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 16, 21, 41, 40, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank13 1183, bank18 1295, bank24 1404, bank29 1513, bank35 1600, bank44 1848, bank54 2149, bank65 2772, bank84 3942, bank95 2576, bank137 3019, bank126 11206, bank149 5119, bank199 7608, bank180 21819, bank212 8810, bank170 28384] i
  head := src2768
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15218, 124524, 579872, 2074876],
    ![25417/2, 380671/4, 432145, 5741099/4],
    ![54680/9, 46030, 432145, 5741099/4],
    ![29433/8, 447359/16, 2025370/9, 757068],
    ![63052/25, 480448/25, 157352, 2289169/4],
    ![5710/3, 85775/6, 1165989/8, 485300],
    ![18775/16, 581075/64, 304304/3, 8968344/25],
    ![89110/121, 680775/121, 440830/7, 1489871/7],
    ![89110/121, 680775/121, 440830/7, 1489871/7],
    ![63754/121, 728234/147, 770661/16, 9565263/49],
    ![63754/121, 728234/147, 770661/16, 1658944/9],
    ![63754/121, 579283/121, 770661/16, 9114361/64],
    ![1355575/3362, 579283/121, 770661/16, 9114361/64],
    ![1355575/3362, 1690387/400, 3844369/98, 26204161/196],
    ![1355575/3362, 1687250/441, 34202829/968, 13845609/121],
    ![25627/74, 1687250/441, 34202829/968, 13845609/121],
    ![25627/74, 20233577/5476, 90922265/2704, 13845609/121],
    ![920087/2738, 20233577/5476, 90922265/2704, 13845609/121]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 26 257027 := by
  refine ⟨?_, rank154 4853, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2768⟩⟩
  · intro i; fin_cases i
    · exact free5_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free29_1
    · exact free35_1
    · exact free44_1
    · exact free54_1
    · exact free65_1
    · exact free84_1
    · exact free95_1
    · exact free137_1
    · exact free126_1
    · exact free149_1
    · exact free199_1
    · exact free180_1
    · exact free212_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [247394642, 319004062, 319029316, 319492216, 319867450, 320809909, 319569862, 147180056, 147212697, 147238641, 147494233, 67553451, 65866235, 83678254, 92233289, 97503014, 147539657, 220775414], [1471551, 1094540, 1094411, 1092040, 1090117, 1085290, 1091642, 2617199, 2616656, 2616224, 2611968, 5954069, 6107170, 4769827, 4308368, 4065375, 2611212, 1690696],
  ![117192005259480, 1622277344596, 198697872600, 5125790530], 133099483062670727⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,7,7,7,7,16,16,13,12,11,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 20233577/5476, 90922265/2704, 13845609/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle83
end Z6969Source1777

-- Source: Research6969.PrefixRescueDataMiddle83
section Z6969Source1778
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle83
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,26⟩
  bank i := ![bank222 7940, bank228 9248, bank228 9538, bank222 8269, bank237 11369, bank246 14075, bank253 17304, bank333 38700, bank383 86299, bank385 77844, bank372 69838] i
  reserve i := ![0, 1, 2, 1, 4, 8, 13, 40, 110, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 26

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank222 7940
    · exact rank228 9248
    · exact rank228 9538
    · exact rank222 8269
    · exact rank237 11369
    · exact rank246 14075
    · exact rank253 17304
    · exact rank333 38700
    · exact rank383 86299
    · exact rank385 77844
    · exact rank372 69838
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2131⟩
    · exact ⟨_, cover2133⟩
    · exact ⟨_, cover2134⟩
    · exact ⟨_, cover2132⟩
    · exact ⟨_, cover2135⟩
    · exact ⟨_, cover2136⟩
    · exact ⟨_, cover2137⟩
    · exact ⟨_, cover2138⟩
    · exact ⟨_, cover2141⟩
    · exact ⟨_, cover2140⟩
    · exact ⟨_, cover2139⟩

def price : EarlyPrice := ⟨2, 26, 10, 70/100, 70/100, ![874434282988, 143905921573, 31107118840, 1196449610], 1564405022912552⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![17023/111, 55373/37, 535376/111, 2243774/111] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle83
end Z6969Source1778

-- Source: Research6969.PrefixMiddleSaved83
section Z6969Source1779
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved83
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle83.price Lower6960.Prefix6969RescueData.Middle83.price :=
  ⟨336, 3694, 153, 1496, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle83.plan Lower6960.Prefix6969RescueData.Middle83.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 26 26 :=
  ⟨Lower6960.Prefix6969MainCases.Middle83.plan, Lower6960.Prefix6969MainCases.Middle83.price, Lower6960.Prefix6969MainCases.Middle83.valid, Lower6960.Prefix6969MainCases.Middle83.priced, Lower6960.Prefix6969MainCases.Middle83.sources,
   Lower6960.Prefix6969RescueData.Middle83.plan, Lower6960.Prefix6969RescueData.Middle83.price, Lower6960.Prefix6969RescueData.Middle83.sources, Lower6960.Prefix6969RescueData.Middle83.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved83
end Z6969Source1779

-- Source: Research6969.PrefixMainDataMiddle84
section Z6969Source1780
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle84
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 17, 21, 41, 40, 76, 76, 76, 76] i
  bank i := ![bank5 1094, bank13 1183, bank18 1295, bank24 1404, bank29 1513, bank35 1600, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank129 10859, bank151 5065, bank212 8810, bank186 19684, bank175 25973, bank169 29097] i
  head := src2769
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15265, 124338, 578741, 2056552],
    ![25417/2, 94585, 429499, 2833285/2],
    ![54680/9, 45750, 429499, 2833285/2],
    ![29433/8, 222325/8, 2013148/9, 747240],
    ![63052/25, 19102, 157352, 2289169/4],
    ![5710/3, 42625/3, 579435/4, 479000],
    ![18775/16, 288805/32, 304304/3, 1770384/5],
    ![89110/121, 676680/121, 438184/7, 1470530/7],
    ![89110/121, 676680/121, 116003/2, 1470530/7],
    ![63754/121, 724580/147, 770661/16, 9441090/49],
    ![63754/121, 724580/147, 770661/16, 536480/3],
    ![63754/121, 575251/121, 770661/16, 9114361/64],
    ![33263/82, 575251/121, 770661/16, 9114361/64],
    ![33263/82, 168493/40, 3874725/98, 25654225/196],
    ![33263/82, 10053505/2738, 45179995/1352, 295399300/2601],
    ![481425/1369, 10053505/2738, 45179995/1352, 295399300/2601],
    ![929061/2738, 10053505/2738, 45179995/1352, 295399300/2601],
    ![459151/1369, 10053505/2738, 45179995/1352, 295399300/2601]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 27 257027 := by
  refine ⟨?_, rank154 4790, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2769⟩⟩
  · intro i; fin_cases i
    · exact free5_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free29_1
    · exact free35_1
    · exact free44_1
    · exact free54_1
    · exact free74_4
    · exact free84_1
    · exact free98_1
    · exact free137_1
    · exact free129_1
    · exact free151_1
    · exact free212_1
    · exact free186_1
    · exact free175_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [246356796, 317447216, 317072193, 318035444, 317699855, 317106076, 319020301, 146846628, 147258469, 146881953, 146986964, 67449255, 69821071, 78402292, 96967884, 112519068, 131916151, 230681328], [1480095, 1102515, 1104436, 1099502, 1101221, 1104263, 1094457, 2623273, 2615894, 2622498, 2620414, 5963524, 5748302, 5102932, 4087990, 3495160, 2951051, 1609145],
  ![122450262528960, 1611529019112, 207613195200, 6071106300], 134428953263115856⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,8,7,8,7,16,16,14,11,10,8,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 10053505/2738, 45179995/1352, 295399300/2601] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle84
end Z6969Source1780

-- Source: Research6969.PhysicalChecks134
section Z6969Source1781
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2144 : Request := ⟨⟨⟨1200,1674,368,8993⟩,52718727069696,218807905514⟩,2,2,1,257027,27⟩
theorem cover2144 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2144) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2145 : Request := ⟨⟨⟨1200,1674,368,9254⟩,52718727069696,218807905514⟩,3,2,1,257027,27⟩
theorem cover2145 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2145) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2146 : Request := ⟨⟨⟨1200,1674,368,9545⟩,52718727069696,218807905514⟩,4,2,1,257027,27⟩
theorem cover2146 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2146) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2147 : Request := ⟨⟨⟨1450,2023,445,11257⟩,92998964346880,466511127281⟩,6,2,1,257027,27⟩
theorem cover2147 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2147) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2148 : Request := ⟨⟨⟨1750,2442,537,13803⟩,163381988556800,989573241440⟩,10,2,1,257027,27⟩
theorem cover2148 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2148) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2149 : Request := ⟨⟨⟨2600,3628,798,20567⟩,535425056505856,4816500515660⟩,20,2,1,257027,27⟩
theorem cover2149 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2149) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2150 : Request := ⟨⟨⟨3950,5512,1213,30202⟩,1877062482395136,25652240151764⟩,32,2,1,257027,27⟩
theorem cover2150 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2150) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2151 : Request := ⟨⟨⟨6900,9628,2118,53188⟩,9997036108906496,238575106344005⟩,65,2,1,257027,27⟩
theorem cover2151 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2151) 2557 2412 [2413, 2418, 2431, 2464, 2550, 2557] := triangleCover (by decide +kernel)
def src2152 : Request := ⟨⟨⟨10000,13953,3070,80369⟩,30428373265940480,1052197377228338⟩,110,2,1,257027,27⟩
theorem cover2152 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2152) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2153 : Request := ⟨⟨⟨825,1151,253,6309⟩,17161575202816,49010625289⟩,0,2,1,257027,28⟩
theorem cover2153 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2153) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
def src2154 : Request := ⟨⟨⟨1000,1395,307,7347⟩,30557599170560,105715278267⟩,1,2,1,257027,28⟩
theorem cover2154 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2154) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2155 : Request := ⟨⟨⟨1000,1395,307,7592⟩,30557599170560,105715278267⟩,2,2,1,257027,28⟩
theorem cover2155 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2155) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2156 : Request := ⟨⟨⟨1200,1674,368,8780⟩,52718727069696,218807905514⟩,3,2,1,257027,28⟩
theorem cover2156 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2156) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2157 : Request := ⟨⟨⟨1200,1674,368,9018⟩,52718727069696,218807905514⟩,4,2,1,257027,28⟩
theorem cover2157 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2157) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2158 : Request := ⟨⟨⟨1450,2023,445,10670⟩,92998964346880,466511127281⟩,6,2,1,257027,28⟩
theorem cover2158 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2158) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2159 : Request := ⟨⟨⟨1750,2442,537,13058⟩,163381988556800,989573241440⟩,10,2,1,257027,28⟩
theorem cover2159 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2159) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1781

-- Source: Research6969.PrefixRescueDataMiddle84
section Z6969Source1782
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle84
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,27⟩
  bank i := ![bank222 7487, bank228 8756, bank228 8993, bank228 9254, bank228 9545, bank237 11257, bank246 13803, bank271 20567, bank316 30202, bank360 53188, bank383 80369] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 20, 32, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 27

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank222 7487
    · exact rank228 8756
    · exact rank228 8993
    · exact rank228 9254
    · exact rank228 9545
    · exact rank237 11257
    · exact rank246 13803
    · exact rank271 20567
    · exact rank316 30202
    · exact rank360 53188
    · exact rank383 80369
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2142⟩
    · exact ⟨_, cover2143⟩
    · exact ⟨_, cover2144⟩
    · exact ⟨_, cover2145⟩
    · exact ⟨_, cover2146⟩
    · exact ⟨_, cover2147⟩
    · exact ⟨_, cover2148⟩
    · exact ⟨_, cover2149⟩
    · exact ⟨_, cover2150⟩
    · exact ⟨_, cover2151⟩
    · exact ⟨_, cover2152⟩

def price : EarlyPrice := ⟨2, 27, 10, 75/100, 70/100, ![845668979032, 145836143411, 32303546960, 1196449610], 1519890570374330⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![17023/111, 163259/111, 537469/111, 723321/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle84
end Z6969Source1782

-- Source: Research6969.PrefixMiddleSaved84
section Z6969Source1783
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved84
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle84.price Lower6960.Prefix6969RescueData.Middle84.price :=
  ⟨335, 3671, 153, 1470, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle84.plan Lower6960.Prefix6969RescueData.Middle84.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 27 27 :=
  ⟨Lower6960.Prefix6969MainCases.Middle84.plan, Lower6960.Prefix6969MainCases.Middle84.price, Lower6960.Prefix6969MainCases.Middle84.valid, Lower6960.Prefix6969MainCases.Middle84.priced, Lower6960.Prefix6969MainCases.Middle84.sources,
   Lower6960.Prefix6969RescueData.Middle84.plan, Lower6960.Prefix6969RescueData.Middle84.price, Lower6960.Prefix6969RescueData.Middle84.sources, Lower6960.Prefix6969RescueData.Middle84.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved84
end Z6969Source1783

end Merged_Z6969Pack0727

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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 25 257073 := by
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

def price : Pricing := ⟨55/100, 90/100, [248689052, 321561290, 321420303, 321368094, 321251202, 321057384, 320421087, 142222614, 140278143, 141015819, 140880920, 67964097, 65625901, 67273981, 93087887, 97011883, 148661497, 221046815], [1460562, 1081194, 1081917, 1082184, 1082783, 1083775, 1087034, 2724166, 2766845, 2750654, 2753615, 5915459, 6127582, 5978067, 4264246, 4085200, 2591945, 1688077],
  ![117336070338300, 1621982773600, 198942133500, 6097628340], 134153786649229823⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2128 : Request := ⟨⟨⟨4800,6698,1474,41651⟩,3367547627110400,55918169002031⟩,40,2,1,257073,25⟩
private theorem pass2128_2390 : (Triangular src2128) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2128_2391 : (Triangular src2128) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2128_2393 : (Triangular src2128) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2128_2398 : (Triangular src2128) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2128_2411 : (Triangular src2128) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2128_2445 : (Triangular src2128) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2128_2533 : (Triangular src2128) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2128 : Cover (Triangular src2128) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2128_2390, by decide, by decide, pass2128_2391, by decide, by decide, pass2128_2393, by decide, by decide, pass2128_2398, by decide, by decide, pass2128_2411, by decide, by decide, pass2128_2445, by decide, by decide, pass2128_2533, rfl⟩
def src2129 : Request := ⟨⟨⟨8300,11581,2498,80160⟩,17139238515245056,491743896877039⟩,85,2,1,257073,25⟩
private theorem pass2129_2390 : (Triangular src2129) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2129_2391 : (Triangular src2129) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2129_2393 : (Triangular src2129) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2129_2398 : (Triangular src2129) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2129_2411 : (Triangular src2129) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2129_2445 : (Triangular src2129) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2129_2533 : (Triangular src2129) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2129 : Cover (Triangular src2129) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2129_2390, by decide, by decide, pass2129_2391, by decide, by decide, pass2129_2393, by decide, by decide, pass2129_2398, by decide, by decide, pass2129_2411, by decide, by decide, pass2129_2445, by decide, by decide, pass2129_2533, rfl⟩
def src2130 : Request := ⟨⟨⟨10000,13954,3070,83252⟩,30428373265940480,1052440252760428⟩,85,2,1,257073,25⟩
private theorem pass2130_2390 : (Triangular src2130) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2130_2391 : (Triangular src2130) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2130_2393 : (Triangular src2130) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2130_2398 : (Triangular src2130) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2130_2411 : (Triangular src2130) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2130_2444 : (Triangular src2130) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2130_2529 : (Triangular src2130) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2130 : Cover (Triangular src2130) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2130_2390, by decide, by decide, pass2130_2391, by decide, by decide, pass2130_2393, by decide, by decide, pass2130_2398, by decide, by decide, pass2130_2411, by decide, by decide, pass2130_2444, by decide, by decide, pass2130_2529, rfl⟩
def src2131 : Request := ⟨⟨⟨1000,1395,307,7940⟩,30557599170560,105715278267⟩,0,2,1,257073,26⟩
private theorem pass2131_2390 : (Triangular src2131) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2131_2391 : (Triangular src2131) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2131_2393 : (Triangular src2131) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2131_2399 : (Triangular src2131) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2131_2415 : (Triangular src2131) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2131_2459 : (Triangular src2131) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2131 : Cover (Triangular src2131) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2131_2390, by decide, by decide, pass2131_2391, by decide, by decide, pass2131_2393, by decide, by decide, pass2131_2399, by decide, by decide, pass2131_2415, by decide, by decide, pass2131_2459, rfl⟩
def src2132 : Request := ⟨⟨⟨1000,1395,307,8269⟩,30557599170560,105715278267⟩,1,2,1,257073,26⟩
private theorem pass2132_2390 : (Triangular src2132) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2132_2391 : (Triangular src2132) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2132_2393 : (Triangular src2132) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2132_2399 : (Triangular src2132) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2132_2415 : (Triangular src2132) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2132_2459 : (Triangular src2132) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2132 : Cover (Triangular src2132) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2132_2390, by decide, by decide, pass2132_2391, by decide, by decide, pass2132_2393, by decide, by decide, pass2132_2399, by decide, by decide, pass2132_2415, by decide, by decide, pass2132_2459, rfl⟩
def src2133 : Request := ⟨⟨⟨1200,1674,368,9248⟩,52718727069696,218807905514⟩,1,2,1,257073,26⟩
private theorem pass2133_2390 : (Triangular src2133) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2133_2391 : (Triangular src2133) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2133_2393 : (Triangular src2133) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2133_2399 : (Triangular src2133) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2133_2415 : (Triangular src2133) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2133_2458 : (Triangular src2133) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2133 : Cover (Triangular src2133) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2133_2390, by decide, by decide, pass2133_2391, by decide, by decide, pass2133_2393, by decide, by decide, pass2133_2399, by decide, by decide, pass2133_2415, by decide, by decide, pass2133_2458, rfl⟩
def src2134 : Request := ⟨⟨⟨1200,1674,368,9538⟩,52718727069696,218807905514⟩,2,2,1,257073,26⟩
private theorem pass2134_2390 : (Triangular src2134) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2134_2391 : (Triangular src2134) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2134_2393 : (Triangular src2134) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2134_2399 : (Triangular src2134) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2134_2415 : (Triangular src2134) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2134_2458 : (Triangular src2134) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2134 : Cover (Triangular src2134) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2134_2390, by decide, by decide, pass2134_2391, by decide, by decide, pass2134_2393, by decide, by decide, pass2134_2399, by decide, by decide, pass2134_2415, by decide, by decide, pass2134_2458, rfl⟩
def src2135 : Request := ⟨⟨⟨1450,2023,445,11369⟩,92998964346880,466511127281⟩,4,2,1,257073,26⟩
private theorem pass2135_2390 : (Triangular src2135) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2135_2391 : (Triangular src2135) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2135_2393 : (Triangular src2135) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2135_2399 : (Triangular src2135) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2135_2415 : (Triangular src2135) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2135_2458 : (Triangular src2135) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2135 : Cover (Triangular src2135) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2135_2390, by decide, by decide, pass2135_2391, by decide, by decide, pass2135_2393, by decide, by decide, pass2135_2399, by decide, by decide, pass2135_2415, by decide, by decide, pass2135_2458, rfl⟩
def src2136 : Request := ⟨⟨⟨1750,2442,537,14075⟩,163381988556800,989573241440⟩,8,2,1,257073,26⟩
private theorem pass2136_2390 : (Triangular src2136) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2136_2391 : (Triangular src2136) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2136_2393 : (Triangular src2136) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2136_2398 : (Triangular src2136) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2136_2412 : (Triangular src2136) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2136_2449 : (Triangular src2136) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2136 : Cover (Triangular src2136) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2136_2390, by decide, by decide, pass2136_2391, by decide, by decide, pass2136_2393, by decide, by decide, pass2136_2398, by decide, by decide, pass2136_2412, by decide, by decide, pass2136_2449, rfl⟩
def src2137 : Request := ⟨⟨⟨2100,2930,645,17304⟩,282396798484480,2051392203643⟩,13,2,1,257073,26⟩
private theorem pass2137_2390 : (Triangular src2137) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2137_2391 : (Triangular src2137) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2137_2393 : (Triangular src2137) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2137_2398 : (Triangular src2137) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2137_2412 : (Triangular src2137) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2137_2449 : (Triangular src2137) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2137 : Cover (Triangular src2137) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2137_2390, by decide, by decide, pass2137_2391, by decide, by decide, pass2137_2393, by decide, by decide, pass2137_2398, by decide, by decide, pass2137_2412, by decide, by decide, pass2137_2449, rfl⟩
def src2138 : Request := ⟨⟨⟨4800,6698,1474,38700⟩,3367547627110400,55918169002031⟩,40,2,1,257073,26⟩
private theorem pass2138_2390 : (Triangular src2138) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2138_2391 : (Triangular src2138) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2138_2393 : (Triangular src2138) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2138_2398 : (Triangular src2138) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2138_2411 : (Triangular src2138) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2138_2445 : (Triangular src2138) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2138_2533 : (Triangular src2138) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2138 : Cover (Triangular src2138) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2138_2390, by decide, by decide, pass2138_2391, by decide, by decide, pass2138_2393, by decide, by decide, pass2138_2398, by decide, by decide, pass2138_2411, by decide, by decide, pass2138_2445, by decide, by decide, pass2138_2533, rfl⟩
def src2139 : Request := ⟨⟨⟨8300,11581,2548,69838⟩,17399709518790656,499402661779949⟩,85,2,1,257073,26⟩
private theorem pass2139_2390 : (Triangular src2139) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2139_2391 : (Triangular src2139) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2139_2393 : (Triangular src2139) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2139_2398 : (Triangular src2139) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2139_2411 : (Triangular src2139) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2139_2445 : (Triangular src2139) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2139_2532 : (Triangular src2139) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2139 : Cover (Triangular src2139) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2139_2390, by decide, by decide, pass2139_2391, by decide, by decide, pass2139_2393, by decide, by decide, pass2139_2398, by decide, by decide, pass2139_2411, by decide, by decide, pass2139_2445, by decide, by decide, pass2139_2532, rfl⟩
def src2140 : Request := ⟨⟨⟨10000,13954,3070,77844⟩,30428373265940480,1052440252760428⟩,85,2,1,257073,26⟩
private theorem pass2140_2390 : (Triangular src2140) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2140_2391 : (Triangular src2140) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2140_2393 : (Triangular src2140) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2140_2398 : (Triangular src2140) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2140_2411 : (Triangular src2140) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2140_2444 : (Triangular src2140) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2140_2529 : (Triangular src2140) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2140 : Cover (Triangular src2140) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2140_2390, by decide, by decide, pass2140_2391, by decide, by decide, pass2140_2393, by decide, by decide, pass2140_2398, by decide, by decide, pass2140_2411, by decide, by decide, pass2140_2444, by decide, by decide, pass2140_2529, rfl⟩
def src2141 : Request := ⟨⟨⟨10000,13953,3070,86299⟩,30428373265940480,1052197377228338⟩,110,2,1,257073,26⟩
private theorem pass2141_2390 : (Triangular src2141) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2141_2391 : (Triangular src2141) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2141_2393 : (Triangular src2141) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2141_2398 : (Triangular src2141) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2141_2411 : (Triangular src2141) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2141_2444 : (Triangular src2141) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2141_2529 : (Triangular src2141) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2141 : Cover (Triangular src2141) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2141_2390, by decide, by decide, pass2141_2391, by decide, by decide, pass2141_2393, by decide, by decide, pass2141_2398, by decide, by decide, pass2141_2411, by decide, by decide, pass2141_2444, by decide, by decide, pass2141_2529, rfl⟩
def src2142 : Request := ⟨⟨⟨1000,1395,307,7487⟩,30557599170560,105715278267⟩,0,2,1,257073,27⟩
private theorem pass2142_2390 : (Triangular src2142) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2142_2391 : (Triangular src2142) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2142_2393 : (Triangular src2142) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2142_2399 : (Triangular src2142) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2142_2415 : (Triangular src2142) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2142_2459 : (Triangular src2142) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2142 : Cover (Triangular src2142) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2142_2390, by decide, by decide, pass2142_2391, by decide, by decide, pass2142_2393, by decide, by decide, pass2142_2399, by decide, by decide, pass2142_2415, by decide, by decide, pass2142_2459, rfl⟩
def src2143 : Request := ⟨⟨⟨1200,1674,368,8756⟩,52718727069696,218807905514⟩,1,2,1,257073,27⟩
private theorem pass2143_2390 : (Triangular src2143) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2143_2391 : (Triangular src2143) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2143_2393 : (Triangular src2143) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2143_2399 : (Triangular src2143) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2143_2415 : (Triangular src2143) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2143_2458 : (Triangular src2143) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2143 : Cover (Triangular src2143) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2143_2390, by decide, by decide, pass2143_2391, by decide, by decide, pass2143_2393, by decide, by decide, pass2143_2399, by decide, by decide, pass2143_2415, by decide, by decide, pass2143_2458, rfl⟩
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
  physicalFloor := 257073
  seedFloor := 25

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨2, 25, 10, 75/100, 70/100, ![811115661044, 138486910144, 29910693790, 1196449610], 1591546989519385⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 26 257073 := by
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

def price : Pricing := ⟨55/100, 90/100, [247394642, 319004062, 319029316, 319492216, 319867450, 320809909, 319569862, 147180056, 147212697, 147238641, 147494233, 67553451, 65866235, 83678254, 92233289, 97503014, 147539657, 220775414], [1471216, 1094291, 1094162, 1091791, 1089869, 1085043, 1091393, 2616603, 2616060, 2615628, 2611374, 5952713, 6105779, 4768741, 4307387, 4064449, 2610618, 1690311],
  ![117192005259480, 1622277344596, 198697872600, 5125790530], 133094631674529718⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 257073
  seedFloor := 26

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨2, 26, 10, 70/100, 70/100, ![874434282988, 143905921573, 31107118840, 1196449610], 1564073909178984⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 27 257073 := by
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

def price : Pricing := ⟨55/100, 90/100, [246356796, 317447216, 317072193, 318035444, 317699855, 317106076, 319020301, 146846628, 147258469, 146881953, 146986964, 67449255, 69821071, 78402292, 96967884, 112519068, 131916151, 230681328], [1479758, 1102264, 1104185, 1099252, 1100970, 1104011, 1094208, 2622676, 2615298, 2621900, 2619817, 5962166, 5746993, 5101770, 4087059, 3494364, 2950379, 1608778],
  ![122450262528960, 1611529019112, 207613195200, 6071106300], 134424090252850424⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2144 : Request := ⟨⟨⟨1200,1674,368,8993⟩,52718727069696,218807905514⟩,2,2,1,257073,27⟩
private theorem pass2144_2390 : (Triangular src2144) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2144_2391 : (Triangular src2144) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2144_2393 : (Triangular src2144) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2144_2399 : (Triangular src2144) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2144_2415 : (Triangular src2144) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2144_2458 : (Triangular src2144) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2144 : Cover (Triangular src2144) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2144_2390, by decide, by decide, pass2144_2391, by decide, by decide, pass2144_2393, by decide, by decide, pass2144_2399, by decide, by decide, pass2144_2415, by decide, by decide, pass2144_2458, rfl⟩
def src2145 : Request := ⟨⟨⟨1200,1674,368,9254⟩,52718727069696,218807905514⟩,3,2,1,257073,27⟩
private theorem pass2145_2390 : (Triangular src2145) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2145_2391 : (Triangular src2145) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2145_2393 : (Triangular src2145) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2145_2399 : (Triangular src2145) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2145_2415 : (Triangular src2145) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2145_2458 : (Triangular src2145) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2145 : Cover (Triangular src2145) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2145_2390, by decide, by decide, pass2145_2391, by decide, by decide, pass2145_2393, by decide, by decide, pass2145_2399, by decide, by decide, pass2145_2415, by decide, by decide, pass2145_2458, rfl⟩
def src2146 : Request := ⟨⟨⟨1200,1674,368,9545⟩,52718727069696,218807905514⟩,4,2,1,257073,27⟩
private theorem pass2146_2390 : (Triangular src2146) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2146_2391 : (Triangular src2146) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2146_2393 : (Triangular src2146) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2146_2399 : (Triangular src2146) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2146_2415 : (Triangular src2146) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2146_2458 : (Triangular src2146) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2146 : Cover (Triangular src2146) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2146_2390, by decide, by decide, pass2146_2391, by decide, by decide, pass2146_2393, by decide, by decide, pass2146_2399, by decide, by decide, pass2146_2415, by decide, by decide, pass2146_2458, rfl⟩
def src2147 : Request := ⟨⟨⟨1450,2023,445,11257⟩,92998964346880,466511127281⟩,6,2,1,257073,27⟩
private theorem pass2147_2390 : (Triangular src2147) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2147_2391 : (Triangular src2147) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2147_2393 : (Triangular src2147) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2147_2399 : (Triangular src2147) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2147_2415 : (Triangular src2147) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2147_2458 : (Triangular src2147) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2147 : Cover (Triangular src2147) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2147_2390, by decide, by decide, pass2147_2391, by decide, by decide, pass2147_2393, by decide, by decide, pass2147_2399, by decide, by decide, pass2147_2415, by decide, by decide, pass2147_2458, rfl⟩
def src2148 : Request := ⟨⟨⟨1750,2442,537,13803⟩,163381988556800,989573241440⟩,10,2,1,257073,27⟩
private theorem pass2148_2390 : (Triangular src2148) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2148_2391 : (Triangular src2148) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2148_2393 : (Triangular src2148) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2148_2398 : (Triangular src2148) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2148_2412 : (Triangular src2148) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2148_2449 : (Triangular src2148) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2148 : Cover (Triangular src2148) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2148_2390, by decide, by decide, pass2148_2391, by decide, by decide, pass2148_2393, by decide, by decide, pass2148_2398, by decide, by decide, pass2148_2412, by decide, by decide, pass2148_2449, rfl⟩
def src2149 : Request := ⟨⟨⟨2600,3628,798,20567⟩,535425056505856,4816500515660⟩,20,2,1,257073,27⟩
private theorem pass2149_2390 : (Triangular src2149) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2149_2391 : (Triangular src2149) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2149_2393 : (Triangular src2149) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2149_2398 : (Triangular src2149) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2149_2411 : (Triangular src2149) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2149_2446 : (Triangular src2149) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2149 : Cover (Triangular src2149) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass2149_2390, by decide, by decide, pass2149_2391, by decide, by decide, pass2149_2393, by decide, by decide, pass2149_2398, by decide, by decide, pass2149_2411, by decide, by decide, pass2149_2446, rfl⟩
def src2150 : Request := ⟨⟨⟨3950,5512,1213,30202⟩,1877062482395136,25652240151764⟩,32,2,1,257073,27⟩
private theorem pass2150_2390 : (Triangular src2150) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2150_2391 : (Triangular src2150) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2150_2393 : (Triangular src2150) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2150_2398 : (Triangular src2150) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2150_2411 : (Triangular src2150) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2150_2445 : (Triangular src2150) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2150_2534 : (Triangular src2150) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2150 : Cover (Triangular src2150) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2150_2390, by decide, by decide, pass2150_2391, by decide, by decide, pass2150_2393, by decide, by decide, pass2150_2398, by decide, by decide, pass2150_2411, by decide, by decide, pass2150_2445, by decide, by decide, pass2150_2534, rfl⟩
def src2151 : Request := ⟨⟨⟨6900,9628,2118,53188⟩,9997036108906496,238575106344005⟩,65,2,1,257073,27⟩
private theorem pass2151_2390 : (Triangular src2151) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2151_2391 : (Triangular src2151) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2151_2393 : (Triangular src2151) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2151_2398 : (Triangular src2151) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2151_2411 : (Triangular src2151) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2151_2445 : (Triangular src2151) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2151_2532 : (Triangular src2151) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2151 : Cover (Triangular src2151) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2151_2390, by decide, by decide, pass2151_2391, by decide, by decide, pass2151_2393, by decide, by decide, pass2151_2398, by decide, by decide, pass2151_2411, by decide, by decide, pass2151_2445, by decide, by decide, pass2151_2532, rfl⟩
def src2152 : Request := ⟨⟨⟨10000,13953,3070,80369⟩,30428373265940480,1052197377228338⟩,110,2,1,257073,27⟩
private theorem pass2152_2390 : (Triangular src2152) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2152_2391 : (Triangular src2152) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2152_2393 : (Triangular src2152) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2152_2398 : (Triangular src2152) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2152_2411 : (Triangular src2152) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2152_2444 : (Triangular src2152) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2152_2529 : (Triangular src2152) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2152 : Cover (Triangular src2152) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2152_2390, by decide, by decide, pass2152_2391, by decide, by decide, pass2152_2393, by decide, by decide, pass2152_2398, by decide, by decide, pass2152_2411, by decide, by decide, pass2152_2444, by decide, by decide, pass2152_2529, rfl⟩
def src2153 : Request := ⟨⟨⟨825,1151,253,6309⟩,17161575202816,49010625289⟩,0,2,1,257073,28⟩
private theorem pass2153_2390 : (Triangular src2153) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2153_2391 : (Triangular src2153) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2153_2393 : (Triangular src2153) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2153_2399 : (Triangular src2153) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2153_2416 : (Triangular src2153) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2153_2463 : (Triangular src2153) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2153 : Cover (Triangular src2153) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2153_2390, by decide, by decide, pass2153_2391, by decide, by decide, pass2153_2393, by decide, by decide, pass2153_2399, by decide, by decide, pass2153_2416, by decide, by decide, pass2153_2463, rfl⟩
def src2154 : Request := ⟨⟨⟨1000,1395,307,7347⟩,30557599170560,105715278267⟩,1,2,1,257073,28⟩
private theorem pass2154_2390 : (Triangular src2154) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2154_2391 : (Triangular src2154) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2154_2393 : (Triangular src2154) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2154_2399 : (Triangular src2154) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2154_2415 : (Triangular src2154) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2154_2459 : (Triangular src2154) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2154 : Cover (Triangular src2154) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2154_2390, by decide, by decide, pass2154_2391, by decide, by decide, pass2154_2393, by decide, by decide, pass2154_2399, by decide, by decide, pass2154_2415, by decide, by decide, pass2154_2459, rfl⟩
def src2155 : Request := ⟨⟨⟨1000,1395,307,7592⟩,30557599170560,105715278267⟩,2,2,1,257073,28⟩
private theorem pass2155_2390 : (Triangular src2155) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2155_2391 : (Triangular src2155) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2155_2393 : (Triangular src2155) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2155_2399 : (Triangular src2155) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2155_2415 : (Triangular src2155) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2155_2459 : (Triangular src2155) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2155 : Cover (Triangular src2155) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2155_2390, by decide, by decide, pass2155_2391, by decide, by decide, pass2155_2393, by decide, by decide, pass2155_2399, by decide, by decide, pass2155_2415, by decide, by decide, pass2155_2459, rfl⟩
def src2156 : Request := ⟨⟨⟨1200,1674,368,8780⟩,52718727069696,218807905514⟩,3,2,1,257073,28⟩
private theorem pass2156_2390 : (Triangular src2156) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2156_2391 : (Triangular src2156) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2156_2393 : (Triangular src2156) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2156_2399 : (Triangular src2156) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2156_2415 : (Triangular src2156) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2156_2458 : (Triangular src2156) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2156 : Cover (Triangular src2156) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2156_2390, by decide, by decide, pass2156_2391, by decide, by decide, pass2156_2393, by decide, by decide, pass2156_2399, by decide, by decide, pass2156_2415, by decide, by decide, pass2156_2458, rfl⟩
def src2157 : Request := ⟨⟨⟨1200,1674,368,9018⟩,52718727069696,218807905514⟩,4,2,1,257073,28⟩
private theorem pass2157_2390 : (Triangular src2157) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2157_2391 : (Triangular src2157) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2157_2393 : (Triangular src2157) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2157_2399 : (Triangular src2157) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2157_2415 : (Triangular src2157) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2157_2458 : (Triangular src2157) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2157 : Cover (Triangular src2157) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2157_2390, by decide, by decide, pass2157_2391, by decide, by decide, pass2157_2393, by decide, by decide, pass2157_2399, by decide, by decide, pass2157_2415, by decide, by decide, pass2157_2458, rfl⟩
def src2158 : Request := ⟨⟨⟨1450,2023,445,10670⟩,92998964346880,466511127281⟩,6,2,1,257073,28⟩
private theorem pass2158_2390 : (Triangular src2158) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2158_2391 : (Triangular src2158) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2158_2393 : (Triangular src2158) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2158_2399 : (Triangular src2158) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2158_2415 : (Triangular src2158) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2158_2458 : (Triangular src2158) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2158 : Cover (Triangular src2158) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2158_2390, by decide, by decide, pass2158_2391, by decide, by decide, pass2158_2393, by decide, by decide, pass2158_2399, by decide, by decide, pass2158_2415, by decide, by decide, pass2158_2458, rfl⟩
def src2159 : Request := ⟨⟨⟨1750,2442,537,13058⟩,163381988556800,989573241440⟩,10,2,1,257073,28⟩
private theorem pass2159_2390 : (Triangular src2159) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2159_2391 : (Triangular src2159) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2159_2393 : (Triangular src2159) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2159_2399 : (Triangular src2159) 2399 2413 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2159_2414 : (Triangular src2159) 2414 2453 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2159_2454 : (Triangular src2159) 2454 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2159 : Cover (Triangular src2159) 2534 2390 [2390,2392,2398,2413,2453,2534] := by
  exact ⟨by decide, by decide, pass2159_2390, by decide, by decide, pass2159_2391, by decide, by decide, pass2159_2393, by decide, by decide, pass2159_2399, by decide, by decide, pass2159_2414, by decide, by decide, pass2159_2454, rfl⟩
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
  physicalFloor := 257073
  seedFloor := 27

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨2, 27, 10, 75/100, 70/100, ![845668979032, 145836143411, 32303546960, 1196449610], 1519569932265763⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 27 27 :=
  ⟨Lower6960.Prefix6969MainCases.Middle84.plan, Lower6960.Prefix6969MainCases.Middle84.price, Lower6960.Prefix6969MainCases.Middle84.valid, Lower6960.Prefix6969MainCases.Middle84.priced, Lower6960.Prefix6969MainCases.Middle84.sources,
   Lower6960.Prefix6969RescueData.Middle84.plan, Lower6960.Prefix6969RescueData.Middle84.price, Lower6960.Prefix6969RescueData.Middle84.sources, Lower6960.Prefix6969RescueData.Middle84.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved84
end Z6969Source1783

end Merged_Z6969Pack0727

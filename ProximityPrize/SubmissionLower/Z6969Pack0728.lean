import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0724
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0727
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0728
section Merged_Z6969Pack0728

-- Source: Research6969.PrefixMainDataMiddle85
section Z6969Source1784
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle85
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 16, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank29 1513, bank35 1600, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank95 2576, bank137 3019, bank126 11206, bank161 5142, bank199 7608, bank181 21723, bank212 8810, bank170 28384] i
  head := src2770
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15507, 124591, 577877, 2023352],
    ![25417/2, 376083/4, 426937, 1399489],
    ![54680/9, 409310/9, 426937, 1399489],
    ![29433/8, 442027/16, 2001314/9, 737724],
    ![63052/25, 474744/25, 157352, 2289169/4],
    ![5710/3, 254225/18, 1151977/8, 472900],
    ![18775/16, 574255/64, 304304/3, 8739192/25],
    ![89110/121, 672715/121, 435622/7, 1451803/7],
    ![89110/121, 672715/121, 116003/2, 1451803/7],
    ![63754/121, 103006/21, 770661/16, 191844],
    ![63754/121, 103006/21, 770661/16, 1658944/9],
    ![63754/121, 571347/121, 770661/16, 9114361/64],
    ![1355575/3362, 571347/121, 770661/16, 9114361/64],
    ![1355575/3362, 6844692/1681, 7691347/196, 12158259/98],
    ![1355575/3362, 185130/49, 33779121/968, 13491837/121],
    ![474397/1369, 185130/49, 33779121/968, 13491837/121],
    ![474397/1369, 19984461/5476, 5616375/169, 13491837/121],
    ![920087/2738, 19984461/5476, 5616375/169, 13491837/121]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 28 257027 := by
  refine ⟨?_, rank154 4729, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2770⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free29_1
    · exact free35_1
    · exact free44_1
    · exact free54_1
    · exact free74_4
    · exact free84_1
    · exact free95_1
    · exact free137_1
    · exact free126_1
    · exact free161_1
    · exact free199_1
    · exact free181_1
    · exact free212_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [246575475, 318374302, 318196270, 317927252, 317857303, 317454861, 318148201, 137930576, 137255180, 135511046, 137040362, 66615585, 72107371, 66174268, 91425754, 96020727, 129218022, 220273118], [1478295, 1097766, 1098678, 1100056, 1100414, 1102476, 1098924, 2819012, 2833840, 2872130, 2838556, 6039173, 5565929, 6079219, 4349143, 4128017, 3010284, 1694831],
  ![116925376496760, 1622822214412, 198245806200, 6199390680], 132249748736585211⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,8,8,8,8,16,15,16,12,11,8,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 19984461/5476, 5616375/169, 13491837/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle85
end Z6969Source1784

-- Source: Research6969.PhysicalChecks135
section Z6969Source1785
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2160 : Request := ⟨⟨⟨2100,2930,645,16138⟩,282396798484480,2051392203643⟩,16,2,1,257027,28⟩
theorem cover2160 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2160) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2161 : Request := ⟨⟨⟨3950,5511,1213,30632⟩,1877062482395136,25637257621145⟩,40,2,1,257027,28⟩
theorem cover2161 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2161) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2162 : Request := ⟨⟨⟨5700,7953,1750,45052⟩,5637370734182400,111115710437454⟩,65,2,1,257027,28⟩
theorem cover2162 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2162) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2163 : Request := ⟨⟨⟨10000,13953,3070,75822⟩,30428373265940480,1052197377228338⟩,110,2,1,257027,28⟩
theorem cover2163 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2163) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2164 : Request := ⟨⟨⟨825,1151,253,6005⟩,17161575202816,49010625289⟩,0,2,1,257027,29⟩
theorem cover2164 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2164) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
def src2165 : Request := ⟨⟨⟨1000,1395,307,7027⟩,30557599170560,105715278267⟩,1,2,1,257027,29⟩
theorem cover2165 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2165) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2166 : Request := ⟨⟨⟨1000,1395,307,7232⟩,30557599170560,105715278267⟩,2,2,1,257027,29⟩
theorem cover2166 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2166) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2167 : Request := ⟨⟨⟨1000,1395,307,7461⟩,30557599170560,105715278267⟩,3,2,1,257027,29⟩
theorem cover2167 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2167) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2168 : Request := ⟨⟨⟨1200,1674,368,8603⟩,52718727069696,218807905514⟩,4,2,1,257027,29⟩
theorem cover2168 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2168) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2169 : Request := ⟨⟨⟨1200,1674,368,9062⟩,52718727069696,218807905514⟩,6,2,1,257027,29⟩
theorem cover2169 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2169) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2170 : Request := ⟨⟨⟨1450,2023,445,11116⟩,92998964346880,466511127281⟩,10,2,1,257027,29⟩
theorem cover2170 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2170) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2171 : Request := ⟨⟨⟨2600,3628,798,19709⟩,535425056505856,4816500515660⟩,25,2,1,257027,29⟩
theorem cover2171 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2171) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2172 : Request := ⟨⟨⟨5700,7953,1750,42697⟩,5637370734182400,111115710437454⟩,65,2,1,257027,29⟩
theorem cover2172 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2172) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2173 : Request := ⟨⟨⟨8300,11580,2548,65010⟩,17399709518790656,499263802703202⟩,110,2,1,257027,29⟩
theorem cover2173 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2173) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2174 : Request := ⟨⟨⟨10000,13953,3070,72253⟩,30428373265940480,1052197377228338⟩,110,2,1,257027,29⟩
theorem cover2174 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2174) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2175 : Request := ⟨⟨⟨690,963,212,5172⟩,10065769922560,24078187611⟩,0,2,1,257027,30⟩
theorem cover2175 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2175) 2557 2412 [2415, 2427, 2461, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1785

-- Source: Research6969.PrefixRescueDataMiddle85
section Z6969Source1786
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle85
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,28⟩
  bank i := ![bank204 6309, bank222 7347, bank222 7592, bank228 8780, bank228 9018, bank237 10670, bank246 13058, bank253 16138, bank313 30632, bank346 45052, bank383 75822] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 16, 40, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 28

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank204 6309
    · exact rank222 7347
    · exact rank222 7592
    · exact rank228 8780
    · exact rank228 9018
    · exact rank237 10670
    · exact rank246 13058
    · exact rank253 16138
    · exact rank313 30632
    · exact rank346 45052
    · exact rank383 75822
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2153⟩
    · exact ⟨_, cover2154⟩
    · exact ⟨_, cover2155⟩
    · exact ⟨_, cover2156⟩
    · exact ⟨_, cover2157⟩
    · exact ⟨_, cover2158⟩
    · exact ⟨_, cover2159⟩
    · exact ⟨_, cover2160⟩
    · exact ⟨_, cover2161⟩
    · exact ⟨_, cover2162⟩
    · exact ⟨_, cover2163⟩

def price : EarlyPrice := ⟨2, 28, 10, 70/100, 70/100, ![827373000168, 148305352158, 33499975080, 1196449610], 1233011967616532⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![9703/66, 47026/33, 156394/33, 630728/33] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle85
end Z6969Source1786

-- Source: Research6969.PrefixMiddleSaved85
section Z6969Source1787
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved85
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle85.price Lower6960.Prefix6969RescueData.Middle85.price :=
  ⟨336, 3649, 147, 1425, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle85.plan Lower6960.Prefix6969RescueData.Middle85.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 28 28 :=
  ⟨Lower6960.Prefix6969MainCases.Middle85.plan, Lower6960.Prefix6969MainCases.Middle85.price, Lower6960.Prefix6969MainCases.Middle85.valid, Lower6960.Prefix6969MainCases.Middle85.priced, Lower6960.Prefix6969MainCases.Middle85.sources,
   Lower6960.Prefix6969RescueData.Middle85.plan, Lower6960.Prefix6969RescueData.Middle85.price, Lower6960.Prefix6969RescueData.Middle85.sources, Lower6960.Prefix6969RescueData.Middle85.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved85
end Z6969Source1787

-- Source: Research6969.PrefixMainDataMiddle86
section Z6969Source1788
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle86
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 16, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank29 1513, bank37 1587, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank95 2576, bank137 3019, bank126 11206, bank161 5142, bank199 7608, bank181 21723, bank212 8810, bank170 28384] i
  head := src2771
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15511, 124423, 576784, 2014005],
    ![25417/2, 186913/2, 424375, 1399489],
    ![54680/9, 406870/9, 424375, 1399489],
    ![29433/8, 109851/4, 663160/3, 728208],
    ![63052/25, 471938/25, 157352, 2289169/4],
    ![17323/9, 84643/6, 142800, 1852029/4],
    ![18775/16, 142725/16, 304304/3, 8626464/25],
    ![89110/121, 668750/121, 433060/7, 1433076/7],
    ![89110/121, 668750/121, 116003/2, 1433076/7],
    ![63754/121, 239168/49, 770661/16, 191844],
    ![63754/121, 239168/49, 770661/16, 1658944/9],
    ![63754/121, 567443/121, 770661/16, 9114361/64],
    ![1355575/3362, 567443/121, 770661/16, 9114361/64],
    ![1355575/3362, 6801504/1681, 1910835/49, 6000714/49],
    ![1355575/3362, 1655800/441, 8392671/242, 13317804/121],
    ![474397/1369, 1655800/441, 8392671/242, 13317804/121],
    ![474397/1369, 4965478/1369, 5616375/169, 13317804/121],
    ![920087/2738, 4965478/1369, 5616375/169, 13317804/121]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 29 257027 := by
  refine ⟨?_, rank154 4668, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2771⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free29_1
    · exact free37_1
    · exact free44_1
    · exact free54_1
    · exact free74_4
    · exact free84_1
    · exact free95_1
    · exact free137_1
    · exact free126_1
    · exact free161_1
    · exact free199_1
    · exact free181_1
    · exact free212_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [245361274, 316035929, 316062331, 315192424, 315013830, 313969137, 314011641, 146060921, 146085808, 146022600, 145948526, 70051731, 70416882, 82983426, 90971066, 96035997, 129783801, 220199624], [1488291, 1109744, 1109609, 1114065, 1114980, 1120332, 1120114, 2640522, 2639976, 2641363, 2642990, 5729520, 5700461, 4811140, 4372102, 4127372, 2997864, 1695436],
  ![116886364411680, 1622902006216, 198179661600, 5201616140], 131268074462874683⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,8,8,8,8,15,15,13,12,11,8,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 4965478/1369, 5616375/169, 13317804/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle86
end Z6969Source1788

-- Source: Research6969.PrefixRescueDataMiddle86
section Z6969Source1789
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle86
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,29⟩
  bank i := ![bank204 6005, bank222 7027, bank222 7232, bank222 7461, bank228 8603, bank228 9062, bank237 11116, bank271 19709, bank346 42697, bank383 72253, bank370 65010] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 65, 110, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 29

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank204 6005
    · exact rank222 7027
    · exact rank222 7232
    · exact rank222 7461
    · exact rank228 8603
    · exact rank228 9062
    · exact rank237 11116
    · exact rank271 19709
    · exact rank346 42697
    · exact rank383 72253
    · exact rank370 65010
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2164⟩
    · exact ⟨_, cover2165⟩
    · exact ⟨_, cover2166⟩
    · exact ⟨_, cover2167⟩
    · exact ⟨_, cover2168⟩
    · exact ⟨_, cover2169⟩
    · exact ⟨_, cover2170⟩
    · exact ⟨_, cover2171⟩
    · exact ⟨_, cover2172⟩
    · exact ⟨_, cover2174⟩
    · exact ⟨_, cover2173⟩

def price : EarlyPrice := ⟨2, 29, 10, 70/100, 70/100, ![816586065280, 151155709999, 34696403200, 1196449610], 1211126937167621⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![14128/111, 138902/111, 155280/37, 628430/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle86
end Z6969Source1789

-- Source: Research6969.PrefixMiddleSaved86
section Z6969Source1790
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved86
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle86.price Lower6960.Prefix6969RescueData.Middle86.price :=
  ⟨336, 3627, 127, 1251, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle86.plan Lower6960.Prefix6969RescueData.Middle86.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 29 29 :=
  ⟨Lower6960.Prefix6969MainCases.Middle86.plan, Lower6960.Prefix6969MainCases.Middle86.price, Lower6960.Prefix6969MainCases.Middle86.valid, Lower6960.Prefix6969MainCases.Middle86.priced, Lower6960.Prefix6969MainCases.Middle86.sources,
   Lower6960.Prefix6969RescueData.Middle86.plan, Lower6960.Prefix6969RescueData.Middle86.price, Lower6960.Prefix6969RescueData.Middle86.sources, Lower6960.Prefix6969RescueData.Middle86.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved86
end Z6969Source1790

-- Source: Research6969.PrefixMainDataMiddle87
section Z6969Source1791
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle87
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank31 1491, bank37 1587, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank129 10859, bank161 5142, bank199 7608, bank183 20877, bank212 8810, bank174 26788, bank169 29097] i
  head := src2772
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15525, 124227, 575707, 2004460],
    ![25417/2, 371643/4, 421897, 1399489],
    ![54680/9, 404510/9, 421897, 1399489],
    ![29433/8, 436867/16, 1978034/9, 719004],
    ![64334/25, 470093/25, 158046, 2223081/4],
    ![17323/9, 168283/12, 2271407/16, 7314483/16],
    ![18775/16, 567655/64, 304304/3, 8517432/25],
    ![89110/121, 664915/121, 430582/7, 1414963/7],
    ![89110/121, 664915/121, 116003/2, 1414963/7],
    ![63754/121, 714082/147, 770661/16, 191844],
    ![63754/121, 714082/147, 770661/16, 516208/3],
    ![63754/121, 563667/121, 770661/16, 13914571/98],
    ![33263/82, 563667/121, 770661/16, 13914571/98],
    ![33263/82, 6759732/1681, 7596907/196, 11849739/98],
    ![33263/82, 78370/21, 33369081/968, 57881664/529],
    ![954471/2738, 78370/21, 33369081/968, 57881664/529],
    ![954471/2738, 19743381/5476, 5616375/169, 284237030/2601],
    ![462882/1369, 19743381/5476, 5616375/169, 284237030/2601],
    ![459151/1369, 19743381/5476, 5616375/169, 284237030/2601]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 30 257027 := by
  refine ⟨?_, rank154 4609, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2772⟩⟩
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
    · exact free183_1
    · exact free212_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [244209569, 313781638, 314454689, 314691250, 314349735, 312846027, 313761856, 142145762, 139680948, 140586927, 140928863, 72279633, 72666645, 81574560, 90512376, 93062905, 119222349, 100000000, 219782480], [1497772, 1121292, 1117844, 1116633, 1118382, 1126085, 1121393, 2726474, 2780586, 2760696, 2753189, 5552220, 5521421, 4894908, 4395263, 4266478, 3289563, 3959851, 1698871],
  ![116664936033600, 1623354941200, 197804232000, 5229171780], 130313379784776297⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,8,8,8,8,15,15,13,12,12,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 19743381/5476, 5616375/169, 284237030/2601] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle87
end Z6969Source1791

-- Source: Research6969.PhysicalChecks136
section Z6969Source1792
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2176 : Request := ⟨⟨⟨825,1151,253,5962⟩,17161575202816,49010625289⟩,1,2,1,257027,30⟩
theorem cover2176 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2176) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
def src2177 : Request := ⟨⟨⟨1000,1395,301,7413⟩,30103476895744,104105680031⟩,3,2,1,257027,30⟩
theorem cover2177 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2177) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
def src2178 : Request := ⟨⟨⟨1000,1395,307,7353⟩,30557599170560,105715278267⟩,4,2,1,257027,30⟩
theorem cover2178 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2178) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2179 : Request := ⟨⟨⟨1200,1674,368,8658⟩,52718727069696,218807905514⟩,6,2,1,257027,30⟩
theorem cover2179 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2179) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2180 : Request := ⟨⟨⟨1450,2023,445,10601⟩,92998964346880,466511127281⟩,10,2,1,257027,30⟩
theorem cover2180 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2180) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2181 : Request := ⟨⟨⟨1750,2441,537,13209⟩,163381988556800,988269431527⟩,16,2,1,257027,30⟩
theorem cover2181 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2181) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2182 : Request := ⟨⟨⟨3200,4465,982,22932⟩,997767489781760,11043969901736⟩,32,2,1,257027,30⟩
theorem cover2182 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2182) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2183 : Request := ⟨⟨⟨6900,9627,2118,50328⟩,9997036108906496,238495318333820⟩,85,2,1,257027,30⟩
theorem cover2183 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2183) 2557 2412 [2413, 2418, 2431, 2464, 2550, 2557] := triangleCover (by decide +kernel)
def src2184 : Request := ⟨⟨⟨8300,11580,2548,61825⟩,17399709518790656,499263802703202⟩,110,2,1,257027,30⟩
theorem cover2184 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2184) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2185 : Request := ⟨⟨⟨10000,13952,3070,77132⟩,30428373265940480,1051954539834997⟩,145,2,1,257027,30⟩
theorem cover2185 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2185) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2186 : Request := ⟨⟨⟨690,963,212,4956⟩,10065769922560,24078187611⟩,0,2,1,257027,31⟩
theorem cover2186 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2186) 2557 2412 [2415, 2427, 2461, 2557] := triangleCover (by decide +kernel)
def src2187 : Request := ⟨⟨⟨825,1151,253,5736⟩,17161575202816,49010625289⟩,1,2,1,257027,31⟩
theorem cover2187 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2187) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
def src2188 : Request := ⟨⟨⟨825,1151,253,5931⟩,17161575202816,49010625289⟩,2,2,1,257027,31⟩
theorem cover2188 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2188) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
def src2189 : Request := ⟨⟨⟨1000,1395,307,7061⟩,30557599170560,105715278267⟩,4,2,1,257027,31⟩
theorem cover2189 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2189) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2190 : Request := ⟨⟨⟨1200,1674,368,8331⟩,52718727069696,218807905514⟩,6,2,1,257027,31⟩
theorem cover2190 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2190) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2191 : Request := ⟨⟨⟨1200,1674,368,8728⟩,52718727069696,218807905514⟩,8,2,1,257027,31⟩
theorem cover2191 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2191) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1792

-- Source: Research6969.PrefixRescueDataMiddle87
section Z6969Source1793
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle87
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,30⟩
  bank i := ![bank196 5172, bank204 5962, bank221 7413, bank222 7353, bank228 8658, bank237 10601, bank242 13209, bank304 22932, bank357 50328, bank380 77132, bank370 61825] i
  reserve i := ![0, 1, 3, 4, 6, 10, 16, 32, 85, 145, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 30

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank196 5172
    · exact rank204 5962
    · exact rank221 7413
    · exact rank222 7353
    · exact rank228 8658
    · exact rank237 10601
    · exact rank242 13209
    · exact rank304 22932
    · exact rank357 50328
    · exact rank380 77132
    · exact rank370 61825
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2175⟩
    · exact ⟨_, cover2176⟩
    · exact ⟨_, cover2177⟩
    · exact ⟨_, cover2178⟩
    · exact ⟨_, cover2179⟩
    · exact ⟨_, cover2180⟩
    · exact ⟨_, cover2181⟩
    · exact ⟨_, cover2182⟩
    · exact ⟨_, cover2183⟩
    · exact ⟨_, cover2185⟩
    · exact ⟨_, cover2184⟩

def price : EarlyPrice := ⟨2, 30, 10, 70/100, 70/100, ![901786849700, 157286745386, 35892828250, 1196449610], 1091096087467398⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8511/73, 84616/73, 286412/73, 1156980/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle87
end Z6969Source1793

-- Source: Research6969.PrefixMiddleSaved87
section Z6969Source1794
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved87
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle87.price Lower6960.Prefix6969RescueData.Middle87.price :=
  ⟨335, 3605, 116, 1159, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle87.plan Lower6960.Prefix6969RescueData.Middle87.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 30 30 :=
  ⟨Lower6960.Prefix6969MainCases.Middle87.plan, Lower6960.Prefix6969MainCases.Middle87.price, Lower6960.Prefix6969MainCases.Middle87.valid, Lower6960.Prefix6969MainCases.Middle87.priced, Lower6960.Prefix6969MainCases.Middle87.sources,
   Lower6960.Prefix6969RescueData.Middle87.plan, Lower6960.Prefix6969RescueData.Middle87.price, Lower6960.Prefix6969RescueData.Middle87.sources, Lower6960.Prefix6969RescueData.Middle87.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved87
end Z6969Source1794

-- Source: Research6969.PrefixMainDataMiddle88
section Z6969Source1795
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle88
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 11, 16, 17, 23, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank30 1501, bank40 1714, bank50 1914, bank57 2225, bank74 2799, bank96 2705, bank92 3992, bank137 3019, bank129 10859, bank161 5142, bank199 7608, bank183 20877, bank212 8810, bank174 26788, bank169 29097] i
  head := src2773
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15634, 124206, 574016, 1975838],
    ![25417/2, 184767/2, 419503, 1399489],
    ![54680/9, 402230/9, 419503, 1399489],
    ![29433/8, 27151, 1966976/9, 710112],
    ![63824/25, 469114/25, 313709/2, 2253001/4],
    ![72196/49, 532636/49, 2402032/25, 2937796/9],
    ![81680/81, 66500/9, 674386/9, 726044/3],
    ![81680/81, 66500/9, 674386/9, 726044/3],
    ![227956/289, 1716396/289, 116003/2, 25482096/121],
    ![227956/289, 150991/27, 1017095/18, 1539145/9],
    ![21715/32, 150991/27, 107285/2, 1539145/9],
    ![21715/32, 560019/121, 2462654/49, 6871244/49],
    ![33263/82, 560019/121, 2462654/49, 6871244/49],
    ![33263/82, 6719376/1681, 269716/7, 5851596/49],
    ![33263/82, 545360/147, 4146789/121, 57881664/529],
    ![954471/2738, 545360/147, 4146789/121, 57881664/529],
    ![954471/2738, 4907217/1369, 5616375/169, 280721840/2601],
    ![462882/1369, 4907217/1369, 5616375/169, 280721840/2601],
    ![459151/1369, 4907217/1369, 5616375/169, 280721840/2601]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 31 257027 := by
  refine ⟨?_, rank154 4552, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2773⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free30_2
    · exact free40_1
    · exact free50_1
    · exact free57_1
    · exact free74_4
    · exact free96_1
    · exact free92_1
    · exact free137_1
    · exact free129_1
    · exact free161_1
    · exact free199_1
    · exact free183_1
    · exact free212_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [243520700, 313265142, 313710176, 313808975, 313388005, 313758981, 145473979, 145491475, 145452398, 103842298, 104728046, 73708983, 75679515, 80918642, 89959085, 92591054, 118757592, 100000000, 219713806], [1503443, 1123938, 1121658, 1121152, 1123308, 1121408, 2653408, 2653024, 2653881, 3797472, 3765974, 5438469, 5291223, 4933907, 4423200, 4290304, 3302572, 3959851, 1699436],
  ![116628482500920, 1623429329084, 197742425400, 5262409670], 129922326100617485⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,8,8,8,11,10,15,14,13,12,12,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 4907217/1369, 5616375/169, 280721840/2601] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle88
end Z6969Source1795

end Merged_Z6969Pack0728

import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0744
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0745
section Merged_Z6969Pack0745

-- Source: Research6969.PrefixRescueDataMiddle49
section Z6969Source1988
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle49
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,24⟩
  bank i := ![bank203 7156, bank222 8014, bank221 8600, bank228 9837, bank237 12186, bank253 18896, bank346 49097, bank356 71278, bank383 82687, bank367 97084, bank370 75105] i
  reserve i := ![0, 1, 2, 4, 8, 20, 65, 110, 110, 145, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 24

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank203 7156
    · exact rank222 8014
    · exact rank221 8600
    · exact rank228 9837
    · exact rank237 12186
    · exact rank253 18896
    · exact rank346 49097
    · exact rank356 71278
    · exact rank383 82687
    · exact rank367 97084
    · exact rank370 75105
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2547⟩
    · exact ⟨_, cover2548⟩
    · exact ⟨_, cover2549⟩
    · exact ⟨_, cover2550⟩
    · exact ⟨_, cover2551⟩
    · exact ⟨_, cover2552⟩
    · exact ⟨_, cover2553⟩
    · exact ⟨_, cover2554⟩
    · exact ⟨_, cover2556⟩
    · exact ⟨_, cover2557⟩
    · exact ⟨_, cover2555⟩

def price : EarlyPrice := ⟨3, 24, 10, 75/100, 70/100, ![908044224204, 166240141416, 28714265670, 2392877730], 1318057093654514⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16575/146, 78518/73, 284574/73, 570224/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle49
end Z6969Source1988

-- Source: Research6969.PrefixMiddleSaved49
section Z6969Source1989
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved49
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle49.price Lower6960.Prefix6969RescueData.Middle49.price :=
  ⟨335, 3668, 113, 1075, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle49.plan Lower6960.Prefix6969RescueData.Middle49.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 24 24 :=
  ⟨Lower6960.Prefix6969MainCases.Middle49.plan, Lower6960.Prefix6969MainCases.Middle49.price, Lower6960.Prefix6969MainCases.Middle49.valid, Lower6960.Prefix6969MainCases.Middle49.priced, Lower6960.Prefix6969MainCases.Middle49.sources,
   Lower6960.Prefix6969RescueData.Middle49.plan, Lower6960.Prefix6969RescueData.Middle49.price, Lower6960.Prefix6969RescueData.Middle49.sources, Lower6960.Prefix6969RescueData.Middle49.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved49
end Z6969Source1989

-- Source: Research6969.PrefixMainDataMiddle50
section Z6969Source1990
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle50
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 16, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank29 1513, bank35 1600, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank95 2576, bank137 3019, bank126 11206, bank161 5142, bank199 7608, bank180 21819, bank212 8810, bank170 28384] i
  head := src2947
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15507, 124576, 577792, 2022667],
    ![25417/2, 187949/2, 426727, 1399489],
    ![54680/9, 136370/3, 426727, 1399489],
    ![29433/8, 110453/4, 2000344/9, 736944],
    ![63052/25, 474514/25, 157352, 2289169/4],
    ![5710/3, 42350/3, 287853/2, 472400],
    ![18775/16, 143495/16, 304304/3, 8729952/25],
    ![89110/121, 672390/121, 435412/7, 1450268/7],
    ![89110/121, 672390/121, 116003/2, 1450268/7],
    ![63754/121, 720752/147, 770661/16, 191844],
    ![63754/121, 720752/147, 770661/16, 1658944/9],
    ![63754/121, 571027/121, 770661/16, 9114361/64],
    ![1355575/3362, 571027/121, 770661/16, 9114361/64],
    ![1355575/3362, 6841152/1681, 1921853/49, 6072702/49],
    ![1355575/3362, 1665320/441, 767319/22, 13477572/121],
    ![25627/74, 1665320/441, 767319/22, 13477572/121],
    ![25627/74, 4993604/1369, 5616375/169, 13477572/121],
    ![920087/2738, 4993604/1369, 5616375/169, 13477572/121]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 25 385541 := by
  refine ⟨?_, rank154 4724, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2947⟩⟩
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
    · exact free180_1
    · exact free212_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [246474460, 318371886, 318238834, 317398389, 318353654, 317203932, 316262926, 147268297, 147357966, 147330602, 147319545, 67129420, 71022797, 83657280, 91427336, 96794715, 147216329, 220267094], [1479126, 1097779, 1098460, 1102765, 1097872, 1103761, 1108582, 2615730, 2614237, 2614693, 2614877, 5992547, 5652241, 4771074, 4349064, 4095308, 2616595, 1694881],
  ![116922178837080, 1622828972596, 198240384600, 5174206870], 132165272192915141⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,7,7,7,7,16,15,13,12,11,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 4993604/1369, 5616375/169, 13477572/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle50
end Z6969Source1990

-- Source: Research6969.PhysicalChecks160
section Z6969Source1991
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2560 : Request := ⟨⟨⟨1000,1395,301,8762⟩,30103476895744,104105680031⟩,4,3,1,385541,25⟩
theorem cover2560 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2560) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
def src2561 : Request := ⟨⟨⟨1200,1674,368,10494⟩,52718727069696,218807905514⟩,8,3,1,385541,25⟩
theorem cover2561 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2561) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2562 : Request := ⟨⟨⟨2100,2930,645,17840⟩,282396798484480,2051392203643⟩,20,3,1,385541,25⟩
theorem cover2562 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2562) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2563 : Request := ⟨⟨⟨3950,5511,1213,34683⟩,1877062482395136,25637257621145⟩,50,3,1,385541,25⟩
theorem cover2563 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2563) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2564 : Request := ⟨⟨⟨5700,7952,1750,53152⟩,5637370734182400,111070724916873⟩,85,3,1,385541,25⟩
theorem cover2564 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2564) 2557 2412 [2413, 2418, 2431, 2465, 2552, 2557] := triangleCover (by decide +kernel)
def src2565 : Request := ⟨⟨⟨6900,9626,2118,66480⟩,9997036108906496,238415548481346⟩,110,3,1,385541,25⟩
theorem cover2565 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2565) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2566 : Request := ⟨⟨⟨10000,13953,3070,78624⟩,30428373265940480,1052197377228338⟩,110,3,1,385541,25⟩
theorem cover2566 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2566) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2567 : Request := ⟨⟨⟨8300,11579,2498,89937⟩,17139238515245056,491470625461013⟩,145,3,1,385541,25⟩
theorem cover2567 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2567) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2568 : Request := ⟨⟨⟨690,963,212,5631⟩,10065769922560,24078187611⟩,0,3,1,385541,26⟩
theorem cover2568 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2568) 2557 2412 [2415, 2426, 2458, 2548, 2557] := triangleCover (by decide +kernel)
def src2569 : Request := ⟨⟨⟨825,1151,248,6735⟩,16903818182656,48256472894⟩,1,3,1,385541,26⟩
theorem cover2569 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2569) 2557 2412 [2415, 2426, 2457, 2544, 2557] := triangleCover (by decide +kernel)
def src2570 : Request := ⟨⟨⟨825,1151,253,6739⟩,17161575202816,49010625289⟩,2,3,1,385541,26⟩
theorem cover2570 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2570) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
def src2571 : Request := ⟨⟨⟨1000,1395,301,8042⟩,30103476895744,104105680031⟩,3,3,1,385541,26⟩
theorem cover2571 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2571) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
def src2572 : Request := ⟨⟨⟨1000,1395,301,8314⟩,30103476895744,104105680031⟩,4,3,1,385541,26⟩
theorem cover2572 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2572) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
def src2573 : Request := ⟨⟨⟨1000,1395,307,8579⟩,30557599170560,105715278267⟩,6,3,1,385541,26⟩
theorem cover2573 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2573) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2574 : Request := ⟨⟨⟨1200,1674,368,9938⟩,52718727069696,218807905514⟩,8,3,1,385541,26⟩
theorem cover2574 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2574) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2575 : Request := ⟨⟨⟨2100,2930,645,16937⟩,282396798484480,2051392203643⟩,20,3,1,385541,26⟩
theorem cover2575 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2575) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1991

-- Source: Research6969.PrefixRescueDataMiddle50
section Z6969Source1992
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle50
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,25⟩
  bank i := ![bank195 6159, bank203 7085, bank221 8762, bank228 10494, bank253 17840, bank313 34683, bank356 66480, bank383 78624, bank367 89937, bank383 78624, bank343 53152] i
  reserve i := ![0, 1, 4, 8, 20, 50, 110, 110, 145, 110, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 25

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank195 6159
    · exact rank203 7085
    · exact rank221 8762
    · exact rank228 10494
    · exact rank253 17840
    · exact rank313 34683
    · exact rank356 66480
    · exact rank383 78624
    · exact rank367 89937
    · exact rank383 78624
    · exact rank343 53152
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2558⟩
    · exact ⟨_, cover2559⟩
    · exact ⟨_, cover2560⟩
    · exact ⟨_, cover2561⟩
    · exact ⟨_, cover2562⟩
    · exact ⟨_, cover2563⟩
    · exact ⟨_, cover2565⟩
    · exact ⟨_, cover2566⟩
    · exact ⟨_, cover2567⟩
    · exact ⟨_, cover2566⟩
    · exact ⟨_, cover2564⟩

def price : EarlyPrice := ⟨3, 25, 10, 80/100, 80/100, ![876246927489, 167314559987, 29910693790, 2392877730], 1128920092695031⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16575/146, 152387/146, 279643/73, 554000/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle50
end Z6969Source1992

-- Source: Research6969.PrefixMiddleSaved50
section Z6969Source1993
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved50
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle50.price Lower6960.Prefix6969RescueData.Middle50.price :=
  ⟨336, 3647, 113, 1043, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle50.plan Lower6960.Prefix6969RescueData.Middle50.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 25 25 :=
  ⟨Lower6960.Prefix6969MainCases.Middle50.plan, Lower6960.Prefix6969MainCases.Middle50.price, Lower6960.Prefix6969MainCases.Middle50.valid, Lower6960.Prefix6969MainCases.Middle50.priced, Lower6960.Prefix6969MainCases.Middle50.sources,
   Lower6960.Prefix6969RescueData.Middle50.plan, Lower6960.Prefix6969RescueData.Middle50.price, Lower6960.Prefix6969RescueData.Middle50.sources, Lower6960.Prefix6969RescueData.Middle50.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved50
end Z6969Source1993

-- Source: Research6969.PrefixMainDataMiddle51
section Z6969Source1994
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle51
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 16, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank29 1513, bank37 1587, bank44 1848, bank54 2149, bank65 2772, bank84 3942, bank95 2576, bank137 3019, bank126 11206, bank161 5142, bank199 7608, bank181 21723, bank212 8810, bank170 28384] i
  head := src2948
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15464, 124390, 576692, 2023698],
    ![25417/2, 186913/2, 424375, 1399489],
    ![54680/9, 406870/9, 424375, 1399489],
    ![29433/8, 109851/4, 663160/3, 728208],
    ![63052/25, 471938/25, 157352, 2289169/4],
    ![17323/9, 84643/6, 142800, 1852029/4],
    ![18775/16, 142725/16, 304304/3, 8626464/25],
    ![89110/121, 668750/121, 433060/7, 1433076/7],
    ![89110/121, 668750/121, 433060/7, 1433076/7],
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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 26 385541 := by
  refine ⟨?_, rank154 4668, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2948⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free29_1
    · exact free37_1
    · exact free44_1
    · exact free54_1
    · exact free65_1
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

def price : Pricing := ⟨55/100, 90/100, [245106372, 316244349, 316798935, 316582257, 315486706, 314634250, 315693019, 146097610, 146095435, 146065265, 146007353, 70083426, 70460683, 65684064, 91005043, 95184785, 146844197, 220199624], [1490389, 1108677, 1105836, 1106946, 1112558, 1116925, 1111501, 2639717, 2639764, 2640427, 2641698, 5726998, 5696975, 6123700, 4370387, 4163345, 2623326, 1695436],
  ![116886364411680, 1622902006216, 198179661600, 6244752120], 131348528527828532⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,8,8,8,8,15,15,16,12,11,8,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 4965478/1369, 5616375/169, 13317804/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle51
end Z6969Source1994

-- Source: Research6969.PhysicalChecks161
section Z6969Source1995
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2576 : Request := ⟨⟨⟨4800,6697,1474,40526⟩,3367547627110400,55891290082931⟩,65,3,1,385541,26⟩
theorem cover2576 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2576) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2577 : Request := ⟨⟨⟨8300,11579,2548,79433⟩,17399709518790656,499124969898998⟩,145,3,1,385541,26⟩
theorem cover2577 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2577) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2578 : Request := ⟨⟨⟨10000,13952,3070,84043⟩,30428373265940480,1051954539834997⟩,145,3,1,385541,26⟩
theorem cover2578 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2578) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2579 : Request := ⟨⟨⟨690,963,212,5371⟩,10065769922560,24078187611⟩,0,3,1,385541,27⟩
theorem cover2579 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2579) 2557 2412 [2415, 2427, 2461, 2557] := triangleCover (by decide +kernel)
def src2580 : Request := ⟨⟨⟨825,1151,248,6435⟩,16903818182656,48256472894⟩,1,3,1,385541,27⟩
theorem cover2580 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2580) 2557 2412 [2415, 2426, 2457, 2544, 2557] := triangleCover (by decide +kernel)
def src2581 : Request := ⟨⟨⟨825,1151,248,6686⟩,16903818182656,48256472894⟩,2,3,1,385541,27⟩
theorem cover2581 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2581) 2557 2412 [2415, 2426, 2457, 2544, 2557] := triangleCover (by decide +kernel)
def src2582 : Request := ⟨⟨⟨1000,1395,301,7931⟩,30103476895744,104105680031⟩,4,3,1,385541,27⟩
theorem cover2582 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2582) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
def src2583 : Request := ⟨⟨⟨1000,1395,307,8145⟩,30557599170560,105715278267⟩,6,3,1,385541,27⟩
theorem cover2583 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2583) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2584 : Request := ⟨⟨⟨1200,1674,368,9466⟩,52718727069696,218807905514⟩,8,3,1,385541,27⟩
theorem cover2584 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2584) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2585 : Request := ⟨⟨⟨1450,2023,445,11760⟩,92998964346880,466511127281⟩,13,3,1,385541,27⟩
theorem cover2585 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2585) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2586 : Request := ⟨⟨⟨2600,3627,783,22153⟩,527755772952576,4741611634368⟩,32,3,1,385541,27⟩
theorem cover2586 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2586) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2587 : Request := ⟨⟨⟨4800,6697,1474,38535⟩,3367547627110400,55891290082931⟩,65,3,1,385541,27⟩
theorem cover2587 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2587) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2588 : Request := ⟨⟨⟨8300,11579,2548,74611⟩,17399709518790656,499124969898998⟩,145,3,1,385541,27⟩
theorem cover2588 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2588) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2589 : Request := ⟨⟨⟨10000,13952,3070,79951⟩,30428373265940480,1051954539834997⟩,145,3,1,385541,27⟩
theorem cover2589 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2589) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2590 : Request := ⟨⟨⟨690,963,212,5150⟩,10065769922560,24078187611⟩,0,3,1,385541,28⟩
theorem cover2590 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2590) 2557 2412 [2415, 2427, 2461, 2557] := triangleCover (by decide +kernel)
def src2591 : Request := ⟨⟨⟨825,1151,253,5961⟩,17161575202816,49010625289⟩,1,3,1,385541,28⟩
theorem cover2591 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2591) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1995

-- Source: Research6969.PrefixRescueDataMiddle51
section Z6969Source1996
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle51
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,26⟩
  bank i := ![bank196 5631, bank203 6735, bank204 6739, bank221 8042, bank221 8314, bank222 8579, bank228 9938, bank253 16937, bank329 40526, bank368 79433, bank380 84043] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 20, 65, 145, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 26

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank196 5631
    · exact rank203 6735
    · exact rank204 6739
    · exact rank221 8042
    · exact rank221 8314
    · exact rank222 8579
    · exact rank228 9938
    · exact rank253 16937
    · exact rank329 40526
    · exact rank368 79433
    · exact rank380 84043
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2568⟩
    · exact ⟨_, cover2569⟩
    · exact ⟨_, cover2570⟩
    · exact ⟨_, cover2571⟩
    · exact ⟨_, cover2572⟩
    · exact ⟨_, cover2573⟩
    · exact ⟨_, cover2574⟩
    · exact ⟨_, cover2575⟩
    · exact ⟨_, cover2576⟩
    · exact ⟨_, cover2577⟩
    · exact ⟨_, cover2578⟩

def price : EarlyPrice := ⟨3, 26, 10, 75/100, 70/100, ![851575110316, 175769475661, 31107118840, 2392877730], 1112970532543105⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16675/146, 145681/146, 539353/146, 1032629/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle51
end Z6969Source1996

-- Source: Research6969.PrefixMiddleSaved51
section Z6969Source1997
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved51
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle51.price Lower6960.Prefix6969RescueData.Middle51.price :=
  ⟨336, 3627, 114, 997, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle51.plan Lower6960.Prefix6969RescueData.Middle51.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 26 26 :=
  ⟨Lower6960.Prefix6969MainCases.Middle51.plan, Lower6960.Prefix6969MainCases.Middle51.price, Lower6960.Prefix6969MainCases.Middle51.valid, Lower6960.Prefix6969MainCases.Middle51.priced, Lower6960.Prefix6969MainCases.Middle51.sources,
   Lower6960.Prefix6969RescueData.Middle51.plan, Lower6960.Prefix6969RescueData.Middle51.price, Lower6960.Prefix6969RescueData.Middle51.sources, Lower6960.Prefix6969RescueData.Middle51.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved51
end Z6969Source1997

-- Source: Research6969.PrefixMainDataMiddle52
section Z6969Source1998
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle52
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank31 1491, bank37 1587, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank129 10859, bank161 5142, bank199 7608, bank183 20877, bank212 8810, bank174 26788, bank169 29097] i
  head := src2949
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15525, 124242, 575792, 2005145],
    ![25417/2, 92957, 422107, 1399489],
    ![54680/9, 404710/9, 422107, 1399489],
    ![29433/8, 218541/8, 659668/3, 719784],
    ![64334/25, 470328/25, 158046, 2223081/4],
    ![17323/9, 42092/3, 1136271/8, 3661209/8],
    ![18775/16, 283965/32, 304304/3, 8526672/25],
    ![89110/121, 665240/121, 430792/7, 1416498/7],
    ![89110/121, 665240/121, 116003/2, 1416498/7],
    ![63754/121, 238124/49, 770661/16, 191844],
    ![63754/121, 238124/49, 770661/16, 172256],
    ![63754/121, 563987/121, 770661/16, 6964833/49],
    ![33263/82, 563987/121, 770661/16, 6964833/49],
    ![33263/82, 6763272/1681, 3800421/98, 5931297/49],
    ![33263/82, 1646620/441, 1517553/44, 57881664/529],
    ![954471/2738, 1646620/441, 1517553/44, 57881664/529],
    ![954471/2738, 9876713/2738, 5616375/169, 94848460/867],
    ![462882/1369, 9876713/2738, 5616375/169, 94848460/867],
    ![459151/1369, 9876713/2738, 5616375/169, 94848460/867]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 27 385541 := by
  refine ⟨?_, rank154 4614, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2949⟩⟩
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

def price : Pricing := ⟨55/100, 90/100, [244310674, 313810136, 313831322, 313978013, 313751880, 314280867, 313808556, 146672199, 146460250, 146664988, 146587349, 72339958, 72750215, 81663118, 90574667, 93162524, 119282561, 100000000, 219788504], [1496940, 1121146, 1121038, 1120286, 1121445, 1118735, 1121154, 2627102, 2631755, 2627261, 2628965, 5547419, 5514770, 4889642, 4392118, 4261448, 3287877, 3959851, 1698821],
  ![116668133693280, 1623348183016, 197809653600, 5225429230], 130292002698322064⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,8,8,8,8,15,15,13,12,12,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 9876713/2738, 5616375/169, 94848460/867] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle52
end Z6969Source1998

-- Source: Research6969.PrefixRescueDataMiddle52
section Z6969Source1999
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle52
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,27⟩
  bank i := ![bank196 5371, bank203 6435, bank203 6686, bank221 7931, bank222 8145, bank228 9466, bank237 11760, bank266 22153, bank329 38535, bank368 74611, bank380 79951] i
  reserve i := ![0, 1, 2, 4, 6, 8, 13, 32, 65, 145, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 27

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank196 5371
    · exact rank203 6435
    · exact rank203 6686
    · exact rank221 7931
    · exact rank222 8145
    · exact rank228 9466
    · exact rank237 11760
    · exact rank266 22153
    · exact rank329 38535
    · exact rank368 74611
    · exact rank380 79951
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2579⟩
    · exact ⟨_, cover2580⟩
    · exact ⟨_, cover2581⟩
    · exact ⟨_, cover2582⟩
    · exact ⟨_, cover2583⟩
    · exact ⟨_, cover2584⟩
    · exact ⟨_, cover2585⟩
    · exact ⟨_, cover2586⟩
    · exact ⟨_, cover2587⟩
    · exact ⟨_, cover2588⟩
    · exact ⟨_, cover2589⟩

def price : EarlyPrice := ⟨3, 27, 10, 75/100, 70/100, ![841270645928, 176820900785, 32303546960, 2392877730], 1083283519180572⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16675/146, 143407/146, 268233/73, 2014497/146] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle52
end Z6969Source1999

end Merged_Z6969Pack0745

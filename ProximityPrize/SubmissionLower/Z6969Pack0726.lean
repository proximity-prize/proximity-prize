import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0725
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0726
section Merged_Z6969Pack0726

-- Source: Research6969.PrefixRescueDataMiddle78
section Z6969Source1760
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle78
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,21⟩
  bank i := ![bank246 17151, bank245 18367, bank245 18995, bank252 22540, bank245 20453, bank271 27226, bank303 37728, bank348 61233, bank332 68286, bank359 102712, bank387 108301] i
  reserve i := ![0, 1, 2, 4, 4, 8, 16, 32, 40, 65, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 21

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank246 17151
    · exact rank245 18367
    · exact rank245 18995
    · exact rank252 22540
    · exact rank245 20453
    · exact rank271 27226
    · exact rank303 37728
    · exact rank348 61233
    · exact rank332 68286
    · exact rank359 102712
    · exact rank387 108301
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2077⟩
    · exact ⟨_, cover2078⟩
    · exact ⟨_, cover2079⟩
    · exact ⟨_, cover2081⟩
    · exact ⟨_, cover2080⟩
    · exact ⟨_, cover2082⟩
    · exact ⟨_, cover2083⟩
    · exact ⟨_, cover2084⟩
    · exact ⟨_, cover2085⟩
    · exact ⟨_, cover2086⟩
    · exact ⟨_, cover2087⟩

def price : EarlyPrice := ⟨2, 21, 10, 80/100, 80/100, ![886339066234, 131290600713, 25124984380, 1196449610], 3063514867344240⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![11705/66, 146329/66, 203806/33, 359492/11] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle78
end Z6969Source1760

-- Source: Research6969.PrefixMiddleSaved78
section Z6969Source1761
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved78
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle78.price Lower6960.Prefix6969RescueData.Middle78.price :=
  ⟨336, 3814, 177, 2217, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle78.plan Lower6960.Prefix6969RescueData.Middle78.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 21 21 :=
  ⟨Lower6960.Prefix6969MainCases.Middle78.plan, Lower6960.Prefix6969MainCases.Middle78.price, Lower6960.Prefix6969MainCases.Middle78.valid, Lower6960.Prefix6969MainCases.Middle78.priced, Lower6960.Prefix6969MainCases.Middle78.sources,
   Lower6960.Prefix6969RescueData.Middle78.plan, Lower6960.Prefix6969RescueData.Middle78.price, Lower6960.Prefix6969RescueData.Middle78.sources, Lower6960.Prefix6969RescueData.Middle78.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved78
end Z6969Source1761

-- Source: Research6969.PrefixMainDataMiddle79
section Z6969Source1762
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle79
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 65, 76, 76] i
  bank i := ![bank5 1094, bank9 1210, bank17 1319, bank24 1404, bank30 1501, bank40 1714, bank49 2130, bank58 2054, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank126 11206, bank161 5142, bank199 7608, bank160 17407, bank177 24344, bank170 28384] i
  head := src2764
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15063, 125498, 583242, 2118218],
    ![12303, 97487, 440809, 1548195],
    ![53398/9, 423832/9, 440809, 1548195],
    ![29433/8, 229377/8, 692260/3, 798408],
    ![63824/25, 495716/25, 313709/2, 2253001/4],
    ![72196/49, 562634/49, 2536174/25, 8772252/25],
    ![40539/50, 332031/50, 71355, 1134225/4],
    ![95180/121, 707440/121, 3182504/49, 10512372/49],
    ![95180/121, 707440/121, 116003/2, 10512372/49],
    ![63754/121, 247868/49, 770661/16, 10087578/49],
    ![63754/121, 247868/49, 770661/16, 191072],
    ![63754/121, 596243/121, 770661/16, 9114361/64],
    ![1355575/3362, 596243/121, 770661/16, 9114361/64],
    ![1355575/3362, 7120104/1681, 3998745/98, 6579189/49],
    ![1355575/3362, 1732300/441, 4332756/121, 14470416/121],
    ![481552/1323, 1732300/441, 4332756/121, 14470416/121],
    ![935333/2738, 1732300/441, 4332756/121, 14470416/121],
    ![920087/2738, 1732300/441, 4332756/121, 14470416/121]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 22 257027 := by
  refine ⟨?_, rank154 5118, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2764⟩⟩
  · intro i; fin_cases i
    · exact free5_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free30_2
    · exact free40_1
    · exact free49_1
    · exact free58_1
    · exact free74_4
    · exact free84_1
    · exact free98_1
    · exact free137_1
    · exact free126_1
    · exact free161_1
    · exact free199_1
    · exact free160_1
    · exact free177_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [251793370, 327444610, 327504831, 327445160, 326869614, 326782045, 327432412, 161646755, 161882086, 162184729, 162174565, 72248836, 72565310, 69300326, 86436716, 100000000, 100000000, 223505641], [1438828, 1051303, 1050995, 1051301, 1054249, 1054697, 1051366, 2376355, 2372437, 2367399, 2367568, 5554671, 5529485, 5795555, 4605815, 3959851, 3959851, 1668219],
  ![118641264355620, 1619314823024, 201155076900, 5910119700], 137251415884350388⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,4,4,4,4,4,4,7,7,7,7,15,15,16,13,11,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 1732300/441, 4332756/121, 14470416/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle79
end Z6969Source1762

-- Source: Research6969.PhysicalChecks131
section Z6969Source1763
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2096 : Request := ⟨⟨⟨6900,9628,2077,89672⟩,9849424459857920,234966243278304⟩,65,2,1,257027,22⟩
theorem cover2096 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2096) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2097 : Request := ⟨⟨⟨8300,11582,2548,89022⟩,17399709518790656,499541547131788⟩,65,2,1,257027,22⟩
theorem cover2097 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2097) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2098 : Request := ⟨⟨⟨10000,13955,3010,102261⟩,29974681586237440,1036603432174989⟩,65,2,1,257027,22⟩
theorem cover2098 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2098) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2099 : Request := ⟨⟨⟨1200,1674,368,11191⟩,52718727069696,218807905514⟩,0,2,1,257027,23⟩
theorem cover2099 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2099) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2100 : Request := ⟨⟨⟨1450,2023,445,13012⟩,92998964346880,466511127281⟩,1,2,1,257027,23⟩
theorem cover2100 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2100) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2101 : Request := ⟨⟨⟨1750,2442,527,16276⟩,161065121873920,975196209190⟩,3,2,1,257027,23⟩
theorem cover2101 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2101) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2102 : Request := ⟨⟨⟨1750,2442,527,16759⟩,161065121873920,975196209190⟩,4,2,1,257027,23⟩
theorem cover2102 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2102) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2103 : Request := ⟨⟨⟨2100,2930,632,19729⟩,278060332482560,2019119590628⟩,6,2,1,257027,23⟩
theorem cover2103 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2103) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2104 : Request := ⟨⟨⟨2100,2930,645,19778⟩,282396798484480,2051392203643⟩,8,2,1,257027,23⟩
theorem cover2104 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2104) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2105 : Request := ⟨⟨⟨2600,3628,798,24892⟩,535425056505856,4816500515660⟩,13,2,1,257027,23⟩
theorem cover2105 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2105) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2106 : Request := ⟨⟨⟨4800,6698,1474,45628⟩,3367547627110400,55918169002031⟩,32,2,1,257027,23⟩
theorem cover2106 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2106) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2107 : Request := ⟨⟨⟨6900,9628,2077,79188⟩,9849424459857920,234966243278304⟩,65,2,1,257027,23⟩
theorem cover2107 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2107) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2108 : Request := ⟨⟨⟨10000,13955,3070,89198⟩,30428373265940480,1052683166434338⟩,65,2,1,257027,23⟩
theorem cover2108 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2108) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2109 : Request := ⟨⟨⟨8300,11581,2498,99780⟩,17139238515245056,491743896877039⟩,85,2,1,257027,23⟩
theorem cover2109 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2109) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2110 : Request := ⟨⟨⟨1200,1674,368,10273⟩,52718727069696,218807905514⟩,0,2,1,257027,24⟩
theorem cover2110 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2110) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2111 : Request := ⟨⟨⟨1450,2023,445,12011⟩,92998964346880,466511127281⟩,1,2,1,257027,24⟩
theorem cover2111 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2111) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1763

-- Source: Research6969.PrefixRescueDataMiddle79
section Z6969Source1764
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle79
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,22⟩
  bank i := ![bank227 12912, bank237 14275, bank237 14867, bank246 17665, bank252 21621, bank270 26844, bank316 38818, bank359 75848, bank386 102261, bank359 89672, bank374 89022] i
  reserve i := ![0, 1, 2, 4, 6, 10, 20, 50, 65, 65, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 22

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank227 12912
    · exact rank237 14275
    · exact rank237 14867
    · exact rank246 17665
    · exact rank252 21621
    · exact rank270 26844
    · exact rank316 38818
    · exact rank359 75848
    · exact rank386 102261
    · exact rank359 89672
    · exact rank374 89022
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2088⟩
    · exact ⟨_, cover2089⟩
    · exact ⟨_, cover2090⟩
    · exact ⟨_, cover2091⟩
    · exact ⟨_, cover2092⟩
    · exact ⟨_, cover2093⟩
    · exact ⟨_, cover2094⟩
    · exact ⟨_, cover2095⟩
    · exact ⟨_, cover2098⟩
    · exact ⟨_, cover2096⟩
    · exact ⟨_, cover2097⟩

def price : EarlyPrice := ⟨2, 22, 10, 80/100, 80/100, ![876760248750, 133693157453, 25806987500, 1173066230], 2199383627306362⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![11705/66, 2051, 17780/3, 29674] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle79
end Z6969Source1764

-- Source: Research6969.PrefixMiddleSaved79
section Z6969Source1765
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved79
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle79.price Lower6960.Prefix6969RescueData.Middle79.price :=
  ⟨336, 3928, 177, 2051, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle79.plan Lower6960.Prefix6969RescueData.Middle79.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 22 22 :=
  ⟨Lower6960.Prefix6969MainCases.Middle79.plan, Lower6960.Prefix6969MainCases.Middle79.price, Lower6960.Prefix6969MainCases.Middle79.valid, Lower6960.Prefix6969MainCases.Middle79.priced, Lower6960.Prefix6969MainCases.Middle79.sources,
   Lower6960.Prefix6969RescueData.Middle79.plan, Lower6960.Prefix6969RescueData.Middle79.price, Lower6960.Prefix6969RescueData.Middle79.sources, Lower6960.Prefix6969RescueData.Middle79.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved79
end Z6969Source1765

-- Source: Research6969.PrefixMainDataMiddle80
section Z6969Source1766
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle80
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank13 1183, bank18 1295, bank24 1404, bank30 1501, bank40 1714, bank49 2130, bank58 2054, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank126 11206, bank153 5200, bank199 7608, bank212 8810, bank180 21819, bank170 28384] i
  head := src2765
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15261, 125358, 583516, 2089275],
    ![25417/2, 96990, 440419, 2987075/2],
    ![54680/9, 422150/9, 440419, 2987075/2],
    ![29433/8, 227915/8, 2063588/9, 787800],
    ![63824/25, 98504/5, 313709/2, 2253001/4],
    ![72196/49, 559030/49, 2520058/25, 346228],
    ![40539/50, 13201/2, 71355, 1134225/4],
    ![95180/121, 63880/11, 3161288/49, 10372700/49],
    ![95180/121, 63880/11, 116003/2, 10372700/49],
    ![63754/121, 739660/147, 770661/16, 9953550/49],
    ![63754/121, 739660/147, 770661/16, 565600/3],
    ![63754/121, 591891/121, 770661/16, 9114361/64],
    ![1355575/3362, 591891/121, 770661/16, 9114361/64],
    ![1355575/3362, 7050800/1681, 3948925/98, 6565000/49],
    ![1355575/3362, 81940/21, 4332756/121, 14407650/121],
    ![1355575/3362, 278775/74, 46340245/1352, 77858375/676],
    ![25627/74, 278775/74, 46340245/1352, 77858375/676],
    ![920087/2738, 278775/74, 46340245/1352, 77858375/676]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 23 257027 := by
  refine ⟨?_, rank154 5050, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2765⟩⟩
  · intro i; fin_cases i
    · exact free5_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free30_2
    · exact free40_1
    · exact free49_1
    · exact free58_1
    · exact free74_4
    · exact free84_1
    · exact free98_1
    · exact free137_1
    · exact free126_1
    · exact free153_1
    · exact free199_1
    · exact free212_1
    · exact free180_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [251731286, 325412055, 324808844, 325036910, 326236397, 325089316, 325641040, 150704297, 150720313, 150661781, 150508697, 69211429, 65774562, 68468368, 96210179, 96202967, 100000000, 221597970], [1439146, 1061715, 1064805, 1063637, 1057492, 1063368, 1060542, 2558527, 2558260, 2559235, 2561783, 5803622, 6115489, 5871048, 4120011, 4120316, 3959851, 1683924],
  ![117628634435400, 1621384967100, 199438173000, 5987105220], 136246520786061119⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,4,4,4,4,4,4,7,7,7,7,16,16,16,11,11,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 278775/74, 46340245/1352, 77858375/676] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle80
end Z6969Source1766

-- Source: Research6969.PrefixRescueDataMiddle80
section Z6969Source1767
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle80
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,23⟩
  bank i := ![bank228 11191, bank237 13012, bank245 16276, bank245 16759, bank252 19729, bank253 19778, bank271 24892, bank333 45628, bank387 89198, bank359 79188, bank371 99780] i
  reserve i := ![0, 1, 3, 4, 6, 8, 13, 32, 65, 65, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 23

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank228 11191
    · exact rank237 13012
    · exact rank245 16276
    · exact rank245 16759
    · exact rank252 19729
    · exact rank253 19778
    · exact rank271 24892
    · exact rank333 45628
    · exact rank387 89198
    · exact rank359 79188
    · exact rank371 99780
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2099⟩
    · exact ⟨_, cover2100⟩
    · exact ⟨_, cover2101⟩
    · exact ⟨_, cover2102⟩
    · exact ⟨_, cover2103⟩
    · exact ⟨_, cover2104⟩
    · exact ⟨_, cover2105⟩
    · exact ⟨_, cover2106⟩
    · exact ⟨_, cover2108⟩
    · exact ⟨_, cover2107⟩
    · exact ⟨_, cover2109⟩

def price : EarlyPrice := ⟨2, 23, 10, 80/100, 70/100, ![894374537700, 132329828679, 27517837550, 1196449610], 2065094709632649⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![14079/86, 78617/43, 465923/86, 1147470/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle80
end Z6969Source1767

-- Source: Research6969.PrefixMiddleSaved80
section Z6969Source1768
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved80
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle80.price Lower6960.Prefix6969RescueData.Middle80.price :=
  ⟨336, 3767, 163, 1828, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle80.plan Lower6960.Prefix6969RescueData.Middle80.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 23 23 :=
  ⟨Lower6960.Prefix6969MainCases.Middle80.plan, Lower6960.Prefix6969MainCases.Middle80.price, Lower6960.Prefix6969MainCases.Middle80.valid, Lower6960.Prefix6969MainCases.Middle80.priced, Lower6960.Prefix6969MainCases.Middle80.sources,
   Lower6960.Prefix6969RescueData.Middle80.plan, Lower6960.Prefix6969RescueData.Middle80.price, Lower6960.Prefix6969RescueData.Middle80.sources, Lower6960.Prefix6969RescueData.Middle80.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved80
end Z6969Source1768

-- Source: Research6969.PrefixMainDataMiddle81
section Z6969Source1769
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle81
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 16, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank13 1183, bank18 1295, bank24 1404, bank29 1513, bank35 1600, bank44 1848, bank54 2149, bank65 2772, bank84 3942, bank95 2576, bank137 3019, bank126 11206, bank153 5200, bank199 7608, bank212 8810, bank180 21819, bank170 28384] i
  head := src2766
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15218, 124914, 582082, 2092686],
    ![25417/2, 385481/4, 437605, 5894889/4],
    ![54680/9, 419470/9, 437605, 5894889/4],
    ![29433/8, 452949/16, 683530/3, 777348],
    ![63052/25, 486428/25, 157352, 2289169/4],
    ![5710/3, 260575/18, 1180679/8, 498300],
    ![18775/16, 588225/64, 304304/3, 9208584/25],
    ![89110/121, 689225/121, 446290/7, 1529781/7],
    ![89110/121, 689225/121, 446290/7, 1529781/7],
    ![63754/121, 245258/49, 770661/16, 9821493/49],
    ![63754/121, 245258/49, 770661/16, 1658944/9],
    ![63754/121, 587603/121, 770661/16, 9114361/64],
    ![1355575/3362, 587603/121, 770661/16, 9114361/64],
    ![1355575/3362, 7004168/1681, 7846327/196, 6477900/49],
    ![1355575/3362, 1709350/441, 34647039/968, 1292409/11],
    ![1355575/3362, 20494747/5476, 92082515/2704, 19404025/169],
    ![25627/74, 20494747/5476, 92082515/2704, 19404025/169],
    ![920087/2738, 20494747/5476, 92082515/2704, 19404025/169]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 24 257027 := by
  refine ⟨?_, rank154 4983, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2766⟩⟩
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
    · exact free153_1
    · exact free199_1
    · exact free212_1
    · exact free180_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [249983462, 323014400, 322282344, 323365757, 324432770, 323091553, 322588613, 147799495, 147888956, 147953756, 147937766, 68587763, 68284463, 67937951, 95794473, 95721273, 100000000, 221318217], [1450238, 1073997, 1077747, 1072197, 1066732, 1073602, 1076178, 2606886, 2605397, 2604318, 2604584, 5860214, 5887736, 5919179, 4137579, 4140672, 3959851, 1686227],
  ![117480135947940, 1621688205888, 199186395300, 6036187620], 135070357819697772⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,7,7,7,7,16,16,16,11,11,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 20494747/5476, 92082515/2704, 19404025/169] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle81
end Z6969Source1769

-- Source: Research6969.PhysicalChecks132
section Z6969Source1770
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2112 : Request := ⟨⟨⟨1450,2023,445,12372⟩,92998964346880,466511127281⟩,2,2,1,257027,24⟩
theorem cover2112 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2112) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2113 : Request := ⟨⟨⟨1750,2442,537,14771⟩,163381988556800,989573241440⟩,4,2,1,257027,24⟩
theorem cover2113 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2113) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2114 : Request := ⟨⟨⟨2100,2930,645,18126⟩,282396798484480,2051392203643⟩,8,2,1,257027,24⟩
theorem cover2114 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2114) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2115 : Request := ⟨⟨⟨2600,3628,798,22764⟩,535425056505856,4816500515660⟩,13,2,1,257027,24⟩
theorem cover2115 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2115) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2116 : Request := ⟨⟨⟨4800,6698,1474,41770⟩,3367547627110400,55918169002031⟩,32,2,1,257027,24⟩
theorem cover2116 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2116) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2117 : Request := ⟨⟨⟨6900,9628,2077,70939⟩,9849424459857920,234966243278304⟩,65,2,1,257027,24⟩
theorem cover2117 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2117) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2118 : Request := ⟨⟨⟨8300,11582,2548,73210⟩,17399709518790656,499541547131788⟩,65,2,1,257027,24⟩
theorem cover2118 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2118) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2119 : Request := ⟨⟨⟨8300,11581,2498,88701⟩,17139238515245056,491743896877039⟩,85,2,1,257027,24⟩
theorem cover2119 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2119) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2120 : Request := ⟨⟨⟨1000,1395,307,8526⟩,30557599170560,105715278267⟩,0,2,1,257027,25⟩
theorem cover2120 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2120) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2121 : Request := ⟨⟨⟨1200,1674,368,9876⟩,52718727069696,218807905514⟩,1,2,1,257027,25⟩
theorem cover2121 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2121) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2122 : Request := ⟨⟨⟨1450,2023,445,11510⟩,92998964346880,466511127281⟩,2,2,1,257027,25⟩
theorem cover2122 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2122) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2123 : Request := ⟨⟨⟨1450,2023,445,11827⟩,92998964346880,466511127281⟩,3,2,1,257027,25⟩
theorem cover2123 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2123) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2124 : Request := ⟨⟨⟨1450,2023,445,12176⟩,92998964346880,466511127281⟩,4,2,1,257027,25⟩
theorem cover2124 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2124) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2125 : Request := ⟨⟨⟨1750,2442,537,14397⟩,163381988556800,989573241440⟩,6,2,1,257027,25⟩
theorem cover2125 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2125) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2126 : Request := ⟨⟨⟨2100,2930,645,17502⟩,282396798484480,2051392203643⟩,10,2,1,257027,25⟩
theorem cover2126 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2126) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2127 : Request := ⟨⟨⟨3200,4465,982,26529⟩,997767489781760,11043969901736⟩,20,2,1,257027,25⟩
theorem cover2127 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2127) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1770

-- Source: Research6969.PrefixRescueDataMiddle81
section Z6969Source1771
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle81
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,24⟩
  bank i := ![bank228 10273, bank237 12011, bank237 12372, bank246 14771, bank253 18126, bank271 22764, bank333 41770, bank359 70939, bank374 73210, bank371 88701, bank359 70939] i
  reserve i := ![0, 1, 2, 4, 8, 13, 32, 65, 65, 85, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 24

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank228 10273
    · exact rank237 12011
    · exact rank237 12372
    · exact rank246 14771
    · exact rank253 18126
    · exact rank271 22764
    · exact rank333 41770
    · exact rank359 70939
    · exact rank374 73210
    · exact rank371 88701
    · exact rank359 70939
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2110⟩
    · exact ⟨_, cover2111⟩
    · exact ⟨_, cover2112⟩
    · exact ⟨_, cover2113⟩
    · exact ⟨_, cover2114⟩
    · exact ⟨_, cover2115⟩
    · exact ⟨_, cover2116⟩
    · exact ⟨_, cover2117⟩
    · exact ⟨_, cover2118⟩
    · exact ⟨_, cover2119⟩
    · exact ⟨_, cover2117⟩

def price : EarlyPrice := ⟨2, 24, 10, 75/100, 70/100, ![829636507881, 119523762846, 23831905188, 993014204], 1879209206882272⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![14079/86, 148653/86, 227673/43, 1064412/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle81
end Z6969Source1771

end Merged_Z6969Pack0726

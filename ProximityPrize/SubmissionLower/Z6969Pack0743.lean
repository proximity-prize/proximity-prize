import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0739
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0742
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0743
section Merged_Z6969Pack0743

-- Source: Research6969.PrefixMainDataMiddle43
section Z6969Source1964
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle43
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank9 1210, bank17 1319, bank24 1404, bank30 1501, bank40 1714, bank49 2130, bank58 2054, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank126 11206, bank161 5142, bank199 7608, bank186 19684, bank176 24684, bank170 28384] i
  head := src2940
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15063, 125567, 583633, 2121369],
    ![12303, 97694, 883481/2, 3110305/2],
    ![53398/9, 424729/9, 883481/2, 3110305/2],
    ![29433/8, 459743/16, 2081242/9, 801996],
    ![63824/25, 496797/25, 313709/2, 2253001/4],
    ![72196/49, 563853/49, 101665, 8811674/25],
    ![40539/50, 665419/100, 71355, 1134225/4],
    ![95180/121, 709050/121, 3189680/49, 10559614/49],
    ![95180/121, 709050/121, 116003/2, 10559614/49],
    ![63754/121, 744938/147, 770661/16, 10132911/49],
    ![63754/121, 744938/147, 770661/16, 575792/3],
    ![63754/121, 597715/121, 770661/16, 9114361/64],
    ![1355575/3362, 597715/121, 770661/16, 9114361/64],
    ![1355575/3362, 7136388/1681, 8015591/196, 13217511/98],
    ![1355575/3362, 248030/63, 4332756/121, 14470416/121],
    ![481425/1369, 248030/63, 4332756/121, 14470416/121],
    ![466774/1369, 248030/63, 4332756/121, 14470416/121],
    ![920087/2738, 248030/63, 4332756/121, 14470416/121]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 18 385541 := by
  refine ⟨?_, rank154 5141, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2940⟩⟩
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
    · exact free186_1
    · exact free176_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [252247827, 327198304, 327479572, 327960966, 326499211, 327792460, 328251894, 150153735, 150135747, 150150360, 150032611, 73968193, 74253286, 69485157, 100202807, 100000000, 100000000, 223534758], [1436500, 1052565, 1051124, 1049039, 1056146, 1049522, 1048241, 2567693, 2567992, 2567749, 2569709, 5417841, 5395153, 5778783, 3951280, 3959851, 3959851, 1667980],
  ![118656720241560, 1619283577272, 201181282200, 5893016340], 137495057655726643⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,4,4,3,4,4,3,7,7,7,7,15,15,16,11,11,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 248030/63, 4332756/121, 14470416/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle43
end Z6969Source1964

-- Source: Research6969.PrefixRescueDataMiddle43
section Z6969Source1965
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle43
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,3,1,18⟩
  bank i := ![bank204 10172, bank228 12863, bank227 13734, bank227 14850, bank246 20773, bank316 45041, bank372 98175, bank329 71730, bank355 120560, bank372 98175] i
  reserve i := ![0, 1, 2, 4, 10, 32, 85, 65, 110, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 18

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank204 10172
    · exact rank228 12863
    · exact rank227 13734
    · exact rank227 14850
    · exact rank246 20773
    · exact rank316 45041
    · exact rank372 98175
    · exact rank329 71730
    · exact rank355 120560
    · exact rank372 98175
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2483⟩
    · exact ⟨_, cover2484⟩
    · exact ⟨_, cover2485⟩
    · exact ⟨_, cover2486⟩
    · exact ⟨_, cover2487⟩
    · exact ⟨_, cover2488⟩
    · exact ⟨_, cover2490⟩
    · exact ⟨_, cover2489⟩
    · exact ⟨_, cover2491⟩
    · exact ⟨_, cover2490⟩

def price : EarlyPrice := ⟨3, 18, 9, 85/100, 70/100, ![845714776720, 146924547803, 17873932076, 1986010572], 1524135087330144⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![13780/111, 157946/111, 178316/37, 723360/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle43
end Z6969Source1965

-- Source: Research6969.PrefixMiddleSaved43
section Z6969Source1966
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved43
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle43.price Lower6960.Prefix6969RescueData.Middle43.price :=
  ⟨336, 3936, 124, 1422, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle43.plan Lower6960.Prefix6969RescueData.Middle43.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 18 18 :=
  ⟨Lower6960.Prefix6969MainCases.Middle43.plan, Lower6960.Prefix6969MainCases.Middle43.price, Lower6960.Prefix6969MainCases.Middle43.valid, Lower6960.Prefix6969MainCases.Middle43.priced, Lower6960.Prefix6969MainCases.Middle43.sources,
   Lower6960.Prefix6969RescueData.Middle43.plan, Lower6960.Prefix6969RescueData.Middle43.price, Lower6960.Prefix6969RescueData.Middle43.sources, Lower6960.Prefix6969RescueData.Middle43.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved43
end Z6969Source1966

-- Source: Research6969.PrefixMainDataMiddle44
section Z6969Source1967
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle44
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 14, 18, 21, 16, 21, 25, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank12 1187, bank18 1295, bank24 1404, bank34 1629, bank44 1848, bank54 2149, bank64 2688, bank86 3038, bank84 3942, bank95 2576, bank116 3050, bank140 3403, bank126 11206, bank161 5142, bank199 7608, bank212 8810, bank180 21819, bank170 28384] i
  head := src2941
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  historyValues := [![15199, 125027, 580952, 2093657],
    ![25247/2, 389713/4, 879739/2, 6028773/4],
    ![54680/9, 423310/9, 879739/2, 6028773/4],
    ![29433/8, 457077/16, 689738/3, 792324],
    ![33449/18, 175267/12, 296871/2, 8273691/16],
    ![18775/16, 593505/64, 304304/3, 9385992/25],
    ![89110/121, 695465/121, 450322/7, 1559253/7],
    ![89110/121, 695465/121, 450322/7, 1559253/7],
    ![242476/361, 1936982/361, 671812/13, 188356],
    ![63754/121, 35302/7, 770661/16, 188356],
    ![63754/121, 35302/7, 770661/16, 1658944/9],
    ![63754/121, 578736/121, 770661/16, 2325625/16],
    ![63754/121, 578736/121, 770661/16, 2325625/16],
    ![1355575/3362, 578736/121, 770661/16, 2325625/16],
    ![1355575/3362, 7092492/1681, 7966797/196, 13058109/98],
    ![1355575/3362, 1725670/441, 4332756/121, 14470416/121],
    ![1355575/3362, 20687611/5476, 92939315/2704, 156610965/1352],
    ![25627/74, 20687611/5476, 92939315/2704, 156610965/1352],
    ![920087/2738, 20687611/5476, 92939315/2704, 156610965/1352]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 19 385541 := by
  refine ⟨?_, rank154 5079, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2941⟩⟩
  · intro i; fin_cases i
    · exact free5_1
    · exact free12_1
    · exact free18_1
    · exact free24_1
    · exact free34_1
    · exact free44_1
    · exact free54_1
    · exact free64_1
    · exact free86_2
    · exact free84_1
    · exact free95_1
    · exact free116_3
    · exact free140_1
    · exact free126_1
    · exact free161_1
    · exact free199_1
    · exact free212_1
    · exact free180_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [251223815, 326233437, 326540914, 326487526, 325578012, 326933527, 146710840, 146815846, 142461402, 141154749, 140927453, 54346243, 70653453, 70838856, 68986916, 96474719, 96275839, 100000000, 221719057], [1441745, 1057508, 1055933, 1056206, 1060865, 1053921, 2626254, 2623949, 2719545, 2748230, 2753220, 7447297, 5681634, 5666879, 5823995, 4108831, 4117236, 3959851, 1682928],
  ![117692909836740, 1621253389268, 199547151300, 5939121360], 136260891146596872⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,4,4,4,4,4,8,8,8,8,8,20,15,15,16,11,11,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 20687611/5476, 92939315/2704, 156610965/1352] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle44
end Z6969Source1967

-- Source: Research6969.PhysicalChecks156
section Z6969Source1968
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2496 : Request := ⟨⟨⟨1450,2023,445,16822⟩,92998964346880,466511127281⟩,8,3,1,385541,19⟩
theorem cover2496 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2496) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2497 : Request := ⟨⟨⟨2100,2930,632,25136⟩,278060332482560,2019119590628⟩,16,3,1,385541,19⟩
theorem cover2497 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2497) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2498 : Request := ⟨⟨⟨3200,4465,963,35776⟩,983050615259136,10877088344236⟩,25,3,1,385541,19⟩
theorem cover2498 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2498) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2499 : Request := ⟨⟨⟨3200,4464,963,45826⟩,983050615259136,10869251283552⟩,40,3,1,385541,19⟩
theorem cover2499 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2499) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2500 : Request := ⟨⟨⟨6900,9628,2118,74261⟩,9997036108906496,238575106344005⟩,65,3,1,385541,19⟩
theorem cover2500 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2500) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2501 : Request := ⟨⟨⟨5700,7952,1716,87312⟩,5553838907981824,109384694947514⟩,85,3,1,385541,19⟩
theorem cover2501 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2501) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2502 : Request := ⟨⟨⟨6900,9626,2077,111310⟩,9849424459857920,234809190715807⟩,110,3,1,385541,19⟩
theorem cover2502 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2502) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2503 : Request := ⟨⟨⟨1000,1395,301,10070⟩,30103476895744,104105680031⟩,0,3,1,385541,20⟩
theorem cover2503 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2503) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
def src2504 : Request := ⟨⟨⟨1000,1395,301,10502⟩,30103476895744,104105680031⟩,1,3,1,385541,20⟩
theorem cover2504 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2504) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
def src2505 : Request := ⟨⟨⟨1000,1395,301,10982⟩,30103476895744,104105680031⟩,2,3,1,385541,20⟩
theorem cover2505 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2505) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
def src2506 : Request := ⟨⟨⟨1200,1674,361,12993⟩,51955677528064,215563369662⟩,4,3,1,385541,20⟩
theorem cover2506 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2506) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2507 : Request := ⟨⟨⟨1450,2023,445,15677⟩,92998964346880,466511127281⟩,8,3,1,385541,20⟩
theorem cover2507 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2507) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2508 : Request := ⟨⟨⟨2100,2930,645,22630⟩,282396798484480,2051392203643⟩,16,3,1,385541,20⟩
theorem cover2508 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2508) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2509 : Request := ⟨⟨⟨2600,3628,798,29546⟩,535425056505856,4816500515660⟩,25,3,1,385541,20⟩
theorem cover2509 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2509) 2557 2412 [2413, 2418, 2431, 2466, 2557] := triangleCover (by decide +kernel)
def src2510 : Request := ⟨⟨⟨3200,4464,963,42475⟩,983050615259136,10869251283552⟩,40,3,1,385541,20⟩
theorem cover2510 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2510) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2511 : Request := ⟨⟨⟨5700,7953,1750,63647⟩,5637370734182400,111115710437454⟩,65,3,1,385541,20⟩
theorem cover2511 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2511) 2557 2412 [2413, 2418, 2431, 2464, 2550, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1968

-- Source: Research6969.PrefixRescueDataMiddle44
section Z6969Source1969
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle44
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,19⟩
  bank i := ![bank204 9473, bank228 12057, bank227 12882, bank227 13885, bank237 16822, bank252 25136, bank303 35776, bank299 45826, bank360 74261, bank355 111310, bank342 87312] i
  reserve i := ![0, 1, 2, 4, 8, 16, 25, 40, 65, 110, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 19

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank204 9473
    · exact rank228 12057
    · exact rank227 12882
    · exact rank227 13885
    · exact rank237 16822
    · exact rank252 25136
    · exact rank303 35776
    · exact rank299 45826
    · exact rank360 74261
    · exact rank355 111310
    · exact rank342 87312
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2492⟩
    · exact ⟨_, cover2493⟩
    · exact ⟨_, cover2494⟩
    · exact ⟨_, cover2495⟩
    · exact ⟨_, cover2496⟩
    · exact ⟨_, cover2497⟩
    · exact ⟨_, cover2498⟩
    · exact ⟨_, cover2499⟩
    · exact ⟨_, cover2500⟩
    · exact ⟨_, cover2502⟩
    · exact ⟨_, cover2501⟩

def price : EarlyPrice := ⟨3, 19, 10, 85/100, 80/100, ![824206359930, 142656703137, 15682949154, 1650851802], 1338054405657365⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![13780/111, 150773/111, 516824/111, 2114890/111] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle44
end Z6969Source1969

-- Source: Research6969.PrefixMiddleSaved44
section Z6969Source1970
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved44
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle44.price Lower6960.Prefix6969RescueData.Middle44.price :=
  ⟨336, 3777, 124, 1358, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle44.plan Lower6960.Prefix6969RescueData.Middle44.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 19 19 :=
  ⟨Lower6960.Prefix6969MainCases.Middle44.plan, Lower6960.Prefix6969MainCases.Middle44.price, Lower6960.Prefix6969MainCases.Middle44.valid, Lower6960.Prefix6969MainCases.Middle44.priced, Lower6960.Prefix6969MainCases.Middle44.sources,
   Lower6960.Prefix6969RescueData.Middle44.plan, Lower6960.Prefix6969RescueData.Middle44.price, Lower6960.Prefix6969RescueData.Middle44.sources, Lower6960.Prefix6969RescueData.Middle44.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved44
end Z6969Source1970

-- Source: Research6969.PrefixMainDataMiddle45
section Z6969Source1971
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle45
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank13 1183, bank18 1295, bank24 1404, bank30 1501, bank40 1714, bank49 2130, bank58 2054, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank126 11206, bank153 5200, bank199 7608, bank212 8810, bank180 21819, bank170 28384] i
  head := src2942
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15261, 125259, 582955, 2084754],
    ![25417/2, 386739/4, 439033, 5935111/4],
    ![54680/9, 420830/9, 439033, 5935111/4],
    ![29433/8, 454411/16, 2057186/9, 782652],
    ![63824/25, 490969/25, 313709/2, 2253001/4],
    ![72196/49, 557281/49, 2512237/25, 8599138/25],
    ![40539/50, 658103/100, 71355, 1134225/4],
    ![95180/121, 63670/11, 3150992/49, 10304918/49],
    ![95180/121, 63670/11, 116003/2, 10304918/49],
    ![63754/121, 737746/147, 770661/16, 9888507/49],
    ![63754/121, 737746/147, 770661/16, 561904/3],
    ![63754/121, 589779/121, 770661/16, 9114361/64],
    ![1355575/3362, 589779/121, 770661/16, 9114361/64],
    ![1355575/3362, 7027832/1681, 1124639/28, 6522100/49],
    ![1355575/3362, 190570/49, 4332756/121, 14313501/121],
    ![1355575/3362, 20563053/5476, 92385965/2704, 19404025/169],
    ![25627/74, 20563053/5476, 92385965/2704, 19404025/169],
    ![920087/2738, 20563053/5476, 92385965/2704, 19404025/169]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 20 385541 := by
  refine ⟨?_, rank154 5017, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2942⟩⟩
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

def price : Pricing := ⟨55/100, 90/100, [251072705, 324504981, 324962073, 325053453, 324364184, 324320725, 325971420, 149887715, 149848535, 149998889, 149969457, 69032301, 63819213, 68207118, 96077909, 96049701, 135922097, 221460181], [1442519, 1066362, 1064020, 1063552, 1067083, 1067306, 1058850, 2572121, 2572774, 2570271, 2570761, 5819876, 6313623, 5894755, 4125601, 4126793, 2863106, 1685059],
  ![117555493278420, 1621534417904, 199314162900, 6011280240], 135817526353161989⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,4,4,4,4,4,4,7,7,7,7,16,17,16,11,11,8,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 20563053/5476, 92385965/2704, 19404025/169] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle45
end Z6969Source1971

-- Source: Research6969.PhysicalChecks157
section Z6969Source1972
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2512 : Request := ⟨⟨⟨6900,9626,2077,102643⟩,9849424459857920,234809190715807⟩,110,3,1,385541,20⟩
theorem cover2512 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2512) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2513 : Request := ⟨⟨⟨10000,13953,3010,109760⟩,29974681586237440,1036125345444439⟩,110,3,1,385541,20⟩
theorem cover2513 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2513) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2514 : Request := ⟨⟨⟨1000,1395,301,9475⟩,30103476895744,104105680031⟩,0,3,1,385541,21⟩
theorem cover2514 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2514) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
def src2515 : Request := ⟨⟨⟨1000,1395,301,9858⟩,30103476895744,104105680031⟩,1,3,1,385541,21⟩
theorem cover2515 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2515) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
def src2516 : Request := ⟨⟨⟨1000,1395,301,10284⟩,30103476895744,104105680031⟩,2,3,1,385541,21⟩
theorem cover2516 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2516) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
def src2517 : Request := ⟨⟨⟨1200,1674,368,11351⟩,52718727069696,218807905514⟩,3,3,1,385541,21⟩
theorem cover2517 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2517) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2518 : Request := ⟨⟨⟨1200,1674,361,12179⟩,51955677528064,215563369662⟩,4,3,1,385541,21⟩
theorem cover2518 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2518) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2519 : Request := ⟨⟨⟨1450,2023,445,14641⟩,92998964346880,466511127281⟩,8,3,1,385541,21⟩
theorem cover2519 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2519) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2520 : Request := ⟨⟨⟨2600,3628,798,27515⟩,535425056505856,4816500515660⟩,25,3,1,385541,21⟩
theorem cover2520 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2520) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2521 : Request := ⟨⟨⟨5700,7953,1750,59334⟩,5637370734182400,111115710437454⟩,65,3,1,385541,21⟩
theorem cover2521 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2521) 2557 2412 [2413, 2418, 2431, 2464, 2550, 2557] := triangleCover (by decide +kernel)
def src2522 : Request := ⟨⟨⟨6900,9626,2077,94628⟩,9849424459857920,234809190715807⟩,110,3,1,385541,21⟩
theorem cover2522 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2522) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2523 : Request := ⟨⟨⟨10000,13953,3010,102836⟩,29974681586237440,1036125345444439⟩,110,3,1,385541,21⟩
theorem cover2523 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2523) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2524 : Request := ⟨⟨⟨8300,11579,2498,124806⟩,17139238515245056,491470625461013⟩,145,3,1,385541,21⟩
theorem cover2524 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2524) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2525 : Request := ⟨⟨⟨825,1151,248,8042⟩,16903818182656,48256472894⟩,0,3,1,385541,22⟩
theorem cover2525 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2525) 2557 2412 [2415, 2426, 2457, 2544, 2557] := triangleCover (by decide +kernel)
def src2526 : Request := ⟨⟨⟨1000,1395,301,9279⟩,30103476895744,104105680031⟩,1,3,1,385541,22⟩
theorem cover2526 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2526) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
def src2527 : Request := ⟨⟨⟨1000,1395,301,9655⟩,30103476895744,104105680031⟩,2,3,1,385541,22⟩
theorem cover2527 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2527) 2557 2412 [2414, 2423, 2448, 2517, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1972

-- Source: Research6969.PrefixRescueDataMiddle45
section Z6969Source1973
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle45
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,20⟩
  bank i := ![bank221 10070, bank221 10502, bank221 10982, bank227 12993, bank237 15677, bank253 22630, bank271 29546, bank299 42475, bank346 63647, bank355 102643, bank382 109760] i
  reserve i := ![0, 1, 2, 4, 8, 16, 25, 40, 65, 110, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 20

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 10070
    · exact rank221 10502
    · exact rank221 10982
    · exact rank227 12993
    · exact rank237 15677
    · exact rank253 22630
    · exact rank271 29546
    · exact rank299 42475
    · exact rank346 63647
    · exact rank355 102643
    · exact rank382 109760
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2503⟩
    · exact ⟨_, cover2504⟩
    · exact ⟨_, cover2505⟩
    · exact ⟨_, cover2506⟩
    · exact ⟨_, cover2507⟩
    · exact ⟨_, cover2508⟩
    · exact ⟨_, cover2509⟩
    · exact ⟨_, cover2510⟩
    · exact ⟨_, cover2511⟩
    · exact ⟨_, cover2512⟩
    · exact ⟨_, cover2513⟩

def price : EarlyPrice := ⟨3, 20, 10, 85/100, 80/100, ![855504343680, 170844446514, 23460897180, 2346111390], 1553716870979309⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![13780/111, 48061/37, 500449/111, 2052860/111] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle45
end Z6969Source1973

-- Source: Research6969.PrefixMiddleSaved45
section Z6969Source1974
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved45
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle45.price Lower6960.Prefix6969RescueData.Middle45.price :=
  ⟨336, 3755, 124, 1298, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle45.plan Lower6960.Prefix6969RescueData.Middle45.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 20 20 :=
  ⟨Lower6960.Prefix6969MainCases.Middle45.plan, Lower6960.Prefix6969MainCases.Middle45.price, Lower6960.Prefix6969MainCases.Middle45.valid, Lower6960.Prefix6969MainCases.Middle45.priced, Lower6960.Prefix6969MainCases.Middle45.sources,
   Lower6960.Prefix6969RescueData.Middle45.plan, Lower6960.Prefix6969RescueData.Middle45.price, Lower6960.Prefix6969RescueData.Middle45.sources, Lower6960.Prefix6969RescueData.Middle45.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved45
end Z6969Source1974

-- Source: Research6969.PrefixMainDataMiddle46
section Z6969Source1975
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle46
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 16, 21, 41, 40, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank13 1183, bank18 1295, bank24 1404, bank29 1513, bank35 1600, bank44 1848, bank54 2149, bank65 2772, bank84 3942, bank95 2576, bank137 3019, bank126 11206, bank149 5119, bank199 7608, bank212 8810, bank180 21819, bank170 28384] i
  head := src2943
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15218, 124833, 581623, 2088987],
    ![25417/2, 192241/2, 436471, 1465737],
    ![54680/9, 418390/9, 436471, 1465737],
    ![29433/8, 112947/4, 681784/3, 773136],
    ![63052/25, 485186/25, 157352, 2289169/4],
    ![5710/3, 129950/9, 294407/2, 495600],
    ![18775/16, 146685/16, 304304/3, 9158688/25],
    ![89110/121, 687470/121, 445156/7, 217356],
    ![89110/121, 687470/121, 445156/7, 217356],
    ![63754/121, 244736/49, 770661/16, 1395468/7],
    ![63754/121, 244736/49, 770661/16, 1658944/9],
    ![63754/121, 585875/121, 770661/16, 9114361/64],
    ![1355575/3362, 585875/121, 770661/16, 9114361/64],
    ![1355575/3362, 853897/200, 3844369/98, 26204161/196],
    ![1355575/3362, 1704760/441, 8638695/242, 14139468/121],
    ![1355575/3362, 5110126/1369, 22960385/676, 19404025/169],
    ![25627/74, 5110126/1369, 22960385/676, 19404025/169],
    ![920087/2738, 5110126/1369, 22960385/676, 19404025/169]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 21 385541 := by
  refine ⟨?_, rank154 4956, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2943⟩⟩
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
    · exact free212_1
    · exact free180_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [249445784, 323819061, 322550678, 322929581, 322940475, 322263040, 322342300, 146144852, 146034675, 144604037, 143594103, 68424760, 64285834, 67423903, 95685823, 95595376, 100000000, 221205481], [1454664, 1069875, 1076373, 1074432, 1074376, 1077846, 1077440, 2638680, 2641098, 2672506, 2694678, 5875006, 6265732, 5965825, 4142171, 4145993, 3959851, 1687156],
  ![117420293424420, 1621810581824, 199084932900, 6083755320], 134910546830969464⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,8,8,8,8,16,17,16,11,11,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 5110126/1369, 22960385/676, 19404025/169] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle46
end Z6969Source1975

end Merged_Z6969Pack0743

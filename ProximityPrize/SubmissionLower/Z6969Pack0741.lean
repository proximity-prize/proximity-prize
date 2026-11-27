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
  physicalFloor := 385610
  seedFloor := 11

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨3, 11, 10, 95/100, 80/100, ![840780899133, 199424903580, 12903499770, 2346111390], 2162667372646294⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 12 385610 := by
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

def price : Pricing := ⟨55/100, 90/100, [257027878, 337203915, 336343554, 336973518, 337035968, 336473837, 336963882, 336056069, 167518851, 167678598, 167724165, 167978182, 65013774, 84196654, 65784139, 77178426, 102452891, 102308034, 125053890, 100000000, 223140933], [1411692, 1023442, 1025802, 1024074, 1023902, 1025445, 1024100, 1026591, 2278077, 2275418, 2274659, 2270431, 6189611, 4737925, 6113227, 5186386, 3855311, 3861432, 3125621, 3958949, 1670841],
  ![118447670055060, 1619710643592, 200826839700, 5290113720], 141481340819192595⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 385610
  seedFloor := 12

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨3, 12, 10, 90/100, 80/100, ![756686777179, 177296202309, 14076544930, 2346111390], 2031723250748947⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 13 385610 := by
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

def price : Pricing := ⟨55/100, 90/100, [255749920, 334985949, 334873450, 335233376, 334204762, 335120347, 335028610, 334363921, 167871179, 167963321, 168198603, 168319668, 81915988, 83851345, 64285646, 88667432, 102667053, 102888670, 124914750, 100000000, 222867429], [1418237, 1029527, 1029835, 1028848, 1031670, 1029158, 1029410, 1031233, 2272212, 2270679, 2266763, 2264748, 4873497, 4758451, 6264324, 4487398, 3846263, 3836899, 3129515, 3958949, 1673092],
  ![118302488661780, 1620007332276, 200580686100, 4711149310], 140423490206167872⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2432 : Request := ⟨⟨⟨1000,1395,301,16526⟩,30103476895744,104105680031⟩,1,3,1,385610,13⟩
private theorem pass2432_2390 : (Triangular src2432) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2432_2391 : (Triangular src2432) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2432_2393 : (Triangular src2432) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2432_2399 : (Triangular src2432) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2432_2415 : (Triangular src2432) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2432_2459 : (Triangular src2432) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2432 : Cover (Triangular src2432) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2432_2390, by decide, by decide, pass2432_2391, by decide, by decide, pass2432_2393, by decide, by decide, pass2432_2399, by decide, by decide, pass2432_2415, by decide, by decide, pass2432_2459, rfl⟩
def src2433 : Request := ⟨⟨⟨1200,1674,368,18552⟩,52718727069696,218807905514⟩,2,3,1,385610,13⟩
private theorem pass2433_2390 : (Triangular src2433) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2433_2391 : (Triangular src2433) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2433_2393 : (Triangular src2433) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2433_2399 : (Triangular src2433) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2433_2415 : (Triangular src2433) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2433_2458 : (Triangular src2433) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2433 : Cover (Triangular src2433) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2433_2390, by decide, by decide, pass2433_2391, by decide, by decide, pass2433_2393, by decide, by decide, pass2433_2399, by decide, by decide, pass2433_2415, by decide, by decide, pass2433_2458, rfl⟩
def src2434 : Request := ⟨⟨⟨1200,1674,361,19657⟩,51955677528064,215563369662⟩,3,3,1,385610,13⟩
private theorem pass2434_2390 : (Triangular src2434) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2434_2391 : (Triangular src2434) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2434_2393 : (Triangular src2434) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2434_2399 : (Triangular src2434) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2434_2415 : (Triangular src2434) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2434_2459 : (Triangular src2434) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2434 : Cover (Triangular src2434) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2434_2390, by decide, by decide, pass2434_2391, by decide, by decide, pass2434_2393, by decide, by decide, pass2434_2399, by decide, by decide, pass2434_2415, by decide, by decide, pass2434_2459, rfl⟩
def src2435 : Request := ⟨⟨⟨1450,2023,436,24026⟩,91566841790464,459151377566⟩,6,3,1,385610,13⟩
private theorem pass2435_2390 : (Triangular src2435) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2435_2391 : (Triangular src2435) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2435_2393 : (Triangular src2435) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2435_2399 : (Triangular src2435) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2435_2415 : (Triangular src2435) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2435_2458 : (Triangular src2435) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2435 : Cover (Triangular src2435) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2435_2390, by decide, by decide, pass2435_2391, by decide, by decide, pass2435_2393, by decide, by decide, pass2435_2399, by decide, by decide, pass2435_2415, by decide, by decide, pass2435_2458, rfl⟩
def src2436 : Request := ⟨⟨⟨1750,2442,527,29554⟩,161065121873920,975196209190⟩,10,3,1,385610,13⟩
private theorem pass2436_2390 : (Triangular src2436) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2436_2391 : (Triangular src2436) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2436_2393 : (Triangular src2436) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2436_2398 : (Triangular src2436) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2436_2412 : (Triangular src2436) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2436_2449 : (Triangular src2436) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2436 : Cover (Triangular src2436) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2436_2390, by decide, by decide, pass2436_2391, by decide, by decide, pass2436_2393, by decide, by decide, pass2436_2398, by decide, by decide, pass2436_2412, by decide, by decide, pass2436_2449, rfl⟩
def src2437 : Request := ⟨⟨⟨2600,3628,783,44114⟩,527755772952576,4745819470168⟩,20,3,1,385610,13⟩
private theorem pass2437_2390 : (Triangular src2437) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2437_2391 : (Triangular src2437) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2437_2393 : (Triangular src2437) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2437_2398 : (Triangular src2437) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2437_2412 : (Triangular src2437) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2437_2448 : (Triangular src2437) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2437 : Cover (Triangular src2437) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass2437_2390, by decide, by decide, pass2437_2391, by decide, by decide, pass2437_2393, by decide, by decide, pass2437_2398, by decide, by decide, pass2437_2412, by decide, by decide, pass2437_2448, rfl⟩
def src2438 : Request := ⟨⟨⟨3200,4465,963,59521⟩,983050615259136,10877088344236⟩,32,3,1,385610,13⟩
private theorem pass2438_2390 : (Triangular src2438) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2438_2391 : (Triangular src2438) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2438_2393 : (Triangular src2438) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2438_2398 : (Triangular src2438) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2438_2411 : (Triangular src2438) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2438_2446 : (Triangular src2438) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2438 : Cover (Triangular src2438) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass2438_2390, by decide, by decide, pass2438_2391, by decide, by decide, pass2438_2393, by decide, by decide, pass2438_2398, by decide, by decide, pass2438_2411, by decide, by decide, pass2438_2446, rfl⟩
def src2439 : Request := ⟨⟨⟨4800,6698,1445,76718⟩,3317023033262080,55058665830093⟩,40,3,1,385610,13⟩
private theorem pass2439_2390 : (Triangular src2439) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2439_2391 : (Triangular src2439) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2439_2393 : (Triangular src2439) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2439_2398 : (Triangular src2439) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2439_2411 : (Triangular src2439) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2439_2445 : (Triangular src2439) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2439_2534 : (Triangular src2439) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2439 : Cover (Triangular src2439) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2439_2390, by decide, by decide, pass2439_2391, by decide, by decide, pass2439_2393, by decide, by decide, pass2439_2398, by decide, by decide, pass2439_2411, by decide, by decide, pass2439_2445, by decide, by decide, pass2439_2534, rfl⟩
def src2440 : Request := ⟨⟨⟨5700,7952,1716,134896⟩,5553838907981824,109384694947514⟩,85,3,1,385610,13⟩
private theorem pass2440_2390 : (Triangular src2440) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2440_2391 : (Triangular src2440) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2440_2393 : (Triangular src2440) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2440_2398 : (Triangular src2440) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2440_2411 : (Triangular src2440) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2440_2445 : (Triangular src2440) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2440_2533 : (Triangular src2440) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2440 : Cover (Triangular src2440) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2440_2390, by decide, by decide, pass2440_2391, by decide, by decide, pass2440_2393, by decide, by decide, pass2440_2398, by decide, by decide, pass2440_2411, by decide, by decide, pass2440_2445, by decide, by decide, pass2440_2533, rfl⟩
def src2441 : Request := ⟨⟨⟨10000,13953,3010,173865⟩,29974681586237440,1036125345444439⟩,110,3,1,385610,13⟩
private theorem pass2441_2390 : (Triangular src2441) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2441_2391 : (Triangular src2441) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2441_2393 : (Triangular src2441) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2441_2398 : (Triangular src2441) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2441_2411 : (Triangular src2441) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2441_2445 : (Triangular src2441) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2441_2533 : (Triangular src2441) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2441 : Cover (Triangular src2441) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2441_2390, by decide, by decide, pass2441_2391, by decide, by decide, pass2441_2393, by decide, by decide, pass2441_2398, by decide, by decide, pass2441_2411, by decide, by decide, pass2441_2445, by decide, by decide, pass2441_2533, rfl⟩
def src2442 : Request := ⟨⟨⟨1000,1395,301,14762⟩,30103476895744,104105680031⟩,0,3,1,385610,14⟩
private theorem pass2442_2390 : (Triangular src2442) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2442_2391 : (Triangular src2442) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2442_2393 : (Triangular src2442) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2442_2399 : (Triangular src2442) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2442_2415 : (Triangular src2442) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2442_2459 : (Triangular src2442) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2442 : Cover (Triangular src2442) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2442_2390, by decide, by decide, pass2442_2391, by decide, by decide, pass2442_2393, by decide, by decide, pass2442_2399, by decide, by decide, pass2442_2415, by decide, by decide, pass2442_2459, rfl⟩
def src2443 : Request := ⟨⟨⟨1000,1395,301,15535⟩,30103476895744,104105680031⟩,1,3,1,385610,14⟩
private theorem pass2443_2390 : (Triangular src2443) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2443_2391 : (Triangular src2443) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2443_2393 : (Triangular src2443) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2443_2399 : (Triangular src2443) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2443_2415 : (Triangular src2443) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2443_2459 : (Triangular src2443) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2443 : Cover (Triangular src2443) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2443_2390, by decide, by decide, pass2443_2391, by decide, by decide, pass2443_2393, by decide, by decide, pass2443_2399, by decide, by decide, pass2443_2415, by decide, by decide, pass2443_2459, rfl⟩
def src2444 : Request := ⟨⟨⟨1450,2023,445,19992⟩,92998964346880,466511127281⟩,3,3,1,385610,14⟩
private theorem pass2444_2390 : (Triangular src2444) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2444_2391 : (Triangular src2444) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2444_2393 : (Triangular src2444) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2444_2399 : (Triangular src2444) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2444_2415 : (Triangular src2444) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2444_2457 : (Triangular src2444) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2444 : Cover (Triangular src2444) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2444_2390, by decide, by decide, pass2444_2391, by decide, by decide, pass2444_2393, by decide, by decide, pass2444_2399, by decide, by decide, pass2444_2415, by decide, by decide, pass2444_2457, rfl⟩
def src2445 : Request := ⟨⟨⟨1450,2023,445,22168⟩,92998964346880,466511127281⟩,6,3,1,385610,14⟩
private theorem pass2445_2390 : (Triangular src2445) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2445_2391 : (Triangular src2445) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2445_2393 : (Triangular src2445) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2445_2399 : (Triangular src2445) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2445_2415 : (Triangular src2445) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2445_2457 : (Triangular src2445) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2445 : Cover (Triangular src2445) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2445_2390, by decide, by decide, pass2445_2391, by decide, by decide, pass2445_2393, by decide, by decide, pass2445_2399, by decide, by decide, pass2445_2415, by decide, by decide, pass2445_2457, rfl⟩
def src2446 : Request := ⟨⟨⟨1750,2442,527,27780⟩,161065121873920,975196209190⟩,10,3,1,385610,14⟩
private theorem pass2446_2390 : (Triangular src2446) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2446_2391 : (Triangular src2446) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2446_2393 : (Triangular src2446) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2446_2399 : (Triangular src2446) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2446_2415 : (Triangular src2446) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2446_2457 : (Triangular src2446) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2446 : Cover (Triangular src2446) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2446_2390, by decide, by decide, pass2446_2391, by decide, by decide, pass2446_2393, by decide, by decide, pass2446_2399, by decide, by decide, pass2446_2415, by decide, by decide, pass2446_2457, rfl⟩
def src2447 : Request := ⟨⟨⟨2100,2930,632,32500⟩,278060332482560,2019119590628⟩,13,3,1,385610,14⟩
private theorem pass2447_2390 : (Triangular src2447) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2447_2391 : (Triangular src2447) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2447_2393 : (Triangular src2447) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2447_2398 : (Triangular src2447) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2447_2412 : (Triangular src2447) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2447_2449 : (Triangular src2447) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2447 : Cover (Triangular src2447) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2447_2390, by decide, by decide, pass2447_2391, by decide, by decide, pass2447_2393, by decide, by decide, pass2447_2398, by decide, by decide, pass2447_2412, by decide, by decide, pass2447_2449, rfl⟩
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
  physicalFloor := 385610
  seedFloor := 13

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨3, 13, 10, 90/100, 80/100, ![880853640420, 190957770179, 15249587080, 2346111390], 1907244779442572⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 14 385610 := by
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

def price : Pricing := ⟨55/100, 90/100, [254361108, 332446591, 332653851, 333049493, 332388965, 333022292, 332623312, 332462737, 166874970, 167096211, 166965312, 166883337, 167120801, 69505862, 71417432, 89225427, 102844604, 102884774, 124777155, 100000000, 222713304], [1425350, 1036494, 1035925, 1034840, 1036652, 1034914, 1036009, 1036449, 2288794, 2285111, 2287290, 2288654, 2284702, 5775589, 5619555, 4459229, 3838761, 3837064, 3133365, 3958949, 1674361],
  ![118220676029280, 1620174796356, 200441973600, 4711149310], 139390191681703265⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.middle _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
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
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2448 : Request := ⟨⟨⟨2100,2930,632,39443⟩,278060332482560,2019119590628⟩,20,3,1,385610,14⟩
private theorem pass2448_2390 : (Triangular src2448) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2448_2391 : (Triangular src2448) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2448_2393 : (Triangular src2448) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2448_2398 : (Triangular src2448) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2448_2412 : (Triangular src2448) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2448_2449 : (Triangular src2448) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2448 : Cover (Triangular src2448) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2448_2390, by decide, by decide, pass2448_2391, by decide, by decide, pass2448_2393, by decide, by decide, pass2448_2398, by decide, by decide, pass2448_2412, by decide, by decide, pass2448_2449, rfl⟩
def src2449 : Request := ⟨⟨⟨3200,4465,963,45754⟩,983050615259136,10877088344236⟩,20,3,1,385610,14⟩
private theorem pass2449_2390 : (Triangular src2449) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2449_2391 : (Triangular src2449) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2449_2393 : (Triangular src2449) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2449_2398 : (Triangular src2449) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2449_2411 : (Triangular src2449) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2449_2446 : (Triangular src2449) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2449 : Cover (Triangular src2449) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass2449_2390, by decide, by decide, pass2449_2391, by decide, by decide, pass2449_2393, by decide, by decide, pass2449_2398, by decide, by decide, pass2449_2411, by decide, by decide, pass2449_2446, rfl⟩
def src2450 : Request := ⟨⟨⟨5700,7953,1716,86116⟩,5553838907981824,109428971647179⟩,50,3,1,385610,14⟩
private theorem pass2450_2390 : (Triangular src2450) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2450_2391 : (Triangular src2450) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2450_2393 : (Triangular src2450) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2450_2398 : (Triangular src2450) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2450_2411 : (Triangular src2450) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2450_2445 : (Triangular src2450) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2450_2533 : (Triangular src2450) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2450 : Cover (Triangular src2450) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2450_2390, by decide, by decide, pass2450_2391, by decide, by decide, pass2450_2393, by decide, by decide, pass2450_2398, by decide, by decide, pass2450_2411, by decide, by decide, pass2450_2445, by decide, by decide, pass2450_2533, rfl⟩
def src2451 : Request := ⟨⟨⟨5700,7952,1716,126274⟩,5553838907981824,109384694947514⟩,85,3,1,385610,14⟩
private theorem pass2451_2390 : (Triangular src2451) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2451_2391 : (Triangular src2451) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2451_2393 : (Triangular src2451) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2451_2398 : (Triangular src2451) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2451_2411 : (Triangular src2451) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2451_2445 : (Triangular src2451) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2451_2533 : (Triangular src2451) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2451 : Cover (Triangular src2451) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2451_2390, by decide, by decide, pass2451_2391, by decide, by decide, pass2451_2393, by decide, by decide, pass2451_2398, by decide, by decide, pass2451_2411, by decide, by decide, pass2451_2445, by decide, by decide, pass2451_2533, rfl⟩
def src2452 : Request := ⟨⟨⟨8300,11581,2498,131625⟩,17139238515245056,491743896877039⟩,85,3,1,385610,14⟩
private theorem pass2452_2390 : (Triangular src2452) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2452_2391 : (Triangular src2452) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2452_2393 : (Triangular src2452) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2452_2398 : (Triangular src2452) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2452_2411 : (Triangular src2452) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2452_2445 : (Triangular src2452) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2452_2533 : (Triangular src2452) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2452 : Cover (Triangular src2452) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2452_2390, by decide, by decide, pass2452_2391, by decide, by decide, pass2452_2393, by decide, by decide, pass2452_2398, by decide, by decide, pass2452_2411, by decide, by decide, pass2452_2445, by decide, by decide, pass2452_2533, rfl⟩
def src2453 : Request := ⟨⟨⟨1000,1395,296,14495⟩,29722184515584,102755930405⟩,0,3,1,385610,15⟩
private theorem pass2453_2390 : (Triangular src2453) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2453_2391 : (Triangular src2453) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2453_2393 : (Triangular src2453) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2453_2399 : (Triangular src2453) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2453_2416 : (Triangular src2453) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2453_2463 : (Triangular src2453) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2453 : Cover (Triangular src2453) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2453_2390, by decide, by decide, pass2453_2391, by decide, by decide, pass2453_2393, by decide, by decide, pass2453_2399, by decide, by decide, pass2453_2416, by decide, by decide, pass2453_2463, rfl⟩
def src2454 : Request := ⟨⟨⟨1200,1674,368,15667⟩,52718727069696,218807905514⟩,1,3,1,385610,15⟩
private theorem pass2454_2390 : (Triangular src2454) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2454_2391 : (Triangular src2454) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2454_2393 : (Triangular src2454) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2454_2399 : (Triangular src2454) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2454_2415 : (Triangular src2454) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2454_2458 : (Triangular src2454) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2454 : Cover (Triangular src2454) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2454_2390, by decide, by decide, pass2454_2391, by decide, by decide, pass2454_2393, by decide, by decide, pass2454_2399, by decide, by decide, pass2454_2415, by decide, by decide, pass2454_2458, rfl⟩
def src2455 : Request := ⟨⟨⟨1200,1674,361,16647⟩,51955677528064,215563369662⟩,2,3,1,385610,15⟩
private theorem pass2455_2390 : (Triangular src2455) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2455_2391 : (Triangular src2455) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2455_2393 : (Triangular src2455) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2455_2399 : (Triangular src2455) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2455_2415 : (Triangular src2455) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2455_2459 : (Triangular src2455) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2455 : Cover (Triangular src2455) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2455_2390, by decide, by decide, pass2455_2391, by decide, by decide, pass2455_2393, by decide, by decide, pass2455_2399, by decide, by decide, pass2455_2415, by decide, by decide, pass2455_2459, rfl⟩
def src2456 : Request := ⟨⟨⟨1200,1674,361,18127⟩,51955677528064,215563369662⟩,4,3,1,385610,15⟩
private theorem pass2456_2390 : (Triangular src2456) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2456_2391 : (Triangular src2456) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2456_2393 : (Triangular src2456) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2456_2399 : (Triangular src2456) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2456_2415 : (Triangular src2456) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2456_2459 : (Triangular src2456) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2456 : Cover (Triangular src2456) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2456_2390, by decide, by decide, pass2456_2391, by decide, by decide, pass2456_2393, by decide, by decide, pass2456_2399, by decide, by decide, pass2456_2415, by decide, by decide, pass2456_2459, rfl⟩
def src2457 : Request := ⟨⟨⟨1450,2023,445,22351⟩,92998964346880,466511127281⟩,8,3,1,385610,15⟩
private theorem pass2457_2390 : (Triangular src2457) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2457_2391 : (Triangular src2457) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2457_2393 : (Triangular src2457) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2457_2399 : (Triangular src2457) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2457_2415 : (Triangular src2457) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2457_2457 : (Triangular src2457) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2457 : Cover (Triangular src2457) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2457_2390, by decide, by decide, pass2457_2391, by decide, by decide, pass2457_2393, by decide, by decide, pass2457_2399, by decide, by decide, pass2457_2415, by decide, by decide, pass2457_2457, rfl⟩
def src2458 : Request := ⟨⟨⟨2100,2930,632,28440⟩,278060332482560,2019119590628⟩,10,3,1,385610,15⟩
private theorem pass2458_2390 : (Triangular src2458) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2458_2391 : (Triangular src2458) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2458_2393 : (Triangular src2458) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2458_2398 : (Triangular src2458) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2458_2412 : (Triangular src2458) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2458_2449 : (Triangular src2458) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2458 : Cover (Triangular src2458) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2458_2390, by decide, by decide, pass2458_2391, by decide, by decide, pass2458_2393, by decide, by decide, pass2458_2398, by decide, by decide, pass2458_2412, by decide, by decide, pass2458_2449, rfl⟩
def src2459 : Request := ⟨⟨⟨2100,2930,632,32940⟩,278060332482560,2019119590628⟩,16,3,1,385610,15⟩
private theorem pass2459_2390 : (Triangular src2459) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2459_2391 : (Triangular src2459) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2459_2393 : (Triangular src2459) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2459_2398 : (Triangular src2459) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2459_2412 : (Triangular src2459) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2459_2449 : (Triangular src2459) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2459 : Cover (Triangular src2459) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2459_2390, by decide, by decide, pass2459_2391, by decide, by decide, pass2459_2393, by decide, by decide, pass2459_2398, by decide, by decide, pass2459_2412, by decide, by decide, pass2459_2449, rfl⟩
def src2460 : Request := ⟨⟨⟨3200,4465,963,46443⟩,983050615259136,10877088344236⟩,25,3,1,385610,15⟩
private theorem pass2460_2390 : (Triangular src2460) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2460_2391 : (Triangular src2460) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2460_2393 : (Triangular src2460) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2460_2398 : (Triangular src2460) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2460_2411 : (Triangular src2460) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2460_2446 : (Triangular src2460) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2460 : Cover (Triangular src2460) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass2460_2390, by decide, by decide, pass2460_2391, by decide, by decide, pass2460_2393, by decide, by decide, pass2460_2398, by decide, by decide, pass2460_2411, by decide, by decide, pass2460_2446, rfl⟩
def src2461 : Request := ⟨⟨⟨4800,6697,1445,75627⟩,3317023033262080,55032215749682⟩,50,3,1,385610,15⟩
private theorem pass2461_2390 : (Triangular src2461) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2461_2391 : (Triangular src2461) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2461_2393 : (Triangular src2461) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2461_2398 : (Triangular src2461) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2461_2411 : (Triangular src2461) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2461_2445 : (Triangular src2461) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2461_2534 : (Triangular src2461) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2461 : Cover (Triangular src2461) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2461_2390, by decide, by decide, pass2461_2391, by decide, by decide, pass2461_2393, by decide, by decide, pass2461_2398, by decide, by decide, pass2461_2411, by decide, by decide, pass2461_2445, by decide, by decide, pass2461_2534, rfl⟩
def src2462 : Request := ⟨⟨⟨5700,7952,1716,117871⟩,5553838907981824,109384694947514⟩,85,3,1,385610,15⟩
private theorem pass2462_2390 : (Triangular src2462) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2462_2391 : (Triangular src2462) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2462_2393 : (Triangular src2462) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2462_2398 : (Triangular src2462) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2462_2411 : (Triangular src2462) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2462_2445 : (Triangular src2462) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2462_2533 : (Triangular src2462) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2462 : Cover (Triangular src2462) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2462_2390, by decide, by decide, pass2462_2391, by decide, by decide, pass2462_2393, by decide, by decide, pass2462_2398, by decide, by decide, pass2462_2411, by decide, by decide, pass2462_2445, by decide, by decide, pass2462_2533, rfl⟩
def src2463 : Request := ⟨⟨⟨10000,13954,3070,132019⟩,30428373265940480,1052440252760428⟩,85,3,1,385610,15⟩
private theorem pass2463_2390 : (Triangular src2463) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2463_2391 : (Triangular src2463) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2463_2393 : (Triangular src2463) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2463_2398 : (Triangular src2463) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2463_2411 : (Triangular src2463) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2463_2444 : (Triangular src2463) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2463_2529 : (Triangular src2463) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2463 : Cover (Triangular src2463) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2463_2390, by decide, by decide, pass2463_2391, by decide, by decide, pass2463_2393, by decide, by decide, pass2463_2398, by decide, by decide, pass2463_2411, by decide, by decide, pass2463_2444, by decide, by decide, pass2463_2529, rfl⟩
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
  physicalFloor := 385610
  seedFloor := 14

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨3, 14, 10, 90/100, 80/100, ![718149159000, 152150724367, 13629147952, 1947038622], 1780798756031214⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5692/43, 75149/43, 245075/43, 883918/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle39
end Z6969Source1951

end Merged_Z6969Pack0741

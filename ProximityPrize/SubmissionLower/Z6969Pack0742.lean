import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0741
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0739
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0742
section Merged_Z6969Pack0742

-- Source: Research6969.PrefixMiddleSaved39
section Z6969Source1952
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved39
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle39.price Lower6960.Prefix6969RescueData.Middle39.price :=
  ⟨335, 3895, 132, 1747, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle39.plan Lower6960.Prefix6969RescueData.Middle39.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 14 14 :=
  ⟨Lower6960.Prefix6969MainCases.Middle39.plan, Lower6960.Prefix6969MainCases.Middle39.price, Lower6960.Prefix6969MainCases.Middle39.valid, Lower6960.Prefix6969MainCases.Middle39.priced, Lower6960.Prefix6969MainCases.Middle39.sources,
   Lower6960.Prefix6969RescueData.Middle39.plan, Lower6960.Prefix6969RescueData.Middle39.price, Lower6960.Prefix6969RescueData.Middle39.sources, Lower6960.Prefix6969RescueData.Middle39.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved39
end Z6969Source1952

-- Source: Research6969.PrefixMainDataMiddle40
section Z6969Source1953
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle40
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank30 1501, bank40 1714, bank49 2130, bank58 2054, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank126 11206, bank153 5200, bank199 7608, bank184 20384, bank212 8810, bank174 26788, bank169 29097] i
  head := src2937
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15027, 126218, 586028, 2150230],
    ![12303, 99431, 449557, 1613535],
    ![53398/9, 432256/9, 449557, 1613535],
    ![29433/8, 234021/8, 706228/3, 832104],
    ![63824/25, 505868/25, 313709/2, 2253001/4],
    ![72196/49, 574082/49, 2587366/25, 9142476/25],
    ![40539/50, 338403/50, 71355, 1134225/4],
    ![95180/121, 722560/121, 3249896/49, 1565148/7],
    ![95180/121, 722560/121, 116003/2, 870489/4],
    ![63754/121, 252044/49, 770661/16, 1501902/7],
    ![63754/121, 252044/49, 770661/16, 199136],
    ![63754/121, 610067/121, 770661/16, 10735564/75],
    ![1355575/3362, 610067/121, 770661/16, 10735564/75],
    ![1355575/3362, 7248464/1681, 1999400/49, 6760000/49],
    ![1355575/3362, 1769020/441, 4332756/121, 9018016/75],
    ![958363/2738, 1769020/441, 4332756/121, 9018016/75],
    ![958363/2738, 10599953/2738, 47607595/1352, 9018016/75],
    ![462882/1369, 10599953/2738, 47607595/1352, 9018016/75],
    ![459151/1369, 10599953/2738, 47607595/1352, 9018016/75]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 15 385541 := by
  refine ⟨?_, rank154 5334, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2937⟩⟩
  · intro i; fin_cases i
    · exact free4_1
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
    · exact free153_1
    · exact free199_1
    · exact free184_1
    · exact free212_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [255762014, 333675728, 332228889, 333035189, 332635148, 332718572, 332883017, 146544048, 146408087, 146428099, 146383192, 73141485, 73161145, 70099261, 101257817, 101843591, 124641107, 100000000, 233550300], [1418498, 1033357, 1037327, 1035115, 1036212, 1035983, 1035532, 2629916, 2632901, 2632461, 2633447, 5483632, 5482067, 5725738, 3906694, 3881939, 3137887, 3959851, 1585526],
  ![123973170246000, 1608416470500, 210195270000, 5838922680], 141968003810057325⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,8,8,8,8,15,15,15,11,11,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 10599953/2738, 47607595/1352, 9018016/75] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle40
end Z6969Source1953

-- Source: Research6969.PrefixRescueDataMiddle40
section Z6969Source1954
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle40
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,15⟩
  bank i := ![bank220 14495, bank228 15667, bank227 16647, bank227 18127, bank237 22351, bank252 28440, bank252 32940, bank303 46443, bank328 75627, bank342 117871, bank385 132019] i
  reserve i := ![0, 1, 2, 4, 8, 10, 16, 25, 50, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 15

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank220 14495
    · exact rank228 15667
    · exact rank227 16647
    · exact rank227 18127
    · exact rank237 22351
    · exact rank252 28440
    · exact rank252 32940
    · exact rank303 46443
    · exact rank328 75627
    · exact rank342 117871
    · exact rank385 132019
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2453⟩
    · exact ⟨_, cover2454⟩
    · exact ⟨_, cover2455⟩
    · exact ⟨_, cover2456⟩
    · exact ⟨_, cover2457⟩
    · exact ⟨_, cover2458⟩
    · exact ⟨_, cover2459⟩
    · exact ⟨_, cover2460⟩
    · exact ⟨_, cover2461⟩
    · exact ⟨_, cover2462⟩
    · exact ⟨_, cover2463⟩

def price : EarlyPrice := ⟨3, 15, 10, 90/100, 80/100, ![771748749060, 166525791501, 17946421800, 2392877730], 1847682334049603⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5692/43, 143611/86, 472893/86, 1768065/86] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle40
end Z6969Source1954

-- Source: Research6969.PrefixMiddleSaved40
section Z6969Source1955
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved40
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle40.price Lower6960.Prefix6969RescueData.Middle40.price :=
  ⟨335, 3871, 132, 1669, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle40.plan Lower6960.Prefix6969RescueData.Middle40.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 15 15 :=
  ⟨Lower6960.Prefix6969MainCases.Middle40.plan, Lower6960.Prefix6969MainCases.Middle40.price, Lower6960.Prefix6969MainCases.Middle40.valid, Lower6960.Prefix6969MainCases.Middle40.priced, Lower6960.Prefix6969MainCases.Middle40.sources,
   Lower6960.Prefix6969RescueData.Middle40.plan, Lower6960.Prefix6969RescueData.Middle40.price, Lower6960.Prefix6969RescueData.Middle40.sources, Lower6960.Prefix6969RescueData.Middle40.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved40
end Z6969Source1955

-- Source: Research6969.PrefixMainDataMiddle41
section Z6969Source1956
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle41
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank5 1094, bank12 1187, bank18 1295, bank24 1404, bank30 1501, bank40 1714, bank49 2130, bank58 2054, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank126 11206, bank153 5200, bank199 7608, bank184 20384, bank212 8810, bank175 25973, bank169 29097] i
  head := src2938
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15228, 126081, 586421, 2121506],
    ![25247/2, 396743/4, 895509/2, 6254303/4],
    ![54680/9, 430910/9, 895509/2, 6254303/4],
    ![29433/8, 465247/16, 2106074/9, 821964],
    ![63824/25, 502813/25, 313709/2, 2253001/4],
    ![72196/49, 570637/49, 2571961/25, 9031066/25],
    ![40539/50, 672971/100, 71355, 1134225/4],
    ![95180/121, 718010/121, 3229616/49, 10822526/49],
    ![95180/121, 718010/121, 116003/2, 870489/4],
    ![63754/121, 752362/147, 770661/16, 10385199/49],
    ![63754/121, 752362/147, 770661/16, 590128/3],
    ![63754/121, 605907/121, 770661/16, 9114361/64],
    ![1355575/3362, 605907/121, 770661/16, 9114361/64],
    ![1355575/3362, 7203224/1681, 1999400/49, 6760000/49],
    ![1355575/3362, 195330/49, 4332756/121, 14470416/121],
    ![958363/2738, 195330/49, 4332756/121, 14470416/121],
    ![958363/2738, 21069321/5476, 94635065/2704, 14470416/121],
    ![929061/2738, 21069321/5476, 94635065/2704, 14470416/121],
    ![459151/1369, 21069321/5476, 94635065/2704, 14470416/121]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 16 385541 := by
  refine ⟨?_, rank154 5269, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2938⟩⟩
  · intro i; fin_cases i
    · exact free5_1
    · exact free12_1
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
    · exact free184_1
    · exact free212_1
    · exact free175_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [255828664, 332610194, 332008756, 332562295, 332078333, 332283951, 330699034, 157628592, 157797761, 157612009, 157635269, 72844296, 72894861, 69844803, 100803763, 100978260, 100000000, 100000000, 233437100], [1418157, 1036281, 1037931, 1036412, 1037740, 1037176, 1041525, 2443250, 2440434, 2443526, 2443139, 5507283, 5503259, 5746149, 3925883, 3918509, 3959851, 3959851, 1586458],
  ![123913081422000, 1608538915120, 210093390000, 5859736800], 141710146945717241⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,7,7,7,7,15,15,16,11,11,11,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 21069321/5476, 94635065/2704, 14470416/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle41
end Z6969Source1956

-- Source: Research6969.PhysicalChecks154
section Z6969Source1957
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2464 : Request := ⟨⟨⟨1000,1395,301,13011⟩,30103476895744,104105680031⟩,0,3,1,385541,16⟩
theorem cover2464 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2464) 2557 2412 [2414, 2423, 2447, 2514, 2557] := triangleCover (by decide +kernel)
def src2465 : Request := ⟨⟨⟨1000,1395,301,13664⟩,30103476895744,104105680031⟩,1,3,1,385541,16⟩
theorem cover2465 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2465) 2557 2412 [2414, 2423, 2447, 2514, 2557] := triangleCover (by decide +kernel)
def src2466 : Request := ⟨⟨⟨1200,1674,361,16978⟩,51955677528064,215563369662⟩,4,3,1,385541,16⟩
theorem cover2466 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2466) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2467 : Request := ⟨⟨⟨1750,2442,527,24422⟩,161065121873920,975196209190⟩,10,3,1,385541,16⟩
theorem cover2467 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2467) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2468 : Request := ⟨⟨⟨3200,4465,982,42450⟩,997767489781760,11043969901736⟩,25,3,1,385541,16⟩
theorem cover2468 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2468) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2469 : Request := ⟨⟨⟨3200,4464,963,57229⟩,983050615259136,10869251283552⟩,40,3,1,385541,16⟩
theorem cover2469 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2469) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2470 : Request := ⟨⟨⟨8300,11581,2498,115777⟩,17139238515245056,491743896877039⟩,85,3,1,385541,16⟩
theorem cover2470 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2470) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2471 : Request := ⟨⟨⟨6900,9626,2077,140521⟩,9849424459857920,234809190715807⟩,110,3,1,385541,16⟩
theorem cover2471 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2471) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2472 : Request := ⟨⟨⟨10000,13953,3010,143548⟩,29974681586237440,1036125345444439⟩,110,3,1,385541,16⟩
theorem cover2472 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2472) 2557 2412 [2413, 2418, 2431, 2465, 2552, 2557] := triangleCover (by decide +kernel)
def src2473 : Request := ⟨⟨⟨1000,1395,301,12199⟩,30103476895744,104105680031⟩,0,3,1,385541,17⟩
theorem cover2473 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2473) 2557 2412 [2414, 2423, 2447, 2514, 2557] := triangleCover (by decide +kernel)
def src2474 : Request := ⟨⟨⟨1000,1395,301,12793⟩,30103476895744,104105680031⟩,1,3,1,385541,17⟩
theorem cover2474 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2474) 2557 2412 [2414, 2423, 2447, 2514, 2557] := triangleCover (by decide +kernel)
def src2475 : Request := ⟨⟨⟨1200,1674,361,14649⟩,51955677528064,215563369662⟩,2,3,1,385541,17⟩
theorem cover2475 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2475) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2476 : Request := ⟨⟨⟨1200,1674,368,15461⟩,52718727069696,218807905514⟩,4,3,1,385541,17⟩
theorem cover2476 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2476) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2477 : Request := ⟨⟨⟨1450,2023,445,18090⟩,92998964346880,466511127281⟩,6,3,1,385541,17⟩
theorem cover2477 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2477) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2478 : Request := ⟨⟨⟨1750,2442,527,22857⟩,161065121873920,975196209190⟩,10,3,1,385541,17⟩
theorem cover2478 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2478) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2479 : Request := ⟨⟨⟨2600,3628,783,34112⟩,527755772952576,4745819470168⟩,20,3,1,385541,17⟩
theorem cover2479 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2479) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1957

-- Source: Research6969.PrefixRescueDataMiddle41
section Z6969Source1958
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle41
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 9
  positive := by decide
  primeShape := ⟨0,3,1,16⟩
  bank i := ![bank221 13011, bank221 13664, bank227 16978, bank245 24422, bank304 42450, bank299 57229, bank371 115777, bank355 140521, bank382 143548] i
  reserve i := ![0, 1, 4, 10, 25, 40, 85, 110, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 16

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 13011
    · exact rank221 13664
    · exact rank227 16978
    · exact rank245 24422
    · exact rank304 42450
    · exact rank299 57229
    · exact rank371 115777
    · exact rank355 140521
    · exact rank382 143548
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2464⟩
    · exact ⟨_, cover2465⟩
    · exact ⟨_, cover2466⟩
    · exact ⟨_, cover2467⟩
    · exact ⟨_, cover2468⟩
    · exact ⟨_, cover2469⟩
    · exact ⟨_, cover2470⟩
    · exact ⟨_, cover2471⟩
    · exact ⟨_, cover2472⟩

def price : EarlyPrice := ⟨3, 16, 8, 90/100, 70/100, ![895087237888, 180121504580, 18768722560, 2346111390], 1780190551692195⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![13780/111, 173753/111, 575579/111, 2248336/111] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle41
end Z6969Source1958

-- Source: Research6969.PrefixMiddleSaved41
section Z6969Source1959
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved41
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle41.price Lower6960.Prefix6969RescueData.Middle41.price :=
  ⟨335, 3847, 124, 1565, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle41.plan Lower6960.Prefix6969RescueData.Middle41.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 16 16 :=
  ⟨Lower6960.Prefix6969MainCases.Middle41.plan, Lower6960.Prefix6969MainCases.Middle41.price, Lower6960.Prefix6969MainCases.Middle41.valid, Lower6960.Prefix6969MainCases.Middle41.priced, Lower6960.Prefix6969MainCases.Middle41.sources,
   Lower6960.Prefix6969RescueData.Middle41.plan, Lower6960.Prefix6969RescueData.Middle41.price, Lower6960.Prefix6969RescueData.Middle41.sources, Lower6960.Prefix6969RescueData.Middle41.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved41
end Z6969Source1959

-- Source: Research6969.PrefixMainDataMiddle42
section Z6969Source1960
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle42
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 15, 21, 14, 18, 21, 30, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank9 1210, bank17 1319, bank24 1404, bank34 1629, bank44 1848, bank54 2149, bank65 2772, bank84 3942, bank85 2394, bank105 2759, bank137 3019, bank168 3916, bank126 11206, bank153 5200, bank199 7608, bank180 21819, bank212 8810, bank170 28384] i
  head := src2939
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15035, 125622, 584840, 2150550],
    ![12303, 98270, 888665/2, 3149025/2],
    ![53398/9, 427225/9, 888665/2, 3149025/2],
    ![29433/8, 462495/16, 697886/3, 811980],
    ![33449/18, 177325/12, 150168, 8478945/16],
    ![18775/16, 600435/64, 304304/3, 379456],
    ![89110/121, 703655/121, 455614/7, 1597935/7],
    ![89110/121, 703655/121, 455614/7, 1597935/7],
    ![63754/121, 35650/7, 770661/16, 10259055/49],
    ![63754/121, 35650/7, 770661/16, 10259055/49],
    ![63754/121, 35650/7, 770661/16, 28721190/169],
    ![63754/121, 601811/121, 770661/16, 9114361/64],
    ![63754/121, 601811/121, 770661/16, 6794260/49],
    ![1355575/3362, 601811/121, 770661/16, 6794260/49],
    ![1355575/3362, 7158680/1681, 1999400/49, 6760000/49],
    ![1355575/3362, 1747090/441, 4332756/121, 14470416/121],
    ![25627/74, 1747090/441, 4332756/121, 14470416/121],
    ![25627/74, 20940745/5476, 94063865/2704, 160496175/1352],
    ![920087/2738, 20940745/5476, 94063865/2704, 160496175/1352]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 17 385541 := by
  refine ⟨?_, rank154 5205, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2939⟩⟩
  · intro i; fin_cases i
    · exact free5_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free34_1
    · exact free44_1
    · exact free54_1
    · exact free65_1
    · exact free84_1
    · exact free85_1
    · exact free105_1
    · exact free137_1
    · exact free168_1
    · exact free126_1
    · exact free153_1
    · exact free199_1
    · exact free180_1
    · exact free212_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [253304419, 329510753, 330177715, 330044972, 329088680, 329922430, 147280700, 147083292, 147301387, 147092033, 147361799, 109904066, 69402002, 69311542, 69594260, 100261959, 100579580, 100000000, 222245159], [1431087, 1044786, 1042956, 1043320, 1045945, 1043657, 2615523, 2618810, 2615179, 2618664, 2614173, 3586057, 5786329, 5794538, 5768883, 3948780, 3935357, 3959851, 1678596],
  ![117972175300380, 1620682657636, 200020643100, 5882920380], 137908214830351582⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,7,7,7,7,7,10,16,16,16,11,11,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 20940745/5476, 94063865/2704, 160496175/1352] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle42
end Z6969Source1960

-- Source: Research6969.PhysicalChecks155
section Z6969Source1961
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2480 : Request := ⟨⟨⟨3950,5511,1213,53370⟩,1877062482395136,25637257621145⟩,40,3,1,385541,17⟩
theorem cover2480 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2480) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2481 : Request := ⟨⟨⟨5700,7952,1716,101884⟩,5553838907981824,109384694947514⟩,85,3,1,385541,17⟩
theorem cover2481 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2481) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2482 : Request := ⟨⟨⟨10000,13953,3070,130391⟩,30428373265940480,1052197377228338⟩,110,3,1,385541,17⟩
theorem cover2482 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2482) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2483 : Request := ⟨⟨⟨825,1151,253,10172⟩,17161575202816,49010625289⟩,0,3,1,385541,18⟩
theorem cover2483 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2483) 2557 2412 [2415, 2426, 2456, 2540, 2557] := triangleCover (by decide +kernel)
def src2484 : Request := ⟨⟨⟨1200,1674,368,12863⟩,52718727069696,218807905514⟩,1,3,1,385541,18⟩
theorem cover2484 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2484) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2485 : Request := ⟨⟨⟨1200,1674,361,13734⟩,51955677528064,215563369662⟩,2,3,1,385541,18⟩
theorem cover2485 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2485) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2486 : Request := ⟨⟨⟨1200,1674,361,14850⟩,51955677528064,215563369662⟩,4,3,1,385541,18⟩
theorem cover2486 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2486) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2487 : Request := ⟨⟨⟨1750,2442,537,20773⟩,163381988556800,989573241440⟩,10,3,1,385541,18⟩
theorem cover2487 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2487) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2488 : Request := ⟨⟨⟨3950,5512,1213,45041⟩,1877062482395136,25652240151764⟩,32,3,1,385541,18⟩
theorem cover2488 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2488) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2489 : Request := ⟨⟨⟨4800,6697,1474,71730⟩,3367547627110400,55891290082931⟩,65,3,1,385541,18⟩
theorem cover2489 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2489) 2557 2412 [2413, 2418, 2431, 2464, 2550, 2557] := triangleCover (by decide +kernel)
def src2490 : Request := ⟨⟨⟨8300,11581,2548,98175⟩,17399709518790656,499402661779949⟩,85,3,1,385541,18⟩
theorem cover2490 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2490) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2491 : Request := ⟨⟨⟨6900,9626,2077,120560⟩,9849424459857920,234809190715807⟩,110,3,1,385541,18⟩
theorem cover2491 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2491) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2492 : Request := ⟨⟨⟨825,1151,253,9473⟩,17161575202816,49010625289⟩,0,3,1,385541,19⟩
theorem cover2492 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2492) 2557 2412 [2415, 2426, 2456, 2540, 2557] := triangleCover (by decide +kernel)
def src2493 : Request := ⟨⟨⟨1200,1674,368,12057⟩,52718727069696,218807905514⟩,1,3,1,385541,19⟩
theorem cover2493 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2493) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2494 : Request := ⟨⟨⟨1200,1674,361,12882⟩,51955677528064,215563369662⟩,2,3,1,385541,19⟩
theorem cover2494 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2494) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2495 : Request := ⟨⟨⟨1200,1674,361,13885⟩,51955677528064,215563369662⟩,4,3,1,385541,19⟩
theorem cover2495 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2495) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1961

-- Source: Research6969.PrefixRescueDataMiddle42
section Z6969Source1962
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle42
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,17⟩
  bank i := ![bank221 12199, bank221 12793, bank221 12793, bank227 14649, bank228 15461, bank237 18090, bank245 22857, bank270 34112, bank313 53370, bank342 101884, bank383 130391] i
  reserve i := ![0, 1, 1, 2, 4, 6, 10, 20, 40, 85, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 17

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 12199
    · exact rank221 12793
    · exact rank221 12793
    · exact rank227 14649
    · exact rank228 15461
    · exact rank237 18090
    · exact rank245 22857
    · exact rank270 34112
    · exact rank313 53370
    · exact rank342 101884
    · exact rank383 130391
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2473⟩
    · exact ⟨_, cover2474⟩
    · exact ⟨_, cover2474⟩
    · exact ⟨_, cover2475⟩
    · exact ⟨_, cover2476⟩
    · exact ⟨_, cover2477⟩
    · exact ⟨_, cover2478⟩
    · exact ⟨_, cover2479⟩
    · exact ⟨_, cover2480⟩
    · exact ⟨_, cover2481⟩
    · exact ⟨_, cover2482⟩

def price : EarlyPrice := ⟨3, 17, 10, 85/100, 80/100, ![863862671861, 173733566642, 20339274970, 2392877730], 1695987848480767⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5692/43, 65528/43, 5126, 2216647/111] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle42
end Z6969Source1962

-- Source: Research6969.PrefixMiddleSaved42
section Z6969Source1963
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved42
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle42.price Lower6960.Prefix6969RescueData.Middle42.price :=
  ⟨336, 3824, 132, 1523, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle42.plan Lower6960.Prefix6969RescueData.Middle42.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 17 17 :=
  ⟨Lower6960.Prefix6969MainCases.Middle42.plan, Lower6960.Prefix6969MainCases.Middle42.price, Lower6960.Prefix6969MainCases.Middle42.valid, Lower6960.Prefix6969MainCases.Middle42.priced, Lower6960.Prefix6969MainCases.Middle42.sources,
   Lower6960.Prefix6969RescueData.Middle42.plan, Lower6960.Prefix6969RescueData.Middle42.price, Lower6960.Prefix6969RescueData.Middle42.sources, Lower6960.Prefix6969RescueData.Middle42.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved42
end Z6969Source1963

end Merged_Z6969Pack0742

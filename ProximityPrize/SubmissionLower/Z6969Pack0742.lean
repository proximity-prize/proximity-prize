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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 15 385610 := by
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

def price : Pricing := ⟨55/100, 90/100, [255762014, 333675728, 332228889, 333035189, 332635148, 332718572, 332883017, 146544048, 146408087, 146428099, 146383192, 73141485, 73161145, 70099261, 101257817, 101843591, 124641107, 100000000, 233550300], [1418175, 1033121, 1037091, 1034879, 1035976, 1035747, 1035296, 2629317, 2632301, 2631862, 2632847, 5482383, 5480819, 5724434, 3905805, 3881055, 3137172, 3958949, 1585165],
  ![123973170246000, 1608416470500, 210195270000, 5838922680], 141963275577745013⟩

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
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
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
  physicalFloor := 385610
  seedFloor := 15

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨3, 15, 10, 90/100, 80/100, ![771748749060, 166525791501, 17946421800, 2392877730], 1847293037027567⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 16 385610 := by
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

def price : Pricing := ⟨55/100, 90/100, [255828664, 332610194, 332008756, 332562295, 332078333, 332283951, 330699034, 157628592, 157797761, 157612009, 157635269, 72844296, 72894861, 69844803, 100803763, 100978260, 100000000, 100000000, 233437100], [1417834, 1036045, 1037695, 1036176, 1037504, 1036940, 1041288, 2442694, 2439878, 2442970, 2442583, 5506029, 5502005, 5744840, 3924989, 3917616, 3958949, 3958949, 1586096],
  ![123913081422000, 1608538915120, 210093390000, 5859736800], 141705398384577260⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2464 : Request := ⟨⟨⟨1000,1395,301,13011⟩,30103476895744,104105680031⟩,0,3,1,385610,16⟩
private theorem pass2464_2390 : (Triangular src2464) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2464_2391 : (Triangular src2464) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2464_2393 : (Triangular src2464) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2464_2399 : (Triangular src2464) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2464_2415 : (Triangular src2464) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2464_2459 : (Triangular src2464) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2464 : Cover (Triangular src2464) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2464_2390, by decide, by decide, pass2464_2391, by decide, by decide, pass2464_2393, by decide, by decide, pass2464_2399, by decide, by decide, pass2464_2415, by decide, by decide, pass2464_2459, rfl⟩
def src2465 : Request := ⟨⟨⟨1000,1395,301,13664⟩,30103476895744,104105680031⟩,1,3,1,385610,16⟩
private theorem pass2465_2390 : (Triangular src2465) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2465_2391 : (Triangular src2465) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2465_2393 : (Triangular src2465) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2465_2399 : (Triangular src2465) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2465_2415 : (Triangular src2465) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2465_2459 : (Triangular src2465) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2465 : Cover (Triangular src2465) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2465_2390, by decide, by decide, pass2465_2391, by decide, by decide, pass2465_2393, by decide, by decide, pass2465_2399, by decide, by decide, pass2465_2415, by decide, by decide, pass2465_2459, rfl⟩
def src2466 : Request := ⟨⟨⟨1200,1674,361,16978⟩,51955677528064,215563369662⟩,4,3,1,385610,16⟩
private theorem pass2466_2390 : (Triangular src2466) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2466_2391 : (Triangular src2466) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2466_2393 : (Triangular src2466) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2466_2399 : (Triangular src2466) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2466_2415 : (Triangular src2466) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2466_2459 : (Triangular src2466) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2466 : Cover (Triangular src2466) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2466_2390, by decide, by decide, pass2466_2391, by decide, by decide, pass2466_2393, by decide, by decide, pass2466_2399, by decide, by decide, pass2466_2415, by decide, by decide, pass2466_2459, rfl⟩
def src2467 : Request := ⟨⟨⟨1750,2442,527,24422⟩,161065121873920,975196209190⟩,10,3,1,385610,16⟩
private theorem pass2467_2390 : (Triangular src2467) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2467_2391 : (Triangular src2467) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2467_2393 : (Triangular src2467) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2467_2399 : (Triangular src2467) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2467_2415 : (Triangular src2467) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2467_2457 : (Triangular src2467) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2467 : Cover (Triangular src2467) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2467_2390, by decide, by decide, pass2467_2391, by decide, by decide, pass2467_2393, by decide, by decide, pass2467_2399, by decide, by decide, pass2467_2415, by decide, by decide, pass2467_2457, rfl⟩
def src2468 : Request := ⟨⟨⟨3200,4465,982,42450⟩,997767489781760,11043969901736⟩,25,3,1,385610,16⟩
private theorem pass2468_2390 : (Triangular src2468) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2468_2391 : (Triangular src2468) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2468_2393 : (Triangular src2468) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2468_2398 : (Triangular src2468) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2468_2411 : (Triangular src2468) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2468_2445 : (Triangular src2468) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2468_2534 : (Triangular src2468) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2468 : Cover (Triangular src2468) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2468_2390, by decide, by decide, pass2468_2391, by decide, by decide, pass2468_2393, by decide, by decide, pass2468_2398, by decide, by decide, pass2468_2411, by decide, by decide, pass2468_2445, by decide, by decide, pass2468_2534, rfl⟩
def src2469 : Request := ⟨⟨⟨3200,4464,963,57229⟩,983050615259136,10869251283552⟩,40,3,1,385610,16⟩
private theorem pass2469_2390 : (Triangular src2469) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2469_2391 : (Triangular src2469) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2469_2393 : (Triangular src2469) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2469_2398 : (Triangular src2469) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2469_2411 : (Triangular src2469) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2469_2446 : (Triangular src2469) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2469 : Cover (Triangular src2469) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass2469_2390, by decide, by decide, pass2469_2391, by decide, by decide, pass2469_2393, by decide, by decide, pass2469_2398, by decide, by decide, pass2469_2411, by decide, by decide, pass2469_2446, rfl⟩
def src2470 : Request := ⟨⟨⟨8300,11581,2498,115777⟩,17139238515245056,491743896877039⟩,85,3,1,385610,16⟩
private theorem pass2470_2390 : (Triangular src2470) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2470_2391 : (Triangular src2470) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2470_2393 : (Triangular src2470) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2470_2398 : (Triangular src2470) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2470_2411 : (Triangular src2470) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2470_2445 : (Triangular src2470) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2470_2533 : (Triangular src2470) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2470 : Cover (Triangular src2470) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2470_2390, by decide, by decide, pass2470_2391, by decide, by decide, pass2470_2393, by decide, by decide, pass2470_2398, by decide, by decide, pass2470_2411, by decide, by decide, pass2470_2445, by decide, by decide, pass2470_2533, rfl⟩
def src2471 : Request := ⟨⟨⟨6900,9626,2077,140521⟩,9849424459857920,234809190715807⟩,110,3,1,385610,16⟩
private theorem pass2471_2390 : (Triangular src2471) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2471_2391 : (Triangular src2471) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2471_2393 : (Triangular src2471) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2471_2398 : (Triangular src2471) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2471_2411 : (Triangular src2471) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2471_2445 : (Triangular src2471) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2471_2533 : (Triangular src2471) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2471 : Cover (Triangular src2471) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2471_2390, by decide, by decide, pass2471_2391, by decide, by decide, pass2471_2393, by decide, by decide, pass2471_2398, by decide, by decide, pass2471_2411, by decide, by decide, pass2471_2445, by decide, by decide, pass2471_2533, rfl⟩
def src2472 : Request := ⟨⟨⟨10000,13953,3010,143548⟩,29974681586237440,1036125345444439⟩,110,3,1,385610,16⟩
private theorem pass2472_2390 : (Triangular src2472) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2472_2391 : (Triangular src2472) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2472_2393 : (Triangular src2472) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2472_2398 : (Triangular src2472) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2472_2411 : (Triangular src2472) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2472_2445 : (Triangular src2472) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2472_2533 : (Triangular src2472) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2472 : Cover (Triangular src2472) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2472_2390, by decide, by decide, pass2472_2391, by decide, by decide, pass2472_2393, by decide, by decide, pass2472_2398, by decide, by decide, pass2472_2411, by decide, by decide, pass2472_2445, by decide, by decide, pass2472_2533, rfl⟩
def src2473 : Request := ⟨⟨⟨1000,1395,301,12199⟩,30103476895744,104105680031⟩,0,3,1,385610,17⟩
private theorem pass2473_2390 : (Triangular src2473) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2473_2391 : (Triangular src2473) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2473_2393 : (Triangular src2473) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2473_2399 : (Triangular src2473) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2473_2415 : (Triangular src2473) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2473_2459 : (Triangular src2473) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2473 : Cover (Triangular src2473) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2473_2390, by decide, by decide, pass2473_2391, by decide, by decide, pass2473_2393, by decide, by decide, pass2473_2399, by decide, by decide, pass2473_2415, by decide, by decide, pass2473_2459, rfl⟩
def src2474 : Request := ⟨⟨⟨1000,1395,301,12793⟩,30103476895744,104105680031⟩,1,3,1,385610,17⟩
private theorem pass2474_2390 : (Triangular src2474) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2474_2391 : (Triangular src2474) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2474_2393 : (Triangular src2474) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2474_2399 : (Triangular src2474) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2474_2415 : (Triangular src2474) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2474_2459 : (Triangular src2474) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2474 : Cover (Triangular src2474) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2474_2390, by decide, by decide, pass2474_2391, by decide, by decide, pass2474_2393, by decide, by decide, pass2474_2399, by decide, by decide, pass2474_2415, by decide, by decide, pass2474_2459, rfl⟩
def src2475 : Request := ⟨⟨⟨1200,1674,361,14649⟩,51955677528064,215563369662⟩,2,3,1,385610,17⟩
private theorem pass2475_2390 : (Triangular src2475) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2475_2391 : (Triangular src2475) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2475_2393 : (Triangular src2475) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2475_2399 : (Triangular src2475) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2475_2415 : (Triangular src2475) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2475_2459 : (Triangular src2475) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2475 : Cover (Triangular src2475) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2475_2390, by decide, by decide, pass2475_2391, by decide, by decide, pass2475_2393, by decide, by decide, pass2475_2399, by decide, by decide, pass2475_2415, by decide, by decide, pass2475_2459, rfl⟩
def src2476 : Request := ⟨⟨⟨1200,1674,368,15461⟩,52718727069696,218807905514⟩,4,3,1,385610,17⟩
private theorem pass2476_2390 : (Triangular src2476) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2476_2391 : (Triangular src2476) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2476_2393 : (Triangular src2476) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2476_2399 : (Triangular src2476) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2476_2415 : (Triangular src2476) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2476_2458 : (Triangular src2476) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2476 : Cover (Triangular src2476) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2476_2390, by decide, by decide, pass2476_2391, by decide, by decide, pass2476_2393, by decide, by decide, pass2476_2399, by decide, by decide, pass2476_2415, by decide, by decide, pass2476_2458, rfl⟩
def src2477 : Request := ⟨⟨⟨1450,2023,445,18090⟩,92998964346880,466511127281⟩,6,3,1,385610,17⟩
private theorem pass2477_2390 : (Triangular src2477) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2477_2391 : (Triangular src2477) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2477_2393 : (Triangular src2477) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2477_2399 : (Triangular src2477) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2477_2415 : (Triangular src2477) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2477_2457 : (Triangular src2477) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2477 : Cover (Triangular src2477) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2477_2390, by decide, by decide, pass2477_2391, by decide, by decide, pass2477_2393, by decide, by decide, pass2477_2399, by decide, by decide, pass2477_2415, by decide, by decide, pass2477_2457, rfl⟩
def src2478 : Request := ⟨⟨⟨1750,2442,527,22857⟩,161065121873920,975196209190⟩,10,3,1,385610,17⟩
private theorem pass2478_2390 : (Triangular src2478) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2478_2391 : (Triangular src2478) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2478_2393 : (Triangular src2478) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2478_2399 : (Triangular src2478) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2478_2415 : (Triangular src2478) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2478_2457 : (Triangular src2478) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2478 : Cover (Triangular src2478) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass2478_2390, by decide, by decide, pass2478_2391, by decide, by decide, pass2478_2393, by decide, by decide, pass2478_2399, by decide, by decide, pass2478_2415, by decide, by decide, pass2478_2457, rfl⟩
def src2479 : Request := ⟨⟨⟨2600,3628,783,34112⟩,527755772952576,4745819470168⟩,20,3,1,385610,17⟩
private theorem pass2479_2390 : (Triangular src2479) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2479_2391 : (Triangular src2479) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2479_2393 : (Triangular src2479) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2479_2398 : (Triangular src2479) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2479_2412 : (Triangular src2479) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2479_2448 : (Triangular src2479) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2479 : Cover (Triangular src2479) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass2479_2390, by decide, by decide, pass2479_2391, by decide, by decide, pass2479_2393, by decide, by decide, pass2479_2398, by decide, by decide, pass2479_2412, by decide, by decide, pass2479_2448, rfl⟩
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
  physicalFloor := 385610
  seedFloor := 16

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨3, 16, 8, 90/100, 70/100, ![895087237888, 180121504580, 18768722560, 2346111390], 1779815234462156⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 17 385610 := by
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

def price : Pricing := ⟨55/100, 90/100, [253304419, 329510753, 330177715, 330044972, 329088680, 329922430, 147280700, 147083292, 147301387, 147092033, 147361799, 109904066, 69402002, 69311542, 69594260, 100261959, 100579580, 100000000, 222245159], [1430761, 1044548, 1042719, 1043083, 1045706, 1043419, 2614928, 2618213, 2614583, 2618068, 2613578, 3585240, 5785011, 5793218, 5767569, 3947881, 3934461, 3958949, 1678214],
  ![117972175300380, 1620682657636, 200020643100, 5882920380], 137903408849389434⟩

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
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2480 : Request := ⟨⟨⟨3950,5511,1213,53370⟩,1877062482395136,25637257621145⟩,40,3,1,385610,17⟩
private theorem pass2480_2390 : (Triangular src2480) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2480_2391 : (Triangular src2480) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2480_2393 : (Triangular src2480) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2480_2398 : (Triangular src2480) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2480_2411 : (Triangular src2480) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2480_2445 : (Triangular src2480) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2480_2533 : (Triangular src2480) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2480 : Cover (Triangular src2480) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2480_2390, by decide, by decide, pass2480_2391, by decide, by decide, pass2480_2393, by decide, by decide, pass2480_2398, by decide, by decide, pass2480_2411, by decide, by decide, pass2480_2445, by decide, by decide, pass2480_2533, rfl⟩
def src2481 : Request := ⟨⟨⟨5700,7952,1716,101884⟩,5553838907981824,109384694947514⟩,85,3,1,385610,17⟩
private theorem pass2481_2390 : (Triangular src2481) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2481_2391 : (Triangular src2481) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2481_2393 : (Triangular src2481) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2481_2398 : (Triangular src2481) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2481_2411 : (Triangular src2481) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2481_2445 : (Triangular src2481) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2481_2533 : (Triangular src2481) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2481 : Cover (Triangular src2481) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2481_2390, by decide, by decide, pass2481_2391, by decide, by decide, pass2481_2393, by decide, by decide, pass2481_2398, by decide, by decide, pass2481_2411, by decide, by decide, pass2481_2445, by decide, by decide, pass2481_2533, rfl⟩
def src2482 : Request := ⟨⟨⟨10000,13953,3070,130391⟩,30428373265940480,1052197377228338⟩,110,3,1,385610,17⟩
private theorem pass2482_2390 : (Triangular src2482) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2482_2391 : (Triangular src2482) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2482_2393 : (Triangular src2482) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2482_2398 : (Triangular src2482) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2482_2411 : (Triangular src2482) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2482_2444 : (Triangular src2482) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2482_2529 : (Triangular src2482) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2482 : Cover (Triangular src2482) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2482_2390, by decide, by decide, pass2482_2391, by decide, by decide, pass2482_2393, by decide, by decide, pass2482_2398, by decide, by decide, pass2482_2411, by decide, by decide, pass2482_2444, by decide, by decide, pass2482_2529, rfl⟩
def src2483 : Request := ⟨⟨⟨825,1151,253,10172⟩,17161575202816,49010625289⟩,0,3,1,385610,18⟩
private theorem pass2483_2390 : (Triangular src2483) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2483_2391 : (Triangular src2483) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2483_2393 : (Triangular src2483) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2483_2399 : (Triangular src2483) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2483_2416 : (Triangular src2483) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2483_2463 : (Triangular src2483) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2483 : Cover (Triangular src2483) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2483_2390, by decide, by decide, pass2483_2391, by decide, by decide, pass2483_2393, by decide, by decide, pass2483_2399, by decide, by decide, pass2483_2416, by decide, by decide, pass2483_2463, rfl⟩
def src2484 : Request := ⟨⟨⟨1200,1674,368,12863⟩,52718727069696,218807905514⟩,1,3,1,385610,18⟩
private theorem pass2484_2390 : (Triangular src2484) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2484_2391 : (Triangular src2484) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2484_2393 : (Triangular src2484) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2484_2399 : (Triangular src2484) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2484_2415 : (Triangular src2484) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2484_2458 : (Triangular src2484) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2484 : Cover (Triangular src2484) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2484_2390, by decide, by decide, pass2484_2391, by decide, by decide, pass2484_2393, by decide, by decide, pass2484_2399, by decide, by decide, pass2484_2415, by decide, by decide, pass2484_2458, rfl⟩
def src2485 : Request := ⟨⟨⟨1200,1674,361,13734⟩,51955677528064,215563369662⟩,2,3,1,385610,18⟩
private theorem pass2485_2390 : (Triangular src2485) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2485_2391 : (Triangular src2485) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2485_2393 : (Triangular src2485) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2485_2399 : (Triangular src2485) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2485_2415 : (Triangular src2485) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2485_2459 : (Triangular src2485) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2485 : Cover (Triangular src2485) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2485_2390, by decide, by decide, pass2485_2391, by decide, by decide, pass2485_2393, by decide, by decide, pass2485_2399, by decide, by decide, pass2485_2415, by decide, by decide, pass2485_2459, rfl⟩
def src2486 : Request := ⟨⟨⟨1200,1674,361,14850⟩,51955677528064,215563369662⟩,4,3,1,385610,18⟩
private theorem pass2486_2390 : (Triangular src2486) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2486_2391 : (Triangular src2486) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2486_2393 : (Triangular src2486) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2486_2399 : (Triangular src2486) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2486_2415 : (Triangular src2486) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2486_2459 : (Triangular src2486) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2486 : Cover (Triangular src2486) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2486_2390, by decide, by decide, pass2486_2391, by decide, by decide, pass2486_2393, by decide, by decide, pass2486_2399, by decide, by decide, pass2486_2415, by decide, by decide, pass2486_2459, rfl⟩
def src2487 : Request := ⟨⟨⟨1750,2442,537,20773⟩,163381988556800,989573241440⟩,10,3,1,385610,18⟩
private theorem pass2487_2390 : (Triangular src2487) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2487_2391 : (Triangular src2487) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2487_2393 : (Triangular src2487) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2487_2398 : (Triangular src2487) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2487_2412 : (Triangular src2487) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2487_2449 : (Triangular src2487) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2487 : Cover (Triangular src2487) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2487_2390, by decide, by decide, pass2487_2391, by decide, by decide, pass2487_2393, by decide, by decide, pass2487_2398, by decide, by decide, pass2487_2412, by decide, by decide, pass2487_2449, rfl⟩
def src2488 : Request := ⟨⟨⟨3950,5512,1213,45041⟩,1877062482395136,25652240151764⟩,32,3,1,385610,18⟩
private theorem pass2488_2390 : (Triangular src2488) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2488_2391 : (Triangular src2488) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2488_2393 : (Triangular src2488) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2488_2398 : (Triangular src2488) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2488_2411 : (Triangular src2488) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2488_2445 : (Triangular src2488) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2488_2533 : (Triangular src2488) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2488 : Cover (Triangular src2488) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2488_2390, by decide, by decide, pass2488_2391, by decide, by decide, pass2488_2393, by decide, by decide, pass2488_2398, by decide, by decide, pass2488_2411, by decide, by decide, pass2488_2445, by decide, by decide, pass2488_2533, rfl⟩
def src2489 : Request := ⟨⟨⟨4800,6697,1474,71730⟩,3367547627110400,55891290082931⟩,65,3,1,385610,18⟩
private theorem pass2489_2390 : (Triangular src2489) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2489_2391 : (Triangular src2489) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2489_2393 : (Triangular src2489) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2489_2398 : (Triangular src2489) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2489_2411 : (Triangular src2489) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2489_2445 : (Triangular src2489) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2489_2533 : (Triangular src2489) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2489 : Cover (Triangular src2489) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2489_2390, by decide, by decide, pass2489_2391, by decide, by decide, pass2489_2393, by decide, by decide, pass2489_2398, by decide, by decide, pass2489_2411, by decide, by decide, pass2489_2445, by decide, by decide, pass2489_2533, rfl⟩
def src2490 : Request := ⟨⟨⟨8300,11581,2548,98175⟩,17399709518790656,499402661779949⟩,85,3,1,385610,18⟩
private theorem pass2490_2390 : (Triangular src2490) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2490_2391 : (Triangular src2490) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2490_2393 : (Triangular src2490) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2490_2398 : (Triangular src2490) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2490_2411 : (Triangular src2490) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2490_2444 : (Triangular src2490) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2490_2529 : (Triangular src2490) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2490 : Cover (Triangular src2490) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2490_2390, by decide, by decide, pass2490_2391, by decide, by decide, pass2490_2393, by decide, by decide, pass2490_2398, by decide, by decide, pass2490_2411, by decide, by decide, pass2490_2444, by decide, by decide, pass2490_2529, rfl⟩
def src2491 : Request := ⟨⟨⟨6900,9626,2077,120560⟩,9849424459857920,234809190715807⟩,110,3,1,385610,18⟩
private theorem pass2491_2390 : (Triangular src2491) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2491_2391 : (Triangular src2491) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2491_2393 : (Triangular src2491) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2491_2398 : (Triangular src2491) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2491_2411 : (Triangular src2491) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2491_2445 : (Triangular src2491) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2491_2533 : (Triangular src2491) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2491 : Cover (Triangular src2491) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2491_2390, by decide, by decide, pass2491_2391, by decide, by decide, pass2491_2393, by decide, by decide, pass2491_2398, by decide, by decide, pass2491_2411, by decide, by decide, pass2491_2445, by decide, by decide, pass2491_2533, rfl⟩
def src2492 : Request := ⟨⟨⟨825,1151,253,9473⟩,17161575202816,49010625289⟩,0,3,1,385610,19⟩
private theorem pass2492_2390 : (Triangular src2492) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2492_2391 : (Triangular src2492) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2492_2393 : (Triangular src2492) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2492_2399 : (Triangular src2492) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2492_2416 : (Triangular src2492) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2492_2463 : (Triangular src2492) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2492 : Cover (Triangular src2492) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2492_2390, by decide, by decide, pass2492_2391, by decide, by decide, pass2492_2393, by decide, by decide, pass2492_2399, by decide, by decide, pass2492_2416, by decide, by decide, pass2492_2463, rfl⟩
def src2493 : Request := ⟨⟨⟨1200,1674,368,12057⟩,52718727069696,218807905514⟩,1,3,1,385610,19⟩
private theorem pass2493_2390 : (Triangular src2493) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2493_2391 : (Triangular src2493) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2493_2393 : (Triangular src2493) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2493_2399 : (Triangular src2493) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2493_2415 : (Triangular src2493) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2493_2458 : (Triangular src2493) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2493 : Cover (Triangular src2493) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2493_2390, by decide, by decide, pass2493_2391, by decide, by decide, pass2493_2393, by decide, by decide, pass2493_2399, by decide, by decide, pass2493_2415, by decide, by decide, pass2493_2458, rfl⟩
def src2494 : Request := ⟨⟨⟨1200,1674,361,12882⟩,51955677528064,215563369662⟩,2,3,1,385610,19⟩
private theorem pass2494_2390 : (Triangular src2494) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2494_2391 : (Triangular src2494) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2494_2393 : (Triangular src2494) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2494_2399 : (Triangular src2494) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2494_2415 : (Triangular src2494) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2494_2459 : (Triangular src2494) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2494 : Cover (Triangular src2494) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2494_2390, by decide, by decide, pass2494_2391, by decide, by decide, pass2494_2393, by decide, by decide, pass2494_2399, by decide, by decide, pass2494_2415, by decide, by decide, pass2494_2459, rfl⟩
def src2495 : Request := ⟨⟨⟨1200,1674,361,13885⟩,51955677528064,215563369662⟩,4,3,1,385610,19⟩
private theorem pass2495_2390 : (Triangular src2495) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2495_2391 : (Triangular src2495) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2495_2393 : (Triangular src2495) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2495_2399 : (Triangular src2495) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2495_2415 : (Triangular src2495) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2495_2459 : (Triangular src2495) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2495 : Cover (Triangular src2495) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2495_2390, by decide, by decide, pass2495_2391, by decide, by decide, pass2495_2393, by decide, by decide, pass2495_2399, by decide, by decide, pass2495_2415, by decide, by decide, pass2495_2459, rfl⟩
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
  physicalFloor := 385610
  seedFloor := 17

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨3, 17, 10, 85/100, 80/100, ![863862671861, 173733566642, 20339274970, 2392877730], 1695631163252869⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 3 17 17 :=
  ⟨Lower6960.Prefix6969MainCases.Middle42.plan, Lower6960.Prefix6969MainCases.Middle42.price, Lower6960.Prefix6969MainCases.Middle42.valid, Lower6960.Prefix6969MainCases.Middle42.priced, Lower6960.Prefix6969MainCases.Middle42.sources,
   Lower6960.Prefix6969RescueData.Middle42.plan, Lower6960.Prefix6969RescueData.Middle42.price, Lower6960.Prefix6969RescueData.Middle42.sources, Lower6960.Prefix6969RescueData.Middle42.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved42
end Z6969Source1963

end Merged_Z6969Pack0742

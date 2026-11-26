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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 28 385610 := by
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

def price : Pricing := ⟨55/100, 90/100, [242988238, 313056431, 313739106, 313423910, 312550243, 311771873, 312234714, 146566664, 146522235, 146798929, 104439358, 74576199, 75486602, 75696785, 94633016, 118850801, 125228441, 219723444], [1507483, 1124751, 1121255, 1122869, 1127343, 1131329, 1128959, 2628820, 2629796, 2623723, 3775149, 5368232, 5303355, 5288824, 4186245, 3299211, 3120736, 1698970],
  ![116633598544080, 1623419045496, 197751099600, 6293700560], 129804173031223649⟩

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
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2592 : Request := ⟨⟨⟨825,1151,248,6399⟩,16903818182656,48256472894⟩,2,3,1,385610,28⟩
private theorem pass2592_2390 : (Triangular src2592) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2592_2391 : (Triangular src2592) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2592_2393 : (Triangular src2592) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2592_2399 : (Triangular src2592) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2592_2416 : (Triangular src2592) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2592_2464 : (Triangular src2592) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2592 : Cover (Triangular src2592) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2592_2390, by decide, by decide, pass2592_2391, by decide, by decide, pass2592_2393, by decide, by decide, pass2592_2399, by decide, by decide, pass2592_2416, by decide, by decide, pass2592_2464, rfl⟩
def src2593 : Request := ⟨⟨⟨825,1151,253,6387⟩,17161575202816,49010625289⟩,3,3,1,385610,28⟩
private theorem pass2593_2390 : (Triangular src2593) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2593_2391 : (Triangular src2593) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2593_2393 : (Triangular src2593) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2593_2399 : (Triangular src2593) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2593_2416 : (Triangular src2593) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2593_2463 : (Triangular src2593) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2593 : Cover (Triangular src2593) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2593_2390, by decide, by decide, pass2593_2391, by decide, by decide, pass2593_2393, by decide, by decide, pass2593_2399, by decide, by decide, pass2593_2416, by decide, by decide, pass2593_2463, rfl⟩
def src2594 : Request := ⟨⟨⟨825,1151,253,6640⟩,17161575202816,49010625289⟩,4,3,1,385610,28⟩
private theorem pass2594_2390 : (Triangular src2594) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2594_2391 : (Triangular src2594) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2594_2393 : (Triangular src2594) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2594_2399 : (Triangular src2594) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2594_2416 : (Triangular src2594) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2594_2463 : (Triangular src2594) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2594 : Cover (Triangular src2594) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2594_2390, by decide, by decide, pass2594_2391, by decide, by decide, pass2594_2393, by decide, by decide, pass2594_2399, by decide, by decide, pass2594_2416, by decide, by decide, pass2594_2463, rfl⟩
def src2595 : Request := ⟨⟨⟨1000,1395,307,7779⟩,30557599170560,105715278267⟩,6,3,1,385610,28⟩
private theorem pass2595_2390 : (Triangular src2595) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2595_2391 : (Triangular src2595) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2595_2393 : (Triangular src2595) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2595_2399 : (Triangular src2595) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2595_2415 : (Triangular src2595) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2595_2459 : (Triangular src2595) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2595 : Cover (Triangular src2595) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2595_2390, by decide, by decide, pass2595_2391, by decide, by decide, pass2595_2393, by decide, by decide, pass2595_2399, by decide, by decide, pass2595_2415, by decide, by decide, pass2595_2459, rfl⟩
def src2596 : Request := ⟨⟨⟨1200,1674,368,9067⟩,52718727069696,218807905514⟩,8,3,1,385610,28⟩
private theorem pass2596_2390 : (Triangular src2596) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2596_2391 : (Triangular src2596) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2596_2393 : (Triangular src2596) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2596_2399 : (Triangular src2596) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2596_2415 : (Triangular src2596) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2596_2458 : (Triangular src2596) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2596 : Cover (Triangular src2596) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2596_2390, by decide, by decide, pass2596_2391, by decide, by decide, pass2596_2393, by decide, by decide, pass2596_2399, by decide, by decide, pass2596_2415, by decide, by decide, pass2596_2458, rfl⟩
def src2597 : Request := ⟨⟨⟨1450,2023,445,11237⟩,92998964346880,466511127281⟩,13,3,1,385610,28⟩
private theorem pass2597_2390 : (Triangular src2597) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2597_2391 : (Triangular src2597) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2597_2393 : (Triangular src2597) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2597_2399 : (Triangular src2597) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2597_2415 : (Triangular src2597) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2597_2458 : (Triangular src2597) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2597 : Cover (Triangular src2597) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2597_2390, by decide, by decide, pass2597_2391, by decide, by decide, pass2597_2393, by decide, by decide, pass2597_2399, by decide, by decide, pass2597_2415, by decide, by decide, pass2597_2458, rfl⟩
def src2598 : Request := ⟨⟨⟨2600,3627,798,20294⟩,535425056505856,4812227595495⟩,32,3,1,385610,28⟩
private theorem pass2598_2390 : (Triangular src2598) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2598_2391 : (Triangular src2598) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2598_2393 : (Triangular src2598) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2598_2398 : (Triangular src2598) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2598_2411 : (Triangular src2598) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2598_2446 : (Triangular src2598) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2598 : Cover (Triangular src2598) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass2598_2390, by decide, by decide, pass2598_2391, by decide, by decide, pass2598_2393, by decide, by decide, pass2598_2398, by decide, by decide, pass2598_2411, by decide, by decide, pass2598_2446, rfl⟩
def src2599 : Request := ⟨⟨⟨8300,11579,2548,70582⟩,17399709518790656,499124969898998⟩,145,3,1,385610,28⟩
private theorem pass2599_2390 : (Triangular src2599) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2599_2391 : (Triangular src2599) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2599_2393 : (Triangular src2599) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2599_2398 : (Triangular src2599) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2599_2411 : (Triangular src2599) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2599_2445 : (Triangular src2599) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2599_2532 : (Triangular src2599) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2599 : Cover (Triangular src2599) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2599_2390, by decide, by decide, pass2599_2391, by decide, by decide, pass2599_2393, by decide, by decide, pass2599_2398, by decide, by decide, pass2599_2411, by decide, by decide, pass2599_2445, by decide, by decide, pass2599_2532, rfl⟩
def src2600 : Request := ⟨⟨⟨10000,13952,3070,76493⟩,30428373265940480,1051954539834997⟩,145,3,1,385610,28⟩
private theorem pass2600_2390 : (Triangular src2600) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2600_2391 : (Triangular src2600) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2600_2393 : (Triangular src2600) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2600_2398 : (Triangular src2600) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2600_2411 : (Triangular src2600) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2600_2445 : (Triangular src2600) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2600_2532 : (Triangular src2600) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2600 : Cover (Triangular src2600) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2600_2390, by decide, by decide, pass2600_2391, by decide, by decide, pass2600_2393, by decide, by decide, pass2600_2398, by decide, by decide, pass2600_2411, by decide, by decide, pass2600_2445, by decide, by decide, pass2600_2532, rfl⟩
def src2601 : Request := ⟨⟨⟨690,963,212,4963⟩,10065769922560,24078187611⟩,0,3,1,385610,29⟩
private theorem pass2601_2390 : (Triangular src2601) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2601_2391 : (Triangular src2601) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2601_2393 : (Triangular src2601) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2601_2399 : (Triangular src2601) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2601_2416 : (Triangular src2601) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2601_2464 : (Triangular src2601) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2601 : Cover (Triangular src2601) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2601_2390, by decide, by decide, pass2601_2391, by decide, by decide, pass2601_2393, by decide, by decide, pass2601_2399, by decide, by decide, pass2601_2416, by decide, by decide, pass2601_2464, rfl⟩
def src2602 : Request := ⟨⟨⟨690,963,212,5162⟩,10065769922560,24078187611⟩,1,3,1,385610,29⟩
private theorem pass2602_2390 : (Triangular src2602) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2602_2391 : (Triangular src2602) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2602_2393 : (Triangular src2602) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2602_2399 : (Triangular src2602) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2602_2416 : (Triangular src2602) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2602_2464 : (Triangular src2602) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2602 : Cover (Triangular src2602) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2602_2390, by decide, by decide, pass2602_2391, by decide, by decide, pass2602_2393, by decide, by decide, pass2602_2399, by decide, by decide, pass2602_2416, by decide, by decide, pass2602_2464, rfl⟩
def src2603 : Request := ⟨⟨⟨825,1151,253,5938⟩,17161575202816,49010625289⟩,2,3,1,385610,29⟩
private theorem pass2603_2390 : (Triangular src2603) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2603_2391 : (Triangular src2603) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2603_2393 : (Triangular src2603) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2603_2399 : (Triangular src2603) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2603_2416 : (Triangular src2603) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2603_2463 : (Triangular src2603) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2603 : Cover (Triangular src2603) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2603_2390, by decide, by decide, pass2603_2391, by decide, by decide, pass2603_2393, by decide, by decide, pass2603_2399, by decide, by decide, pass2603_2416, by decide, by decide, pass2603_2463, rfl⟩
def src2604 : Request := ⟨⟨⟨825,1151,253,6136⟩,17161575202816,49010625289⟩,3,3,1,385610,29⟩
private theorem pass2604_2390 : (Triangular src2604) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2604_2391 : (Triangular src2604) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2604_2393 : (Triangular src2604) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2604_2399 : (Triangular src2604) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2604_2416 : (Triangular src2604) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2604_2463 : (Triangular src2604) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2604 : Cover (Triangular src2604) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2604_2390, by decide, by decide, pass2604_2391, by decide, by decide, pass2604_2393, by decide, by decide, pass2604_2399, by decide, by decide, pass2604_2416, by decide, by decide, pass2604_2463, rfl⟩
def src2605 : Request := ⟨⟨⟨1000,1395,307,7470⟩,30557599170560,105715278267⟩,6,3,1,385610,29⟩
private theorem pass2605_2390 : (Triangular src2605) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2605_2391 : (Triangular src2605) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2605_2393 : (Triangular src2605) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2605_2399 : (Triangular src2605) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2605_2415 : (Triangular src2605) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2605_2459 : (Triangular src2605) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2605 : Cover (Triangular src2605) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2605_2390, by decide, by decide, pass2605_2391, by decide, by decide, pass2605_2393, by decide, by decide, pass2605_2399, by decide, by decide, pass2605_2415, by decide, by decide, pass2605_2459, rfl⟩
def src2606 : Request := ⟨⟨⟨1450,2023,445,11489⟩,92998964346880,466511127281⟩,16,3,1,385610,29⟩
private theorem pass2606_2390 : (Triangular src2606) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2606_2391 : (Triangular src2606) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2606_2393 : (Triangular src2606) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2606_2399 : (Triangular src2606) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2606_2415 : (Triangular src2606) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2606_2458 : (Triangular src2606) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2606 : Cover (Triangular src2606) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2606_2390, by decide, by decide, pass2606_2391, by decide, by decide, pass2606_2393, by decide, by decide, pass2606_2399, by decide, by decide, pass2606_2415, by decide, by decide, pass2606_2458, rfl⟩
def src2607 : Request := ⟨⟨⟨2600,3627,798,19484⟩,535425056505856,4812227595495⟩,32,3,1,385610,29⟩
private theorem pass2607_2390 : (Triangular src2607) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2607_2391 : (Triangular src2607) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2607_2393 : (Triangular src2607) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2607_2398 : (Triangular src2607) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2607_2412 : (Triangular src2607) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2607_2448 : (Triangular src2607) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2607 : Cover (Triangular src2607) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass2607_2390, by decide, by decide, pass2607_2391, by decide, by decide, pass2607_2393, by decide, by decide, pass2607_2398, by decide, by decide, pass2607_2412, by decide, by decide, pass2607_2448, rfl⟩
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
  physicalFloor := 385610
  seedFloor := 28

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨3, 28, 10, 75/100, 70/100, ![834694981692, 178366490235, 33499975080, 2392877730], 1104044989629058⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 29 385610 := by
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

def price : Pricing := ⟨55/100, 90/100, [242167248, 311290955, 311650254, 312339869, 311170535, 310377337, 311187118, 146561426, 146501767, 146524901, 146663812, 68065000, 68213549, 82117313, 90408929, 95297204, 118637596, 100000000, 219660794], [1514241, 1133792, 1131952, 1128421, 1134409, 1138471, 1134324, 2628935, 2630245, 2629737, 2626688, 5906305, 5892829, 4861529, 4399484, 4157647, 3305177, 3958949, 1699485],
  ![116600342671080, 1623486675196, 197694714600, 5235385960], 129005623030656602⟩

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
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 4885118/1369, 5616375/169, 278008360/2601] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle54
end Z6969Source2005

-- Source: Research6969.PhysicalChecks163
section Z6969Source2006
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2608 : Request := ⟨⟨⟨4800,6696,1474,40432⟩,3367547627110400,55864419956306⟩,85,3,1,385610,29⟩
private theorem pass2608_2390 : (Triangular src2608) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2608_2391 : (Triangular src2608) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2608_2393 : (Triangular src2608) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2608_2398 : (Triangular src2608) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2608_2411 : (Triangular src2608) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2608_2445 : (Triangular src2608) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2608_2533 : (Triangular src2608) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2608 : Cover (Triangular src2608) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2608_2390, by decide, by decide, pass2608_2391, by decide, by decide, pass2608_2393, by decide, by decide, pass2608_2398, by decide, by decide, pass2608_2411, by decide, by decide, pass2608_2445, by decide, by decide, pass2608_2533, rfl⟩
def src2609 : Request := ⟨⟨⟨5700,7952,1750,43331⟩,5637370734182400,111070724916873⟩,85,3,1,385610,29⟩
private theorem pass2609_2390 : (Triangular src2609) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2609_2391 : (Triangular src2609) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2609_2393 : (Triangular src2609) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2609_2398 : (Triangular src2609) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2609_2411 : (Triangular src2609) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2609_2445 : (Triangular src2609) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2609_2533 : (Triangular src2609) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2609 : Cover (Triangular src2609) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2609_2390, by decide, by decide, pass2609_2391, by decide, by decide, pass2609_2393, by decide, by decide, pass2609_2398, by decide, by decide, pass2609_2411, by decide, by decide, pass2609_2445, by decide, by decide, pass2609_2533, rfl⟩
def src2610 : Request := ⟨⟨⟨6900,9626,2118,53622⟩,9997036108906496,238415548481346⟩,110,3,1,385610,29⟩
private theorem pass2610_2390 : (Triangular src2610) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2610_2391 : (Triangular src2610) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2610_2393 : (Triangular src2610) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2610_2398 : (Triangular src2610) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2610_2411 : (Triangular src2610) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2610_2445 : (Triangular src2610) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2610_2533 : (Triangular src2610) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2610 : Cover (Triangular src2610) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2610_2390, by decide, by decide, pass2610_2391, by decide, by decide, pass2610_2393, by decide, by decide, pass2610_2398, by decide, by decide, pass2610_2411, by decide, by decide, pass2610_2445, by decide, by decide, pass2610_2533, rfl⟩
def src2611 : Request := ⟨⟨⟨10000,13952,3070,73566⟩,30428373265940480,1051954539834997⟩,145,3,1,385610,29⟩
private theorem pass2611_2390 : (Triangular src2611) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2611_2391 : (Triangular src2611) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2611_2393 : (Triangular src2611) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2611_2398 : (Triangular src2611) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2611_2411 : (Triangular src2611) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2611_2445 : (Triangular src2611) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2611_2532 : (Triangular src2611) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2611 : Cover (Triangular src2611) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2611_2390, by decide, by decide, pass2611_2391, by decide, by decide, pass2611_2393, by decide, by decide, pass2611_2398, by decide, by decide, pass2611_2411, by decide, by decide, pass2611_2445, by decide, by decide, pass2611_2532, rfl⟩
def src2612 : Request := ⟨⟨⟨560,781,169,4378⟩,5316921262080,10299257375⟩,0,3,1,385610,30⟩
private theorem pass2612_2390 : (Triangular src2612) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2612_2391 : (Triangular src2612) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2612_2393 : (Triangular src2612) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2612_2399 : (Triangular src2612) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2612_2417 : (Triangular src2612) 2417 2469 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2612_2470 : (Triangular src2612) 2470 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2612 : Cover (Triangular src2612) 2534 2390 [2390,2392,2398,2416,2469,2534] := by
  exact ⟨by decide, by decide, pass2612_2390, by decide, by decide, pass2612_2391, by decide, by decide, pass2612_2393, by decide, by decide, pass2612_2399, by decide, by decide, pass2612_2417, by decide, by decide, pass2612_2470, rfl⟩
def src2613 : Request := ⟨⟨⟨690,963,208,5140⟩,9921631092736,23724874690⟩,1,3,1,385610,30⟩
private theorem pass2613_2390 : (Triangular src2613) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2613_2391 : (Triangular src2613) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2613_2393 : (Triangular src2613) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2613_2399 : (Triangular src2613) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2613_2416 : (Triangular src2613) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2613_2465 : (Triangular src2613) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2613 : Cover (Triangular src2613) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2613_2390, by decide, by decide, pass2613_2391, by decide, by decide, pass2613_2393, by decide, by decide, pass2613_2399, by decide, by decide, pass2613_2416, by decide, by decide, pass2613_2465, rfl⟩
def src2614 : Request := ⟨⟨⟨690,962,208,5322⟩,9921631092736,23645774460⟩,2,3,1,385610,30⟩
private theorem pass2614_2390 : (Triangular src2614) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2614_2391 : (Triangular src2614) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2614_2393 : (Triangular src2614) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2614_2399 : (Triangular src2614) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2614_2416 : (Triangular src2614) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2614_2465 : (Triangular src2614) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2614 : Cover (Triangular src2614) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2614_2390, by decide, by decide, pass2614_2391, by decide, by decide, pass2614_2393, by decide, by decide, pass2614_2399, by decide, by decide, pass2614_2416, by decide, by decide, pass2614_2465, rfl⟩
def src2615 : Request := ⟨⟨⟨825,1151,253,6119⟩,17161575202816,49010625289⟩,4,3,1,385610,30⟩
private theorem pass2615_2390 : (Triangular src2615) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2615_2391 : (Triangular src2615) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2615_2393 : (Triangular src2615) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2615_2399 : (Triangular src2615) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2615_2416 : (Triangular src2615) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2615_2463 : (Triangular src2615) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2615 : Cover (Triangular src2615) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2615_2390, by decide, by decide, pass2615_2391, by decide, by decide, pass2615_2393, by decide, by decide, pass2615_2399, by decide, by decide, pass2615_2416, by decide, by decide, pass2615_2463, rfl⟩
def src2616 : Request := ⟨⟨⟨1000,1395,315,7111⟩,31157463285760,107844841957⟩,6,3,1,385610,30⟩
private theorem pass2616_2390 : (Triangular src2616) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2616_2391 : (Triangular src2616) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2616_2393 : (Triangular src2616) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2616_2399 : (Triangular src2616) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2616_2415 : (Triangular src2616) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2616_2459 : (Triangular src2616) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2616 : Cover (Triangular src2616) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2616_2390, by decide, by decide, pass2616_2391, by decide, by decide, pass2616_2393, by decide, by decide, pass2616_2399, by decide, by decide, pass2616_2415, by decide, by decide, pass2616_2459, rfl⟩
def src2617 : Request := ⟨⟨⟨1200,1674,378,8676⟩,53798525730816,223406703910⟩,10,3,1,385610,30⟩
private theorem pass2617_2390 : (Triangular src2617) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2617_2391 : (Triangular src2617) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2617_2393 : (Triangular src2617) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2617_2399 : (Triangular src2617) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2617_2415 : (Triangular src2617) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2617_2458 : (Triangular src2617) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2617 : Cover (Triangular src2617) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2617_2390, by decide, by decide, pass2617_2391, by decide, by decide, pass2617_2393, by decide, by decide, pass2617_2399, by decide, by decide, pass2617_2415, by decide, by decide, pass2617_2458, rfl⟩
def src2618 : Request := ⟨⟨⟨2100,2930,645,15397⟩,282396798484480,2051392203643⟩,25,3,1,385610,30⟩
private theorem pass2618_2390 : (Triangular src2618) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2618_2391 : (Triangular src2618) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2618_2393 : (Triangular src2618) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2618_2398 : (Triangular src2618) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2618_2412 : (Triangular src2618) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2618_2449 : (Triangular src2618) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2618 : Cover (Triangular src2618) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2618_2390, by decide, by decide, pass2618_2391, by decide, by decide, pass2618_2393, by decide, by decide, pass2618_2398, by decide, by decide, pass2618_2412, by decide, by decide, pass2618_2449, rfl⟩
def src2619 : Request := ⟨⟨⟨3950,5510,1213,30936⟩,1877062482395136,25622281045803⟩,65,3,1,385610,30⟩
private theorem pass2619_2390 : (Triangular src2619) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2619_2391 : (Triangular src2619) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2619_2393 : (Triangular src2619) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2619_2398 : (Triangular src2619) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2619_2411 : (Triangular src2619) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2619_2445 : (Triangular src2619) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2619_2534 : (Triangular src2619) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2619 : Cover (Triangular src2619) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2619_2390, by decide, by decide, pass2619_2391, by decide, by decide, pass2619_2393, by decide, by decide, pass2619_2398, by decide, by decide, pass2619_2411, by decide, by decide, pass2619_2445, by decide, by decide, pass2619_2534, rfl⟩
def src2620 : Request := ⟨⟨⟨5700,7952,1796,41078⟩,5749327563587584,113334118485107⟩,85,3,1,385610,30⟩
private theorem pass2620_2390 : (Triangular src2620) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2620_2391 : (Triangular src2620) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2620_2393 : (Triangular src2620) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2620_2398 : (Triangular src2620) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2620_2411 : (Triangular src2620) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2620_2445 : (Triangular src2620) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2620_2533 : (Triangular src2620) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2620 : Cover (Triangular src2620) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2620_2390, by decide, by decide, pass2620_2391, by decide, by decide, pass2620_2393, by decide, by decide, pass2620_2398, by decide, by decide, pass2620_2411, by decide, by decide, pass2620_2445, by decide, by decide, pass2620_2533, rfl⟩
def src2621 : Request := ⟨⟨⟨8300,11579,2548,64421⟩,17399709518790656,499124969898998⟩,145,3,1,385610,30⟩
private theorem pass2621_2390 : (Triangular src2621) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2621_2391 : (Triangular src2621) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2621_2393 : (Triangular src2621) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2621_2398 : (Triangular src2621) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2621_2411 : (Triangular src2621) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2621_2445 : (Triangular src2621) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2621_2532 : (Triangular src2621) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2621 : Cover (Triangular src2621) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2621_2390, by decide, by decide, pass2621_2391, by decide, by decide, pass2621_2393, by decide, by decide, pass2621_2398, by decide, by decide, pass2621_2411, by decide, by decide, pass2621_2445, by decide, by decide, pass2621_2532, rfl⟩
def src2622 : Request := ⟨⟨⟨10000,13950,3070,80985⟩,30428373265940480,1051468979452278⟩,190,3,1,385610,30⟩
private theorem pass2622_2390 : (Triangular src2622) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2622_2391 : (Triangular src2622) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2622_2393 : (Triangular src2622) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2622_2398 : (Triangular src2622) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2622_2411 : (Triangular src2622) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2622_2445 : (Triangular src2622) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2622_2532 : (Triangular src2622) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2622 : Cover (Triangular src2622) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2622_2390, by decide, by decide, pass2622_2391, by decide, by decide, pass2622_2393, by decide, by decide, pass2622_2398, by decide, by decide, pass2622_2411, by decide, by decide, pass2622_2445, by decide, by decide, pass2622_2532, rfl⟩
def src2623 : Request := ⟨⟨⟨560,781,172,4098⟩,5388141854720,10440670587⟩,0,3,1,385610,31⟩
private theorem pass2623_2390 : (Triangular src2623) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2623_2391 : (Triangular src2623) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2623_2394 : (Triangular src2623) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2623_2402 : (Triangular src2623) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2623_2426 : (Triangular src2623) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2623_2496 : (Triangular src2623) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2623 : Cover (Triangular src2623) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2623_2390, by decide, by decide, pass2623_2391, by decide, by decide, pass2623_2394, by decide, by decide, pass2623_2402, by decide, by decide, pass2623_2426, by decide, by decide, pass2623_2496, rfl⟩
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
  physicalFloor := 385610
  seedFloor := 29

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨3, 29, 10, 70/100, 70/100, ![831425276160, 180325961794, 34696403200, 2392877730], 1043057215519251⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 30 385610 := by
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

def price : Pricing := ⟨55/100, 90/100, [241480611, 311746435, 310587576, 310690565, 310643824, 311272026, 309873456, 146715841, 146704182, 146247937, 103671694, 94406371, 55000000, 64778784, 87140696, 93422871, 130408446, 229460952], [1519892, 1131460, 1137395, 1136867, 1137107, 1133889, 1141052, 2625546, 2625802, 2635816, 3803816, 4197686, 7352332, 6213724, 4564470, 4247335, 2983471, 1618823],
  ![121802462540640, 1612853391228, 206514856800, 6337998480], 130864819425485479⟩

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
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 20 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 385610
  seedFloor := 30

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨3, 30, 10, 70/100, 70/100, ![946834102875, 190326115415, 35892828250, 2392877730], 961019047223712⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 3 30 30 :=
  ⟨Lower6960.Prefix6969MainCases.Middle55.plan, Lower6960.Prefix6969MainCases.Middle55.price, Lower6960.Prefix6969MainCases.Middle55.valid, Lower6960.Prefix6969MainCases.Middle55.priced, Lower6960.Prefix6969MainCases.Middle55.sources,
   Lower6960.Prefix6969RescueData.Middle55.plan, Lower6960.Prefix6969RescueData.Middle55.price, Lower6960.Prefix6969RescueData.Middle55.sources, Lower6960.Prefix6969RescueData.Middle55.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved55
end Z6969Source2011

end Merged_Z6969Pack0746

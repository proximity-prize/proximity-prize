import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0744
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0746
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice
import ProximityPrize.SubmissionLower.Z6969Pack0738
import ProximityPrize.SubmissionLower.Z6969Pack0739
import ProximityPrize.SubmissionLower.Z6969Pack0740
import ProximityPrize.SubmissionLower.Z6969Pack0741
import ProximityPrize.SubmissionLower.Z6969Pack0742
import ProximityPrize.SubmissionLower.Z6969Pack0743
import ProximityPrize.SubmissionLower.Z6969Pack0745

set_option Elab.async false

-- merged module Z6969Pack0747
section Merged_Z6969Pack0747

-- Source: Research6969.PrefixMainDataMiddle56
section Z6969Source2012
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle56
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 20, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank31 1491, bank37 1587, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank115 2949, bank168 3916, bank130 10521, bank161 5142, bank212 8810, bank186 19684, bank175 25973, bank169 29097] i
  head := src2953
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15525, 123858, 573461, 1979012],
    ![25417/2, 364169/4, 413413, 1399489],
    ![54680/9, 396430/9, 413413, 1399489],
    ![29433/8, 428181/16, 646282/3, 687492],
    ![64334/25, 460599/25, 158046, 2223081/4],
    ![17323/9, 164849/12, 2225553/16, 6993909/16],
    ![18775/16, 556545/64, 503037/5, 8144136/25],
    ![89110/121, 651785/121, 422098/7, 1352949/7],
    ![89110/121, 651785/121, 116003/2, 1352949/7],
    ![63754/121, 4778, 770661/16, 191844],
    ![63754/121, 224030/49, 751995/16, 8696601/64],
    ![63754/121, 224030/49, 751995/16, 126736],
    ![33463/82, 224030/49, 751995/16, 126736],
    ![33463/82, 6616716/1681, 7437933/196, 2937796/25],
    ![33463/82, 19337563/5476, 5616375/169, 77616100/729],
    ![481425/1369, 19337563/5476, 5616375/169, 77616100/729],
    ![929061/2738, 19337563/5476, 5616375/169, 77616100/729],
    ![459151/1369, 19337563/5476, 5616375/169, 77616100/729]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 31 385610 := by
  refine ⟨?_, rank154 4407, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2953⟩⟩
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
    · exact free130_1
    · exact free161_1
    · exact free212_1
    · exact free186_1
    · exact free175_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [240469561, 310156179, 310344758, 309746105, 309388479, 309969212, 308245210, 133093846, 133435236, 133260852, 103399239, 55340171, 55000000, 74334961, 92600980, 110386955, 128473971, 229029350], [1528214, 1139604, 1138638, 1141704, 1143536, 1140561, 1149391, 2924530, 2917037, 2920864, 3815327, 7303801, 7352332, 5387426, 4288825, 3568459, 3029912, 1622375],
  ![121573359567000, 1613321482900, 206126415000, 6411036940], 131004441233970686⟩

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
    · exact Pricing.height_from_critical Band.middle _ 20 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 20 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 19337563/5476, 5616375/169, 77616100/729] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle56
end Z6969Source2012

-- Source: Research6969.PhysicalChecks164
section Z6969Source2013
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2624 : Request := ⟨⟨⟨690,963,208,4972⟩,9921631092736,23724874690⟩,1,3,1,385610,31⟩
private theorem pass2624_2390 : (Triangular src2624) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2624_2391 : (Triangular src2624) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2624_2393 : (Triangular src2624) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2624_2399 : (Triangular src2624) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2624_2416 : (Triangular src2624) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2624_2465 : (Triangular src2624) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2624 : Cover (Triangular src2624) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2624_2390, by decide, by decide, pass2624_2391, by decide, by decide, pass2624_2393, by decide, by decide, pass2624_2399, by decide, by decide, pass2624_2416, by decide, by decide, pass2624_2465, rfl⟩
def src2625 : Request := ⟨⟨⟨690,962,208,5133⟩,9921631092736,23645774460⟩,2,3,1,385610,31⟩
private theorem pass2625_2390 : (Triangular src2625) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2625_2391 : (Triangular src2625) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2625_2393 : (Triangular src2625) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2625_2399 : (Triangular src2625) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2625_2416 : (Triangular src2625) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2625_2465 : (Triangular src2625) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2625 : Cover (Triangular src2625) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2625_2390, by decide, by decide, pass2625_2391, by decide, by decide, pass2625_2393, by decide, by decide, pass2625_2399, by decide, by decide, pass2625_2416, by decide, by decide, pass2625_2465, rfl⟩
def src2626 : Request := ⟨⟨⟨690,962,212,5173⟩,10065769922560,23997864317⟩,3,3,1,385610,31⟩
private theorem pass2626_2390 : (Triangular src2626) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2626_2391 : (Triangular src2626) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2626_2393 : (Triangular src2626) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2626_2399 : (Triangular src2626) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2626_2416 : (Triangular src2626) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2626_2464 : (Triangular src2626) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2626 : Cover (Triangular src2626) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2626_2390, by decide, by decide, pass2626_2391, by decide, by decide, pass2626_2393, by decide, by decide, pass2626_2399, by decide, by decide, pass2626_2416, by decide, by decide, pass2626_2464, rfl⟩
def src2627 : Request := ⟨⟨⟨825,1151,253,6326⟩,17161575202816,49010625289⟩,6,3,1,385610,31⟩
private theorem pass2627_2390 : (Triangular src2627) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2627_2391 : (Triangular src2627) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2627_2393 : (Triangular src2627) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2627_2399 : (Triangular src2627) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2627_2416 : (Triangular src2627) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2627_2463 : (Triangular src2627) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2627 : Cover (Triangular src2627) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2627_2390, by decide, by decide, pass2627_2391, by decide, by decide, pass2627_2393, by decide, by decide, pass2627_2399, by decide, by decide, pass2627_2416, by decide, by decide, pass2627_2463, rfl⟩
def src2628 : Request := ⟨⟨⟨1000,1395,307,7351⟩,30557599170560,105715278267⟩,8,3,1,385610,31⟩
private theorem pass2628_2390 : (Triangular src2628) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2628_2391 : (Triangular src2628) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2628_2393 : (Triangular src2628) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2628_2399 : (Triangular src2628) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2628_2415 : (Triangular src2628) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2628_2459 : (Triangular src2628) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2628 : Cover (Triangular src2628) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2628_2390, by decide, by decide, pass2628_2391, by decide, by decide, pass2628_2393, by decide, by decide, pass2628_2399, by decide, by decide, pass2628_2415, by decide, by decide, pass2628_2459, rfl⟩
def src2629 : Request := ⟨⟨⟨1450,2023,445,10645⟩,92998964346880,466511127281⟩,16,3,1,385610,31⟩
private theorem pass2629_2390 : (Triangular src2629) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2629_2391 : (Triangular src2629) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2629_2393 : (Triangular src2629) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2629_2399 : (Triangular src2629) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2629_2415 : (Triangular src2629) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2629_2458 : (Triangular src2629) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2629 : Cover (Triangular src2629) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2629_2390, by decide, by decide, pass2629_2391, by decide, by decide, pass2629_2393, by decide, by decide, pass2629_2399, by decide, by decide, pass2629_2415, by decide, by decide, pass2629_2458, rfl⟩
def src2630 : Request := ⟨⟨⟨2100,2929,645,16307⟩,282396798484480,2049139102608⟩,32,3,1,385610,31⟩
private theorem pass2630_2390 : (Triangular src2630) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2630_2391 : (Triangular src2630) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2630_2393 : (Triangular src2630) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2630_2398 : (Triangular src2630) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2630_2412 : (Triangular src2630) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2630_2449 : (Triangular src2630) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2630 : Cover (Triangular src2630) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2630_2390, by decide, by decide, pass2630_2391, by decide, by decide, pass2630_2393, by decide, by decide, pass2630_2398, by decide, by decide, pass2630_2412, by decide, by decide, pass2630_2449, rfl⟩
def src2631 : Request := ⟨⟨⟨3950,5510,1213,29777⟩,1877062482395136,25622281045803⟩,65,3,1,385610,31⟩
private theorem pass2631_2390 : (Triangular src2631) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2631_2391 : (Triangular src2631) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2631_2393 : (Triangular src2631) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2631_2398 : (Triangular src2631) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2631_2411 : (Triangular src2631) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2631_2445 : (Triangular src2631) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2631_2534 : (Triangular src2631) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2631 : Cover (Triangular src2631) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2631_2390, by decide, by decide, pass2631_2391, by decide, by decide, pass2631_2393, by decide, by decide, pass2631_2398, by decide, by decide, pass2631_2411, by decide, by decide, pass2631_2445, by decide, by decide, pass2631_2534, rfl⟩
def src2632 : Request := ⟨⟨⟨5700,7951,1750,45806⟩,5637370734182400,111025751789870⟩,110,3,1,385610,31⟩
private theorem pass2632_2390 : (Triangular src2632) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2632_2391 : (Triangular src2632) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2632_2393 : (Triangular src2632) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2632_2398 : (Triangular src2632) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2632_2411 : (Triangular src2632) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2632_2445 : (Triangular src2632) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2632_2533 : (Triangular src2632) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2632 : Cover (Triangular src2632) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2632_2390, by decide, by decide, pass2632_2391, by decide, by decide, pass2632_2393, by decide, by decide, pass2632_2398, by decide, by decide, pass2632_2411, by decide, by decide, pass2632_2445, by decide, by decide, pass2632_2533, rfl⟩
def src2633 : Request := ⟨⟨⟨8300,11579,2548,62058⟩,17399709518790656,499124969898998⟩,145,3,1,385610,31⟩
private theorem pass2633_2390 : (Triangular src2633) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2633_2391 : (Triangular src2633) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2633_2393 : (Triangular src2633) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2633_2398 : (Triangular src2633) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2633_2411 : (Triangular src2633) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2633_2445 : (Triangular src2633) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2633_2532 : (Triangular src2633) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2633 : Cover (Triangular src2633) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2633_2390, by decide, by decide, pass2633_2391, by decide, by decide, pass2633_2393, by decide, by decide, pass2633_2398, by decide, by decide, pass2633_2411, by decide, by decide, pass2633_2445, by decide, by decide, pass2633_2532, rfl⟩
def src2634 : Request := ⟨⟨⟨560,781,176,3926⟩,5482316038144,10627925923⟩,0,3,1,385610,32⟩
private theorem pass2634_2390 : (Triangular src2634) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2634_2391 : (Triangular src2634) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2634_2394 : (Triangular src2634) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2634_2402 : (Triangular src2634) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2634_2426 : (Triangular src2634) 2426 2494 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2634_2495 : (Triangular src2634) 2495 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2634 : Cover (Triangular src2634) 2534 2390 [2390,2393,2401,2425,2494,2534] := by
  exact ⟨by decide, by decide, pass2634_2390, by decide, by decide, pass2634_2391, by decide, by decide, pass2634_2394, by decide, by decide, pass2634_2402, by decide, by decide, pass2634_2426, by decide, by decide, pass2634_2495, rfl⟩
def src2635 : Request := ⟨⟨⟨690,963,212,4691⟩,10065769922560,24078187611⟩,1,3,1,385610,32⟩
private theorem pass2635_2390 : (Triangular src2635) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2635_2391 : (Triangular src2635) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2635_2393 : (Triangular src2635) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2635_2399 : (Triangular src2635) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2635_2416 : (Triangular src2635) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2635_2464 : (Triangular src2635) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2635 : Cover (Triangular src2635) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2635_2390, by decide, by decide, pass2635_2391, by decide, by decide, pass2635_2393, by decide, by decide, pass2635_2399, by decide, by decide, pass2635_2416, by decide, by decide, pass2635_2464, rfl⟩
def src2636 : Request := ⟨⟨⟨690,962,208,4971⟩,9921631092736,23645774460⟩,2,3,1,385610,32⟩
private theorem pass2636_2390 : (Triangular src2636) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2636_2391 : (Triangular src2636) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2636_2393 : (Triangular src2636) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2636_2399 : (Triangular src2636) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2636_2416 : (Triangular src2636) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2636_2465 : (Triangular src2636) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2636 : Cover (Triangular src2636) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2636_2390, by decide, by decide, pass2636_2391, by decide, by decide, pass2636_2393, by decide, by decide, pass2636_2399, by decide, by decide, pass2636_2416, by decide, by decide, pass2636_2465, rfl⟩
def src2637 : Request := ⟨⟨⟨690,962,212,5206⟩,10065769922560,23997864317⟩,4,3,1,385610,32⟩
private theorem pass2637_2390 : (Triangular src2637) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2637_2391 : (Triangular src2637) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2637_2393 : (Triangular src2637) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2637_2399 : (Triangular src2637) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2637_2416 : (Triangular src2637) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2637_2464 : (Triangular src2637) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2637 : Cover (Triangular src2637) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2637_2390, by decide, by decide, pass2637_2391, by decide, by decide, pass2637_2393, by decide, by decide, pass2637_2399, by decide, by decide, pass2637_2416, by decide, by decide, pass2637_2464, rfl⟩
def src2638 : Request := ⟨⟨⟨825,1151,253,6109⟩,17161575202816,49010625289⟩,6,3,1,385610,32⟩
private theorem pass2638_2390 : (Triangular src2638) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2638_2391 : (Triangular src2638) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2638_2393 : (Triangular src2638) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2638_2399 : (Triangular src2638) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2638_2416 : (Triangular src2638) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2638_2463 : (Triangular src2638) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2638 : Cover (Triangular src2638) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2638_2390, by decide, by decide, pass2638_2391, by decide, by decide, pass2638_2393, by decide, by decide, pass2638_2399, by decide, by decide, pass2638_2416, by decide, by decide, pass2638_2463, rfl⟩
def src2639 : Request := ⟨⟨⟨1000,1395,307,7512⟩,30557599170560,105715278267⟩,10,3,1,385610,32⟩
private theorem pass2639_2390 : (Triangular src2639) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2639_2391 : (Triangular src2639) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2639_2393 : (Triangular src2639) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2639_2399 : (Triangular src2639) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2639_2415 : (Triangular src2639) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2639_2459 : (Triangular src2639) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2639 : Cover (Triangular src2639) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2639_2390, by decide, by decide, pass2639_2391, by decide, by decide, pass2639_2393, by decide, by decide, pass2639_2399, by decide, by decide, pass2639_2415, by decide, by decide, pass2639_2459, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2013

-- Source: Research6969.PrefixRescueDataMiddle56
section Z6969Source2014
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle56
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,31⟩
  bank i := ![bank156 4098, bank195 4972, bank192 5133, bank193 5173, bank204 6326, bank222 7351, bank237 10645, bank249 16307, bank310 29777, bank368 62058, bank340 45806] i
  reserve i := ![0, 1, 2, 3, 6, 8, 16, 32, 65, 145, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385610
  seedFloor := 31

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank156 4098
    · exact rank195 4972
    · exact rank192 5133
    · exact rank193 5173
    · exact rank204 6326
    · exact rank222 7351
    · exact rank237 10645
    · exact rank249 16307
    · exact rank310 29777
    · exact rank368 62058
    · exact rank340 45806
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2623⟩
    · exact ⟨_, cover2624⟩
    · exact ⟨_, cover2625⟩
    · exact ⟨_, cover2626⟩
    · exact ⟨_, cover2627⟩
    · exact ⟨_, cover2628⟩
    · exact ⟨_, cover2629⟩
    · exact ⟨_, cover2630⟩
    · exact ⟨_, cover2631⟩
    · exact ⟨_, cover2633⟩
    · exact ⟨_, cover2632⟩

def price : EarlyPrice := ⟨3, 31, 10, 70/100, 70/100, ![749734551078, 157475661383, 30782874668, 1986010572], 837387550735052⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![3817/37, 33352/37, 383899/111, 38378/3] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle56
end Z6969Source2014

-- Source: Research6969.PrefixMiddleSaved56
section Z6969Source2015
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved56
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle56.price Lower6960.Prefix6969RescueData.Middle56.price :=
  ⟨335, 3531, 103, 901, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle56.plan Lower6960.Prefix6969RescueData.Middle56.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 3 31 31 :=
  ⟨Lower6960.Prefix6969MainCases.Middle56.plan, Lower6960.Prefix6969MainCases.Middle56.price, Lower6960.Prefix6969MainCases.Middle56.valid, Lower6960.Prefix6969MainCases.Middle56.priced, Lower6960.Prefix6969MainCases.Middle56.sources,
   Lower6960.Prefix6969RescueData.Middle56.plan, Lower6960.Prefix6969RescueData.Middle56.price, Lower6960.Prefix6969RescueData.Middle56.sources, Lower6960.Prefix6969RescueData.Middle56.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved56
end Z6969Source2015

-- Source: Research6969.PrefixMainDataMiddle57
section Z6969Source2016
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle57
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 20, 18, 21, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank58 2054, bank77 3883, bank82 2422, bank75 3842, bank104 2782, bank137 3019, bank144 3940, bank129 10859, bank161 5142, bank212 8810, bank183 20877, bank174 26788, bank169 29097] i
  head := src2954
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15088, 123475, 572406, 2048522],
    ![25417/2, 90589, 411355, 1399489],
    ![54680/9, 43830, 411355, 1399489],
    ![29433/8, 213037/8, 1929340/9, 679848],
    ![16211/9, 122734/9, 1118123/8, 3667257/8],
    ![24292/27, 199108/27, 452323/6, 4644025/16],
    ![73478/121, 721872/121, 3259742/49, 4644025/16],
    ![73478/121, 721872/121, 3259742/49, 2102735/9],
    ![73478/121, 654240/121, 2945384/49, 8951332/49],
    ![78398/147, 234838/49, 2331216/49, 8951332/49],
    ![78398/147, 234838/49, 2331216/49, 8951332/49],
    ![3719/7, 100178/21, 2304495/49, 8951332/49],
    ![3719/7, 100178/21, 2304495/49, 7739524/49],
    ![3719/7, 547603/121, 2304495/49, 6578401/49],
    ![3719/7, 219857/50, 5240200/121, 15523600/121],
    ![33263/82, 219857/50, 5240200/121, 15523600/121],
    ![33263/82, 6582024/1681, 3699685/98, 2937796/25],
    ![33263/82, 9619561/2738, 5616375/169, 77616100/729],
    ![954471/2738, 9619561/2738, 5616375/169, 77616100/729],
    ![462882/1369, 9619561/2738, 5616375/169, 77616100/729],
    ![459151/1369, 9619561/2738, 5616375/169, 77616100/729]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 32 385610 := by
  refine ⟨?_, rank154 4358, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2954⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free32_1
    · exact free41_1
    · exact free42_6
    · exact free48_1
    · exact free58_1
    · exact free77_1
    · exact free82_1
    · exact free75_1
    · exact free104_1
    · exact free137_1
    · exact free144_1
    · exact free129_1
    · exact free161_1
    · exact free212_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [237394474, 307788017, 308007106, 308049519, 308217248, 307803044, 311505554, 311291929, 155763541, 156718848, 156417023, 156572094, 156999023, 105414303, 71746476, 77178426, 91326416, 91934712, 118615190, 100000000, 219480072], [1553524, 1151732, 1150610, 1150393, 1149534, 1151655, 1132693, 1133787, 2473736, 2457836, 2462860, 2460278, 2453172, 3741268, 5593375, 5186386, 4353168, 4322460, 3305804, 3958949, 1700973],
  ![116504411819040, 1623683044308, 197532064800, 5180269920], 127665648834639985⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 9619561/2738, 5616375/169, 77616100/729] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle57
end Z6969Source2016

-- Source: Research6969.PhysicalChecks165
section Z6969Source2017
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2640 : Request := ⟨⟨⟨1750,2441,537,13133⟩,163381988556800,988269431527⟩,25,3,1,385610,32⟩
private theorem pass2640_2390 : (Triangular src2640) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2640_2391 : (Triangular src2640) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2640_2393 : (Triangular src2640) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2640_2398 : (Triangular src2640) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2640_2412 : (Triangular src2640) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2640_2449 : (Triangular src2640) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2640 : Cover (Triangular src2640) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2640_2390, by decide, by decide, pass2640_2391, by decide, by decide, pass2640_2393, by decide, by decide, pass2640_2398, by decide, by decide, pass2640_2412, by decide, by decide, pass2640_2449, rfl⟩
def src2641 : Request := ⟨⟨⟨3950,5510,1213,28792⟩,1877062482395136,25622281045803⟩,65,3,1,385610,32⟩
private theorem pass2641_2390 : (Triangular src2641) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2641_2391 : (Triangular src2641) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2641_2393 : (Triangular src2641) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2641_2398 : (Triangular src2641) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2641_2411 : (Triangular src2641) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2641_2445 : (Triangular src2641) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2641_2534 : (Triangular src2641) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2641 : Cover (Triangular src2641) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2641_2390, by decide, by decide, pass2641_2391, by decide, by decide, pass2641_2393, by decide, by decide, pass2641_2398, by decide, by decide, pass2641_2411, by decide, by decide, pass2641_2445, by decide, by decide, pass2641_2534, rfl⟩
def src2642 : Request := ⟨⟨⟨4800,6696,1512,35169⟩,3433136573644800,56980856955989⟩,85,3,1,385610,32⟩
private theorem pass2642_2390 : (Triangular src2642) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2642_2391 : (Triangular src2642) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2642_2393 : (Triangular src2642) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2642_2398 : (Triangular src2642) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2642_2411 : (Triangular src2642) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2642_2445 : (Triangular src2642) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2642_2533 : (Triangular src2642) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2642 : Cover (Triangular src2642) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2642_2390, by decide, by decide, pass2642_2391, by decide, by decide, pass2642_2393, by decide, by decide, pass2642_2398, by decide, by decide, pass2642_2411, by decide, by decide, pass2642_2445, by decide, by decide, pass2642_2533, rfl⟩
def src2643 : Request := ⟨⟨⟨5700,7951,1750,44053⟩,5637370734182400,111025751789870⟩,110,3,1,385610,32⟩
private theorem pass2643_2390 : (Triangular src2643) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2643_2391 : (Triangular src2643) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2643_2393 : (Triangular src2643) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2643_2398 : (Triangular src2643) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2643_2411 : (Triangular src2643) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2643_2445 : (Triangular src2643) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2643_2533 : (Triangular src2643) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2643 : Cover (Triangular src2643) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2643_2390, by decide, by decide, pass2643_2391, by decide, by decide, pass2643_2393, by decide, by decide, pass2643_2398, by decide, by decide, pass2643_2411, by decide, by decide, pass2643_2445, by decide, by decide, pass2643_2533, rfl⟩
def src2644 : Request := ⟨⟨⟨8300,11579,2548,60047⟩,17399709518790656,499124969898998⟩,145,3,1,385610,32⟩
private theorem pass2644_2390 : (Triangular src2644) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2644_2391 : (Triangular src2644) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2644_2393 : (Triangular src2644) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2644_2398 : (Triangular src2644) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2644_2411 : (Triangular src2644) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2644_2445 : (Triangular src2644) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2644_2532 : (Triangular src2644) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2644 : Cover (Triangular src2644) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2644_2390, by decide, by decide, pass2644_2391, by decide, by decide, pass2644_2393, by decide, by decide, pass2644_2398, by decide, by decide, pass2644_2411, by decide, by decide, pass2644_2445, by decide, by decide, pass2644_2532, rfl⟩
def src2645 : Request := ⟨⟨⟨560,781,169,3964⟩,5316921262080,10299257375⟩,0,3,1,385610,33⟩
private theorem pass2645_2390 : (Triangular src2645) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2645_2391 : (Triangular src2645) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2645_2394 : (Triangular src2645) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2645_2402 : (Triangular src2645) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2645_2426 : (Triangular src2645) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2645_2496 : (Triangular src2645) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2645 : Cover (Triangular src2645) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2645_2390, by decide, by decide, pass2645_2391, by decide, by decide, pass2645_2394, by decide, by decide, pass2645_2402, by decide, by decide, pass2645_2426, by decide, by decide, pass2645_2496, rfl⟩
def src2646 : Request := ⟨⟨⟨560,781,172,4034⟩,5388141854720,10440670587⟩,1,3,1,385610,33⟩
private theorem pass2646_2390 : (Triangular src2646) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2646_2391 : (Triangular src2646) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2646_2394 : (Triangular src2646) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2646_2402 : (Triangular src2646) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2646_2426 : (Triangular src2646) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2646_2496 : (Triangular src2646) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2646 : Cover (Triangular src2646) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2646_2390, by decide, by decide, pass2646_2391, by decide, by decide, pass2646_2394, by decide, by decide, pass2646_2402, by decide, by decide, pass2646_2426, by decide, by decide, pass2646_2496, rfl⟩
def src2647 : Request := ⟨⟨⟨690,962,212,4694⟩,10065769922560,23997864317⟩,2,3,1,385610,33⟩
private theorem pass2647_2390 : (Triangular src2647) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2647_2391 : (Triangular src2647) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2647_2393 : (Triangular src2647) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2647_2399 : (Triangular src2647) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2647_2416 : (Triangular src2647) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2647_2464 : (Triangular src2647) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2647 : Cover (Triangular src2647) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2647_2390, by decide, by decide, pass2647_2391, by decide, by decide, pass2647_2393, by decide, by decide, pass2647_2399, by decide, by decide, pass2647_2416, by decide, by decide, pass2647_2464, rfl⟩
def src2648 : Request := ⟨⟨⟨690,962,212,4857⟩,10065769922560,23997864317⟩,3,3,1,385610,33⟩
private theorem pass2648_2390 : (Triangular src2648) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2648_2391 : (Triangular src2648) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2648_2393 : (Triangular src2648) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2648_2399 : (Triangular src2648) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2648_2416 : (Triangular src2648) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2648_2464 : (Triangular src2648) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2648 : Cover (Triangular src2648) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2648_2390, by decide, by decide, pass2648_2391, by decide, by decide, pass2648_2393, by decide, by decide, pass2648_2399, by decide, by decide, pass2648_2416, by decide, by decide, pass2648_2464, rfl⟩
def src2649 : Request := ⟨⟨⟨690,962,212,5040⟩,10065769922560,23997864317⟩,4,3,1,385610,33⟩
private theorem pass2649_2390 : (Triangular src2649) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2649_2391 : (Triangular src2649) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2649_2393 : (Triangular src2649) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2649_2399 : (Triangular src2649) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2649_2416 : (Triangular src2649) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2649_2464 : (Triangular src2649) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2649 : Cover (Triangular src2649) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2649_2390, by decide, by decide, pass2649_2391, by decide, by decide, pass2649_2393, by decide, by decide, pass2649_2399, by decide, by decide, pass2649_2416, by decide, by decide, pass2649_2464, rfl⟩
def src2650 : Request := ⟨⟨⟨825,1151,253,5924⟩,17161575202816,49010625289⟩,6,3,1,385610,33⟩
private theorem pass2650_2390 : (Triangular src2650) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2650_2391 : (Triangular src2650) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2650_2393 : (Triangular src2650) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2650_2399 : (Triangular src2650) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2650_2416 : (Triangular src2650) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2650_2463 : (Triangular src2650) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2650 : Cover (Triangular src2650) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2650_2390, by decide, by decide, pass2650_2391, by decide, by decide, pass2650_2393, by decide, by decide, pass2650_2399, by decide, by decide, pass2650_2416, by decide, by decide, pass2650_2463, rfl⟩
def src2651 : Request := ⟨⟨⟨1000,1395,307,7276⟩,30557599170560,105715278267⟩,10,3,1,385610,33⟩
private theorem pass2651_2390 : (Triangular src2651) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2651_2391 : (Triangular src2651) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2651_2393 : (Triangular src2651) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2651_2399 : (Triangular src2651) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2651_2415 : (Triangular src2651) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2651_2459 : (Triangular src2651) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2651 : Cover (Triangular src2651) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2651_2390, by decide, by decide, pass2651_2391, by decide, by decide, pass2651_2393, by decide, by decide, pass2651_2399, by decide, by decide, pass2651_2415, by decide, by decide, pass2651_2459, rfl⟩
def src2652 : Request := ⟨⟨⟨1750,2441,537,12721⟩,163381988556800,988269431527⟩,25,3,1,385610,33⟩
private theorem pass2652_2390 : (Triangular src2652) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2652_2391 : (Triangular src2652) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2652_2393 : (Triangular src2652) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2652_2398 : (Triangular src2652) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2652_2412 : (Triangular src2652) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2652_2449 : (Triangular src2652) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2652 : Cover (Triangular src2652) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2652_2390, by decide, by decide, pass2652_2391, by decide, by decide, pass2652_2393, by decide, by decide, pass2652_2398, by decide, by decide, pass2652_2412, by decide, by decide, pass2652_2449, rfl⟩
def src2653 : Request := ⟨⟨⟨3950,5510,1244,27504⟩,1913299978158080,26129827888718⟩,65,3,1,385610,33⟩
private theorem pass2653_2390 : (Triangular src2653) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2653_2391 : (Triangular src2653) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2653_2393 : (Triangular src2653) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2653_2398 : (Triangular src2653) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2653_2411 : (Triangular src2653) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2653_2445 : (Triangular src2653) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2653_2533 : (Triangular src2653) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2653 : Cover (Triangular src2653) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2653_2390, by decide, by decide, pass2653_2391, by decide, by decide, pass2653_2393, by decide, by decide, pass2653_2398, by decide, by decide, pass2653_2411, by decide, by decide, pass2653_2445, by decide, by decide, pass2653_2533, rfl⟩
def src2654 : Request := ⟨⟨⟨6900,9625,2118,53719⟩,9997036108906496,238335796784464⟩,145,3,1,385610,33⟩
private theorem pass2654_2390 : (Triangular src2654) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2654_2391 : (Triangular src2654) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2654_2393 : (Triangular src2654) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2654_2398 : (Triangular src2654) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2654_2411 : (Triangular src2654) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2654_2445 : (Triangular src2654) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2654_2533 : (Triangular src2654) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2654 : Cover (Triangular src2654) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2654_2390, by decide, by decide, pass2654_2391, by decide, by decide, pass2654_2393, by decide, by decide, pass2654_2398, by decide, by decide, pass2654_2411, by decide, by decide, pass2654_2445, by decide, by decide, pass2654_2533, rfl⟩
def src2655 : Request := ⟨⟨⟨10000,13950,3070,72621⟩,30428373265940480,1051468979452278⟩,190,3,1,385610,33⟩
private theorem pass2655_2390 : (Triangular src2655) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2655_2391 : (Triangular src2655) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2655_2393 : (Triangular src2655) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2655_2398 : (Triangular src2655) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2655_2411 : (Triangular src2655) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2655_2445 : (Triangular src2655) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2655_2532 : (Triangular src2655) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2655 : Cover (Triangular src2655) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2655_2390, by decide, by decide, pass2655_2391, by decide, by decide, pass2655_2393, by decide, by decide, pass2655_2398, by decide, by decide, pass2655_2411, by decide, by decide, pass2655_2445, by decide, by decide, pass2655_2532, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source2017

-- Source: Research6969.PrefixRescueDataMiddle57
section Z6969Source2018
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle57
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,32⟩
  bank i := ![bank157 3926, bank196 4691, bank192 4971, bank193 5206, bank204 6109, bank222 7512, bank242 13133, bank310 28792, bank368 60047, bank340 44053, bank327 35169] i
  reserve i := ![0, 1, 2, 4, 6, 10, 25, 65, 145, 110, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385610
  seedFloor := 32

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank157 3926
    · exact rank196 4691
    · exact rank192 4971
    · exact rank193 5206
    · exact rank204 6109
    · exact rank222 7512
    · exact rank242 13133
    · exact rank310 28792
    · exact rank368 60047
    · exact rank340 44053
    · exact rank327 35169
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2634⟩
    · exact ⟨_, cover2635⟩
    · exact ⟨_, cover2636⟩
    · exact ⟨_, cover2637⟩
    · exact ⟨_, cover2638⟩
    · exact ⟨_, cover2639⟩
    · exact ⟨_, cover2640⟩
    · exact ⟨_, cover2641⟩
    · exact ⟨_, cover2644⟩
    · exact ⟨_, cover2643⟩
    · exact ⟨_, cover2642⟩

def price : EarlyPrice := ⟨3, 32, 10, 70/100, 70/100, ![748840552629, 159427734750, 31775871036, 1986010572], 847663831918226⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![3817/37, 33351/37, 386591/111, 1409696/111] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle57
end Z6969Source2018

-- Source: Research6969.PrefixMiddleSaved57
section Z6969Source2019
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved57
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle57.price Lower6960.Prefix6969RescueData.Middle57.price :=
  ⟨335, 3513, 103, 901, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle57.plan Lower6960.Prefix6969RescueData.Middle57.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 3 32 32 :=
  ⟨Lower6960.Prefix6969MainCases.Middle57.plan, Lower6960.Prefix6969MainCases.Middle57.price, Lower6960.Prefix6969MainCases.Middle57.valid, Lower6960.Prefix6969MainCases.Middle57.priced, Lower6960.Prefix6969MainCases.Middle57.sources,
   Lower6960.Prefix6969RescueData.Middle57.plan, Lower6960.Prefix6969RescueData.Middle57.price, Lower6960.Prefix6969RescueData.Middle57.sources, Lower6960.Prefix6969RescueData.Middle57.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved57
end Z6969Source2019

-- Source: Research6969.PrefixMainDataMiddle58
section Z6969Source2020
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle58
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 20, 17, 21, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank58 2054, bank81 3885, bank82 2422, bank75 3842, bank99 2680, bank127 3031, bank144 3940, bank126 11206, bank161 5142, bank212 8810, bank183 20877, bank174 26788, bank169 29097] i
  head := src2955
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15089, 123282, 571348, 2042651],
    ![25417/2, 360617/4, 409381, 1399489],
    ![54680/9, 392590/9, 409381, 5582745/4],
    ![29433/8, 424053/16, 213358, 672516],
    ![16211/9, 54303/4, 2226141/16, 7255413/16],
    ![24292/27, 594833/81, 2702611/36, 4644025/16],
    ![73478/121, 65394/11, 3248415/49, 4644025/16],
    ![73478/121, 65394/11, 3248415/49, 931225/4],
    ![73478/121, 650950/121, 2930720/49, 8854794/49],
    ![235552/441, 702152/147, 4650333/98, 8854794/49],
    ![235552/441, 702152/147, 4650333/98, 8854794/49],
    ![3719/7, 99802/21, 4591271/98, 8854794/49],
    ![3719/7, 99802/21, 4591271/98, 160465],
    ![3719/7, 1074553/242, 4591271/98, 1866663/14],
    ![3719/7, 1312139/300, 5240200/121, 2547801/20],
    ![1355575/3362, 1312139/300, 5240200/121, 2547801/20],
    ![1355575/3362, 6548748/1681, 7362381/196, 2937796/25],
    ![1355575/3362, 19144699/5476, 86084915/2601, 26585937/250],
    ![954471/2738, 19144699/5476, 86084915/2601, 26585937/250],
    ![462882/1369, 19144699/5476, 86084915/2601, 26585937/250],
    ![459151/1369, 19144699/5476, 86084915/2601, 26585937/250]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 33 385610 := by
  refine ⟨?_, rank154 4311, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2955⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free32_1
    · exact free41_1
    · exact free42_6
    · exact free48_1
    · exact free58_1
    · exact free81_1
    · exact free82_1
    · exact free75_1
    · exact free99_1
    · exact free127_1
    · exact free144_1
    · exact free126_1
    · exact free161_1
    · exact free212_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [236393603, 305521052, 305348989, 305899360, 304640487, 306295994, 308929757, 308309384, 154553315, 155235980, 154986133, 155349518, 155188396, 107939685, 66625567, 77178426, 90929636, 91004130, 118510061, 100000000, 219300924], [1561762, 1163342, 1164223, 1161405, 1167852, 1159373, 1145885, 1149062, 2493880, 2482517, 2486676, 2480627, 2483309, 3653506, 6036892, 5186386, 4373198, 4369437, 3308746, 3958949, 1702447],
  ![116409316477680, 1623877150956, 197370831600, 5204105620], 126824690377699630⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 19144699/5476, 86084915/2601, 26585937/250] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle58
end Z6969Source2020

-- Source: Research6969.PrefixRescueDataMiddle58
section Z6969Source2021
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle58
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,33⟩
  bank i := ![bank155 3964, bank156 4034, bank193 4694, bank193 4857, bank193 5040, bank204 5924, bank222 7276, bank242 12721, bank311 27504, bank353 53719, bank377 72621] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 65, 145, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385610
  seedFloor := 33

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank155 3964
    · exact rank156 4034
    · exact rank193 4694
    · exact rank193 4857
    · exact rank193 5040
    · exact rank204 5924
    · exact rank222 7276
    · exact rank242 12721
    · exact rank311 27504
    · exact rank353 53719
    · exact rank377 72621
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2645⟩
    · exact ⟨_, cover2646⟩
    · exact ⟨_, cover2647⟩
    · exact ⟨_, cover2648⟩
    · exact ⟨_, cover2649⟩
    · exact ⟨_, cover2650⟩
    · exact ⟨_, cover2651⟩
    · exact ⟨_, cover2652⟩
    · exact ⟨_, cover2653⟩
    · exact ⟨_, cover2654⟩
    · exact ⟨_, cover2655⟩

def price : EarlyPrice := ⟨3, 33, 10, 70/100, 70/100, ![933951230262, 196527206979, 39482109540, 2392877730], 915801793012213⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![13861/146, 123613/146, 239391/73, 1772727/146] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle58
end Z6969Source2021

-- Source: Research6969.PrefixMiddleSaved58
section Z6969Source2022
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved58
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle58.price Lower6960.Prefix6969RescueData.Middle58.price :=
  ⟨335, 3496, 94, 846, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle58.plan Lower6960.Prefix6969RescueData.Middle58.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 3 33 33 :=
  ⟨Lower6960.Prefix6969MainCases.Middle58.plan, Lower6960.Prefix6969MainCases.Middle58.price, Lower6960.Prefix6969MainCases.Middle58.valid, Lower6960.Prefix6969MainCases.Middle58.priced, Lower6960.Prefix6969MainCases.Middle58.sources,
   Lower6960.Prefix6969RescueData.Middle58.plan, Lower6960.Prefix6969RescueData.Middle58.price, Lower6960.Prefix6969RescueData.Middle58.sources, Lower6960.Prefix6969RescueData.Middle58.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved58
end Z6969Source2022

-- Source: Research6969.PrefixMainDataMiddle59
section Z6969Source2023
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle59
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 20, 23, 25, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank35 1600, bank44 1848, bank53 2196, bank42 2862, bank61 2044, bank69 3442, bank72 2320, bank95 2576, bank115 2949, bank92 3992, bank140 3403, bank130 10521, bank164 5088, bank212 8810, bank186 19684, bank174 26788, bank169 29097] i
  head := src2956
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15471, 123190, 567294, 1966906],
    ![25417/2, 358915/4, 407449, 1399489],
    ![54680/9, 130250/3, 407449, 5523175/4],
    ![29433/8, 422075/16, 1911298/9, 665340],
    ![5710/3, 80875/6, 1099545/8, 426500],
    ![18775/16, 548735/64, 2480111/25, 1576344/5],
    ![86808/121, 646280/121, 2906572/49, 4822416/25],
    ![73478/121, 646280/121, 2906572/49, 4822416/25],
    ![73478/121, 646280/121, 2906572/49, 1245380/7],
    ![73478/121, 1869740/361, 2478240/49, 1245380/7],
    ![73478/121, 1869740/361, 2478240/49, 1245380/7],
    ![73478/121, 1869740/361, 2478240/49, 1245380/7],
    ![73478/121, 1983610/441, 751995/16, 8696601/64],
    ![73478/121, 1983610/441, 751995/16, 8696601/64],
    ![73478/121, 1983610/441, 751995/16, 8696601/64],
    ![33463/82, 1983610/441, 751995/16, 8696601/64],
    ![33463/82, 159700/41, 1839249/49, 2876416/25],
    ![33463/82, 19052285/5476, 85674365/2601, 5260451/50],
    ![481425/1369, 19052285/5476, 85674365/2601, 5260451/50],
    ![462882/1369, 19052285/5476, 85674365/2601, 5260451/50],
    ![459151/1369, 19052285/5476, 85674365/2601, 5260451/50]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 3 34 385610 := by
  refine ⟨?_, rank154 4265, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2956⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free35_1
    · exact free44_1
    · exact free53_1
    · exact free42_6
    · exact free61_1
    · exact free69_1
    · exact free72_1
    · exact free95_1
    · exact free115_1
    · exact free92_1
    · exact free140_1
    · exact free130_1
    · exact free164_1
    · exact free212_1
    · exact free186_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [236584175, 304352756, 305081892, 305275379, 305617694, 305533518, 305018361, 304833414, 164085349, 163905416, 163881040, 164100723, 81970807, 54398749, 71911720, 79295524, 91517762, 91580920, 118406479, 100000000, 219103444], [1560194, 1169325, 1165591, 1164600, 1162847, 1163278, 1165916, 1166864, 2335225, 2338220, 2338626, 2334969, 4870238, 7438110, 5580228, 5040014, 4343508, 4340320, 3311645, 3958949, 1704073],
  ![116304490144080, 1624091739956, 197193099600, 5168774520], 126637495925607463⟩

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
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 20 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 19052285/5476, 85674365/2601, 5260451/50] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle59
end Z6969Source2023

end Merged_Z6969Pack0747

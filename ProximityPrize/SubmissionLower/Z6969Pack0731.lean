import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0730
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0724
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0731
section Merged_Z6969Pack0731

-- Source: Research6969.PrefixMiddleSaved94
section Z6969Source1820
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved94
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle94.price Lower6960.Prefix6969RescueData.Middle94.price :=
  ⟨335, 3469, 80, 888, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle94.plan Lower6960.Prefix6969RescueData.Middle94.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 37 37 :=
  ⟨Lower6960.Prefix6969MainCases.Middle94.plan, Lower6960.Prefix6969MainCases.Middle94.price, Lower6960.Prefix6969MainCases.Middle94.valid, Lower6960.Prefix6969MainCases.Middle94.priced, Lower6960.Prefix6969MainCases.Middle94.sources,
   Lower6960.Prefix6969RescueData.Middle94.plan, Lower6960.Prefix6969RescueData.Middle94.price, Lower6960.Prefix6969RescueData.Middle94.sources, Lower6960.Prefix6969RescueData.Middle94.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved94
end Z6969Source1820

-- Source: Research6969.PrefixMainDataMiddle95
section Z6969Source1821
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle95
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 20, 23, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank35 1600, bank44 1848, bank53 2196, bank42 2862, bank61 2044, bank69 3442, bank72 2320, bank95 2576, bank112 2964, bank138 3222, bank144 3940, bank126 11206, bank164 5088, bank214 8650, bank183 20877, bank174 26788, bank169 29097] i
  head := src2780
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15734, 123048, 565887, 1952127],
    ![25417/2, 89035, 404299, 1399489],
    ![54680/9, 129250/3, 404299, 2713025/2],
    ![29433/8, 209425/8, 1896748/9, 653640],
    ![5710/3, 13375, 545535/4, 419000],
    ![18775/16, 272305/32, 2461586/25, 1548624/5],
    ![86808/121, 641480/121, 2885272/49, 4822416/25],
    ![73478/121, 641480/121, 2885272/49, 4822416/25],
    ![73478/121, 641480/121, 2885272/49, 1223480/7],
    ![73478/121, 97760/19, 2478240/49, 1223480/7],
    ![73478/121, 97760/19, 2478240/49, 1223480/7],
    ![73478/121, 97760/19, 2478240/49, 1223480/7],
    ![73478/121, 1954700/441, 187473/4, 549081/4],
    ![73478/121, 1954700/441, 187473/4, 549081/4],
    ![73478/121, 43137/10, 5240200/121, 247629/2],
    ![1355575/3362, 43137/10, 5240200/121, 247629/2],
    ![1355575/3362, 6493400/1681, 1824174/49, 2876416/25],
    ![1355575/3362, 4743795/1369, 85372210/2601, 507409/5],
    ![954471/2738, 4743795/1369, 85372210/2601, 507409/5],
    ![462882/1369, 4743795/1369, 85372210/2601, 507409/5],
    ![459151/1369, 4743795/1369, 85372210/2601, 507409/5]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 38 257073 := by
  refine ⟨?_, rank154 4190, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2780⟩⟩
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
    · exact free112_1
    · exact free138_1
    · exact free144_1
    · exact free126_1
    · exact free164_1
    · exact free214_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [236201146, 303758741, 303204053, 303101789, 304151149, 302401616, 303053190, 303857789, 162340771, 162283391, 162314381, 162215736, 81623961, 81623719, 64699093, 77678603, 91198772, 91187465, 118025740, 100000000, 218952652], [1563346, 1172367, 1175208, 1175732, 1170358, 1179318, 1175981, 1171860, 2364263, 2365218, 2364702, 2366344, 4890856, 4890871, 6221901, 5151805, 4359611, 4360182, 3322300, 3958949, 1705314],
  ![116224446734640, 1624255286648, 197057386800, 5188616580], 126062926515208276⟩

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
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 4743795/1369, 85372210/2601, 507409/5] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle95
end Z6969Source1821

-- Source: Research6969.PhysicalChecks142
section Z6969Source1822
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2272 : Request := ⟨⟨⟨6900,9625,2118,48910⟩,9997036108906496,238335796784464⟩,145,2,1,257073,38⟩
private theorem pass2272_2390 : (Triangular src2272) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2272_2391 : (Triangular src2272) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2272_2393 : (Triangular src2272) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2272_2398 : (Triangular src2272) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2272_2411 : (Triangular src2272) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2272_2445 : (Triangular src2272) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2272_2533 : (Triangular src2272) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2272 : Cover (Triangular src2272) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2272_2390, by decide, by decide, pass2272_2391, by decide, by decide, pass2272_2393, by decide, by decide, pass2272_2398, by decide, by decide, pass2272_2411, by decide, by decide, pass2272_2445, by decide, by decide, pass2272_2533, rfl⟩
def src2273 : Request := ⟨⟨⟨470,655,144,3162⟩,3184589537280,5168862572⟩,0,2,1,257073,39⟩
private theorem pass2273_2390 : (Triangular src2273) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2273_2391 : (Triangular src2273) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2273_2394 : (Triangular src2273) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2273_2403 : (Triangular src2273) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2273_2430 : (Triangular src2273) 2430 2510 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2273_2511 : (Triangular src2273) 2511 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2273 : Cover (Triangular src2273) 2534 2390 [2390,2393,2402,2429,2510,2534] := by
  exact ⟨by decide, by decide, pass2273_2390, by decide, by decide, pass2273_2391, by decide, by decide, pass2273_2394, by decide, by decide, pass2273_2403, by decide, by decide, pass2273_2430, by decide, by decide, pass2273_2511, rfl⟩
def src2274 : Request := ⟨⟨⟨560,781,176,3599⟩,5482316038144,10627925923⟩,1,2,1,257073,39⟩
private theorem pass2274_2390 : (Triangular src2274) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2274_2391 : (Triangular src2274) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2274_2393 : (Triangular src2274) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2274_2399 : (Triangular src2274) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2274_2417 : (Triangular src2274) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2274_2469 : (Triangular src2274) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2274 : Cover (Triangular src2274) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2274_2390, by decide, by decide, pass2274_2391, by decide, by decide, pass2274_2393, by decide, by decide, pass2274_2399, by decide, by decide, pass2274_2417, by decide, by decide, pass2274_2469, rfl⟩
def src2275 : Request := ⟨⟨⟨560,781,172,3784⟩,5388141854720,10440670587⟩,2,2,1,257073,39⟩
private theorem pass2275_2390 : (Triangular src2275) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2275_2391 : (Triangular src2275) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2275_2394 : (Triangular src2275) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2275_2402 : (Triangular src2275) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2275_2426 : (Triangular src2275) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2275_2496 : (Triangular src2275) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2275 : Cover (Triangular src2275) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2275_2390, by decide, by decide, pass2275_2391, by decide, by decide, pass2275_2394, by decide, by decide, pass2275_2402, by decide, by decide, pass2275_2426, by decide, by decide, pass2275_2496, rfl⟩
def src2276 : Request := ⟨⟨⟨560,781,172,3948⟩,5388141854720,10440670587⟩,3,2,1,257073,39⟩
private theorem pass2276_2390 : (Triangular src2276) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2276_2391 : (Triangular src2276) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2276_2394 : (Triangular src2276) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2276_2402 : (Triangular src2276) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2276_2426 : (Triangular src2276) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2276_2496 : (Triangular src2276) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2276 : Cover (Triangular src2276) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2276_2390, by decide, by decide, pass2276_2391, by decide, by decide, pass2276_2394, by decide, by decide, pass2276_2402, by decide, by decide, pass2276_2426, by decide, by decide, pass2276_2496, rfl⟩
def src2277 : Request := ⟨⟨⟨690,962,212,4536⟩,10065769922560,23997864317⟩,4,2,1,257073,39⟩
private theorem pass2277_2390 : (Triangular src2277) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2277_2391 : (Triangular src2277) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2277_2393 : (Triangular src2277) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2277_2399 : (Triangular src2277) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2277_2416 : (Triangular src2277) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2277_2465 : (Triangular src2277) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2277 : Cover (Triangular src2277) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2277_2390, by decide, by decide, pass2277_2391, by decide, by decide, pass2277_2393, by decide, by decide, pass2277_2399, by decide, by decide, pass2277_2416, by decide, by decide, pass2277_2465, rfl⟩
def src2278 : Request := ⟨⟨⟨690,962,212,4847⟩,10065769922560,23997864317⟩,6,2,1,257073,39⟩
private theorem pass2278_2390 : (Triangular src2278) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2278_2391 : (Triangular src2278) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2278_2393 : (Triangular src2278) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2278_2399 : (Triangular src2278) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2278_2416 : (Triangular src2278) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2278_2464 : (Triangular src2278) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2278 : Cover (Triangular src2278) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2278_2390, by decide, by decide, pass2278_2391, by decide, by decide, pass2278_2393, by decide, by decide, pass2278_2399, by decide, by decide, pass2278_2416, by decide, by decide, pass2278_2464, rfl⟩
def src2279 : Request := ⟨⟨⟨825,1151,260,5893⟩,17518948515840,50057971890⟩,10,2,1,257073,39⟩
private theorem pass2279_2390 : (Triangular src2279) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2279_2391 : (Triangular src2279) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2279_2393 : (Triangular src2279) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2279_2399 : (Triangular src2279) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2279_2416 : (Triangular src2279) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2279_2463 : (Triangular src2279) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2279 : Cover (Triangular src2279) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2279_2390, by decide, by decide, pass2279_2391, by decide, by decide, pass2279_2393, by decide, by decide, pass2279_2399, by decide, by decide, pass2279_2416, by decide, by decide, pass2279_2463, rfl⟩
def src2280 : Request := ⟨⟨⟨1450,2022,445,10451⟩,92998964346880,465769321795⟩,25,2,1,257073,39⟩
private theorem pass2280_2390 : (Triangular src2280) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2280_2391 : (Triangular src2280) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2280_2393 : (Triangular src2280) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2280_2399 : (Triangular src2280) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2280_2415 : (Triangular src2280) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2280_2458 : (Triangular src2280) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2280 : Cover (Triangular src2280) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2280_2390, by decide, by decide, pass2280_2391, by decide, by decide, pass2280_2393, by decide, by decide, pass2280_2399, by decide, by decide, pass2280_2415, by decide, by decide, pass2280_2458, rfl⟩
def src2281 : Request := ⟨⟨⟨2100,2929,662,14755⟩,288013660979200,2090961110089⟩,40,2,1,257073,39⟩
private theorem pass2281_2390 : (Triangular src2281) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2281_2391 : (Triangular src2281) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2281_2393 : (Triangular src2281) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2281_2398 : (Triangular src2281) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2281_2412 : (Triangular src2281) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2281_2449 : (Triangular src2281) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2281 : Cover (Triangular src2281) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2281_2390, by decide, by decide, pass2281_2391, by decide, by decide, pass2281_2393, by decide, by decide, pass2281_2398, by decide, by decide, pass2281_2412, by decide, by decide, pass2281_2449, rfl⟩
def src2282 : Request := ⟨⟨⟨3950,5510,1213,28414⟩,1877062482395136,25622281045803⟩,85,2,1,257073,39⟩
private theorem pass2282_2390 : (Triangular src2282) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2282_2391 : (Triangular src2282) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2282_2393 : (Triangular src2282) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2282_2398 : (Triangular src2282) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2282_2411 : (Triangular src2282) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2282_2445 : (Triangular src2282) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2282_2534 : (Triangular src2282) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2282 : Cover (Triangular src2282) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass2282_2390, by decide, by decide, pass2282_2391, by decide, by decide, pass2282_2393, by decide, by decide, pass2282_2398, by decide, by decide, pass2282_2411, by decide, by decide, pass2282_2445, by decide, by decide, pass2282_2534, rfl⟩
def src2283 : Request := ⟨⟨⟨8300,11577,2548,59758⟩,17399709518790656,498847383098023⟩,190,2,1,257073,39⟩
private theorem pass2283_2390 : (Triangular src2283) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2283_2391 : (Triangular src2283) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2283_2393 : (Triangular src2283) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2283_2398 : (Triangular src2283) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2283_2411 : (Triangular src2283) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2283_2445 : (Triangular src2283) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2283_2532 : (Triangular src2283) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2283 : Cover (Triangular src2283) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2283_2390, by decide, by decide, pass2283_2391, by decide, by decide, pass2283_2393, by decide, by decide, pass2283_2398, by decide, by decide, pass2283_2411, by decide, by decide, pass2283_2445, by decide, by decide, pass2283_2532, rfl⟩
def src2284 : Request := ⟨⟨⟨470,655,144,3098⟩,3184589537280,5168862572⟩,0,2,1,257073,40⟩
private theorem pass2284_2390 : (Triangular src2284) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2284_2391 : (Triangular src2284) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2284_2394 : (Triangular src2284) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2284_2403 : (Triangular src2284) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2284_2430 : (Triangular src2284) 2430 2510 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2284_2511 : (Triangular src2284) 2511 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2284 : Cover (Triangular src2284) 2534 2390 [2390,2393,2402,2429,2510,2534] := by
  exact ⟨by decide, by decide, pass2284_2390, by decide, by decide, pass2284_2391, by decide, by decide, pass2284_2394, by decide, by decide, pass2284_2403, by decide, by decide, pass2284_2430, by decide, by decide, pass2284_2511, rfl⟩
def src2285 : Request := ⟨⟨⟨470,655,144,3249⟩,3184589537280,5168862572⟩,1,2,1,257073,40⟩
private theorem pass2285_2390 : (Triangular src2285) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2285_2391 : (Triangular src2285) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2285_2394 : (Triangular src2285) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2285_2403 : (Triangular src2285) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2285_2430 : (Triangular src2285) 2430 2510 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2285_2511 : (Triangular src2285) 2511 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2285 : Cover (Triangular src2285) 2534 2390 [2390,2393,2402,2429,2510,2534] := by
  exact ⟨by decide, by decide, pass2285_2390, by decide, by decide, pass2285_2391, by decide, by decide, pass2285_2394, by decide, by decide, pass2285_2403, by decide, by decide, pass2285_2430, by decide, by decide, pass2285_2511, rfl⟩
def src2286 : Request := ⟨⟨⟨560,781,169,3801⟩,5316921262080,10299257375⟩,2,2,1,257073,40⟩
private theorem pass2286_2390 : (Triangular src2286) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2286_2391 : (Triangular src2286) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2286_2394 : (Triangular src2286) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2286_2402 : (Triangular src2286) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2286_2426 : (Triangular src2286) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2286_2496 : (Triangular src2286) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2286 : Cover (Triangular src2286) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2286_2390, by decide, by decide, pass2286_2391, by decide, by decide, pass2286_2394, by decide, by decide, pass2286_2402, by decide, by decide, pass2286_2426, by decide, by decide, pass2286_2496, rfl⟩
def src2287 : Request := ⟨⟨⟨560,781,176,3810⟩,5482316038144,10627925923⟩,3,2,1,257073,40⟩
private theorem pass2287_2390 : (Triangular src2287) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2287_2391 : (Triangular src2287) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2287_2394 : (Triangular src2287) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2287_2402 : (Triangular src2287) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2287_2426 : (Triangular src2287) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2287_2496 : (Triangular src2287) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2287 : Cover (Triangular src2287) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2287_2390, by decide, by decide, pass2287_2391, by decide, by decide, pass2287_2394, by decide, by decide, pass2287_2402, by decide, by decide, pass2287_2426, by decide, by decide, pass2287_2496, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1822

-- Source: Research6969.PrefixRescueDataMiddle95
section Z6969Source1823
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle95
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,38⟩
  bank i := ![bank142 3234, bank155 3813, bank156 3872, bank193 4489, bank192 4772, bank193 4974, bank204 5778, bank228 8362, bank243 11522, bank268 18408, bank353 48910] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 16, 25, 50, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 38

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 3234
    · exact rank155 3813
    · exact rank156 3872
    · exact rank193 4489
    · exact rank192 4772
    · exact rank193 4974
    · exact rank204 5778
    · exact rank228 8362
    · exact rank243 11522
    · exact rank268 18408
    · exact rank353 48910
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2262⟩
    · exact ⟨_, cover2263⟩
    · exact ⟨_, cover2264⟩
    · exact ⟨_, cover2265⟩
    · exact ⟨_, cover2266⟩
    · exact ⟨_, cover2267⟩
    · exact ⟨_, cover2268⟩
    · exact ⟨_, cover2269⟩
    · exact ⟨_, cover2270⟩
    · exact ⟨_, cover2271⟩
    · exact ⟨_, cover2272⟩

def price : EarlyPrice := ⟨2, 38, 10, 65/100, 60/100, ![724318020910, 130234023837, 31365887718, 825433314], 647055225241528⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![11743/146, 64697/73, 231785/73, 12730] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle95
end Z6969Source1823

-- Source: Research6969.PrefixMiddleSaved95
section Z6969Source1824
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved95
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle95.price Lower6960.Prefix6969RescueData.Middle95.price :=
  ⟨335, 3465, 80, 886, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle95.plan Lower6960.Prefix6969RescueData.Middle95.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 38 38 :=
  ⟨Lower6960.Prefix6969MainCases.Middle95.plan, Lower6960.Prefix6969MainCases.Middle95.price, Lower6960.Prefix6969MainCases.Middle95.valid, Lower6960.Prefix6969MainCases.Middle95.priced, Lower6960.Prefix6969MainCases.Middle95.sources,
   Lower6960.Prefix6969RescueData.Middle95.plan, Lower6960.Prefix6969RescueData.Middle95.price, Lower6960.Prefix6969RescueData.Middle95.sources, Lower6960.Prefix6969RescueData.Middle95.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved95
end Z6969Source1824

-- Source: Research6969.PrefixMainDataMiddle96
section Z6969Source1825
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle96
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 20, 23, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank35 1600, bank44 1848, bank53 2196, bank42 2862, bank61 2044, bank69 3442, bank72 2320, bank95 2576, bank112 2964, bank138 3222, bank144 3940, bank126 11206, bank165 5082, bank214 8650, bank183 20877, bank174 26788, bank169 29097] i
  head := src2781
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15734, 122868, 565077, 1946412],
    ![25417/2, 354475/4, 402409, 1399489],
    ![54680/9, 128650/3, 402409, 5367775/4],
    ![29433/8, 416915/16, 1888018/9, 646620],
    ![5710/3, 26625/2, 1085985/8, 414500],
    ![18775/16, 542135/64, 2450471/25, 1531992/5],
    ![86808/121, 638600/121, 410356/7, 4822416/25],
    ![73478/121, 638600/121, 410356/7, 4822416/25],
    ![73478/121, 638600/121, 410356/7, 1210340/7],
    ![73478/121, 1850060/361, 2478240/49, 1210340/7],
    ![73478/121, 1850060/361, 2478240/49, 1210340/7],
    ![73478/121, 1850060/361, 2478240/49, 1210340/7],
    ![73478/121, 277790/63, 187473/4, 549081/4],
    ![73478/121, 277790/63, 187473/4, 549081/4],
    ![73478/121, 85827/20, 5240200/121, 489939/4],
    ![1355575/3362, 85827/20, 5240200/121, 489939/4],
    ![1355575/3362, 6473320/1681, 1813971/49, 2869636/25],
    ![1355575/3362, 4720485/1369, 84957355/2601, 1003919/10],
    ![954471/2738, 4720485/1369, 84957355/2601, 1003919/10],
    ![462882/1369, 4720485/1369, 84957355/2601, 1003919/10],
    ![459151/1369, 4720485/1369, 84957355/2601, 1003919/10]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 39 257073 := by
  refine ⟨?_, rank154 4145, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2781⟩⟩
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
    · exact free112_1
    · exact free138_1
    · exact free144_1
    · exact free126_1
    · exact free165_1
    · exact free214_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [235247056, 302213394, 301778032, 301687162, 303032913, 303021817, 302850678, 303316099, 164106333, 163824266, 164154650, 163965209, 82853478, 82815457, 64618140, 78338597, 92139058, 92139228, 117636314, 100000000, 218753186], [1571199, 1180282, 1182511, 1182977, 1176085, 1176141, 1177018, 1174634, 2334876, 2339571, 2334072, 2337225, 4817769, 4820029, 6230207, 5106174, 4312144, 4312136, 3333198, 3958949, 1706956],
  ![116118566192520, 1624471846744, 196877867400, 5131451360], 125390924518548298⟩

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
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 4720485/1369, 84957355/2601, 1003919/10] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle96
end Z6969Source1825

-- Source: Research6969.PrefixRescueDataMiddle96
section Z6969Source1826
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle96
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,39⟩
  bank i := ![bank142 3162, bank157 3599, bank156 3784, bank156 3948, bank193 4536, bank193 4847, bank205 5893, bank233 10451, bank250 14755, bank310 28414, bank365 59758] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 40, 85, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 39

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 3162
    · exact rank157 3599
    · exact rank156 3784
    · exact rank156 3948
    · exact rank193 4536
    · exact rank193 4847
    · exact rank205 5893
    · exact rank233 10451
    · exact rank250 14755
    · exact rank310 28414
    · exact rank365 59758
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2273⟩
    · exact ⟨_, cover2274⟩
    · exact ⟨_, cover2275⟩
    · exact ⟨_, cover2276⟩
    · exact ⟨_, cover2277⟩
    · exact ⟨_, cover2278⟩
    · exact ⟨_, cover2279⟩
    · exact ⟨_, cover2280⟩
    · exact ⟨_, cover2281⟩
    · exact ⟨_, cover2282⟩
    · exact ⟨_, cover2283⟩

def price : EarlyPrice := ⟨2, 39, 10, 65/100, 70/100, ![908256822328, 160520079598, 38726837968, 993014204], 693517015086557⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![14125/191, 159130/191, 571019/191, 2330562/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle96
end Z6969Source1826

-- Source: Research6969.PrefixMiddleSaved96
section Z6969Source1827
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved96
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle96.price Lower6960.Prefix6969RescueData.Middle96.price :=
  ⟨335, 3448, 73, 833, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle96.plan Lower6960.Prefix6969RescueData.Middle96.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 39 39 :=
  ⟨Lower6960.Prefix6969MainCases.Middle96.plan, Lower6960.Prefix6969MainCases.Middle96.price, Lower6960.Prefix6969MainCases.Middle96.valid, Lower6960.Prefix6969MainCases.Middle96.priced, Lower6960.Prefix6969MainCases.Middle96.sources,
   Lower6960.Prefix6969RescueData.Middle96.plan, Lower6960.Prefix6969RescueData.Middle96.price, Lower6960.Prefix6969RescueData.Middle96.sources, Lower6960.Prefix6969RescueData.Middle96.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved96
end Z6969Source1827

-- Source: Research6969.PrefixMainDataMiddle97
section Z6969Source1828
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle97
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 20, 23, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank35 1600, bank44 1848, bank53 2196, bank42 2862, bank61 2044, bank69 3442, bank72 2320, bank95 2576, bank112 2964, bank138 3222, bank144 3940, bank131 10228, bank164 5088, bank214 8650, bank186 19684, bank174 26788, bank169 29097] i
  head := src2782
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15734, 122692, 564285, 1940824],
    ![25417/2, 352847/4, 400561, 1399489],
    ![54680/9, 384190/9, 400561, 5310795/4],
    ![29433/8, 415023/16, 626494/3, 639756],
    ![5710/3, 238525/18, 1081013/8, 410100],
    ![18775/16, 539715/64, 2439603/25, 7578648/25],
    ![86808/121, 635784/121, 2859996/49, 4822416/25],
    ![73478/121, 635784/121, 2859996/49, 4822416/25],
    ![73478/121, 635784/121, 2859996/49, 1197492/7],
    ![73478/121, 1842844/361, 2478240/49, 1197492/7],
    ![73478/121, 1842844/361, 2478240/49, 1197492/7],
    ![73478/121, 1842844/361, 2478240/49, 1197492/7],
    ![73478/121, 214954/49, 187473/4, 549081/4],
    ![73478/121, 214954/49, 187473/4, 549081/4],
    ![73478/121, 1280849/300, 3461307/80, 2423691/20],
    ![688141/1681, 1280849/300, 3461307/80, 2423691/20],
    ![688141/1681, 156804/41, 1806285/49, 9273728/81],
    ![688141/1681, 4697693/1369, 84551719/2601, 4966311/50],
    ![481425/1369, 4697693/1369, 84551719/2601, 4966311/50],
    ![462882/1369, 4697693/1369, 84551719/2601, 4966311/50],
    ![459151/1369, 4697693/1369, 84551719/2601, 4966311/50]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 40 257073 := by
  refine ⟨?_, rank154 4101, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2782⟩⟩
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
    · exact free112_1
    · exact free138_1
    · exact free144_1
    · exact free131_1
    · exact free164_1
    · exact free214_1
    · exact free186_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [234314168, 300489820, 300942965, 300261180, 300261602, 299745169, 299600734, 303654353, 163068495, 163004800, 162716422, 163030870, 82910620, 82917016, 70700813, 70711883, 91245417, 91205570, 117258513, 100000000, 218558154], [1578877, 1189109, 1186788, 1190280, 1190277, 1192922, 1193662, 1172902, 2352150, 2353210, 2358010, 2352776, 4814372, 4813992, 5676572, 5675691, 4357257, 4359268, 3343770, 3958949, 1708561],
  ![116015039306280, 1624683327756, 196702338600, 5187528920], 124694601620898300⟩

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
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 4697693/1369, 84551719/2601, 4966311/50] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle97
end Z6969Source1828

-- Source: Research6969.PrefixRescueDataMiddle97
section Z6969Source1829
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle97
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,40⟩
  bank i := ![bank142 3098, bank142 3249, bank155 3801, bank157 3810, bank156 4030, bank193 4737, bank205 5750, bank228 8655, bank267 17855, bank325 33870, bank375 72807] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 20, 50, 110, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 40

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 3098
    · exact rank142 3249
    · exact rank155 3801
    · exact rank157 3810
    · exact rank156 4030
    · exact rank193 4737
    · exact rank205 5750
    · exact rank228 8655
    · exact rank267 17855
    · exact rank325 33870
    · exact rank375 72807
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2284⟩
    · exact ⟨_, cover2285⟩
    · exact ⟨_, cover2286⟩
    · exact ⟨_, cover2287⟩
    · exact ⟨_, cover2288⟩
    · exact ⟨_, cover2289⟩
    · exact ⟨_, cover2290⟩
    · exact ⟨_, cover2291⟩
    · exact ⟨_, cover2292⟩
    · exact ⟨_, cover2293⟩
    · exact ⟨_, cover2294⟩

def price : EarlyPrice := ⟨2, 40, 10, 65/100, 70/100, ![1134961530024, 197947701357, 47857100240, 1196449610], 768704878192908⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8509/123, 195607/246, 351767/123, 485380/41] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle97
end Z6969Source1829

-- Source: Research6969.PrefixMiddleSaved97
section Z6969Source1830
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved97
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle97.price Lower6960.Prefix6969RescueData.Middle97.price :=
  ⟨335, 3431, 69, 795, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle97.plan Lower6960.Prefix6969RescueData.Middle97.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 40 40 :=
  ⟨Lower6960.Prefix6969MainCases.Middle97.plan, Lower6960.Prefix6969MainCases.Middle97.price, Lower6960.Prefix6969MainCases.Middle97.valid, Lower6960.Prefix6969MainCases.Middle97.priced, Lower6960.Prefix6969MainCases.Middle97.sources,
   Lower6960.Prefix6969RescueData.Middle97.plan, Lower6960.Prefix6969RescueData.Middle97.price, Lower6960.Prefix6969RescueData.Middle97.sources, Lower6960.Prefix6969RescueData.Middle97.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved97
end Z6969Source1830

-- Source: Research6969.PhysicalChecks171
section Z6969Source1831
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2736 : Request := ⟨⟨⟨560,781,172,3807⟩,5388141854720,10440670587⟩,4,3,1,385610,41⟩
private theorem pass2736_2390 : (Triangular src2736) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2736_2391 : (Triangular src2736) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2736_2394 : (Triangular src2736) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2736_2402 : (Triangular src2736) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2736_2426 : (Triangular src2736) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2736_2496 : (Triangular src2736) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2736 : Cover (Triangular src2736) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2736_2390, by decide, by decide, pass2736_2391, by decide, by decide, pass2736_2394, by decide, by decide, pass2736_2402, by decide, by decide, pass2736_2426, by decide, by decide, pass2736_2496, rfl⟩
def src2737 : Request := ⟨⟨⟨560,781,176,4080⟩,5482316038144,10627925923⟩,6,3,1,385610,41⟩
private theorem pass2737_2390 : (Triangular src2737) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2737_2391 : (Triangular src2737) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2737_2393 : (Triangular src2737) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2737_2399 : (Triangular src2737) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2737_2417 : (Triangular src2737) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2737_2469 : (Triangular src2737) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2737 : Cover (Triangular src2737) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2737_2390, by decide, by decide, pass2737_2391, by decide, by decide, pass2737_2393, by decide, by decide, pass2737_2399, by decide, by decide, pass2737_2417, by decide, by decide, pass2737_2469, rfl⟩
def src2738 : Request := ⟨⟨⟨690,962,217,5063⟩,10244384358400,24434817260⟩,10,3,1,385610,41⟩
private theorem pass2738_2390 : (Triangular src2738) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2738_2391 : (Triangular src2738) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2738_2393 : (Triangular src2738) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2738_2399 : (Triangular src2738) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2738_2416 : (Triangular src2738) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2738_2464 : (Triangular src2738) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2738 : Cover (Triangular src2738) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2738_2390, by decide, by decide, pass2738_2391, by decide, by decide, pass2738_2393, by decide, by decide, pass2738_2399, by decide, by decide, pass2738_2416, by decide, by decide, pass2738_2464, rfl⟩
def src2739 : Request := ⟨⟨⟨1000,1395,307,6953⟩,30557599170560,105715278267⟩,16,3,1,385610,41⟩
private theorem pass2739_2390 : (Triangular src2739) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2739_2391 : (Triangular src2739) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2739_2393 : (Triangular src2739) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2739_2399 : (Triangular src2739) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2739_2415 : (Triangular src2739) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2739_2459 : (Triangular src2739) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2739 : Cover (Triangular src2739) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2739_2390, by decide, by decide, pass2739_2391, by decide, by decide, pass2739_2393, by decide, by decide, pass2739_2399, by decide, by decide, pass2739_2415, by decide, by decide, pass2739_2459, rfl⟩
def src2740 : Request := ⟨⟨⟨1450,2022,457,10612⟩,94890063298560,475487789910⟩,32,3,1,385610,41⟩
private theorem pass2740_2390 : (Triangular src2740) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2740_2391 : (Triangular src2740) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2740_2393 : (Triangular src2740) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2740_2399 : (Triangular src2740) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2740_2415 : (Triangular src2740) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2740_2458 : (Triangular src2740) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2740 : Cover (Triangular src2740) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2740_2390, by decide, by decide, pass2740_2391, by decide, by decide, pass2740_2393, by decide, by decide, pass2740_2399, by decide, by decide, pass2740_2415, by decide, by decide, pass2740_2458, rfl⟩
def src2741 : Request := ⟨⟨⟨2600,3626,798,19305⟩,535425056505856,4807957255301⟩,65,3,1,385610,41⟩
private theorem pass2741_2390 : (Triangular src2741) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2741_2391 : (Triangular src2741) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2741_2393 : (Triangular src2741) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2741_2398 : (Triangular src2741) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2741_2412 : (Triangular src2741) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2741_2448 : (Triangular src2741) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2741 : Cover (Triangular src2741) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass2741_2390, by decide, by decide, pass2741_2391, by decide, by decide, pass2741_2393, by decide, by decide, pass2741_2398, by decide, by decide, pass2741_2412, by decide, by decide, pass2741_2448, rfl⟩
def src2742 : Request := ⟨⟨⟨6900,9623,2174,50425⟩,10196763128627200,243058712908678⟩,190,3,1,385610,41⟩
private theorem pass2742_2390 : (Triangular src2742) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2742_2391 : (Triangular src2742) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2742_2393 : (Triangular src2742) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2742_2398 : (Triangular src2742) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2742_2411 : (Triangular src2742) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2742_2445 : (Triangular src2742) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2742_2532 : (Triangular src2742) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2742 : Cover (Triangular src2742) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2742_2390, by decide, by decide, pass2742_2391, by decide, by decide, pass2742_2393, by decide, by decide, pass2742_2398, by decide, by decide, pass2742_2411, by decide, by decide, pass2742_2445, by decide, by decide, pass2742_2532, rfl⟩
def src2743 : Request := ⟨⟨⟨556,772,170,6768⟩,5255817068544,9968090926⟩,10,3,2,385609,2⟩
private theorem pass2743_2390 : (Triangular src2743) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2743_2391 : (Triangular src2743) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2743_2394 : (Triangular src2743) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2743_2402 : (Triangular src2743) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2743_2426 : (Triangular src2743) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2743_2496 : (Triangular src2743) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2743 : Cover (Triangular src2743) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2743_2390, by decide, by decide, pass2743_2391, by decide, by decide, pass2743_2394, by decide, by decide, pass2743_2402, by decide, by decide, pass2743_2426, by decide, by decide, pass2743_2496, rfl⟩
def src2744 : Request := ⟨⟨⟨556,772,170,6682⟩,5255817068544,9968090926⟩,10,3,2,385609,3⟩
private theorem pass2744_2390 : (Triangular src2744) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2744_2391 : (Triangular src2744) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2744_2394 : (Triangular src2744) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2744_2402 : (Triangular src2744) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2744_2426 : (Triangular src2744) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2744_2496 : (Triangular src2744) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2744 : Cover (Triangular src2744) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2744_2390, by decide, by decide, pass2744_2391, by decide, by decide, pass2744_2394, by decide, by decide, pass2744_2402, by decide, by decide, pass2744_2426, by decide, by decide, pass2744_2496, rfl⟩
def src2745 : Request := ⟨⟨⟨556,772,170,6596⟩,5255817068544,9968090926⟩,10,3,2,385609,4⟩
private theorem pass2745_2390 : (Triangular src2745) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2745_2391 : (Triangular src2745) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2745_2393 : (Triangular src2745) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2745_2399 : (Triangular src2745) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2745_2417 : (Triangular src2745) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2745_2469 : (Triangular src2745) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2745 : Cover (Triangular src2745) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2745_2390, by decide, by decide, pass2745_2391, by decide, by decide, pass2745_2393, by decide, by decide, pass2745_2399, by decide, by decide, pass2745_2417, by decide, by decide, pass2745_2469, rfl⟩
def src2746 : Request := ⟨⟨⟨556,772,170,6511⟩,5255817068544,9968090926⟩,10,3,2,385609,5⟩
private theorem pass2746_2390 : (Triangular src2746) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2746_2391 : (Triangular src2746) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2746_2393 : (Triangular src2746) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2746_2399 : (Triangular src2746) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2746_2417 : (Triangular src2746) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2746_2469 : (Triangular src2746) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2746 : Cover (Triangular src2746) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2746_2390, by decide, by decide, pass2746_2391, by decide, by decide, pass2746_2393, by decide, by decide, pass2746_2399, by decide, by decide, pass2746_2417, by decide, by decide, pass2746_2469, rfl⟩
def src2747 : Request := ⟨⟨⟨556,772,170,6427⟩,5255817068544,9968090926⟩,10,3,2,385609,6⟩
private theorem pass2747_2390 : (Triangular src2747) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2747_2391 : (Triangular src2747) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2747_2393 : (Triangular src2747) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2747_2399 : (Triangular src2747) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2747_2417 : (Triangular src2747) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2747_2469 : (Triangular src2747) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2747 : Cover (Triangular src2747) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2747_2390, by decide, by decide, pass2747_2391, by decide, by decide, pass2747_2393, by decide, by decide, pass2747_2399, by decide, by decide, pass2747_2417, by decide, by decide, pass2747_2469, rfl⟩
def src2748 : Request := ⟨⟨⟨556,772,170,6343⟩,5255817068544,9968090926⟩,10,3,2,385609,7⟩
private theorem pass2748_2390 : (Triangular src2748) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2748_2391 : (Triangular src2748) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2748_2393 : (Triangular src2748) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2748_2399 : (Triangular src2748) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2748_2417 : (Triangular src2748) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2748_2469 : (Triangular src2748) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2748 : Cover (Triangular src2748) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2748_2390, by decide, by decide, pass2748_2391, by decide, by decide, pass2748_2393, by decide, by decide, pass2748_2399, by decide, by decide, pass2748_2417, by decide, by decide, pass2748_2469, rfl⟩
def src2749 : Request := ⟨⟨⟨556,772,170,6261⟩,5255817068544,9968090926⟩,10,3,2,385609,8⟩
private theorem pass2749_2390 : (Triangular src2749) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2749_2391 : (Triangular src2749) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2749_2394 : (Triangular src2749) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2749_2402 : (Triangular src2749) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2749_2426 : (Triangular src2749) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2749_2496 : (Triangular src2749) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2749 : Cover (Triangular src2749) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2749_2390, by decide, by decide, pass2749_2391, by decide, by decide, pass2749_2394, by decide, by decide, pass2749_2402, by decide, by decide, pass2749_2426, by decide, by decide, pass2749_2496, rfl⟩
def src2750 : Request := ⟨⟨⟨556,772,170,6178⟩,5255817068544,9968090926⟩,10,3,2,385609,9⟩
private theorem pass2750_2390 : (Triangular src2750) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2750_2391 : (Triangular src2750) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2750_2393 : (Triangular src2750) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2750_2399 : (Triangular src2750) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2750_2417 : (Triangular src2750) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2750_2469 : (Triangular src2750) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2750 : Cover (Triangular src2750) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2750_2390, by decide, by decide, pass2750_2391, by decide, by decide, pass2750_2393, by decide, by decide, pass2750_2399, by decide, by decide, pass2750_2417, by decide, by decide, pass2750_2469, rfl⟩
def src2751 : Request := ⟨⟨⟨556,772,170,6097⟩,5255817068544,9968090926⟩,10,3,2,385609,10⟩
private theorem pass2751_2390 : (Triangular src2751) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2751_2391 : (Triangular src2751) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2751_2393 : (Triangular src2751) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2751_2399 : (Triangular src2751) 2399 2416 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2751_2417 : (Triangular src2751) 2417 2468 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2751_2469 : (Triangular src2751) 2469 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2751 : Cover (Triangular src2751) 2534 2390 [2390,2392,2398,2416,2468,2534] := by
  exact ⟨by decide, by decide, pass2751_2390, by decide, by decide, pass2751_2391, by decide, by decide, pass2751_2393, by decide, by decide, pass2751_2399, by decide, by decide, pass2751_2417, by decide, by decide, pass2751_2469, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1831

end Merged_Z6969Pack0731

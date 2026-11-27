import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0733
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0731
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0725
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice
import ProximityPrize.SubmissionLower.Z6969Pack0726
import ProximityPrize.SubmissionLower.Z6969Pack0727
import ProximityPrize.SubmissionLower.Z6969Pack0728
import ProximityPrize.SubmissionLower.Z6969Pack0729
import ProximityPrize.SubmissionLower.Z6969Pack0730
import ProximityPrize.SubmissionLower.Z6969Pack0732

set_option Elab.async false

-- merged module Z6969Pack0734
section Merged_Z6969Pack0734

-- Source: Research6969.PrefixRescueDataMiddle104
section Z6969Source1856
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle104
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,8⟩
  bank i := ![bank245 57407, bank245 60527, bank245 64010, bank252 75137, bank270 88494, bank252 82923, bank270 103412, bank303 109676, bank315 130082, bank315 139688, bank332 164289] i
  reserve i := ![0, 1, 2, 4, 6, 6, 10, 10, 13, 16, 20] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 8

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 57407
    · exact rank245 60527
    · exact rank245 64010
    · exact rank252 75137
    · exact rank270 88494
    · exact rank252 82923
    · exact rank270 103412
    · exact rank303 109676
    · exact rank315 130082
    · exact rank315 139688
    · exact rank332 164289
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1936⟩
    · exact ⟨_, cover1937⟩
    · exact ⟨_, cover1938⟩
    · exact ⟨_, cover1939⟩
    · exact ⟨_, cover1941⟩
    · exact ⟨_, cover1940⟩
    · exact ⟨_, cover1942⟩
    · exact ⟨_, cover1943⟩
    · exact ⟨_, cover1944⟩
    · exact ⟨_, cover1945⟩
    · exact ⟨_, cover1946⟩

def price : EarlyPrice := ⟨2, 8, 10, 95/100, 80/100, ![512208743970, 80404637637, 4505119850, 563149735], 6406932729654260⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8143/21, 175849/21, 382162/21, 438104/7] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle104
end Z6969Source1856

-- Source: Research6969.PrefixMiddleSaved104
section Z6969Source1857
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved104
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle104.price Lower6960.Prefix6969RescueData.Middle104.price :=
  ⟨335, 4157, 387, 8373, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle104.plan Lower6960.Prefix6969RescueData.Middle104.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 8 8 :=
  ⟨Lower6960.Prefix6969MainCases.Middle104.plan, Lower6960.Prefix6969MainCases.Middle104.price, Lower6960.Prefix6969MainCases.Middle104.valid, Lower6960.Prefix6969MainCases.Middle104.priced, Lower6960.Prefix6969MainCases.Middle104.sources,
   Lower6960.Prefix6969RescueData.Middle104.plan, Lower6960.Prefix6969RescueData.Middle104.price, Lower6960.Prefix6969RescueData.Middle104.sources, Lower6960.Prefix6969RescueData.Middle104.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved104
end Z6969Source1857

-- Source: Research6969.PrefixMainDataMiddle105
section Z6969Source1858
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle105
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 20, 16, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank2 1121, bank8 1238, bank14 1349, bank23 1429, bank25 1577, bank32 1683, bank44 1848, bank53 2196, bank65 2772, bank73 3927, bank95 2576, bank137 3019, bank121 11999, bank152 5208, bank198 7884, bank183 20877, bank210 8954, bank174 26788, bank169 29097] i
  head := src2751
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14389, 127577, 598283, 2335739],
    ![23965/2, 423855/4, 959531/2, 3774043/2],
    ![17372/3, 51224, 464056, 1819801],
    ![3599, 124751/4, 2261618/9, 8712613/9],
    ![60148/25, 536358/25, 156123, 2486929/4],
    ![16211/9, 572669/36, 156123, 2486929/4],
    ![18775/16, 649495/64, 304304/3, 379456],
    ![86808/121, 763528/121, 3426860/49, 1912716/7],
    ![86808/121, 763528/121, 3426860/49, 1912716/7],
    ![77324/147, 345424/63, 757975/14, 488631/2],
    ![77324/147, 345424/63, 757975/14, 1963234/9],
    ![77324/147, 658899/121, 860415/16, 36813686/225],
    ![671521/1681, 658899/121, 860415/16, 36813686/225],
    ![671521/1681, 7760564/1681, 34836676/841, 127012704/841],
    ![671521/1681, 5631508/1323, 25330222/675, 6906384/49],
    ![954471/2738, 5631508/1323, 25330222/675, 6906384/49],
    ![954471/2738, 5651345/1369, 101736166/2809, 382147766/2809],
    ![462882/1369, 5651345/1369, 101736166/2809, 382147766/2809],
    ![459151/1369, 5651345/1369, 101736166/2809, 382147766/2809]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 9 257073 := by
  refine ⟨?_, rank154 6097, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2751⟩⟩
  · intro i; fin_cases i
    · exact free2_1
    · exact free8_1
    · exact free14_1
    · exact free23_1
    · exact free25_1
    · exact free32_1
    · exact free44_1
    · exact free53_1
    · exact free65_1
    · exact free73_1
    · exact free95_1
    · exact free137_1
    · exact free121_1
    · exact free152_1
    · exact free198_1
    · exact free183_1
    · exact free210_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [266239197, 348895978, 349103355, 349450810, 349584877, 349677924, 349559947, 159820211, 159389321, 159548261, 159570258, 80904054, 82992655, 92827701, 103561999, 103602567, 100000000, 100000000, 224185291], [1364518, 991364, 990795, 989841, 989473, 989218, 989542, 2406216, 2413388, 2410742, 2410376, 4933651, 4809496, 4277380, 3808450, 3806736, 3958949, 3958949, 1662245],
  ![119002036168620, 1618577386544, 201766761900, 4711149310], 148330606553903947⟩

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
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 5651345/1369, 101736166/2809, 382147766/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle105
end Z6969Source1858

-- Source: Research6969.PhysicalChecks122
section Z6969Source1859
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1952 : Request := ⟨⟨⟨2100,2930,622,71237⟩,274699477319680,1994139134137⟩,4,2,1,257073,9⟩
private theorem pass1952_2390 : (Triangular src1952) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1952_2391 : (Triangular src1952) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1952_2393 : (Triangular src1952) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1952_2399 : (Triangular src1952) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1952_2415 : (Triangular src1952) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1952_2457 : (Triangular src1952) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1952 : Cover (Triangular src1952) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass1952_2390, by decide, by decide, pass1952_2391, by decide, by decide, pass1952_2393, by decide, by decide, pass1952_2399, by decide, by decide, pass1952_2415, by decide, by decide, pass1952_2457, rfl⟩
def src1953 : Request := ⟨⟨⟨2600,3628,783,89093⟩,527755772952576,4745819470168⟩,8,2,1,257073,9⟩
private theorem pass1953_2390 : (Triangular src1953) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1953_2391 : (Triangular src1953) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1953_2393 : (Triangular src1953) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1953_2398 : (Triangular src1953) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1953_2412 : (Triangular src1953) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1953_2448 : (Triangular src1953) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1953 : Cover (Triangular src1953) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass1953_2390, by decide, by decide, pass1953_2391, by decide, by decide, pass1953_2393, by decide, by decide, pass1953_2398, by decide, by decide, pass1953_2412, by decide, by decide, pass1953_2448, rfl⟩
def src1954 : Request := ⟨⟨⟨3200,4465,947,104362⟩,970564165959680,10735676910569⟩,10,2,1,257073,9⟩
private theorem pass1954_2390 : (Triangular src1954) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1954_2391 : (Triangular src1954) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1954_2393 : (Triangular src1954) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1954_2398 : (Triangular src1954) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1954_2412 : (Triangular src1954) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1954_2449 : (Triangular src1954) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1954 : Cover (Triangular src1954) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1954_2390, by decide, by decide, pass1954_2391, by decide, by decide, pass1954_2393, by decide, by decide, pass1954_2398, by decide, by decide, pass1954_2412, by decide, by decide, pass1954_2449, rfl⟩
def src1955 : Request := ⟨⟨⟨3200,4465,963,112405⟩,983050615259136,10877088344236⟩,13,2,1,257073,9⟩
private theorem pass1955_2390 : (Triangular src1955) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1955_2391 : (Triangular src1955) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1955_2393 : (Triangular src1955) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1955_2398 : (Triangular src1955) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1955_2411 : (Triangular src1955) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1955_2445 : (Triangular src1955) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1955_2534 : (Triangular src1955) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1955 : Cover (Triangular src1955) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1955_2390, by decide, by decide, pass1955_2391, by decide, by decide, pass1955_2393, by decide, by decide, pass1955_2398, by decide, by decide, pass1955_2411, by decide, by decide, pass1955_2445, by decide, by decide, pass1955_2534, rfl⟩
def src1956 : Request := ⟨⟨⟨3200,4465,963,124459⟩,983050615259136,10877088344236⟩,16,2,1,257073,9⟩
private theorem pass1956_2390 : (Triangular src1956) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1956_2391 : (Triangular src1956) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1956_2393 : (Triangular src1956) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1956_2398 : (Triangular src1956) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1956_2411 : (Triangular src1956) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1956_2445 : (Triangular src1956) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1956_2534 : (Triangular src1956) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1956 : Cover (Triangular src1956) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1956_2390, by decide, by decide, pass1956_2391, by decide, by decide, pass1956_2393, by decide, by decide, pass1956_2398, by decide, by decide, pass1956_2411, by decide, by decide, pass1956_2445, by decide, by decide, pass1956_2534, rfl⟩
def src1957 : Request := ⟨⟨⟨4800,6698,1421,156282⟩,3274891856707584,54342858960622⟩,20,2,1,257073,9⟩
private theorem pass1957_2390 : (Triangular src1957) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1957_2391 : (Triangular src1957) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1957_2393 : (Triangular src1957) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1957_2398 : (Triangular src1957) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1957_2411 : (Triangular src1957) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1957_2446 : (Triangular src1957) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1957 : Cover (Triangular src1957) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1957_2390, by decide, by decide, pass1957_2391, by decide, by decide, pass1957_2393, by decide, by decide, pass1957_2398, by decide, by decide, pass1957_2411, by decide, by decide, pass1957_2446, rfl⟩
def src1958 : Request := ⟨⟨⟨1750,2442,527,49942⟩,161065121873920,975196209190⟩,0,2,1,257073,10⟩
private theorem pass1958_2390 : (Triangular src1958) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1958_2391 : (Triangular src1958) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1958_2393 : (Triangular src1958) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1958_2398 : (Triangular src1958) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1958_2412 : (Triangular src1958) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1958_2449 : (Triangular src1958) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1958 : Cover (Triangular src1958) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1958_2390, by decide, by decide, pass1958_2391, by decide, by decide, pass1958_2393, by decide, by decide, pass1958_2398, by decide, by decide, pass1958_2412, by decide, by decide, pass1958_2449, rfl⟩
def src1959 : Request := ⟨⟨⟨1750,2442,527,52629⟩,161065121873920,975196209190⟩,1,2,1,257073,10⟩
private theorem pass1959_2390 : (Triangular src1959) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1959_2391 : (Triangular src1959) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1959_2393 : (Triangular src1959) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1959_2398 : (Triangular src1959) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1959_2412 : (Triangular src1959) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1959_2449 : (Triangular src1959) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1959 : Cover (Triangular src1959) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1959_2390, by decide, by decide, pass1959_2391, by decide, by decide, pass1959_2393, by decide, by decide, pass1959_2398, by decide, by decide, pass1959_2412, by decide, by decide, pass1959_2449, rfl⟩
def src1960 : Request := ⟨⟨⟨1750,2442,527,55629⟩,161065121873920,975196209190⟩,2,2,1,257073,10⟩
private theorem pass1960_2390 : (Triangular src1960) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1960_2391 : (Triangular src1960) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1960_2393 : (Triangular src1960) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1960_2398 : (Triangular src1960) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1960_2412 : (Triangular src1960) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1960_2449 : (Triangular src1960) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1960 : Cover (Triangular src1960) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1960_2390, by decide, by decide, pass1960_2391, by decide, by decide, pass1960_2393, by decide, by decide, pass1960_2398, by decide, by decide, pass1960_2412, by decide, by decide, pass1960_2449, rfl⟩
def src1961 : Request := ⟨⟨⟨2100,2930,632,65328⟩,278060332482560,2019119590628⟩,4,2,1,257073,10⟩
private theorem pass1961_2390 : (Triangular src1961) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1961_2391 : (Triangular src1961) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1961_2393 : (Triangular src1961) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1961_2398 : (Triangular src1961) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1961_2412 : (Triangular src1961) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1961_2449 : (Triangular src1961) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1961 : Cover (Triangular src1961) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1961_2390, by decide, by decide, pass1961_2391, by decide, by decide, pass1961_2393, by decide, by decide, pass1961_2398, by decide, by decide, pass1961_2412, by decide, by decide, pass1961_2449, rfl⟩
def src1962 : Request := ⟨⟨⟨2100,2930,632,72035⟩,278060332482560,2019119590628⟩,6,2,1,257073,10⟩
private theorem pass1962_2390 : (Triangular src1962) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1962_2391 : (Triangular src1962) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1962_2393 : (Triangular src1962) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1962_2398 : (Triangular src1962) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1962_2412 : (Triangular src1962) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1962_2449 : (Triangular src1962) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1962 : Cover (Triangular src1962) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1962_2390, by decide, by decide, pass1962_2391, by decide, by decide, pass1962_2393, by decide, by decide, pass1962_2398, by decide, by decide, pass1962_2412, by decide, by decide, pass1962_2449, rfl⟩
def src1963 : Request := ⟨⟨⟨2600,3628,783,76968⟩,527755772952576,4745819470168⟩,6,2,1,257073,10⟩
private theorem pass1963_2390 : (Triangular src1963) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1963_2391 : (Triangular src1963) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1963_2393 : (Triangular src1963) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1963_2398 : (Triangular src1963) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1963_2412 : (Triangular src1963) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1963_2448 : (Triangular src1963) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1963 : Cover (Triangular src1963) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass1963_2390, by decide, by decide, pass1963_2391, by decide, by decide, pass1963_2393, by decide, by decide, pass1963_2398, by decide, by decide, pass1963_2412, by decide, by decide, pass1963_2448, rfl⟩
def src1964 : Request := ⟨⟨⟨3200,4465,963,95415⟩,983050615259136,10877088344236⟩,10,2,1,257073,10⟩
private theorem pass1964_2390 : (Triangular src1964) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1964_2391 : (Triangular src1964) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1964_2393 : (Triangular src1964) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1964_2398 : (Triangular src1964) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1964_2411 : (Triangular src1964) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1964_2445 : (Triangular src1964) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1964_2534 : (Triangular src1964) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1964 : Cover (Triangular src1964) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1964_2390, by decide, by decide, pass1964_2391, by decide, by decide, pass1964_2393, by decide, by decide, pass1964_2398, by decide, by decide, pass1964_2411, by decide, by decide, pass1964_2445, by decide, by decide, pass1964_2534, rfl⟩
def src1965 : Request := ⟨⟨⟨2600,3628,783,102741⟩,527755772952576,4745819470168⟩,13,2,1,257073,10⟩
private theorem pass1965_2390 : (Triangular src1965) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1965_2391 : (Triangular src1965) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1965_2393 : (Triangular src1965) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1965_2398 : (Triangular src1965) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1965_2411 : (Triangular src1965) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1965_2446 : (Triangular src1965) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1965 : Cover (Triangular src1965) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1965_2390, by decide, by decide, pass1965_2391, by decide, by decide, pass1965_2393, by decide, by decide, pass1965_2398, by decide, by decide, pass1965_2411, by decide, by decide, pass1965_2446, rfl⟩
def src1966 : Request := ⟨⟨⟨3950,5512,1189,113214⟩,1848744952463360,25255771038451⟩,13,2,1,257073,10⟩
private theorem pass1966_2390 : (Triangular src1966) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1966_2391 : (Triangular src1966) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1966_2393 : (Triangular src1966) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1966_2398 : (Triangular src1966) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1966_2411 : (Triangular src1966) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1966_2445 : (Triangular src1966) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1966_2534 : (Triangular src1966) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1966 : Cover (Triangular src1966) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1966_2390, by decide, by decide, pass1966_2391, by decide, by decide, pass1966_2393, by decide, by decide, pass1966_2398, by decide, by decide, pass1966_2411, by decide, by decide, pass1966_2445, by decide, by decide, pass1966_2534, rfl⟩
def src1967 : Request := ⟨⟨⟨3950,5512,1189,121491⟩,1848744952463360,25255771038451⟩,16,2,1,257073,10⟩
private theorem pass1967_2390 : (Triangular src1967) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1967_2391 : (Triangular src1967) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1967_2393 : (Triangular src1967) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1967_2398 : (Triangular src1967) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1967_2411 : (Triangular src1967) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1967_2445 : (Triangular src1967) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1967_2534 : (Triangular src1967) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1967 : Cover (Triangular src1967) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1967_2390, by decide, by decide, pass1967_2391, by decide, by decide, pass1967_2393, by decide, by decide, pass1967_2398, by decide, by decide, pass1967_2411, by decide, by decide, pass1967_2445, by decide, by decide, pass1967_2534, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1859

-- Source: Research6969.PrefixRescueDataMiddle105
section Z6969Source1860
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle105
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,9⟩
  bank i := ![bank236 49755, bank244 57422, bank252 64210, bank252 67071, bank251 71237, bank245 67554, bank270 89093, bank302 104362, bank303 112405, bank331 156282, bank303 124459] i
  reserve i := ![0, 1, 2, 3, 4, 4, 8, 10, 13, 20, 16] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 9

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 49755
    · exact rank244 57422
    · exact rank252 64210
    · exact rank252 67071
    · exact rank251 71237
    · exact rank245 67554
    · exact rank270 89093
    · exact rank302 104362
    · exact rank303 112405
    · exact rank331 156282
    · exact rank303 124459
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1947⟩
    · exact ⟨_, cover1948⟩
    · exact ⟨_, cover1949⟩
    · exact ⟨_, cover1950⟩
    · exact ⟨_, cover1952⟩
    · exact ⟨_, cover1951⟩
    · exact ⟨_, cover1953⟩
    · exact ⟨_, cover1954⟩
    · exact ⟨_, cover1955⟩
    · exact ⟨_, cover1957⟩
    · exact ⟨_, cover1956⟩

def price : EarlyPrice := ⟨2, 9, 10, 95/100, 80/100, ![548150675772, 79415482428, 4984080766, 553796383], 5215325995750808⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5428/17, 133126/17, 289103/17, 1120131/17] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle105
end Z6969Source1860

-- Source: Research6969.PrefixMiddleSaved105
section Z6969Source1861
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved105
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle105.price Lower6960.Prefix6969RescueData.Middle105.price :=
  ⟨335, 4128, 319, 7830, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle105.plan Lower6960.Prefix6969RescueData.Middle105.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 9 9 :=
  ⟨Lower6960.Prefix6969MainCases.Middle105.plan, Lower6960.Prefix6969MainCases.Middle105.price, Lower6960.Prefix6969MainCases.Middle105.valid, Lower6960.Prefix6969MainCases.Middle105.priced, Lower6960.Prefix6969MainCases.Middle105.sources,
   Lower6960.Prefix6969RescueData.Middle105.plan, Lower6960.Prefix6969RescueData.Middle105.price, Lower6960.Prefix6969RescueData.Middle105.sources, Lower6960.Prefix6969RescueData.Middle105.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved105
end Z6969Source1861

-- Source: Research6969.PrefixMainDataMiddle106
section Z6969Source1862
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle106
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 16, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank2 1121, bank8 1238, bank14 1349, bank23 1429, bank26 1570, bank32 1683, bank44 1848, bank54 2149, bank65 2772, bank84 3942, bank95 2576, bank137 3019, bank121 11999, bank152 5208, bank198 7884, bank183 20877, bank210 8954, bank174 26788, bank169 29097] i
  head := src2752
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14455, 127265, 597619, 2320779],
    ![23965/2, 105255, 476566, 1861952],
    ![17372/3, 50882, 464056, 1819801],
    ![3599, 247801/8, 2246228/9, 8596864/9],
    ![60658/25, 531604/25, 157785, 616225],
    ![16211/9, 284431/18, 157785, 616225],
    ![18775/16, 40315/4, 304304/3, 379456],
    ![89110/121, 756370/121, 489676/7, 1846912/7],
    ![89110/121, 756370/121, 489676/7, 1846912/7],
    ![63754/121, 1305879/242, 770661/16, 11857536/49],
    ![63754/121, 1305879/242, 770661/16, 1937152/9],
    ![63754/121, 1305879/242, 770661/16, 36324608/225],
    ![671521/1681, 1305879/242, 770661/16, 36324608/225],
    ![671521/1681, 7704512/1681, 34587520/841, 125325312/841],
    ![671521/1681, 5592304/1323, 25155424/675, 3513344/25],
    ![954471/2738, 5592304/1323, 25155424/675, 3513344/25],
    ![954471/2738, 5611655/1369, 101027416/2809, 377070848/2809],
    ![462882/1369, 5611655/1369, 101027416/2809, 377070848/2809],
    ![459151/1369, 5611655/1369, 101027416/2809, 377070848/2809]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 10 257073 := by
  refine ⟨?_, rank154 6016, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2752⟩⟩
  · intro i; fin_cases i
    · exact free2_1
    · exact free8_1
    · exact free14_1
    · exact free23_1
    · exact free26_1
    · exact free32_1
    · exact free44_1
    · exact free54_1
    · exact free65_1
    · exact free84_1
    · exact free95_1
    · exact free137_1
    · exact free121_1
    · exact free152_1
    · exact free198_1
    · exact free183_1
    · exact free210_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [265170040, 347719013, 347551230, 348141871, 346713063, 347778152, 346748249, 150245683, 150587662, 150705137, 150447865, 80817601, 81784538, 91984148, 104780319, 104820144, 100000000, 100000000, 223862999], [1369993, 994593, 995053, 993432, 997353, 994430, 997256, 2565577, 2559885, 2557930, 2562212, 4938790, 4881311, 4319964, 3763300, 3761916, 3958949, 3958949, 1664898],
  ![118830957129180, 1618927245076, 201476699100, 4711149310], 147371593101908862⟩

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
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5611655/1369, 101027416/2809, 377070848/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle106
end Z6969Source1862

-- Source: Research6969.PhysicalChecks123
section Z6969Source1863
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1968 : Request := ⟨⟨⟨4800,6698,1445,142930⟩,3317023033262080,55058665830093⟩,20,2,1,257073,10⟩
private theorem pass1968_2390 : (Triangular src1968) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1968_2391 : (Triangular src1968) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1968_2393 : (Triangular src1968) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1968_2398 : (Triangular src1968) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1968_2411 : (Triangular src1968) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1968_2445 : (Triangular src1968) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1968_2533 : (Triangular src1968) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1968 : Cover (Triangular src1968) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass1968_2390, by decide, by decide, pass1968_2391, by decide, by decide, pass1968_2393, by decide, by decide, pass1968_2398, by decide, by decide, pass1968_2411, by decide, by decide, pass1968_2445, by decide, by decide, pass1968_2533, rfl⟩
def src1969 : Request := ⟨⟨⟨1450,2023,436,42887⟩,91566841790464,459151377566⟩,0,2,1,257073,11⟩
private theorem pass1969_2390 : (Triangular src1969) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1969_2391 : (Triangular src1969) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1969_2393 : (Triangular src1969) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1969_2399 : (Triangular src1969) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1969_2415 : (Triangular src1969) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1969_2458 : (Triangular src1969) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1969 : Cover (Triangular src1969) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1969_2390, by decide, by decide, pass1969_2391, by decide, by decide, pass1969_2393, by decide, by decide, pass1969_2399, by decide, by decide, pass1969_2415, by decide, by decide, pass1969_2458, rfl⟩
def src1970 : Request := ⟨⟨⟨1750,2442,518,49883⟩,158964379549696,962176592398⟩,1,2,1,257073,11⟩
private theorem pass1970_2390 : (Triangular src1970) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1970_2391 : (Triangular src1970) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1970_2393 : (Triangular src1970) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1970_2399 : (Triangular src1970) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1970_2415 : (Triangular src1970) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1970_2458 : (Triangular src1970) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1970 : Cover (Triangular src1970) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1970_2390, by decide, by decide, pass1970_2391, by decide, by decide, pass1970_2393, by decide, by decide, pass1970_2399, by decide, by decide, pass1970_2415, by decide, by decide, pass1970_2458, rfl⟩
def src1971 : Request := ⟨⟨⟨1750,2442,518,55848⟩,158964379549696,962176592398⟩,3,2,1,257073,11⟩
private theorem pass1971_2390 : (Triangular src1971) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1971_2391 : (Triangular src1971) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1971_2393 : (Triangular src1971) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1971_2399 : (Triangular src1971) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1971_2415 : (Triangular src1971) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1971_2458 : (Triangular src1971) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1971 : Cover (Triangular src1971) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1971_2390, by decide, by decide, pass1971_2391, by decide, by decide, pass1971_2393, by decide, by decide, pass1971_2399, by decide, by decide, pass1971_2415, by decide, by decide, pass1971_2458, rfl⟩
def src1972 : Request := ⟨⟨⟨2100,2930,622,59126⟩,274699477319680,1994139134137⟩,3,2,1,257073,11⟩
private theorem pass1972_2390 : (Triangular src1972) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1972_2391 : (Triangular src1972) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1972_2393 : (Triangular src1972) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1972_2399 : (Triangular src1972) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1972_2415 : (Triangular src1972) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1972_2457 : (Triangular src1972) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1972 : Cover (Triangular src1972) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass1972_2390, by decide, by decide, pass1972_2391, by decide, by decide, pass1972_2393, by decide, by decide, pass1972_2399, by decide, by decide, pass1972_2415, by decide, by decide, pass1972_2457, rfl⟩
def src1973 : Request := ⟨⟨⟨1750,2442,527,58125⟩,161065121873920,975196209190⟩,4,2,1,257073,11⟩
private theorem pass1973_2390 : (Triangular src1973) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1973_2391 : (Triangular src1973) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1973_2393 : (Triangular src1973) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1973_2398 : (Triangular src1973) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1973_2412 : (Triangular src1973) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1973_2449 : (Triangular src1973) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1973 : Cover (Triangular src1973) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1973_2390, by decide, by decide, pass1973_2391, by decide, by decide, pass1973_2393, by decide, by decide, pass1973_2398, by decide, by decide, pass1973_2412, by decide, by decide, pass1973_2449, rfl⟩
def src1974 : Request := ⟨⟨⟨2600,3628,783,83146⟩,527755772952576,4745819470168⟩,10,2,1,257073,11⟩
private theorem pass1974_2390 : (Triangular src1974) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1974_2391 : (Triangular src1974) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1974_2393 : (Triangular src1974) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1974_2398 : (Triangular src1974) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1974_2412 : (Triangular src1974) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1974_2448 : (Triangular src1974) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1974 : Cover (Triangular src1974) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass1974_2390, by decide, by decide, pass1974_2391, by decide, by decide, pass1974_2393, by decide, by decide, pass1974_2398, by decide, by decide, pass1974_2412, by decide, by decide, pass1974_2448, rfl⟩
def src1975 : Request := ⟨⟨⟨3200,4465,963,88437⟩,983050615259136,10877088344236⟩,10,2,1,257073,11⟩
private theorem pass1975_2390 : (Triangular src1975) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1975_2391 : (Triangular src1975) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1975_2393 : (Triangular src1975) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1975_2398 : (Triangular src1975) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1975_2411 : (Triangular src1975) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1975_2445 : (Triangular src1975) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1975_2534 : (Triangular src1975) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1975 : Cover (Triangular src1975) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1975_2390, by decide, by decide, pass1975_2391, by decide, by decide, pass1975_2393, by decide, by decide, pass1975_2398, by decide, by decide, pass1975_2411, by decide, by decide, pass1975_2445, by decide, by decide, pass1975_2534, rfl⟩
def src1976 : Request := ⟨⟨⟨3200,4465,963,107134⟩,983050615259136,10877088344236⟩,16,2,1,257073,11⟩
private theorem pass1976_2390 : (Triangular src1976) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1976_2391 : (Triangular src1976) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1976_2393 : (Triangular src1976) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1976_2398 : (Triangular src1976) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1976_2411 : (Triangular src1976) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1976_2445 : (Triangular src1976) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1976_2534 : (Triangular src1976) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1976 : Cover (Triangular src1976) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1976_2390, by decide, by decide, pass1976_2391, by decide, by decide, pass1976_2393, by decide, by decide, pass1976_2398, by decide, by decide, pass1976_2411, by decide, by decide, pass1976_2445, by decide, by decide, pass1976_2534, rfl⟩
def src1977 : Request := ⟨⟨⟨3950,5512,1169,115485⟩,1824966114017280,24923274283249⟩,16,2,1,257073,11⟩
private theorem pass1977_2390 : (Triangular src1977) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1977_2391 : (Triangular src1977) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1977_2393 : (Triangular src1977) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1977_2398 : (Triangular src1977) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1977_2412 : (Triangular src1977) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1977_2448 : (Triangular src1977) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1977 : Cover (Triangular src1977) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass1977_2390, by decide, by decide, pass1977_2391, by decide, by decide, pass1977_2393, by decide, by decide, pass1977_2398, by decide, by decide, pass1977_2412, by decide, by decide, pass1977_2448, rfl⟩
def src1978 : Request := ⟨⟨⟨4800,6698,1421,135816⟩,3274891856707584,54342858960622⟩,20,2,1,257073,11⟩
private theorem pass1978_2390 : (Triangular src1978) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1978_2391 : (Triangular src1978) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1978_2393 : (Triangular src1978) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1978_2398 : (Triangular src1978) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1978_2411 : (Triangular src1978) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1978_2446 : (Triangular src1978) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1978 : Cover (Triangular src1978) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1978_2390, by decide, by decide, pass1978_2391, by decide, by decide, pass1978_2393, by decide, by decide, pass1978_2398, by decide, by decide, pass1978_2411, by decide, by decide, pass1978_2446, rfl⟩
def src1979 : Request := ⟨⟨⟨5700,7954,1716,155667⟩,5553838907981824,109473260530676⟩,25,2,1,257073,11⟩
private theorem pass1979_2390 : (Triangular src1979) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1979_2391 : (Triangular src1979) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1979_2393 : (Triangular src1979) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1979_2398 : (Triangular src1979) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1979_2411 : (Triangular src1979) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1979_2445 : (Triangular src1979) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1979_2533 : (Triangular src1979) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1979 : Cover (Triangular src1979) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass1979_2390, by decide, by decide, pass1979_2391, by decide, by decide, pass1979_2393, by decide, by decide, pass1979_2398, by decide, by decide, pass1979_2411, by decide, by decide, pass1979_2445, by decide, by decide, pass1979_2533, rfl⟩
def src1980 : Request := ⟨⟨⟨1750,2442,527,42716⟩,161065121873920,975196209190⟩,0,2,1,257073,12⟩
private theorem pass1980_2390 : (Triangular src1980) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1980_2391 : (Triangular src1980) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1980_2393 : (Triangular src1980) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1980_2398 : (Triangular src1980) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1980_2412 : (Triangular src1980) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1980_2449 : (Triangular src1980) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1980 : Cover (Triangular src1980) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1980_2390, by decide, by decide, pass1980_2391, by decide, by decide, pass1980_2393, by decide, by decide, pass1980_2398, by decide, by decide, pass1980_2412, by decide, by decide, pass1980_2449, rfl⟩
def src1981 : Request := ⟨⟨⟨1750,2442,527,44972⟩,161065121873920,975196209190⟩,1,2,1,257073,12⟩
private theorem pass1981_2390 : (Triangular src1981) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1981_2391 : (Triangular src1981) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1981_2393 : (Triangular src1981) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1981_2398 : (Triangular src1981) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1981_2412 : (Triangular src1981) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1981_2449 : (Triangular src1981) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1981 : Cover (Triangular src1981) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1981_2390, by decide, by decide, pass1981_2391, by decide, by decide, pass1981_2393, by decide, by decide, pass1981_2398, by decide, by decide, pass1981_2412, by decide, by decide, pass1981_2449, rfl⟩
def src1982 : Request := ⟨⟨⟨1750,2442,527,47490⟩,161065121873920,975196209190⟩,2,2,1,257073,12⟩
private theorem pass1982_2390 : (Triangular src1982) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1982_2391 : (Triangular src1982) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1982_2393 : (Triangular src1982) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1982_2398 : (Triangular src1982) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1982_2412 : (Triangular src1982) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1982_2449 : (Triangular src1982) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1982 : Cover (Triangular src1982) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1982_2390, by decide, by decide, pass1982_2391, by decide, by decide, pass1982_2393, by decide, by decide, pass1982_2398, by decide, by decide, pass1982_2412, by decide, by decide, pass1982_2449, rfl⟩
def src1983 : Request := ⟨⟨⟨1750,2442,527,50317⟩,161065121873920,975196209190⟩,3,2,1,257073,12⟩
private theorem pass1983_2390 : (Triangular src1983) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1983_2391 : (Triangular src1983) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1983_2393 : (Triangular src1983) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1983_2398 : (Triangular src1983) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1983_2412 : (Triangular src1983) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1983_2449 : (Triangular src1983) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1983 : Cover (Triangular src1983) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1983_2390, by decide, by decide, pass1983_2391, by decide, by decide, pass1983_2393, by decide, by decide, pass1983_2398, by decide, by decide, pass1983_2412, by decide, by decide, pass1983_2449, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1863

-- Source: Research6969.PrefixRescueDataMiddle106
section Z6969Source1864
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle106
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,10⟩
  bank i := ![bank245 49942, bank245 52629, bank245 55629, bank252 65328, bank270 76968, bank252 72035, bank303 95415, bank315 113214, bank315 121491, bank270 102741, bank332 142930] i
  reserve i := ![0, 1, 2, 4, 6, 6, 10, 13, 16, 13, 20] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 10

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 49942
    · exact rank245 52629
    · exact rank245 55629
    · exact rank252 65328
    · exact rank270 76968
    · exact rank252 72035
    · exact rank303 95415
    · exact rank315 113214
    · exact rank315 121491
    · exact rank270 102741
    · exact rank332 142930
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1958⟩
    · exact ⟨_, cover1959⟩
    · exact ⟨_, cover1960⟩
    · exact ⟨_, cover1961⟩
    · exact ⟨_, cover1963⟩
    · exact ⟨_, cover1962⟩
    · exact ⟨_, cover1964⟩
    · exact ⟨_, cover1966⟩
    · exact ⟨_, cover1967⟩
    · exact ⟨_, cover1965⟩
    · exact ⟨_, cover1968⟩

def price : EarlyPrice := ⟨2, 10, 10, 95/100, 80/100, ![557021221730, 76174895123, 5631397645, 563149735], 5663561166671970⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![4411/14, 52460/7, 352840/21, 1429300/21] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle106
end Z6969Source1864

-- Source: Research6969.PrefixMiddleSaved106
section Z6969Source1865
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved106
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle106.price Lower6960.Prefix6969RescueData.Middle106.price :=
  ⟨335, 4099, 315, 7494, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle106.plan Lower6960.Prefix6969RescueData.Middle106.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 10 10 :=
  ⟨Lower6960.Prefix6969MainCases.Middle106.plan, Lower6960.Prefix6969MainCases.Middle106.price, Lower6960.Prefix6969MainCases.Middle106.valid, Lower6960.Prefix6969MainCases.Middle106.priced, Lower6960.Prefix6969MainCases.Middle106.sources,
   Lower6960.Prefix6969RescueData.Middle106.plan, Lower6960.Prefix6969RescueData.Middle106.price, Lower6960.Prefix6969RescueData.Middle106.sources, Lower6960.Prefix6969RescueData.Middle106.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved106
end Z6969Source1865

-- Source: Research6969.PrefixMainDataMiddle107
section Z6969Source1866
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle107
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank61 2044, bank84 3942, bank85 2394, bank74 4330, bank113 3080, bank144 3940, bank150 5281, bank120 12477, bank198 7884, bank210 8954, bank183 20877, bank174 26788, bank169 29097] i
  head := src2753
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 128024, 595801, 2308251],
    ![12303, 104849, 473938, 1795640],
    ![53398/9, 455734/9, 464288, 1739761],
    ![29433/8, 61741/2, 2235472/9, 926016],
    ![16211/9, 282551/18, 643879/4, 624393],
    ![24292/27, 75662/9, 85951, 3198020/9],
    ![73478/121, 807084/121, 3640040/49, 2426976/7],
    ![73478/121, 807084/121, 3640040/49, 2864120/9],
    ![73478/121, 768936/121, 492544/7, 247616],
    ![63754/121, 1298919/242, 770661/16, 1671408/7],
    ![63754/121, 1298919/242, 770661/16, 28421568/121],
    ![61324/121, 1298919/242, 770661/16, 28421568/121],
    ![61324/121, 623252/121, 770661/16, 7313152/45],
    ![61324/121, 623252/121, 6989120/147, 155236],
    ![61324/121, 7603816/1681, 34234448/841, 125392064/841],
    ![667406/1681, 7603816/1681, 34234448/841, 125392064/841],
    ![667406/1681, 5553584/1323, 24982784/675, 3466624/25],
    ![667406/1681, 5572455/1369, 35816, 7019936/53],
    ![954471/2738, 5572455/1369, 35816, 7019936/53],
    ![462882/1369, 5572455/1369, 35816, 7019936/53],
    ![459151/1369, 5572455/1369, 35816, 7019936/53]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 11 257073 := by
  refine ⟨?_, rank154 5936, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2753⟩⟩
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
    · exact free144_1
    · exact free150_1
    · exact free120_1
    · exact free198_1
    · exact free210_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [264713546, 345737371, 346866748, 345292806, 345345864, 346411895, 345454338, 346601321, 167393660, 167913672, 168100202, 167868382, 115705130, 74375446, 67007639, 77178426, 105978186, 105482226, 127004852, 100000000, 223634310], [1372331, 1000029, 996931, 1001249, 1001104, 998179, 1000806, 997659, 2280160, 2271505, 2268401, 2272259, 3387241, 5384205, 6002230, 5186386, 3721672, 3738908, 3071024, 3958949, 1666780],
  ![118709564434200, 1619175233640, 201270879000, 5290113720], 146903218875648432⟩

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
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5572455/1369, 35816, 7019936/53] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle107
end Z6969Source1866

-- Source: Research6969.PrefixRescueDataMiddle107
section Z6969Source1867
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle107
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,11⟩
  bank i := ![bank236 42887, bank244 49883, bank251 59126, bank244 55848, bank245 58125, bank270 83146, bank303 88437, bank314 115485, bank331 135816, bank303 107134, bank347 155667] i
  reserve i := ![0, 1, 3, 3, 4, 10, 10, 16, 20, 16, 25] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 11

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 42887
    · exact rank244 49883
    · exact rank251 59126
    · exact rank244 55848
    · exact rank245 58125
    · exact rank270 83146
    · exact rank303 88437
    · exact rank314 115485
    · exact rank331 135816
    · exact rank303 107134
    · exact rank347 155667
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1969⟩
    · exact ⟨_, cover1970⟩
    · exact ⟨_, cover1972⟩
    · exact ⟨_, cover1971⟩
    · exact ⟨_, cover1973⟩
    · exact ⟨_, cover1974⟩
    · exact ⟨_, cover1975⟩
    · exact ⟨_, cover1977⟩
    · exact ⟨_, cover1978⟩
    · exact ⟨_, cover1976⟩
    · exact ⟨_, cover1979⟩

def price : EarlyPrice := ⟨2, 11, 10, 95/100, 80/100, ![667325281959, 87408548967, 7356280932, 668764668], 4739393698549449⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5428/17, 174543/26, 199414/13, 1712337/26] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle107
end Z6969Source1867

end Merged_Z6969Pack0734

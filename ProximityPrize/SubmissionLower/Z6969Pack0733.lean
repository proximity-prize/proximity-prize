import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0731
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0732
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0733
section Merged_Z6969Pack0733

-- Source: Research6969.PrefixMainDataMiddle101
section Z6969Source1844
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle101
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 21, 20, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank1 1128, bank8 1238, bank14 1349, bank23 1429, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank58 2054, bank73 3927, bank82 2422, bank74 4330, bank111 2977, bank140 3403, bank145 5985, bank120 12477, bank199 7608, bank210 8954, bank182 21248, bank174 26788, bank169 29097] i
  head := src2747
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![13949, 129130, 600432, 2445387],
    ![23965/2, 435405/4, 985601/2, 3978313/2],
    ![17372/3, 157852/3, 464056, 1819801],
    ![3599, 32054, 2324318/9, 9184183/9],
    ![16211/9, 588179/36, 2681081/16, 10816641/16],
    ![24292/27, 706981/81, 3212567/36, 13850185/36],
    ![73478/121, 833598/121, 3758371/49, 18394074/49],
    ![73478/121, 833598/121, 3758371/49, 6202055/18],
    ![73478/121, 799070/121, 3590912/49, 1054729/4],
    ![77324/147, 2472748/441, 5428915/98, 3605547/14],
    ![77324/147, 2472748/441, 5428915/98, 31132388/121],
    ![61324/121, 2472748/441, 11480062/225, 31132388/121],
    ![61324/121, 2438974/441, 11480062/225, 8862529/49],
    ![61324/121, 2438974/441, 11480062/225, 8862529/49],
    ![1640767/3362, 15938239/3362, 35706040/841, 8862529/49],
    ![667406/1681, 15938239/3362, 35706040/841, 8862529/49],
    ![667406/1681, 651610/147, 26387458/675, 73344924/529],
    ![667406/1681, 5813045/1369, 104623666/2809, 73344924/529],
    ![476343/1369, 5813045/1369, 104623666/2809, 73344924/529],
    ![462882/1369, 5813045/1369, 104623666/2809, 73344924/529],
    ![459151/1369, 5813045/1369, 104623666/2809, 73344924/529]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 5 257073 := by
  refine ⟨?_, rank154 6427, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2747⟩⟩
  · intro i; fin_cases i
    · exact free1_1
    · exact free8_1
    · exact free14_1
    · exact free23_1
    · exact free32_1
    · exact free41_1
    · exact free42_6
    · exact free48_1
    · exact free58_1
    · exact free73_1
    · exact free82_1
    · exact free74_5
    · exact free111_1
    · exact free140_1
    · exact free145_1
    · exact free120_1
    · exact free199_1
    · exact free210_1
    · exact free182_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [269459923, 356083778, 356387930, 356304246, 355800186, 356402962, 356114145, 354792226, 164460333, 164925175, 164956607, 164792818, 82129874, 80529768, 74108143, 77178426, 111143564, 111138776, 129929796, 100000000, 225498333], [1348023, 971643, 970809, 971038, 972421, 970768, 971560, 975187, 2328984, 2321247, 2320724, 2323450, 4860783, 4955900, 5405472, 5186386, 3542165, 3542331, 2993976, 3958949, 1651438],
  ![119699025123060, 1617152844732, 202948499700, 5290113720], 152432989860864517⟩

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
    · exact Pricing.height_from_critical Band.middle _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5813045/1369, 104623666/2809, 73344924/529] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle101
end Z6969Source1844

-- Source: Research6969.PrefixRescueDataMiddle101
section Z6969Source1845
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle101
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 9
  positive := by decide
  primeShape := ⟨0,2,1,5⟩
  bank i := ![bank236 63929, bank244 72978, bank251 86538, bank269 115018, bank303 144443, bank314 168880, bank303 160083, bank331 198523, bank347 231542] i
  reserve i := ![0, 1, 3, 8, 13, 16, 16, 20, 25] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 5

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 63929
    · exact rank244 72978
    · exact rank251 86538
    · exact rank269 115018
    · exact rank303 144443
    · exact rank314 168880
    · exact rank303 160083
    · exact rank331 198523
    · exact rank347 231542
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1905⟩
    · exact ⟨_, cover1906⟩
    · exact ⟨_, cover1907⟩
    · exact ⟨_, cover1908⟩
    · exact ⟨_, cover1909⟩
    · exact ⟨_, cover1911⟩
    · exact ⟨_, cover1910⟩
    · exact ⟨_, cover1912⟩
    · exact ⟨_, cover1913⟩

def price : EarlyPrice := ⟨2, 5, 8, 95/100, 80/100, ![451178804986, 102392503620, 3343768428, 668764668], 6825092491494990⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5428/17, 120061/13, 251427/13, 578855/13] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle101
end Z6969Source1845

-- Source: Research6969.PrefixMiddleSaved101
section Z6969Source1846
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved101
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle101.price Lower6960.Prefix6969RescueData.Middle101.price :=
  ⟨335, 4246, 319, 9235, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle101.plan Lower6960.Prefix6969RescueData.Middle101.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 5 5 :=
  ⟨Lower6960.Prefix6969MainCases.Middle101.plan, Lower6960.Prefix6969MainCases.Middle101.price, Lower6960.Prefix6969MainCases.Middle101.valid, Lower6960.Prefix6969MainCases.Middle101.priced, Lower6960.Prefix6969MainCases.Middle101.sources,
   Lower6960.Prefix6969RescueData.Middle101.plan, Lower6960.Prefix6969RescueData.Middle101.price, Lower6960.Prefix6969RescueData.Middle101.sources, Lower6960.Prefix6969RescueData.Middle101.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved101
end Z6969Source1846

-- Source: Research6969.PrefixMainDataMiddle102
section Z6969Source1847
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle102
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 19
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 14, 20, 14, 21, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank1 1128, bank8 1238, bank14 1349, bank23 1429, bank26 1570, bank38 1764, bank49 2130, bank62 2724, bank73 3927, bank82 2422, bank74 4330, bank116 3050, bank168 3916, bank148 5351, bank120 12477, bank199 7608, bank210 8954, bank182 21248, bank174 26788, bank169 29097] i
  head := src2748
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14197, 128911, 599143, 2410564],
    ![23965/2, 432465/4, 978965/2, 3926317/2],
    ![17372/3, 156788/3, 464056, 1819801],
    ![3599, 63667/2, 2308358/9, 9064147/9],
    ![60658/25, 545992/25, 157785, 4979255/8],
    ![69802/49, 623373/49, 2820698/25, 11189052/25],
    ![40539/50, 736337/100, 71355, 1134225/4],
    ![40539/50, 736337/100, 71355, 1134225/4],
    ![77324/147, 2458804/441, 5397583/98, 3558423/14],
    ![77324/147, 2458804/441, 5397583/98, 30725492/121],
    ![61324/121, 2458804/441, 11417398/225, 30725492/121],
    ![61324/121, 59392/11, 11356664/225, 1547692/9],
    ![61324/121, 59392/11, 11356664/225, 1693581/11],
    ![61324/121, 7850432/1681, 35324540/841, 1693581/11],
    ![667406/1681, 7850432/1681, 35324540/841, 1693581/11],
    ![667406/1681, 646850/147, 26196106/675, 72386316/529],
    ![667406/1681, 5771885/1369, 103888666/2809, 72386316/529],
    ![476343/1369, 5771885/1369, 103888666/2809, 72386316/529],
    ![462882/1369, 5771885/1369, 103888666/2809, 72386316/529],
    ![459151/1369, 5771885/1369, 103888666/2809, 72386316/529]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 6 257073 := by
  refine ⟨?_, rank154 6343, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2748⟩⟩
  · intro i; fin_cases i
    · exact free1_1
    · exact free8_1
    · exact free14_1
    · exact free23_1
    · exact free26_1
    · exact free38_1
    · exact free49_1
    · exact free62_1
    · exact free73_1
    · exact free82_1
    · exact free74_5
    · exact free116_3
    · exact free168_1
    · exact free148_1
    · exact free120_1
    · exact free199_1
    · exact free210_1
    · exact free182_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [269510303, 353033621, 354550622, 354276382, 355167953, 352599506, 160834122, 160834842, 161602193, 161438929, 161395733, 118291330, 75126879, 68734385, 74821605, 109791379, 109771412, 100000000, 100000000, 225164104], [1347765, 980012, 975850, 976602, 974156, 981203, 2389340, 2389328, 2376556, 2379273, 2379992, 3314867, 5328226, 5845578, 5349332, 3589156, 3589850, 3958949, 3958949, 1654189],
  ![119521609685280, 1617515522516, 202647693600, 5456318640], 151524458671951737⟩

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
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 5771885/1369, 103888666/2809, 72386316/529] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle102
end Z6969Source1847

-- Source: Research6969.PhysicalChecks120
section Z6969Source1848
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1920 : Request := ⟨⟨⟨2600,3628,770,108808⟩,521059839508480,4684185417862⟩,8,2,1,257073,6⟩
private theorem pass1920_2390 : (Triangular src1920) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1920_2391 : (Triangular src1920) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1920_2393 : (Triangular src1920) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1920_2398 : (Triangular src1920) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1920_2412 : (Triangular src1920) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1920_2449 : (Triangular src1920) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1920 : Cover (Triangular src1920) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1920_2390, by decide, by decide, pass1920_2391, by decide, by decide, pass1920_2393, by decide, by decide, pass1920_2398, by decide, by decide, pass1920_2412, by decide, by decide, pass1920_2449, rfl⟩
def src1921 : Request := ⟨⟨⟨3200,4465,963,124232⟩,983050615259136,10877088344236⟩,10,2,1,257073,6⟩
private theorem pass1921_2390 : (Triangular src1921) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1921_2391 : (Triangular src1921) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1921_2393 : (Triangular src1921) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1921_2398 : (Triangular src1921) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1921_2411 : (Triangular src1921) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1921_2445 : (Triangular src1921) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1921_2534 : (Triangular src1921) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1921 : Cover (Triangular src1921) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1921_2390, by decide, by decide, pass1921_2391, by decide, by decide, pass1921_2393, by decide, by decide, pass1921_2398, by decide, by decide, pass1921_2411, by decide, by decide, pass1921_2445, by decide, by decide, pass1921_2534, rfl⟩
def src1922 : Request := ⟨⟨⟨3950,5512,1189,147314⟩,1848744952463360,25255771038451⟩,13,2,1,257073,6⟩
private theorem pass1922_2390 : (Triangular src1922) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1922_2391 : (Triangular src1922) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1922_2393 : (Triangular src1922) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1922_2398 : (Triangular src1922) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1922_2411 : (Triangular src1922) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1922_2445 : (Triangular src1922) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1922_2534 : (Triangular src1922) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1922 : Cover (Triangular src1922) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1922_2390, by decide, by decide, pass1922_2391, by decide, by decide, pass1922_2393, by decide, by decide, pass1922_2398, by decide, by decide, pass1922_2411, by decide, by decide, pass1922_2445, by decide, by decide, pass1922_2534, rfl⟩
def src1923 : Request := ⟨⟨⟨3950,5512,1189,158250⟩,1848744952463360,25255771038451⟩,16,2,1,257073,6⟩
private theorem pass1923_2390 : (Triangular src1923) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1923_2391 : (Triangular src1923) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1923_2393 : (Triangular src1923) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1923_2398 : (Triangular src1923) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1923_2411 : (Triangular src1923) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1923_2445 : (Triangular src1923) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1923_2534 : (Triangular src1923) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1923 : Cover (Triangular src1923) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1923_2390, by decide, by decide, pass1923_2391, by decide, by decide, pass1923_2393, by decide, by decide, pass1923_2398, by decide, by decide, pass1923_2411, by decide, by decide, pass1923_2445, by decide, by decide, pass1923_2534, rfl⟩
def src1924 : Request := ⟨⟨⟨4800,6698,1445,186092⟩,3317023033262080,55058665830093⟩,20,2,1,257073,6⟩
private theorem pass1924_2390 : (Triangular src1924) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1924_2391 : (Triangular src1924) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1924_2393 : (Triangular src1924) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1924_2398 : (Triangular src1924) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1924_2411 : (Triangular src1924) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1924_2445 : (Triangular src1924) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1924_2533 : (Triangular src1924) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1924 : Cover (Triangular src1924) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass1924_2390, by decide, by decide, pass1924_2391, by decide, by decide, pass1924_2393, by decide, by decide, pass1924_2398, by decide, by decide, pass1924_2411, by decide, by decide, pass1924_2445, by decide, by decide, pass1924_2533, rfl⟩
def src1925 : Request := ⟨⟨⟨1450,2023,436,56786⟩,91566841790464,459151377566⟩,0,2,1,257073,7⟩
private theorem pass1925_2390 : (Triangular src1925) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1925_2391 : (Triangular src1925) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1925_2393 : (Triangular src1925) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1925_2399 : (Triangular src1925) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1925_2415 : (Triangular src1925) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1925_2458 : (Triangular src1925) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1925 : Cover (Triangular src1925) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1925_2390, by decide, by decide, pass1925_2391, by decide, by decide, pass1925_2393, by decide, by decide, pass1925_2399, by decide, by decide, pass1925_2415, by decide, by decide, pass1925_2458, rfl⟩
def src1926 : Request := ⟨⟨⟨1750,2442,518,65138⟩,158964379549696,962176592398⟩,1,2,1,257073,7⟩
private theorem pass1926_2390 : (Triangular src1926) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1926_2391 : (Triangular src1926) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1926_2393 : (Triangular src1926) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1926_2399 : (Triangular src1926) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1926_2415 : (Triangular src1926) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1926_2458 : (Triangular src1926) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1926 : Cover (Triangular src1926) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1926_2390, by decide, by decide, pass1926_2391, by decide, by decide, pass1926_2393, by decide, by decide, pass1926_2399, by decide, by decide, pass1926_2415, by decide, by decide, pass1926_2458, rfl⟩
def src1927 : Request := ⟨⟨⟨2100,2930,632,73233⟩,278060332482560,2019119590628⟩,2,2,1,257073,7⟩
private theorem pass1927_2390 : (Triangular src1927) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1927_2391 : (Triangular src1927) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1927_2393 : (Triangular src1927) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1927_2398 : (Triangular src1927) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1927_2412 : (Triangular src1927) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1927_2449 : (Triangular src1927) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1927 : Cover (Triangular src1927) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1927_2390, by decide, by decide, pass1927_2391, by decide, by decide, pass1927_2393, by decide, by decide, pass1927_2398, by decide, by decide, pass1927_2412, by decide, by decide, pass1927_2449, rfl⟩
def src1928 : Request := ⟨⟨⟨2100,2930,622,77230⟩,274699477319680,1994139134137⟩,3,2,1,257073,7⟩
private theorem pass1928_2390 : (Triangular src1928) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1928_2391 : (Triangular src1928) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1928_2393 : (Triangular src1928) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1928_2399 : (Triangular src1928) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1928_2415 : (Triangular src1928) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1928_2457 : (Triangular src1928) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1928 : Cover (Triangular src1928) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass1928_2390, by decide, by decide, pass1928_2391, by decide, by decide, pass1928_2393, by decide, by decide, pass1928_2399, by decide, by decide, pass1928_2415, by decide, by decide, pass1928_2457, rfl⟩
def src1929 : Request := ⟨⟨⟨1750,2442,527,77183⟩,161065121873920,975196209190⟩,4,2,1,257073,7⟩
private theorem pass1929_2390 : (Triangular src1929) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1929_2391 : (Triangular src1929) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1929_2393 : (Triangular src1929) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1929_2398 : (Triangular src1929) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1929_2412 : (Triangular src1929) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1929_2449 : (Triangular src1929) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1929 : Cover (Triangular src1929) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1929_2390, by decide, by decide, pass1929_2391, by decide, by decide, pass1929_2393, by decide, by decide, pass1929_2398, by decide, by decide, pass1929_2412, by decide, by decide, pass1929_2449, rfl⟩
def src1930 : Request := ⟨⟨⟨2100,2930,622,80845⟩,274699477319680,1994139134137⟩,4,2,1,257073,7⟩
private theorem pass1930_2390 : (Triangular src1930) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1930_2391 : (Triangular src1930) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1930_2393 : (Triangular src1930) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1930_2399 : (Triangular src1930) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1930_2415 : (Triangular src1930) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1930_2457 : (Triangular src1930) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1930 : Cover (Triangular src1930) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass1930_2390, by decide, by decide, pass1930_2391, by decide, by decide, pass1930_2393, by decide, by decide, pass1930_2399, by decide, by decide, pass1930_2415, by decide, by decide, pass1930_2457, rfl⟩
def src1931 : Request := ⟨⟨⟨2600,3628,783,101705⟩,527755772952576,4745819470168⟩,8,2,1,257073,7⟩
private theorem pass1931_2390 : (Triangular src1931) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1931_2391 : (Triangular src1931) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1931_2393 : (Triangular src1931) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1931_2398 : (Triangular src1931) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1931_2412 : (Triangular src1931) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1931_2448 : (Triangular src1931) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1931 : Cover (Triangular src1931) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass1931_2390, by decide, by decide, pass1931_2391, by decide, by decide, pass1931_2393, by decide, by decide, pass1931_2398, by decide, by decide, pass1931_2412, by decide, by decide, pass1931_2448, rfl⟩
def src1932 : Request := ⟨⟨⟨3200,4465,947,118354⟩,970564165959680,10735676910569⟩,10,2,1,257073,7⟩
private theorem pass1932_2390 : (Triangular src1932) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1932_2391 : (Triangular src1932) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1932_2393 : (Triangular src1932) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1932_2398 : (Triangular src1932) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1932_2412 : (Triangular src1932) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1932_2449 : (Triangular src1932) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1932 : Cover (Triangular src1932) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1932_2390, by decide, by decide, pass1932_2391, by decide, by decide, pass1932_2393, by decide, by decide, pass1932_2398, by decide, by decide, pass1932_2412, by decide, by decide, pass1932_2449, rfl⟩
def src1933 : Request := ⟨⟨⟨3200,4465,963,128301⟩,983050615259136,10877088344236⟩,13,2,1,257073,7⟩
private theorem pass1933_2390 : (Triangular src1933) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1933_2391 : (Triangular src1933) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1933_2393 : (Triangular src1933) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1933_2398 : (Triangular src1933) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1933_2411 : (Triangular src1933) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1933_2445 : (Triangular src1933) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1933_2534 : (Triangular src1933) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1933 : Cover (Triangular src1933) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1933_2390, by decide, by decide, pass1933_2391, by decide, by decide, pass1933_2393, by decide, by decide, pass1933_2398, by decide, by decide, pass1933_2411, by decide, by decide, pass1933_2445, by decide, by decide, pass1933_2534, rfl⟩
def src1934 : Request := ⟨⟨⟨4800,6698,1421,177233⟩,3274891856707584,54342858960622⟩,20,2,1,257073,7⟩
private theorem pass1934_2390 : (Triangular src1934) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1934_2391 : (Triangular src1934) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1934_2393 : (Triangular src1934) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1934_2398 : (Triangular src1934) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1934_2411 : (Triangular src1934) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1934_2446 : (Triangular src1934) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1934 : Cover (Triangular src1934) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1934_2390, by decide, by decide, pass1934_2391, by decide, by decide, pass1934_2393, by decide, by decide, pass1934_2398, by decide, by decide, pass1934_2411, by decide, by decide, pass1934_2446, rfl⟩
def src1935 : Request := ⟨⟨⟨5700,7954,1716,205746⟩,5553838907981824,109473260530676⟩,25,2,1,257073,7⟩
private theorem pass1935_2390 : (Triangular src1935) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1935_2391 : (Triangular src1935) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1935_2393 : (Triangular src1935) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1935_2398 : (Triangular src1935) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1935_2411 : (Triangular src1935) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1935_2445 : (Triangular src1935) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1935_2533 : (Triangular src1935) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1935 : Cover (Triangular src1935) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass1935_2390, by decide, by decide, pass1935_2391, by decide, by decide, pass1935_2393, by decide, by decide, pass1935_2398, by decide, by decide, pass1935_2411, by decide, by decide, pass1935_2445, by decide, by decide, pass1935_2533, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1848

-- Source: Research6969.PrefixRescueDataMiddle102
section Z6969Source1849
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle102
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,6⟩
  bank i := ![bank245 65035, bank245 68589, bank245 72556, bank252 85142, bank270 100262, bank252 94008, bank269 108808, bank303 124232, bank315 147314, bank315 158250, bank332 186092] i
  reserve i := ![0, 1, 2, 4, 6, 6, 8, 10, 13, 16, 20] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 6

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 65035
    · exact rank245 68589
    · exact rank245 72556
    · exact rank252 85142
    · exact rank270 100262
    · exact rank252 94008
    · exact rank269 108808
    · exact rank303 124232
    · exact rank315 147314
    · exact rank315 158250
    · exact rank332 186092
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1914⟩
    · exact ⟨_, cover1915⟩
    · exact ⟨_, cover1916⟩
    · exact ⟨_, cover1917⟩
    · exact ⟨_, cover1919⟩
    · exact ⟨_, cover1918⟩
    · exact ⟨_, cover1920⟩
    · exact ⟨_, cover1921⟩
    · exact ⟨_, cover1922⟩
    · exact ⟨_, cover1923⟩
    · exact ⟨_, cover1924⟩

def price : EarlyPrice := ⟨2, 6, 10, 95/100, 80/100, ![435138737508, 84807417163, 3378842055, 563149735], 7229515652847768⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8143/21, 194762/21, 412372/21, 372184/7] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle102
end Z6969Source1849

-- Source: Research6969.PrefixMiddleSaved102
section Z6969Source1850
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved102
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle102.price Lower6960.Prefix6969RescueData.Middle102.price :=
  ⟨335, 4216, 387, 9274, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle102.plan Lower6960.Prefix6969RescueData.Middle102.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 6 6 :=
  ⟨Lower6960.Prefix6969MainCases.Middle102.plan, Lower6960.Prefix6969MainCases.Middle102.price, Lower6960.Prefix6969MainCases.Middle102.valid, Lower6960.Prefix6969MainCases.Middle102.priced, Lower6960.Prefix6969MainCases.Middle102.sources,
   Lower6960.Prefix6969RescueData.Middle102.plan, Lower6960.Prefix6969RescueData.Middle102.price, Lower6960.Prefix6969RescueData.Middle102.sources, Lower6960.Prefix6969RescueData.Middle102.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved102
end Z6969Source1850

-- Source: Research6969.PrefixMainDataMiddle103
section Z6969Source1851
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle103
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 14, 14, 21, 20, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank1 1128, bank8 1238, bank14 1349, bank20 1460, bank25 1577, bank32 1683, bank44 1848, bank53 2196, bank62 2724, bank82 2422, bank84 3942, bank116 2935, bank121 11999, bank148 5351, bank210 8954, bank182 21248, bank174 26788, bank169 29097] i
  head := src2749
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14261, 128289, 598348, 2360527],
    ![23965/2, 429595/4, 972487/2, 3875559/2],
    ![17372/3, 467248/9, 464056, 1819801],
    ![28151/8, 504901/16, 2291666/9, 3047020/3],
    ![60148/25, 543574/25, 156123, 2486929/4],
    ![16211/9, 193459/12, 156123, 2486929/4],
    ![18775/16, 658515/64, 304304/3, 379456],
    ![86808/121, 774024/121, 3473436/49, 13749156/49],
    ![86808/121, 774024/121, 3473436/49, 13749156/49],
    ![86808/121, 774024/121, 3473436/49, 30328284/121],
    ![63754/121, 60327/11, 146434/3, 3884841/16],
    ![63754/121, 60327/11, 146434/3, 8614225/49],
    ![671521/1681, 60327/11, 146434/3, 8614225/49],
    ![671521/1681, 7795984/1681, 35081492/841, 134010444/841],
    ![671521/1681, 5731705/1369, 103171166/2809, 20043529/144],
    ![476343/1369, 5731705/1369, 103171166/2809, 20043529/144],
    ![462882/1369, 5731705/1369, 103171166/2809, 20043529/144],
    ![459151/1369, 5731705/1369, 103171166/2809, 20043529/144]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 7 257073 := by
  refine ⟨?_, rank154 6261, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2749⟩⟩
  · intro i; fin_cases i
    · exact free1_1
    · exact free8_1
    · exact free14_1
    · exact free20_1
    · exact free25_1
    · exact free32_1
    · exact free44_1
    · exact free53_1
    · exact free62_1
    · exact free82_1
    · exact free84_1
    · exact free116_2
    · exact free121_1
    · exact free148_1
    · exact free210_1
    · exact free182_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [268237259, 352287920, 352911962, 351854640, 351964230, 352168777, 353062695, 183370907, 183338996, 182881533, 182944097, 80010096, 77453226, 86690862, 109875656, 100000000, 164898703, 224837833], [1354285, 982057, 980345, 983246, 982946, 982384, 979932, 2073282, 2073668, 2079190, 2078435, 4990610, 5167387, 4589659, 3586227, 3958949, 2321687, 1656874],
  ![119348418513060, 1617869300252, 202354049700, 5461694210], 150672653303827627⟩

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
    · exact Pricing.height_from_critical Band.middle _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5731705/1369, 103171166/2809, 20043529/144] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle103
end Z6969Source1851

-- Source: Research6969.PrefixRescueDataMiddle103
section Z6969Source1852
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle103
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,7⟩
  bank i := ![bank236 56786, bank244 65138, bank252 73233, bank251 77230, bank251 80845, bank245 77183, bank270 101705, bank302 118354, bank303 128301, bank331 177233, bank347 205746] i
  reserve i := ![0, 1, 2, 3, 4, 4, 8, 10, 13, 20, 25] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 7

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 56786
    · exact rank244 65138
    · exact rank252 73233
    · exact rank251 77230
    · exact rank251 80845
    · exact rank245 77183
    · exact rank270 101705
    · exact rank302 118354
    · exact rank303 128301
    · exact rank331 177233
    · exact rank347 205746
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1925⟩
    · exact ⟨_, cover1926⟩
    · exact ⟨_, cover1927⟩
    · exact ⟨_, cover1928⟩
    · exact ⟨_, cover1930⟩
    · exact ⟨_, cover1929⟩
    · exact ⟨_, cover1931⟩
    · exact ⟨_, cover1932⟩
    · exact ⟨_, cover1933⟩
    · exact ⟨_, cover1934⟩
    · exact ⟨_, cover1935⟩

def price : EarlyPrice := ⟨2, 7, 10, 95/100, 80/100, ![561277968444, 97201299690, 4681272024, 668764668], 6080801546577028⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![4835/13, 108879/13, 233585/13, 720111/13] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle103
end Z6969Source1852

-- Source: Research6969.PrefixMiddleSaved103
section Z6969Source1853
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved103
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle103.price Lower6960.Prefix6969RescueData.Middle103.price :=
  ⟨335, 4186, 371, 8375, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle103.plan Lower6960.Prefix6969RescueData.Middle103.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 7 7 :=
  ⟨Lower6960.Prefix6969MainCases.Middle103.plan, Lower6960.Prefix6969MainCases.Middle103.price, Lower6960.Prefix6969MainCases.Middle103.valid, Lower6960.Prefix6969MainCases.Middle103.priced, Lower6960.Prefix6969MainCases.Middle103.sources,
   Lower6960.Prefix6969RescueData.Middle103.plan, Lower6960.Prefix6969RescueData.Middle103.price, Lower6960.Prefix6969RescueData.Middle103.sources, Lower6960.Prefix6969RescueData.Middle103.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved103
end Z6969Source1853

-- Source: Research6969.PrefixMainDataMiddle104
section Z6969Source1854
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle104
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 20, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank8 1238, bank14 1349, bank23 1429, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank61 2044, bank84 3942, bank85 2394, bank74 4330, bank115 2949, bank144 3940, bank148 5351, bank120 12477, bank198 7884, bank210 8954, bank183 20877, bank174 26788, bank169 29097] i
  head := src2750
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14337, 128594, 599709, 2365605],
    ![23965/2, 213345/2, 482965, 1912091],
    ![17372/3, 51566, 464056, 1819801],
    ![3599, 251203/8, 2277008/9, 8828362/9],
    ![16211/9, 144119/9, 1313773/8, 5198787/8],
    ![24292/27, 693784/81, 1576279/18, 6656795/18],
    ![73478/121, 820152/121, 3698362/49, 17681436/49],
    ![73478/121, 820152/121, 3698362/49, 2980885/9],
    ![73478/121, 786118/121, 503434/7, 1803976/7],
    ![63754/121, 1319973/242, 10917644/225, 3884841/16],
    ![63754/121, 1319973/242, 10917644/225, 3884841/16],
    ![61324/121, 1319973/242, 10917644/225, 3884841/16],
    ![61324/121, 1319973/242, 10917644/225, 8696601/49],
    ![61324/121, 795161/150, 10917644/225, 155236],
    ![61324/121, 7740872/1681, 34835480/841, 155236],
    ![667406/1681, 7740872/1681, 34835480/841, 155236],
    ![667406/1681, 5670712/1323, 5101004/135, 6906384/49],
    ![667406/1681, 5691035/1369, 102444916/2809, 387224684/2809],
    ![954471/2738, 5691035/1369, 102444916/2809, 387224684/2809],
    ![462882/1369, 5691035/1369, 102444916/2809, 387224684/2809],
    ![459151/1369, 5691035/1369, 102444916/2809, 387224684/2809]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 8 257073 := by
  refine ⟨?_, rank154 6178, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2750⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free8_1
    · exact free14_1
    · exact free23_1
    · exact free32_1
    · exact free41_1
    · exact free42_6
    · exact free48_1
    · exact free61_1
    · exact free84_1
    · exact free85_1
    · exact free74_5
    · exact free115_1
    · exact free144_1
    · exact free148_1
    · exact free120_1
    · exact free198_1
    · exact free210_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [267938104, 350761234, 351017448, 350307991, 350891832, 351604621, 351720504, 350261632, 168561101, 169026130, 169192221, 168579809, 117248868, 74694934, 74594654, 77178426, 108370948, 108371601, 128292244, 100000000, 224507583], [1355817, 986246, 985543, 987490, 985888, 983932, 983614, 987617, 2260729, 2252989, 2250225, 2260418, 3344040, 5358785, 5366764, 5186386, 3638519, 3638496, 3034997, 3958949, 1659593],
  ![119173115208060, 1618228058832, 202056824700, 5290113720], 149661526243136091⟩

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
    · exact Pricing.height_from_critical Band.middle _ 15 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 5691035/1369, 102444916/2809, 387224684/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle104
end Z6969Source1854

-- Source: Research6969.PhysicalChecks121
section Z6969Source1855
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1936 : Request := ⟨⟨⟨1750,2442,527,57407⟩,161065121873920,975196209190⟩,0,2,1,257073,8⟩
private theorem pass1936_2390 : (Triangular src1936) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1936_2391 : (Triangular src1936) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1936_2393 : (Triangular src1936) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1936_2398 : (Triangular src1936) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1936_2412 : (Triangular src1936) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1936_2449 : (Triangular src1936) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1936 : Cover (Triangular src1936) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1936_2390, by decide, by decide, pass1936_2391, by decide, by decide, pass1936_2393, by decide, by decide, pass1936_2398, by decide, by decide, pass1936_2412, by decide, by decide, pass1936_2449, rfl⟩
def src1937 : Request := ⟨⟨⟨1750,2442,527,60527⟩,161065121873920,975196209190⟩,1,2,1,257073,8⟩
private theorem pass1937_2390 : (Triangular src1937) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1937_2391 : (Triangular src1937) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1937_2393 : (Triangular src1937) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1937_2398 : (Triangular src1937) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1937_2412 : (Triangular src1937) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1937_2449 : (Triangular src1937) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1937 : Cover (Triangular src1937) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1937_2390, by decide, by decide, pass1937_2391, by decide, by decide, pass1937_2393, by decide, by decide, pass1937_2398, by decide, by decide, pass1937_2412, by decide, by decide, pass1937_2449, rfl⟩
def src1938 : Request := ⟨⟨⟨1750,2442,527,64010⟩,161065121873920,975196209190⟩,2,2,1,257073,8⟩
private theorem pass1938_2390 : (Triangular src1938) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1938_2391 : (Triangular src1938) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1938_2393 : (Triangular src1938) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1938_2398 : (Triangular src1938) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1938_2412 : (Triangular src1938) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1938_2449 : (Triangular src1938) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1938 : Cover (Triangular src1938) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1938_2390, by decide, by decide, pass1938_2391, by decide, by decide, pass1938_2393, by decide, by decide, pass1938_2398, by decide, by decide, pass1938_2412, by decide, by decide, pass1938_2449, rfl⟩
def src1939 : Request := ⟨⟨⟨2100,2930,632,75137⟩,278060332482560,2019119590628⟩,4,2,1,257073,8⟩
private theorem pass1939_2390 : (Triangular src1939) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1939_2391 : (Triangular src1939) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1939_2393 : (Triangular src1939) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1939_2398 : (Triangular src1939) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1939_2412 : (Triangular src1939) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1939_2449 : (Triangular src1939) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1939 : Cover (Triangular src1939) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1939_2390, by decide, by decide, pass1939_2391, by decide, by decide, pass1939_2393, by decide, by decide, pass1939_2398, by decide, by decide, pass1939_2412, by decide, by decide, pass1939_2449, rfl⟩
def src1940 : Request := ⟨⟨⟨2100,2930,632,82923⟩,278060332482560,2019119590628⟩,6,2,1,257073,8⟩
private theorem pass1940_2390 : (Triangular src1940) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1940_2391 : (Triangular src1940) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1940_2393 : (Triangular src1940) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1940_2398 : (Triangular src1940) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1940_2412 : (Triangular src1940) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1940_2449 : (Triangular src1940) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1940 : Cover (Triangular src1940) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1940_2390, by decide, by decide, pass1940_2391, by decide, by decide, pass1940_2393, by decide, by decide, pass1940_2398, by decide, by decide, pass1940_2412, by decide, by decide, pass1940_2449, rfl⟩
def src1941 : Request := ⟨⟨⟨2600,3628,783,88494⟩,527755772952576,4745819470168⟩,6,2,1,257073,8⟩
private theorem pass1941_2390 : (Triangular src1941) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1941_2391 : (Triangular src1941) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1941_2393 : (Triangular src1941) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1941_2398 : (Triangular src1941) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1941_2412 : (Triangular src1941) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1941_2448 : (Triangular src1941) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1941 : Cover (Triangular src1941) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass1941_2390, by decide, by decide, pass1941_2391, by decide, by decide, pass1941_2393, by decide, by decide, pass1941_2398, by decide, by decide, pass1941_2412, by decide, by decide, pass1941_2448, rfl⟩
def src1942 : Request := ⟨⟨⟨2600,3628,783,103412⟩,527755772952576,4745819470168⟩,10,2,1,257073,8⟩
private theorem pass1942_2390 : (Triangular src1942) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1942_2391 : (Triangular src1942) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1942_2393 : (Triangular src1942) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1942_2398 : (Triangular src1942) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1942_2411 : (Triangular src1942) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1942_2446 : (Triangular src1942) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1942 : Cover (Triangular src1942) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1942_2390, by decide, by decide, pass1942_2391, by decide, by decide, pass1942_2393, by decide, by decide, pass1942_2398, by decide, by decide, pass1942_2411, by decide, by decide, pass1942_2446, rfl⟩
def src1943 : Request := ⟨⟨⟨3200,4465,963,109676⟩,983050615259136,10877088344236⟩,10,2,1,257073,8⟩
private theorem pass1943_2390 : (Triangular src1943) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1943_2391 : (Triangular src1943) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1943_2393 : (Triangular src1943) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1943_2398 : (Triangular src1943) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1943_2411 : (Triangular src1943) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1943_2445 : (Triangular src1943) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1943_2534 : (Triangular src1943) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1943 : Cover (Triangular src1943) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1943_2390, by decide, by decide, pass1943_2391, by decide, by decide, pass1943_2393, by decide, by decide, pass1943_2398, by decide, by decide, pass1943_2411, by decide, by decide, pass1943_2445, by decide, by decide, pass1943_2534, rfl⟩
def src1944 : Request := ⟨⟨⟨3950,5512,1189,130082⟩,1848744952463360,25255771038451⟩,13,2,1,257073,8⟩
private theorem pass1944_2390 : (Triangular src1944) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1944_2391 : (Triangular src1944) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1944_2393 : (Triangular src1944) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1944_2398 : (Triangular src1944) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1944_2411 : (Triangular src1944) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1944_2445 : (Triangular src1944) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1944_2534 : (Triangular src1944) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1944 : Cover (Triangular src1944) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1944_2390, by decide, by decide, pass1944_2391, by decide, by decide, pass1944_2393, by decide, by decide, pass1944_2398, by decide, by decide, pass1944_2411, by decide, by decide, pass1944_2445, by decide, by decide, pass1944_2534, rfl⟩
def src1945 : Request := ⟨⟨⟨3950,5512,1189,139688⟩,1848744952463360,25255771038451⟩,16,2,1,257073,8⟩
private theorem pass1945_2390 : (Triangular src1945) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1945_2391 : (Triangular src1945) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1945_2393 : (Triangular src1945) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1945_2398 : (Triangular src1945) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1945_2411 : (Triangular src1945) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1945_2445 : (Triangular src1945) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1945_2534 : (Triangular src1945) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1945 : Cover (Triangular src1945) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1945_2390, by decide, by decide, pass1945_2391, by decide, by decide, pass1945_2393, by decide, by decide, pass1945_2398, by decide, by decide, pass1945_2411, by decide, by decide, pass1945_2445, by decide, by decide, pass1945_2534, rfl⟩
def src1946 : Request := ⟨⟨⟨4800,6698,1445,164289⟩,3317023033262080,55058665830093⟩,20,2,1,257073,8⟩
private theorem pass1946_2390 : (Triangular src1946) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1946_2391 : (Triangular src1946) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1946_2393 : (Triangular src1946) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1946_2398 : (Triangular src1946) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1946_2411 : (Triangular src1946) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1946_2445 : (Triangular src1946) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1946_2533 : (Triangular src1946) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1946 : Cover (Triangular src1946) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass1946_2390, by decide, by decide, pass1946_2391, by decide, by decide, pass1946_2393, by decide, by decide, pass1946_2398, by decide, by decide, pass1946_2411, by decide, by decide, pass1946_2445, by decide, by decide, pass1946_2533, rfl⟩
def src1947 : Request := ⟨⟨⟨1450,2023,436,49755⟩,91566841790464,459151377566⟩,0,2,1,257073,9⟩
private theorem pass1947_2390 : (Triangular src1947) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1947_2391 : (Triangular src1947) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1947_2393 : (Triangular src1947) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1947_2399 : (Triangular src1947) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1947_2415 : (Triangular src1947) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1947_2458 : (Triangular src1947) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1947 : Cover (Triangular src1947) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1947_2390, by decide, by decide, pass1947_2391, by decide, by decide, pass1947_2393, by decide, by decide, pass1947_2399, by decide, by decide, pass1947_2415, by decide, by decide, pass1947_2458, rfl⟩
def src1948 : Request := ⟨⟨⟨1750,2442,518,57422⟩,158964379549696,962176592398⟩,1,2,1,257073,9⟩
private theorem pass1948_2390 : (Triangular src1948) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1948_2391 : (Triangular src1948) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1948_2393 : (Triangular src1948) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1948_2399 : (Triangular src1948) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1948_2415 : (Triangular src1948) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1948_2458 : (Triangular src1948) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1948 : Cover (Triangular src1948) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1948_2390, by decide, by decide, pass1948_2391, by decide, by decide, pass1948_2393, by decide, by decide, pass1948_2399, by decide, by decide, pass1948_2415, by decide, by decide, pass1948_2458, rfl⟩
def src1949 : Request := ⟨⟨⟨2100,2930,632,64210⟩,278060332482560,2019119590628⟩,2,2,1,257073,9⟩
private theorem pass1949_2390 : (Triangular src1949) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1949_2391 : (Triangular src1949) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1949_2393 : (Triangular src1949) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1949_2398 : (Triangular src1949) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1949_2412 : (Triangular src1949) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1949_2449 : (Triangular src1949) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1949 : Cover (Triangular src1949) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1949_2390, by decide, by decide, pass1949_2391, by decide, by decide, pass1949_2393, by decide, by decide, pass1949_2398, by decide, by decide, pass1949_2412, by decide, by decide, pass1949_2449, rfl⟩
def src1950 : Request := ⟨⟨⟨2100,2930,632,67071⟩,278060332482560,2019119590628⟩,3,2,1,257073,9⟩
private theorem pass1950_2390 : (Triangular src1950) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1950_2391 : (Triangular src1950) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1950_2393 : (Triangular src1950) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1950_2398 : (Triangular src1950) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1950_2412 : (Triangular src1950) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1950_2449 : (Triangular src1950) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1950 : Cover (Triangular src1950) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1950_2390, by decide, by decide, pass1950_2391, by decide, by decide, pass1950_2393, by decide, by decide, pass1950_2398, by decide, by decide, pass1950_2412, by decide, by decide, pass1950_2449, rfl⟩
def src1951 : Request := ⟨⟨⟨1750,2442,527,67554⟩,161065121873920,975196209190⟩,4,2,1,257073,9⟩
private theorem pass1951_2390 : (Triangular src1951) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1951_2391 : (Triangular src1951) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1951_2393 : (Triangular src1951) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1951_2398 : (Triangular src1951) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1951_2412 : (Triangular src1951) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1951_2449 : (Triangular src1951) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1951 : Cover (Triangular src1951) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1951_2390, by decide, by decide, pass1951_2391, by decide, by decide, pass1951_2393, by decide, by decide, pass1951_2398, by decide, by decide, pass1951_2412, by decide, by decide, pass1951_2449, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1855

end Merged_Z6969Pack0733

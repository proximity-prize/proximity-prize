import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 5 257027 := by
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

def price : Pricing := ⟨55/100, 90/100, [269459923, 356083778, 356387930, 356304246, 355800186, 356402962, 356114145, 354792226, 164460333, 164925175, 164956607, 164792818, 82129874, 80529768, 74108143, 77178426, 111143564, 111138776, 129929796, 100000000, 225498333], [1348331, 971865, 971030, 971260, 972643, 970989, 971781, 975409, 2329514, 2321776, 2321252, 2323979, 4861890, 4957029, 5406704, 5187567, 3542972, 3543138, 2994658, 3959851, 1651814],
  ![119699025123060, 1617152844732, 202948499700, 5290113720], 152435626715222004⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,3,7,7,7,7,13,13,15,14,10,10,8,11,5] (by decide +kernel) i⟩
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
  physicalFloor := 257027
  seedFloor := 5

theorem sources : plan.Sources 2412 (Band.middle).last := by
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

def price : EarlyPrice := ⟨2, 5, 8, 95/100, 80/100, ![451178804986, 102392503620, 3343768428, 668764668], 6826580961391315⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 6 257027 := by
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

def price : Pricing := ⟨55/100, 90/100, [269510303, 353033621, 354550622, 354276382, 355167953, 352599506, 160834122, 160834842, 161602193, 161438929, 161395733, 118291330, 75126879, 68734385, 74821605, 109791379, 109771412, 100000000, 100000000, 225164104], [1348072, 980235, 976072, 976824, 974378, 981426, 2389884, 2389872, 2377097, 2379815, 2380534, 3315623, 5329440, 5846910, 5350551, 3589974, 3590668, 3959851, 3959851, 1654566],
  ![119521609685280, 1617515522516, 202647693600, 5456318640], 151527071912712548⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,7,7,7,7,7,9,14,16,14,10,10,11,11,5] (by decide +kernel) i⟩
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
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1920 : Request := ⟨⟨⟨2600,3628,770,108808⟩,521059839508480,4684185417862⟩,8,2,1,257027,6⟩
theorem cover1920 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1920) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1921 : Request := ⟨⟨⟨3200,4465,963,124232⟩,983050615259136,10877088344236⟩,10,2,1,257027,6⟩
theorem cover1921 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1921) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1922 : Request := ⟨⟨⟨3950,5512,1189,147314⟩,1848744952463360,25255771038451⟩,13,2,1,257027,6⟩
theorem cover1922 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1922) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1923 : Request := ⟨⟨⟨3950,5512,1189,158250⟩,1848744952463360,25255771038451⟩,16,2,1,257027,6⟩
theorem cover1923 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1923) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1924 : Request := ⟨⟨⟨4800,6698,1445,186092⟩,3317023033262080,55058665830093⟩,20,2,1,257027,6⟩
theorem cover1924 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1924) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src1925 : Request := ⟨⟨⟨1450,2023,436,56786⟩,91566841790464,459151377566⟩,0,2,1,257027,7⟩
theorem cover1925 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1925) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src1926 : Request := ⟨⟨⟨1750,2442,518,65138⟩,158964379549696,962176592398⟩,1,2,1,257027,7⟩
theorem cover1926 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1926) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src1927 : Request := ⟨⟨⟨2100,2930,632,73233⟩,278060332482560,2019119590628⟩,2,2,1,257027,7⟩
theorem cover1927 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1927) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1928 : Request := ⟨⟨⟨2100,2930,622,77230⟩,274699477319680,1994139134137⟩,3,2,1,257027,7⟩
theorem cover1928 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1928) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1929 : Request := ⟨⟨⟨1750,2442,527,77183⟩,161065121873920,975196209190⟩,4,2,1,257027,7⟩
theorem cover1929 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1929) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1930 : Request := ⟨⟨⟨2100,2930,622,80845⟩,274699477319680,1994139134137⟩,4,2,1,257027,7⟩
theorem cover1930 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1930) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1931 : Request := ⟨⟨⟨2600,3628,783,101705⟩,527755772952576,4745819470168⟩,8,2,1,257027,7⟩
theorem cover1931 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1931) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src1932 : Request := ⟨⟨⟨3200,4465,947,118354⟩,970564165959680,10735676910569⟩,10,2,1,257027,7⟩
theorem cover1932 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1932) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src1933 : Request := ⟨⟨⟨3200,4465,963,128301⟩,983050615259136,10877088344236⟩,13,2,1,257027,7⟩
theorem cover1933 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1933) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1934 : Request := ⟨⟨⟨4800,6698,1421,177233⟩,3274891856707584,54342858960622⟩,20,2,1,257027,7⟩
theorem cover1934 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1934) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src1935 : Request := ⟨⟨⟨5700,7954,1716,205746⟩,5553838907981824,109473260530676⟩,25,2,1,257027,7⟩
theorem cover1935 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1935) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
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
  physicalFloor := 257027
  seedFloor := 6

theorem sources : plan.Sources 2412 (Band.middle).last := by
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

def price : EarlyPrice := ⟨2, 6, 10, 95/100, 80/100, ![435138737508, 84807417163, 3378842055, 563149735], 7231092550608056⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 7 257027 := by
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

def price : Pricing := ⟨55/100, 90/100, [268237259, 352287920, 352911962, 351854640, 351964230, 352168777, 353062695, 183370907, 183338996, 182881533, 182944097, 80010096, 77453226, 86690862, 109875656, 100000000, 164898703, 224837833], [1354594, 982281, 980569, 983470, 983169, 982608, 980155, 2073755, 2074140, 2079664, 2078908, 4991747, 5168564, 4590704, 3587044, 3959851, 2322216, 1657252],
  ![119348418513060, 1617869300252, 202354049700, 5461694210], 150675252021519381⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,6,6,6,6,14,14,13,10,11,7,5] (by decide +kernel) i⟩
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
  physicalFloor := 257027
  seedFloor := 7

theorem sources : plan.Sources 2412 (Band.middle).last := by
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

def price : EarlyPrice := ⟨2, 7, 10, 95/100, 80/100, ![561277968444, 97201299690, 4681272024, 668764668], 6082125467713431⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 8 257027 := by
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

def price : Pricing := ⟨55/100, 90/100, [267938104, 350761234, 351017448, 350307991, 350891832, 351604621, 351720504, 350261632, 168561101, 169026130, 169192221, 168579809, 117248868, 74694934, 74594654, 77178426, 108370948, 108371601, 128292244, 100000000, 224507583], [1356126, 986471, 985768, 987714, 986112, 984156, 983838, 987842, 2261244, 2253502, 2250737, 2260933, 3344802, 5360006, 5367986, 5187567, 3639348, 3639325, 3035689, 3959851, 1659971],
  ![119173115208060, 1618228058832, 202056824700, 5290113720], 149664105883455544⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,3,7,7,7,7,9,15,15,14,10,10,9,11,5] (by decide +kernel) i⟩
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
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1936 : Request := ⟨⟨⟨1750,2442,527,57407⟩,161065121873920,975196209190⟩,0,2,1,257027,8⟩
theorem cover1936 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1936) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1937 : Request := ⟨⟨⟨1750,2442,527,60527⟩,161065121873920,975196209190⟩,1,2,1,257027,8⟩
theorem cover1937 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1937) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1938 : Request := ⟨⟨⟨1750,2442,527,64010⟩,161065121873920,975196209190⟩,2,2,1,257027,8⟩
theorem cover1938 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1938) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1939 : Request := ⟨⟨⟨2100,2930,632,75137⟩,278060332482560,2019119590628⟩,4,2,1,257027,8⟩
theorem cover1939 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1939) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1940 : Request := ⟨⟨⟨2100,2930,632,82923⟩,278060332482560,2019119590628⟩,6,2,1,257027,8⟩
theorem cover1940 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1940) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1941 : Request := ⟨⟨⟨2600,3628,783,88494⟩,527755772952576,4745819470168⟩,6,2,1,257027,8⟩
theorem cover1941 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1941) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src1942 : Request := ⟨⟨⟨2600,3628,783,103412⟩,527755772952576,4745819470168⟩,10,2,1,257027,8⟩
theorem cover1942 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1942) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src1943 : Request := ⟨⟨⟨3200,4465,963,109676⟩,983050615259136,10877088344236⟩,10,2,1,257027,8⟩
theorem cover1943 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1943) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1944 : Request := ⟨⟨⟨3950,5512,1189,130082⟩,1848744952463360,25255771038451⟩,13,2,1,257027,8⟩
theorem cover1944 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1944) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1945 : Request := ⟨⟨⟨3950,5512,1189,139688⟩,1848744952463360,25255771038451⟩,16,2,1,257027,8⟩
theorem cover1945 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1945) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1946 : Request := ⟨⟨⟨4800,6698,1445,164289⟩,3317023033262080,55058665830093⟩,20,2,1,257027,8⟩
theorem cover1946 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1946) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src1947 : Request := ⟨⟨⟨1450,2023,436,49755⟩,91566841790464,459151377566⟩,0,2,1,257027,9⟩
theorem cover1947 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1947) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src1948 : Request := ⟨⟨⟨1750,2442,518,57422⟩,158964379549696,962176592398⟩,1,2,1,257027,9⟩
theorem cover1948 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1948) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src1949 : Request := ⟨⟨⟨2100,2930,632,64210⟩,278060332482560,2019119590628⟩,2,2,1,257027,9⟩
theorem cover1949 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1949) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1950 : Request := ⟨⟨⟨2100,2930,632,67071⟩,278060332482560,2019119590628⟩,3,2,1,257027,9⟩
theorem cover1950 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1950) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1951 : Request := ⟨⟨⟨1750,2442,527,67554⟩,161065121873920,975196209190⟩,4,2,1,257027,9⟩
theorem cover1951 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1951) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1855

end Merged_Z6969Pack0733

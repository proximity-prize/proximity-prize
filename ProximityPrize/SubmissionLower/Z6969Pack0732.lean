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
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0732
section Merged_Z6969Pack0732

-- Source: Research6969.PrefixMainDataMiddle98
section Z6969Source1832
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle98
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 21, 20, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank1 1128, bank8 1238, bank14 1349, bank21 1459, bank30 1706, bank41 2155, bank42 2862, bank48 1930, bank58 2054, bank73 3927, bank82 2422, bank74 4330, bank111 2977, bank140 3403, bank145 5985, bank119 12995, bank198 7884, bank208 9103, bank181 21723, bank174 26788, bank169 29097] i
  head := src2744
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![13905, 129998, 603681, 2486593],
    ![23965/2, 222165/2, 502873, 2068079],
    ![17372/3, 53694, 464056, 1819801],
    ![7059/2, 65249/2, 2375882/9, 9749038/9],
    ![15956/9, 100679/6, 1356785/8, 2849873/4],
    ![24292/27, 720496/81, 1637011/18, 7199855/18],
    ![73478/121, 847368/121, 3819826/49, 19123884/49],
    ![73478/121, 847368/121, 3819826/49, 3224065/9],
    ![73478/121, 816920/121, 3670472/49, 1054729/4],
    ![77324/147, 2515078/441, 2762015/49, 1054729/4],
    ![77324/147, 2515078/441, 2762015/49, 1054729/4],
    ![61324/121, 2515078/441, 11670292/225, 1054729/4],
    ![61324/121, 356512/63, 11670292/225, 8862529/49],
    ![61324/121, 356512/63, 11670292/225, 8862529/49],
    ![1640767/3362, 16242199/3362, 36389440/841, 8862529/49],
    ![1330489/3362, 16242199/3362, 36389440/841, 8862529/49],
    ![1330489/3362, 5914648/1323, 1890408/49, 79021332/529],
    ![1330489/3362, 11824323/2738, 106677858/2809, 212891861/1458],
    ![474397/1369, 11824323/2738, 106677858/2809, 212891861/1458],
    ![462882/1369, 11824323/2738, 106677858/2809, 212891861/1458],
    ![459151/1369, 11824323/2738, 106677858/2809, 212891861/1458]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 2 257027 := by
  refine ⟨?_, rank154 6682, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2744⟩⟩
  · intro i; fin_cases i
    · exact free1_1
    · exact free8_1
    · exact free14_1
    · exact free21_1
    · exact free30_3
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
    · exact free119_1
    · exact free198_1
    · exact free208_1
    · exact free181_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [273797776, 361774598, 361252498, 362222808, 361525171, 362313791, 362219968, 360452931, 159996443, 160297803, 160575178, 160052944, 70418531, 83022269, 73845132, 77450754, 112601354, 112501521, 131501682, 100000000, 226394258], [1326110, 956248, 957681, 955018, 956932, 954768, 955026, 959875, 2403830, 2398813, 2394195, 2402889, 5700329, 4808830, 5427634, 5168735, 3492299, 3495770, 2960150, 3959851, 1644438],
  ![120174600031560, 1616180795752, 203754832200, 5270909160], 155962424893424735⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,3,7,7,7,7,15,13,15,14,10,10,8,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 11824323/2738, 106677858/2809, 212891861/1458] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle98
end Z6969Source1832

-- Source: Research6969.PhysicalChecks117
section Z6969Source1833
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1872 : Request := ⟨⟨⟨3950,5512,1189,205621⟩,1848744952463360,25255771038451⟩,16,2,1,257027,1⟩
theorem cover1872 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1872) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1873 : Request := ⟨⟨⟨1750,2442,518,80507⟩,158964379549696,962176592398⟩,0,2,1,257027,2⟩
theorem cover1873 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1873) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src1874 : Request := ⟨⟨⟨1750,2442,518,84897⟩,158964379549696,962176592398⟩,1,2,1,257027,2⟩
theorem cover1874 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1874) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src1875 : Request := ⟨⟨⟨1750,2442,518,89793⟩,158964379549696,962176592398⟩,2,2,1,257027,2⟩
theorem cover1875 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1875) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src1876 : Request := ⟨⟨⟨1750,2442,527,95498⟩,161065121873920,975196209190⟩,3,2,1,257027,2⟩
theorem cover1876 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1876) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1877 : Request := ⟨⟨⟨1750,2442,527,101769⟩,161065121873920,975196209190⟩,4,2,1,257027,2⟩
theorem cover1877 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1877) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1878 : Request := ⟨⟨⟨2100,2930,622,116384⟩,274699477319680,1994139134137⟩,6,2,1,257027,2⟩
theorem cover1878 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1878) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1879 : Request := ⟨⟨⟨2600,3628,783,133992⟩,527755772952576,4745819470168⟩,8,2,1,257027,2⟩
theorem cover1879 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1879) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src1880 : Request := ⟨⟨⟨3200,4465,947,154190⟩,970564165959680,10735676910569⟩,10,2,1,257027,2⟩
theorem cover1880 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1880) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src1881 : Request := ⟨⟨⟨3200,4465,963,168969⟩,983050615259136,10877088344236⟩,13,2,1,257027,2⟩
theorem cover1881 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1881) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1882 : Request := ⟨⟨⟨3950,5512,1169,196413⟩,1824966114017280,24923274283249⟩,16,2,1,257027,2⟩
theorem cover1882 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1882) 2557 2412 [2413, 2418, 2432, 2469, 2557] := triangleCover (by decide +kernel)
def src1883 : Request := ⟨⟨⟨4800,6698,1421,230893⟩,3274891856707584,54342858960622⟩,20,2,1,257027,2⟩
theorem cover1883 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1883) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src1884 : Request := ⟨⟨⟨1450,2023,436,71151⟩,91566841790464,459151377566⟩,0,2,1,257027,3⟩
theorem cover1884 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1884) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src1885 : Request := ⟨⟨⟨1450,2023,429,76671⟩,90444517867520,453391020534⟩,1,2,1,257027,3⟩
theorem cover1885 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1885) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src1886 : Request := ⟨⟨⟨1450,2023,436,82785⟩,91566841790464,459151377566⟩,2,2,1,257027,3⟩
theorem cover1886 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1886) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src1887 : Request := ⟨⟨⟨1750,2442,527,96810⟩,161065121873920,975196209190⟩,4,2,1,257027,3⟩
theorem cover1887 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1887) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1833

-- Source: Research6969.PrefixRescueDataMiddle98
section Z6969Source1834
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle98
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,2⟩
  bank i := ![bank244 80507, bank244 84897, bank244 89793, bank245 95498, bank245 101769, bank251 116384, bank270 133992, bank302 154190, bank303 168969, bank314 196413, bank331 230893] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 13, 16, 20] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 2

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank244 80507
    · exact rank244 84897
    · exact rank244 89793
    · exact rank245 95498
    · exact rank245 101769
    · exact rank251 116384
    · exact rank270 133992
    · exact rank302 154190
    · exact rank303 168969
    · exact rank314 196413
    · exact rank331 230893
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1873⟩
    · exact ⟨_, cover1874⟩
    · exact ⟨_, cover1875⟩
    · exact ⟨_, cover1876⟩
    · exact ⟨_, cover1877⟩
    · exact ⟨_, cover1878⟩
    · exact ⟨_, cover1879⟩
    · exact ⟨_, cover1880⟩
    · exact ⟨_, cover1881⟩
    · exact ⟨_, cover1882⟩
    · exact ⟨_, cover1883⟩

def price : EarlyPrice := ⟨2, 2, 10, 100/100, 80/100, ![179966316348, 94097396411, 1107578556, 553796383], 8981214967764077⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8119/21, 233735/21, 158394/7, 461786/21] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle98
end Z6969Source1834

-- Source: Research6969.PrefixMiddleSaved98
section Z6969Source1835
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved98
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle98.price Lower6960.Prefix6969RescueData.Middle98.price :=
  ⟨335, 4318, 386, 11130, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle98.plan Lower6960.Prefix6969RescueData.Middle98.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 2 2 :=
  ⟨Lower6960.Prefix6969MainCases.Middle98.plan, Lower6960.Prefix6969MainCases.Middle98.price, Lower6960.Prefix6969MainCases.Middle98.valid, Lower6960.Prefix6969MainCases.Middle98.priced, Lower6960.Prefix6969MainCases.Middle98.sources,
   Lower6960.Prefix6969RescueData.Middle98.plan, Lower6960.Prefix6969RescueData.Middle98.price, Lower6960.Prefix6969RescueData.Middle98.sources, Lower6960.Prefix6969RescueData.Middle98.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved98
end Z6969Source1835

-- Source: Research6969.PrefixMainDataMiddle99
section Z6969Source1836
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle99
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 21, 20, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank1 1128, bank8 1238, bank14 1349, bank21 1459, bank31 1686, bank41 2155, bank42 2862, bank48 1930, bank58 2054, bank73 3927, bank82 2422, bank74 4330, bank111 2977, bank140 3403, bank145 5985, bank119 12995, bank199 7608, bank209 9062, bank181 21723, bank174 26788, bank169 29097] i
  head := src2745
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![13920, 129662, 602773, 2472406],
    ![23965/2, 110330, 499476, 2041462],
    ![17372/3, 479978/9, 464056, 1819801],
    ![7059/2, 259233/8, 262200, 9623564/9],
    ![32167/18, 149158/9, 337493/2, 1390107/2],
    ![24292/27, 238646/27, 271108/3, 3553595/9],
    ![73478/121, 842724/121, 3799100/49, 18877752/49],
    ![73478/121, 842724/121, 3799100/49, 3182570/9],
    ![73478/121, 810900/121, 74360, 1054729/4],
    ![77324/147, 2500802/441, 2745976/49, 1054729/4],
    ![77324/147, 2500802/441, 2745976/49, 1054729/4],
    ![61324/121, 2500802/441, 3868712/75, 1054729/4],
    ![61324/121, 2476492/441, 3868712/75, 8862529/49],
    ![61324/121, 2476492/441, 3868712/75, 8862529/49],
    ![1640767/3362, 16139687/3362, 36158960/841, 8862529/49],
    ![1330489/3362, 16139687/3362, 36158960/841, 8862529/49],
    ![1330489/3362, 1983560/441, 5777008/147, 75273552/529],
    ![1330489/3362, 5881813/1369, 105716436/2809, 75273552/529],
    ![474397/1369, 5881813/1369, 105716436/2809, 75273552/529],
    ![462882/1369, 5881813/1369, 105716436/2809, 75273552/529],
    ![459151/1369, 5881813/1369, 105716436/2809, 75273552/529]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 3 257027 := by
  refine ⟨?_, rank154 6596, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2745⟩⟩
  · intro i; fin_cases i
    · exact free1_1
    · exact free8_1
    · exact free14_1
    · exact free21_1
    · exact free31_3
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
    · exact free119_1
    · exact free199_1
    · exact free209_1
    · exact free181_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [272344254, 358725311, 359813645, 359184664, 359711941, 359170423, 360245536, 358607008, 163842506, 164274426, 164256911, 164260305, 61731104, 82308138, 73521917, 77178426, 112154437, 112061691, 131014171, 100000000, 226013418], [1333555, 964616, 961629, 963355, 961908, 963394, 960444, 964940, 2339800, 2332609, 2332901, 2332844, 6528292, 4851291, 5453356, 5187567, 3507834, 3511058, 2970852, 3959851, 1647574],
  ![119972442542760, 1616594237892, 203412076200, 5290113720], 154654435949931558⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,3,7,7,7,7,18,13,15,14,10,10,8,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5881813/1369, 105716436/2809, 75273552/529] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle99
end Z6969Source1836

-- Source: Research6969.PhysicalChecks118
section Z6969Source1837
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1888 : Request := ⟨⟨⟨2100,2930,622,110901⟩,274699477319680,1994139134137⟩,6,2,1,257027,3⟩
theorem cover1888 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1888) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1889 : Request := ⟨⟨⟨2600,3628,770,127531⟩,521059839508480,4684185417862⟩,8,2,1,257027,3⟩
theorem cover1889 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1889) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1890 : Request := ⟨⟨⟨2600,3628,783,138308⟩,527755772952576,4745819470168⟩,10,2,1,257027,3⟩
theorem cover1890 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1890) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src1891 : Request := ⟨⟨⟨3200,4465,963,146435⟩,983050615259136,10877088344236⟩,10,2,1,257027,3⟩
theorem cover1891 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1891) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1892 : Request := ⟨⟨⟨3950,5512,1189,173616⟩,1848744952463360,25255771038451⟩,13,2,1,257027,3⟩
theorem cover1892 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1892) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1893 : Request := ⟨⟨⟨4800,6698,1421,220056⟩,3274891856707584,54342858960622⟩,20,2,1,257027,3⟩
theorem cover1893 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1893) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src1894 : Request := ⟨⟨⟨1750,2442,527,72776⟩,161065121873920,975196209190⟩,0,2,1,257027,4⟩
theorem cover1894 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1894) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1895 : Request := ⟨⟨⟨1750,2442,527,76764⟩,161065121873920,975196209190⟩,1,2,1,257027,4⟩
theorem cover1895 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1895) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1896 : Request := ⟨⟨⟨1750,2442,527,81214⟩,161065121873920,975196209190⟩,2,2,1,257027,4⟩
theorem cover1896 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1896) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1897 : Request := ⟨⟨⟨2100,2930,632,90984⟩,278060332482560,2019119590628⟩,3,2,1,257027,4⟩
theorem cover1897 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1897) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1898 : Request := ⟨⟨⟨2100,2930,632,95283⟩,278060332482560,2019119590628⟩,4,2,1,257027,4⟩
theorem cover1898 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1898) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1899 : Request := ⟨⟨⟨2600,3628,770,112503⟩,521059839508480,4684185417862⟩,6,2,1,257027,4⟩
theorem cover1899 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1899) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1900 : Request := ⟨⟨⟨2600,3628,783,120981⟩,527755772952576,4745819470168⟩,8,2,1,257027,4⟩
theorem cover1900 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1900) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src1901 : Request := ⟨⟨⟨3200,4465,947,139746⟩,970564165959680,10735676910569⟩,10,2,1,257027,4⟩
theorem cover1901 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1901) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src1902 : Request := ⟨⟨⟨2600,3628,783,150429⟩,527755772952576,4745819470168⟩,13,2,1,257027,4⟩
theorem cover1902 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1902) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src1903 : Request := ⟨⟨⟨3950,5512,1169,165716⟩,1824966114017280,24923274283249⟩,13,2,1,257027,4⟩
theorem cover1903 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1903) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1837

-- Source: Research6969.PrefixRescueDataMiddle99
section Z6969Source1838
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle99
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,3⟩
  bank i := ![bank236 71151, bank235 76671, bank236 82785, bank245 96810, bank251 110901, bank270 138308, bank269 127531, bank251 110901, bank303 146435, bank315 173616, bank331 220056] i
  reserve i := ![0, 1, 2, 4, 6, 10, 8, 6, 10, 13, 20] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 3

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 71151
    · exact rank235 76671
    · exact rank236 82785
    · exact rank245 96810
    · exact rank251 110901
    · exact rank270 138308
    · exact rank269 127531
    · exact rank251 110901
    · exact rank303 146435
    · exact rank315 173616
    · exact rank331 220056
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1884⟩
    · exact ⟨_, cover1885⟩
    · exact ⟨_, cover1886⟩
    · exact ⟨_, cover1887⟩
    · exact ⟨_, cover1888⟩
    · exact ⟨_, cover1890⟩
    · exact ⟨_, cover1889⟩
    · exact ⟨_, cover1888⟩
    · exact ⟨_, cover1891⟩
    · exact ⟨_, cover1892⟩
    · exact ⟨_, cover1893⟩

def price : EarlyPrice := ⟨2, 3, 10, 100/100, 90/100, ![257278912512, 91930499592, 1661364992, 553796383], 7487711967405886⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8119/21, 74773/7, 153402/7, 220056/7] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle99
end Z6969Source1838

-- Source: Research6969.PrefixMiddleSaved99
section Z6969Source1839
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved99
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle99.price Lower6960.Prefix6969RescueData.Middle99.price :=
  ⟨335, 4296, 386, 10681, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle99.plan Lower6960.Prefix6969RescueData.Middle99.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 3 3 :=
  ⟨Lower6960.Prefix6969MainCases.Middle99.plan, Lower6960.Prefix6969MainCases.Middle99.price, Lower6960.Prefix6969MainCases.Middle99.valid, Lower6960.Prefix6969MainCases.Middle99.priced, Lower6960.Prefix6969MainCases.Middle99.sources,
   Lower6960.Prefix6969RescueData.Middle99.plan, Lower6960.Prefix6969RescueData.Middle99.price, Lower6960.Prefix6969RescueData.Middle99.sources, Lower6960.Prefix6969RescueData.Middle99.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved99
end Z6969Source1839

-- Source: Research6969.PrefixMainDataMiddle100
section Z6969Source1840
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle100
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 21, 20, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank1 1128, bank8 1238, bank14 1349, bank22 1443, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank58 2054, bank73 3927, bank82 2422, bank74 4330, bank111 2977, bank140 3403, bank145 5985, bank120 12477, bank199 7608, bank210 8954, bank181 21723, bank174 26788, bank169 29097] i
  head := src2746
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![13938, 129425, 601400, 2458315],
    ![23965/2, 438345/4, 992237/2, 4030309/2],
    ![17372/3, 52972, 464056, 1819801],
    ![28537/8, 129693/4, 2331553/9, 3131791/3],
    ![16211/9, 592127/36, 2699141/16, 10958013/16],
    ![24292/27, 711433/81, 3232811/36, 14031205/36],
    ![73478/121, 76194/11, 3778615/49, 18634482/49],
    ![73478/121, 76194/11, 3778615/49, 6283115/18],
    ![73478/121, 804950/121, 3617120/49, 1054729/4],
    ![77324/147, 2486692/441, 5460247/98, 3652671/14],
    ![77324/147, 2486692/441, 5460247/98, 31539284/121],
    ![61324/121, 2486692/441, 11542726/225, 31539284/121],
    ![61324/121, 2457622/441, 11542726/225, 8862529/49],
    ![61324/121, 2457622/441, 11542726/225, 8862529/49],
    ![1640767/3362, 16038367/3362, 35931160/841, 8862529/49],
    ![667406/1681, 16038367/3362, 35931160/841, 8862529/49],
    ![667406/1681, 218790/49, 5777008/147, 74303532/529],
    ![667406/1681, 5854205/1369, 105358666/2809, 204048229/1458],
    ![474397/1369, 5854205/1369, 105358666/2809, 204048229/1458],
    ![462882/1369, 5854205/1369, 105358666/2809, 204048229/1458],
    ![459151/1369, 5854205/1369, 105358666/2809, 204048229/1458]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 4 257027 := by
  refine ⟨?_, rank154 6511, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2746⟩⟩
  · intro i; fin_cases i
    · exact free1_1
    · exact free8_1
    · exact free14_1
    · exact free22_1
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
    · exact free181_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [270902168, 355676025, 357955892, 356172665, 356029029, 357939930, 356287998, 357713066, 166117348, 166446147, 166492495, 166390769, 70820441, 81594007, 70549171, 77178426, 110921019, 110957263, 130482600, 100000000, 225832562], [1340943, 972984, 966727, 971621, 972015, 966771, 971304, 967393, 2301928, 2296454, 2295683, 2297376, 5668345, 4893751, 5689933, 5187567, 3550708, 3549448, 2982522, 3959851, 1649063],
  ![119876440560840, 1616790166948, 203249305800, 5290113720], 153416745108552887⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,3,7,7,7,7,15,13,15,14,10,10,8,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5854205/1369, 105358666/2809, 204048229/1458] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle100
end Z6969Source1840

-- Source: Research6969.PhysicalChecks119
section Z6969Source1841
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1904 : Request := ⟨⟨⟨4800,6698,1445,208204⟩,3317023033262080,55058665830093⟩,20,2,1,257027,4⟩
theorem cover1904 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1904) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src1905 : Request := ⟨⟨⟨1450,2023,436,63929⟩,91566841790464,459151377566⟩,0,2,1,257027,5⟩
theorem cover1905 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1905) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src1906 : Request := ⟨⟨⟨1750,2442,518,72978⟩,158964379549696,962176592398⟩,1,2,1,257027,5⟩
theorem cover1906 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1906) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src1907 : Request := ⟨⟨⟨2100,2930,622,86538⟩,274699477319680,1994139134137⟩,3,2,1,257027,5⟩
theorem cover1907 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1907) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1908 : Request := ⟨⟨⟨2600,3628,770,115018⟩,521059839508480,4684185417862⟩,8,2,1,257027,5⟩
theorem cover1908 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1908) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1909 : Request := ⟨⟨⟨3200,4465,963,144443⟩,983050615259136,10877088344236⟩,13,2,1,257027,5⟩
theorem cover1909 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1909) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1910 : Request := ⟨⟨⟨3200,4465,963,160083⟩,983050615259136,10877088344236⟩,16,2,1,257027,5⟩
theorem cover1910 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1910) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1911 : Request := ⟨⟨⟨3950,5512,1169,168880⟩,1824966114017280,24923274283249⟩,16,2,1,257027,5⟩
theorem cover1911 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1911) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src1912 : Request := ⟨⟨⟨4800,6698,1421,198523⟩,3274891856707584,54342858960622⟩,20,2,1,257027,5⟩
theorem cover1912 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1912) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src1913 : Request := ⟨⟨⟨5700,7954,1716,231542⟩,5553838907981824,109473260530676⟩,25,2,1,257027,5⟩
theorem cover1913 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1913) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src1914 : Request := ⟨⟨⟨1750,2442,527,65035⟩,161065121873920,975196209190⟩,0,2,1,257027,6⟩
theorem cover1914 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1914) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1915 : Request := ⟨⟨⟨1750,2442,527,68589⟩,161065121873920,975196209190⟩,1,2,1,257027,6⟩
theorem cover1915 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1915) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1916 : Request := ⟨⟨⟨1750,2442,527,72556⟩,161065121873920,975196209190⟩,2,2,1,257027,6⟩
theorem cover1916 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1916) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1917 : Request := ⟨⟨⟨2100,2930,632,85142⟩,278060332482560,2019119590628⟩,4,2,1,257027,6⟩
theorem cover1917 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1917) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1918 : Request := ⟨⟨⟨2100,2930,632,94008⟩,278060332482560,2019119590628⟩,6,2,1,257027,6⟩
theorem cover1918 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1918) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1919 : Request := ⟨⟨⟨2600,3628,783,100262⟩,527755772952576,4745819470168⟩,6,2,1,257027,6⟩
theorem cover1919 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1919) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1841

-- Source: Research6969.PrefixRescueDataMiddle100
section Z6969Source1842
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle100
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,4⟩
  bank i := ![bank245 72776, bank245 76764, bank245 81214, bank252 90984, bank252 95283, bank269 112503, bank270 120981, bank302 139746, bank314 165716, bank332 208204, bank270 150429] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 13, 20, 13] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 4

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 72776
    · exact rank245 76764
    · exact rank245 81214
    · exact rank252 90984
    · exact rank252 95283
    · exact rank269 112503
    · exact rank270 120981
    · exact rank302 139746
    · exact rank314 165716
    · exact rank332 208204
    · exact rank270 150429
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1894⟩
    · exact ⟨_, cover1895⟩
    · exact ⟨_, cover1896⟩
    · exact ⟨_, cover1897⟩
    · exact ⟨_, cover1898⟩
    · exact ⟨_, cover1899⟩
    · exact ⟨_, cover1900⟩
    · exact ⟨_, cover1901⟩
    · exact ⟨_, cover1903⟩
    · exact ⟨_, cover1904⟩
    · exact ⟨_, cover1902⟩

def price : EarlyPrice := ⟨2, 4, 10, 95/100, 80/100, ![324562344868, 89330615843, 2918541271, 563149735], 8120420160790834⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![4411/14, 71328/7, 443200/21, 832816/21] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle100
end Z6969Source1842

-- Source: Research6969.PrefixMiddleSaved100
section Z6969Source1843
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved100
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle100.price Lower6960.Prefix6969RescueData.Middle100.price :=
  ⟨335, 4276, 315, 10189, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle100.plan Lower6960.Prefix6969RescueData.Middle100.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 4 4 :=
  ⟨Lower6960.Prefix6969MainCases.Middle100.plan, Lower6960.Prefix6969MainCases.Middle100.price, Lower6960.Prefix6969MainCases.Middle100.valid, Lower6960.Prefix6969MainCases.Middle100.priced, Lower6960.Prefix6969MainCases.Middle100.sources,
   Lower6960.Prefix6969RescueData.Middle100.plan, Lower6960.Prefix6969RescueData.Middle100.price, Lower6960.Prefix6969RescueData.Middle100.sources, Lower6960.Prefix6969RescueData.Middle100.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved100
end Z6969Source1843

end Merged_Z6969Pack0732

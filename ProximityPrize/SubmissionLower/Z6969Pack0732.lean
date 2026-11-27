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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 2 257073 := by
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

def price : Pricing := ⟨55/100, 90/100, [273797776, 361774598, 361252498, 362222808, 361525171, 362313791, 362219968, 360452931, 159996443, 160297803, 160575178, 160052944, 70418531, 83022269, 73845132, 77450754, 112601354, 112501521, 131501682, 100000000, 226394258], [1325808, 956030, 957462, 954800, 956714, 954551, 954808, 959656, 2403282, 2398266, 2393650, 2402342, 5699031, 4807735, 5426398, 5167558, 3491504, 3494973, 2959476, 3958949, 1644064],
  ![120174600031560, 1616180795752, 203754832200, 5270909160], 155959754088974635⟩

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
    · exact Pricing.height_from_critical Band.middle _ 15 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 11824323/2738, 106677858/2809, 212891861/1458] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle98
end Z6969Source1832

-- Source: Research6969.PhysicalChecks117
section Z6969Source1833
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1872 : Request := ⟨⟨⟨3950,5512,1189,205621⟩,1848744952463360,25255771038451⟩,16,2,1,257073,1⟩
private theorem pass1872_2390 : (Triangular src1872) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1872_2391 : (Triangular src1872) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1872_2393 : (Triangular src1872) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1872_2398 : (Triangular src1872) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1872_2411 : (Triangular src1872) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1872_2445 : (Triangular src1872) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1872_2534 : (Triangular src1872) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1872 : Cover (Triangular src1872) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1872_2390, by decide, by decide, pass1872_2391, by decide, by decide, pass1872_2393, by decide, by decide, pass1872_2398, by decide, by decide, pass1872_2411, by decide, by decide, pass1872_2445, by decide, by decide, pass1872_2534, rfl⟩
def src1873 : Request := ⟨⟨⟨1750,2442,518,80507⟩,158964379549696,962176592398⟩,0,2,1,257073,2⟩
private theorem pass1873_2390 : (Triangular src1873) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1873_2391 : (Triangular src1873) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1873_2393 : (Triangular src1873) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1873_2399 : (Triangular src1873) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1873_2415 : (Triangular src1873) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1873_2458 : (Triangular src1873) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1873 : Cover (Triangular src1873) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1873_2390, by decide, by decide, pass1873_2391, by decide, by decide, pass1873_2393, by decide, by decide, pass1873_2399, by decide, by decide, pass1873_2415, by decide, by decide, pass1873_2458, rfl⟩
def src1874 : Request := ⟨⟨⟨1750,2442,518,84897⟩,158964379549696,962176592398⟩,1,2,1,257073,2⟩
private theorem pass1874_2390 : (Triangular src1874) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1874_2391 : (Triangular src1874) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1874_2393 : (Triangular src1874) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1874_2399 : (Triangular src1874) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1874_2415 : (Triangular src1874) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1874_2458 : (Triangular src1874) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1874 : Cover (Triangular src1874) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1874_2390, by decide, by decide, pass1874_2391, by decide, by decide, pass1874_2393, by decide, by decide, pass1874_2399, by decide, by decide, pass1874_2415, by decide, by decide, pass1874_2458, rfl⟩
def src1875 : Request := ⟨⟨⟨1750,2442,518,89793⟩,158964379549696,962176592398⟩,2,2,1,257073,2⟩
private theorem pass1875_2390 : (Triangular src1875) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1875_2391 : (Triangular src1875) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1875_2393 : (Triangular src1875) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1875_2399 : (Triangular src1875) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1875_2415 : (Triangular src1875) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1875_2458 : (Triangular src1875) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1875 : Cover (Triangular src1875) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1875_2390, by decide, by decide, pass1875_2391, by decide, by decide, pass1875_2393, by decide, by decide, pass1875_2399, by decide, by decide, pass1875_2415, by decide, by decide, pass1875_2458, rfl⟩
def src1876 : Request := ⟨⟨⟨1750,2442,527,95498⟩,161065121873920,975196209190⟩,3,2,1,257073,2⟩
private theorem pass1876_2390 : (Triangular src1876) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1876_2391 : (Triangular src1876) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1876_2393 : (Triangular src1876) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1876_2398 : (Triangular src1876) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1876_2412 : (Triangular src1876) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1876_2449 : (Triangular src1876) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1876 : Cover (Triangular src1876) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1876_2390, by decide, by decide, pass1876_2391, by decide, by decide, pass1876_2393, by decide, by decide, pass1876_2398, by decide, by decide, pass1876_2412, by decide, by decide, pass1876_2449, rfl⟩
def src1877 : Request := ⟨⟨⟨1750,2442,527,101769⟩,161065121873920,975196209190⟩,4,2,1,257073,2⟩
private theorem pass1877_2390 : (Triangular src1877) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1877_2391 : (Triangular src1877) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1877_2393 : (Triangular src1877) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1877_2398 : (Triangular src1877) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1877_2412 : (Triangular src1877) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1877_2449 : (Triangular src1877) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1877 : Cover (Triangular src1877) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1877_2390, by decide, by decide, pass1877_2391, by decide, by decide, pass1877_2393, by decide, by decide, pass1877_2398, by decide, by decide, pass1877_2412, by decide, by decide, pass1877_2449, rfl⟩
def src1878 : Request := ⟨⟨⟨2100,2930,622,116384⟩,274699477319680,1994139134137⟩,6,2,1,257073,2⟩
private theorem pass1878_2390 : (Triangular src1878) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1878_2391 : (Triangular src1878) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1878_2393 : (Triangular src1878) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1878_2399 : (Triangular src1878) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1878_2415 : (Triangular src1878) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1878_2457 : (Triangular src1878) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1878 : Cover (Triangular src1878) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass1878_2390, by decide, by decide, pass1878_2391, by decide, by decide, pass1878_2393, by decide, by decide, pass1878_2399, by decide, by decide, pass1878_2415, by decide, by decide, pass1878_2457, rfl⟩
def src1879 : Request := ⟨⟨⟨2600,3628,783,133992⟩,527755772952576,4745819470168⟩,8,2,1,257073,2⟩
private theorem pass1879_2390 : (Triangular src1879) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1879_2391 : (Triangular src1879) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1879_2393 : (Triangular src1879) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1879_2398 : (Triangular src1879) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1879_2411 : (Triangular src1879) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1879_2446 : (Triangular src1879) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1879 : Cover (Triangular src1879) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1879_2390, by decide, by decide, pass1879_2391, by decide, by decide, pass1879_2393, by decide, by decide, pass1879_2398, by decide, by decide, pass1879_2411, by decide, by decide, pass1879_2446, rfl⟩
def src1880 : Request := ⟨⟨⟨3200,4465,947,154190⟩,970564165959680,10735676910569⟩,10,2,1,257073,2⟩
private theorem pass1880_2390 : (Triangular src1880) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1880_2391 : (Triangular src1880) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1880_2393 : (Triangular src1880) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1880_2398 : (Triangular src1880) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1880_2412 : (Triangular src1880) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1880_2449 : (Triangular src1880) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1880 : Cover (Triangular src1880) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1880_2390, by decide, by decide, pass1880_2391, by decide, by decide, pass1880_2393, by decide, by decide, pass1880_2398, by decide, by decide, pass1880_2412, by decide, by decide, pass1880_2449, rfl⟩
def src1881 : Request := ⟨⟨⟨3200,4465,963,168969⟩,983050615259136,10877088344236⟩,13,2,1,257073,2⟩
private theorem pass1881_2390 : (Triangular src1881) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1881_2391 : (Triangular src1881) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1881_2393 : (Triangular src1881) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1881_2398 : (Triangular src1881) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1881_2411 : (Triangular src1881) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1881_2445 : (Triangular src1881) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1881_2534 : (Triangular src1881) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1881 : Cover (Triangular src1881) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1881_2390, by decide, by decide, pass1881_2391, by decide, by decide, pass1881_2393, by decide, by decide, pass1881_2398, by decide, by decide, pass1881_2411, by decide, by decide, pass1881_2445, by decide, by decide, pass1881_2534, rfl⟩
def src1882 : Request := ⟨⟨⟨3950,5512,1169,196413⟩,1824966114017280,24923274283249⟩,16,2,1,257073,2⟩
private theorem pass1882_2390 : (Triangular src1882) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1882_2391 : (Triangular src1882) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1882_2393 : (Triangular src1882) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1882_2398 : (Triangular src1882) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1882_2412 : (Triangular src1882) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1882_2448 : (Triangular src1882) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1882 : Cover (Triangular src1882) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass1882_2390, by decide, by decide, pass1882_2391, by decide, by decide, pass1882_2393, by decide, by decide, pass1882_2398, by decide, by decide, pass1882_2412, by decide, by decide, pass1882_2448, rfl⟩
def src1883 : Request := ⟨⟨⟨4800,6698,1421,230893⟩,3274891856707584,54342858960622⟩,20,2,1,257073,2⟩
private theorem pass1883_2390 : (Triangular src1883) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1883_2391 : (Triangular src1883) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1883_2393 : (Triangular src1883) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1883_2398 : (Triangular src1883) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1883_2411 : (Triangular src1883) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1883_2446 : (Triangular src1883) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1883 : Cover (Triangular src1883) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1883_2390, by decide, by decide, pass1883_2391, by decide, by decide, pass1883_2393, by decide, by decide, pass1883_2398, by decide, by decide, pass1883_2411, by decide, by decide, pass1883_2446, rfl⟩
def src1884 : Request := ⟨⟨⟨1450,2023,436,71151⟩,91566841790464,459151377566⟩,0,2,1,257073,3⟩
private theorem pass1884_2390 : (Triangular src1884) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1884_2391 : (Triangular src1884) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1884_2393 : (Triangular src1884) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1884_2399 : (Triangular src1884) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1884_2415 : (Triangular src1884) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1884_2458 : (Triangular src1884) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1884 : Cover (Triangular src1884) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1884_2390, by decide, by decide, pass1884_2391, by decide, by decide, pass1884_2393, by decide, by decide, pass1884_2399, by decide, by decide, pass1884_2415, by decide, by decide, pass1884_2458, rfl⟩
def src1885 : Request := ⟨⟨⟨1450,2023,429,76671⟩,90444517867520,453391020534⟩,1,2,1,257073,3⟩
private theorem pass1885_2390 : (Triangular src1885) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1885_2391 : (Triangular src1885) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1885_2393 : (Triangular src1885) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1885_2399 : (Triangular src1885) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1885_2415 : (Triangular src1885) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1885_2458 : (Triangular src1885) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1885 : Cover (Triangular src1885) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1885_2390, by decide, by decide, pass1885_2391, by decide, by decide, pass1885_2393, by decide, by decide, pass1885_2399, by decide, by decide, pass1885_2415, by decide, by decide, pass1885_2458, rfl⟩
def src1886 : Request := ⟨⟨⟨1450,2023,436,82785⟩,91566841790464,459151377566⟩,2,2,1,257073,3⟩
private theorem pass1886_2390 : (Triangular src1886) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1886_2391 : (Triangular src1886) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1886_2393 : (Triangular src1886) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1886_2399 : (Triangular src1886) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1886_2415 : (Triangular src1886) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1886_2458 : (Triangular src1886) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1886 : Cover (Triangular src1886) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1886_2390, by decide, by decide, pass1886_2391, by decide, by decide, pass1886_2393, by decide, by decide, pass1886_2399, by decide, by decide, pass1886_2415, by decide, by decide, pass1886_2458, rfl⟩
def src1887 : Request := ⟨⟨⟨1750,2442,527,96810⟩,161065121873920,975196209190⟩,4,2,1,257073,3⟩
private theorem pass1887_2390 : (Triangular src1887) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1887_2391 : (Triangular src1887) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1887_2393 : (Triangular src1887) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1887_2398 : (Triangular src1887) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1887_2412 : (Triangular src1887) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1887_2449 : (Triangular src1887) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1887 : Cover (Triangular src1887) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1887_2390, by decide, by decide, pass1887_2391, by decide, by decide, pass1887_2393, by decide, by decide, pass1887_2398, by decide, by decide, pass1887_2412, by decide, by decide, pass1887_2449, rfl⟩
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
  physicalFloor := 257073
  seedFloor := 2

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨2, 2, 10, 100/100, 80/100, ![179966316348, 94097396411, 1107578556, 553796383], 8979249681392931⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 3 257073 := by
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

def price : Pricing := ⟨55/100, 90/100, [272344254, 358725311, 359813645, 359184664, 359711941, 359170423, 360245536, 358607008, 163842506, 164274426, 164256911, 164260305, 61731104, 82308138, 73521917, 77178426, 112154437, 112061691, 131014171, 100000000, 226013418], [1333252, 964396, 961410, 963136, 961689, 963175, 960225, 964721, 2339267, 2332078, 2332370, 2332313, 6526805, 4850186, 5452115, 5186386, 3507035, 3510258, 2970176, 3958949, 1647199],
  ![119972442542760, 1616594237892, 203412076200, 5290113720], 154651776911763355⟩

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
    · exact Pricing.height_from_critical Band.middle _ 18 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 5881813/1369, 105716436/2809, 75273552/529] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle99
end Z6969Source1836

-- Source: Research6969.PhysicalChecks118
section Z6969Source1837
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1888 : Request := ⟨⟨⟨2100,2930,622,110901⟩,274699477319680,1994139134137⟩,6,2,1,257073,3⟩
private theorem pass1888_2390 : (Triangular src1888) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1888_2391 : (Triangular src1888) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1888_2393 : (Triangular src1888) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1888_2399 : (Triangular src1888) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1888_2415 : (Triangular src1888) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1888_2457 : (Triangular src1888) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1888 : Cover (Triangular src1888) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass1888_2390, by decide, by decide, pass1888_2391, by decide, by decide, pass1888_2393, by decide, by decide, pass1888_2399, by decide, by decide, pass1888_2415, by decide, by decide, pass1888_2457, rfl⟩
def src1889 : Request := ⟨⟨⟨2600,3628,770,127531⟩,521059839508480,4684185417862⟩,8,2,1,257073,3⟩
private theorem pass1889_2390 : (Triangular src1889) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1889_2391 : (Triangular src1889) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1889_2393 : (Triangular src1889) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1889_2398 : (Triangular src1889) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1889_2412 : (Triangular src1889) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1889_2449 : (Triangular src1889) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1889 : Cover (Triangular src1889) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1889_2390, by decide, by decide, pass1889_2391, by decide, by decide, pass1889_2393, by decide, by decide, pass1889_2398, by decide, by decide, pass1889_2412, by decide, by decide, pass1889_2449, rfl⟩
def src1890 : Request := ⟨⟨⟨2600,3628,783,138308⟩,527755772952576,4745819470168⟩,10,2,1,257073,3⟩
private theorem pass1890_2390 : (Triangular src1890) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1890_2391 : (Triangular src1890) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1890_2393 : (Triangular src1890) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1890_2398 : (Triangular src1890) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1890_2411 : (Triangular src1890) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1890_2446 : (Triangular src1890) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1890 : Cover (Triangular src1890) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1890_2390, by decide, by decide, pass1890_2391, by decide, by decide, pass1890_2393, by decide, by decide, pass1890_2398, by decide, by decide, pass1890_2411, by decide, by decide, pass1890_2446, rfl⟩
def src1891 : Request := ⟨⟨⟨3200,4465,963,146435⟩,983050615259136,10877088344236⟩,10,2,1,257073,3⟩
private theorem pass1891_2390 : (Triangular src1891) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1891_2391 : (Triangular src1891) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1891_2393 : (Triangular src1891) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1891_2398 : (Triangular src1891) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1891_2411 : (Triangular src1891) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1891_2445 : (Triangular src1891) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1891_2534 : (Triangular src1891) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1891 : Cover (Triangular src1891) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1891_2390, by decide, by decide, pass1891_2391, by decide, by decide, pass1891_2393, by decide, by decide, pass1891_2398, by decide, by decide, pass1891_2411, by decide, by decide, pass1891_2445, by decide, by decide, pass1891_2534, rfl⟩
def src1892 : Request := ⟨⟨⟨3950,5512,1189,173616⟩,1848744952463360,25255771038451⟩,13,2,1,257073,3⟩
private theorem pass1892_2390 : (Triangular src1892) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1892_2391 : (Triangular src1892) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1892_2393 : (Triangular src1892) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1892_2398 : (Triangular src1892) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1892_2411 : (Triangular src1892) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1892_2445 : (Triangular src1892) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1892_2534 : (Triangular src1892) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1892 : Cover (Triangular src1892) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1892_2390, by decide, by decide, pass1892_2391, by decide, by decide, pass1892_2393, by decide, by decide, pass1892_2398, by decide, by decide, pass1892_2411, by decide, by decide, pass1892_2445, by decide, by decide, pass1892_2534, rfl⟩
def src1893 : Request := ⟨⟨⟨4800,6698,1421,220056⟩,3274891856707584,54342858960622⟩,20,2,1,257073,3⟩
private theorem pass1893_2390 : (Triangular src1893) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1893_2391 : (Triangular src1893) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1893_2393 : (Triangular src1893) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1893_2398 : (Triangular src1893) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1893_2411 : (Triangular src1893) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1893_2446 : (Triangular src1893) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1893 : Cover (Triangular src1893) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1893_2390, by decide, by decide, pass1893_2391, by decide, by decide, pass1893_2393, by decide, by decide, pass1893_2398, by decide, by decide, pass1893_2411, by decide, by decide, pass1893_2446, rfl⟩
def src1894 : Request := ⟨⟨⟨1750,2442,527,72776⟩,161065121873920,975196209190⟩,0,2,1,257073,4⟩
private theorem pass1894_2390 : (Triangular src1894) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1894_2391 : (Triangular src1894) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1894_2393 : (Triangular src1894) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1894_2398 : (Triangular src1894) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1894_2412 : (Triangular src1894) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1894_2449 : (Triangular src1894) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1894 : Cover (Triangular src1894) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1894_2390, by decide, by decide, pass1894_2391, by decide, by decide, pass1894_2393, by decide, by decide, pass1894_2398, by decide, by decide, pass1894_2412, by decide, by decide, pass1894_2449, rfl⟩
def src1895 : Request := ⟨⟨⟨1750,2442,527,76764⟩,161065121873920,975196209190⟩,1,2,1,257073,4⟩
private theorem pass1895_2390 : (Triangular src1895) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1895_2391 : (Triangular src1895) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1895_2393 : (Triangular src1895) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1895_2398 : (Triangular src1895) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1895_2412 : (Triangular src1895) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1895_2449 : (Triangular src1895) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1895 : Cover (Triangular src1895) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1895_2390, by decide, by decide, pass1895_2391, by decide, by decide, pass1895_2393, by decide, by decide, pass1895_2398, by decide, by decide, pass1895_2412, by decide, by decide, pass1895_2449, rfl⟩
def src1896 : Request := ⟨⟨⟨1750,2442,527,81214⟩,161065121873920,975196209190⟩,2,2,1,257073,4⟩
private theorem pass1896_2390 : (Triangular src1896) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1896_2391 : (Triangular src1896) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1896_2393 : (Triangular src1896) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1896_2398 : (Triangular src1896) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1896_2412 : (Triangular src1896) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1896_2449 : (Triangular src1896) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1896 : Cover (Triangular src1896) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1896_2390, by decide, by decide, pass1896_2391, by decide, by decide, pass1896_2393, by decide, by decide, pass1896_2398, by decide, by decide, pass1896_2412, by decide, by decide, pass1896_2449, rfl⟩
def src1897 : Request := ⟨⟨⟨2100,2930,632,90984⟩,278060332482560,2019119590628⟩,3,2,1,257073,4⟩
private theorem pass1897_2390 : (Triangular src1897) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1897_2391 : (Triangular src1897) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1897_2393 : (Triangular src1897) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1897_2398 : (Triangular src1897) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1897_2412 : (Triangular src1897) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1897_2449 : (Triangular src1897) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1897 : Cover (Triangular src1897) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1897_2390, by decide, by decide, pass1897_2391, by decide, by decide, pass1897_2393, by decide, by decide, pass1897_2398, by decide, by decide, pass1897_2412, by decide, by decide, pass1897_2449, rfl⟩
def src1898 : Request := ⟨⟨⟨2100,2930,632,95283⟩,278060332482560,2019119590628⟩,4,2,1,257073,4⟩
private theorem pass1898_2390 : (Triangular src1898) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1898_2391 : (Triangular src1898) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1898_2393 : (Triangular src1898) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1898_2398 : (Triangular src1898) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1898_2412 : (Triangular src1898) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1898_2449 : (Triangular src1898) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1898 : Cover (Triangular src1898) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1898_2390, by decide, by decide, pass1898_2391, by decide, by decide, pass1898_2393, by decide, by decide, pass1898_2398, by decide, by decide, pass1898_2412, by decide, by decide, pass1898_2449, rfl⟩
def src1899 : Request := ⟨⟨⟨2600,3628,770,112503⟩,521059839508480,4684185417862⟩,6,2,1,257073,4⟩
private theorem pass1899_2390 : (Triangular src1899) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1899_2391 : (Triangular src1899) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1899_2393 : (Triangular src1899) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1899_2398 : (Triangular src1899) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1899_2412 : (Triangular src1899) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1899_2449 : (Triangular src1899) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1899 : Cover (Triangular src1899) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1899_2390, by decide, by decide, pass1899_2391, by decide, by decide, pass1899_2393, by decide, by decide, pass1899_2398, by decide, by decide, pass1899_2412, by decide, by decide, pass1899_2449, rfl⟩
def src1900 : Request := ⟨⟨⟨2600,3628,783,120981⟩,527755772952576,4745819470168⟩,8,2,1,257073,4⟩
private theorem pass1900_2390 : (Triangular src1900) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1900_2391 : (Triangular src1900) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1900_2393 : (Triangular src1900) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1900_2398 : (Triangular src1900) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1900_2411 : (Triangular src1900) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1900_2446 : (Triangular src1900) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1900 : Cover (Triangular src1900) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1900_2390, by decide, by decide, pass1900_2391, by decide, by decide, pass1900_2393, by decide, by decide, pass1900_2398, by decide, by decide, pass1900_2411, by decide, by decide, pass1900_2446, rfl⟩
def src1901 : Request := ⟨⟨⟨3200,4465,947,139746⟩,970564165959680,10735676910569⟩,10,2,1,257073,4⟩
private theorem pass1901_2390 : (Triangular src1901) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1901_2391 : (Triangular src1901) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1901_2393 : (Triangular src1901) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1901_2398 : (Triangular src1901) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1901_2412 : (Triangular src1901) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1901_2449 : (Triangular src1901) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1901 : Cover (Triangular src1901) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1901_2390, by decide, by decide, pass1901_2391, by decide, by decide, pass1901_2393, by decide, by decide, pass1901_2398, by decide, by decide, pass1901_2412, by decide, by decide, pass1901_2449, rfl⟩
def src1902 : Request := ⟨⟨⟨2600,3628,783,150429⟩,527755772952576,4745819470168⟩,13,2,1,257073,4⟩
private theorem pass1902_2390 : (Triangular src1902) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1902_2391 : (Triangular src1902) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1902_2393 : (Triangular src1902) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1902_2398 : (Triangular src1902) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1902_2411 : (Triangular src1902) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1902_2446 : (Triangular src1902) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1902 : Cover (Triangular src1902) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1902_2390, by decide, by decide, pass1902_2391, by decide, by decide, pass1902_2393, by decide, by decide, pass1902_2398, by decide, by decide, pass1902_2411, by decide, by decide, pass1902_2446, rfl⟩
def src1903 : Request := ⟨⟨⟨3950,5512,1169,165716⟩,1824966114017280,24923274283249⟩,13,2,1,257073,4⟩
private theorem pass1903_2390 : (Triangular src1903) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1903_2391 : (Triangular src1903) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1903_2393 : (Triangular src1903) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1903_2398 : (Triangular src1903) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1903_2412 : (Triangular src1903) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1903_2448 : (Triangular src1903) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1903 : Cover (Triangular src1903) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass1903_2390, by decide, by decide, pass1903_2391, by decide, by decide, pass1903_2393, by decide, by decide, pass1903_2398, by decide, by decide, pass1903_2412, by decide, by decide, pass1903_2448, rfl⟩
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
  physicalFloor := 257073
  seedFloor := 3

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨2, 3, 10, 100/100, 90/100, ![257278912512, 91930499592, 1661364992, 553796383], 7486078168950288⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 4 257073 := by
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

def price : Pricing := ⟨55/100, 90/100, [270902168, 355676025, 357955892, 356172665, 356029029, 357939930, 356287998, 357713066, 166117348, 166446147, 166492495, 166390769, 70820441, 81594007, 70549171, 77178426, 110921019, 110957263, 130482600, 100000000, 225832562], [1340637, 972762, 966507, 971399, 971793, 966551, 971083, 967173, 2301404, 2295931, 2295160, 2296853, 5667054, 4892637, 5688637, 5186386, 3549899, 3548639, 2981843, 3958949, 1648687],
  ![119876440560840, 1616790166948, 203249305800, 5290113720], 153414094367630078⟩

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
    · exact Pricing.height_from_critical Band.middle _ 15 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 5854205/1369, 105358666/2809, 204048229/1458] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle100
end Z6969Source1840

-- Source: Research6969.PhysicalChecks119
section Z6969Source1841
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1904 : Request := ⟨⟨⟨4800,6698,1445,208204⟩,3317023033262080,55058665830093⟩,20,2,1,257073,4⟩
private theorem pass1904_2390 : (Triangular src1904) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1904_2391 : (Triangular src1904) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1904_2393 : (Triangular src1904) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1904_2398 : (Triangular src1904) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1904_2411 : (Triangular src1904) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1904_2445 : (Triangular src1904) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1904_2533 : (Triangular src1904) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1904 : Cover (Triangular src1904) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass1904_2390, by decide, by decide, pass1904_2391, by decide, by decide, pass1904_2393, by decide, by decide, pass1904_2398, by decide, by decide, pass1904_2411, by decide, by decide, pass1904_2445, by decide, by decide, pass1904_2533, rfl⟩
def src1905 : Request := ⟨⟨⟨1450,2023,436,63929⟩,91566841790464,459151377566⟩,0,2,1,257073,5⟩
private theorem pass1905_2390 : (Triangular src1905) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1905_2391 : (Triangular src1905) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1905_2393 : (Triangular src1905) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1905_2399 : (Triangular src1905) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1905_2415 : (Triangular src1905) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1905_2458 : (Triangular src1905) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1905 : Cover (Triangular src1905) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1905_2390, by decide, by decide, pass1905_2391, by decide, by decide, pass1905_2393, by decide, by decide, pass1905_2399, by decide, by decide, pass1905_2415, by decide, by decide, pass1905_2458, rfl⟩
def src1906 : Request := ⟨⟨⟨1750,2442,518,72978⟩,158964379549696,962176592398⟩,1,2,1,257073,5⟩
private theorem pass1906_2390 : (Triangular src1906) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1906_2391 : (Triangular src1906) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1906_2393 : (Triangular src1906) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1906_2399 : (Triangular src1906) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1906_2415 : (Triangular src1906) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1906_2458 : (Triangular src1906) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1906 : Cover (Triangular src1906) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass1906_2390, by decide, by decide, pass1906_2391, by decide, by decide, pass1906_2393, by decide, by decide, pass1906_2399, by decide, by decide, pass1906_2415, by decide, by decide, pass1906_2458, rfl⟩
def src1907 : Request := ⟨⟨⟨2100,2930,622,86538⟩,274699477319680,1994139134137⟩,3,2,1,257073,5⟩
private theorem pass1907_2390 : (Triangular src1907) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1907_2391 : (Triangular src1907) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1907_2393 : (Triangular src1907) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1907_2399 : (Triangular src1907) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1907_2415 : (Triangular src1907) 2415 2456 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1907_2457 : (Triangular src1907) 2457 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1907 : Cover (Triangular src1907) 2534 2390 [2390,2392,2398,2414,2456,2534] := by
  exact ⟨by decide, by decide, pass1907_2390, by decide, by decide, pass1907_2391, by decide, by decide, pass1907_2393, by decide, by decide, pass1907_2399, by decide, by decide, pass1907_2415, by decide, by decide, pass1907_2457, rfl⟩
def src1908 : Request := ⟨⟨⟨2600,3628,770,115018⟩,521059839508480,4684185417862⟩,8,2,1,257073,5⟩
private theorem pass1908_2390 : (Triangular src1908) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1908_2391 : (Triangular src1908) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1908_2393 : (Triangular src1908) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1908_2398 : (Triangular src1908) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1908_2412 : (Triangular src1908) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1908_2449 : (Triangular src1908) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1908 : Cover (Triangular src1908) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1908_2390, by decide, by decide, pass1908_2391, by decide, by decide, pass1908_2393, by decide, by decide, pass1908_2398, by decide, by decide, pass1908_2412, by decide, by decide, pass1908_2449, rfl⟩
def src1909 : Request := ⟨⟨⟨3200,4465,963,144443⟩,983050615259136,10877088344236⟩,13,2,1,257073,5⟩
private theorem pass1909_2390 : (Triangular src1909) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1909_2391 : (Triangular src1909) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1909_2393 : (Triangular src1909) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1909_2398 : (Triangular src1909) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1909_2411 : (Triangular src1909) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1909_2445 : (Triangular src1909) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1909_2534 : (Triangular src1909) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1909 : Cover (Triangular src1909) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1909_2390, by decide, by decide, pass1909_2391, by decide, by decide, pass1909_2393, by decide, by decide, pass1909_2398, by decide, by decide, pass1909_2411, by decide, by decide, pass1909_2445, by decide, by decide, pass1909_2534, rfl⟩
def src1910 : Request := ⟨⟨⟨3200,4465,963,160083⟩,983050615259136,10877088344236⟩,16,2,1,257073,5⟩
private theorem pass1910_2390 : (Triangular src1910) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1910_2391 : (Triangular src1910) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1910_2393 : (Triangular src1910) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1910_2398 : (Triangular src1910) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1910_2411 : (Triangular src1910) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1910_2445 : (Triangular src1910) 2445 2533 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1910_2534 : (Triangular src1910) 2534 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1910 : Cover (Triangular src1910) 2534 2390 [2390,2392,2397,2410,2444,2533,2534] := by
  exact ⟨by decide, by decide, pass1910_2390, by decide, by decide, pass1910_2391, by decide, by decide, pass1910_2393, by decide, by decide, pass1910_2398, by decide, by decide, pass1910_2411, by decide, by decide, pass1910_2445, by decide, by decide, pass1910_2534, rfl⟩
def src1911 : Request := ⟨⟨⟨3950,5512,1169,168880⟩,1824966114017280,24923274283249⟩,16,2,1,257073,5⟩
private theorem pass1911_2390 : (Triangular src1911) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1911_2391 : (Triangular src1911) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1911_2393 : (Triangular src1911) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1911_2398 : (Triangular src1911) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1911_2412 : (Triangular src1911) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1911_2448 : (Triangular src1911) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1911 : Cover (Triangular src1911) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass1911_2390, by decide, by decide, pass1911_2391, by decide, by decide, pass1911_2393, by decide, by decide, pass1911_2398, by decide, by decide, pass1911_2412, by decide, by decide, pass1911_2448, rfl⟩
def src1912 : Request := ⟨⟨⟨4800,6698,1421,198523⟩,3274891856707584,54342858960622⟩,20,2,1,257073,5⟩
private theorem pass1912_2390 : (Triangular src1912) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1912_2391 : (Triangular src1912) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1912_2393 : (Triangular src1912) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1912_2398 : (Triangular src1912) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1912_2411 : (Triangular src1912) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1912_2446 : (Triangular src1912) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1912 : Cover (Triangular src1912) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass1912_2390, by decide, by decide, pass1912_2391, by decide, by decide, pass1912_2393, by decide, by decide, pass1912_2398, by decide, by decide, pass1912_2411, by decide, by decide, pass1912_2446, rfl⟩
def src1913 : Request := ⟨⟨⟨5700,7954,1716,231542⟩,5553838907981824,109473260530676⟩,25,2,1,257073,5⟩
private theorem pass1913_2390 : (Triangular src1913) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1913_2391 : (Triangular src1913) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1913_2393 : (Triangular src1913) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1913_2398 : (Triangular src1913) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1913_2411 : (Triangular src1913) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1913_2445 : (Triangular src1913) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1913_2533 : (Triangular src1913) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1913 : Cover (Triangular src1913) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass1913_2390, by decide, by decide, pass1913_2391, by decide, by decide, pass1913_2393, by decide, by decide, pass1913_2398, by decide, by decide, pass1913_2411, by decide, by decide, pass1913_2445, by decide, by decide, pass1913_2533, rfl⟩
def src1914 : Request := ⟨⟨⟨1750,2442,527,65035⟩,161065121873920,975196209190⟩,0,2,1,257073,6⟩
private theorem pass1914_2390 : (Triangular src1914) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1914_2391 : (Triangular src1914) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1914_2393 : (Triangular src1914) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1914_2398 : (Triangular src1914) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1914_2412 : (Triangular src1914) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1914_2449 : (Triangular src1914) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1914 : Cover (Triangular src1914) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1914_2390, by decide, by decide, pass1914_2391, by decide, by decide, pass1914_2393, by decide, by decide, pass1914_2398, by decide, by decide, pass1914_2412, by decide, by decide, pass1914_2449, rfl⟩
def src1915 : Request := ⟨⟨⟨1750,2442,527,68589⟩,161065121873920,975196209190⟩,1,2,1,257073,6⟩
private theorem pass1915_2390 : (Triangular src1915) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1915_2391 : (Triangular src1915) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1915_2393 : (Triangular src1915) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1915_2398 : (Triangular src1915) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1915_2412 : (Triangular src1915) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1915_2449 : (Triangular src1915) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1915 : Cover (Triangular src1915) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1915_2390, by decide, by decide, pass1915_2391, by decide, by decide, pass1915_2393, by decide, by decide, pass1915_2398, by decide, by decide, pass1915_2412, by decide, by decide, pass1915_2449, rfl⟩
def src1916 : Request := ⟨⟨⟨1750,2442,527,72556⟩,161065121873920,975196209190⟩,2,2,1,257073,6⟩
private theorem pass1916_2390 : (Triangular src1916) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1916_2391 : (Triangular src1916) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1916_2393 : (Triangular src1916) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1916_2398 : (Triangular src1916) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1916_2412 : (Triangular src1916) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1916_2449 : (Triangular src1916) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1916 : Cover (Triangular src1916) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1916_2390, by decide, by decide, pass1916_2391, by decide, by decide, pass1916_2393, by decide, by decide, pass1916_2398, by decide, by decide, pass1916_2412, by decide, by decide, pass1916_2449, rfl⟩
def src1917 : Request := ⟨⟨⟨2100,2930,632,85142⟩,278060332482560,2019119590628⟩,4,2,1,257073,6⟩
private theorem pass1917_2390 : (Triangular src1917) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1917_2391 : (Triangular src1917) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1917_2393 : (Triangular src1917) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1917_2398 : (Triangular src1917) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1917_2412 : (Triangular src1917) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1917_2449 : (Triangular src1917) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1917 : Cover (Triangular src1917) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1917_2390, by decide, by decide, pass1917_2391, by decide, by decide, pass1917_2393, by decide, by decide, pass1917_2398, by decide, by decide, pass1917_2412, by decide, by decide, pass1917_2449, rfl⟩
def src1918 : Request := ⟨⟨⟨2100,2930,632,94008⟩,278060332482560,2019119590628⟩,6,2,1,257073,6⟩
private theorem pass1918_2390 : (Triangular src1918) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1918_2391 : (Triangular src1918) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1918_2393 : (Triangular src1918) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1918_2398 : (Triangular src1918) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1918_2412 : (Triangular src1918) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1918_2449 : (Triangular src1918) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1918 : Cover (Triangular src1918) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass1918_2390, by decide, by decide, pass1918_2391, by decide, by decide, pass1918_2393, by decide, by decide, pass1918_2398, by decide, by decide, pass1918_2412, by decide, by decide, pass1918_2449, rfl⟩
def src1919 : Request := ⟨⟨⟨2600,3628,783,100262⟩,527755772952576,4745819470168⟩,6,2,1,257073,6⟩
private theorem pass1919_2390 : (Triangular src1919) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1919_2391 : (Triangular src1919) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1919_2393 : (Triangular src1919) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1919_2398 : (Triangular src1919) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1919_2412 : (Triangular src1919) 2412 2447 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1919_2448 : (Triangular src1919) 2448 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1919 : Cover (Triangular src1919) 2534 2390 [2390,2392,2397,2411,2447,2534] := by
  exact ⟨by decide, by decide, pass1919_2390, by decide, by decide, pass1919_2391, by decide, by decide, pass1919_2393, by decide, by decide, pass1919_2398, by decide, by decide, pass1919_2412, by decide, by decide, pass1919_2448, rfl⟩
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
  physicalFloor := 257073
  seedFloor := 4

theorem sources : plan.Sources 2390 (Band.middle).last := by
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

def price : EarlyPrice := ⟨2, 4, 10, 95/100, 80/100, ![324562344868, 89330615843, 2918541271, 563149735], 8118645556738783⟩
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
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 4 4 :=
  ⟨Lower6960.Prefix6969MainCases.Middle100.plan, Lower6960.Prefix6969MainCases.Middle100.price, Lower6960.Prefix6969MainCases.Middle100.valid, Lower6960.Prefix6969MainCases.Middle100.priced, Lower6960.Prefix6969MainCases.Middle100.sources,
   Lower6960.Prefix6969RescueData.Middle100.plan, Lower6960.Prefix6969RescueData.Middle100.price, Lower6960.Prefix6969RescueData.Middle100.sources, Lower6960.Prefix6969RescueData.Middle100.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved100
end Z6969Source1843

end Merged_Z6969Pack0732

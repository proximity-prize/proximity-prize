import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0724
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0725
section Merged_Z6969Pack0725

-- Source: Research6969.PrefixMiddleSaved75
section Z6969Source1748
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved75
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle75.price Lower6960.Prefix6969RescueData.Middle75.price :=
  ⟨335, 3285, 50, 734, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle75.plan Lower6960.Prefix6969RescueData.Middle75.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 51 56 :=
  ⟨Lower6960.Prefix6969MainCases.Middle75.plan, Lower6960.Prefix6969MainCases.Middle75.price, Lower6960.Prefix6969MainCases.Middle75.valid, Lower6960.Prefix6969MainCases.Middle75.priced, Lower6960.Prefix6969MainCases.Middle75.sources,
   Lower6960.Prefix6969RescueData.Middle75.plan, Lower6960.Prefix6969RescueData.Middle75.price, Lower6960.Prefix6969RescueData.Middle75.sources, Lower6960.Prefix6969RescueData.Middle75.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved75
end Z6969Source1748

-- Source: Research6969.PhysicalChecks172
section Z6969Source1749
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2752 : Request := ⟨⟨⟨556,772,170,6016⟩,5255817068544,9968090926⟩,10,3,2,385540,11⟩
theorem cover2752 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2752) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2753 : Request := ⟨⟨⟨556,772,170,5936⟩,5255817068544,9968090926⟩,10,3,2,385540,12⟩
theorem cover2753 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2753) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2754 : Request := ⟨⟨⟨556,772,170,5857⟩,5255817068544,9968090926⟩,10,3,2,385540,13⟩
theorem cover2754 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2754) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2755 : Request := ⟨⟨⟨556,772,170,5779⟩,5255817068544,9968090926⟩,10,3,2,385540,14⟩
theorem cover2755 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2755) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2756 : Request := ⟨⟨⟨556,772,170,5702⟩,5255817068544,9968090926⟩,10,3,2,385540,15⟩
theorem cover2756 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2756) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2757 : Request := ⟨⟨⟨556,772,170,5625⟩,5255817068544,9968090926⟩,10,3,2,385540,16⟩
theorem cover2757 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2757) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2758 : Request := ⟨⟨⟨556,772,170,5550⟩,5255817068544,9968090926⟩,10,3,2,385540,17⟩
theorem cover2758 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2758) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2759 : Request := ⟨⟨⟨556,772,170,5475⟩,5255817068544,9968090926⟩,10,3,2,385540,18⟩
theorem cover2759 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2759) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2760 : Request := ⟨⟨⟨556,772,170,5402⟩,5255817068544,9968090926⟩,10,3,2,385540,19⟩
theorem cover2760 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2760) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2761 : Request := ⟨⟨⟨556,772,170,5329⟩,5255817068544,9968090926⟩,10,3,2,385540,20⟩
theorem cover2761 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2761) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2762 : Request := ⟨⟨⟨556,772,170,5258⟩,5255817068544,9968090926⟩,10,3,2,385540,21⟩
theorem cover2762 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2762) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2763 : Request := ⟨⟨⟨556,772,170,5187⟩,5255817068544,9968090926⟩,10,3,2,385540,22⟩
theorem cover2763 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2763) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2764 : Request := ⟨⟨⟨556,772,170,5118⟩,5255817068544,9968090926⟩,10,3,2,385540,23⟩
theorem cover2764 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2764) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2765 : Request := ⟨⟨⟨556,772,170,5050⟩,5255817068544,9968090926⟩,10,3,2,385540,24⟩
theorem cover2765 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2765) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2766 : Request := ⟨⟨⟨556,772,170,4983⟩,5255817068544,9968090926⟩,10,3,2,385540,25⟩
theorem cover2766 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2766) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2767 : Request := ⟨⟨⟨556,772,170,4918⟩,5255817068544,9968090926⟩,10,3,2,385540,26⟩
theorem cover2767 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2767) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1749

-- Source: Research6969.PrefixMainDataMiddle76
section Z6969Source1750
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle76
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank30 1501, bank40 1714, bank49 2130, bank58 2054, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank126 11206, bank153 5200, bank199 7608, bank186 19684, bank176 24684, bank170 28384, bank212 8810] i
  head := src2761
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15027, 126203, 585943, 2149545],
    ![12303, 99386, 898709/2, 3224045/2],
    ![53398/9, 432061/9, 898709/2, 3224045/2],
    ![29433/8, 467827/16, 2117714/9, 831324],
    ![63824/25, 505633/25, 313709/2, 2253001/4],
    ![72196/49, 573817/49, 2586181/25, 9133906/25],
    ![40539/50, 676511/100, 71355, 1134225/4],
    ![95180/121, 722210/121, 464048/7, 10945766/49],
    ![95180/121, 722210/121, 116003/2, 870489/4],
    ![63754/121, 755842/147, 770661/16, 10503459/49],
    ![63754/121, 755842/147, 770661/16, 596848/3],
    ![63754/121, 609747/121, 770661/16, 32176502/225],
    ![1355575/3362, 609747/121, 770661/16, 32176502/225],
    ![1355575/3362, 7244984/1681, 1999400/49, 6760000/49],
    ![1355575/3362, 589390/147, 4332756/121, 27028688/225],
    ![481425/1369, 589390/147, 4332756/121, 27028688/225],
    ![466774/1369, 589390/147, 4332756/121, 27028688/225],
    ![920087/2738, 589390/147, 4332756/121, 27028688/225],
    ![920087/2738, 21189861/5476, 95170565/2704, 27028688/225]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 19 257027 := by
  refine ⟨?_, rank154 5329, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2761⟩⟩
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
    · exact free186_1
    · exact free176_1
    · exact free170_1
    · exact free212_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [255663399, 332700328, 331974128, 332068544, 331551260, 331747343, 331972242, 146240031, 146597514, 146789285, 146522942, 73032174, 73063202, 70079688, 101033294, 100425148, 150823316, 101057369, 233826221], [1419003, 1036033, 1038026, 1037767, 1039187, 1038649, 1038031, 2636590, 2628742, 2624532, 2630379, 5492331, 5489862, 5727295, 3916183, 3941883, 2556545, 3915165, 1583254],
  ![124119634631220, 1608116572024, 210443598900, 5840510820], 141929299618195497⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,8,8,8,8,15,15,15,11,11,7,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 21189861/5476, 95170565/2704, 27028688/225] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle76
end Z6969Source1750

-- Source: Research6969.PhysicalChecks128
section Z6969Source1751
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2048 : Request := ⟨⟨⟨2100,2930,632,29839⟩,278060332482560,2019119590628⟩,3,2,1,257027,18⟩
theorem cover2048 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2048) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2049 : Request := ⟨⟨⟨1750,2442,527,28917⟩,161065121873920,975196209190⟩,4,2,1,257027,18⟩
theorem cover2049 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2049) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2050 : Request := ⟨⟨⟨2100,2930,632,30948⟩,278060332482560,2019119590628⟩,4,2,1,257027,18⟩
theorem cover2050 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2050) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2051 : Request := ⟨⟨⟨2600,3628,783,39053⟩,527755772952576,4745819470168⟩,8,2,1,257027,18⟩
theorem cover2051 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2051) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2052 : Request := ⟨⟨⟨3200,4465,963,45637⟩,983050615259136,10877088344236⟩,10,2,1,257027,18⟩
theorem cover2052 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2052) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2053 : Request := ⟨⟨⟨3200,4465,963,49146⟩,983050615259136,10877088344236⟩,13,2,1,257027,18⟩
theorem cover2053 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2053) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2054 : Request := ⟨⟨⟨4800,6698,1445,84978⟩,3317023033262080,55058665830093⟩,32,2,1,257027,18⟩
theorem cover2054 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2054) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2055 : Request := ⟨⟨⟨5700,7954,1716,88754⟩,5553838907981824,109473260530676⟩,32,2,1,257027,18⟩
theorem cover2055 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2055) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2056 : Request := ⟨⟨⟨1450,2023,436,19562⟩,91566841790464,459151377566⟩,0,2,1,257027,19⟩
theorem cover2056 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2056) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2057 : Request := ⟨⟨⟨1750,2442,527,22518⟩,161065121873920,975196209190⟩,1,2,1,257027,19⟩
theorem cover2057 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2057) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2058 : Request := ⟨⟨⟨2100,2930,632,26836⟩,278060332482560,2019119590628⟩,3,2,1,257027,19⟩
theorem cover2058 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2058) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2059 : Request := ⟨⟨⟨2100,2930,632,27758⟩,278060332482560,2019119590628⟩,4,2,1,257027,19⟩
theorem cover2059 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2059) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2060 : Request := ⟨⟨⟨2600,3628,783,34973⟩,527755772952576,4745819470168⟩,8,2,1,257027,19⟩
theorem cover2060 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2060) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2061 : Request := ⟨⟨⟨3200,4465,963,43957⟩,983050615259136,10877088344236⟩,13,2,1,257027,19⟩
theorem cover2061 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2061) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2062 : Request := ⟨⟨⟨5700,7954,1716,79307⟩,5553838907981824,109473260530676⟩,32,2,1,257027,19⟩
theorem cover2062 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2062) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2063 : Request := ⟨⟨⟨6900,9628,2077,136716⟩,9849424459857920,234966243278304⟩,65,2,1,257027,19⟩
theorem cover2063 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2063) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1751

-- Source: Research6969.PhysicalChecks129
section Z6969Source1752
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2064 : Request := ⟨⟨⟨8300,11582,2498,133661⟩,17139238515245056,491880571317053⟩,65,2,1,257027,19⟩
theorem cover2064 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2064) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2065 : Request := ⟨⟨⟨10000,13955,3010,140635⟩,29974681586237440,1036603432174989⟩,65,2,1,257027,19⟩
theorem cover2065 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2065) 2557 2412 [2413, 2418, 2431, 2464, 2550, 2557] := triangleCover (by decide +kernel)
def src2066 : Request := ⟨⟨⟨1450,2023,436,17554⟩,91566841790464,459151377566⟩,0,2,1,257027,20⟩
theorem cover2066 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2066) 2557 2412 [2414, 2422, 2444, 2503, 2557] := triangleCover (by decide +kernel)
def src2067 : Request := ⟨⟨⟨1450,2023,436,18436⟩,91566841790464,459151377566⟩,1,2,1,257027,20⟩
theorem cover2067 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2067) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2068 : Request := ⟨⟨⟨1750,2442,537,20387⟩,163381988556800,989573241440⟩,2,2,1,257027,20⟩
theorem cover2068 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2068) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2069 : Request := ⟨⟨⟨1750,2442,527,21920⟩,161065121873920,975196209190⟩,3,2,1,257027,20⟩
theorem cover2069 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2069) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2070 : Request := ⟨⟨⟨2100,2930,632,26671⟩,278060332482560,2019119590628⟩,6,2,1,257027,20⟩
theorem cover2070 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2070) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2071 : Request := ⟨⟨⟨2600,3628,783,33149⟩,527755772952576,4745819470168⟩,10,2,1,257027,20⟩
theorem cover2071 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2071) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2072 : Request := ⟨⟨⟨3950,5512,1189,50049⟩,1848744952463360,25255771038451⟩,20,2,1,257027,20⟩
theorem cover2072 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2072) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2073 : Request := ⟨⟨⟨4800,6698,1445,78274⟩,3317023033262080,55058665830093⟩,40,2,1,257027,20⟩
theorem cover2073 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2073) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2074 : Request := ⟨⟨⟨6900,9629,2077,85238⟩,9849424459857920,235044796335102⟩,40,2,1,257027,20⟩
theorem cover2074 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2074) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2075 : Request := ⟨⟨⟨6900,9628,2077,118434⟩,9849424459857920,234966243278304⟩,65,2,1,257027,20⟩
theorem cover2075 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2075) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2076 : Request := ⟨⟨⟨10000,13955,3010,125771⟩,29974681586237440,1036603432174989⟩,65,2,1,257027,20⟩
theorem cover2076 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2076) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2077 : Request := ⟨⟨⟨1750,2442,537,17151⟩,163381988556800,989573241440⟩,0,2,1,257027,21⟩
theorem cover2077 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2077) 2557 2412 [2414, 2421, 2440, 2490, 2557] := triangleCover (by decide +kernel)
def src2078 : Request := ⟨⟨⟨1750,2442,527,18367⟩,161065121873920,975196209190⟩,1,2,1,257027,21⟩
theorem cover2078 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2078) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2079 : Request := ⟨⟨⟨1750,2442,527,18995⟩,161065121873920,975196209190⟩,2,2,1,257027,21⟩
theorem cover2079 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2079) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1752

-- Source: Research6969.PrefixRescueDataMiddle76
section Z6969Source1753
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle76
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,19⟩
  bank i := ![bank236 19562, bank245 22518, bank252 26836, bank252 27758, bank270 34973, bank303 43957, bank347 79307, bank373 133661, bank386 140635, bank359 136716, bank386 140635] i
  reserve i := ![0, 1, 3, 4, 8, 13, 32, 65, 65, 65, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 19

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 19562
    · exact rank245 22518
    · exact rank252 26836
    · exact rank252 27758
    · exact rank270 34973
    · exact rank303 43957
    · exact rank347 79307
    · exact rank373 133661
    · exact rank386 140635
    · exact rank359 136716
    · exact rank386 140635
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2056⟩
    · exact ⟨_, cover2057⟩
    · exact ⟨_, cover2058⟩
    · exact ⟨_, cover2059⟩
    · exact ⟨_, cover2060⟩
    · exact ⟨_, cover2061⟩
    · exact ⟨_, cover2062⟩
    · exact ⟨_, cover2064⟩
    · exact ⟨_, cover2065⟩
    · exact ⟨_, cover2063⟩
    · exact ⟨_, cover2065⟩

def price : EarlyPrice := ⟨2, 19, 10, 85/100, 80/100, ![1041346342905, 135852073940, 22287855030, 1173066230], 3133550975785620⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![11705/66, 176179/66, 228182/33, 230869/6] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle76
end Z6969Source1753

-- Source: Research6969.PrefixMiddleSaved76
section Z6969Source1754
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved76
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle76.price Lower6960.Prefix6969RescueData.Middle76.price :=
  ⟨336, 3869, 177, 2669, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle76.plan Lower6960.Prefix6969RescueData.Middle76.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 19 19 :=
  ⟨Lower6960.Prefix6969MainCases.Middle76.plan, Lower6960.Prefix6969MainCases.Middle76.price, Lower6960.Prefix6969MainCases.Middle76.valid, Lower6960.Prefix6969MainCases.Middle76.priced, Lower6960.Prefix6969MainCases.Middle76.sources,
   Lower6960.Prefix6969RescueData.Middle76.plan, Lower6960.Prefix6969RescueData.Middle76.price, Lower6960.Prefix6969RescueData.Middle76.sources, Lower6960.Prefix6969RescueData.Middle76.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved76
end Z6969Source1754

-- Source: Research6969.PrefixMainDataMiddle77
section Z6969Source1755
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle77
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank30 1501, bank40 1714, bank49 2130, bank58 2054, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank126 11206, bank153 5200, bank199 7608, bank186 19684, bank175 25973, bank169 29097] i
  head := src2762
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15027, 125990, 584736, 2139818],
    ![12303, 98747, 446479, 1590545],
    ![53398/9, 429292/9, 446479, 1590545],
    ![29433/8, 232387/8, 2103940/9, 820248],
    ![63824/25, 502296/25, 313709/2, 2253001/4],
    ![72196/49, 570054/49, 2569354/25, 9012212/25],
    ![40539/50, 336161/50, 71355, 1134225/4],
    ![95180/121, 717240/121, 3226184/49, 10799932/49],
    ![95180/121, 717240/121, 116003/2, 870489/4],
    ![63754/121, 751724/147, 770661/16, 10363518/49],
    ![63754/121, 751724/147, 770661/16, 588896/3],
    ![63754/121, 605203/121, 770661/16, 9114361/64],
    ![1355575/3362, 605203/121, 770661/16, 9114361/64],
    ![1355575/3362, 7195568/1681, 1999400/49, 6760000/49],
    ![1355575/3362, 1756100/441, 4332756/121, 14470416/121],
    ![481425/1369, 1756100/441, 4332756/121, 14470416/121],
    ![929061/2738, 1756100/441, 4332756/121, 14470416/121],
    ![459151/1369, 1756100/441, 4332756/121, 14470416/121]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 20 257027 := by
  refine ⟨?_, rank154 5258, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2762⟩⟩
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
    · exact free186_1
    · exact free175_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [254263066, 330421184, 330304637, 330695863, 329380663, 331260180, 329470694, 148007347, 148015753, 148548054, 148257042, 70913668, 71985065, 90016352, 104062727, 102397073, 172034813, 223336812], [1426177, 1042288, 1042608, 1041534, 1045143, 1039986, 1044896, 2603426, 2603286, 2594424, 2599269, 5660926, 5575662, 4420309, 3789101, 3858549, 2210632, 1669609],
  ![118551646545840, 1619498228388, 204721427470, 4590627300], 138912411308266538⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,7,7,7,7,15,15,12,10,11,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 1756100/441, 4332756/121, 14470416/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle77
end Z6969Source1755

-- Source: Research6969.PrefixRescueDataMiddle77
section Z6969Source1756
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle77
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,20⟩
  bank i := ![bank236 17554, bank236 18436, bank246 20387, bank245 21920, bank252 26671, bank270 33149, bank315 50049, bank361 85238, bank332 78274, bank359 118434, bank386 125771] i
  reserve i := ![0, 1, 2, 3, 6, 10, 20, 40, 40, 65, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 20

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 17554
    · exact rank236 18436
    · exact rank246 20387
    · exact rank245 21920
    · exact rank252 26671
    · exact rank270 33149
    · exact rank315 50049
    · exact rank361 85238
    · exact rank332 78274
    · exact rank359 118434
    · exact rank386 125771
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2066⟩
    · exact ⟨_, cover2067⟩
    · exact ⟨_, cover2068⟩
    · exact ⟨_, cover2069⟩
    · exact ⟨_, cover2070⟩
    · exact ⟨_, cover2071⟩
    · exact ⟨_, cover2072⟩
    · exact ⟨_, cover2074⟩
    · exact ⟨_, cover2073⟩
    · exact ⟨_, cover2075⟩
    · exact ⟨_, cover2076⟩

def price : EarlyPrice := ⟨2, 20, 10, 85/100, 80/100, ![980299169178, 134324661943, 23460897180, 1173066230], 2782079981020738⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![11705/66, 79987/33, 214714/33, 394780/11] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle77
end Z6969Source1756

-- Source: Research6969.PrefixMiddleSaved77
section Z6969Source1757
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved77
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle77.price Lower6960.Prefix6969RescueData.Middle77.price :=
  ⟨335, 3982, 177, 2423, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle77.plan Lower6960.Prefix6969RescueData.Middle77.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 20 20 :=
  ⟨Lower6960.Prefix6969MainCases.Middle77.plan, Lower6960.Prefix6969MainCases.Middle77.price, Lower6960.Prefix6969MainCases.Middle77.valid, Lower6960.Prefix6969MainCases.Middle77.priced, Lower6960.Prefix6969MainCases.Middle77.sources,
   Lower6960.Prefix6969RescueData.Middle77.plan, Lower6960.Prefix6969RescueData.Middle77.price, Lower6960.Prefix6969RescueData.Middle77.sources, Lower6960.Prefix6969RescueData.Middle77.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved77
end Z6969Source1757

-- Source: Research6969.PrefixMainDataMiddle78
section Z6969Source1758
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle78
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 10, 16, 21, 17, 21, 41, 41, 65, 65, 76, 76, 76] i
  bank i := ![bank5 1094, bank9 1210, bank17 1319, bank24 1404, bank30 1501, bank40 1714, bank49 2130, bank58 2054, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank126 11206, bank161 5142, bank199 7608, bank162 16965, bank178 23472, bank170 28384, bank213 8827] i
  head := src2763
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15063, 125705, 584415, 2127671],
    ![12303, 98108, 887207/2, 3138135/2],
    ![53398/9, 426523/9, 887207/2, 3138135/2],
    ![29433/8, 461721/16, 696722/3, 809172],
    ![63824/25, 498959/25, 313709/2, 2253001/4],
    ![72196/49, 566291/49, 2552527/25, 8890518/25],
    ![40539/50, 668133/100, 71355, 1134225/4],
    ![95180/121, 712270/121, 3204032/49, 1522014/7],
    ![95180/121, 712270/121, 116003/2, 1522014/7],
    ![63754/121, 249202/49, 770661/16, 1460511/7],
    ![63754/121, 249202/49, 770661/16, 193648],
    ![63754/121, 600659/121, 770661/16, 9114361/64],
    ![1355575/3362, 600659/121, 770661/16, 9114361/64],
    ![1355575/3362, 7168956/1681, 8051793/196, 6610041/49],
    ![1355575/3362, 1744030/441, 4332756/121, 14470416/121],
    ![483776/1323, 1744030/441, 4332756/121, 14470416/121],
    ![939225/2738, 1744030/441, 4332756/121, 14470416/121],
    ![920087/2738, 1744030/441, 4332756/121, 14470416/121],
    ![920087/2738, 5222126/1369, 1816675/52, 1896447/16]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 21 257027 := by
  refine ⟨?_, rank154 5187, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2763⟩⟩
  · intro i; fin_cases i
    · exact free5_1
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
    · exact free161_1
    · exact free199_1
    · exact free162_1
    · exact free178_1
    · exact free170_1
    · exact free213_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [253156741, 327835046, 327884130, 328483225, 327566228, 328618384, 327927736, 150492029, 150340294, 150484178, 150382262, 72396804, 72493904, 87413784, 87490355, 100000000, 150617209, 101901537, 233302171], [1431844, 1049385, 1049250, 1047606, 1050680, 1047235, 1049130, 2562061, 2564587, 2562191, 2563888, 5542895, 5535168, 4551721, 4547855, 3959851, 2559977, 3879490, 1587568],
  ![123841458410220, 1608685549304, 209971953900, 4711149310], 139765802837446975⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,4,3,3,7,7,7,7,15,15,12,12,11,7,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 5222126/1369, 1816675/52, 1896447/16] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle78
end Z6969Source1758

-- Source: Research6969.PhysicalChecks130
section Z6969Source1759
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2080 : Request := ⟨⟨⟨1750,2442,527,20453⟩,161065121873920,975196209190⟩,4,2,1,257027,21⟩
theorem cover2080 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2080) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2081 : Request := ⟨⟨⟨2100,2930,632,22540⟩,278060332482560,2019119590628⟩,4,2,1,257027,21⟩
theorem cover2081 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2081) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2082 : Request := ⟨⟨⟨2600,3628,798,27226⟩,535425056505856,4816500515660⟩,8,2,1,257027,21⟩
theorem cover2082 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2082) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2083 : Request := ⟨⟨⟨3200,4465,963,37728⟩,983050615259136,10877088344236⟩,16,2,1,257027,21⟩
theorem cover2083 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2083) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2084 : Request := ⟨⟨⟨5700,7954,1750,61233⟩,5637370734182400,111160708353364⟩,32,2,1,257027,21⟩
theorem cover2084 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2084) 2557 2412 [2413, 2418, 2431, 2464, 2550, 2557] := triangleCover (by decide +kernel)
def src2085 : Request := ⟨⟨⟨4800,6698,1445,68286⟩,3317023033262080,55058665830093⟩,40,2,1,257027,21⟩
theorem cover2085 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2085) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2086 : Request := ⟨⟨⟨6900,9628,2077,102712⟩,9849424459857920,234966243278304⟩,65,2,1,257027,21⟩
theorem cover2086 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2086) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2087 : Request := ⟨⟨⟨10000,13955,3070,108301⟩,30428373265940480,1052683166434338⟩,65,2,1,257027,21⟩
theorem cover2087 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2087) 2557 2412 [2413, 2418, 2431, 2464, 2549, 2557] := triangleCover (by decide +kernel)
def src2088 : Request := ⟨⟨⟨1200,1674,361,12912⟩,51955677528064,215563369662⟩,0,2,1,257027,22⟩
theorem cover2088 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2088) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2089 : Request := ⟨⟨⟨1450,2023,445,14275⟩,92998964346880,466511127281⟩,1,2,1,257027,22⟩
theorem cover2089 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2089) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2090 : Request := ⟨⟨⟨1450,2023,445,14867⟩,92998964346880,466511127281⟩,2,2,1,257027,22⟩
theorem cover2090 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2090) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2091 : Request := ⟨⟨⟨1750,2442,537,17665⟩,163381988556800,989573241440⟩,4,2,1,257027,22⟩
theorem cover2091 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2091) 2557 2412 [2414, 2421, 2440, 2490, 2557] := triangleCover (by decide +kernel)
def src2092 : Request := ⟨⟨⟨2100,2930,632,21621⟩,278060332482560,2019119590628⟩,6,2,1,257027,22⟩
theorem cover2092 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2092) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2093 : Request := ⟨⟨⟨2600,3628,783,26844⟩,527755772952576,4745819470168⟩,10,2,1,257027,22⟩
theorem cover2093 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2093) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2094 : Request := ⟨⟨⟨3950,5512,1213,38818⟩,1877062482395136,25652240151764⟩,20,2,1,257027,22⟩
theorem cover2094 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2094) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2095 : Request := ⟨⟨⟨6900,9628,2077,75848⟩,9849424459857920,234966243278304⟩,50,2,1,257027,22⟩
theorem cover2095 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2095) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1759

end Merged_Z6969Pack0725

import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0729
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0724
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0730
section Merged_Z6969Pack0730

-- Source: Research6969.PrefixRescueDataMiddle91
section Z6969Source1808
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle91
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,34⟩
  bank i := ![bank156 3955, bank196 4661, bank193 4799, bank204 5546, bank204 5712, bank222 6745, bank222 7095, bank237 10275, bank254 14170, bank300 23157, bank369 58807] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 16, 25, 50, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 34

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank156 3955
    · exact rank196 4661
    · exact rank193 4799
    · exact rank204 5546
    · exact rank204 5712
    · exact rank222 6745
    · exact rank222 7095
    · exact rank237 10275
    · exact rank254 14170
    · exact rank300 23157
    · exact rank369 58807
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2218⟩
    · exact ⟨_, cover2219⟩
    · exact ⟨_, cover2220⟩
    · exact ⟨_, cover2221⟩
    · exact ⟨_, cover2222⟩
    · exact ⟨_, cover2223⟩
    · exact ⟨_, cover2224⟩
    · exact ⟨_, cover2225⟩
    · exact ⟨_, cover2226⟩
    · exact ⟨_, cover2227⟩
    · exact ⟨_, cover2228⟩

def price : EarlyPrice := ⟨2, 34, 10, 65/100, 60/100, ![779212626766, 141694470293, 34649633870, 1019125645], 805877424901575⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![7097/73, 147717/146, 255650/73, 999719/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle91
end Z6969Source1808

-- Source: Research6969.PrefixMiddleSaved91
section Z6969Source1809
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved91
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle91.price Lower6960.Prefix6969RescueData.Middle91.price :=
  ⟨335, 3524, 97, 1011, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle91.plan Lower6960.Prefix6969RescueData.Middle91.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 34 34 :=
  ⟨Lower6960.Prefix6969MainCases.Middle91.plan, Lower6960.Prefix6969MainCases.Middle91.price, Lower6960.Prefix6969MainCases.Middle91.valid, Lower6960.Prefix6969MainCases.Middle91.priced, Lower6960.Prefix6969MainCases.Middle91.sources,
   Lower6960.Prefix6969RescueData.Middle91.plan, Lower6960.Prefix6969RescueData.Middle91.price, Lower6960.Prefix6969RescueData.Middle91.sources, Lower6960.Prefix6969RescueData.Middle91.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved91
end Z6969Source1809

-- Source: Research6969.PrefixMainDataMiddle92
section Z6969Source1810
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle92
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 20, 20, 30, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank31 1491, bank37 1587, bank44 1848, bank54 2149, bank74 2799, bank81 3885, bank115 2949, bank168 3916, bank129 10859, bank161 5142, bank199 7608, bank181 21723, bank212 8810, bank170 28384] i
  head := src2777
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15596, 123588, 572757, 1967704],
    ![25417/2, 180771/2, 410431, 1399489],
    ![54680/9, 393590/9, 410431, 1399489],
    ![29433/8, 53141/2, 1925072/9, 676416],
    ![64334/25, 457262/25, 158046, 2223081/4],
    ![17323/9, 81821/6, 552359/4, 430077],
    ![18775/16, 8635, 2497648/25, 8012928/25],
    ![89110/121, 647170/121, 419116/7, 1331152/7],
    ![89110/121, 647170/121, 116003/2, 1331152/7],
    ![235552/441, 2110606/441, 2329954/49, 1331152/7],
    ![235552/441, 1999940/441, 751995/16, 8696601/64],
    ![235552/441, 1999940/441, 751995/16, 126736],
    ![33263/82, 1999940/441, 751995/16, 126736],
    ![33263/82, 6566448/1681, 1845514/49, 2937796/25],
    ![33263/82, 10880/3, 4054530/121, 197929728/1849],
    ![474397/1369, 10880/3, 4054530/121, 197929728/1849],
    ![474397/1369, 4798731/1369, 86308040/2601, 77616100/729],
    ![920087/2738, 4798731/1369, 86308040/2601, 77616100/729]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 35 257073 := by
  refine ⟨?_, rank154 4336, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2777⟩⟩
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
    · exact free81_1
    · exact free115_1
    · exact free168_1
    · exact free129_1
    · exact free161_1
    · exact free199_1
    · exact free181_1
    · exact free212_1
    · exact free170_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [239392922, 308093404, 308829578, 307465907, 307334670, 307987090, 307013133, 155448805, 155580537, 155722118, 103778402, 65539980, 61940025, 80515894, 76675803, 93359553, 121150218, 229254929], [1537075, 1150168, 1146398, 1153382, 1154054, 1150713, 1155701, 2478975, 2476782, 2474426, 3799307, 6135618, 6505008, 4956724, 5221136, 4250531, 3234863, 1620519],
  ![121693101411780, 1613077082416, 206329436100, 6213151840], 130240637108188887⟩

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
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 4798731/1369, 86308040/2601, 77616100/729] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle92
end Z6969Source1810

-- Source: Research6969.PrefixRescueDataMiddle92
section Z6969Source1811
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle92
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,35⟩
  bank i := ![bank155 3946, bank197 4487, bank193 4664, bank193 4834, bank204 5554, bank204 5903, bank223 7144, bank238 9815, bank249 15195, bank311 27356, bank377 72425] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 16, 32, 65, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 35

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank155 3946
    · exact rank197 4487
    · exact rank193 4664
    · exact rank193 4834
    · exact rank204 5554
    · exact rank204 5903
    · exact rank223 7144
    · exact rank238 9815
    · exact rank249 15195
    · exact rank311 27356
    · exact rank377 72425
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2229⟩
    · exact ⟨_, cover2230⟩
    · exact ⟨_, cover2231⟩
    · exact ⟨_, cover2232⟩
    · exact ⟨_, cover2233⟩
    · exact ⟨_, cover2234⟩
    · exact ⟨_, cover2235⟩
    · exact ⟨_, cover2236⟩
    · exact ⟨_, cover2237⟩
    · exact ⟨_, cover2238⟩
    · exact ⟨_, cover2239⟩

def price : EarlyPrice := ⟨2, 35, 10, 65/100, 70/100, ![987880910950, 176629475795, 41874965780, 1196449610], 874395096220758⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![17020/191, 179875/191, 633100/191, 2534875/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle92
end Z6969Source1811

-- Source: Research6969.PrefixMiddleSaved92
section Z6969Source1812
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved92
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle92.price Lower6960.Prefix6969RescueData.Middle92.price :=
  ⟨336, 3505, 89, 941, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle92.plan Lower6960.Prefix6969RescueData.Middle92.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 35 35 :=
  ⟨Lower6960.Prefix6969MainCases.Middle92.plan, Lower6960.Prefix6969MainCases.Middle92.price, Lower6960.Prefix6969MainCases.Middle92.valid, Lower6960.Prefix6969MainCases.Middle92.priced, Lower6960.Prefix6969MainCases.Middle92.sources,
   Lower6960.Prefix6969RescueData.Middle92.plan, Lower6960.Prefix6969RescueData.Middle92.price, Lower6960.Prefix6969RescueData.Middle92.sources, Lower6960.Prefix6969RescueData.Middle92.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved92
end Z6969Source1812

-- Source: Research6969.PrefixMainDataMiddle93
section Z6969Source1813
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle93
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 20, 23, 25, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank35 1600, bank44 1848, bank53 2196, bank42 2862, bank61 2044, bank69 3442, bank72 2320, bank95 2576, bank115 2949, bank92 3992, bank140 3403, bank130 10521, bank164 5088, bank212 8810, bank186 19684, bank174 26788, bank169 29097] i
  head := src2778
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15471, 123253, 567651, 1969636],
    ![25417/2, 89923, 408331, 1399489],
    ![54680/9, 43510, 408331, 2775185/2],
    ![29433/8, 211489/8, 1915372/9, 668616],
    ![5710/3, 40525/3, 550959/4, 428600],
    ![18775/16, 274945/32, 2485298/25, 7920528/25],
    ![86808/121, 647624/121, 2912536/49, 4822416/25],
    ![73478/121, 647624/121, 2912536/49, 4822416/25],
    ![73478/121, 647624/121, 2912536/49, 1251512/7],
    ![73478/121, 1873184/361, 2478240/49, 1251512/7],
    ![73478/121, 1873184/361, 2478240/49, 1251512/7],
    ![73478/121, 1873184/361, 2478240/49, 1251512/7],
    ![73478/121, 1988440/441, 751995/16, 8696601/64],
    ![73478/121, 1988440/441, 751995/16, 8696601/64],
    ![73478/121, 1988440/441, 751995/16, 8696601/64],
    ![33463/82, 1988440/441, 751995/16, 8696601/64],
    ![33463/82, 6562904/1681, 1843470/49, 2876416/25],
    ![33463/82, 9547237/2738, 85861790/2601, 13215881/125],
    ![481425/1369, 9547237/2738, 85861790/2601, 13215881/125],
    ![462882/1369, 9547237/2738, 85861790/2601, 13215881/125],
    ![459151/1369, 9547237/2738, 85861790/2601, 13215881/125]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 36 257073 := by
  refine ⟨?_, rank154 4286, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2778⟩⟩
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

def price : Pricing := ⟨55/100, 100/100, [237007682, 305338423, 306012196, 304705004, 306166327, 305609074, 305661345, 304833414, 164074989, 163912804, 164015985, 163927006, 68392490, 82066779, 75527604, 75238655, 92534725, 92544877, 118457497, 100000000, 219193598], [1556708, 1164277, 1160827, 1167521, 1160037, 1162891, 1162624, 1166864, 2335398, 2338097, 2336380, 2337861, 5876595, 4864533, 5300521, 5320498, 4292170, 4291658, 3310217, 3958949, 1703331],
  ![116352345690360, 1623993937252, 197274238200, 5107682300], 126972324836552457⟩

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
    · exact Pricing.height_from_critical Band.middle _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.middle _ 14 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 9547237/2738, 85861790/2601, 13215881/125] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle93
end Z6969Source1813

-- Source: Research6969.PhysicalChecks140
section Z6969Source1814
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2240 : Request := ⟨⟨⟨560,781,172,3740⟩,5388141854720,10440670587⟩,0,2,1,257073,36⟩
private theorem pass2240_2390 : (Triangular src2240) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2240_2391 : (Triangular src2240) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2240_2394 : (Triangular src2240) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2240_2402 : (Triangular src2240) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2240_2426 : (Triangular src2240) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2240_2496 : (Triangular src2240) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2240 : Cover (Triangular src2240) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2240_2390, by decide, by decide, pass2240_2391, by decide, by decide, pass2240_2394, by decide, by decide, pass2240_2402, by decide, by decide, pass2240_2426, by decide, by decide, pass2240_2496, rfl⟩
def src2241 : Request := ⟨⟨⟨560,781,172,3903⟩,5388141854720,10440670587⟩,1,2,1,257073,36⟩
private theorem pass2241_2390 : (Triangular src2241) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2241_2391 : (Triangular src2241) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2241_2394 : (Triangular src2241) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2241_2402 : (Triangular src2241) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2241_2426 : (Triangular src2241) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2241_2496 : (Triangular src2241) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2241 : Cover (Triangular src2241) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2241_2390, by decide, by decide, pass2241_2391, by decide, by decide, pass2241_2394, by decide, by decide, pass2241_2402, by decide, by decide, pass2241_2426, by decide, by decide, pass2241_2496, rfl⟩
def src2242 : Request := ⟨⟨⟨690,962,217,4494⟩,10244384358400,24434817260⟩,2,2,1,257073,36⟩
private theorem pass2242_2390 : (Triangular src2242) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2242_2391 : (Triangular src2242) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2242_2393 : (Triangular src2242) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2242_2399 : (Triangular src2242) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2242_2416 : (Triangular src2242) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2242_2464 : (Triangular src2242) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2242 : Cover (Triangular src2242) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2242_2390, by decide, by decide, pass2242_2391, by decide, by decide, pass2242_2393, by decide, by decide, pass2242_2399, by decide, by decide, pass2242_2416, by decide, by decide, pass2242_2464, rfl⟩
def src2243 : Request := ⟨⟨⟨690,962,212,4702⟩,10065769922560,23997864317⟩,3,2,1,257073,36⟩
private theorem pass2243_2390 : (Triangular src2243) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2243_2391 : (Triangular src2243) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2243_2393 : (Triangular src2243) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2243_2399 : (Triangular src2243) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2243_2416 : (Triangular src2243) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2243_2464 : (Triangular src2243) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2243 : Cover (Triangular src2243) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2243_2390, by decide, by decide, pass2243_2391, by decide, by decide, pass2243_2393, by decide, by decide, pass2243_2399, by decide, by decide, pass2243_2416, by decide, by decide, pass2243_2464, rfl⟩
def src2244 : Request := ⟨⟨⟨690,962,212,4875⟩,10065769922560,23997864317⟩,4,2,1,257073,36⟩
private theorem pass2244_2390 : (Triangular src2244) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2244_2391 : (Triangular src2244) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2244_2393 : (Triangular src2244) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2244_2399 : (Triangular src2244) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2244_2416 : (Triangular src2244) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2244_2464 : (Triangular src2244) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2244 : Cover (Triangular src2244) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2244_2390, by decide, by decide, pass2244_2391, by decide, by decide, pass2244_2393, by decide, by decide, pass2244_2399, by decide, by decide, pass2244_2416, by decide, by decide, pass2244_2464, rfl⟩
def src2245 : Request := ⟨⟨⟨825,1151,253,5733⟩,17161575202816,49010625289⟩,6,2,1,257073,36⟩
private theorem pass2245_2390 : (Triangular src2245) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2245_2391 : (Triangular src2245) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2245_2393 : (Triangular src2245) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2245_2399 : (Triangular src2245) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2245_2416 : (Triangular src2245) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2245_2463 : (Triangular src2245) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2245 : Cover (Triangular src2245) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2245_2390, by decide, by decide, pass2245_2391, by decide, by decide, pass2245_2393, by decide, by decide, pass2245_2399, by decide, by decide, pass2245_2416, by decide, by decide, pass2245_2463, rfl⟩
def src2246 : Request := ⟨⟨⟨1000,1395,307,7039⟩,30557599170560,105715278267⟩,10,2,1,257073,36⟩
private theorem pass2246_2390 : (Triangular src2246) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2246_2391 : (Triangular src2246) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2246_2393 : (Triangular src2246) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2246_2399 : (Triangular src2246) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2246_2415 : (Triangular src2246) 2415 2458 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2246_2459 : (Triangular src2246) 2459 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2246 : Cover (Triangular src2246) 2534 2390 [2390,2392,2398,2414,2458,2534] := by
  exact ⟨by decide, by decide, pass2246_2390, by decide, by decide, pass2246_2391, by decide, by decide, pass2246_2393, by decide, by decide, pass2246_2399, by decide, by decide, pass2246_2415, by decide, by decide, pass2246_2459, rfl⟩
def src2247 : Request := ⟨⟨⟨1750,2441,551,12100⟩,166595992223744,1008217465165⟩,25,2,1,257073,36⟩
private theorem pass2247_2390 : (Triangular src2247) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2247_2391 : (Triangular src2247) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2247_2393 : (Triangular src2247) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2247_2399 : (Triangular src2247) 2399 2413 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2247_2414 : (Triangular src2247) 2414 2453 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2247_2454 : (Triangular src2247) 2454 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2247 : Cover (Triangular src2247) 2534 2390 [2390,2392,2398,2413,2453,2534] := by
  exact ⟨by decide, by decide, pass2247_2390, by decide, by decide, pass2247_2391, by decide, by decide, pass2247_2393, by decide, by decide, pass2247_2399, by decide, by decide, pass2247_2414, by decide, by decide, pass2247_2454, rfl⟩
def src2248 : Request := ⟨⟨⟨2600,3627,819,17637⟩,546063062138880,4910333421859⟩,40,2,1,257073,36⟩
private theorem pass2248_2390 : (Triangular src2248) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2248_2391 : (Triangular src2248) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2248_2393 : (Triangular src2248) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2248_2398 : (Triangular src2248) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2248_2411 : (Triangular src2248) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2248_2446 : (Triangular src2248) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2248 : Cover (Triangular src2248) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass2248_2390, by decide, by decide, pass2248_2391, by decide, by decide, pass2248_2393, by decide, by decide, pass2248_2398, by decide, by decide, pass2248_2411, by decide, by decide, pass2248_2446, rfl⟩
def src2249 : Request := ⟨⟨⟨5700,7951,1796,40426⟩,5749327563587584,113288194826317⟩,110,2,1,257073,36⟩
private theorem pass2249_2390 : (Triangular src2249) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2249_2391 : (Triangular src2249) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2249_2393 : (Triangular src2249) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2249_2398 : (Triangular src2249) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2249_2411 : (Triangular src2249) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2249_2445 : (Triangular src2249) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2249_2533 : (Triangular src2249) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2249 : Cover (Triangular src2249) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2249_2390, by decide, by decide, pass2249_2391, by decide, by decide, pass2249_2393, by decide, by decide, pass2249_2398, by decide, by decide, pass2249_2411, by decide, by decide, pass2249_2445, by decide, by decide, pass2249_2533, rfl⟩
def src2250 : Request := ⟨⟨⟨10000,13950,3070,70265⟩,30428373265940480,1051468979452278⟩,190,2,1,257073,36⟩
private theorem pass2250_2390 : (Triangular src2250) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2250_2391 : (Triangular src2250) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2250_2393 : (Triangular src2250) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2250_2398 : (Triangular src2250) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2250_2411 : (Triangular src2250) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2250_2445 : (Triangular src2250) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2250_2532 : (Triangular src2250) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2250 : Cover (Triangular src2250) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2250_2390, by decide, by decide, pass2250_2391, by decide, by decide, pass2250_2393, by decide, by decide, pass2250_2398, by decide, by decide, pass2250_2411, by decide, by decide, pass2250_2445, by decide, by decide, pass2250_2532, rfl⟩
def src2251 : Request := ⟨⟨⟨470,655,144,3318⟩,3184589537280,5168862572⟩,0,2,1,257073,37⟩
private theorem pass2251_2390 : (Triangular src2251) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2251_2391 : (Triangular src2251) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2251_2394 : (Triangular src2251) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2251_2403 : (Triangular src2251) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2251_2430 : (Triangular src2251) 2430 2510 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2251_2511 : (Triangular src2251) 2511 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2251 : Cover (Triangular src2251) 2534 2390 [2390,2393,2402,2429,2510,2534] := by
  exact ⟨by decide, by decide, pass2251_2390, by decide, by decide, pass2251_2391, by decide, by decide, pass2251_2394, by decide, by decide, pass2251_2403, by decide, by decide, pass2251_2430, by decide, by decide, pass2251_2511, rfl⟩
def src2252 : Request := ⟨⟨⟨560,781,172,3803⟩,5388141854720,10440670587⟩,1,2,1,257073,37⟩
private theorem pass2252_2390 : (Triangular src2252) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2252_2391 : (Triangular src2252) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2252_2394 : (Triangular src2252) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2252_2402 : (Triangular src2252) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2252_2426 : (Triangular src2252) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2252_2496 : (Triangular src2252) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2252 : Cover (Triangular src2252) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2252_2390, by decide, by decide, pass2252_2391, by decide, by decide, pass2252_2394, by decide, by decide, pass2252_2402, by decide, by decide, pass2252_2426, by decide, by decide, pass2252_2496, rfl⟩
def src2253 : Request := ⟨⟨⟨560,781,172,3974⟩,5388141854720,10440670587⟩,2,2,1,257073,37⟩
private theorem pass2253_2390 : (Triangular src2253) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2253_2391 : (Triangular src2253) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2253_2394 : (Triangular src2253) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2253_2402 : (Triangular src2253) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2253_2426 : (Triangular src2253) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2253_2496 : (Triangular src2253) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2253 : Cover (Triangular src2253) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2253_2390, by decide, by decide, pass2253_2391, by decide, by decide, pass2253_2394, by decide, by decide, pass2253_2402, by decide, by decide, pass2253_2426, by decide, by decide, pass2253_2496, rfl⟩
def src2254 : Request := ⟨⟨⟨690,962,208,4724⟩,9921631092736,23645774460⟩,3,2,1,257073,37⟩
private theorem pass2254_2390 : (Triangular src2254) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2254_2391 : (Triangular src2254) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2254_2394 : (Triangular src2254) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2254_2402 : (Triangular src2254) 2402 2424 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2254_2425 : (Triangular src2254) 2425 2490 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2254_2491 : (Triangular src2254) 2491 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2254 : Cover (Triangular src2254) 2534 2390 [2390,2393,2401,2424,2490,2534] := by
  exact ⟨by decide, by decide, pass2254_2390, by decide, by decide, pass2254_2391, by decide, by decide, pass2254_2394, by decide, by decide, pass2254_2402, by decide, by decide, pass2254_2425, by decide, by decide, pass2254_2491, rfl⟩
def src2255 : Request := ⟨⟨⟨690,962,212,4745⟩,10065769922560,23997864317⟩,4,2,1,257073,37⟩
private theorem pass2255_2390 : (Triangular src2255) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2255_2391 : (Triangular src2255) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2255_2393 : (Triangular src2255) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2255_2399 : (Triangular src2255) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2255_2416 : (Triangular src2255) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2255_2464 : (Triangular src2255) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2255 : Cover (Triangular src2255) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2255_2390, by decide, by decide, pass2255_2391, by decide, by decide, pass2255_2393, by decide, by decide, pass2255_2399, by decide, by decide, pass2255_2416, by decide, by decide, pass2255_2464, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1814

-- Source: Research6969.PrefixRescueDataMiddle93
section Z6969Source1815
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle93
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,36⟩
  bank i := ![bank156 3740, bank156 3903, bank194 4494, bank193 4702, bank193 4875, bank204 5733, bank222 7039, bank243 12100, bank268 17637, bank341 40426, bank377 70265] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 40, 110, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 36

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank156 3740
    · exact rank156 3903
    · exact rank194 4494
    · exact rank193 4702
    · exact rank193 4875
    · exact rank204 5733
    · exact rank222 7039
    · exact rank243 12100
    · exact rank268 17637
    · exact rank341 40426
    · exact rank377 70265
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2240⟩
    · exact ⟨_, cover2241⟩
    · exact ⟨_, cover2242⟩
    · exact ⟨_, cover2243⟩
    · exact ⟨_, cover2244⟩
    · exact ⟨_, cover2245⟩
    · exact ⟨_, cover2246⟩
    · exact ⟨_, cover2247⟩
    · exact ⟨_, cover2248⟩
    · exact ⟨_, cover2249⟩
    · exact ⟨_, cover2250⟩

def price : EarlyPrice := ⟨2, 36, 10, 65/100, 70/100, ![985801718785, 180027773315, 43071390830, 1196449610], 857694983941190⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![3249/37, 180785/191, 367088/111, 485112/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle93
end Z6969Source1815

-- Source: Research6969.PrefixMiddleSaved93
section Z6969Source1816
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved93
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle93.price Lower6960.Prefix6969RescueData.Middle93.price :=
  ⟨335, 3486, 87, 946, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle93.plan Lower6960.Prefix6969RescueData.Middle93.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133605 _ (by norm_num)]; decide +kernel

def data : Case 2 36 36 :=
  ⟨Lower6960.Prefix6969MainCases.Middle93.plan, Lower6960.Prefix6969MainCases.Middle93.price, Lower6960.Prefix6969MainCases.Middle93.valid, Lower6960.Prefix6969MainCases.Middle93.priced, Lower6960.Prefix6969MainCases.Middle93.sources,
   Lower6960.Prefix6969RescueData.Middle93.plan, Lower6960.Prefix6969RescueData.Middle93.price, Lower6960.Prefix6969RescueData.Middle93.sources, Lower6960.Prefix6969RescueData.Middle93.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved93
end Z6969Source1816

-- Source: Research6969.PrefixMainDataMiddle94
section Z6969Source1817
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle94
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 20, 23, 25, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank35 1600, bank44 1848, bank53 2196, bank42 2862, bank61 2044, bank69 3442, bank72 2320, bank95 2576, bank115 2949, bank92 3992, bank140 3403, bank130 10521, bank164 5088, bank212 8810, bank186 19684, bank174 26788, bank169 29097] i
  head := src2779
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15471, 123109, 566835, 1963396],
    ![25417/2, 89479, 406315, 1399489],
    ![54680/9, 129890/3, 406315, 2744105/2],
    ![29433/8, 210457/8, 1906060/9, 661128],
    ![5710/3, 40325/3, 548247/4, 423800],
    ![18775/16, 273625/32, 2473442/25, 7831824/25],
    ![86808/121, 644552/121, 2898904/49, 4822416/25],
    ![73478/121, 644552/121, 2898904/49, 4822416/25],
    ![73478/121, 644552/121, 2898904/49, 1237496/7],
    ![73478/121, 1865312/361, 2478240/49, 1237496/7],
    ![73478/121, 1865312/361, 2478240/49, 1237496/7],
    ![73478/121, 1865312/361, 2478240/49, 1237496/7],
    ![73478/121, 1977400/441, 751995/16, 8696601/64],
    ![73478/121, 1977400/441, 751995/16, 8696601/64],
    ![73478/121, 1977400/441, 751995/16, 8696601/64],
    ![33463/82, 1977400/441, 751995/16, 8696601/64],
    ![33463/82, 6528152/1681, 1833822/49, 2876416/25],
    ![33463/82, 9499021/2738, 85433390/2601, 13067873/125],
    ![481425/1369, 9499021/2738, 85433390/2601, 13067873/125],
    ![462882/1369, 9499021/2738, 85433390/2601, 13067873/125],
    ![459151/1369, 9499021/2738, 85433390/2601, 13067873/125]]

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

theorem sources : plan.Sources 2390 (Band.middle).last Prefix6969MiddleHelper.helperBank 128536 2 37 257073 := by
  refine ⟨?_, rank154 4238, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2779⟩⟩
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

def price : Pricing := ⟨55/100, 100/100, [236039666, 303117202, 304038823, 304554303, 304989750, 303820617, 304841041, 306069707, 163168031, 162975809, 163074446, 162952896, 81726301, 81725991, 76892187, 79006931, 92089240, 92075016, 118349277, 100000000, 218987532], [1564675, 1175653, 1170933, 1168293, 1166063, 1172051, 1166825, 1160532, 2350493, 2353693, 2352051, 2354074, 4884773, 4884791, 5206176, 5059967, 4314659, 4315377, 3313246, 3958949, 1705027],
  ![116242961736240, 1624217487228, 197088778800, 5135298630], 126205451429494142⟩

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
    · exact Pricing.height_from_critical Band.middle _ 14 _
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

theorem final_cap : plan.history plan.last = ![459151/1369, 9499021/2738, 85433390/2601, 13067873/125] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle94
end Z6969Source1817

-- Source: Research6969.PhysicalChecks141
section Z6969Source1818
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2256 : Request := ⟨⟨⟨825,1151,253,5935⟩,17161575202816,49010625289⟩,8,2,1,257073,37⟩
private theorem pass2256_2390 : (Triangular src2256) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2256_2391 : (Triangular src2256) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2256_2393 : (Triangular src2256) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2256_2399 : (Triangular src2256) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2256_2416 : (Triangular src2256) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2256_2463 : (Triangular src2256) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2256 : Cover (Triangular src2256) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2256_2390, by decide, by decide, pass2256_2391, by decide, by decide, pass2256_2393, by decide, by decide, pass2256_2399, by decide, by decide, pass2256_2416, by decide, by decide, pass2256_2463, rfl⟩
def src2257 : Request := ⟨⟨⟨1200,1674,368,8586⟩,52718727069696,218807905514⟩,16,2,1,257073,37⟩
private theorem pass2257_2390 : (Triangular src2257) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2257_2391 : (Triangular src2257) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2257_2393 : (Triangular src2257) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2257_2399 : (Triangular src2257) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2257_2415 : (Triangular src2257) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2257_2458 : (Triangular src2257) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2257 : Cover (Triangular src2257) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2257_2390, by decide, by decide, pass2257_2391, by decide, by decide, pass2257_2393, by decide, by decide, pass2257_2399, by decide, by decide, pass2257_2415, by decide, by decide, pass2257_2458, rfl⟩
def src2258 : Request := ⟨⟨⟨2100,2929,662,14136⟩,288013660979200,2090961110089⟩,32,2,1,257073,37⟩
private theorem pass2258_2390 : (Triangular src2258) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2258_2391 : (Triangular src2258) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2258_2393 : (Triangular src2258) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2258_2398 : (Triangular src2258) 2398 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2258_2412 : (Triangular src2258) 2412 2448 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2258_2449 : (Triangular src2258) 2449 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2258 : Cover (Triangular src2258) 2534 2390 [2390,2392,2397,2411,2448,2534] := by
  exact ⟨by decide, by decide, pass2258_2390, by decide, by decide, pass2258_2391, by decide, by decide, pass2258_2393, by decide, by decide, pass2258_2398, by decide, by decide, pass2258_2412, by decide, by decide, pass2258_2449, rfl⟩
def src2259 : Request := ⟨⟨⟨5700,7951,1796,39314⟩,5749327563587584,113288194826317⟩,110,2,1,257073,37⟩
private theorem pass2259_2390 : (Triangular src2259) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2259_2391 : (Triangular src2259) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2259_2393 : (Triangular src2259) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2259_2398 : (Triangular src2259) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2259_2411 : (Triangular src2259) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2259_2445 : (Triangular src2259) 2445 2532 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2259_2533 : (Triangular src2259) 2533 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2259 : Cover (Triangular src2259) 2534 2390 [2390,2392,2397,2410,2444,2532,2534] := by
  exact ⟨by decide, by decide, pass2259_2390, by decide, by decide, pass2259_2391, by decide, by decide, pass2259_2393, by decide, by decide, pass2259_2398, by decide, by decide, pass2259_2411, by decide, by decide, pass2259_2445, by decide, by decide, pass2259_2533, rfl⟩
def src2260 : Request := ⟨⟨⟨6900,9625,2174,49346⟩,10196763128627200,243221551977378⟩,145,2,1,257073,37⟩
private theorem pass2260_2390 : (Triangular src2260) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2260_2391 : (Triangular src2260) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2260_2393 : (Triangular src2260) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2260_2398 : (Triangular src2260) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2260_2411 : (Triangular src2260) 2411 2444 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2260_2445 : (Triangular src2260) 2445 2531 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2260_2532 : (Triangular src2260) 2532 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2260 : Cover (Triangular src2260) 2534 2390 [2390,2392,2397,2410,2444,2531,2534] := by
  exact ⟨by decide, by decide, pass2260_2390, by decide, by decide, pass2260_2391, by decide, by decide, pass2260_2393, by decide, by decide, pass2260_2398, by decide, by decide, pass2260_2411, by decide, by decide, pass2260_2445, by decide, by decide, pass2260_2532, rfl⟩
def src2261 : Request := ⟨⟨⟨10000,13950,3150,67261⟩,31027650042265600,1072717072025530⟩,190,2,1,257073,37⟩
private theorem pass2261_2390 : (Triangular src2261) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2261_2391 : (Triangular src2261) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2261_2393 : (Triangular src2261) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2261_2398 : (Triangular src2261) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2261_2411 : (Triangular src2261) 2411 2443 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2261_2444 : (Triangular src2261) 2444 2528 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2261_2529 : (Triangular src2261) 2529 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2261 : Cover (Triangular src2261) 2534 2390 [2390,2392,2397,2410,2443,2528,2534] := by
  exact ⟨by decide, by decide, pass2261_2390, by decide, by decide, pass2261_2391, by decide, by decide, pass2261_2393, by decide, by decide, pass2261_2398, by decide, by decide, pass2261_2411, by decide, by decide, pass2261_2444, by decide, by decide, pass2261_2529, rfl⟩
def src2262 : Request := ⟨⟨⟨470,655,144,3234⟩,3184589537280,5168862572⟩,0,2,1,257073,38⟩
private theorem pass2262_2390 : (Triangular src2262) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2262_2391 : (Triangular src2262) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2262_2394 : (Triangular src2262) 2394 2402 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2262_2403 : (Triangular src2262) 2403 2429 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2262_2430 : (Triangular src2262) 2430 2510 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2262_2511 : (Triangular src2262) 2511 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2262 : Cover (Triangular src2262) 2534 2390 [2390,2393,2402,2429,2510,2534] := by
  exact ⟨by decide, by decide, pass2262_2390, by decide, by decide, pass2262_2391, by decide, by decide, pass2262_2394, by decide, by decide, pass2262_2403, by decide, by decide, pass2262_2430, by decide, by decide, pass2262_2511, rfl⟩
def src2263 : Request := ⟨⟨⟨560,781,169,3813⟩,5316921262080,10299257375⟩,1,2,1,257073,38⟩
private theorem pass2263_2390 : (Triangular src2263) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2263_2391 : (Triangular src2263) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2263_2394 : (Triangular src2263) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2263_2402 : (Triangular src2263) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2263_2426 : (Triangular src2263) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2263_2496 : (Triangular src2263) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2263 : Cover (Triangular src2263) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2263_2390, by decide, by decide, pass2263_2391, by decide, by decide, pass2263_2394, by decide, by decide, pass2263_2402, by decide, by decide, pass2263_2426, by decide, by decide, pass2263_2496, rfl⟩
def src2264 : Request := ⟨⟨⟨560,781,172,3872⟩,5388141854720,10440670587⟩,2,2,1,257073,38⟩
private theorem pass2264_2390 : (Triangular src2264) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2264_2391 : (Triangular src2264) 2391 2393 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2264_2394 : (Triangular src2264) 2394 2401 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2264_2402 : (Triangular src2264) 2402 2425 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2264_2426 : (Triangular src2264) 2426 2495 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2264_2496 : (Triangular src2264) 2496 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2264 : Cover (Triangular src2264) 2534 2390 [2390,2393,2401,2425,2495,2534] := by
  exact ⟨by decide, by decide, pass2264_2390, by decide, by decide, pass2264_2391, by decide, by decide, pass2264_2394, by decide, by decide, pass2264_2402, by decide, by decide, pass2264_2426, by decide, by decide, pass2264_2496, rfl⟩
def src2265 : Request := ⟨⟨⟨690,962,212,4489⟩,10065769922560,23997864317⟩,3,2,1,257073,38⟩
private theorem pass2265_2390 : (Triangular src2265) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2265_2391 : (Triangular src2265) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2265_2393 : (Triangular src2265) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2265_2399 : (Triangular src2265) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2265_2416 : (Triangular src2265) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2265_2464 : (Triangular src2265) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2265 : Cover (Triangular src2265) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2265_2390, by decide, by decide, pass2265_2391, by decide, by decide, pass2265_2393, by decide, by decide, pass2265_2399, by decide, by decide, pass2265_2416, by decide, by decide, pass2265_2464, rfl⟩
def src2266 : Request := ⟨⟨⟨690,962,208,4772⟩,9921631092736,23645774460⟩,4,2,1,257073,38⟩
private theorem pass2266_2390 : (Triangular src2266) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2266_2391 : (Triangular src2266) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2266_2393 : (Triangular src2266) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2266_2399 : (Triangular src2266) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2266_2416 : (Triangular src2266) 2416 2464 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2266_2465 : (Triangular src2266) 2465 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2266 : Cover (Triangular src2266) 2534 2390 [2390,2392,2398,2415,2464,2534] := by
  exact ⟨by decide, by decide, pass2266_2390, by decide, by decide, pass2266_2391, by decide, by decide, pass2266_2393, by decide, by decide, pass2266_2399, by decide, by decide, pass2266_2416, by decide, by decide, pass2266_2465, rfl⟩
def src2267 : Request := ⟨⟨⟨690,962,212,4974⟩,10065769922560,23997864317⟩,6,2,1,257073,38⟩
private theorem pass2267_2390 : (Triangular src2267) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2267_2391 : (Triangular src2267) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2267_2393 : (Triangular src2267) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2267_2399 : (Triangular src2267) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2267_2416 : (Triangular src2267) 2416 2463 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2267_2464 : (Triangular src2267) 2464 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2267 : Cover (Triangular src2267) 2534 2390 [2390,2392,2398,2415,2463,2534] := by
  exact ⟨by decide, by decide, pass2267_2390, by decide, by decide, pass2267_2391, by decide, by decide, pass2267_2393, by decide, by decide, pass2267_2399, by decide, by decide, pass2267_2416, by decide, by decide, pass2267_2464, rfl⟩
def src2268 : Request := ⟨⟨⟨825,1151,253,5778⟩,17161575202816,49010625289⟩,8,2,1,257073,38⟩
private theorem pass2268_2390 : (Triangular src2268) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2268_2391 : (Triangular src2268) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2268_2393 : (Triangular src2268) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2268_2399 : (Triangular src2268) 2399 2415 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2268_2416 : (Triangular src2268) 2416 2462 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2268_2463 : (Triangular src2268) 2463 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2268 : Cover (Triangular src2268) 2534 2390 [2390,2392,2398,2415,2462,2534] := by
  exact ⟨by decide, by decide, pass2268_2390, by decide, by decide, pass2268_2391, by decide, by decide, pass2268_2393, by decide, by decide, pass2268_2399, by decide, by decide, pass2268_2416, by decide, by decide, pass2268_2463, rfl⟩
def src2269 : Request := ⟨⟨⟨1200,1674,368,8362⟩,52718727069696,218807905514⟩,16,2,1,257073,38⟩
private theorem pass2269_2390 : (Triangular src2269) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2269_2391 : (Triangular src2269) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2269_2393 : (Triangular src2269) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2269_2399 : (Triangular src2269) 2399 2414 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2269_2415 : (Triangular src2269) 2415 2457 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2269_2458 : (Triangular src2269) 2458 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2269 : Cover (Triangular src2269) 2534 2390 [2390,2392,2398,2414,2457,2534] := by
  exact ⟨by decide, by decide, pass2269_2390, by decide, by decide, pass2269_2391, by decide, by decide, pass2269_2393, by decide, by decide, pass2269_2399, by decide, by decide, pass2269_2415, by decide, by decide, pass2269_2458, rfl⟩
def src2270 : Request := ⟨⟨⟨1750,2441,551,11522⟩,166595992223744,1008217465165⟩,25,2,1,257073,38⟩
private theorem pass2270_2390 : (Triangular src2270) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2270_2391 : (Triangular src2270) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2270_2393 : (Triangular src2270) 2393 2398 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2270_2399 : (Triangular src2270) 2399 2413 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2270_2414 : (Triangular src2270) 2414 2453 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2270_2454 : (Triangular src2270) 2454 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2270 : Cover (Triangular src2270) 2534 2390 [2390,2392,2398,2413,2453,2534] := by
  exact ⟨by decide, by decide, pass2270_2390, by decide, by decide, pass2270_2391, by decide, by decide, pass2270_2393, by decide, by decide, pass2270_2399, by decide, by decide, pass2270_2414, by decide, by decide, pass2270_2454, rfl⟩
def src2271 : Request := ⟨⟨⟨2600,3627,819,18408⟩,546063062138880,4910333421859⟩,50,2,1,257073,38⟩
private theorem pass2271_2390 : (Triangular src2271) 2390 2390 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2271_2391 : (Triangular src2271) 2391 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2271_2393 : (Triangular src2271) 2393 2397 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2271_2398 : (Triangular src2271) 2398 2410 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2271_2411 : (Triangular src2271) 2411 2445 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass2271_2446 : (Triangular src2271) 2446 2534 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover2271 : Cover (Triangular src2271) 2534 2390 [2390,2392,2397,2410,2445,2534] := by
  exact ⟨by decide, by decide, pass2271_2390, by decide, by decide, pass2271_2391, by decide, by decide, pass2271_2393, by decide, by decide, pass2271_2398, by decide, by decide, pass2271_2411, by decide, by decide, pass2271_2446, rfl⟩
end Research6969.PhysicalCatalogue
end Z6969Source1818

-- Source: Research6969.PrefixRescueDataMiddle94
section Z6969Source1819
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle94
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,37⟩
  bank i := ![bank142 3318, bank156 3803, bank156 3974, bank192 4724, bank193 4745, bank204 5935, bank228 8586, bank250 14136, bank341 39314, bank378 67261, bank354 49346] i
  reserve i := ![0, 1, 2, 3, 4, 8, 16, 32, 110, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257073
  seedFloor := 37

theorem sources : plan.Sources 2390 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 3318
    · exact rank156 3803
    · exact rank156 3974
    · exact rank192 4724
    · exact rank193 4745
    · exact rank204 5935
    · exact rank228 8586
    · exact rank250 14136
    · exact rank341 39314
    · exact rank378 67261
    · exact rank354 49346
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2251⟩
    · exact ⟨_, cover2252⟩
    · exact ⟨_, cover2253⟩
    · exact ⟨_, cover2254⟩
    · exact ⟨_, cover2255⟩
    · exact ⟨_, cover2256⟩
    · exact ⟨_, cover2257⟩
    · exact ⟨_, cover2258⟩
    · exact ⟨_, cover2259⟩
    · exact ⟨_, cover2261⟩
    · exact ⟨_, cover2260⟩

def price : EarlyPrice := ⟨2, 37, 10, 65/100, 60/100, ![969868980585, 181943596703, 45421377750, 1227627450], 792723676931053⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![11799/146, 64892/73, 454817/146, 912901/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle94
end Z6969Source1819

end Merged_Z6969Pack0730

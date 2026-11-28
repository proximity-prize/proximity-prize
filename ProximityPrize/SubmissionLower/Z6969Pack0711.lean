import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0700
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice
import ProximityPrize.SubmissionLower.Z6969FastCeil

set_option Elab.async false

-- merged module Z6969Pack0701
section Merged_Z6969Pack0701

-- Source: Research6969.PrefixMainDataCubicSingletons17
section Z6969Source1476
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons17
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 16, 21, 41, 40, 65, 76, 76, 76] i
  bank i := ![bank5 1462, bank13 1553, bank18 1703, bank24 1838, bank29 1976, bank35 2061, bank44 2409, bank54 2755, bank65 3612, bank84 5564, bank95 3103, bank137 3540, bank126 26574, bank149 6281, bank199 9241, bank212 10770, bank180 62680, bank170 227095] i
  head := src1406
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15218, 163103, 758640, 3591228],
    ![25417/2, 124888, 567101, 4943199/2],
    ![54680/9, 544150/9, 567101, 4943199/2],
    ![29433/8, 293099/8, 2653940/9, 3900236/3],
    ![63052/25, 628756/25, 205504, 976144],
    ![5710/3, 111445/6, 189363, 6560163/8],
    ![18775/16, 189915/16, 396682/3, 15335694/25],
    ![89110/121, 882140/121, 3998464/49, 17538330/49],
    ![89110/121, 882140/121, 3998464/49, 17538330/49],
    ![63754/121, 428492/63, 543881/8, 17538330/49],
    ![63754/121, 428492/63, 543881/8, 3292283/12],
    ![63754/121, 722484/121, 252225/4, 1001584/5],
    ![1355575/3362, 722484/121, 252225/4, 1001584/5],
    ![1355575/3362, 267953/50, 4814899/98, 1001584/5],
    ![1355575/3362, 6388600/1323, 10525499/242, 85396081/484],
    ![1355575/3362, 12802797/2738, 4423755/104, 85396081/484],
    ![25627/74, 12802797/2738, 4423755/104, 85396081/484],
    ![920087/2738, 12802797/2738, 4423755/104, 85396081/484]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 21 385979 := by
  refine ⟨?_, rank154 6366, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1406⟩⟩
  · intro i; fin_cases i
    · exact free5_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free29_0
    · exact free35_0
    · exact free44_0
    · exact free54_0
    · exact free65_0
    · exact free84_0
    · exact free95_0
    · exact free137_0
    · exact free126_0
    · exact free149_0
    · exact free199_0
    · exact free212_0
    · exact free180_0
    · exact free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [324034594, 323819061, 322550678, 322929581, 322940475, 322263040, 322342300, 146144852, 146034675, 144604037, 143594103, 71257922, 67523490, 84871996, 95685823, 95595376, 148967944, 232016961], [1067604, 1068706, 1075197, 1073258, 1073202, 1076668, 1076263, 2635797, 2638213, 2669586, 2691734, 5627374, 5950280, 4693716, 4137645, 4141463, 2584607, 1596403],
  ![123159243238020, 1609159491744, 208815264900, 4927254500], 175584581098239968⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,8,8,8,8,15,16,13,11,11,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 12802797/2738, 4423755/104, 85396081/484] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons17
end Z6969Source1476

-- Source: Research6969.PrefixRescueDataCubicSingletons17
section Z6969Source1477
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons17
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,21⟩
  bank i := ![bank221 17590, bank221 19788, bank221 22261, bank228 22261, bank227 25043, bank237 31694, bank271 64247, bank346 130242, bank355 535271, bank382 208621, bank367 3000000] i
  reserve i := ![0, 1, 2, 3, 4, 8, 25, 65, 110, 110, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 21

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 17590
    · exact rank221 19788
    · exact rank221 22261
    · exact rank228 22261
    · exact rank227 25043
    · exact rank237 31694
    · exact rank271 64247
    · exact rank346 130242
    · exact rank355 535271
    · exact rank382 208621
    · exact rank367 3000000
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover863⟩
    · exact ⟨_, cover864⟩
    · exact ⟨_, cover865⟩
    · exact ⟨_, cover866⟩
    · exact ⟨_, cover867⟩
    · exact ⟨_, cover868⟩
    · exact ⟨_, cover870⟩
    · exact ⟨_, cover872⟩
    · exact ⟨_, cover873⟩
    · exact ⟨_, cover874⟩
    · exact ⟨_, cover875⟩

def price : EarlyPrice := ⟨3, 21, 10, 80/100, 70/100, ![24525456000000, 2410017555312, 24607207520, 2343564930], 11529417713752482⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16575/146, 271831/111, 306292/37, 1460347/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons17
end Z6969Source1477

-- Source: Research6969.PrefixNearSavedCubicSingletons17
section Z6969Source1478
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons17
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨336,4675,113,2448,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons17.plan Lower6960.Prefix6969RescueData.CubicSingletons17.plan Lower6960.Prefix6969RescueData.CubicSingletons17.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 21 21 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons17.plan, Lower6960.Prefix6969MainCases.CubicSingletons17.price, Lower6960.Prefix6969MainCases.CubicSingletons17.valid, Lower6960.Prefix6969MainCases.CubicSingletons17.priced, Lower6960.Prefix6969MainCases.CubicSingletons17.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons17.plan, Lower6960.Prefix6969RescueData.CubicSingletons17.price, Lower6960.Prefix6969RescueData.CubicSingletons17.sources, Lower6960.Prefix6969RescueData.CubicSingletons17.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 217175699752731019 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons17
end Z6969Source1478

-- Source: Research6969.PrefixMainDataCubicSingletons18
section Z6969Source1479
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons18
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 16, 23, 21, 41, 40, 65, 76, 76, 76] i
  bank i := ![bank5 1462, bank13 1553, bank18 1703, bank24 1838, bank29 1976, bank35 2061, bank44 2409, bank54 2755, bank65 3612, bank95 3103, bank92 5432, bank137 3540, bank126 26574, bank149 6281, bank199 9241, bank180 62680, bank212 10770, bank170 227095] i
  head := src1407
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15294, 162728, 756735, 3491428],
    ![25417/2, 496555/4, 563699, 9760605/4],
    ![54680/9, 540910/9, 563699, 9760605/4],
    ![29433/8, 582715/16, 2638226/9, 3850610/3],
    ![63052/25, 125006/5, 205504, 976144],
    ![5710/3, 55385/3, 1505751/8, 12953385/16],
    ![18775/16, 755205/64, 396682/3, 3028113/5],
    ![89110/121, 876875/121, 3974650/49, 17315175/49],
    ![89110/121, 876875/121, 3974650/49, 17315175/49],
    ![89110/121, 876875/121, 673351/9, 6500785/24],
    ![21715/32, 876875/121, 145985/2, 6500785/24],
    ![21715/32, 717300/121, 252225/4, 197768],
    ![1355575/3362, 717300/121, 252225/4, 197768],
    ![1355575/3362, 425987/80, 9568967/196, 197768],
    ![1355575/3362, 6347290/1323, 10525499/242, 85396081/484],
    ![25627/74, 6347290/1323, 10525499/242, 85396081/484],
    ![25627/74, 18585/4, 114294705/2704, 236913075/1352],
    ![920087/2738, 18585/4, 114294705/2704, 236913075/1352]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 22 385979 := by
  refine ⟨?_, rank154 6285, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1407⟩⟩
  · intro i; fin_cases i
    · exact free5_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free29_0
    · exact free35_0
    · exact free44_0
    · exact free54_0
    · exact free65_0
    · exact free95_0
    · exact free92_0
    · exact free137_0
    · exact free126_0
    · exact free149_0
    · exact free199_0
    · exact free180_0
    · exact free212_0
    · exact free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [322729996, 321350307, 321600264, 322182507, 321551057, 321074936, 321472927, 161704338, 161777745, 103682379, 78611255, 75186064, 67289685, 84235857, 97247799, 97825452, 148524566, 231678753], [1074279, 1081339, 1080060, 1077080, 1080312, 1082748, 1080711, 2372801, 2371580, 3800074, 5082922, 5319528, 5971473, 4731498, 4071707, 4047322, 2591980, 1599184],
  ![122979715667460, 1609525027092, 208510877700, 4844262710], 174774842422431040⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,7,7,11,14,14,16,13,11,11,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 18585/4, 114294705/2704, 236913075/1352] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons18
end Z6969Source1479

-- Source: Research6969.PhysicalChecks073
section Z6969Source1480
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src879 : Request := ⟨⟨⟨1200,1674,368,19788⟩,52718727069696,218807905514⟩,3,3,1,385979,22⟩
theorem cover879 : PhysicalWindow.Cover (PhysicalWindow.Triangular src879) 2411 2314 [2320, 2340, 2398, 2411] := triangleCover (by decide +kernel)
def src880 : Request := ⟨⟨⟨1200,1674,368,22261⟩,52718727069696,218807905514⟩,4,3,1,385979,22⟩
theorem cover880 : PhysicalWindow.Cover (PhysicalWindow.Triangular src880) 2411 2314 [2324, 2356, 2411] := triangleCover (by decide +kernel)
def src881 : Request := ⟨⟨⟨1450,2023,445,28173⟩,92998964346880,466511127281⟩,8,3,1,385979,22⟩
theorem cover881 : PhysicalWindow.Cover (PhysicalWindow.Triangular src881) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src883 : Request := ⟨⟨⟨2600,3628,798,57109⟩,535425056505856,4816500515660⟩,25,3,1,385979,22⟩
theorem cover883 : PhysicalWindow.Cover (PhysicalWindow.Triangular src883) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src885 : Request := ⟨⟨⟨5700,7953,1750,115771⟩,5637370734182400,111115710437454⟩,65,3,1,385979,22⟩
theorem cover885 : PhysicalWindow.Cover (PhysicalWindow.Triangular src885) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src886 : Request := ⟨⟨⟨6900,9626,2077,475797⟩,9849424459857920,234809190715807⟩,110,3,1,385979,22⟩
theorem cover886 : PhysicalWindow.Cover (PhysicalWindow.Triangular src886) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src887 : Request := ⟨⟨⟨10000,13953,3010,185441⟩,29974681586237440,1036125345444439⟩,110,3,1,385979,22⟩
theorem cover887 : PhysicalWindow.Cover (PhysicalWindow.Triangular src887) 2411 2314 [2315, 2321, 2337, 2381, 2411] := triangleCover (by decide +kernel)
def src888 : Request := ⟨⟨⟨8300,11579,2498,2474877⟩,17139238515245056,491470625461013⟩,145,3,1,385979,22⟩
theorem cover888 : PhysicalWindow.Cover (PhysicalWindow.Triangular src888) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src889 : Request := ⟨⟨⟨1000,1395,307,13899⟩,30557599170560,105715278267⟩,0,3,1,385979,23⟩
theorem cover889 : PhysicalWindow.Cover (PhysicalWindow.Triangular src889) 2411 2314 [2320, 2341, 2403, 2411] := triangleCover (by decide +kernel)
def src890 : Request := ⟨⟨⟨1000,1395,307,15636⟩,30557599170560,105715278267⟩,1,3,1,385979,23⟩
theorem cover890 : PhysicalWindow.Cover (PhysicalWindow.Triangular src890) 2411 2314 [2326, 2364, 2411] := triangleCover (by decide +kernel)
def src891 : Request := ⟨⟨⟨1000,1395,301,17590⟩,30103476895744,104105680031⟩,2,3,1,385979,23⟩
theorem cover891 : PhysicalWindow.Cover (PhysicalWindow.Triangular src891) 2411 2314 [2318, 2333, 2377, 2411] := triangleCover (by decide +kernel)
def src892 : Request := ⟨⟨⟨1200,1674,368,19788⟩,52718727069696,218807905514⟩,4,3,1,385979,23⟩
theorem cover892 : PhysicalWindow.Cover (PhysicalWindow.Triangular src892) 2411 2314 [2324, 2356, 2411] := triangleCover (by decide +kernel)
def src893 : Request := ⟨⟨⟨1450,2023,445,25043⟩,92998964346880,466511127281⟩,8,3,1,385979,23⟩
theorem cover893 : PhysicalWindow.Cover (PhysicalWindow.Triangular src893) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src894 : Request := ⟨⟨⟨2100,2930,645,45124⟩,282396798484480,2051392203643⟩,20,3,1,385979,23⟩
theorem cover894 : PhysicalWindow.Cover (PhysicalWindow.Triangular src894) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src899 : Request := ⟨⟨⟨4800,6697,1474,81311⟩,3367547627110400,55891290082931⟩,50,3,1,385979,23⟩
theorem cover899 : PhysicalWindow.Cover (PhysicalWindow.Triangular src899) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src900 : Request := ⟨⟨⟨4800,6697,1474,130242⟩,3367547627110400,55891290082931⟩,65,3,1,385979,23⟩
theorem cover900 : PhysicalWindow.Cover (PhysicalWindow.Triangular src900) 2411 2314 [2315, 2321, 2337, 2381, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1480

-- Source: Research6969.PrefixRescueDataCubicSingletons18
section Z6969Source1481
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons18
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,22⟩
  bank i := ![bank203 17590, bank221 17590, bank221 19788, bank228 19788, bank228 22261, bank237 28173, bank271 57109, bank346 115771, bank355 475797, bank382 185441, bank367 2474877] i
  reserve i := ![0, 1, 2, 3, 4, 8, 25, 65, 110, 110, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 22

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank203 17590
    · exact rank221 17590
    · exact rank221 19788
    · exact rank228 19788
    · exact rank228 22261
    · exact rank237 28173
    · exact rank271 57109
    · exact rank346 115771
    · exact rank355 475797
    · exact rank382 185441
    · exact rank367 2474877
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover876⟩
    · exact ⟨_, cover877⟩
    · exact ⟨_, cover878⟩
    · exact ⟨_, cover879⟩
    · exact ⟨_, cover880⟩
    · exact ⟨_, cover881⟩
    · exact ⟨_, cover883⟩
    · exact ⟨_, cover885⟩
    · exact ⟨_, cover886⟩
    · exact ⟨_, cover887⟩
    · exact ⟨_, cover888⟩

def price : EarlyPrice := ⟨3, 22, 10, 80/100, 80/100, ![21195947948265, 2004695633106, 25778979450, 2343564930], 9528524818358370⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16575/146, 83887/37, 287763/37, 4079702/111] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons18
end Z6969Source1481

-- Source: Research6969.PrefixNearSavedCubicSingletons18
section Z6969Source1482
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons18
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨336,4646,113,2267,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons18.plan Lower6960.Prefix6969RescueData.CubicSingletons18.plan Lower6960.Prefix6969RescueData.CubicSingletons18.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 22 22 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons18.plan, Lower6960.Prefix6969MainCases.CubicSingletons18.price, Lower6960.Prefix6969MainCases.CubicSingletons18.valid, Lower6960.Prefix6969MainCases.CubicSingletons18.priced, Lower6960.Prefix6969MainCases.CubicSingletons18.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons18.plan, Lower6960.Prefix6969RescueData.CubicSingletons18.price, Lower6960.Prefix6969RescueData.CubicSingletons18.sources, Lower6960.Prefix6969RescueData.CubicSingletons18.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 215902755068378628 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons18
end Z6969Source1482

-- Source: Research6969.PhysicalChecks099
section Z6969Source1483
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1408 : Request := ⟨⟨⟨556,772,170,6204⟩,5255817068544,9968090926⟩,10,4,2,514638,24⟩
theorem cover1408 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1408) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1409 : Request := ⟨⟨⟨556,772,170,6124⟩,5255817068544,9968090926⟩,10,4,2,514638,25⟩
theorem cover1409 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1409) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1410 : Request := ⟨⟨⟨556,772,170,6046⟩,5255817068544,9968090926⟩,10,4,2,514638,26⟩
theorem cover1410 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1410) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1411 : Request := ⟨⟨⟨556,772,170,5969⟩,5255817068544,9968090926⟩,10,4,2,514638,27⟩
theorem cover1411 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1411) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1412 : Request := ⟨⟨⟨556,772,170,5893⟩,5255817068544,9968090926⟩,10,4,2,514638,28⟩
theorem cover1412 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1412) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1413 : Request := ⟨⟨⟨556,772,170,5818⟩,5255817068544,9968090926⟩,10,4,2,514638,29⟩
theorem cover1413 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1413) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1414 : Request := ⟨⟨⟨556,772,170,5744⟩,5255817068544,9968090926⟩,10,4,2,514638,30⟩
theorem cover1414 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1414) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1415 : Request := ⟨⟨⟨556,772,170,5671⟩,5255817068544,9968090926⟩,10,4,2,514638,31⟩
theorem cover1415 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1415) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1416 : Request := ⟨⟨⟨556,772,170,5600⟩,5255817068544,9968090926⟩,10,4,2,514638,32⟩
theorem cover1416 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1416) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1417 : Request := ⟨⟨⟨556,772,170,5530⟩,5255817068544,9968090926⟩,10,4,2,514638,33⟩
theorem cover1417 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1417) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1418 : Request := ⟨⟨⟨556,772,170,5462⟩,5255817068544,9968090926⟩,10,4,2,514638,34⟩
theorem cover1418 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1418) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1419 : Request := ⟨⟨⟨556,772,170,5395⟩,5255817068544,9968090926⟩,10,4,2,514638,35⟩
theorem cover1419 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1419) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1420 : Request := ⟨⟨⟨556,772,170,5329⟩,5255817068544,9968090926⟩,10,4,2,514638,36⟩
theorem cover1420 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1420) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1421 : Request := ⟨⟨⟨556,772,170,5265⟩,5255817068544,9968090926⟩,10,4,2,514638,37⟩
theorem cover1421 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1421) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1422 : Request := ⟨⟨⟨556,772,170,5202⟩,5255817068544,9968090926⟩,10,4,2,514638,38⟩
theorem cover1422 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1422) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1423 : Request := ⟨⟨⟨556,772,170,5140⟩,5255817068544,9968090926⟩,10,4,2,514638,39⟩
theorem cover1423 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1423) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1483

-- Source: Research6969.PrefixMainDataCubicSingletons19
section Z6969Source1484
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons19
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 16, 21, 41, 40, 65, 76, 76, 76] i
  bank i := ![bank5 1462, bank13 1553, bank18 1703, bank24 1838, bank29 1976, bank35 2061, bank44 2409, bank54 2755, bank65 3612, bank84 5564, bank95 3103, bank137 3540, bank126 26574, bank149 6281, bank199 9241, bank180 62680, bank212 10770, bank170 227095] i
  head := src1408
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15218, 162617, 755886, 3565308],
    ![25417/2, 246779/2, 560297, 2411809],
    ![54680/9, 537670/9, 560297, 2411809],
    ![29433/8, 36202, 2622512/9, 3800984/3],
    ![63052/25, 621304/25, 205504, 976144],
    ![5710/3, 110095/6, 748299/4, 3196611/4],
    ![18775/16, 375375/32, 396682/3, 14945436/25],
    ![89110/121, 871610/121, 3950836/49, 17092020/49],
    ![89110/121, 871610/121, 3950836/49, 17092020/49],
    ![63754/121, 2971256/441, 543881/8, 17092020/49],
    ![63754/121, 2971256/441, 543881/8, 9628609/36],
    ![63754/121, 712116/121, 252225/4, 783225/4],
    ![1355575/3362, 712116/121, 252225/4, 783225/4],
    ![1355575/3362, 1058123/200, 2377034/49, 783225/4],
    ![1355575/3362, 6305980/1323, 10525499/242, 85396081/484],
    ![25627/74, 6305980/1323, 10525499/242, 85396081/484],
    ![25627/74, 6320034/1369, 28392945/676, 58464945/338],
    ![920087/2738, 6320034/1369, 28392945/676, 58464945/338]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 23 385979 := by
  refine ⟨?_, rank154 6204, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1408⟩⟩
  · intro i; fin_cases i
    · exact free5_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free29_0
    · exact free35_0
    · exact free44_0
    · exact free54_0
    · exact free65_0
    · exact free84_0
    · exact free95_0
    · exact free137_0
    · exact free126_0
    · exact free149_0
    · exact free199_0
    · exact free180_0
    · exact free212_0
    · exact free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [320808526, 318844981, 318799168, 319158437, 320259467, 319677881, 319549375, 147094230, 147166767, 147105875, 147389078, 71051590, 67055881, 83599718, 97116219, 97457600, 148081189, 231340544], [1084111, 1094158, 1094393, 1092554, 1086921, 1089896, 1090554, 2615767, 2614560, 2615573, 2610863, 5643776, 5992665, 4769280, 4077261, 4062850, 2599354, 1601965],
  ![122800187566080, 1609890028336, 208206489600, 4863593580], 173619271185572466⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,7,7,7,7,15,16,13,11,11,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 6320034/1369, 28392945/676, 58464945/338] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons19
end Z6969Source1484

-- Source: Research6969.PhysicalChecks074
section Z6969Source1485
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src901 : Request := ⟨⟨⟨6900,9626,2077,375939⟩,9849424459857920,234809190715807⟩,110,3,1,385979,23⟩
theorem cover901 : PhysicalWindow.Cover (PhysicalWindow.Triangular src901) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src902 : Request := ⟨⟨⟨10000,13953,3070,164837⟩,30428373265940480,1052197377228338⟩,110,3,1,385979,23⟩
theorem cover902 : PhysicalWindow.Cover (PhysicalWindow.Triangular src902) 2411 2314 [2323, 2351, 2411] := triangleCover (by decide +kernel)
def src903 : Request := ⟨⟨⟨8300,11579,2498,1955459⟩,17139238515245056,491470625461013⟩,145,3,1,385979,23⟩
theorem cover903 : PhysicalWindow.Cover (PhysicalWindow.Triangular src903) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src904 : Request := ⟨⟨⟨825,1151,248,13899⟩,16903818182656,48256472894⟩,0,3,1,385979,24⟩
theorem cover904 : PhysicalWindow.Cover (PhysicalWindow.Triangular src904) 2411 2314 [2324, 2358, 2411] := triangleCover (by decide +kernel)
def src905 : Request := ⟨⟨⟨1000,1395,307,13899⟩,30557599170560,105715278267⟩,1,3,1,385979,24⟩
theorem cover905 : PhysicalWindow.Cover (PhysicalWindow.Triangular src905) 2411 2314 [2324, 2356, 2411] := triangleCover (by decide +kernel)
def src906 : Request := ⟨⟨⟨1000,1395,301,15636⟩,30103476895744,104105680031⟩,2,3,1,385979,24⟩
theorem cover906 : PhysicalWindow.Cover (PhysicalWindow.Triangular src906) 2411 2314 [2317, 2328, 2361, 2411] := triangleCover (by decide +kernel)
def src907 : Request := ⟨⟨⟨1200,1674,368,17590⟩,52718727069696,218807905514⟩,4,3,1,385979,24⟩
theorem cover907 : PhysicalWindow.Cover (PhysicalWindow.Triangular src907) 2411 2314 [2323, 2352, 2411] := triangleCover (by decide +kernel)
def src908 : Request := ⟨⟨⟨1450,2023,445,22261⟩,92998964346880,466511127281⟩,8,3,1,385979,24⟩
theorem cover908 : PhysicalWindow.Cover (PhysicalWindow.Triangular src908) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src909 : Request := ⟨⟨⟨2100,2930,645,40111⟩,282396798484480,2051392203643⟩,20,3,1,385979,24⟩
theorem cover909 : PhysicalWindow.Cover (PhysicalWindow.Triangular src909) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src914 : Request := ⟨⟨⟨5700,7953,1750,91474⟩,5637370734182400,111115710437454⟩,65,3,1,385979,24⟩
theorem cover914 : PhysicalWindow.Cover (PhysicalWindow.Triangular src914) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src915 : Request := ⟨⟨⟨6900,9626,2118,297039⟩,9997036108906496,238415548481346⟩,110,3,1,385979,24⟩
theorem cover915 : PhysicalWindow.Cover (PhysicalWindow.Triangular src915) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src916 : Request := ⟨⟨⟨8300,11580,2548,164837⟩,17399709518790656,499263802703202⟩,110,3,1,385979,24⟩
theorem cover916 : PhysicalWindow.Cover (PhysicalWindow.Triangular src916) 2411 2314 [2322, 2347, 2411] := triangleCover (by decide +kernel)
def src917 : Request := ⟨⟨⟨10000,13953,3070,146522⟩,30428373265940480,1052197377228338⟩,110,3,1,385979,24⟩
theorem cover917 : PhysicalWindow.Cover (PhysicalWindow.Triangular src917) 2411 2314 [2322, 2347, 2411] := triangleCover (by decide +kernel)
def src918 : Request := ⟨⟨⟨8300,11579,2498,1545055⟩,17139238515245056,491470625461013⟩,145,3,1,385979,24⟩
theorem cover918 : PhysicalWindow.Cover (PhysicalWindow.Triangular src918) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src919 : Request := ⟨⟨⟨690,963,208,13899⟩,9921631092736,23724874690⟩,0,3,1,385979,25⟩
theorem cover919 : PhysicalWindow.Cover (PhysicalWindow.Triangular src919) 2411 2314 [2322, 2349, 2411] := triangleCover (by decide +kernel)
def src920 : Request := ⟨⟨⟨825,1151,248,13899⟩,16903818182656,48256472894⟩,1,3,1,385979,25⟩
theorem cover920 : PhysicalWindow.Cover (PhysicalWindow.Triangular src920) 2411 2314 [2320, 2342, 2408, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1485

-- Source: Research6969.PrefixRescueDataCubicSingletons19
section Z6969Source1486
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons19
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,23⟩
  bank i := ![bank222 13899, bank222 15636, bank221 17590, bank228 19788, bank237 25043, bank253 45124, bank329 81311, bank329 130242, bank383 164837, bank355 375939, bank367 1955459] i
  reserve i := ![0, 1, 2, 4, 8, 20, 50, 65, 110, 110, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 23

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank222 13899
    · exact rank222 15636
    · exact rank221 17590
    · exact rank228 19788
    · exact rank237 25043
    · exact rank253 45124
    · exact rank329 81311
    · exact rank329 130242
    · exact rank383 164837
    · exact rank355 375939
    · exact rank367 1955459
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover889⟩
    · exact ⟨_, cover890⟩
    · exact ⟨_, cover891⟩
    · exact ⟨_, cover892⟩
    · exact ⟨_, cover893⟩
    · exact ⟨_, cover894⟩
    · exact ⟨_, cover899⟩
    · exact ⟨_, cover900⟩
    · exact ⟨_, cover902⟩
    · exact ⟨_, cover901⟩
    · exact ⟨_, cover903⟩

def price : EarlyPrice := ⟨3, 23, 10, 75/100, 70/100, ![17508665600283, 1603815574884, 27487972590, 2390280510], 7644701773167698⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16575/146, 235447/111, 271810/37, 3791251/111] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons19
end Z6969Source1486

-- Source: Research6969.PrefixNearSavedCubicSingletons19
section Z6969Source1487
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons19
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨336,4616,113,2121,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons19.plan Lower6960.Prefix6969RescueData.CubicSingletons19.plan Lower6960.Prefix6969RescueData.CubicSingletons19.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 23 23 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons19.plan, Lower6960.Prefix6969MainCases.CubicSingletons19.price, Lower6960.Prefix6969MainCases.CubicSingletons19.valid, Lower6960.Prefix6969MainCases.CubicSingletons19.priced, Lower6960.Prefix6969MainCases.CubicSingletons19.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons19.plan, Lower6960.Prefix6969RescueData.CubicSingletons19.price, Lower6960.Prefix6969RescueData.CubicSingletons19.sources, Lower6960.Prefix6969RescueData.CubicSingletons19.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 214532286596888149 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons19
end Z6969Source1487

end Merged_Z6969Pack0701

-- merged module Z6969Pack0702
section Merged_Z6969Pack0702

-- Source: Research6969.PrefixMainDataCubicSingletons2
section Z6969Source1488
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons2
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank84 5564, bank85 2903, bank74 6544, bank113 3716, bank144 4704, bank150 6517, bank120 36262, bank198 9780, bank210 11036, bank183 54742, bank174 148759, bank169 292467] i
  head := src1391
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 169818, 790364, 4145142],
    ![12303, 138284, 625120, 3124576],
    ![53398/9, 599344/9, 619520, 3097600],
    ![29433/8, 160847/4, 2911960/9, 14145248/9],
    ![16211/9, 41279/2, 846559/4, 1078883],
    ![24292/27, 916018/81, 1040561/9, 5750836/9],
    ![73478/121, 1189424/121, 5368880/49, 5750836/9],
    ![73478/121, 1189424/121, 5368880/49, 4775368/9],
    ![73478/121, 977536/121, 4382032/49, 19517056/49],
    ![63754/121, 65936/9, 543881/8, 19517056/49],
    ![63754/121, 65936/9, 543881/8, 44682976/121],
    ![61324/121, 65936/9, 543881/8, 44682976/121],
    ![61324/121, 782402/121, 13525856/225, 57196672/225],
    ![61324/121, 782402/121, 1249904/21, 27151488/121],
    ![61324/121, 9634056/1681, 43366416/841, 27151488/121],
    ![667406/1681, 9634056/1681, 43366416/841, 27151488/121],
    ![667406/1681, 1007152/189, 31708288/675, 10627600/49],
    ![667406/1681, 7054250/1369, 126978544/2809, 7612081/36],
    ![954471/2738, 7054250/1369, 126978544/2809, 7612081/36],
    ![462882/1369, 7054250/1369, 126978544/2809, 7612081/36],
    ![459151/1369, 7054250/1369, 126978544/2809, 7612081/36]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 6 385979 := by
  refine ⟨?_, rank154 7696, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1391⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free61_0
    · exact free84_0
    · exact free85_0
    · exact free74_2
    · exact free113_0
    · exact free144_0
    · exact free150_0
    · exact free120_0
    · exact free198_0
    · exact free210_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [348553724, 347815214, 348197040, 348082630, 347231566, 346510877, 347483542, 346787961, 166902763, 166983885, 167637295, 167617990, 115999940, 74774265, 67242944, 91630721, 106576509, 106547194, 127364696, 174395108, 235638249], [991444, 993469, 992422, 992735, 995068, 997044, 994378, 996284, 2286352, 2285003, 2274136, 2274457, 3376068, 5347975, 5975709, 4334053, 3697678, 3698696, 3058306, 2179749, 1566623],
  ![125081495334180, 1605247166856, 212074424100, 4419759960], 192076034693805123⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,9,14,16,12,10,10,9,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 7054250/1369, 126978544/2809, 7612081/36] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons2
end Z6969Source1488

-- Source: Research6969.PhysicalChecks063
section Z6969Source1489
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src697 : Request := ⟨⟨⟨8300,11581,2498,475797⟩,17139238515245056,491743896877039⟩,85,3,1,385979,6⟩
theorem cover697 : PhysicalWindow.Cover (PhysicalWindow.Triangular src697) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src698 : Request := ⟨⟨⟨1000,1395,301,50764⟩,30103476895744,104105680031⟩,0,3,1,385979,7⟩
theorem cover698 : PhysicalWindow.Cover (PhysicalWindow.Triangular src698) 2411 2314 [2324, 2357, 2411] := triangleCover (by decide +kernel)
def src699 : Request := ⟨⟨⟨1200,1674,361,57109⟩,51955677528064,215563369662⟩,2,3,1,385979,7⟩
theorem cover699 : PhysicalWindow.Cover (PhysicalWindow.Triangular src699) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src700 : Request := ⟨⟨⟨1200,1674,361,72277⟩,51955677528064,215563369662⟩,4,3,1,385979,7⟩
theorem cover700 : PhysicalWindow.Cover (PhysicalWindow.Triangular src700) 2411 2314 [2318, 2333, 2377, 2411] := triangleCover (by decide +kernel)
def src701 : Request := ⟨⟨⟨1750,2442,527,102908⟩,161065121873920,975196209190⟩,10,3,1,385979,7⟩
theorem cover701 : PhysicalWindow.Cover (PhysicalWindow.Triangular src701) 2411 2314 [2322, 2348, 2411] := triangleCover (by decide +kernel)
def src702 : Request := ⟨⟨⟨2600,3628,770,130242⟩,521059839508480,4684185417862⟩,16,3,1,385979,7⟩
theorem cover702 : PhysicalWindow.Cover (PhysicalWindow.Triangular src702) 2411 2314 [2318, 2333, 2375, 2411] := triangleCover (by decide +kernel)
def src703 : Request := ⟨⟨⟨3200,4465,963,164837⟩,983050615259136,10877088344236⟩,25,3,1,385979,7⟩
theorem cover703 : PhysicalWindow.Cover (PhysicalWindow.Triangular src703) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src704 : Request := ⟨⟨⟨3200,4464,963,422931⟩,983050615259136,10869251283552⟩,40,3,1,385979,7⟩
theorem cover704 : PhysicalWindow.Cover (PhysicalWindow.Triangular src704) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src705 : Request := ⟨⟨⟨6900,9628,2042,375939⟩,9722458861731840,231866079487253⟩,65,3,1,385979,7⟩
theorem cover705 : PhysicalWindow.Cover (PhysicalWindow.Triangular src705) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src706 : Request := ⟨⟨⟨10000,13953,3010,602179⟩,29974681586237440,1036125345444439⟩,110,3,1,385979,7⟩
theorem cover706 : PhysicalWindow.Cover (PhysicalWindow.Triangular src706) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src707 : Request := ⟨⟨⟨1000,1395,296,50764⟩,29722184515584,102755930405⟩,0,3,1,385979,8⟩
theorem cover707 : PhysicalWindow.Cover (PhysicalWindow.Triangular src707) 2411 2314 [2323, 2353, 2411] := triangleCover (by decide +kernel)
def src708 : Request := ⟨⟨⟨1200,1674,361,50764⟩,51955677528064,215563369662⟩,1,3,1,385979,8⟩
theorem cover708 : PhysicalWindow.Cover (PhysicalWindow.Triangular src708) 2411 2314 [2320, 2341, 2402, 2411] := triangleCover (by decide +kernel)
def src709 : Request := ⟨⟨⟨1200,1674,361,57109⟩,51955677528064,215563369662⟩,2,3,1,385979,8⟩
theorem cover709 : PhysicalWindow.Cover (PhysicalWindow.Triangular src709) 2411 2314 [2324, 2356, 2411] := triangleCover (by decide +kernel)
def src710 : Request := ⟨⟨⟨1200,1674,361,72277⟩,51955677528064,215563369662⟩,4,3,1,385979,8⟩
theorem cover710 : PhysicalWindow.Cover (PhysicalWindow.Triangular src710) 2411 2314 [2325, 2360, 2411] := triangleCover (by decide +kernel)
def src711 : Request := ⟨⟨⟨2100,2930,632,91474⟩,278060332482560,2019119590628⟩,10,3,1,385979,8⟩
theorem cover711 : PhysicalWindow.Cover (PhysicalWindow.Triangular src711) 2411 2314 [2321, 2344, 2410, 2411] := triangleCover (by decide +kernel)
def src712 : Request := ⟨⟨⟨2600,3628,783,115771⟩,527755772952576,4745819470168⟩,16,3,1,385979,8⟩
theorem cover712 : PhysicalWindow.Cover (PhysicalWindow.Triangular src712) 2411 2314 [2317, 2329, 2362, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1489

-- Source: Research6969.PrefixRescueDataCubicSingletons2
section Z6969Source1490
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons2
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,6⟩
  bank i := ![bank221 50764, bank227 57109, bank226 64247, bank226 72277, bank226 81311, bank245 102908, bank303 146522, bank315 208621, bank345 297039, bank299 422931, bank371 475797] i
  reserve i := ![0, 1, 2, 3, 4, 10, 20, 32, 50, 40, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 6

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 50764
    · exact rank227 57109
    · exact rank226 64247
    · exact rank226 72277
    · exact rank226 81311
    · exact rank245 102908
    · exact rank303 146522
    · exact rank315 208621
    · exact rank345 297039
    · exact rank299 422931
    · exact rank371 475797
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover687⟩
    · exact ⟨_, cover688⟩
    · exact ⟨_, cover689⟩
    · exact ⟨_, cover690⟩
    · exact ⟨_, cover691⟩
    · exact ⟨_, cover692⟩
    · exact ⟨_, cover693⟩
    · exact ⟨_, cover694⟩
    · exact ⟨_, cover696⟩
    · exact ⟨_, cover695⟩
    · exact ⟨_, cover697⟩

def price : EarlyPrice := ⟨3, 6, 10, 95/100, 80/100, ![1111348076517, 391667930784, 5834730978, 1944925314], 8745104459178171⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![6390/41, 490785/86, 1496877/86, 1427391/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons2
end Z6969Source1490

-- Source: Research6969.PrefixNearSavedCubicSingletons2
section Z6969Source1491
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons2
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,5152,155,5706,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons2.plan Lower6960.Prefix6969RescueData.CubicSingletons2.plan Lower6960.Prefix6969RescueData.CubicSingletons2.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 6 6 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons2.plan, Lower6960.Prefix6969MainCases.CubicSingletons2.price, Lower6960.Prefix6969MainCases.CubicSingletons2.valid, Lower6960.Prefix6969MainCases.CubicSingletons2.priced, Lower6960.Prefix6969MainCases.CubicSingletons2.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons2.plan, Lower6960.Prefix6969RescueData.CubicSingletons2.price, Lower6960.Prefix6969RescueData.CubicSingletons2.sources, Lower6960.Prefix6969RescueData.CubicSingletons2.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 220023121768400903 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons2
end Z6969Source1491

-- Source: Research6969.PrefixMainDataCubicSingletons20
section Z6969Source1492
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons20
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 17, 21, 41, 40, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank29 1976, bank37 2039, bank44 2409, bank54 2755, bank74 3583, bank84 5564, bank98 3253, bank137 3540, bank129 24535, bank151 6174, bank212 10770, bank186 46700, bank175 125592, bank169 292467] i
  head := src1409
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15511, 162079, 750488, 3444900],
    ![25417/2, 245299/2, 556937, 2411809],
    ![54680/9, 534470/9, 556937, 2411809],
    ![29433/8, 35987, 2606992/9, 11255912/9],
    ![63052/25, 617624/25, 205504, 976144],
    ![17323/9, 329477/18, 185266, 3121709/4],
    ![18775/16, 373175/32, 396682/3, 14752716/25],
    ![89110/121, 866410/121, 3927316/49, 16871620/49],
    ![89110/121, 866410/121, 1336459/18, 16871620/49],
    ![63754/121, 2957336/441, 543881/8, 16871620/49],
    ![63754/121, 2957336/441, 543881/8, 4980343/18],
    ![63754/121, 706996/121, 252225/4, 783225/4],
    ![33263/82, 706996/121, 252225/4, 783225/4],
    ![33263/82, 525727/100, 2362797/49, 194481],
    ![33263/82, 6279854/1369, 28214445/676, 28998225/169],
    ![481425/1369, 6279854/1369, 28214445/676, 28998225/169],
    ![929061/2738, 6279854/1369, 28214445/676, 28998225/169],
    ![459151/1369, 6279854/1369, 28214445/676, 28998225/169]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 24 385979 := by
  refine ⟨?_, rank154 6124, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1409⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free29_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free74_1
    · exact free84_0
    · exact free98_0
    · exact free137_0
    · exact free129_0
    · exact free151_0
    · exact free212_0
    · exact free186_0
    · exact free175_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [320143882, 319861335, 320154543, 319392088, 317845377, 319089361, 318341639, 146815879, 146915063, 146867026, 146923616, 69875364, 69805957, 96925597, 96937676, 113163740, 168238037, 230660451], [1087512, 1088958, 1087457, 1091359, 1099273, 1092908, 1096734, 2621081, 2618906, 2619960, 2618719, 5737280, 5743392, 4085308, 4084799, 3468957, 2264146, 1607558],
  ![122439180599820, 1610624948364, 207594405900, 4860445520], 172600723052751063⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,8,8,8,8,15,16,11,11,10,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 6279854/1369, 28214445/676, 28998225/169] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons20
end Z6969Source1492

-- Source: Research6969.PrefixRescueDataCubicSingletons20
section Z6969Source1493
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons20
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,24⟩
  bank i := ![bank203 13899, bank222 13899, bank221 15636, bank228 17590, bank237 22261, bank253 40111, bank346 91474, bank356 297039, bank383 146522, bank367 1545055, bank370 164837] i
  reserve i := ![0, 1, 2, 4, 8, 20, 65, 110, 110, 145, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 24

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank203 13899
    · exact rank222 13899
    · exact rank221 15636
    · exact rank228 17590
    · exact rank237 22261
    · exact rank253 40111
    · exact rank346 91474
    · exact rank356 297039
    · exact rank383 146522
    · exact rank367 1545055
    · exact rank370 164837
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover904⟩
    · exact ⟨_, cover905⟩
    · exact ⟨_, cover906⟩
    · exact ⟨_, cover907⟩
    · exact ⟨_, cover908⟩
    · exact ⟨_, cover909⟩
    · exact ⟨_, cover914⟩
    · exact ⟨_, cover915⟩
    · exact ⟨_, cover917⟩
    · exact ⟨_, cover918⟩
    · exact ⟨_, cover916⟩

def price : EarlyPrice := ⟨3, 24, 10, 75/100, 70/100, ![14435495216650, 1287813063045, 28683102100, 2390280510], 6263922056762505⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16575/146, 220202/111, 257477/37, 1172176/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons20
end Z6969Source1493

-- Source: Research6969.PrefixNearSavedCubicSingletons20
section Z6969Source1494
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons20
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4587,113,1983,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons20.plan Lower6960.Prefix6969RescueData.CubicSingletons20.plan Lower6960.Prefix6969RescueData.CubicSingletons20.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 24 24 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons20.plan, Lower6960.Prefix6969MainCases.CubicSingletons20.price, Lower6960.Prefix6969MainCases.CubicSingletons20.valid, Lower6960.Prefix6969MainCases.CubicSingletons20.priced, Lower6960.Prefix6969MainCases.CubicSingletons20.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons20.plan, Lower6960.Prefix6969RescueData.CubicSingletons20.price, Lower6960.Prefix6969RescueData.CubicSingletons20.sources, Lower6960.Prefix6969RescueData.CubicSingletons20.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 213411110355531343 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons20
end Z6969Source1494

-- Source: Research6969.PrefixMainDataCubicSingletons21
section Z6969Source1495
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons21
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 16, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank29 1976, bank35 2061, bank44 2409, bank54 2755, bank74 3583, bank84 5564, bank95 3103, bank137 3540, bank126 26574, bank161 6246, bank199 9241, bank180 62680, bank212 10770, bank170 227095] i
  head := src1410
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15507, 161831, 749310, 3435044],
    ![25417/2, 121928, 553661, 2411809],
    ![54680/9, 531350/9, 553661, 2411809],
    ![29433/8, 286219/8, 2591860/9, 11112548/9],
    ![63052/25, 614036/25, 205504, 976144],
    ![5710/3, 326335/18, 184843, 6230403/8],
    ![18775/16, 185515/16, 396682/3, 14564814/25],
    ![89110/121, 861340/121, 3904384/49, 16656730/49],
    ![89110/121, 861340/121, 1336459/18, 16656730/49],
    ![63754/121, 2943764/441, 67953, 16656730/49],
    ![63754/121, 2943764/441, 67953, 9628609/36],
    ![63754/121, 702004/121, 3089550/49, 783225/4],
    ![1355575/3362, 702004/121, 3089550/49, 783225/4],
    ![1355575/3362, 8527848/1681, 4790057/98, 9440829/49],
    ![1355575/3362, 6225400/1323, 1911879/44, 83806629/484],
    ![25627/74, 6225400/1323, 1911879/44, 83806629/484],
    ![25627/74, 12481357/2738, 56080815/1352, 28998225/169],
    ![920087/2738, 12481357/2738, 56080815/1352, 28998225/169]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 25 385979 := by
  refine ⟨?_, rank154 6046, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1410⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free29_0
    · exact free35_0
    · exact free44_0
    · exact free54_0
    · exact free74_1
    · exact free84_0
    · exact free95_0
    · exact free137_0
    · exact free126_0
    · exact free161_0
    · exact free199_0
    · exact free180_0
    · exact free212_0
    · exact free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [318560284, 318371886, 318238834, 317398389, 318353654, 317203932, 316262926, 147268297, 147357966, 147330602, 147319545, 70847491, 71022797, 83657280, 96809574, 96794715, 147216329, 230680829], [1095615, 1096579, 1097260, 1101560, 1096672, 1102555, 1107370, 2612872, 2611381, 2611836, 2612020, 5660001, 5646065, 4765861, 4090206, 4090834, 2613736, 1607391],
  ![122449997649780, 1610602691956, 207612746100, 4867019080], 171721753065408827⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,7,7,7,7,15,15,13,11,11,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 12481357/2738, 56080815/1352, 28998225/169] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons21
end Z6969Source1495

-- Source: Research6969.PhysicalChecks075
section Z6969Source1496
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src921 : Request := ⟨⟨⟨1000,1395,301,17590⟩,30103476895744,104105680031⟩,4,3,1,385979,25⟩
theorem cover921 : PhysicalWindow.Cover (PhysicalWindow.Triangular src921) 2411 2314 [2317, 2329, 2365, 2411] := triangleCover (by decide +kernel)
def src922 : Request := ⟨⟨⟨1200,1674,368,22261⟩,52718727069696,218807905514⟩,8,3,1,385979,25⟩
theorem cover922 : PhysicalWindow.Cover (PhysicalWindow.Triangular src922) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src923 : Request := ⟨⟨⟨2100,2930,645,35655⟩,282396798484480,2051392203643⟩,20,3,1,385979,25⟩
theorem cover923 : PhysicalWindow.Cover (PhysicalWindow.Triangular src923) 2411 2314 [2321, 2344, 2409, 2411] := triangleCover (by decide +kernel)
def src926 : Request := ⟨⟨⟨3950,5511,1213,72277⟩,1877062482395136,25637257621145⟩,50,3,1,385979,25⟩
theorem cover926 : PhysicalWindow.Cover (PhysicalWindow.Triangular src926) 2411 2314 [2316, 2325, 2349, 2411] := triangleCover (by decide +kernel)
def src927 : Request := ⟨⟨⟨5700,7952,1750,146522⟩,5637370734182400,111070724916873⟩,85,3,1,385979,25⟩
theorem cover927 : PhysicalWindow.Cover (PhysicalWindow.Triangular src927) 2411 2314 [2319, 2335, 2379, 2411] := triangleCover (by decide +kernel)
def src928 : Request := ⟨⟨⟨6900,9626,2118,234698⟩,9997036108906496,238415548481346⟩,110,3,1,385979,25⟩
theorem cover928 : PhysicalWindow.Cover (PhysicalWindow.Triangular src928) 2411 2314 [2319, 2335, 2379, 2411] := triangleCover (by decide +kernel)
def src929 : Request := ⟨⟨⟨10000,13953,3070,130242⟩,30428373265940480,1052197377228338⟩,110,3,1,385979,25⟩
theorem cover929 : PhysicalWindow.Cover (PhysicalWindow.Triangular src929) 2411 2314 [2320, 2339, 2392, 2411] := triangleCover (by decide +kernel)
def src930 : Request := ⟨⟨⟨8300,11579,2498,964572⟩,17139238515245056,491470625461013⟩,145,3,1,385979,25⟩
theorem cover930 : PhysicalWindow.Cover (PhysicalWindow.Triangular src930) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src931 : Request := ⟨⟨⟨690,963,212,10983⟩,10065769922560,24078187611⟩,0,3,1,385979,26⟩
theorem cover931 : PhysicalWindow.Cover (PhysicalWindow.Triangular src931) 2411 2314 [2320, 2341, 2405, 2411] := triangleCover (by decide +kernel)
def src932 : Request := ⟨⟨⟨825,1151,248,12355⟩,16903818182656,48256472894⟩,1,3,1,385979,26⟩
theorem cover932 : PhysicalWindow.Cover (PhysicalWindow.Triangular src932) 2411 2314 [2321, 2345, 2411] := triangleCover (by decide +kernel)
def src933 : Request := ⟨⟨⟨825,1151,253,13899⟩,17161575202816,49010625289⟩,2,3,1,385979,26⟩
theorem cover933 : PhysicalWindow.Cover (PhysicalWindow.Triangular src933) 2411 2314 [2328, 2373, 2411] := triangleCover (by decide +kernel)
def src934 : Request := ⟨⟨⟨1000,1395,301,13899⟩,30103476895744,104105680031⟩,3,3,1,385979,26⟩
theorem cover934 : PhysicalWindow.Cover (PhysicalWindow.Triangular src934) 2411 2314 [2316, 2325, 2352, 2411] := triangleCover (by decide +kernel)
def src935 : Request := ⟨⟨⟨1000,1395,301,15636⟩,30103476895744,104105680031⟩,4,3,1,385979,26⟩
theorem cover935 : PhysicalWindow.Cover (PhysicalWindow.Triangular src935) 2411 2314 [2318, 2333, 2378, 2411] := triangleCover (by decide +kernel)
def src936 : Request := ⟨⟨⟨1000,1395,307,19788⟩,30557599170560,105715278267⟩,6,3,1,385979,26⟩
theorem cover936 : PhysicalWindow.Cover (PhysicalWindow.Triangular src936) 2411 2314 [2320, 2341, 2402, 2411] := triangleCover (by decide +kernel)
def src937 : Request := ⟨⟨⟨1200,1674,368,19788⟩,52718727069696,218807905514⟩,8,3,1,385979,26⟩
theorem cover937 : PhysicalWindow.Cover (PhysicalWindow.Triangular src937) 2411 2314 [2320, 2341, 2402, 2411] := triangleCover (by decide +kernel)
def src938 : Request := ⟨⟨⟨2100,2930,645,31694⟩,282396798484480,2051392203643⟩,20,3,1,385979,26⟩
theorem cover938 : PhysicalWindow.Cover (PhysicalWindow.Triangular src938) 2411 2314 [2324, 2355, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1496

-- Source: Research6969.PrefixRescueDataCubicSingletons21
section Z6969Source1497
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons21
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,25⟩
  bank i := ![bank195 13899, bank203 13899, bank221 17590, bank228 22261, bank253 35655, bank313 72277, bank356 234698, bank383 130242, bank367 964572, bank383 130242, bank343 146522] i
  reserve i := ![0, 1, 4, 8, 20, 50, 110, 110, 145, 110, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 25

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank195 13899
    · exact rank203 13899
    · exact rank221 17590
    · exact rank228 22261
    · exact rank253 35655
    · exact rank313 72277
    · exact rank356 234698
    · exact rank383 130242
    · exact rank367 964572
    · exact rank383 130242
    · exact rank343 146522
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover919⟩
    · exact ⟨_, cover920⟩
    · exact ⟨_, cover921⟩
    · exact ⟨_, cover922⟩
    · exact ⟨_, cover923⟩
    · exact ⟨_, cover926⟩
    · exact ⟨_, cover928⟩
    · exact ⟨_, cover929⟩
    · exact ⟨_, cover930⟩
    · exact ⟨_, cover929⟩
    · exact ⟨_, cover927⟩

def price : EarlyPrice := ⟨3, 25, 10, 80/100, 80/100, ![9387526260756, 839388232359, 29878231610, 2390280510], 4434357735658391⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16575/146, 206992/111, 246517/37, 1085350/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons21
end Z6969Source1497

-- Source: Research6969.PrefixNearSavedCubicSingletons21
section Z6969Source1498
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons21
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨336,4558,113,1864,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons21.plan Lower6960.Prefix6969RescueData.CubicSingletons21.plan Lower6960.Prefix6969RescueData.CubicSingletons21.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 25 25 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons21.plan, Lower6960.Prefix6969MainCases.CubicSingletons21.price, Lower6960.Prefix6969MainCases.CubicSingletons21.valid, Lower6960.Prefix6969MainCases.CubicSingletons21.priced, Lower6960.Prefix6969MainCases.CubicSingletons21.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons21.plan, Lower6960.Prefix6969RescueData.CubicSingletons21.price, Lower6960.Prefix6969RescueData.CubicSingletons21.sources, Lower6960.Prefix6969RescueData.CubicSingletons21.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 212499991639762255 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons21
end Z6969Source1498

-- Source: Research6969.PrefixMainDataCubicSingletons22
section Z6969Source1499
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons22
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 16, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank29 1976, bank37 2039, bank44 2409, bank54 2755, bank65 3612, bank84 5564, bank95 3103, bank137 3540, bank126 26574, bank161 6246, bank199 9241, bank181 61748, bank212 10770, bank170 227095] i
  head := src1411
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15464, 161703, 748370, 3450540],
    ![25417/2, 484863/4, 550427, 2411809],
    ![54680/9, 176090/3, 550427, 2411809],
    ![29433/8, 569127/16, 858974/3, 10971022/9],
    ![63052/25, 610494/25, 205504, 976144],
    ![17323/9, 651049/36, 2929071/16, 12170791/16],
    ![18775/16, 737825/64, 396682/3, 14379321/25],
    ![89110/121, 856335/121, 3881746/49, 16444595/49],
    ![89110/121, 856335/121, 3881746/49, 16444595/49],
    ![63754/121, 2930366/441, 947041/14, 16444595/49],
    ![63754/121, 2930366/441, 947041/14, 9628609/36],
    ![63754/121, 697076/121, 3067605/49, 783225/4],
    ![1355575/3362, 697076/121, 3067605/49, 783225/4],
    ![1355575/3362, 8473332/1681, 9519515/196, 18641187/98],
    ![1355575/3362, 6186130/1323, 3799839/88, 165478587/968],
    ![474397/1369, 6186130/1323, 3799839/88, 165478587/968],
    ![474397/1369, 24808021/5476, 111474405/2704, 165478587/968],
    ![920087/2738, 24808021/5476, 111474405/2704, 165478587/968]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 26 385979 := by
  refine ⟨?_, rank154 5969, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1411⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free29_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free65_0
    · exact free84_0
    · exact free95_0
    · exact free137_0
    · exact free126_0
    · exact free161_0
    · exact free199_0
    · exact free181_0
    · exact free212_0
    · exact free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [316872722, 316244349, 316798935, 316582257, 315486706, 314634250, 315693019, 146097610, 146095435, 146065265, 146007353, 70444877, 70460683, 82187542, 95985255, 95184785, 146844197, 230359323], [1104250, 1107466, 1104628, 1105736, 1111342, 1115704, 1110287, 2636833, 2636880, 2637542, 2638812, 5692007, 5690751, 4853153, 4125005, 4158796, 2620460, 1610035],
  ![122279335834860, 1610950354332, 207323390700, 4949124660], 170794824248774458⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,8,8,8,8,15,15,13,11,11,8,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 24808021/5476, 111474405/2704, 165478587/968] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons22
end Z6969Source1499

end Merged_Z6969Pack0702

-- merged module Z6969Pack0703
section Merged_Z6969Pack0703

-- Source: Research6969.PhysicalChecks076
section Z6969Source1500
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src941 : Request := ⟨⟨⟨4800,6697,1474,81311⟩,3367547627110400,55891290082931⟩,65,3,1,385979,26⟩
theorem cover941 : PhysicalWindow.Cover (PhysicalWindow.Triangular src941) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src942 : Request := ⟨⟨⟨8300,11579,2548,475797⟩,17399709518790656,499124969898998⟩,145,3,1,385979,26⟩
theorem cover942 : PhysicalWindow.Cover (PhysicalWindow.Triangular src942) 2411 2314 [2315, 2320, 2334, 2372, 2411] := triangleCover (by decide +kernel)
def src943 : Request := ⟨⟨⟨10000,13952,3070,164837⟩,30428373265940480,1051954539834997⟩,145,3,1,385979,26⟩
theorem cover943 : PhysicalWindow.Cover (PhysicalWindow.Triangular src943) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src944 : Request := ⟨⟨⟨690,963,212,9763⟩,10065769922560,24078187611⟩,0,3,1,385979,27⟩
theorem cover944 : PhysicalWindow.Cover (PhysicalWindow.Triangular src944) 2411 2314 [2322, 2350, 2411] := triangleCover (by decide +kernel)
def src945 : Request := ⟨⟨⟨825,1151,248,10983⟩,16903818182656,48256472894⟩,1,3,1,385979,27⟩
theorem cover945 : PhysicalWindow.Cover (PhysicalWindow.Triangular src945) 2411 2314 [2320, 2341, 2405, 2411] := triangleCover (by decide +kernel)
def src946 : Request := ⟨⟨⟨825,1151,248,12355⟩,16903818182656,48256472894⟩,2,3,1,385979,27⟩
theorem cover946 : PhysicalWindow.Cover (PhysicalWindow.Triangular src946) 2411 2314 [2318, 2333, 2379, 2411] := triangleCover (by decide +kernel)
def src947 : Request := ⟨⟨⟨1000,1395,301,13899⟩,30103476895744,104105680031⟩,4,3,1,385979,27⟩
theorem cover947 : PhysicalWindow.Cover (PhysicalWindow.Triangular src947) 2411 2314 [2319, 2336, 2387, 2411] := triangleCover (by decide +kernel)
def src948 : Request := ⟨⟨⟨1000,1395,307,17590⟩,30557599170560,105715278267⟩,6,3,1,385979,27⟩
theorem cover948 : PhysicalWindow.Cover (PhysicalWindow.Triangular src948) 2411 2314 [2326, 2365, 2411] := triangleCover (by decide +kernel)
def src949 : Request := ⟨⟨⟨1200,1674,368,17590⟩,52718727069696,218807905514⟩,8,3,1,385979,27⟩
theorem cover949 : PhysicalWindow.Cover (PhysicalWindow.Triangular src949) 2411 2314 [2323, 2353, 2411] := triangleCover (by decide +kernel)
def src950 : Request := ⟨⟨⟨1450,2023,445,22261⟩,92998964346880,466511127281⟩,13,3,1,385979,27⟩
theorem cover950 : PhysicalWindow.Cover (PhysicalWindow.Triangular src950) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src951 : Request := ⟨⟨⟨2600,3627,783,45124⟩,527755772952576,4741611634368⟩,32,3,1,385979,27⟩
theorem cover951 : PhysicalWindow.Cover (PhysicalWindow.Triangular src951) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src954 : Request := ⟨⟨⟨4800,6697,1474,72277⟩,3367547627110400,55891290082931⟩,65,3,1,385979,27⟩
theorem cover954 : PhysicalWindow.Cover (PhysicalWindow.Triangular src954) 2411 2314 [2321, 2343, 2404, 2411] := triangleCover (by decide +kernel)
def src955 : Request := ⟨⟨⟨8300,11579,2548,264035⟩,17399709518790656,499124969898998⟩,145,3,1,385979,27⟩
theorem cover955 : PhysicalWindow.Cover (PhysicalWindow.Triangular src955) 2411 2314 [2315, 2321, 2337, 2381, 2411] := triangleCover (by decide +kernel)
def src956 : Request := ⟨⟨⟨10000,13952,3070,146522⟩,30428373265940480,1051954539834997⟩,145,3,1,385979,27⟩
theorem cover956 : PhysicalWindow.Cover (PhysicalWindow.Triangular src956) 2411 2314 [2320, 2339, 2392, 2411] := triangleCover (by decide +kernel)
def src957 : Request := ⟨⟨⟨690,963,212,8679⟩,10065769922560,24078187611⟩,0,3,1,385979,28⟩
theorem cover957 : PhysicalWindow.Cover (PhysicalWindow.Triangular src957) 2411 2314 [2323, 2353, 2411] := triangleCover (by decide +kernel)
def src958 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,1,3,1,385979,28⟩
theorem cover958 : PhysicalWindow.Cover (PhysicalWindow.Triangular src958) 2411 2314 [2333, 2393, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1500

-- Source: Research6969.PrefixRescueDataCubicSingletons22
section Z6969Source1501
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons22
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,26⟩
  bank i := ![bank196 10983, bank203 12355, bank204 13899, bank221 13899, bank221 15636, bank222 19788, bank228 19788, bank253 31694, bank329 81311, bank368 475797, bank380 164837] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 20, 65, 145, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 26

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank196 10983
    · exact rank203 12355
    · exact rank204 13899
    · exact rank221 13899
    · exact rank221 15636
    · exact rank222 19788
    · exact rank228 19788
    · exact rank253 31694
    · exact rank329 81311
    · exact rank368 475797
    · exact rank380 164837
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover931⟩
    · exact ⟨_, cover932⟩
    · exact ⟨_, cover933⟩
    · exact ⟨_, cover934⟩
    · exact ⟨_, cover935⟩
    · exact ⟨_, cover936⟩
    · exact ⟨_, cover937⟩
    · exact ⟨_, cover938⟩
    · exact ⟨_, cover941⟩
    · exact ⟨_, cover942⟩
    · exact ⟨_, cover943⟩

def price : EarlyPrice := ⟨3, 26, 10, 75/100, 70/100, ![4815834527952, 461860527717, 31073361120, 2390280510], 2915817316349592⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16675/146, 244657/146, 857263/146, 2142881/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons22
end Z6969Source1501

-- Source: Research6969.PrefixNearSavedCubicSingletons22
section Z6969Source1502
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons22
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨336,4530,114,1675,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons22.plan Lower6960.Prefix6969RescueData.CubicSingletons22.plan Lower6960.Prefix6969RescueData.CubicSingletons22.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 26 26 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons22.plan, Lower6960.Prefix6969MainCases.CubicSingletons22.price, Lower6960.Prefix6969MainCases.CubicSingletons22.valid, Lower6960.Prefix6969MainCases.CubicSingletons22.priced, Lower6960.Prefix6969MainCases.CubicSingletons22.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons22.plan, Lower6960.Prefix6969RescueData.CubicSingletons22.price, Lower6960.Prefix6969RescueData.CubicSingletons22.sources, Lower6960.Prefix6969RescueData.CubicSingletons22.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 210483833156175973 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons22
end Z6969Source1502

-- Source: Research6969.PrefixMainDataCubicSingletons23
section Z6969Source1503
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons23
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank37 2039, bank44 2409, bank54 2755, bank74 3583, bank84 5564, bank98 3253, bank137 3540, bank129 24535, bank161 6246, bank199 9241, bank183 54742, bank212 10770, bank174 148759, bank169 292467] i
  head := src1412
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15525, 161359, 746424, 3403536],
    ![25417/2, 482051/4, 547235, 2411809],
    ![54680/9, 525230/9, 547235, 2411809],
    ![29433/8, 565859/16, 2562178/9, 10831334/9],
    ![64334/25, 604221/25, 204050, 3705625/4],
    ![17323/9, 647173/36, 2911819/16, 12015827/16],
    ![18775/16, 733645/64, 396682/3, 14196237/25],
    ![89110/121, 851395/121, 3859402/49, 16235215/49],
    ![89110/121, 851395/121, 1336459/18, 16235215/49],
    ![63754/121, 2917142/441, 6599571/98, 16235215/49],
    ![63754/121, 2917142/441, 6599571/98, 19169929/72],
    ![63754/121, 692212/121, 435135/7, 783225/4],
    ![33263/82, 692212/121, 435135/7, 783225/4],
    ![33263/82, 8419524/1681, 9459703/196, 18403839/98],
    ![33263/82, 6147370/1323, 41538537/968, 163371639/968],
    ![954471/2738, 6147370/1323, 41538537/968, 163371639/968],
    ![954471/2738, 24655337/5476, 110796105/2704, 163371639/968],
    ![462882/1369, 24655337/5476, 110796105/2704, 163371639/968],
    ![459151/1369, 24655337/5476, 110796105/2704, 163371639/968]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 27 385979 := by
  refine ⟨?_, rank154 5893, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1412⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free74_1
    · exact free84_0
    · exact free98_0
    · exact free137_0
    · exact free129_0
    · exact free161_0
    · exact free199_0
    · exact free183_0
    · exact free212_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [315519023, 313810136, 313831322, 313978013, 313751880, 314280867, 313808556, 146672199, 146460250, 146664988, 146587349, 72339958, 72750215, 81663118, 92851341, 93162524, 119591000, 166621412, 229695931], [1111177, 1119921, 1119813, 1119062, 1120219, 1117512, 1119929, 2624232, 2628880, 2624390, 2626093, 5541358, 5508745, 4884300, 4272488, 4256792, 3275661, 2291030, 1615490],
  ![121927194093420, 1611666867284, 206726337900, 5083139740], 169642095762488152⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,8,8,8,8,15,15,13,12,12,9,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 24655337/5476, 110796105/2704, 163371639/968] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons23
end Z6969Source1503

-- Source: Research6969.PrefixRescueDataCubicSingletons23
section Z6969Source1504
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons23
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,27⟩
  bank i := ![bank196 9763, bank203 10983, bank203 12355, bank221 13899, bank222 17590, bank228 17590, bank237 22261, bank266 45124, bank329 72277, bank368 264035, bank380 146522] i
  reserve i := ![0, 1, 2, 4, 6, 8, 13, 32, 65, 145, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 27

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank196 9763
    · exact rank203 10983
    · exact rank203 12355
    · exact rank221 13899
    · exact rank222 17590
    · exact rank228 17590
    · exact rank237 22261
    · exact rank266 45124
    · exact rank329 72277
    · exact rank368 264035
    · exact rank380 146522
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover944⟩
    · exact ⟨_, cover945⟩
    · exact ⟨_, cover946⟩
    · exact ⟨_, cover947⟩
    · exact ⟨_, cover948⟩
    · exact ⟨_, cover949⟩
    · exact ⟨_, cover950⟩
    · exact ⟨_, cover951⟩
    · exact ⟨_, cover954⟩
    · exact ⟨_, cover955⟩
    · exact ⟨_, cover956⟩

def price : EarlyPrice := ⟨3, 27, 10, 75/100, 70/100, ![2775247593780, 300499812903, 32268487560, 2390280510], 2158498060181870⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16675/146, 114706/73, 408135/73, 1978047/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons23
end Z6969Source1504

-- Source: Research6969.PrefixNearSavedCubicSingletons23
section Z6969Source1505
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons23
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4502,114,1571,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons23.plan Lower6960.Prefix6969RescueData.CubicSingletons23.plan Lower6960.Prefix6969RescueData.CubicSingletons23.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 27 27 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons23.plan, Lower6960.Prefix6969MainCases.CubicSingletons23.price, Lower6960.Prefix6969MainCases.CubicSingletons23.valid, Lower6960.Prefix6969MainCases.CubicSingletons23.priced, Lower6960.Prefix6969MainCases.CubicSingletons23.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons23.plan, Lower6960.Prefix6969RescueData.CubicSingletons23.price, Lower6960.Prefix6969RescueData.CubicSingletons23.sources, Lower6960.Prefix6969RescueData.CubicSingletons23.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 209336878889025441 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons23
end Z6969Source1505

-- Source: Research6969.PrefixMainDataCubicSingletons24
section Z6969Source1506
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons24
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 20, 25, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank37 2039, bank44 2409, bank54 2755, bank74 3583, bank84 5564, bank109 3631, bank140 3997, bank129 24535, bank161 6246, bank212 10770, bank186 46700, bank174 148759, bank169 292467] i
  head := src1413
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15525, 161217, 745228, 3387567],
    ![25417/2, 119819, 544085, 2411809],
    ![54680/9, 522230/9, 544085, 2411809],
    ![29433/8, 281317/8, 2547628/9, 10693484/9],
    ![64334/25, 600696/25, 204050, 3705625/4],
    ![17323/9, 160837/9, 1447397/8, 5931451/8],
    ![18775/16, 45595/4, 3296794/25, 14015562/25],
    ![89110/121, 846520/121, 3837352/49, 16028590/49],
    ![89110/121, 846520/121, 1336459/18, 16028590/49],
    ![63754/121, 2904092/441, 3285123/49, 16028590/49],
    ![63754/121, 39728/7, 2809522/49, 10562579/49],
    ![63754/121, 39728/7, 2809522/49, 11627273/54],
    ![33263/82, 39728/7, 2809522/49, 11627273/54],
    ![33263/82, 8366424/1681, 671477/14, 9084807/49],
    ![33263/82, 12252331/2738, 55063365/1352, 146206340/867],
    ![481425/1369, 12252331/2738, 55063365/1352, 146206340/867],
    ![462882/1369, 12252331/2738, 55063365/1352, 146206340/867],
    ![459151/1369, 12252331/2738, 55063365/1352, 146206340/867]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 28 385979 := by
  refine ⟨?_, rank154 5818, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1413⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free74_1
    · exact free84_0
    · exact free109_0
    · exact free140_0
    · exact free129_0
    · exact free161_0
    · exact free212_0
    · exact free186_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [314065844, 313056431, 313739106, 313423910, 312550243, 311771873, 312234714, 146566664, 146522235, 146798929, 104439358, 74576199, 75486602, 94569194, 94633016, 119635706, 166210877, 229382775], [1118613, 1123778, 1120285, 1121897, 1126368, 1130351, 1127982, 2626546, 2627521, 2621453, 3771884, 5363588, 5298768, 4185842, 4182623, 3274411, 2297858, 1618065],
  ![121760964625500, 1612005324480, 206444497500, 4980054800], 169014930302463529⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,8,8,8,10,15,14,12,12,9,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 12252331/2738, 55063365/1352, 146206340/867] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons24
end Z6969Source1506

-- Source: Research6969.PhysicalChecks077
section Z6969Source1507
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src959 : Request := ⟨⟨⟨825,1151,248,10983⟩,16903818182656,48256472894⟩,2,3,1,385979,28⟩
theorem cover959 : PhysicalWindow.Cover (PhysicalWindow.Triangular src959) 2411 2314 [2318, 2333, 2379, 2411] := triangleCover (by decide +kernel)
def src960 : Request := ⟨⟨⟨825,1151,253,12355⟩,17161575202816,49010625289⟩,3,3,1,385979,28⟩
theorem cover960 : PhysicalWindow.Cover (PhysicalWindow.Triangular src960) 2411 2314 [2329, 2378, 2411] := triangleCover (by decide +kernel)
def src961 : Request := ⟨⟨⟨825,1151,253,13899⟩,17161575202816,49010625289⟩,4,3,1,385979,28⟩
theorem cover961 : PhysicalWindow.Cover (PhysicalWindow.Triangular src961) 2411 2314 [2320, 2341, 2404, 2411] := triangleCover (by decide +kernel)
def src962 : Request := ⟨⟨⟨1000,1395,307,13899⟩,30557599170560,105715278267⟩,6,3,1,385979,28⟩
theorem cover962 : PhysicalWindow.Cover (PhysicalWindow.Triangular src962) 2411 2314 [2317, 2329, 2364, 2411] := triangleCover (by decide +kernel)
def src963 : Request := ⟨⟨⟨1200,1674,368,15636⟩,52718727069696,218807905514⟩,8,3,1,385979,28⟩
theorem cover963 : PhysicalWindow.Cover (PhysicalWindow.Triangular src963) 2411 2314 [2325, 2360, 2411] := triangleCover (by decide +kernel)
def src964 : Request := ⟨⟨⟨1450,2023,445,19788⟩,92998964346880,466511127281⟩,13,3,1,385979,28⟩
theorem cover964 : PhysicalWindow.Cover (PhysicalWindow.Triangular src964) 2411 2314 [2318, 2333, 2376, 2411] := triangleCover (by decide +kernel)
def src965 : Request := ⟨⟨⟨2600,3627,798,35655⟩,535425056505856,4812227595495⟩,32,3,1,385979,28⟩
theorem cover965 : PhysicalWindow.Cover (PhysicalWindow.Triangular src965) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src968 : Request := ⟨⟨⟨8300,11579,2548,185441⟩,17399709518790656,499124969898998⟩,145,3,1,385979,28⟩
theorem cover968 : PhysicalWindow.Cover (PhysicalWindow.Triangular src968) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src969 : Request := ⟨⟨⟨10000,13952,3070,130242⟩,30428373265940480,1051954539834997⟩,145,3,1,385979,28⟩
theorem cover969 : PhysicalWindow.Cover (PhysicalWindow.Triangular src969) 2411 2314 [2321, 2343, 2404, 2411] := triangleCover (by decide +kernel)
def src970 : Request := ⟨⟨⟨690,963,212,7715⟩,10065769922560,24078187611⟩,0,3,1,385979,29⟩
theorem cover970 : PhysicalWindow.Cover (PhysicalWindow.Triangular src970) 2411 2314 [2319, 2338, 2396, 2411] := triangleCover (by decide +kernel)
def src971 : Request := ⟨⟨⟨690,963,212,8679⟩,10065769922560,24078187611⟩,1,3,1,385979,29⟩
theorem cover971 : PhysicalWindow.Cover (PhysicalWindow.Triangular src971) 2411 2314 [2318, 2333, 2379, 2411] := triangleCover (by decide +kernel)
def src972 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,2,3,1,385979,29⟩
theorem cover972 : PhysicalWindow.Cover (PhysicalWindow.Triangular src972) 2411 2314 [2333, 2394, 2411] := triangleCover (by decide +kernel)
def src973 : Request := ⟨⟨⟨825,1151,253,10983⟩,17161575202816,49010625289⟩,3,3,1,385979,29⟩
theorem cover973 : PhysicalWindow.Cover (PhysicalWindow.Triangular src973) 2411 2314 [2333, 2393, 2411] := triangleCover (by decide +kernel)
def src974 : Request := ⟨⟨⟨1000,1395,307,12355⟩,30557599170560,105715278267⟩,6,3,1,385979,29⟩
theorem cover974 : PhysicalWindow.Cover (PhysicalWindow.Triangular src974) 2411 2314 [2318, 2333, 2377, 2411] := triangleCover (by decide +kernel)
def src975 : Request := ⟨⟨⟨1450,2023,445,22261⟩,92998964346880,466511127281⟩,16,3,1,385979,29⟩
theorem cover975 : PhysicalWindow.Cover (PhysicalWindow.Triangular src975) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src976 : Request := ⟨⟨⟨2600,3627,798,31694⟩,535425056505856,4812227595495⟩,32,3,1,385979,29⟩
theorem cover976 : PhysicalWindow.Cover (PhysicalWindow.Triangular src976) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1507

-- Source: Research6969.PrefixRescueDataCubicSingletons24
section Z6969Source1508
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons24
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,28⟩
  bank i := ![bank196 8679, bank204 9763, bank203 10983, bank204 12355, bank204 13899, bank222 13899, bank228 15636, bank237 19788, bank267 35655, bank368 185441, bank380 130242] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 13, 32, 145, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 28

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank196 8679
    · exact rank204 9763
    · exact rank203 10983
    · exact rank204 12355
    · exact rank204 13899
    · exact rank222 13899
    · exact rank228 15636
    · exact rank237 19788
    · exact rank267 35655
    · exact rank368 185441
    · exact rank380 130242
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover957⟩
    · exact ⟨_, cover958⟩
    · exact ⟨_, cover959⟩
    · exact ⟨_, cover960⟩
    · exact ⟨_, cover961⟩
    · exact ⟨_, cover962⟩
    · exact ⟨_, cover963⟩
    · exact ⟨_, cover964⟩
    · exact ⟨_, cover965⟩
    · exact ⟨_, cover968⟩
    · exact ⟨_, cover969⟩

def price : EarlyPrice := ⟨3, 28, 10, 75/100, 70/100, ![2021344173641, 242822779744, 33463617070, 2390280510], 1871044654339709⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16675/146, 108101/73, 390691/73, 1823388/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons24
end Z6969Source1508

-- Source: Research6969.PrefixNearSavedCubicSingletons24
section Z6969Source1509
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons24
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4474,114,1480,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons24.plan Lower6960.Prefix6969RescueData.CubicSingletons24.plan Lower6960.Prefix6969RescueData.CubicSingletons24.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 28 28 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons24.plan, Lower6960.Prefix6969MainCases.CubicSingletons24.price, Lower6960.Prefix6969MainCases.CubicSingletons24.valid, Lower6960.Prefix6969MainCases.CubicSingletons24.priced, Lower6960.Prefix6969MainCases.CubicSingletons24.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons24.plan, Lower6960.Prefix6969RescueData.CubicSingletons24.price, Lower6960.Prefix6969RescueData.CubicSingletons24.sources, Lower6960.Prefix6969RescueData.CubicSingletons24.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 208979025316045094 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons24
end Z6969Source1509

-- Source: Research6969.PrefixMainDataCubicSingletons25
section Z6969Source1510
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons25
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank37 2039, bank44 2409, bank54 2755, bank74 3583, bank84 5564, bank98 3253, bank137 3540, bank129 24535, bank161 6246, bank199 9241, bank181 61748, bank212 10770, bank174 148759, bank169 292467] i
  head := src1414
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15525, 160912, 743891, 3379696],
    ![25417/2, 238269/2, 540977, 2411809],
    ![54680/9, 173090/3, 540977, 2411809],
    ![29433/8, 139863/4, 844424/3, 10557472/9],
    ![64334/25, 597218/25, 204050, 3705625/4],
    ![17323/9, 319787/18, 719499/4, 732001],
    ![18775/16, 362725/32, 3278516/25, 13837296/25],
    ![89110/121, 841710/121, 3815596/49, 15824720/49],
    ![89110/121, 841710/121, 1336459/18, 15824720/49],
    ![63754/121, 2891216/441, 3270656/49, 15824720/49],
    ![63754/121, 2891216/441, 3270656/49, 2335654/9],
    ![63754/121, 682676/121, 3003480/49, 783225/4],
    ![33263/82, 682676/121, 3003480/49, 783225/4],
    ![33263/82, 8314032/1681, 2335610/49, 8969256/49],
    ![33263/82, 867340/189, 10257351/242, 19905114/121],
    ![474397/1369, 867340/189, 10257351/242, 19905114/121],
    ![474397/1369, 6088999/1369, 6865875/169, 19905114/121],
    ![462882/1369, 6088999/1369, 6865875/169, 19905114/121],
    ![459151/1369, 6088999/1369, 6865875/169, 19905114/121]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 29 385979 := by
  refine ⟨?_, rank154 5744, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1414⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free74_1
    · exact free84_0
    · exact free98_0
    · exact free137_0
    · exact free129_0
    · exact free161_0
    · exact free199_0
    · exact free181_0
    · exact free212_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [312506094, 311290955, 311650254, 312339869, 311170535, 310377337, 311187118, 146561426, 146501767, 146524901, 146663812, 68194073, 68213549, 82117313, 94825360, 95297204, 118637596, 165976447, 229202843], [1126594, 1132812, 1130973, 1127444, 1133428, 1137487, 1133343, 2626661, 2627970, 2627462, 2624416, 5889497, 5887731, 4857324, 4173969, 4154050, 3302318, 2301756, 1619545],
  ![121665453121260, 1612199510572, 206282558700, 4965928310], 167906681013079821⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,8,8,8,8,16,16,13,11,11,9,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 6088999/1369, 6865875/169, 19905114/121] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons25
end Z6969Source1510

-- Source: Research6969.PhysicalChecks078
section Z6969Source1511
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src979 : Request := ⟨⟨⟨4800,6696,1474,130242⟩,3367547627110400,55864419956306⟩,85,3,1,385979,29⟩
theorem cover979 : PhysicalWindow.Cover (PhysicalWindow.Triangular src979) 2411 2314 [2315, 2321, 2337, 2381, 2411] := triangleCover (by decide +kernel)
def src980 : Request := ⟨⟨⟨5700,7952,1750,72277⟩,5637370734182400,111070724916873⟩,85,3,1,385979,29⟩
theorem cover980 : PhysicalWindow.Cover (PhysicalWindow.Triangular src980) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src981 : Request := ⟨⟨⟨6900,9626,2118,102908⟩,9997036108906496,238415548481346⟩,110,3,1,385979,29⟩
theorem cover981 : PhysicalWindow.Cover (PhysicalWindow.Triangular src981) 2411 2314 [2327, 2365, 2411] := triangleCover (by decide +kernel)
def src982 : Request := ⟨⟨⟨10000,13952,3070,115771⟩,30428373265940480,1051954539834997⟩,145,3,1,385979,29⟩
theorem cover982 : PhysicalWindow.Cover (PhysicalWindow.Triangular src982) 2411 2314 [2320, 2339, 2391, 2411] := triangleCover (by decide +kernel)
def src983 : Request := ⟨⟨⟨560,781,169,8679⟩,5316921262080,10299257375⟩,0,3,1,385979,30⟩
theorem cover983 : PhysicalWindow.Cover (PhysicalWindow.Triangular src983) 2411 2314 [2320, 2342, 2411] := triangleCover (by decide +kernel)
def src984 : Request := ⟨⟨⟨690,963,208,8679⟩,9921631092736,23724874690⟩,1,3,1,385979,30⟩
theorem cover984 : PhysicalWindow.Cover (PhysicalWindow.Triangular src984) 2411 2314 [2324, 2358, 2411] := triangleCover (by decide +kernel)
def src985 : Request := ⟨⟨⟨690,962,208,9763⟩,9921631092736,23645774460⟩,2,3,1,385979,30⟩
theorem cover985 : PhysicalWindow.Cover (PhysicalWindow.Triangular src985) 2411 2314 [2319, 2338, 2397, 2411] := triangleCover (by decide +kernel)
def src986 : Request := ⟨⟨⟨825,1151,253,10983⟩,17161575202816,49010625289⟩,4,3,1,385979,30⟩
theorem cover986 : PhysicalWindow.Cover (PhysicalWindow.Triangular src986) 2411 2314 [2331, 2386, 2411] := triangleCover (by decide +kernel)
def src987 : Request := ⟨⟨⟨1000,1395,315,10983⟩,31157463285760,107844841957⟩,6,3,1,385979,30⟩
theorem cover987 : PhysicalWindow.Cover (PhysicalWindow.Triangular src987) 2411 2314 [2317, 2328, 2361, 2411] := triangleCover (by decide +kernel)
def src988 : Request := ⟨⟨⟨1200,1674,378,13899⟩,53798525730816,223406703910⟩,10,3,1,385979,30⟩
theorem cover988 : PhysicalWindow.Cover (PhysicalWindow.Triangular src988) 2411 2314 [2317, 2329, 2364, 2411] := triangleCover (by decide +kernel)
def src989 : Request := ⟨⟨⟨2100,2930,645,25043⟩,282396798484480,2051392203643⟩,25,3,1,385979,30⟩
theorem cover989 : PhysicalWindow.Cover (PhysicalWindow.Triangular src989) 2411 2314 [2324, 2355, 2411] := triangleCover (by decide +kernel)
def src992 : Request := ⟨⟨⟨3950,5510,1213,64247⟩,1877062482395136,25622281045803⟩,65,3,1,385979,30⟩
theorem cover992 : PhysicalWindow.Cover (PhysicalWindow.Triangular src992) 2411 2314 [2324, 2355, 2411] := triangleCover (by decide +kernel)
def src993 : Request := ⟨⟨⟨5700,7952,1796,64247⟩,5749327563587584,113334118485107⟩,85,3,1,385979,30⟩
theorem cover993 : PhysicalWindow.Cover (PhysicalWindow.Triangular src993) 2411 2314 [2318, 2332, 2370, 2411] := triangleCover (by decide +kernel)
def src994 : Request := ⟨⟨⟨8300,11579,2548,115771⟩,17399709518790656,499124969898998⟩,145,3,1,385979,30⟩
theorem cover994 : PhysicalWindow.Cover (PhysicalWindow.Triangular src994) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src995 : Request := ⟨⟨⟨10000,13950,3070,185441⟩,30428373265940480,1051468979452278⟩,190,3,1,385979,30⟩
theorem cover995 : PhysicalWindow.Cover (PhysicalWindow.Triangular src995) 2411 2314 [2316, 2324, 2346, 2406, 2411] := triangleCover (by decide +kernel)
def src996 : Request := ⟨⟨⟨560,781,172,6858⟩,5388141854720,10440670587⟩,0,3,1,385979,31⟩
theorem cover996 : PhysicalWindow.Cover (PhysicalWindow.Triangular src996) 2411 2314 [2320, 2342, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1511

end Merged_Z6969Pack0703

-- merged module Z6969Pack0704
section Merged_Z6969Pack0704

-- Source: Research6969.PrefixRescueDataCubicSingletons25
section Z6969Source1512
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons25
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,29⟩
  bank i := ![bank196 7715, bank196 8679, bank204 9763, bank204 10983, bank222 12355, bank237 22261, bank267 31694, bank343 72277, bank326 130242, bank380 115771, bank356 102908] i
  reserve i := ![0, 1, 2, 3, 6, 16, 32, 85, 85, 145, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 29

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank196 7715
    · exact rank196 8679
    · exact rank204 9763
    · exact rank204 10983
    · exact rank222 12355
    · exact rank237 22261
    · exact rank267 31694
    · exact rank343 72277
    · exact rank326 130242
    · exact rank380 115771
    · exact rank356 102908
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover970⟩
    · exact ⟨_, cover971⟩
    · exact ⟨_, cover972⟩
    · exact ⟨_, cover973⟩
    · exact ⟨_, cover974⟩
    · exact ⟨_, cover975⟩
    · exact ⟨_, cover976⟩
    · exact ⟨_, cover980⟩
    · exact ⟨_, cover979⟩
    · exact ⟨_, cover982⟩
    · exact ⟨_, cover981⟩

def price : EarlyPrice := ⟨3, 29, 10, 70/100, 70/100, ![1470366277548, 212990763911, 34658746580, 2390280510], 1592081250881518⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![4822/43, 204801/146, 751921/146, 3357359/146] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons25
end Z6969Source1512

-- Source: Research6969.PrefixNearSavedCubicSingletons25
section Z6969Source1513
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons25
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4447,112,1402,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons25.plan Lower6960.Prefix6969RescueData.CubicSingletons25.plan Lower6960.Prefix6969RescueData.CubicSingletons25.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 29 29 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons25.plan, Lower6960.Prefix6969MainCases.CubicSingletons25.price, Lower6960.Prefix6969MainCases.CubicSingletons25.valid, Lower6960.Prefix6969MainCases.CubicSingletons25.priced, Lower6960.Prefix6969MainCases.CubicSingletons25.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons25.plan, Lower6960.Prefix6969RescueData.CubicSingletons25.price, Lower6960.Prefix6969RescueData.CubicSingletons25.sources, Lower6960.Prefix6969RescueData.CubicSingletons25.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 207974249494598757 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons25
end Z6969Source1513

-- Source: Research6969.PrefixMainDataCubicSingletons26
section Z6969Source1514
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons26
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 20, 30, 30, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank37 2039, bank44 2409, bank54 2755, bank74 3583, bank84 5564, bank115 3521, bank168 4492, bank94 16634, bank152 6378, bank199 9241, bank183 54742, bank212 10770, bank170 227095] i
  head := src1415
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15525, 161275, 745562, 3371054],
    ![25417/2, 473837/4, 537911, 2411809],
    ![54680/9, 516350/9, 537911, 2411809],
    ![29433/8, 556313/16, 2519110/9, 10423298/9],
    ![64334/25, 593787/25, 204050, 3705625/4],
    ![17323/9, 635851/36, 2861425/16, 11563169/16],
    ![18775/16, 721435/64, 652097/5, 13661439/25],
    ![89110/121, 836965/121, 3794134/49, 15623605/49],
    ![89110/121, 836965/121, 1336459/18, 15623605/49],
    ![63754/121, 2878514/441, 6512769/98, 15623605/49],
    ![63754/121, 2501470/441, 2805211/49, 2852513/14],
    ![63754/121, 2501470/441, 2805211/49, 25474132/147],
    ![22029/50, 2501470/441, 2805211/49, 25474132/147],
    ![22029/50, 8261372/1681, 9284815/196, 25474132/147],
    ![22029/50, 6034150/1323, 40779963/968, 157217133/968],
    ![954471/2738, 6034150/1323, 40779963/968, 157217133/968],
    ![954471/2738, 24209339/5476, 6865875/169, 157217133/968],
    ![920087/2738, 24209339/5476, 6865875/169, 157217133/968]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 30 385979 := by
  refine ⟨?_, rank154 5671, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1415⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free74_1
    · exact free84_0
    · exact free115_0
    · exact free168_0
    · exact free94_0
    · exact free152_0
    · exact free199_0
    · exact free183_0
    · exact free212_0
    · exact free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [311875365, 311746435, 310587576, 310690565, 310643824, 311272026, 309873456, 146715841, 146704182, 146247937, 103671694, 94406371, 62582396, 81061494, 93470509, 93422871, 146141226, 229460952], [1129821, 1130481, 1136411, 1135884, 1136123, 1132908, 1140065, 2623275, 2623531, 2633536, 3800525, 4194055, 6433524, 4920032, 4241258, 4243661, 2635876, 1617422],
  ![121802462540640, 1611920740488, 206514856800, 5048842750], 168095960143763090⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,8,8,8,11,12,17,13,12,12,8,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 24209339/5476, 6865875/169, 157217133/968] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons26
end Z6969Source1514

-- Source: Research6969.PrefixRescueDataCubicSingletons26
section Z6969Source1515
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons26
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,30⟩
  bank i := ![bank155 8679, bank195 8679, bank192 9763, bank204 10983, bank223 10983, bank229 13899, bank253 25043, bank310 64247, bank344 64247, bank377 185441, bank368 115771] i
  reserve i := ![0, 1, 2, 4, 6, 10, 25, 65, 85, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 30

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank155 8679
    · exact rank195 8679
    · exact rank192 9763
    · exact rank204 10983
    · exact rank223 10983
    · exact rank229 13899
    · exact rank253 25043
    · exact rank310 64247
    · exact rank344 64247
    · exact rank377 185441
    · exact rank368 115771
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover983⟩
    · exact ⟨_, cover984⟩
    · exact ⟨_, cover985⟩
    · exact ⟨_, cover986⟩
    · exact ⟨_, cover987⟩
    · exact ⟨_, cover988⟩
    · exact ⟨_, cover989⟩
    · exact ⟨_, cover992⟩
    · exact ⟨_, cover993⟩
    · exact ⟨_, cover995⟩
    · exact ⟨_, cover994⟩

def price : EarlyPrice := ⟨3, 30, 10, 70/100, 70/100, ![2165725940067, 271448267073, 35853876090, 2390280510], 1678394651522175⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![20090/191, 192211/146, 694683/146, 963705/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons26
end Z6969Source1515

-- Source: Research6969.PrefixNearSavedCubicSingletons26
section Z6969Source1516
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons26
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨336,4420,105,1316,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons26.plan Lower6960.Prefix6969RescueData.CubicSingletons26.plan Lower6960.Prefix6969RescueData.CubicSingletons26.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 30 30 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons26.plan, Lower6960.Prefix6969MainCases.CubicSingletons26.price, Lower6960.Prefix6969MainCases.CubicSingletons26.valid, Lower6960.Prefix6969MainCases.CubicSingletons26.priced, Lower6960.Prefix6969MainCases.CubicSingletons26.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons26.plan, Lower6960.Prefix6969RescueData.CubicSingletons26.price, Lower6960.Prefix6969RescueData.CubicSingletons26.sources, Lower6960.Prefix6969RescueData.CubicSingletons26.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 207460788245856758 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons26
end Z6969Source1516

-- Source: Research6969.PrefixMainDataCubicSingletons27
section Z6969Source1517
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons27
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 20, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank37 2039, bank44 2409, bank54 2755, bank74 3583, bank84 5564, bank115 3521, bank168 4492, bank130 22726, bank161 6246, bank212 10770, bank186 46700, bank175 125592, bank169 292467] i
  head := src1416
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15525, 161062, 744355, 3359197],
    ![25417/2, 235605/2, 534929, 2411809],
    ![54680/9, 171170/3, 534929, 2384200],
    ![29433/8, 138315/4, 835112/3, 10292800/9],
    ![64334/25, 23618, 204050, 3705625/4],
    ![17323/9, 316115/18, 711327/4, 713650],
    ![18775/16, 358765/32, 3242948/25, 539616],
    ![89110/121, 832350/121, 3773260/49, 2204000/7],
    ![89110/121, 832350/121, 1336459/18, 2204000/7],
    ![63754/121, 2866160/441, 3242504/49, 2204000/7],
    ![63754/121, 118340/21, 398158/7, 201200],
    ![63754/121, 118340/21, 398158/7, 3593600/21],
    ![33463/82, 118340/21, 398158/7, 3593600/21],
    ![33463/82, 8212080/1681, 2307278/49, 3593600/21],
    ![33463/82, 6016675/1369, 6865875/169, 140728000/867],
    ![481425/1369, 6016675/1369, 6865875/169, 140728000/867],
    ![929061/2738, 6016675/1369, 6865875/169, 140728000/867],
    ![459151/1369, 6016675/1369, 6865875/169, 140728000/867]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 31 385979 := by
  refine ⟨?_, rank154 5600, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1416⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free74_1
    · exact free84_0
    · exact free115_0
    · exact free168_0
    · exact free130_0
    · exact free161_0
    · exact free212_0
    · exact free186_0
    · exact free175_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [310439674, 310156179, 310344758, 309746105, 309388479, 309969212, 308245210, 133093846, 133435236, 133260852, 103399239, 64222020, 61388972, 92617221, 92600980, 111031703, 166106000, 229029350], [1137168, 1138618, 1137653, 1140716, 1142546, 1139575, 1148396, 2922000, 2914514, 2918338, 3812027, 6265428, 6560549, 4284296, 4285115, 3542985, 2299602, 1620972],
  ![121573359567000, 1612386708880, 206126415000, 5098163490], 167095210947964112⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,8,8,8,11,17,18,12,12,10,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 6016675/1369, 6865875/169, 140728000/867] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons27
end Z6969Source1517

-- Source: Research6969.PhysicalChecks079
section Z6969Source1518
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src997 : Request := ⟨⟨⟨690,963,208,7715⟩,9921631092736,23724874690⟩,1,3,1,385979,31⟩
theorem cover997 : PhysicalWindow.Cover (PhysicalWindow.Triangular src997) 2411 2314 [2320, 2342, 2410, 2411] := triangleCover (by decide +kernel)
def src998 : Request := ⟨⟨⟨690,962,208,8679⟩,9921631092736,23645774460⟩,2,3,1,385979,31⟩
theorem cover998 : PhysicalWindow.Cover (PhysicalWindow.Triangular src998) 2411 2314 [2321, 2346, 2411] := triangleCover (by decide +kernel)
def src999 : Request := ⟨⟨⟨690,962,212,9763⟩,10065769922560,23997864317⟩,3,3,1,385979,31⟩
theorem cover999 : PhysicalWindow.Cover (PhysicalWindow.Triangular src999) 2411 2314 [2326, 2366, 2411] := triangleCover (by decide +kernel)
def src1000 : Request := ⟨⟨⟨825,1151,253,12355⟩,17161575202816,49010625289⟩,6,3,1,385979,31⟩
theorem cover1000 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1000) 2411 2314 [2321, 2345, 2411] := triangleCover (by decide +kernel)
def src1001 : Request := ⟨⟨⟨1000,1395,307,12355⟩,30557599170560,105715278267⟩,8,3,1,385979,31⟩
theorem cover1001 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1001) 2411 2314 [2324, 2356, 2411] := triangleCover (by decide +kernel)
def src1002 : Request := ⟨⟨⟨1450,2023,445,17590⟩,92998964346880,466511127281⟩,16,3,1,385979,31⟩
theorem cover1002 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1002) 2411 2314 [2323, 2352, 2411] := triangleCover (by decide +kernel)
def src1003 : Request := ⟨⟨⟨2100,2929,645,31694⟩,282396798484480,2049139102608⟩,32,3,1,385979,31⟩
theorem cover1003 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1003) 2411 2314 [2317, 2329, 2362, 2411] := triangleCover (by decide +kernel)
def src1006 : Request := ⟨⟨⟨3950,5510,1213,50764⟩,1877062482395136,25622281045803⟩,65,3,1,385979,31⟩
theorem cover1006 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1006) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src1007 : Request := ⟨⟨⟨5700,7951,1750,115771⟩,5637370734182400,111025751789870⟩,110,3,1,385979,31⟩
theorem cover1007 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1007) 2411 2314 [2315, 2321, 2338, 2384, 2411] := triangleCover (by decide +kernel)
def src1008 : Request := ⟨⟨⟨8300,11579,2548,102908⟩,17399709518790656,499124969898998⟩,145,3,1,385979,31⟩
theorem cover1008 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1008) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src1009 : Request := ⟨⟨⟨560,781,176,6096⟩,5482316038144,10627925923⟩,0,3,1,385979,32⟩
theorem cover1009 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1009) 2411 2314 [2320, 2342, 2411] := triangleCover (by decide +kernel)
def src1010 : Request := ⟨⟨⟨690,963,212,6858⟩,10065769922560,24078187611⟩,1,3,1,385979,32⟩
theorem cover1010 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1010) 2411 2314 [2327, 2370, 2411] := triangleCover (by decide +kernel)
def src1011 : Request := ⟨⟨⟨690,962,208,7715⟩,9921631092736,23645774460⟩,2,3,1,385979,32⟩
theorem cover1011 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1011) 2411 2314 [2318, 2333, 2380, 2411] := triangleCover (by decide +kernel)
def src1012 : Request := ⟨⟨⟨690,962,212,9763⟩,10065769922560,23997864317⟩,4,3,1,385979,32⟩
theorem cover1012 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1012) 2411 2314 [2319, 2337, 2392, 2411] := triangleCover (by decide +kernel)
def src1013 : Request := ⟨⟨⟨825,1151,253,10983⟩,17161575202816,49010625289⟩,6,3,1,385979,32⟩
theorem cover1013 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1013) 2411 2314 [2327, 2369, 2411] := triangleCover (by decide +kernel)
def src1014 : Request := ⟨⟨⟨1000,1395,307,13899⟩,30557599170560,105715278267⟩,10,3,1,385979,32⟩
theorem cover1014 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1014) 2411 2314 [2323, 2353, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1518

-- Source: Research6969.PrefixRescueDataCubicSingletons27
section Z6969Source1519
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons27
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,31⟩
  bank i := ![bank156 6858, bank195 7715, bank192 8679, bank193 9763, bank204 12355, bank222 12355, bank237 17590, bank249 31694, bank310 50764, bank368 102908, bank340 115771] i
  reserve i := ![0, 1, 2, 3, 6, 8, 16, 32, 65, 145, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 31

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank156 6858
    · exact rank195 7715
    · exact rank192 8679
    · exact rank193 9763
    · exact rank204 12355
    · exact rank222 12355
    · exact rank237 17590
    · exact rank249 31694
    · exact rank310 50764
    · exact rank368 102908
    · exact rank340 115771
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover996⟩
    · exact ⟨_, cover997⟩
    · exact ⟨_, cover998⟩
    · exact ⟨_, cover999⟩
    · exact ⟨_, cover1000⟩
    · exact ⟨_, cover1001⟩
    · exact ⟨_, cover1002⟩
    · exact ⟨_, cover1003⟩
    · exact ⟨_, cover1006⟩
    · exact ⟨_, cover1008⟩
    · exact ⟨_, cover1007⟩

def price : EarlyPrice := ⟨3, 31, 10, 70/100, 70/100, ![1397133573909, 189110269893, 30749465292, 1983854964], 1279715224043854⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![3817/37, 90948/73, 667673/146, 1595074/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons27
end Z6969Source1519

-- Source: Research6969.PrefixNearSavedCubicSingletons27
section Z6969Source1520
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons27
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4394,103,1245,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons27.plan Lower6960.Prefix6969RescueData.CubicSingletons27.plan Lower6960.Prefix6969RescueData.CubicSingletons27.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 31 31 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons27.plan, Lower6960.Prefix6969MainCases.CubicSingletons27.price, Lower6960.Prefix6969MainCases.CubicSingletons27.valid, Lower6960.Prefix6969MainCases.CubicSingletons27.priced, Lower6960.Prefix6969MainCases.CubicSingletons27.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons27.plan, Lower6960.Prefix6969RescueData.CubicSingletons27.price, Lower6960.Prefix6969RescueData.CubicSingletons27.sources, Lower6960.Prefix6969RescueData.CubicSingletons27.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 206409605670827754 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons27
end Z6969Source1520

-- Source: Research6969.PrefixMainDataCubicSingletons28
section Z6969Source1521
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons28
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 20, 18, 21, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank58 2557, bank77 5503, bank82 2965, bank75 5459, bank104 3359, bank137 3540, bank144 4704, bank129 24535, bank161 6246, bank212 10770, bank183 54742, bank174 148759, bank169 292467] i
  head := src1417
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15088, 161831, 749096, 3619466],
    ![25417/2, 117155, 531989, 2411809],
    ![54680/9, 510710/9, 531989, 4708795/2],
    ![29433/8, 275125/8, 2491756/9, 10164140/9],
    ![16211/9, 53435/3, 1460273/8, 6201895/8],
    ![24292/27, 801220/81, 1820119/18, 8934121/16],
    ![73478/121, 1072460/121, 4846874/49, 8934121/16],
    ![73478/121, 1072460/121, 282257/3, 1540081/4],
    ![73478/121, 821790/121, 3699364/49, 2020030/7],
    ![78398/147, 2888054/441, 1051073/16, 2020030/7],
    ![78398/147, 2888054/441, 1051073/16, 2020030/7],
    ![3719/7, 45681/7, 2058043/32, 2020030/7],
    ![3719/7, 2292300/361, 3090280/49, 11282881/49],
    ![3719/7, 668980/121, 2942490/49, 783225/4],
    ![3719/7, 32473/6, 6256320/121, 22127616/121],
    ![33263/82, 32473/6, 6256320/121, 22127616/121],
    ![33263/82, 8162520/1681, 4587011/98, 1233585/7],
    ![33263/82, 11963035/2738, 6865875/169, 138968900/867],
    ![954471/2738, 11963035/2738, 6865875/169, 138968900/867],
    ![462882/1369, 11963035/2738, 6865875/169, 138968900/867],
    ![459151/1369, 11963035/2738, 6865875/169, 138968900/867]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 32 385979 := by
  refine ⟨?_, rank154 5530, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1417⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free58_0
    · exact free77_0
    · exact free82_0
    · exact free75_0
    · exact free104_0
    · exact free137_0
    · exact free144_0
    · exact free129_0
    · exact free161_0
    · exact free212_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [308205222, 307788017, 308007106, 308049519, 308217248, 307803044, 311505554, 311291929, 155763541, 156718848, 156417023, 156572094, 156999023, 105414303, 71746476, 77178426, 91864131, 91934712, 118615190, 165645602, 228945013], [1148601, 1150736, 1149615, 1149398, 1148539, 1150659, 1131714, 1132807, 2471596, 2455710, 2460729, 2458150, 2451050, 3738032, 5588537, 5181899, 4322281, 4318721, 3302945, 2307258, 1621665],
  ![121528591800660, 1612478135252, 206050511700, 5142380320], 166776137713363509⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,4,7,7,7,7,7,10,15,14,12,12,9,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 11963035/2738, 6865875/169, 138968900/867] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons28
end Z6969Source1521

-- Source: Research6969.PhysicalChecks080
section Z6969Source1522
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1015 : Request := ⟨⟨⟨1750,2441,537,22261⟩,163381988556800,988269431527⟩,25,3,1,385979,32⟩
theorem cover1015 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1015) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src1016 : Request := ⟨⟨⟨3950,5510,1213,45124⟩,1877062482395136,25622281045803⟩,65,3,1,385979,32⟩
theorem cover1016 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1016) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src1017 : Request := ⟨⟨⟨4800,6696,1512,57109⟩,3433136573644800,56980856955989⟩,85,3,1,385979,32⟩
theorem cover1017 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1017) 2411 2314 [2315, 2321, 2337, 2381, 2411] := triangleCover (by decide +kernel)
def src1018 : Request := ⟨⟨⟨5700,7951,1750,91474⟩,5637370734182400,111025751789870⟩,110,3,1,385979,32⟩
theorem cover1018 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1018) 2411 2314 [2322, 2347, 2411] := triangleCover (by decide +kernel)
def src1019 : Request := ⟨⟨⟨8300,11579,2548,91474⟩,17399709518790656,499124969898998⟩,145,3,1,385979,32⟩
theorem cover1019 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1019) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src1020 : Request := ⟨⟨⟨560,781,169,6096⟩,5316921262080,10299257375⟩,0,3,1,385979,33⟩
theorem cover1020 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1020) 2411 2314 [2323, 2355, 2411] := triangleCover (by decide +kernel)
def src1021 : Request := ⟨⟨⟨560,781,172,6858⟩,5388141854720,10440670587⟩,1,3,1,385979,33⟩
theorem cover1021 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1021) 2411 2314 [2329, 2380, 2411] := triangleCover (by decide +kernel)
def src1022 : Request := ⟨⟨⟨690,962,212,6858⟩,10065769922560,23997864317⟩,2,3,1,385979,33⟩
theorem cover1022 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1022) 2411 2314 [2326, 2366, 2411] := triangleCover (by decide +kernel)
def src1023 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,3,3,1,385979,33⟩
theorem cover1023 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1023) 2411 2314 [2330, 2383, 2411] := triangleCover (by decide +kernel)
def src1024 : Request := ⟨⟨⟨690,962,212,8679⟩,10065769922560,23997864317⟩,4,3,1,385979,33⟩
theorem cover1024 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1024) 2411 2314 [2324, 2358, 2411] := triangleCover (by decide +kernel)
def src1025 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,6,3,1,385979,33⟩
theorem cover1025 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1025) 2411 2314 [2330, 2381, 2411] := triangleCover (by decide +kernel)
def src1026 : Request := ⟨⟨⟨1000,1395,307,12355⟩,30557599170560,105715278267⟩,10,3,1,385979,33⟩
theorem cover1026 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1026) 2411 2314 [2328, 2372, 2411] := triangleCover (by decide +kernel)
def src1027 : Request := ⟨⟨⟨1750,2441,537,19788⟩,163381988556800,988269431527⟩,25,3,1,385979,33⟩
theorem cover1027 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1027) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src1030 : Request := ⟨⟨⟨3950,5510,1244,40111⟩,1913299978158080,26129827888718⟩,65,3,1,385979,33⟩
theorem cover1030 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1030) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src1031 : Request := ⟨⟨⟨6900,9625,2118,115771⟩,9997036108906496,238335796784464⟩,145,3,1,385979,33⟩
theorem cover1031 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1031) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src1032 : Request := ⟨⟨⟨10000,13950,3070,115771⟩,30428373265940480,1051468979452278⟩,190,3,1,385979,33⟩
theorem cover1032 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1032) 2411 2314 [2323, 2350, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1522

-- Source: Research6969.PrefixRescueDataCubicSingletons28
section Z6969Source1523
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons28
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,32⟩
  bank i := ![bank157 6096, bank196 6858, bank192 7715, bank193 9763, bank204 10983, bank222 13899, bank242 22261, bank310 45124, bank368 91474, bank340 91474, bank327 57109] i
  reserve i := ![0, 1, 2, 4, 6, 10, 25, 65, 145, 110, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 32

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank157 6096
    · exact rank196 6858
    · exact rank192 7715
    · exact rank193 9763
    · exact rank204 10983
    · exact rank222 13899
    · exact rank242 22261
    · exact rank310 45124
    · exact rank368 91474
    · exact rank340 91474
    · exact rank327 57109
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1009⟩
    · exact ⟨_, cover1010⟩
    · exact ⟨_, cover1011⟩
    · exact ⟨_, cover1012⟩
    · exact ⟨_, cover1013⟩
    · exact ⟨_, cover1014⟩
    · exact ⟨_, cover1015⟩
    · exact ⟨_, cover1016⟩
    · exact ⟨_, cover1019⟩
    · exact ⟨_, cover1018⟩
    · exact ⟨_, cover1017⟩

def price : EarlyPrice := ⟨3, 32, 10, 70/100, 70/100, ![1139525646328, 183723542614, 31741383856, 1983854964], 1185478275267412⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![3817/37, 1185, 322475/73, 1463584/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons28
end Z6969Source1523

end Merged_Z6969Pack0704

-- merged module Z6969Pack0705
section Merged_Z6969Pack0705

-- Source: Research6969.PrefixNearSavedCubicSingletons28
section Z6969Source1524
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons28
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4369,103,1185,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons28.plan Lower6960.Prefix6969RescueData.CubicSingletons28.plan Lower6960.Prefix6969RescueData.CubicSingletons28.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 32 32 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons28.plan, Lower6960.Prefix6969MainCases.CubicSingletons28.price, Lower6960.Prefix6969MainCases.CubicSingletons28.valid, Lower6960.Prefix6969MainCases.CubicSingletons28.priced, Lower6960.Prefix6969MainCases.CubicSingletons28.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons28.plan, Lower6960.Prefix6969RescueData.CubicSingletons28.price, Lower6960.Prefix6969RescueData.CubicSingletons28.sources, Lower6960.Prefix6969RescueData.CubicSingletons28.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 206615029002571050 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons28
end Z6969Source1524

-- Source: Research6969.PrefixMainDataCubicSingletons29
section Z6969Source1525
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons29
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 20, 17, 21, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank58 2557, bank81 5502, bank82 2965, bank75 5459, bank99 3235, bank127 3592, bank144 4704, bank126 26574, bank161 6246, bank212 10770, bank183 54742, bank174 148759, bank169 292467] i
  head := src1418
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15089, 161731, 748531, 3615157],
    ![25417/2, 116526, 529133, 2411809],
    ![54680/9, 169330/3, 529133, 4650893/2],
    ![29433/8, 273663/8, 275396, 10039156/9],
    ![16211/9, 159506/9, 1452963/8, 6125633/8],
    ![24292/27, 88624/9, 201325/2, 8934121/16],
    ![73478/121, 1068788/121, 4830486/49, 8934121/16],
    ![73478/121, 1068788/121, 842249/9, 1540081/4],
    ![73478/121, 817030/121, 3678148/49, 13966334/49],
    ![235552/441, 2876408/441, 1053633/16, 13966334/49],
    ![235552/441, 2876408/441, 1053633/16, 13966334/49],
    ![3719/7, 136499/21, 2058043/32, 13966334/49],
    ![3719/7, 136499/21, 2058043/32, 8834785/36],
    ![3719/7, 658258/121, 2866714/49, 9809752/49],
    ![3719/7, 806759/150, 6256320/121, 22127616/121],
    ![1355575/3362, 806759/150, 6256320/121, 22127616/121],
    ![1355575/3362, 8114376/1681, 4560253/98, 8528913/49],
    ![1355575/3362, 11894729/2738, 6865875/169, 12888100/81],
    ![954471/2738, 11894729/2738, 6865875/169, 12888100/81],
    ![462882/1369, 11894729/2738, 6865875/169, 12888100/81],
    ![459151/1369, 11894729/2738, 6865875/169, 12888100/81]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 33 385979 := by
  refine ⟨?_, rank154 5462, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1418⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free58_0
    · exact free81_0
    · exact free82_0
    · exact free75_0
    · exact free99_0
    · exact free127_0
    · exact free144_0
    · exact free126_0
    · exact free161_0
    · exact free212_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [307028450, 305521052, 305348989, 305899360, 304640487, 306295994, 308929757, 308309384, 154553315, 155235980, 154986133, 155349518, 155188396, 107939685, 66625567, 77178426, 91132091, 91004130, 118510061, 165540474, 228863086], [1154622, 1162336, 1163216, 1160400, 1166841, 1158370, 1144894, 1148068, 2491722, 2480370, 2484525, 2478482, 2481161, 3650346, 6031670, 5181899, 4359203, 4365658, 3305884, 2309006, 1622339],
  ![121485103310520, 1612566328844, 205976777400, 5193987050], 166195218527025706⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,4,7,7,7,7,7,10,16,14,12,12,9,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 11894729/2738, 6865875/169, 12888100/81] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons29
end Z6969Source1525

-- Source: Research6969.PrefixRescueDataCubicSingletons29
section Z6969Source1526
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons29
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,33⟩
  bank i := ![bank155 6096, bank156 6858, bank193 6858, bank193 7715, bank193 8679, bank204 9763, bank222 12355, bank242 19788, bank311 40111, bank353 115771, bank377 115771] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 65, 145, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 33

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank155 6096
    · exact rank156 6858
    · exact rank193 6858
    · exact rank193 7715
    · exact rank193 8679
    · exact rank204 9763
    · exact rank222 12355
    · exact rank242 19788
    · exact rank311 40111
    · exact rank353 115771
    · exact rank377 115771
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1020⟩
    · exact ⟨_, cover1021⟩
    · exact ⟨_, cover1022⟩
    · exact ⟨_, cover1023⟩
    · exact ⟨_, cover1024⟩
    · exact ⟨_, cover1025⟩
    · exact ⟨_, cover1026⟩
    · exact ⟨_, cover1027⟩
    · exact ⟨_, cover1030⟩
    · exact ⟨_, cover1031⟩
    · exact ⟨_, cover1032⟩

def price : EarlyPrice := ⟨3, 33, 10, 70/100, 70/100, ![1487271253715, 229910205403, 39439261550, 2390280510], 1304166355177095⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![13861/146, 217081/191, 807663/191, 3820443/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons29
end Z6969Source1526

-- Source: Research6969.PrefixNearSavedCubicSingletons29
section Z6969Source1527
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons29
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4344,94,1136,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons29.plan Lower6960.Prefix6969RescueData.CubicSingletons29.plan Lower6960.Prefix6969RescueData.CubicSingletons29.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 33 33 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons29.plan, Lower6960.Prefix6969MainCases.CubicSingletons29.price, Lower6960.Prefix6969MainCases.CubicSingletons29.valid, Lower6960.Prefix6969MainCases.CubicSingletons29.priced, Lower6960.Prefix6969MainCases.CubicSingletons29.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons29.plan, Lower6960.Prefix6969RescueData.CubicSingletons29.price, Lower6960.Prefix6969RescueData.CubicSingletons29.sources, Lower6960.Prefix6969RescueData.CubicSingletons29.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 205353984016239205 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons29
end Z6969Source1527

-- Source: Research6969.PrefixMainDataCubicSingletons3
section Z6969Source1528
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons3
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank84 5564, bank85 2903, bank74 6544, bank113 3716, bank144 4704, bank150 6517, bank120 36262, bank198 9780, bank210 11036, bank183 54742, bank174 148759, bank169 292467] i
  head := src1392
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 169536, 788860, 4130948],
    ![12303, 137438, 621313, 3086412],
    ![53398/9, 595678/9, 619520, 3086412],
    ![29433/8, 319673/8, 2893724/9, 4657492/3],
    ![16211/9, 184651/9, 1683013/8, 8525643/8],
    ![24292/27, 911036/81, 2069795/18, 3787063/6],
    ![73478/121, 9788, 5346226/49, 3787063/6],
    ![73478/121, 9788, 5346226/49, 1572347/3],
    ![73478/121, 970862/121, 4352422/49, 2754096/7],
    ![63754/121, 3214508/441, 543881/8, 2754096/7],
    ![63754/121, 3214508/441, 543881/8, 44137212/121],
    ![61324/121, 3214508/441, 543881/8, 44137212/121],
    ![61324/121, 777044/121, 13430728/225, 18832688/75],
    ![61324/121, 777044/121, 59094, 26819856/121],
    ![61324/121, 9570512/1681, 43082536/841, 26819856/121],
    ![667406/1681, 9570512/1681, 43082536/841, 26819856/121],
    ![667406/1681, 2334856/441, 1166868/25, 10627600/49],
    ![667406/1681, 7008190/1369, 126156044/2809, 587269704/2809],
    ![954471/2738, 7008190/1369, 126156044/2809, 587269704/2809],
    ![462882/1369, 7008190/1369, 126156044/2809, 587269704/2809],
    ![459151/1369, 7008190/1369, 126156044/2809, 587269704/2809]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 7 385979 := by
  refine ⟨?_, rank154 7602, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1392⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free61_0
    · exact free84_0
    · exact free85_0
    · exact free74_2
    · exact free113_0
    · exact free144_0
    · exact free150_0
    · exact free120_0
    · exact free198_0
    · exact free210_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [346760768, 344984529, 346203362, 344815872, 345166996, 344260515, 345165402, 346509342, 170172458, 170501411, 170626914, 170566878, 115552091, 74211083, 66922384, 90925957, 104957189, 105015799, 126874474, 173904886, 235264231], [996359, 1001228, 997887, 1001690, 1000728, 1003213, 1000732, 997048, 2231977, 2226712, 2225198, 2225922, 3388590, 5392613, 6004766, 4369600, 3753904, 3751869, 3072013, 2185661, 1569699],
  ![124882959099420, 1605651694064, 211737807900, 4466160440], 190899312101710277⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,6,6,6,9,15,16,12,10,10,9,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 7008190/1369, 126156044/2809, 587269704/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons3
end Z6969Source1528

-- Source: Research6969.PrefixRescueDataCubicSingletons3
section Z6969Source1529
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons3
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 9
  positive := by decide
  primeShape := ⟨0,3,1,7⟩
  bank i := ![bank221 50764, bank227 57109, bank227 72277, bank245 102908, bank269 130242, bank303 164837, bank299 422931, bank358 375939, bank382 602179] i
  reserve i := ![0, 2, 4, 10, 16, 25, 40, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 7

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 50764
    · exact rank227 57109
    · exact rank227 72277
    · exact rank245 102908
    · exact rank269 130242
    · exact rank303 164837
    · exact rank299 422931
    · exact rank358 375939
    · exact rank382 602179
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover698⟩
    · exact ⟨_, cover699⟩
    · exact ⟨_, cover700⟩
    · exact ⟨_, cover701⟩
    · exact ⟨_, cover702⟩
    · exact ⟨_, cover703⟩
    · exact ⟨_, cover704⟩
    · exact ⟨_, cover705⟩
    · exact ⟨_, cover706⟩

def price : EarlyPrice := ⟨3, 7, 8, 95/100, 80/100, ![1640970292666, 498672620069, 8202412540, 2343564930], 9696977543870034⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![6390/41, 623249/111, 634736/37, 4215253/111] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons3
end Z6969Source1529

-- Source: Research6969.PrefixNearSavedCubicSingletons3
section Z6969Source1530
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons3
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,5119,155,5614,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons3.plan Lower6960.Prefix6969RescueData.CubicSingletons3.plan Lower6960.Prefix6969RescueData.CubicSingletons3.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 7 7 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons3.plan, Lower6960.Prefix6969MainCases.CubicSingletons3.price, Lower6960.Prefix6969MainCases.CubicSingletons3.valid, Lower6960.Prefix6969MainCases.CubicSingletons3.priced, Lower6960.Prefix6969MainCases.CubicSingletons3.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons3.plan, Lower6960.Prefix6969RescueData.CubicSingletons3.price, Lower6960.Prefix6969RescueData.CubicSingletons3.sources, Lower6960.Prefix6969RescueData.CubicSingletons3.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 222526940682334350 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons3
end Z6969Source1530

-- Source: Research6969.PrefixMainDataCubicSingletons30
section Z6969Source1531
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons30
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 20, 23, 25, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank35 2061, bank44 2409, bank53 2871, bank42 4552, bank61 2536, bank69 4787, bank72 2841, bank95 3103, bank115 3521, bank92 5432, bank140 3997, bank130 22726, bank164 6138, bank212 10770, bank186 46700, bank174 148759, bank169 292467] i
  head := src1419
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15471, 160609, 738157, 3373585],
    ![25417/2, 463625/4, 526319, 2411809],
    ![54680/9, 505310/9, 526319, 9187685/4],
    ![29433/8, 544445/16, 2465566/9, 9916010/9],
    ![5710/3, 155030/9, 1405181/8, 11119095/16],
    ![18775/16, 706255/64, 3192313/25, 2599311/5],
    ![86808/121, 833350/121, 3748592/49, 8242641/25],
    ![73478/121, 833350/121, 3748592/49, 8242641/25],
    ![73478/121, 74015/11, 3657217/49, 13681720/49],
    ![73478/121, 74015/11, 3446640/49, 13681720/49],
    ![73478/121, 74015/11, 3446640/49, 13681720/49],
    ![73478/121, 74015/11, 3446640/49, 9628609/36],
    ![73478/121, 2437990/441, 897855/16, 2713685/14],
    ![73478/121, 2437990/441, 897855/16, 2713685/14],
    ![73478/121, 2437990/441, 897855/16, 2713685/14],
    ![33463/82, 2437990/441, 897855/16, 2713685/14],
    ![33463/82, 8079820/1681, 324147/7, 16557255/98],
    ![33463/82, 23654855/5476, 6865875/169, 12888100/81],
    ![481425/1369, 23654855/5476, 6865875/169, 12888100/81],
    ![462882/1369, 23654855/5476, 6865875/169, 12888100/81],
    ![459151/1369, 23654855/5476, 6865875/169, 12888100/81]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 34 385979 := by
  refine ⟨?_, rank154 5395, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1419⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free35_0
    · exact free44_0
    · exact free53_0
    · exact free42_2
    · exact free61_0
    · exact free69_0
    · exact free72_0
    · exact free95_0
    · exact free115_0
    · exact free92_0
    · exact free140_0
    · exact free130_0
    · exact free164_0
    · exact free212_0
    · exact free186_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [305639353, 304352756, 305081892, 305275379, 305617694, 305533518, 305018361, 304833414, 164085349, 163905416, 163881040, 164100723, 81970807, 54398749, 71911720, 79295524, 91517762, 91580920, 118861721, 165436891, 228782363], [1161730, 1168314, 1164583, 1163593, 1161841, 1162272, 1164908, 1165854, 2333205, 2336197, 2336603, 2332949, 4866025, 7431675, 5575401, 5035654, 4339751, 4336565, 3296052, 2310729, 1623003],
  ![121442253927660, 1612653698992, 205904126700, 5163164860], 164547742414760157⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,4,7,7,7,7,13,20,15,14,12,12,9,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 23654855/5476, 6865875/169, 12888100/81] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons30
end Z6969Source1531

-- Source: Research6969.PhysicalChecks081
section Z6969Source1532
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1033 : Request := ⟨⟨⟨470,655,144,6096⟩,3184589537280,5168862572⟩,0,3,1,385979,34⟩
theorem cover1033 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1033) 2411 2314 [2325, 2365, 2411] := triangleCover (by decide +kernel)
def src1034 : Request := ⟨⟨⟨560,781,172,6096⟩,5388141854720,10440670587⟩,1,3,1,385979,34⟩
theorem cover1034 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1034) 2411 2314 [2327, 2371, 2411] := triangleCover (by decide +kernel)
def src1035 : Request := ⟨⟨⟨690,962,208,6858⟩,9921631092736,23645774460⟩,2,3,1,385979,34⟩
theorem cover1035 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1035) 2411 2314 [2328, 2375, 2411] := triangleCover (by decide +kernel)
def src1036 : Request := ⟨⟨⟨690,962,212,6858⟩,10065769922560,23997864317⟩,3,3,1,385979,34⟩
theorem cover1036 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1036) 2411 2314 [2321, 2345, 2411] := triangleCover (by decide +kernel)
def src1037 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,4,3,1,385979,34⟩
theorem cover1037 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1037) 2411 2314 [2324, 2358, 2411] := triangleCover (by decide +kernel)
def src1038 : Request := ⟨⟨⟨825,1151,253,10983⟩,17161575202816,49010625289⟩,8,3,1,385979,34⟩
theorem cover1038 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1038) 2411 2314 [2322, 2349, 2411] := triangleCover (by decide +kernel)
def src1039 : Request := ⟨⟨⟨1450,2023,457,15636⟩,94890063298560,476245648464⟩,20,3,1,385979,34⟩
theorem cover1039 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1039) 2411 2314 [2317, 2328, 2360, 2411] := triangleCover (by decide +kernel)
def src1040 : Request := ⟨⟨⟨2600,3627,819,25043⟩,546063062138880,4910333421859⟩,40,3,1,385979,34⟩
theorem cover1040 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1040) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src1043 : Request := ⟨⟨⟨5700,7951,1750,64247⟩,5637370734182400,111025751789870⟩,110,3,1,385979,34⟩
theorem cover1043 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1043) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
def src1044 : Request := ⟨⟨⟨6900,9625,2118,91474⟩,9997036108906496,238335796784464⟩,145,3,1,385979,34⟩
theorem cover1044 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1044) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src1045 : Request := ⟨⟨⟨10000,13950,3070,102908⟩,30428373265940480,1051468979452278⟩,190,3,1,385979,34⟩
theorem cover1045 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1045) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src1046 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,0,3,1,385979,35⟩
theorem cover1046 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1046) 2411 2314 [2328, 2377, 2411] := triangleCover (by decide +kernel)
def src1047 : Request := ⟨⟨⟨560,781,176,5419⟩,5482316038144,10627925923⟩,1,3,1,385979,35⟩
theorem cover1047 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1047) 2411 2314 [2320, 2342, 2411] := triangleCover (by decide +kernel)
def src1048 : Request := ⟨⟨⟨560,781,176,6096⟩,5482316038144,10627925923⟩,2,3,1,385979,35⟩
theorem cover1048 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1048) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1049 : Request := ⟨⟨⟨690,962,208,6858⟩,9921631092736,23645774460⟩,3,3,1,385979,35⟩
theorem cover1049 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1049) 2411 2314 [2322, 2349, 2411] := triangleCover (by decide +kernel)
def src1050 : Request := ⟨⟨⟨690,962,217,6858⟩,10244384358400,24434817260⟩,4,3,1,385979,35⟩
theorem cover1050 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1050) 2411 2314 [2320, 2342, 2409, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1532

-- Source: Research6969.PrefixRescueDataCubicSingletons30
section Z6969Source1533
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons30
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,34⟩
  bank i := ![bank142 6096, bank156 6096, bank192 6858, bank193 6858, bank193 7715, bank204 10983, bank238 15636, bank268 25043, bank340 64247, bank377 102908, bank353 91474] i
  reserve i := ![0, 1, 2, 3, 4, 8, 20, 40, 110, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 34

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 6096
    · exact rank156 6096
    · exact rank192 6858
    · exact rank193 6858
    · exact rank193 7715
    · exact rank204 10983
    · exact rank238 15636
    · exact rank268 25043
    · exact rank340 64247
    · exact rank377 102908
    · exact rank353 91474
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1033⟩
    · exact ⟨_, cover1034⟩
    · exact ⟨_, cover1035⟩
    · exact ⟨_, cover1036⟩
    · exact ⟨_, cover1037⟩
    · exact ⟨_, cover1038⟩
    · exact ⟨_, cover1039⟩
    · exact ⟨_, cover1040⟩
    · exact ⟨_, cover1043⟩
    · exact ⟨_, cover1045⟩
    · exact ⟨_, cover1044⟩

def price : EarlyPrice := ⟨3, 34, 10, 65/100, 60/100, ![1362085965864, 224130671484, 40634391060, 2390280510], 1184260224419274⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![13861/146, 207288/191, 783024/191, 3498872/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons30
end Z6969Source1533

-- Source: Research6969.PrefixNearSavedCubicSingletons30
section Z6969Source1534
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons30
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4319,94,1085,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons30.plan Lower6960.Prefix6969RescueData.CubicSingletons30.plan Lower6960.Prefix6969RescueData.CubicSingletons30.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 34 34 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons30.plan, Lower6960.Prefix6969MainCases.CubicSingletons30.price, Lower6960.Prefix6969MainCases.CubicSingletons30.valid, Lower6960.Prefix6969MainCases.CubicSingletons30.priced, Lower6960.Prefix6969MainCases.CubicSingletons30.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons30.plan, Lower6960.Prefix6969RescueData.CubicSingletons30.price, Lower6960.Prefix6969RescueData.CubicSingletons30.sources, Lower6960.Prefix6969RescueData.CubicSingletons30.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 204208574791208299 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons30
end Z6969Source1534

-- Source: Research6969.PrefixMainDataCubicSingletons31
section Z6969Source1535
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons31
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 20, 23, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank35 2061, bank44 2409, bank53 2871, bank42 4552, bank61 2536, bank69 4787, bank72 2841, bank95 3103, bank112 3547, bank138 3813, bank144 4704, bank126 26574, bank164 6138, bank214 10456, bank183 54742, bank174 148759, bank169 292467] i
  head := src1420
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15734, 160067, 736018, 3347104],
    ![25417/2, 461183/4, 523547, 2411809],
    ![54680/9, 502670/9, 523547, 9075287/4],
    ![29433/8, 541607/16, 2452762/9, 9794702/9],
    ![5710/3, 154205/9, 1397723/8, 10983069/16],
    ![18775/16, 702625/64, 3176011/25, 12837561/25],
    ![86808/121, 829126/121, 3729848/49, 8242641/25],
    ![73478/121, 829126/121, 3729848/49, 8242641/25],
    ![73478/121, 73589/11, 3636427/49, 13514344/49],
    ![73478/121, 73589/11, 3446640/49, 13514344/49],
    ![73478/121, 73589/11, 3446640/49, 13514344/49],
    ![73478/121, 73589/11, 3446640/49, 9628609/36],
    ![73478/121, 2410334/441, 897391/16, 12581209/64],
    ![73478/121, 2410334/441, 897391/16, 12581209/64],
    ![73478/121, 1593701/300, 6256320/121, 22127616/121],
    ![1355575/3362, 1593701/300, 6256320/121, 22127616/121],
    ![1355575/3362, 8032036/1681, 2255763/49, 4186116/25],
    ![1355575/3362, 5871082/1369, 105632275/2601, 109327936/729],
    ![954471/2738, 5871082/1369, 105632275/2601, 109327936/729],
    ![462882/1369, 5871082/1369, 105632275/2601, 109327936/729],
    ![459151/1369, 5871082/1369, 105632275/2601, 109327936/729]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 35 385979 := by
  refine ⟨?_, rank154 5329, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1420⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free35_0
    · exact free44_0
    · exact free53_0
    · exact free42_2
    · exact free61_0
    · exact free69_0
    · exact free72_0
    · exact free95_0
    · exact free112_0
    · exact free138_0
    · exact free144_0
    · exact free126_0
    · exact free164_0
    · exact free214_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [305329880, 305130587, 303980832, 303996140, 304332651, 303611047, 304023379, 304833414, 162801398, 162822377, 162678016, 162772102, 81615105, 81625947, 65406030, 78780736, 92893096, 92791505, 118258233, 165288645, 228667226], [1163314, 1164334, 1170217, 1170139, 1168417, 1172109, 1169999, 1165854, 2354557, 2354208, 2356609, 2355044, 4887152, 4886508, 6144043, 5071215, 4270382, 4275506, 3312925, 2313194, 1623950],
  ![121381136905320, 1612778275624, 205800503400, 5086729970], 164027947972462443⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,4,7,7,7,7,13,13,17,14,12,12,9,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5871082/1369, 105632275/2601, 109327936/729] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons31
end Z6969Source1535

end Merged_Z6969Pack0705

-- merged module Z6969Pack0706
section Merged_Z6969Pack0706

-- Source: Research6969.PhysicalChecks082
section Z6969Source1536
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1051 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,8,3,1,385979,35⟩
theorem cover1051 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1051) 2411 2314 [2325, 2362, 2411] := triangleCover (by decide +kernel)
def src1052 : Request := ⟨⟨⟨1200,1674,368,13899⟩,52718727069696,218807905514⟩,16,3,1,385979,35⟩
theorem cover1052 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1052) 2411 2314 [2327, 2368, 2411] := triangleCover (by decide +kernel)
def src1053 : Request := ⟨⟨⟨2100,2929,662,19788⟩,288013660979200,2090961110089⟩,32,3,1,385979,35⟩
theorem cover1053 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1053) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src1056 : Request := ⟨⟨⟨3200,4464,1008,40111⟩,1017717693874176,11262426748352⟩,65,3,1,385979,35⟩
theorem cover1056 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1056) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src1057 : Request := ⟨⟨⟨6900,9625,2118,81311⟩,9997036108906496,238335796784464⟩,145,3,1,385979,35⟩
theorem cover1057 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1057) 2411 2314 [2321, 2343, 2404, 2411] := triangleCover (by decide +kernel)
def src1058 : Request := ⟨⟨⟨8300,11577,2615,115771⟩,17745461310914560,509018341309343⟩,190,3,1,385979,35⟩
theorem cover1058 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1058) 2411 2314 [2315, 2321, 2337, 2381, 2411] := triangleCover (by decide +kernel)
def src1059 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,0,3,1,385979,36⟩
theorem cover1059 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1059) 2411 2314 [2321, 2347, 2411] := triangleCover (by decide +kernel)
def src1060 : Request := ⟨⟨⟨560,781,172,5419⟩,5388141854720,10440670587⟩,1,3,1,385979,36⟩
theorem cover1060 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1060) 2411 2314 [2335, 2405, 2411] := triangleCover (by decide +kernel)
def src1061 : Request := ⟨⟨⟨560,781,172,6096⟩,5388141854720,10440670587⟩,2,3,1,385979,36⟩
theorem cover1061 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1061) 2411 2314 [2335, 2405, 2411] := triangleCover (by decide +kernel)
def src1062 : Request := ⟨⟨⟨560,781,172,6858⟩,5388141854720,10440670587⟩,3,3,1,385979,36⟩
theorem cover1062 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1062) 2411 2314 [2323, 2354, 2411] := triangleCover (by decide +kernel)
def src1063 : Request := ⟨⟨⟨690,962,212,8679⟩,10065769922560,23997864317⟩,6,3,1,385979,36⟩
theorem cover1063 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1063) 2411 2314 [2330, 2382, 2411] := triangleCover (by decide +kernel)
def src1064 : Request := ⟨⟨⟨825,1151,253,8679⟩,17161575202816,49010625289⟩,8,3,1,385979,36⟩
theorem cover1064 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1064) 2411 2314 [2321, 2345, 2411] := triangleCover (by decide +kernel)
def src1065 : Request := ⟨⟨⟨1200,1674,368,12355⟩,52718727069696,218807905514⟩,16,3,1,385979,36⟩
theorem cover1065 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1065) 2411 2314 [2321, 2344, 2411] := triangleCover (by decide +kernel)
def src1066 : Request := ⟨⟨⟨2100,2929,645,25043⟩,282396798484480,2049139102608⟩,40,3,1,385979,36⟩
theorem cover1066 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1066) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src1069 : Request := ⟨⟨⟨4800,6695,1474,72277⟩,3367547627110400,55837558620681⟩,110,3,1,385979,36⟩
theorem cover1069 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1069) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src1070 : Request := ⟨⟨⟨6900,9625,2118,72277⟩,9997036108906496,238335796784464⟩,145,3,1,385979,36⟩
theorem cover1070 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1070) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1536

-- Source: Research6969.PrefixRescueDataCubicSingletons31
section Z6969Source1537
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons31
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,35⟩
  bank i := ![bank142 5419, bank157 5419, bank157 6096, bank192 6858, bank194 6858, bank204 9763, bank228 13899, bank250 19788, bank301 40111, bank353 81311, bank366 115771] i
  reserve i := ![0, 1, 2, 3, 4, 8, 16, 32, 65, 145, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 35

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 5419
    · exact rank157 5419
    · exact rank157 6096
    · exact rank192 6858
    · exact rank194 6858
    · exact rank204 9763
    · exact rank228 13899
    · exact rank250 19788
    · exact rank301 40111
    · exact rank353 81311
    · exact rank366 115771
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1046⟩
    · exact ⟨_, cover1047⟩
    · exact ⟨_, cover1048⟩
    · exact ⟨_, cover1049⟩
    · exact ⟨_, cover1050⟩
    · exact ⟨_, cover1051⟩
    · exact ⟨_, cover1052⟩
    · exact ⟨_, cover1053⟩
    · exact ⟨_, cover1056⟩
    · exact ⟨_, cover1057⟩
    · exact ⟨_, cover1058⟩

def price : EarlyPrice := ⟨3, 35, 10, 65/100, 60/100, ![1577408817750, 212247980703, 35630028750, 2036020695], 1093144374095503⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![16807/191, 155441/146, 752508/191, 2845885/146] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons31
end Z6969Source1537

-- Source: Research6969.PrefixNearSavedCubicSingletons31
section Z6969Source1538
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons31
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4288,87,1064,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons31.plan Lower6960.Prefix6969RescueData.CubicSingletons31.plan Lower6960.Prefix6969RescueData.CubicSingletons31.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 35 35 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons31.plan, Lower6960.Prefix6969MainCases.CubicSingletons31.price, Lower6960.Prefix6969MainCases.CubicSingletons31.valid, Lower6960.Prefix6969MainCases.CubicSingletons31.priced, Lower6960.Prefix6969MainCases.CubicSingletons31.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons31.plan, Lower6960.Prefix6969RescueData.CubicSingletons31.price, Lower6960.Prefix6969RescueData.CubicSingletons31.sources, Lower6960.Prefix6969RescueData.CubicSingletons31.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 203501355649835839 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons31
end Z6969Source1538

-- Source: Research6969.PrefixMainDataCubicSingletons32
section Z6969Source1539
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons32
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 14, 20, 21, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank37 2039, bank44 2409, bank54 2755, bank65 3612, bank88 2848, bank87 4698, bank127 3592, bank130 22726, bank166 6058, bank199 9241, bank181 61748, bank214 10456, bank170 227095] i
  head := src1421
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15875, 159232, 733726, 3240780],
    ![25417/2, 458815/4, 521808, 2411809],
    ![54680/9, 500110/9, 521808, 8966295/4],
    ![29433/8, 538855/16, 2440346/9, 1075230],
    ![64334/25, 114941/5, 204050, 3705625/4],
    ![17323/9, 615145/36, 2769263/16, 10735335/16],
    ![18775/16, 699105/64, 3160203/25, 2536677/5],
    ![89110/121, 810575/121, 3674770/49, 303601],
    ![89110/121, 810575/121, 3674770/49, 303601],
    ![89110/121, 810575/121, 3674770/49, 1499472/5],
    ![27452/49, 288522/49, 467451/8, 3805380/13],
    ![27452/49, 646241/121, 2813327/49, 9455940/49],
    ![33463/82, 646241/121, 2813327/49, 9455940/49],
    ![33463/82, 8015540/1681, 4491773/98, 36699364/225],
    ![33463/82, 5827090/1323, 3581151/88, 291923190/1849],
    ![474397/1369, 5827090/1323, 3581151/88, 291923190/1849],
    ![474397/1369, 5837930/1369, 105042259/2601, 109327936/729],
    ![920087/2738, 5837930/1369, 105042259/2601, 109327936/729]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 36 385979 := by
  refine ⟨?_, rank154 5265, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1421⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free65_0
    · exact free88_0
    · exact free87_1
    · exact free127_0
    · exact free130_0
    · exact free166_0
    · exact free199_0
    · exact free181_0
    · exact free214_0
    · exact free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [304172959, 303976140, 303857172, 302531021, 303138924, 303940900, 302715267, 162056251, 162133770, 161874340, 161614392, 75075630, 75510088, 78840451, 92185745, 91758567, 144723433, 228729603], [1169234, 1170241, 1170850, 1177635, 1174525, 1170421, 1176693, 2366949, 2365660, 2369974, 2374297, 5327157, 5297145, 5067090, 4306059, 4327605, 2666968, 1623437],
  ![121414247864460, 1612710811032, 205856642700, 5167292460], 163160094036535759⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,7,7,7,7,14,14,14,12,12,8,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 5837930/1369, 105042259/2601, 109327936/729] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons32
end Z6969Source1539

-- Source: Research6969.PrefixRescueDataCubicSingletons32
section Z6969Source1540
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons32
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,3,1,36⟩
  bank i := ![bank142 4817, bank156 5419, bank156 6096, bank156 6858, bank193 8679, bank204 8679, bank228 12355, bank249 25043, bank324 72277, bank353 72277] i
  reserve i := ![0, 1, 2, 3, 6, 8, 16, 40, 110, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 36

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 4817
    · exact rank156 5419
    · exact rank156 6096
    · exact rank156 6858
    · exact rank193 8679
    · exact rank204 8679
    · exact rank228 12355
    · exact rank249 25043
    · exact rank324 72277
    · exact rank353 72277
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1059⟩
    · exact ⟨_, cover1060⟩
    · exact ⟨_, cover1061⟩
    · exact ⟨_, cover1062⟩
    · exact ⟨_, cover1063⟩
    · exact ⟨_, cover1064⟩
    · exact ⟨_, cover1065⟩
    · exact ⟨_, cover1066⟩
    · exact ⟨_, cover1069⟩
    · exact ⟨_, cover1070⟩

def price : EarlyPrice := ⟨3, 36, 9, 65/100, 70/100, ![1012929124411, 161481540562, 29682802074, 1649059974], 921125093397434⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![9643/111, 148525/146, 563331/146, 1300986/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons32
end Z6969Source1540

-- Source: Research6969.PrefixNearSavedCubicSingletons32
section Z6969Source1541
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons32
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨336,4264,86,1017,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons32.plan Lower6960.Prefix6969RescueData.CubicSingletons32.plan Lower6960.Prefix6969RescueData.CubicSingletons32.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 36 36 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons32.plan, Lower6960.Prefix6969MainCases.CubicSingletons32.price, Lower6960.Prefix6969MainCases.CubicSingletons32.valid, Lower6960.Prefix6969MainCases.CubicSingletons32.priced, Lower6960.Prefix6969MainCases.CubicSingletons32.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons32.plan, Lower6960.Prefix6969RescueData.CubicSingletons32.price, Lower6960.Prefix6969RescueData.CubicSingletons32.sources, Lower6960.Prefix6969RescueData.CubicSingletons32.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 202932381943208355 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons32
end Z6969Source1541

-- Source: Research6969.PrefixMainDataCubicSingletons33
section Z6969Source1542
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons33
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 14, 20, 21, 30, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank37 2039, bank44 2409, bank54 2755, bank65 3612, bank88 2848, bank87 4698, bank127 3592, bank94 16634, bank165 6130, bank190 37026, bank214 10456, bank176 98699, bank169 292467] i
  head := src1422
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![15875, 158980, 732592, 3230511],
    ![25417/2, 114121, 521808, 2411809],
    ![54680/9, 497590/9, 521808, 4429503/2],
    ![29433/8, 268073/8, 2428124/9, 1062364],
    ![64334/25, 571744/25, 204050, 3705625/4],
    ![17323/9, 152983/9, 1377481/8, 5303439/8],
    ![18775/16, 86955/8, 3144642/25, 12531618/25],
    ![89110/121, 806480/121, 3656248/49, 303601],
    ![89110/121, 806480/121, 3656248/49, 303601],
    ![89110/121, 806480/121, 3656248/49, 7407648/25],
    ![27452/49, 287262/49, 467451/8, 48877992/169],
    ![27452/49, 642398/121, 2796254/49, 9342792/49],
    ![22029/50, 642398/121, 2796254/49, 9342792/49],
    ![22029/50, 7955456/1681, 2228692/49, 1503076/9],
    ![489643/1369, 7955456/1681, 2228692/49, 1503076/9],
    ![489643/1369, 5805296/1369, 104461462/2601, 109327936/729],
    ![466774/1369, 5805296/1369, 104461462/2601, 109327936/729],
    ![459151/1369, 5805296/1369, 104461462/2601, 109327936/729]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 37 385979 := by
  refine ⟨?_, rank154 5202, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1422⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free65_0
    · exact free88_0
    · exact free87_1
    · exact free127_0
    · exact free94_0
    · exact free165_0
    · exact free190_0
    · exact free214_0
    · exact free176_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [302828350, 302486800, 300750102, 300679872, 302436629, 300771346, 301650577, 162885923, 162947141, 162938890, 162879889, 98121618, 81911160, 90381357, 90896204, 100963602, 165381949, 228104291], [1176114, 1177862, 1186748, 1187108, 1178118, 1186640, 1182141, 2353152, 2352133, 2352271, 2353252, 4034819, 4869568, 4397069, 4371101, 3914846, 2311643, 1628579],
  ![121082319748620, 1613386232044, 205293861900, 5231359000], 162353048970814338⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,7,7,7,7,11,13,12,12,11,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5805296/1369, 104461462/2601, 109327936/729] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons33
end Z6969Source1542

-- Source: Research6969.PhysicalChecks083
section Z6969Source1543
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1071 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,0,3,1,385979,37⟩
theorem cover1071 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1071) 2411 2314 [2342, 2411] := triangleCover (by decide +kernel)
def src1072 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,1,3,1,385979,37⟩
theorem cover1072 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1072) 2411 2314 [2328, 2377, 2411] := triangleCover (by decide +kernel)
def src1073 : Request := ⟨⟨⟨560,781,172,5419⟩,5388141854720,10440670587⟩,2,3,1,385979,37⟩
theorem cover1073 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1073) 2411 2314 [2322, 2350, 2411] := triangleCover (by decide +kernel)
def src1074 : Request := ⟨⟨⟨560,781,172,6096⟩,5388141854720,10440670587⟩,3,3,1,385979,37⟩
theorem cover1074 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1074) 2411 2314 [2321, 2347, 2411] := triangleCover (by decide +kernel)
def src1075 : Request := ⟨⟨⟨560,781,172,7715⟩,5388141854720,10440670587⟩,4,3,1,385979,37⟩
theorem cover1075 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1075) 2411 2314 [2321, 2346, 2411] := triangleCover (by decide +kernel)
def src1076 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,6,3,1,385979,37⟩
theorem cover1076 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1076) 2411 2314 [2331, 2386, 2411] := triangleCover (by decide +kernel)
def src1077 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,10,3,1,385979,37⟩
theorem cover1077 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1077) 2411 2314 [2320, 2341, 2404, 2411] := triangleCover (by decide +kernel)
def src1078 : Request := ⟨⟨⟨1450,2022,457,15636⟩,94890063298560,475487789910⟩,25,3,1,385979,37⟩
theorem cover1078 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1078) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src1081 : Request := ⟨⟨⟨3950,5510,1213,45124⟩,1877062482395136,25622281045803⟩,85,3,1,385979,37⟩
theorem cover1081 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1081) 2411 2314 [2325, 2358, 2411] := triangleCover (by decide +kernel)
def src1082 : Request := ⟨⟨⟨8300,11577,2548,91474⟩,17399709518790656,498847383098023⟩,190,3,1,385979,37⟩
theorem cover1082 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1082) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src1083 : Request := ⟨⟨⟨10000,13948,3070,130242⟩,30428373265940480,1050983571587703⟩,245,3,1,385979,37⟩
theorem cover1083 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1083) 2411 2314 [2318, 2332, 2370, 2411] := triangleCover (by decide +kernel)
def src1084 : Request := ⟨⟨⟨400,558,123,4817⟩,1971918995456,2734096379⟩,0,3,1,385979,38⟩
theorem cover1084 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1084) 2411 2314 [2321, 2348, 2411] := triangleCover (by decide +kernel)
def src1085 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,1,3,1,385979,38⟩
theorem cover1085 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1085) 2411 2314 [2320, 2343, 2411] := triangleCover (by decide +kernel)
def src1086 : Request := ⟨⟨⟨560,781,169,6096⟩,5316921262080,10299257375⟩,3,3,1,385979,38⟩
theorem cover1086 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1086) 2411 2314 [2323, 2355, 2411] := triangleCover (by decide +kernel)
def src1087 : Request := ⟨⟨⟨560,781,172,6858⟩,5388141854720,10440670587⟩,4,3,1,385979,38⟩
theorem cover1087 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1087) 2411 2314 [2328, 2375, 2411] := triangleCover (by decide +kernel)
def src1088 : Request := ⟨⟨⟨690,962,212,6858⟩,10065769922560,23997864317⟩,6,3,1,385979,38⟩
theorem cover1088 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1088) 2411 2314 [2320, 2342, 2410, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1543

-- Source: Research6969.PrefixRescueDataCubicSingletons33
section Z6969Source1544
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons33
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,37⟩
  bank i := ![bank142 4817, bank142 5419, bank156 5419, bank156 6096, bank156 7715, bank193 7715, bank204 9763, bank234 15636, bank310 45124, bank365 91474, bank375 130242] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 85, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 37

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 4817
    · exact rank142 5419
    · exact rank156 5419
    · exact rank156 6096
    · exact rank156 7715
    · exact rank193 7715
    · exact rank204 9763
    · exact rank234 15636
    · exact rank310 45124
    · exact rank365 91474
    · exact rank375 130242
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1071⟩
    · exact ⟨_, cover1072⟩
    · exact ⟨_, cover1073⟩
    · exact ⟨_, cover1074⟩
    · exact ⟨_, cover1075⟩
    · exact ⟨_, cover1076⟩
    · exact ⟨_, cover1077⟩
    · exact ⟨_, cover1078⟩
    · exact ⟨_, cover1081⟩
    · exact ⟨_, cover1082⟩
    · exact ⟨_, cover1083⟩

def price : EarlyPrice := ⟨3, 37, 10, 65/100, 70/100, ![1875984408312, 258090437514, 44219776520, 2390280510], 1148792187895206⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![3348/41, 185750/191, 702771/191, 3384538/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons33
end Z6969Source1544

-- Source: Research6969.PrefixNearSavedCubicSingletons33
section Z6969Source1545
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons33
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4240,81,972,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons33.plan Lower6960.Prefix6969RescueData.CubicSingletons33.plan Lower6960.Prefix6969RescueData.CubicSingletons33.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 37 37 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons33.plan, Lower6960.Prefix6969MainCases.CubicSingletons33.price, Lower6960.Prefix6969MainCases.CubicSingletons33.valid, Lower6960.Prefix6969MainCases.CubicSingletons33.priced, Lower6960.Prefix6969MainCases.CubicSingletons33.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons33.plan, Lower6960.Prefix6969RescueData.CubicSingletons33.price, Lower6960.Prefix6969RescueData.CubicSingletons33.sources, Lower6960.Prefix6969RescueData.CubicSingletons33.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 201722567590510920 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons33
end Z6969Source1545

-- Source: Research6969.PrefixMainDataCubicSingletons34
section Z6969Source1546
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons34
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 14, 13, 18, 17, 21, 20, 25, 41, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank37 2039, bank44 2409, bank54 2755, bank64 3514, bank72 2841, bank76 4276, bank97 3273, bank116 3644, bank86 4712, bank140 3997, bank166 6058, bank191 35220, bank214 10456, bank174 148759] i
  head := src1423
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15869, 158001, 727626, 3206793],
    ![25417/2, 227095/2, 521808, 2411809],
    ![54680/9, 495110/9, 521808, 2188355],
    ![29433/8, 66685/2, 2416096/9, 9447320/9],
    ![64334/25, 113766/5, 204050, 3705625/4],
    ![17323/9, 304385/18, 342611/2, 2620115/4],
    ![18775/16, 346115/32, 3129328/25, 2476452/5],
    ![89110/121, 72950/11, 3638020/49, 303601],
    ![89110/121, 72950/11, 3638020/49, 303601],
    ![89110/121, 72950/11, 3638020/49, 303601],
    ![230520/361, 2327640/361, 3224104/49, 303601],
    ![230520/361, 2327640/361, 3224104/49, 1401935/6],
    ![230520/361, 636686/121, 2753264/49, 9365080/49],
    ![246184/441, 636686/121, 2753264/49, 9365080/49],
    ![246184/441, 636686/121, 2753264/49, 9365080/49],
    ![246184/441, 7923040/1681, 2220324/49, 36699364/225],
    ![491589/1369, 7923040/1681, 2220324/49, 36699364/225],
    ![491589/1369, 5773180/1369, 103889884/2601, 109327936/729],
    ![462882/1369, 5773180/1369, 103889884/2601, 109327936/729]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 38 385979 := by
  refine ⟨?_, rank154 5140, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1423⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free64_0
    · exact free72_0
    · exact free76_0
    · exact free97_0
    · exact free116_1
    · exact free86_1
    · exact free140_0
    · exact free166_0
    · exact free191_0
    · exact free214_0
    · exact free174_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [300379682, 300201069, 299878460, 300022359, 299959754, 299907905, 299739632, 150219189, 150146358, 150169921, 150448250, 150344926, 48388627, 62568867, 81353410, 93869446, 94190277, 118719391, 229276141], [1188644, 1189558, 1191208, 1190472, 1190792, 1191058, 1191919, 2563799, 2565010, 2564618, 2559989, 2561708, 8377976, 6434911, 4902694, 4221136, 4204954, 3300031, 1618942],
  ![121704361165620, 1612120136744, 206348526900, 5022045140], 161417415169783171⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,7,7,7,7,7,22,17,13,12,12,9,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![462882/1369, 5773180/1369, 103889884/2601, 109327936/729] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons34
end Z6969Source1546

-- Source: Research6969.PhysicalChecks084
section Z6969Source1547
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1089 : Request := ⟨⟨⟨825,1151,260,8679⟩,17518948515840,50057971890⟩,10,3,1,385979,38⟩
theorem cover1089 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1089) 2411 2314 [2322, 2349, 2411] := triangleCover (by decide +kernel)
def src1090 : Request := ⟨⟨⟨1000,1395,315,12355⟩,31157463285760,107844841957⟩,16,3,1,385979,38⟩
theorem cover1090 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1090) 2411 2314 [2319, 2336, 2387, 2411] := triangleCover (by decide +kernel)
def src1091 : Request := ⟨⟨⟨1750,2441,551,17590⟩,166595992223744,1008217465165⟩,32,3,1,385979,38⟩
theorem cover1091 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1091) 2411 2314 [2321, 2344, 2409, 2411] := triangleCover (by decide +kernel)
def src1094 : Request := ⟨⟨⟨3950,5510,1213,40111⟩,1877062482395136,25622281045803⟩,85,3,1,385979,38⟩
theorem cover1094 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1094) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src1095 : Request := ⟨⟨⟨5700,7950,1796,91474⟩,5749327563587584,113242283843565⟩,145,3,1,385979,38⟩
theorem cover1095 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1095) 2411 2314 [2315, 2321, 2337, 2381, 2411] := triangleCover (by decide +kernel)
def src1096 : Request := ⟨⟨⟨8300,11577,2615,81311⟩,17745461310914560,509018341309343⟩,190,3,1,385979,38⟩
theorem cover1096 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1096) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src1097 : Request := ⟨⟨⟨400,558,126,4282⟩,2007957766144,2785382344⟩,0,3,1,385979,39⟩
theorem cover1097 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1097) 2411 2314 [2320, 2343, 2411] := triangleCover (by decide +kernel)
def src1098 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,1,3,1,385979,39⟩
theorem cover1098 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1098) 2411 2314 [2340, 2411] := triangleCover (by decide +kernel)
def src1099 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,2,3,1,385979,39⟩
theorem cover1099 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1099) 2411 2314 [2326, 2369, 2411] := triangleCover (by decide +kernel)
def src1100 : Request := ⟨⟨⟨560,781,172,5419⟩,5388141854720,10440670587⟩,3,3,1,385979,39⟩
theorem cover1100 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1100) 2411 2314 [2326, 2368, 2411] := triangleCover (by decide +kernel)
def src1101 : Request := ⟨⟨⟨560,781,172,6096⟩,5388141854720,10440670587⟩,4,3,1,385979,39⟩
theorem cover1101 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1101) 2411 2314 [2326, 2367, 2411] := triangleCover (by decide +kernel)
def src1102 : Request := ⟨⟨⟨690,962,217,7715⟩,10244384358400,24434817260⟩,8,3,1,385979,39⟩
theorem cover1102 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1102) 2411 2314 [2320, 2341, 2406, 2411] := triangleCover (by decide +kernel)
def src1103 : Request := ⟨⟨⟨1450,2022,457,13899⟩,94890063298560,475487789910⟩,25,3,1,385979,39⟩
theorem cover1103 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1103) 2411 2314 [2322, 2348, 2411] := triangleCover (by decide +kernel)
def src1106 : Request := ⟨⟨⟨4800,6695,1474,50764⟩,3367547627110400,55837558620681⟩,110,3,1,385979,39⟩
theorem cover1106 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1106) 2411 2314 [2329, 2373, 2411] := triangleCover (by decide +kernel)
def src1107 : Request := ⟨⟨⟨5700,7950,1750,72277⟩,5637370734182400,110980791054694⟩,145,3,1,385979,39⟩
theorem cover1107 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1107) 2411 2314 [2320, 2339, 2392, 2411] := triangleCover (by decide +kernel)
def src1108 : Request := ⟨⟨⟨8300,11577,2548,81311⟩,17399709518790656,498847383098023⟩,190,3,1,385979,39⟩
theorem cover1108 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1108) 2411 2314 [2324, 2354, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1547

end Merged_Z6969Pack0706

-- merged module Z6969Pack0707
section Merged_Z6969Pack0707

-- Source: Research6969.PrefixRescueDataCubicSingletons34
section Z6969Source1548
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons34
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,38⟩
  bank i := ![bank134 4817, bank142 4817, bank155 6096, bank156 6858, bank193 6858, bank205 8679, bank223 12355, bank243 17590, bank310 40111, bank339 91474, bank366 81311] i
  reserve i := ![0, 1, 3, 4, 6, 10, 16, 32, 85, 145, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 38

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank134 4817
    · exact rank142 4817
    · exact rank155 6096
    · exact rank156 6858
    · exact rank193 6858
    · exact rank205 8679
    · exact rank223 12355
    · exact rank243 17590
    · exact rank310 40111
    · exact rank339 91474
    · exact rank366 81311
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1084⟩
    · exact ⟨_, cover1085⟩
    · exact ⟨_, cover1086⟩
    · exact ⟨_, cover1087⟩
    · exact ⟨_, cover1088⟩
    · exact ⟨_, cover1089⟩
    · exact ⟨_, cover1090⟩
    · exact ⟨_, cover1091⟩
    · exact ⟨_, cover1094⟩
    · exact ⟨_, cover1095⟩
    · exact ⟨_, cover1096⟩

def price : EarlyPrice := ⟨3, 38, 10, 65/100, 60/100, ![1353186590672, 195884188559, 38684029720, 2036020695], 939610290393008⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5771/73, 180681/191, 683859/191, 3089818/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons34
end Z6969Source1548

-- Source: Research6969.PrefixNearSavedCubicSingletons34
section Z6969Source1549
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons34
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨338,4217,79,945,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons34.plan Lower6960.Prefix6969RescueData.CubicSingletons34.plan Lower6960.Prefix6969RescueData.CubicSingletons34.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 38 38 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons34.plan, Lower6960.Prefix6969MainCases.CubicSingletons34.price, Lower6960.Prefix6969MainCases.CubicSingletons34.valid, Lower6960.Prefix6969MainCases.CubicSingletons34.priced, Lower6960.Prefix6969MainCases.CubicSingletons34.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons34.plan, Lower6960.Prefix6969RescueData.CubicSingletons34.price, Lower6960.Prefix6969RescueData.CubicSingletons34.sources, Lower6960.Prefix6969RescueData.CubicSingletons34.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 201139005745965136 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons34
end Z6969Source1549

-- Source: Research6969.PrefixMainDataCubicSingletons35
section Z6969Source1550
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons35
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 21, 23, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank35 2061, bank44 2409, bank53 2871, bank42 4552, bank61 2536, bank69 4787, bank72 2841, bank95 3103, bank113 3716, bank138 3813, bank144 4704, bank131 21237, bank164 6138, bank214 10456, bank186 46700, bank174 148759, bank169 292467] i
  head := src1424
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15734, 159089, 731554, 3309656],
    ![25417/2, 452007/4, 521808, 2411809],
    ![54680/9, 54750, 521808, 8652943/4],
    ![29433/8, 530943/16, 801550/3, 9338878/9],
    ![5710/3, 151105/9, 1369699/8, 10471941/16],
    ![18775/16, 688985/64, 622951/5, 12240129/25],
    ![86808/121, 813254/121, 3659416/49, 8242641/25],
    ![73478/121, 813254/121, 3659416/49, 8242641/25],
    ![73478/121, 791871/121, 3558307/49, 12885416/49],
    ![73478/121, 791871/121, 3446640/49, 12885416/49],
    ![73478/121, 791871/121, 3446640/49, 12885416/49],
    ![73478/121, 791871/121, 3446640/49, 31532686/121],
    ![73478/121, 57577/11, 2719869/49, 9440498/49],
    ![73478/121, 57577/11, 2719869/49, 9440498/49],
    ![73478/121, 1556749/300, 6256320/121, 4481442/25],
    ![688141/1681, 1556749/300, 6256320/121, 4481442/25],
    ![688141/1681, 191524/41, 2205915/49, 4186116/25],
    ![688141/1681, 5742618/1369, 103345963/2601, 92972138/625],
    ![481425/1369, 5742618/1369, 103345963/2601, 92972138/625],
    ![462882/1369, 5742618/1369, 103345963/2601, 92972138/625],
    ![459151/1369, 5742618/1369, 103345963/2601, 92972138/625]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 39 385979 := by
  refine ⟨?_, rank154 5081, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1424⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free35_0
    · exact free44_0
    · exact free53_0
    · exact free42_2
    · exact free61_0
    · exact free69_0
    · exact free72_0
    · exact free95_0
    · exact free113_0
    · exact free138_0
    · exact free144_0
    · exact free131_0
    · exact free164_0
    · exact free214_0
    · exact free186_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [300080212, 298615597, 299924480, 298793822, 299785168, 298196344, 299827350, 303870521, 162037606, 162055162, 162159585, 162182314, 84853257, 84803697, 70449002, 70728502, 92038513, 92040086, 117272017, 163847188, 227567951], [1190176, 1197670, 1190973, 1196758, 1191686, 1199816, 1191470, 1170781, 2367259, 2366967, 2365230, 2364852, 4694829, 4697772, 5691679, 5669460, 4313485, 4313406, 3340500, 2337166, 1632990],
  ![120797619749820, 1613965807684, 204811155900, 5131915460], 160944076951560009⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,4,7,7,7,7,13,13,15,15,12,12,9,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5742618/1369, 103345963/2601, 92972138/625] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons35
end Z6969Source1550

-- Source: Research6969.PrefixRescueDataCubicSingletons35
section Z6969Source1551
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons35
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,39⟩
  bank i := ![bank135 4282, bank142 4817, bank142 5419, bank156 5419, bank156 6096, bank194 7715, bank234 13899, bank324 50764, bank376 102908, bank365 81311, bank338 72277] i
  reserve i := ![0, 1, 2, 3, 4, 8, 25, 110, 245, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 39

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank135 4282
    · exact rank142 4817
    · exact rank142 5419
    · exact rank156 5419
    · exact rank156 6096
    · exact rank194 7715
    · exact rank234 13899
    · exact rank324 50764
    · exact rank376 102908
    · exact rank365 81311
    · exact rank338 72277
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1097⟩
    · exact ⟨_, cover1098⟩
    · exact ⟨_, cover1099⟩
    · exact ⟨_, cover1100⟩
    · exact ⟨_, cover1101⟩
    · exact ⟨_, cover1102⟩
    · exact ⟨_, cover1103⟩
    · exact ⟨_, cover1106⟩
    · exact ⟨_, cover1109⟩
    · exact ⟨_, cover1108⟩
    · exact ⟨_, cover1107⟩

def price : EarlyPrice := ⟨3, 39, 10, 65/100, 60/100, ![1562392580268, 244063230402, 47824626150, 2452567950], 1047023073893987⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5725/73, 112879/123, 142116/41, 668902/41] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons35
end Z6969Source1551

-- Source: Research6969.PrefixNearSavedCubicSingletons35
section Z6969Source1552
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons35
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4194,78,917,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons35.plan Lower6960.Prefix6969RescueData.CubicSingletons35.plan Lower6960.Prefix6969RescueData.CubicSingletons35.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 39 39 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons35.plan, Lower6960.Prefix6969MainCases.CubicSingletons35.price, Lower6960.Prefix6969MainCases.CubicSingletons35.valid, Lower6960.Prefix6969MainCases.CubicSingletons35.priced, Lower6960.Prefix6969MainCases.CubicSingletons35.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons35.plan, Lower6960.Prefix6969RescueData.CubicSingletons35.price, Lower6960.Prefix6969RescueData.CubicSingletons35.sources, Lower6960.Prefix6969RescueData.CubicSingletons35.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 201321941475632960 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons35
end Z6969Source1552

-- Source: Research6969.PrefixMainDataCubicSingletons36
section Z6969Source1553
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons36
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 12, 14, 18, 21, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank35 2061, bank44 2409, bank53 2871, bank42 4552, bank58 2557, bank69 4787, bank71 2671, bank88 2848, bank105 3304, bank137 3540, bank144 4704, bank131 21237, bank165 6130, bank214 10456, bank186 46700, bank174 148759, bank169 292467] i
  head := src1425
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15734, 158862, 730578, 3301217],
    ![25417/2, 112456, 521808, 2411809],
    ![54680/9, 490390/9, 521808, 4276233/2],
    ![29433/8, 264203/8, 2393204/9, 1025604],
    ![5710/3, 33415/2, 170379, 5175171/8],
    ![18775/16, 171435/16, 3100182/25, 12097998/25],
    ![86808/121, 809478/121, 74340, 8242641/25],
    ![73478/121, 809478/121, 74340, 8242641/25],
    ![73478/121, 786230/121, 3540868/49, 12841254/49],
    ![73478/121, 786230/121, 3446640/49, 12841254/49],
    ![73478/121, 786230/121, 3446640/49, 12841254/49],
    ![73478/121, 786230/121, 3446640/49, 12841254/49],
    ![73478/121, 2198068/361, 447456/7, 222784],
    ![73478/121, 636468/121, 2797710/49, 8888940/49],
    ![73478/121, 257993/50, 6256320/121, 4429404/25],
    ![688141/1681, 257993/50, 6256320/121, 4429404/25],
    ![688141/1681, 7824416/1681, 313216/7, 1503076/9],
    ![688141/1681, 5712056/1369, 102802042/2601, 91892556/625],
    ![481425/1369, 5712056/1369, 102802042/2601, 91892556/625],
    ![462882/1369, 5712056/1369, 102802042/2601, 91892556/625],
    ![459151/1369, 5712056/1369, 102802042/2601, 91892556/625]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 40 385979 := by
  refine ⟨?_, rank154 5022, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1425⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free35_0
    · exact free44_0
    · exact free53_0
    · exact free42_2
    · exact free58_0
    · exact free69_0
    · exact free71_0
    · exact free88_0
    · exact free105_0
    · exact free137_0
    · exact free144_0
    · exact free131_0
    · exact free165_0
    · exact free214_0
    · exact free186_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [298849332, 297686968, 296729157, 298152266, 298738484, 297045943, 297534484, 301544676, 161410202, 161256956, 161425347, 161464292, 161493506, 94565103, 67841949, 67884706, 91459820, 91556563, 116929090, 163504260, 227306430], [1196474, 1202422, 1207323, 1200041, 1197041, 1205702, 1203202, 1182682, 2377693, 2380241, 2377441, 2376793, 2376307, 4186049, 5921414, 5917538, 4342673, 4337794, 3350089, 2342869, 1635140],
  ![120658799172600, 1614248235720, 204575787000, 5166642040], 160216170430362722⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,4,7,7,7,7,7,12,16,16,12,12,9,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5712056/1369, 102802042/2601, 91892556/625] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons36
end Z6969Source1553

-- Source: Research6969.PrefixRescueDataCubicSingletons36
section Z6969Source1554
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons36
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,40⟩
  bank i := ![bank134 4282, bank143 4282, bank143 4817, bank155 5419, bank157 5419, bank193 7715, bank204 10983, bank228 12355, bank243 22261, bank338 64247, bank352 91474] i
  reserve i := ![0, 1, 2, 3, 4, 8, 13, 20, 40, 145, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 40

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank134 4282
    · exact rank143 4282
    · exact rank143 4817
    · exact rank155 5419
    · exact rank157 5419
    · exact rank193 7715
    · exact rank204 10983
    · exact rank228 12355
    · exact rank243 22261
    · exact rank338 64247
    · exact rank352 91474
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1110⟩
    · exact ⟨_, cover1111⟩
    · exact ⟨_, cover1112⟩
    · exact ⟨_, cover1113⟩
    · exact ⟨_, cover1114⟩
    · exact ⟨_, cover1115⟩
    · exact ⟨_, cover1116⟩
    · exact ⟨_, cover1117⟩
    · exact ⟨_, cover1118⟩
    · exact ⟨_, cover1121⟩
    · exact ⟨_, cover1122⟩

def price : EarlyPrice := ⟨3, 40, 10, 65/100, 60/100, ![1424406966436, 187214713668, 33852906236, 1692661182], 874289494038662⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![13971/191, 1839/2, 659342/191, 1284940/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons36
end Z6969Source1554

-- Source: Research6969.PrefixNearSavedCubicSingletons36
section Z6969Source1555
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons36
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4172,73,919,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons36.plan Lower6960.Prefix6969RescueData.CubicSingletons36.plan Lower6960.Prefix6969RescueData.CubicSingletons36.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 40 40 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons36.plan, Lower6960.Prefix6969MainCases.CubicSingletons36.price, Lower6960.Prefix6969MainCases.CubicSingletons36.valid, Lower6960.Prefix6969MainCases.CubicSingletons36.priced, Lower6960.Prefix6969MainCases.CubicSingletons36.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons36.plan, Lower6960.Prefix6969RescueData.CubicSingletons36.price, Lower6960.Prefix6969RescueData.CubicSingletons36.sources, Lower6960.Prefix6969RescueData.CubicSingletons36.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 200816918415748225 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons36
end Z6969Source1555

-- Source: Research6969.PrefixMainDataCubicSingletons4
section Z6969Source1556
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons4
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank84 5564, bank85 2903, bank74 6544, bank113 3716, bank140 3997, bank150 6517, bank120 36262, bank198 9780, bank210 11036, bank183 54742, bank174 148759, bank169 292467] i
  head := src1393
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 169196, 787140, 4119443],
    ![12303, 136601, 1235093/2, 3048654],
    ![53398/9, 592051/9, 1235093/2, 3048654],
    ![29433/8, 635347/16, 2875682/9, 4600514/3],
    ![16211/9, 734233/36, 3346031/16, 16842687/16],
    ![24292/27, 906107/81, 4117177/36, 7481467/12],
    ![73478/121, 1179326/121, 5323813/49, 7481467/12],
    ![73478/121, 1179326/121, 5323813/49, 3106223/6],
    ![73478/121, 964259/121, 4323127/49, 19042824/49],
    ![63754/121, 3198326/441, 543881/8, 19042824/49],
    ![63754/121, 3198326/441, 543881/8, 43597254/121],
    ![61324/121, 3198326/441, 543881/8, 43597254/121],
    ![61324/121, 771743/121, 13336612/225, 18602296/75],
    ![61324/121, 771743/121, 13336612/225, 18602296/75],
    ![61324/121, 9507644/1681, 42801676/841, 195744612/841],
    ![667406/1681, 9507644/1681, 42801676/841, 195744612/841],
    ![667406/1681, 773284/147, 10434914/225, 10627600/49],
    ![667406/1681, 6962620/1369, 125342294/2809, 580085268/2809],
    ![954471/2738, 6962620/1369, 125342294/2809, 580085268/2809],
    ![462882/1369, 6962620/1369, 125342294/2809, 580085268/2809],
    ![459151/1369, 6962620/1369, 125342294/2809, 580085268/2809]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 8 385979 := by
  refine ⟨?_, rank154 7509, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1393⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free61_0
    · exact free84_0
    · exact free85_0
    · exact free74_2
    · exact free113_0
    · exact free140_0
    · exact free150_0
    · exact free120_0
    · exact free198_0
    · exact free210_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [344910724, 343543275, 343587378, 344813584, 343470304, 343956311, 343870609, 343751460, 170619178, 171284734, 171075623, 170652381, 82087383, 85661319, 66605234, 90228690, 103947573, 103747405, 126389466, 173419878, 234894192], [1001430, 1005179, 1005058, 1001697, 1005379, 1004047, 1004282, 1004608, 2225291, 2217264, 2219786, 2224891, 4859102, 4646836, 6033513, 4404769, 3788959, 3797329, 3085574, 2191511, 1572742],
  ![124686534997440, 1606051240428, 211404772800, 4517825480], 189737384617545739⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,6,6,6,6,13,13,16,12,10,11,9,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 6962620/1369, 125342294/2809, 580085268/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons4
end Z6969Source1556

-- Source: Research6969.PhysicalChecks064
section Z6969Source1557
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src713 : Request := ⟨⟨⟨2600,3627,783,375939⟩,527755772952576,4741611634368⟩,32,3,1,385979,8⟩
theorem cover713 : PhysicalWindow.Cover (PhysicalWindow.Triangular src713) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src714 : Request := ⟨⟨⟨3950,5512,1189,185441⟩,1848744952463360,25255771038451⟩,32,3,1,385979,8⟩
theorem cover714 : PhysicalWindow.Cover (PhysicalWindow.Triangular src714) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src715 : Request := ⟨⟨⟨6900,9628,2077,334168⟩,9849424459857920,234966243278304⟩,65,3,1,385979,8⟩
theorem cover715 : PhysicalWindow.Cover (PhysicalWindow.Triangular src715) 2411 2314 [2316, 2325, 2349, 2411] := triangleCover (by decide +kernel)
def src716 : Request := ⟨⟨⟨10000,13954,3010,422931⟩,29974681586237440,1036364370066239⟩,85,3,1,385979,8⟩
theorem cover716 : PhysicalWindow.Cover (PhysicalWindow.Triangular src716) 2411 2314 [2320, 2339, 2392, 2411] := triangleCover (by decide +kernel)
def src717 : Request := ⟨⟨⟨1000,1395,301,45124⟩,30103476895744,104105680031⟩,0,3,1,385979,9⟩
theorem cover717 : PhysicalWindow.Cover (PhysicalWindow.Triangular src717) 2411 2314 [2323, 2352, 2411] := triangleCover (by decide +kernel)
def src718 : Request := ⟨⟨⟨1000,1395,301,50764⟩,30103476895744,104105680031⟩,1,3,1,385979,9⟩
theorem cover718 : PhysicalWindow.Cover (PhysicalWindow.Triangular src718) 2411 2314 [2321, 2345, 2411] := triangleCover (by decide +kernel)
def src719 : Request := ⟨⟨⟨1000,1395,301,57109⟩,30103476895744,104105680031⟩,2,3,1,385979,9⟩
theorem cover719 : PhysicalWindow.Cover (PhysicalWindow.Triangular src719) 2411 2314 [2318, 2332, 2374, 2411] := triangleCover (by decide +kernel)
def src720 : Request := ⟨⟨⟨1200,1674,361,64247⟩,51955677528064,215563369662⟩,4,3,1,385979,9⟩
theorem cover720 : PhysicalWindow.Cover (PhysicalWindow.Triangular src720) 2411 2314 [2317, 2329, 2364, 2411] := triangleCover (by decide +kernel)
def src721 : Request := ⟨⟨⟨1450,2023,436,72277⟩,91566841790464,459151377566⟩,6,3,1,385979,9⟩
theorem cover721 : PhysicalWindow.Cover (PhysicalWindow.Triangular src721) 2411 2314 [2320, 2340, 2398, 2411] := triangleCover (by decide +kernel)
def src722 : Request := ⟨⟨⟨1750,2442,527,91474⟩,161065121873920,975196209190⟩,10,3,1,385979,9⟩
theorem cover722 : PhysicalWindow.Cover (PhysicalWindow.Triangular src722) 2411 2314 [2320, 2340, 2398, 2411] := triangleCover (by decide +kernel)
def src723 : Request := ⟨⟨⟨2600,3628,770,115771⟩,521059839508480,4684185417862⟩,16,3,1,385979,9⟩
theorem cover723 : PhysicalWindow.Cover (PhysicalWindow.Triangular src723) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src725 : Request := ⟨⟨⟨3950,5512,1189,146522⟩,1848744952463360,25255771038451⟩,25,3,1,385979,9⟩
theorem cover725 : PhysicalWindow.Cover (PhysicalWindow.Triangular src725) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src727 : Request := ⟨⟨⟨4800,6698,1445,208621⟩,3317023033262080,55058665830093⟩,40,3,1,385979,9⟩
theorem cover727 : PhysicalWindow.Cover (PhysicalWindow.Triangular src727) 2411 2314 [2316, 2324, 2346, 2408, 2411] := triangleCover (by decide +kernel)
def src728 : Request := ⟨⟨⟨4800,6697,1445,535271⟩,3317023033262080,55032215749682⟩,65,3,1,385979,9⟩
theorem cover728 : PhysicalWindow.Cover (PhysicalWindow.Triangular src728) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src729 : Request := ⟨⟨⟨10000,13953,3010,535271⟩,29974681586237440,1036125345444439⟩,110,3,1,385979,9⟩
theorem cover729 : PhysicalWindow.Cover (PhysicalWindow.Triangular src729) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src730 : Request := ⟨⟨⟨1000,1395,296,45124⟩,29722184515584,102755930405⟩,0,3,1,385979,10⟩
theorem cover730 : PhysicalWindow.Cover (PhysicalWindow.Triangular src730) 2411 2314 [2322, 2349, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1557

-- Source: Research6969.PrefixRescueDataCubicSingletons4
section Z6969Source1558
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons4
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,3,1,8⟩
  bank i := ![bank220 50764, bank227 50764, bank227 57109, bank227 72277, bank252 91474, bank270 115771, bank315 185441, bank266 375939, bank359 334168, bank384 422931] i
  reserve i := ![0, 1, 2, 4, 10, 16, 32, 32, 65, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 8

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank220 50764
    · exact rank227 50764
    · exact rank227 57109
    · exact rank227 72277
    · exact rank252 91474
    · exact rank270 115771
    · exact rank315 185441
    · exact rank266 375939
    · exact rank359 334168
    · exact rank384 422931
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover707⟩
    · exact ⟨_, cover708⟩
    · exact ⟨_, cover709⟩
    · exact ⟨_, cover710⟩
    · exact ⟨_, cover711⟩
    · exact ⟨_, cover712⟩
    · exact ⟨_, cover714⟩
    · exact ⟨_, cover713⟩
    · exact ⟨_, cover715⟩
    · exact ⟨_, cover716⟩

def price : EarlyPrice := ⟨3, 8, 9, 95/100, 80/100, ![1317153468126, 363374518707, 9374181460, 2343564930], 8779494326722725⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![1731/11, 447011/86, 1380425/86, 1691724/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons4
end Z6969Source1558

-- Source: Research6969.PrefixNearSavedCubicSingletons4
section Z6969Source1559
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons4
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,5085,157,5197,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons4.plan Lower6960.Prefix6969RescueData.CubicSingletons4.plan Lower6960.Prefix6969RescueData.CubicSingletons4.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 8 8 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons4.plan, Lower6960.Prefix6969MainCases.CubicSingletons4.price, Lower6960.Prefix6969MainCases.CubicSingletons4.valid, Lower6960.Prefix6969MainCases.CubicSingletons4.priced, Lower6960.Prefix6969MainCases.CubicSingletons4.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons4.plan, Lower6960.Prefix6969RescueData.CubicSingletons4.price, Lower6960.Prefix6969RescueData.CubicSingletons4.sources, Lower6960.Prefix6969RescueData.CubicSingletons4.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 223159617641302904 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons4
end Z6969Source1559

end Merged_Z6969Pack0707

-- merged module Z6969Pack0708
section Merged_Z6969Pack0708

-- Source: Research6969.PrefixMainDataCubicSingletons5
section Z6969Source1560
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons5
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 17, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank23 1898, bank26 2102, bank32 2243, bank44 2409, bank54 2755, bank74 3583, bank84 5564, bank98 3253, bank137 3540, bank125 29117, bank152 6378, bank198 9780, bank183 54742, bank210 11036, bank174 148759, bank169 292467] i
  head := src1394
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14917, 167206, 778580, 3845490],
    ![12303, 135764, 613780, 3010896],
    ![53398/9, 588424/9, 613780, 3010896],
    ![3599, 158533/4, 2874296/9, 1563952],
    ![60658/25, 683644/25, 211251, 1104601],
    ![16211/9, 364931/18, 831509/4, 2079261/2],
    ![18775/16, 408705/32, 396682/3, 644809],
    ![89110/121, 950390/121, 4307164/49, 20431080/49],
    ![89110/121, 950390/121, 1383061/18, 369049],
    ![63754/121, 454592/63, 543881/8, 369049],
    ![63754/121, 454592/63, 543881/8, 10582009/36],
    ![63754/121, 789684/121, 252225/4, 1166784/5],
    ![675632/1681, 789684/121, 252225/4, 1166784/5],
    ![675632/1681, 9468912/1681, 42506880/841, 189196992/841],
    ![675632/1681, 329264/63, 10368016/225, 1074496/5],
    ![954471/2738, 329264/63, 10368016/225, 1074496/5],
    ![954471/2738, 6917050/1369, 124528544/2809, 572900832/2809],
    ![462882/1369, 6917050/1369, 124528544/2809, 572900832/2809],
    ![459151/1369, 6917050/1369, 124528544/2809, 572900832/2809]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 9 385979 := by
  refine ⟨?_, rank154 7416, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1394⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free23_0
    · exact free26_0
    · exact free32_0
    · exact free44_0
    · exact free54_0
    · exact free74_1
    · exact free84_0
    · exact free98_0
    · exact free137_0
    · exact free125_0
    · exact free152_0
    · exact free198_0
    · exact free183_0
    · exact free210_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [343641084, 340941862, 342408099, 342410683, 343110075, 343510802, 343026186, 147118620, 147358119, 147528797, 147159164, 74223356, 74411283, 89784125, 103179208, 103067425, 125904459, 172934871, 234524152], [1004911, 1012310, 1008291, 1008283, 1006366, 1005268, 1006596, 2615361, 2611378, 2608540, 2614687, 5391637, 5376698, 4427192, 3821315, 3826034, 3099135, 2197361, 1575785],
  ![124490110364640, 1606450783508, 211071736800, 4551977290], 187832475323613924⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,7,7,7,7,15,15,12,11,11,9,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 6917050/1369, 124528544/2809, 572900832/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons5
end Z6969Source1560

-- Source: Research6969.PrefixRescueDataCubicSingletons5
section Z6969Source1561
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons5
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,9⟩
  bank i := ![bank221 45124, bank221 50764, bank221 57109, bank227 64247, bank236 72277, bank245 91474, bank269 115771, bank315 146522, bank332 208621, bank328 535271, bank382 535271] i
  reserve i := ![0, 1, 2, 4, 6, 10, 16, 25, 40, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 9

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 45124
    · exact rank221 50764
    · exact rank221 57109
    · exact rank227 64247
    · exact rank236 72277
    · exact rank245 91474
    · exact rank269 115771
    · exact rank315 146522
    · exact rank332 208621
    · exact rank328 535271
    · exact rank382 535271
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover717⟩
    · exact ⟨_, cover718⟩
    · exact ⟨_, cover719⟩
    · exact ⟨_, cover720⟩
    · exact ⟨_, cover721⟩
    · exact ⟨_, cover722⟩
    · exact ⟨_, cover723⟩
    · exact ⟨_, cover725⟩
    · exact ⟨_, cover727⟩
    · exact ⟨_, cover728⟩
    · exact ⟨_, cover729⟩

def price : EarlyPrice := ⟨3, 9, 10, 95/100, 80/100, ![1875396351169, 455098575280, 10545953390, 2343564930], 8364735904646487⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![9587/66, 562361/111, 577130/37, 1605813/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons5
end Z6969Source1561

-- Source: Research6969.PrefixNearSavedCubicSingletons5
section Z6969Source1562
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons5
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,5052,145,5066,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons5.plan Lower6960.Prefix6969RescueData.CubicSingletons5.plan Lower6960.Prefix6969RescueData.CubicSingletons5.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 9 9 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons5.plan, Lower6960.Prefix6969MainCases.CubicSingletons5.price, Lower6960.Prefix6969MainCases.CubicSingletons5.valid, Lower6960.Prefix6969MainCases.CubicSingletons5.priced, Lower6960.Prefix6969MainCases.CubicSingletons5.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons5.plan, Lower6960.Prefix6969RescueData.CubicSingletons5.price, Lower6960.Prefix6969RescueData.CubicSingletons5.sources, Lower6960.Prefix6969RescueData.CubicSingletons5.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 223051821952878682 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons5
end Z6969Source1562

-- Source: Research6969.PrefixMainDataCubicSingletons6
section Z6969Source1563
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons6
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 14, 14, 21, 21, 21, 30, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank44 2409, bank53 2871, bank62 3617, bank82 2965, bank84 5564, bank116 3644, bank110 3824, bank168 4492, bank121 32187, bank150 6517, bank198 9780, bank179 76613, bank212 10770, bank170 227095] i
  head := src1395
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![14876, 167619, 779582, 3826350],
    ![12303, 134945, 1220189/2, 2973950],
    ![53398/9, 584875/9, 1220189/2, 2973950],
    ![29433/8, 627435/16, 315554, 13463350/9],
    ![16211/9, 725585/36, 3306471/16, 16429975/16],
    ![18775/16, 812405/64, 396682/3, 644809],
    ![86808/121, 956870/121, 87688, 21030075/49],
    ![86808/121, 956870/121, 87688, 21030075/49],
    ![86808/121, 956870/121, 87688, 43437250/121],
    ![63754/121, 452330/63, 543881/8, 43437250/121],
    ![63754/121, 765601/121, 119341/2, 2135384/9],
    ![63754/121, 1515425/242, 117349/2, 2135384/9],
    ![63754/121, 1515425/242, 117349/2, 24677925/121],
    ![671521/1681, 1515425/242, 117349/2, 24677925/121],
    ![671521/1681, 228860/41, 42245996/841, 24677925/121],
    ![671521/1681, 981500/189, 6181534/135, 24677925/121],
    ![470505/1369, 981500/189, 6181534/135, 24677925/121],
    ![470505/1369, 27532225/5476, 123576705/2809, 552231750/2809],
    ![920087/2738, 27532225/5476, 123576705/2809, 552231750/2809]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 10 385979 := by
  refine ⟨?_, rank154 7325, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1395⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free32_0
    · exact free44_0
    · exact free53_0
    · exact free62_0
    · exact free82_0
    · exact free84_0
    · exact free116_1
    · exact free110_0
    · exact free168_0
    · exact free121_0
    · exact free150_0
    · exact free198_0
    · exact free179_0
    · exact free212_0
    · exact free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [342402278, 341232983, 341292954, 341652789, 342004062, 340613795, 150440488, 150377921, 150469907, 150449223, 92897403, 114081140, 74770370, 69755332, 91927760, 106978032, 107005349, 151588154, 234483700], [1008307, 1011512, 1011347, 1010361, 1009398, 1013209, 2560119, 2561159, 2559629, 2559973, 4270164, 3437103, 5348244, 5747980, 4319071, 3683736, 3682788, 2541033, 1576117],
  ![124468637634000, 1606494702200, 211035330000, 4404481380], 187453914992202421⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,7,7,7,7,12,10,14,16,12,10,10,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 27532225/5476, 123576705/2809, 552231750/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons6
end Z6969Source1563

-- Source: Research6969.PhysicalChecks065
section Z6969Source1564
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src731 : Request := ⟨⟨⟨1200,1674,361,45124⟩,51955677528064,215563369662⟩,1,3,1,385979,10⟩
theorem cover731 : PhysicalWindow.Cover (PhysicalWindow.Triangular src731) 2411 2314 [2319, 2337, 2389, 2411] := triangleCover (by decide +kernel)
def src732 : Request := ⟨⟨⟨1200,1674,361,50764⟩,51955677528064,215563369662⟩,2,3,1,385979,10⟩
theorem cover732 : PhysicalWindow.Cover (PhysicalWindow.Triangular src732) 2411 2314 [2323, 2352, 2411] := triangleCover (by decide +kernel)
def src733 : Request := ⟨⟨⟨1450,2023,436,57109⟩,91566841790464,459151377566⟩,4,3,1,385979,10⟩
theorem cover733 : PhysicalWindow.Cover (PhysicalWindow.Triangular src733) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src734 : Request := ⟨⟨⟨1750,2442,527,72277⟩,161065121873920,975196209190⟩,8,3,1,385979,10⟩
theorem cover734 : PhysicalWindow.Cover (PhysicalWindow.Triangular src734) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src735 : Request := ⟨⟨⟨2600,3628,783,102908⟩,527755772952576,4745819470168⟩,16,3,1,385979,10⟩
theorem cover735 : PhysicalWindow.Cover (PhysicalWindow.Triangular src735) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src736 : Request := ⟨⟨⟨4800,6698,1445,164837⟩,3317023033262080,55058665830093⟩,32,3,1,385979,10⟩
theorem cover736 : PhysicalWindow.Cover (PhysicalWindow.Triangular src736) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src737 : Request := ⟨⟨⟨6900,9628,2077,297039⟩,9849424459857920,234966243278304⟩,65,3,1,385979,10⟩
theorem cover737 : PhysicalWindow.Cover (PhysicalWindow.Triangular src737) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src738 : Request := ⟨⟨⟨5700,7952,1716,857398⟩,5553838907981824,109384694947514⟩,85,3,1,385979,10⟩
theorem cover738 : PhysicalWindow.Cover (PhysicalWindow.Triangular src738) 2411 2314 [2315, 2321, 2337, 2381, 2411] := triangleCover (by decide +kernel)
def src739 : Request := ⟨⟨⟨10000,13954,3010,375939⟩,29974681586237440,1036364370066239⟩,85,3,1,385979,10⟩
theorem cover739 : PhysicalWindow.Cover (PhysicalWindow.Triangular src739) 2411 2314 [2319, 2335, 2379, 2411] := triangleCover (by decide +kernel)
def src740 : Request := ⟨⟨⟨1000,1395,301,40111⟩,30103476895744,104105680031⟩,0,3,1,385979,11⟩
theorem cover740 : PhysicalWindow.Cover (PhysicalWindow.Triangular src740) 2411 2314 [2323, 2352, 2411] := triangleCover (by decide +kernel)
def src741 : Request := ⟨⟨⟨1000,1395,301,45124⟩,30103476895744,104105680031⟩,1,3,1,385979,11⟩
theorem cover741 : PhysicalWindow.Cover (PhysicalWindow.Triangular src741) 2411 2314 [2321, 2345, 2411] := triangleCover (by decide +kernel)
def src742 : Request := ⟨⟨⟨1000,1395,301,50764⟩,30103476895744,104105680031⟩,2,3,1,385979,11⟩
theorem cover742 : PhysicalWindow.Cover (PhysicalWindow.Triangular src742) 2411 2314 [2318, 2333, 2377, 2411] := triangleCover (by decide +kernel)
def src743 : Request := ⟨⟨⟨1200,1674,361,57109⟩,51955677528064,215563369662⟩,4,3,1,385979,11⟩
theorem cover743 : PhysicalWindow.Cover (PhysicalWindow.Triangular src743) 2411 2314 [2317, 2329, 2364, 2411] := triangleCover (by decide +kernel)
def src744 : Request := ⟨⟨⟨1750,2442,527,81311⟩,161065121873920,975196209190⟩,10,3,1,385979,11⟩
theorem cover744 : PhysicalWindow.Cover (PhysicalWindow.Triangular src744) 2411 2314 [2320, 2340, 2398, 2411] := triangleCover (by decide +kernel)
def src745 : Request := ⟨⟨⟨2600,3628,783,102908⟩,527755772952576,4745819470168⟩,16,3,1,385979,11⟩
theorem cover745 : PhysicalWindow.Cover (PhysicalWindow.Triangular src745) 2411 2314 [2325, 2359, 2411] := triangleCover (by decide +kernel)
def src746 : Request := ⟨⟨⟨3950,5512,1189,130242⟩,1848744952463360,25255771038451⟩,25,3,1,385979,11⟩
theorem cover746 : PhysicalWindow.Cover (PhysicalWindow.Triangular src746) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1564

-- Source: Research6969.PrefixRescueDataCubicSingletons6
section Z6969Source1565
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons6
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,3,1,10⟩
  bank i := ![bank220 45124, bank227 45124, bank227 50764, bank236 57109, bank245 72277, bank270 102908, bank332 164837, bank359 297039, bank342 857398, bank384 375939] i
  reserve i := ![0, 1, 2, 4, 8, 16, 32, 65, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 10

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank220 45124
    · exact rank227 45124
    · exact rank227 50764
    · exact rank236 57109
    · exact rank245 72277
    · exact rank270 102908
    · exact rank332 164837
    · exact rank359 297039
    · exact rank342 857398
    · exact rank384 375939
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover730⟩
    · exact ⟨_, cover731⟩
    · exact ⟨_, cover732⟩
    · exact ⟨_, cover733⟩
    · exact ⟨_, cover734⟩
    · exact ⟨_, cover735⟩
    · exact ⟨_, cover736⟩
    · exact ⟨_, cover737⟩
    · exact ⟨_, cover738⟩
    · exact ⟨_, cover739⟩

def price : EarlyPrice := ⟨3, 10, 9, 95/100, 80/100, ![3337792110936, 691840404966, 11717725320, 2343564930], 9783912494261020⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5692/43, 406039/86, 1267357/86, 1879695/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons6
end Z6969Source1565

-- Source: Research6969.PrefixNearSavedCubicSingletons6
section Z6969Source1566
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons6
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨336,5027,132,4721,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons6.plan Lower6960.Prefix6969RescueData.CubicSingletons6.plan Lower6960.Prefix6969RescueData.CubicSingletons6.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 10 10 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons6.plan, Lower6960.Prefix6969MainCases.CubicSingletons6.price, Lower6960.Prefix6969MainCases.CubicSingletons6.valid, Lower6960.Prefix6969MainCases.CubicSingletons6.priced, Lower6960.Prefix6969MainCases.CubicSingletons6.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons6.plan, Lower6960.Prefix6969RescueData.CubicSingletons6.price, Lower6960.Prefix6969RescueData.CubicSingletons6.sources, Lower6960.Prefix6969RescueData.CubicSingletons6.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 224163778746674123 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons6
end Z6969Source1566

-- Source: Research6969.PrefixMainDataCubicSingletons7
section Z6969Source1567
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons7
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank84 5564, bank85 2903, bank74 6544, bank113 3716, bank140 3997, bank150 6517, bank120 36262, bank198 9780, bank212 10770, bank183 54742, bank174 148759, bank169 292467] i
  head := src1396
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 168368, 782724, 4077215],
    ![12303, 134117, 1212737/2, 2936598],
    ![53398/9, 581287/9, 1212737/2, 2936598],
    ![29433/8, 623479/16, 2822138/9, 4431418/3],
    ![16211/9, 721261/36, 3286691/16, 16223619/16],
    ![24292/27, 891479/81, 4050661/36, 7206479/12],
    ![73478/121, 1164422/121, 5257297/49, 7206479/12],
    ![73478/121, 1164422/121, 1920041/18, 2992051/6],
    ![73478/121, 944663/121, 4236187/49, 18342888/49],
    ![63754/121, 3150302/441, 543881/8, 18342888/49],
    ![63754/121, 3150302/441, 543881/8, 41994798/121],
    ![61324/121, 3150302/441, 543881/8, 41994798/121],
    ![61324/121, 756011/121, 235037/4, 17918552/75],
    ![61324/121, 756011/121, 235037/4, 17918552/75],
    ![61324/121, 9321068/1681, 100415/2, 188549844/841],
    ![667406/1681, 9321068/1681, 100415/2, 188549844/841],
    ![667406/1681, 2275324/441, 3412126/75, 3143944/15],
    ![667406/1681, 27347397/5476, 219708/5, 545295870/2809],
    ![954471/2738, 27347397/5476, 219708/5, 545295870/2809],
    ![462882/1369, 27347397/5476, 219708/5, 545295870/2809],
    ![459151/1369, 27347397/5476, 219708/5, 545295870/2809]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 11 385979 := by
  refine ⟨?_, rank154 7233, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1396⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free61_0
    · exact free84_0
    · exact free85_0
    · exact free74_2
    · exact free113_0
    · exact free140_0
    · exact free150_0
    · exact free120_0
    · exact free198_0
    · exact free212_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [339646300, 339388551, 338868966, 339352465, 337550263, 338544552, 338876011, 339208881, 169324804, 169596432, 169532204, 169607335, 80220871, 84541964, 67225139, 88470296, 102746252, 102457988, 125193031, 172223443, 233980418], [1015861, 1016568, 1017992, 1016667, 1021607, 1018881, 1017973, 1017060, 2246073, 2241556, 2242624, 2241375, 4971733, 4713318, 5977323, 4493459, 3839592, 3851761, 3119027, 2205942, 1580256],
  ![124201485482760, 1607038457272, 210582376200, 4582585280], 186392185325688656⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,14,13,16,12,11,11,9,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 27347397/5476, 219708/5, 545295870/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons7
end Z6969Source1567

-- Source: Research6969.PhysicalChecks066
section Z6969Source1568
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src747 : Request := ⟨⟨⟨4800,6698,1445,185441⟩,3317023033262080,55058665830093⟩,40,3,1,385979,11⟩
theorem cover747 : PhysicalWindow.Cover (PhysicalWindow.Triangular src747) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src748 : Request := ⟨⟨⟨5700,7952,1716,857398⟩,5553838907981824,109384694947514⟩,85,3,1,385979,11⟩
theorem cover748 : PhysicalWindow.Cover (PhysicalWindow.Triangular src748) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src749 : Request := ⟨⟨⟨6900,9626,2077,1545055⟩,9849424459857920,234809190715807⟩,110,3,1,385979,11⟩
theorem cover749 : PhysicalWindow.Cover (PhysicalWindow.Triangular src749) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src750 : Request := ⟨⟨⟨10000,13953,3010,475797⟩,29974681586237440,1036125345444439⟩,110,3,1,385979,11⟩
theorem cover750 : PhysicalWindow.Cover (PhysicalWindow.Triangular src750) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src751 : Request := ⟨⟨⟨1000,1395,296,40111⟩,29722184515584,102755930405⟩,0,3,1,385979,12⟩
theorem cover751 : PhysicalWindow.Cover (PhysicalWindow.Triangular src751) 2411 2314 [2322, 2349, 2411] := triangleCover (by decide +kernel)
def src752 : Request := ⟨⟨⟨1200,1674,361,40111⟩,51955677528064,215563369662⟩,1,3,1,385979,12⟩
theorem cover752 : PhysicalWindow.Cover (PhysicalWindow.Triangular src752) 2411 2314 [2320, 2340, 2399, 2411] := triangleCover (by decide +kernel)
def src753 : Request := ⟨⟨⟨1200,1674,361,45124⟩,51955677528064,215563369662⟩,2,3,1,385979,12⟩
theorem cover753 : PhysicalWindow.Cover (PhysicalWindow.Triangular src753) 2411 2314 [2323, 2353, 2411] := triangleCover (by decide +kernel)
def src754 : Request := ⟨⟨⟨1200,1674,361,57109⟩,51955677528064,215563369662⟩,4,3,1,385979,12⟩
theorem cover754 : PhysicalWindow.Cover (PhysicalWindow.Triangular src754) 2411 2314 [2325, 2360, 2411] := triangleCover (by decide +kernel)
def src755 : Request := ⟨⟨⟨1450,2023,436,72277⟩,91566841790464,459151377566⟩,8,3,1,385979,12⟩
theorem cover755 : PhysicalWindow.Cover (PhysicalWindow.Triangular src755) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src756 : Request := ⟨⟨⟨2100,2930,632,72277⟩,278060332482560,2019119590628⟩,10,3,1,385979,12⟩
theorem cover756 : PhysicalWindow.Cover (PhysicalWindow.Triangular src756) 2411 2314 [2321, 2343, 2406, 2411] := triangleCover (by decide +kernel)
def src757 : Request := ⟨⟨⟨2600,3628,783,91474⟩,527755772952576,4745819470168⟩,16,3,1,385979,12⟩
theorem cover757 : PhysicalWindow.Cover (PhysicalWindow.Triangular src757) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src758 : Request := ⟨⟨⟨3950,5512,1213,146522⟩,1877062482395136,25652240151764⟩,32,3,1,385979,12⟩
theorem cover758 : PhysicalWindow.Cover (PhysicalWindow.Triangular src758) 2411 2314 [2315, 2321, 2337, 2381, 2411] := triangleCover (by decide +kernel)
def src759 : Request := ⟨⟨⟨6900,9628,2077,264035⟩,9849424459857920,234966243278304⟩,65,3,1,385979,12⟩
theorem cover759 : PhysicalWindow.Cover (PhysicalWindow.Triangular src759) 2411 2314 [2316, 2324, 2346, 2407, 2411] := triangleCover (by decide +kernel)
def src760 : Request := ⟨⟨⟨5700,7952,1716,762132⟩,5553838907981824,109384694947514⟩,85,3,1,385979,12⟩
theorem cover760 : PhysicalWindow.Cover (PhysicalWindow.Triangular src760) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src761 : Request := ⟨⟨⟨10000,13954,3010,334168⟩,29974681586237440,1036364370066239⟩,85,3,1,385979,12⟩
theorem cover761 : PhysicalWindow.Cover (PhysicalWindow.Triangular src761) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
def src762 : Request := ⟨⟨⟨1000,1395,301,35655⟩,30103476895744,104105680031⟩,0,3,1,385979,13⟩
theorem cover762 : PhysicalWindow.Cover (PhysicalWindow.Triangular src762) 2411 2314 [2324, 2357, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1568

-- Source: Research6969.PrefixRescueDataCubicSingletons7
section Z6969Source1569
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons7
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,11⟩
  bank i := ![bank221 40111, bank221 45124, bank221 50764, bank227 57109, bank245 81311, bank270 102908, bank315 130242, bank332 185441, bank382 475797, bank342 857398, bank355 1545055] i
  reserve i := ![0, 1, 2, 4, 10, 16, 25, 40, 110, 85, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 11

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 40111
    · exact rank221 45124
    · exact rank221 50764
    · exact rank227 57109
    · exact rank245 81311
    · exact rank270 102908
    · exact rank315 130242
    · exact rank332 185441
    · exact rank382 475797
    · exact rank342 857398
    · exact rank355 1545055
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover740⟩
    · exact ⟨_, cover741⟩
    · exact ⟨_, cover742⟩
    · exact ⟨_, cover743⟩
    · exact ⟨_, cover744⟩
    · exact ⟨_, cover745⟩
    · exact ⟨_, cover746⟩
    · exact ⟨_, cover747⟩
    · exact ⟨_, cover750⟩
    · exact ⟨_, cover748⟩
    · exact ⟨_, cover749⟩

def price : EarlyPrice := ⟨3, 11, 10, 95/100, 80/100, ![6616273147375, 1235295524140, 12889497250, 2343564930], 11777465853147480⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![13780/111, 508907/111, 526958/37, 1744589/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons7
end Z6969Source1569

-- Source: Research6969.PrefixNearSavedCubicSingletons7
section Z6969Source1570
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons7
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4994,124,4584,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons7.plan Lower6960.Prefix6969RescueData.CubicSingletons7.plan Lower6960.Prefix6969RescueData.CubicSingletons7.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 11 11 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons7.plan, Lower6960.Prefix6969MainCases.CubicSingletons7.price, Lower6960.Prefix6969MainCases.CubicSingletons7.valid, Lower6960.Prefix6969MainCases.CubicSingletons7.priced, Lower6960.Prefix6969MainCases.CubicSingletons7.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons7.plan, Lower6960.Prefix6969RescueData.CubicSingletons7.price, Lower6960.Prefix6969RescueData.CubicSingletons7.sources, Lower6960.Prefix6969RescueData.CubicSingletons7.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 224542062656868928 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons7
end Z6969Source1570

-- Source: Research6969.PrefixMainDataCubicSingletons8
section Z6969Source1571
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons8
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank84 5564, bank85 2903, bank74 6544, bank113 3716, bank140 3997, bank150 6517, bank120 36262, bank198 9780, bank212 10770, bank183 54742, bank174 148759, bank169 292467] i
  head := src1397
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 168098, 781284, 4063445],
    ![12303, 133307, 1205447/2, 2900058],
    ![53398/9, 577777/9, 1205447/2, 2900058],
    ![29433/8, 619609/16, 2804678/9, 4376278/3],
    ![16211/9, 717031/36, 3267341/16, 16021749/16],
    ![24292/27, 886709/81, 4028971/36, 7116809/12],
    ![73478/121, 1159562/121, 5235607/49, 7116809/12],
    ![73478/121, 1159562/121, 1908071/18, 2954821/6],
    ![73478/121, 938273/121, 4207837/49, 18114648/49],
    ![63754/121, 447806/63, 543881/8, 18114648/49],
    ![63754/121, 447806/63, 543881/8, 41472258/121],
    ![61324/121, 447806/63, 543881/8, 41472258/121],
    ![61324/121, 750881/121, 235037/4, 17695592/75],
    ![61324/121, 750881/121, 235037/4, 17695592/75],
    ![61324/121, 9260228/1681, 100415/2, 186203724/841],
    ![667406/1681, 9260228/1681, 100415/2, 186203724/841],
    ![667406/1681, 322972/63, 1130182/25, 3104824/15],
    ![667406/1681, 27166587/5476, 219708/5, 538510770/2809],
    ![954471/2738, 27166587/5476, 219708/5, 538510770/2809],
    ![462882/1369, 27166587/5476, 219708/5, 538510770/2809],
    ![459151/1369, 27166587/5476, 219708/5, 538510770/2809]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 12 385979 := by
  refine ⟨?_, rank154 7143, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1397⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free61_0
    · exact free84_0
    · exact free85_0
    · exact free74_2
    · exact free113_0
    · exact free140_0
    · exact free150_0
    · exact free120_0
    · exact free198_0
    · exact free212_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [337929640, 337203915, 336343554, 336973518, 337035968, 336473837, 336963882, 336056069, 167518851, 167678598, 167724165, 167978182, 65013774, 84196654, 65784139, 88125172, 102452891, 102308034, 125053890, 172084302, 233871985], [1020567, 1022556, 1024915, 1023188, 1023017, 1024558, 1023214, 1025703, 2276106, 2273450, 2272692, 2268467, 6184257, 4733826, 6107939, 4510867, 3851976, 3858092, 3122917, 2207620, 1581148],
  ![124143927077700, 1607155323920, 210484786500, 4600069440], 185376668400634598⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,17,13,16,12,11,11,9,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 27166587/5476, 219708/5, 538510770/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons8
end Z6969Source1571

end Merged_Z6969Pack0708

-- merged module Z6969Pack0709
section Merged_Z6969Pack0709

-- Source: Research6969.PrefixRescueDataCubicSingletons8
section Z6969Source1572
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons8
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,12⟩
  bank i := ![bank220 40111, bank227 40111, bank227 45124, bank227 57109, bank236 72277, bank252 72277, bank270 91474, bank316 146522, bank359 264035, bank342 762132, bank384 334168] i
  reserve i := ![0, 1, 2, 4, 8, 10, 16, 32, 65, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 12

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank220 40111
    · exact rank227 40111
    · exact rank227 45124
    · exact rank227 57109
    · exact rank236 72277
    · exact rank252 72277
    · exact rank270 91474
    · exact rank316 146522
    · exact rank359 264035
    · exact rank342 762132
    · exact rank384 334168
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover751⟩
    · exact ⟨_, cover752⟩
    · exact ⟨_, cover753⟩
    · exact ⟨_, cover754⟩
    · exact ⟨_, cover755⟩
    · exact ⟨_, cover756⟩
    · exact ⟨_, cover757⟩
    · exact ⟨_, cover758⟩
    · exact ⟨_, cover759⟩
    · exact ⟨_, cover760⟩
    · exact ⟨_, cover761⟩

def price : EarlyPrice := ⟨3, 12, 10, 90/100, 80/100, ![3560312594244, 622522220288, 14061266170, 2343564930], 8470967042284767⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5692/43, 185144/43, 584976/43, 2005008/43] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons8
end Z6969Source1572

-- Source: Research6969.PrefixNearSavedCubicSingletons8
section Z6969Source1573
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons8
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4961,132,4305,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons8.plan Lower6960.Prefix6969RescueData.CubicSingletons8.plan Lower6960.Prefix6969RescueData.CubicSingletons8.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 12 12 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons8.plan, Lower6960.Prefix6969MainCases.CubicSingletons8.price, Lower6960.Prefix6969MainCases.CubicSingletons8.valid, Lower6960.Prefix6969MainCases.CubicSingletons8.priced, Lower6960.Prefix6969MainCases.CubicSingletons8.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons8.plan, Lower6960.Prefix6969RescueData.CubicSingletons8.price, Lower6960.Prefix6969RescueData.CubicSingletons8.sources, Lower6960.Prefix6969RescueData.CubicSingletons8.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 224909797908138785 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons8
end Z6969Source1573

-- Source: Research6969.PrefixMainDataCubicSingletons9
section Z6969Source1574
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.CubicSingletons9
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank24 1838, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank84 5564, bank85 2903, bank74 6544, bank113 3716, bank140 3997, bank150 6517, bank120 36262, bank198 9780, bank212 10770, bank183 54742, bank174 148759, bank169 292467] i
  head := src1398
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 167828, 779844, 4049675],
    ![12303, 132497, 1198157/2, 2863518],
    ![53398/9, 574267/9, 1198157/2, 2863518],
    ![29433/8, 615739/16, 2787218/9, 4321138/3],
    ![16211/9, 712801/36, 3247991/16, 15819879/16],
    ![24292/27, 881939/81, 4007281/36, 7027139/12],
    ![73478/121, 1154702/121, 5213917/49, 7027139/12],
    ![73478/121, 1154702/121, 1896101/18, 2917591/6],
    ![73478/121, 931883/121, 4179487/49, 17886408/49],
    ![63754/121, 3118982/441, 543881/8, 17886408/49],
    ![63754/121, 3118982/441, 543881/8, 40949718/121],
    ![61324/121, 3118982/441, 543881/8, 40949718/121],
    ![61324/121, 745751/121, 235037/4, 17472632/75],
    ![61324/121, 745751/121, 235037/4, 17472632/75],
    ![61324/121, 9199388/1681, 100415/2, 183857604/841],
    ![667406/1681, 9199388/1681, 100415/2, 183857604/841],
    ![667406/1681, 2246284/441, 3368966/75, 3065704/15],
    ![667406/1681, 26985777/5476, 219708/5, 531725670/2809],
    ![954471/2738, 26985777/5476, 219708/5, 531725670/2809],
    ![462882/1369, 26985777/5476, 219708/5, 531725670/2809],
    ![459151/1369, 26985777/5476, 219708/5, 531725670/2809]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 13 385979 := by
  refine ⟨?_, rank154 7053, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1398⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free24_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free61_0
    · exact free84_0
    · exact free85_0
    · exact free74_2
    · exact free113_0
    · exact free140_0
    · exact free150_0
    · exact free120_0
    · exact free198_0
    · exact free212_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [336212980, 334985949, 334873450, 335233376, 334204762, 335120347, 335028610, 334363921, 167871179, 167963321, 168198603, 168319668, 81915988, 83851345, 65696987, 88667432, 102667053, 102888670, 124914750, 171945162, 233763552], [1025273, 1028636, 1028945, 1027958, 1030778, 1028268, 1028519, 1030341, 2270247, 2268715, 2264802, 2262789, 4869281, 4754335, 6115838, 4483516, 3842936, 3833580, 3126807, 2209298, 1582040],
  ![124086368672640, 1607272721388, 210387196800, 4572178560], 184365956974387414⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,13,13,16,12,11,11,9,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 26985777/5476, 219708/5, 531725670/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.CubicSingletons9
end Z6969Source1574

-- Source: Research6969.PrefixRescueDataCubicSingletons9
section Z6969Source1575
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons9
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,13⟩
  bank i := ![bank221 35655, bank221 40111, bank228 40111, bank227 45124, bank236 57109, bank245 72277, bank270 102908, bank303 164837, bank332 164837, bank342 762132, bank382 422931] i
  reserve i := ![0, 1, 2, 3, 6, 10, 20, 32, 40, 85, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 13

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 35655
    · exact rank221 40111
    · exact rank228 40111
    · exact rank227 45124
    · exact rank236 57109
    · exact rank245 72277
    · exact rank270 102908
    · exact rank303 164837
    · exact rank332 164837
    · exact rank342 762132
    · exact rank382 422931
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover762⟩
    · exact ⟨_, cover763⟩
    · exact ⟨_, cover764⟩
    · exact ⟨_, cover765⟩
    · exact ⟨_, cover766⟩
    · exact ⟨_, cover767⟩
    · exact ⟨_, cover768⟩
    · exact ⟨_, cover772⟩
    · exact ⟨_, cover774⟩
    · exact ⟨_, cover775⟩
    · exact ⟨_, cover776⟩

def price : EarlyPrice := ⟨3, 13, 10, 90/100, 80/100, ![3857005246920, 624949851436, 15233038100, 2343564930], 7845205704390622⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![5692/43, 462061/111, 483394/37, 1832701/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.CubicSingletons9
end Z6969Source1575

-- Source: Research6969.PrefixNearSavedCubicSingletons9
section Z6969Source1576
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedCubicSingletons9
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4928,132,4162,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.CubicSingletons9.plan Lower6960.Prefix6969RescueData.CubicSingletons9.plan Lower6960.Prefix6969RescueData.CubicSingletons9.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 13 13 385979 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons9.plan, Lower6960.Prefix6969MainCases.CubicSingletons9.price, Lower6960.Prefix6969MainCases.CubicSingletons9.valid, Lower6960.Prefix6969MainCases.CubicSingletons9.priced, Lower6960.Prefix6969MainCases.CubicSingletons9.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons9.plan, Lower6960.Prefix6969RescueData.CubicSingletons9.price, Lower6960.Prefix6969RescueData.CubicSingletons9.sources, Lower6960.Prefix6969RescueData.CubicSingletons9.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 225296833957297132 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons9
end Z6969Source1576

-- Source: Research6969.PrefixMainDataHigherHelperCases0
section Z6969Source1577
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases0
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 15, 21, 15, 25, 21, 30, 40, 40, 65, 65, 75, 75] i
  bank i := ![bank3 1490, bank10 1603, bank16 1778, bank24 1838, bank33 2191, bank42 2497, bank52 2900, bank65 3612, bank83 5597, bank93 2947, bank89 8176, bank123 3616, bank168 4492, bank122 24063, bank147 6388, bank199 9241, bank158 51722, bank211 10626, bank171 201573] i
  head := src1387
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14755, 170982, 794759, 4098931],
    ![24861/2, 283387/2, 1293113/2, 6551461/2],
    ![53228/9, 621046/9, 622300, 3161284],
    ![29433/8, 331971/8, 1001564/3, 15023812/9],
    ![5468/3, 382411/18, 864259/4, 8954617/8],
    ![36739/32, 432943/32, 1203554/9, 6235009/9],
    ![86036/121, 1007962/121, 4552042/49, 23704600/49],
    ![86036/121, 1007962/121, 4552042/49, 23704600/49],
    ![254619/484, 3644285/484, 1091415/16, 22874939/49],
    ![254619/484, 3644285/484, 1091415/16, 8684809/25],
    ![254619/484, 3644285/484, 1091415/16, 8684809/25],
    ![254619/484, 819496/121, 14345632/225, 59114368/225],
    ![254619/484, 819496/121, 14345632/225, 27538206/121],
    ![41249/100, 819496/121, 14345632/225, 27538206/121],
    ![41249/100, 610711/100, 9454240/169, 27538206/121],
    ![41249/100, 7310680/1323, 21050998/441, 85396081/400],
    ![480716/1323, 7310680/1323, 21050998/441, 85396081/400],
    ![480716/1323, 28894852/5329, 2243857/48, 213444],
    ![1826342/5329, 28894852/5329, 2243857/48, 213444]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 1 385979 := by
  refine ⟨?_, rank154 8174, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1387⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free16_0
    · exact free24_0
    · exact free33_1
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free83_1
    · exact free93_0
    · exact free89_2
    · exact free123_0
    · exact free168_0
    · exact free122_0
    · exact free147_0
    · exact free199_0
    · exact free158_0
    · exact free211_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 80/100, [358647564, 356396580, 357398106, 357571189, 357751774, 358365782, 188859074, 188866086, 188900511, 125852357, 87998777, 125917758, 76864796, 73151109, 99350135, 94048835, 109203280, 151720217, 241800140], [963775, 969945, 967200, 966725, 966230, 964547, 2005294, 2005210, 2004795, 3100592, 4517242, 3098763, 5203564, 5476876, 3982958, 4212088, 3606471, 2538837, 1515950],
  ![128352350314800, 1598590944880, 217620126000, 4295383200], 201885478218210494⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,6,6,6,9,12,9,14,15,11,12,10,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 28894852/5329, 2243857/48, 213444] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases0
end Z6969Source1577

-- Source: Research6969.PhysicalChecks060
section Z6969Source1578
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src643 : Request := ⟨⟨⟨1200,1674,355,102908⟩,51296765214720,212765123946⟩,4,3,1,385979,1⟩
theorem cover643 : PhysicalWindow.Cover (PhysicalWindow.Triangular src643) 2411 2314 [2321, 2345, 2411] := triangleCover (by decide +kernel)
def src644 : Request := ⟨⟨⟨1450,2023,436,102908⟩,91566841790464,459151377566⟩,6,3,1,385979,1⟩
theorem cover644 : PhysicalWindow.Cover (PhysicalWindow.Triangular src644) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src645 : Request := ⟨⟨⟨1750,2442,527,115771⟩,161065121873920,975196209190⟩,8,3,1,385979,1⟩
theorem cover645 : PhysicalWindow.Cover (PhysicalWindow.Triangular src645) 2411 2314 [2322, 2348, 2411] := triangleCover (by decide +kernel)
def src646 : Request := ⟨⟨⟨1750,2442,527,130242⟩,161065121873920,975196209190⟩,10,3,1,385979,1⟩
theorem cover646 : PhysicalWindow.Cover (PhysicalWindow.Triangular src646) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src647 : Request := ⟨⟨⟨2100,2930,632,146522⟩,278060332482560,2019119590628⟩,13,3,1,385979,1⟩
theorem cover647 : PhysicalWindow.Cover (PhysicalWindow.Triangular src647) 2411 2314 [2319, 2336, 2384, 2411] := triangleCover (by decide +kernel)
def src648 : Request := ⟨⟨⟨3200,4465,963,185441⟩,983050615259136,10877088344236⟩,20,3,1,385979,1⟩
theorem cover648 : PhysicalWindow.Cover (PhysicalWindow.Triangular src648) 2411 2314 [2320, 2340, 2396, 2411] := triangleCover (by decide +kernel)
def src651 : Request := ⟨⟨⟨5700,7953,1716,375939⟩,5553838907981824,109428971647179⟩,50,3,1,385979,1⟩
theorem cover651 : PhysicalWindow.Cover (PhysicalWindow.Triangular src651) 2411 2314 [2321, 2343, 2404, 2411] := triangleCover (by decide +kernel)
def src652 : Request := ⟨⟨⟨1000,1395,296,64247⟩,29722184515584,102755930405⟩,0,3,1,385979,2⟩
theorem cover652 : PhysicalWindow.Cover (PhysicalWindow.Triangular src652) 2411 2314 [2318, 2333, 2378, 2411] := triangleCover (by decide +kernel)
def src653 : Request := ⟨⟨⟨1000,1395,301,72277⟩,30103476895744,104105680031⟩,1,3,1,385979,2⟩
theorem cover653 : PhysicalWindow.Cover (PhysicalWindow.Triangular src653) 2411 2314 [2324, 2356, 2411] := triangleCover (by decide +kernel)
def src654 : Request := ⟨⟨⟨1000,1395,301,81311⟩,30103476895744,104105680031⟩,2,3,1,385979,2⟩
theorem cover654 : PhysicalWindow.Cover (PhysicalWindow.Triangular src654) 2411 2314 [2320, 2341, 2403, 2411] := triangleCover (by decide +kernel)
def src655 : Request := ⟨⟨⟨1200,1674,361,91474⟩,51955677528064,215563369662⟩,4,3,1,385979,2⟩
theorem cover655 : PhysicalWindow.Cover (PhysicalWindow.Triangular src655) 2411 2314 [2319, 2337, 2390, 2411] := triangleCover (by decide +kernel)
def src656 : Request := ⟨⟨⟨1450,2023,436,102908⟩,91566841790464,459151377566⟩,6,3,1,385979,2⟩
theorem cover656 : PhysicalWindow.Cover (PhysicalWindow.Triangular src656) 2411 2314 [2323, 2352, 2411] := triangleCover (by decide +kernel)
def src657 : Request := ⟨⟨⟨1750,2442,527,130242⟩,161065121873920,975196209190⟩,10,3,1,385979,2⟩
theorem cover657 : PhysicalWindow.Cover (PhysicalWindow.Triangular src657) 2411 2314 [2323, 2351, 2411] := triangleCover (by decide +kernel)
def src658 : Request := ⟨⟨⟨2100,2930,622,146522⟩,274699477319680,1994139134137⟩,13,3,1,385979,2⟩
theorem cover658 : PhysicalWindow.Cover (PhysicalWindow.Triangular src658) 2411 2314 [2317, 2328, 2360, 2411] := triangleCover (by decide +kernel)
def src659 : Request := ⟨⟨⟨2600,3628,783,185441⟩,527755772952576,4745819470168⟩,20,3,1,385979,2⟩
theorem cover659 : PhysicalWindow.Cover (PhysicalWindow.Triangular src659) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src661 : Request := ⟨⟨⟨3200,4465,963,208621⟩,983050615259136,10877088344236⟩,25,3,1,385979,2⟩
theorem cover661 : PhysicalWindow.Cover (PhysicalWindow.Triangular src661) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1578

-- Source: Research6969.PrefixRescueDataHigherHelperCases0
section Z6969Source1579
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases0
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,3,1,1⟩
  bank i := ![bank221 64247, bank221 72277, bank220 91474, bank226 102908, bank236 102908, bank245 130242, bank245 115771, bank252 146522, bank303 185441, bank345 375939] i
  reserve i := ![0, 1, 2, 4, 6, 10, 8, 13, 20, 50] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 1

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 64247
    · exact rank221 72277
    · exact rank220 91474
    · exact rank226 102908
    · exact rank236 102908
    · exact rank245 130242
    · exact rank245 115771
    · exact rank252 146522
    · exact rank303 185441
    · exact rank345 375939
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover640⟩
    · exact ⟨_, cover641⟩
    · exact ⟨_, cover642⟩
    · exact ⟨_, cover643⟩
    · exact ⟨_, cover644⟩
    · exact ⟨_, cover646⟩
    · exact ⟨_, cover645⟩
    · exact ⟨_, cover647⟩
    · exact ⟨_, cover648⟩
    · exact ⟨_, cover651⟩

def price : EarlyPrice := ⟨3, 1, 9, 100/100, 80/100, ![146351924883, 295131519216, 668033652, 1336065588], 10481771080117152⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![3795/17, 7405, 22270, 125313/17] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases0
end Z6969Source1579

-- Source: Research6969.PrefixNearSavedHigherHelperCases0
section Z6969Source1580
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases0
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,5422,223,7405,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases0.plan Lower6960.Prefix6969RescueData.HigherHelperCases0.plan Lower6960.Prefix6969RescueData.HigherHelperCases0.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 1 1 385979 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases0.plan, Lower6960.Prefix6969MainCases.HigherHelperCases0.price, Lower6960.Prefix6969MainCases.HigherHelperCases0.valid, Lower6960.Prefix6969MainCases.HigherHelperCases0.priced, Lower6960.Prefix6969MainCases.HigherHelperCases0.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases0.plan, Lower6960.Prefix6969RescueData.HigherHelperCases0.price, Lower6960.Prefix6969RescueData.HigherHelperCases0.sources, Lower6960.Prefix6969RescueData.HigherHelperCases0.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 214673921804481624 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases0
end Z6969Source1580

-- Source: Research6969.PrefixMainDataHigherHelperCases1
section Z6969Source1581
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases1
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 65, 75, 75] i
  bank i := ![bank3 1490, bank10 1603, bank16 1778, bank24 1838, bank28 2005, bank33 2191, bank42 2497, bank52 2900, bank65 3612, bank83 5597, bank83 2752, bank123 3616, bank122 24063, bank147 6388, bank199 9241, bank158 51722, bank211 10626, bank171 201573] i
  head := src1388
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14880, 170369, 791781, 4020327],
    ![24861/2, 281641/2, 2570221/4, 12947431/4],
    ![53228/9, 617263/9, 622300, 3161284],
    ![29433/8, 659771/16, 2985874/9, 14845526/9],
    ![62542/25, 712392/25, 411025/2, 16194385/16],
    ![5468/3, 380083/18, 411025/2, 16194385/16],
    ![36739/32, 107581/8, 1203554/9, 6235009/9],
    ![86036/121, 1001851/121, 4524591/49, 23423300/49],
    ![86036/121, 1001851/121, 4524591/49, 23423300/49],
    ![254619/484, 3627407/484, 1091415/16, 45206969/98],
    ![254619/484, 3627407/484, 1091415/16, 11113952/25],
    ![254619/484, 813676/121, 4747216/75, 58412864/225],
    ![41249/100, 813676/121, 4747216/75, 58412864/225],
    ![41249/100, 1213371/200, 2727129/49, 206383504/841],
    ![41249/100, 7261210/1323, 21050998/441, 223918671/1058],
    ![480716/1323, 7261210/1323, 21050998/441, 223918671/1058],
    ![480716/1323, 28702016/5329, 2243857/48, 223918671/1058],
    ![1826342/5329, 28702016/5329, 2243857/48, 223918671/1058]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 3 2 385979 := by
  refine ⟨?_, rank154 8077, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1388⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free16_0
    · exact free24_0
    · exact free28_0
    · exact free33_1
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free83_1
    · exact free83_0
    · exact free123_0
    · exact free122_0
    · exact free147_0
    · exact free199_0
    · exact free158_0
    · exact free211_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 80/100, [357350668, 357282902, 357279163, 357133150, 355390221, 356594952, 356888435, 162501166, 162477607, 162381925, 162428242, 78776582, 78759359, 98672379, 89848447, 103831948, 151567728, 241681304], [967330, 967516, 967526, 967926, 972704, 969401, 968597, 2359550, 2359942, 2361533, 2360763, 5071502, 5072691, 4011569, 4423948, 3793760, 2541373, 1516927],
  ![128289269789280, 1598719298596, 217513173600, 4513579560], 200602596187613149⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,7,7,7,7,14,14,11,12,11,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 28702016/5329, 2243857/48, 223918671/1058] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases1
end Z6969Source1581

-- Source: Research6969.PrefixRescueDataHigherHelperCases1
section Z6969Source1582
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases1
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,3⟩
  bank i := ![bank220 64247, bank221 72277, bank221 81311, bank227 91474, bank245 130242, bank236 102908, bank251 146522, bank270 185441, bank303 208621, bank332 297039, bank382 762132] i
  reserve i := ![0, 1, 2, 4, 10, 6, 13, 20, 25, 40, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 2

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank220 64247
    · exact rank221 72277
    · exact rank221 81311
    · exact rank227 91474
    · exact rank245 130242
    · exact rank236 102908
    · exact rank251 146522
    · exact rank270 185441
    · exact rank303 208621
    · exact rank332 297039
    · exact rank382 762132
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover652⟩
    · exact ⟨_, cover653⟩
    · exact ⟨_, cover654⟩
    · exact ⟨_, cover655⟩
    · exact ⟨_, cover657⟩
    · exact ⟨_, cover656⟩
    · exact ⟨_, cover658⟩
    · exact ⟨_, cover659⟩
    · exact ⟨_, cover661⟩
    · exact ⟨_, cover663⟩
    · exact ⟨_, cover664⟩

def price : EarlyPrice := ⟨3, 3, 10, 95/100, 80/100, ![890081006556, 606170783945, 3515327830, 2343564930], 13257665800344225⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![19973/111, 257054/37, 776085/37, 762132/37] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases1
end Z6969Source1582

-- Source: Research6969.PrefixNearSavedHigherHelperCases1
section Z6969Source1583
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases1
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,5386,179,6947,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases1.plan Lower6960.Prefix6969RescueData.HigherHelperCases1.plan Lower6960.Prefix6969RescueData.HigherHelperCases1.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 3 2 3 385979 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases1.plan, Lower6960.Prefix6969MainCases.HigherHelperCases1.price, Lower6960.Prefix6969MainCases.HigherHelperCases1.valid, Lower6960.Prefix6969MainCases.HigherHelperCases1.priced, Lower6960.Prefix6969MainCases.HigherHelperCases1.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases1.plan, Lower6960.Prefix6969RescueData.HigherHelperCases1.price, Lower6960.Prefix6969RescueData.HigherHelperCases1.sources, Lower6960.Prefix6969RescueData.HigherHelperCases1.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 222373570226656575 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases1
end Z6969Source1583

end Merged_Z6969Pack0709

-- merged module Z6969Pack0710
section Merged_Z6969Pack0710

-- Source: Research6969.PrefixNearSelect3
section Z6969Source1584
set_option autoImplicit true
namespace Lower6960.Prefix6969Early
set_option maxHeartbeats 8000000

theorem nearChoose3 (j : Fin 56) (ok : UniformAllowed 3 (seed j)) :
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧ w≤385979 ∧ ∃ c : NearCase 3 l u w, c.uniform := by
  fin_cases j
  · refine ⟨1, 1, 385979, by decide, by decide, by decide, NearSavedHigherHelperCases0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases0.fee_exact]; decide +kernel
  · refine ⟨2, 3, 385979, by decide, by decide, by decide, NearSavedHigherHelperCases1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases1.fee_exact]; decide +kernel
  · refine ⟨2, 3, 385979, by decide, by decide, by decide, NearSavedHigherHelperCases1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases1.fee_exact]; decide +kernel
  · refine ⟨4, 4, 385979, by decide, by decide, by decide, NearSavedCubicSingletons0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons0.fee_exact]; decide +kernel
  · refine ⟨5, 5, 385979, by decide, by decide, by decide, NearSavedCubicSingletons1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons1.fee_exact]; decide +kernel
  · refine ⟨6, 6, 385979, by decide, by decide, by decide, NearSavedCubicSingletons2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons2.fee_exact]; decide +kernel
  · refine ⟨7, 7, 385979, by decide, by decide, by decide, NearSavedCubicSingletons3.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons3.fee_exact]; decide +kernel
  · refine ⟨8, 8, 385979, by decide, by decide, by decide, NearSavedCubicSingletons4.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons4.fee_exact]; decide +kernel
  · refine ⟨9, 9, 385979, by decide, by decide, by decide, NearSavedCubicSingletons5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons5.fee_exact]; decide +kernel
  · refine ⟨10, 10, 385979, by decide, by decide, by decide, NearSavedCubicSingletons6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons6.fee_exact]; decide +kernel
  · refine ⟨11, 11, 385979, by decide, by decide, by decide, NearSavedCubicSingletons7.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons7.fee_exact]; decide +kernel
  · refine ⟨12, 12, 385979, by decide, by decide, by decide, NearSavedCubicSingletons8.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons8.fee_exact]; decide +kernel
  · refine ⟨13, 13, 385979, by decide, by decide, by decide, NearSavedCubicSingletons9.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons9.fee_exact]; decide +kernel
  · refine ⟨14, 14, 385979, by decide, by decide, by decide, NearSavedCubicSingletons10.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons10.fee_exact]; decide +kernel
  · refine ⟨15, 15, 385979, by decide, by decide, by decide, NearSavedCubicSingletons11.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons11.fee_exact]; decide +kernel
  · refine ⟨16, 16, 385979, by decide, by decide, by decide, NearSavedCubicSingletons12.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons12.fee_exact]; decide +kernel
  · refine ⟨17, 17, 385979, by decide, by decide, by decide, NearSavedCubicSingletons13.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons13.fee_exact]; decide +kernel
  · refine ⟨18, 18, 385979, by decide, by decide, by decide, NearSavedCubicSingletons14.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons14.fee_exact]; decide +kernel
  · refine ⟨19, 19, 385979, by decide, by decide, by decide, NearSavedCubicSingletons15.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons15.fee_exact]; decide +kernel
  · refine ⟨20, 20, 385979, by decide, by decide, by decide, NearSavedCubicSingletons16.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons16.fee_exact]; decide +kernel
  · refine ⟨21, 21, 385979, by decide, by decide, by decide, NearSavedCubicSingletons17.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons17.fee_exact]; decide +kernel
  · refine ⟨22, 22, 385979, by decide, by decide, by decide, NearSavedCubicSingletons18.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons18.fee_exact]; decide +kernel
  · refine ⟨23, 23, 385979, by decide, by decide, by decide, NearSavedCubicSingletons19.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons19.fee_exact]; decide +kernel
  · refine ⟨24, 24, 385979, by decide, by decide, by decide, NearSavedCubicSingletons20.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons20.fee_exact]; decide +kernel
  · refine ⟨25, 25, 385979, by decide, by decide, by decide, NearSavedCubicSingletons21.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons21.fee_exact]; decide +kernel
  · refine ⟨26, 26, 385979, by decide, by decide, by decide, NearSavedCubicSingletons22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons22.fee_exact]; decide +kernel
  · refine ⟨27, 27, 385979, by decide, by decide, by decide, NearSavedCubicSingletons23.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons23.fee_exact]; decide +kernel
  · refine ⟨28, 28, 385979, by decide, by decide, by decide, NearSavedCubicSingletons24.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons24.fee_exact]; decide +kernel
  · refine ⟨29, 29, 385979, by decide, by decide, by decide, NearSavedCubicSingletons25.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons25.fee_exact]; decide +kernel
  · refine ⟨30, 30, 385979, by decide, by decide, by decide, NearSavedCubicSingletons26.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons26.fee_exact]; decide +kernel
  · refine ⟨31, 31, 385979, by decide, by decide, by decide, NearSavedCubicSingletons27.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons27.fee_exact]; decide +kernel
  · refine ⟨32, 32, 385979, by decide, by decide, by decide, NearSavedCubicSingletons28.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons28.fee_exact]; decide +kernel
  · refine ⟨33, 33, 385979, by decide, by decide, by decide, NearSavedCubicSingletons29.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons29.fee_exact]; decide +kernel
  · refine ⟨34, 34, 385979, by decide, by decide, by decide, NearSavedCubicSingletons30.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons30.fee_exact]; decide +kernel
  · refine ⟨35, 35, 385979, by decide, by decide, by decide, NearSavedCubicSingletons31.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons31.fee_exact]; decide +kernel
  · refine ⟨36, 36, 385979, by decide, by decide, by decide, NearSavedCubicSingletons32.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons32.fee_exact]; decide +kernel
  · refine ⟨37, 37, 385979, by decide, by decide, by decide, NearSavedCubicSingletons33.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons33.fee_exact]; decide +kernel
  · refine ⟨38, 38, 385979, by decide, by decide, by decide, NearSavedCubicSingletons34.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons34.fee_exact]; decide +kernel
  · refine ⟨39, 39, 385979, by decide, by decide, by decide, NearSavedCubicSingletons35.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons35.fee_exact]; decide +kernel
  · refine ⟨40, 40, 385979, by decide, by decide, by decide, NearSavedCubicSingletons36.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons36.fee_exact]; decide +kernel
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide
  · exfalso; revert ok; decide

end Lower6960.Prefix6969Early
end Z6969Source1584

-- Source: Research6969.PrefixMainDataHigherHelperCases2
section Z6969Source1585
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases2
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 7, 10, 15, 13, 21, 21, 65, 65, 75] i
  bank i := ![bank3 1490, bank10 1603, bank24 1838, bank33 2191, bank42 2497, bank52 2900, bank65 3612, bank83 2752, bank83 5597, bank123 3616, bank198 9780, bank158 51722, bank171 201573] i
  head := src1544
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15074, 170166, 789833, 3896382],
    ![24861/2, 271795/2, 1239983/2, 6035295/2],
    ![29433/8, 318125/8, 2879756/9, 4613380/3],
    ![5468/3, 366955/18, 829483/4, 8249115/8],
    ![36739/32, 415555/32, 1203554/9, 6235009/9],
    ![86036/121, 967390/121, 4369790/49, 21837000/49],
    ![86036/121, 967390/121, 4369790/49, 21837000/49],
    ![86036/121, 967390/121, 4369790/49, 2072256/5],
    ![254619/484, 3213200/441, 1091415/16, 2072256/5],
    ![254619/484, 780856/121, 13655264/225, 3630464/15],
    ![658228/1323, 2323240/441, 696668/15, 10627600/49],
    ![480716/1323, 2323240/441, 696668/15, 10627600/49],
    ![1826342/5329, 2323240/441, 696668/15, 10627600/49]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 4 1 514639 := by
  refine ⟨?_, rank154 7530, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1544⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free24_0
    · exact free33_1
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free83_0
    · exact free83_1
    · exact free123_0
    · exact free198_0
    · exact free158_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [350218762, 348129386, 348903874, 349256091, 348344927, 149040181, 148902840, 133799260, 131871722, 108981331, 108615557, 150710995, 241021927], [986880, 992607, 990484, 989519, 992016, 2583406, 2585690, 2906531, 2948801, 3614178, 3626878, 2555620, 1522350],
  ![127939259290140, 1599431479748, 216919734300, 3698600580], 196328885810483429⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,7,7,8,8,10,10,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 2323240/441, 696668/15, 10627600/49] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases2
end Z6969Source1585

-- Source: Research6969.PhysicalChecks089
section Z6969Source1586
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1206 : Request := ⟨⟨⟨560,781,169,25043⟩,5316921262080,10299257375⟩,0,4,1,514639,1⟩
theorem cover1206 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1206) 2411 2314 [2329, 2379, 2411] := triangleCover (by decide +kernel)
def src1207 : Request := ⟨⟨⟨560,781,169,28173⟩,5316921262080,10299257375⟩,1,4,1,514639,1⟩
theorem cover1207 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1207) 2411 2314 [2320, 2342, 2411] := triangleCover (by decide +kernel)
def src1208 : Request := ⟨⟨⟨690,962,208,28173⟩,9921631092736,23645774460⟩,2,4,1,514639,1⟩
theorem cover1208 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1208) 2411 2314 [2318, 2333, 2379, 2411] := triangleCover (by decide +kernel)
def src1209 : Request := ⟨⟨⟨560,781,169,45124⟩,5316921262080,10299257375⟩,3,4,1,514639,1⟩
theorem cover1209 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1209) 2411 2314 [2329, 2379, 2411] := triangleCover (by decide +kernel)
def src1210 : Request := ⟨⟨⟨690,962,208,31694⟩,9921631092736,23645774460⟩,3,4,1,514639,1⟩
theorem cover1210 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1210) 2411 2314 [2318, 2333, 2380, 2411] := triangleCover (by decide +kernel)
def src1211 : Request := ⟨⟨⟨825,1151,248,40111⟩,16903818182656,48256472894⟩,6,4,1,514639,1⟩
theorem cover1211 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1211) 2411 2314 [2319, 2337, 2392, 2411] := triangleCover (by decide +kernel)
def src1212 : Request := ⟨⟨⟨1200,1674,368,45124⟩,52718727069696,218807905514⟩,10,4,1,514639,1⟩
theorem cover1212 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1212) 2411 2314 [2319, 2336, 2386, 2411] := triangleCover (by decide +kernel)
def src1213 : Request := ⟨⟨⟨1450,2023,445,50764⟩,92998964346880,466511127281⟩,13,4,1,514639,1⟩
theorem cover1213 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1213) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src1214 : Request := ⟨⟨⟨2100,2930,632,81311⟩,278060332482560,2019119590628⟩,25,4,1,514639,1⟩
theorem cover1214 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1214) 2411 2314 [2323, 2351, 2411] := triangleCover (by decide +kernel)
def src1217 : Request := ⟨⟨⟨4800,6697,1474,164837⟩,3367547627110400,55891290082931⟩,65,4,1,514639,1⟩
theorem cover1217 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1217) 2411 2314 [2319, 2335, 2379, 2411] := triangleCover (by decide +kernel)
def src1218 : Request := ⟨⟨⟨6900,9626,2118,264035⟩,9997036108906496,238415548481346⟩,110,4,1,514639,1⟩
theorem cover1218 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1218) 2411 2314 [2316, 2325, 2349, 2411] := triangleCover (by decide +kernel)
def src1219 : Request := ⟨⟨⟨690,963,212,22261⟩,10065769922560,24078187611⟩,0,4,1,514639,2⟩
theorem cover1219 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1219) 2411 2314 [2320, 2341, 2405, 2411] := triangleCover (by decide +kernel)
def src1220 : Request := ⟨⟨⟨690,963,208,25043⟩,9921631092736,23724874690⟩,1,4,1,514639,2⟩
theorem cover1220 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1220) 2411 2314 [2322, 2350, 2411] := triangleCover (by decide +kernel)
def src1221 : Request := ⟨⟨⟨690,962,208,31694⟩,9921631092736,23645774460⟩,3,4,1,514639,2⟩
theorem cover1221 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1221) 2411 2314 [2325, 2362, 2411] := triangleCover (by decide +kernel)
def src1222 : Request := ⟨⟨⟨1000,1395,307,40111⟩,30557599170560,105715278267⟩,8,4,1,514639,2⟩
theorem cover1222 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1222) 2411 2314 [2318, 2332, 2373, 2411] := triangleCover (by decide +kernel)
def src1223 : Request := ⟨⟨⟨1450,2023,436,50764⟩,91566841790464,459151377566⟩,13,4,1,514639,2⟩
theorem cover1223 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1223) 2411 2314 [2318, 2332, 2373, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1586

-- Source: Research6969.PrefixRescueDataHigherHelperCases2
section Z6969Source1587
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases2
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,1⟩
  bank i := ![bank155 25043, bank155 28173, bank192 28173, bank192 31694, bank203 40111, bank155 45124, bank228 45124, bank237 50764, bank252 81311, bank329 164837, bank356 264035] i
  reserve i := ![0, 1, 2, 3, 6, 3, 10, 13, 25, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514639
  seedFloor := 1

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank155 25043
    · exact rank155 28173
    · exact rank192 28173
    · exact rank192 31694
    · exact rank203 40111
    · exact rank155 45124
    · exact rank228 45124
    · exact rank237 50764
    · exact rank252 81311
    · exact rank329 164837
    · exact rank356 264035
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1206⟩
    · exact ⟨_, cover1207⟩
    · exact ⟨_, cover1208⟩
    · exact ⟨_, cover1210⟩
    · exact ⟨_, cover1211⟩
    · exact ⟨_, cover1209⟩
    · exact ⟨_, cover1212⟩
    · exact ⟨_, cover1213⟩
    · exact ⟨_, cover1214⟩
    · exact ⟨_, cover1217⟩
    · exact ⟨_, cover1218⟩

def price : EarlyPrice := ⟨4, 1, 10, 95/100, 80/100, ![102788033395, 311285357851, 981624731, 2473580430], 2746011305248412⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![15980/111, 266153/111, 1065766/111, 264035/111] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases2
end Z6969Source1587

-- Source: Research6969.PrefixNearSavedHigherHelperCases2
section Z6969Source1588
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases2
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,5268,143,2397,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases2.plan Lower6960.Prefix6969RescueData.HigherHelperCases2.plan Lower6960.Prefix6969RescueData.HigherHelperCases2.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 4 1 1 514639 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases2.plan, Lower6960.Prefix6969MainCases.HigherHelperCases2.price, Lower6960.Prefix6969MainCases.HigherHelperCases2.valid, Lower6960.Prefix6969MainCases.HigherHelperCases2.priced, Lower6960.Prefix6969MainCases.HigherHelperCases2.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases2.plan, Lower6960.Prefix6969RescueData.HigherHelperCases2.price, Lower6960.Prefix6969RescueData.HigherHelperCases2.sources, Lower6960.Prefix6969RescueData.HigherHelperCases2.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 200516303951982622 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases2
end Z6969Source1588

-- Source: Research6969.PrefixMainDataHigherHelperCases3
section Z6969Source1589
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases3
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 7, 10, 15, 13, 21, 21, 65, 65, 75] i
  bank i := ![bank3 1490, bank10 1603, bank24 1838, bank33 2191, bank42 2497, bank52 2900, bank65 3612, bank83 2752, bank83 5597, bank123 3616, bank198 9780, bank158 51722, bank171 201573] i
  head := src1545
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15074, 169920, 788439, 3882934],
    ![24861/2, 270319/2, 616609, 2984786],
    ![29433/8, 158181/4, 954616/3, 13689424/9],
    ![5468/3, 364987/18, 825055/4, 2039821/2],
    ![36739/32, 413341/32, 1203554/9, 6235009/9],
    ![86036/121, 962224/121, 4346584/49, 440800],
    ![86036/121, 962224/121, 4346584/49, 440800],
    ![86036/121, 962224/121, 4346584/49, 10248448/25],
    ![254619/484, 3198932/441, 1091415/16, 10248448/25],
    ![254619/484, 775936/121, 60568, 53863936/225],
    ![658228/1323, 6930032/1323, 31173104/675, 9712192/45],
    ![480716/1323, 6930032/1323, 31173104/675, 9712192/45],
    ![1826342/5329, 6930032/1323, 31173104/675, 9712192/45]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 4 2 514639 := by
  refine ⟨?_, rank154 7448, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1545⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free24_0
    · exact free33_1
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free83_0
    · exact free83_1
    · exact free123_0
    · exact free198_0
    · exact free158_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [348597622, 348141080, 348124473, 347963134, 348170671, 142394489, 139839785, 137715773, 135693494, 108451132, 107701110, 150272615, 240687471], [991324, 992575, 992621, 993063, 992494, 2718041, 2774064, 2820643, 2864991, 3632587, 3658629, 2562910, 1525100],
  ![127761723356220, 1599792881244, 216618723900, 3730979460], 195255361188461142⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,8,8,8,8,10,10,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 6930032/1323, 31173104/675, 9712192/45] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases3
end Z6969Source1589

-- Source: Research6969.PhysicalChecks090
section Z6969Source1590
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1224 : Request := ⟨⟨⟨1750,2441,537,64247⟩,163381988556800,988269431527⟩,20,4,1,514639,2⟩
theorem cover1224 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1224) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src1225 : Request := ⟨⟨⟨1750,2441,537,130242⟩,163381988556800,988269431527⟩,32,4,1,514639,2⟩
theorem cover1225 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1225) 2411 2314 [2321, 2343, 2406, 2411] := triangleCover (by decide +kernel)
def src1227 : Request := ⟨⟨⟨3950,5511,1189,130242⟩,1848744952463360,25241028863276⟩,50,4,1,514639,2⟩
theorem cover1227 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1227) 2411 2314 [2317, 2329, 2362, 2411] := triangleCover (by decide +kernel)
def src1229 : Request := ⟨⟨⟨5700,7952,1716,208621⟩,5553838907981824,109384694947514⟩,85,4,1,514639,2⟩
theorem cover1229 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1229) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
def src1230 : Request := ⟨⟨⟨10000,13952,3010,334168⟩,29974681586237440,1035886358306578⟩,145,4,1,514639,2⟩
theorem cover1230 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1230) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src1231 : Request := ⟨⟨⟨560,781,169,22261⟩,5316921262080,10299257375⟩,0,4,1,514639,4⟩
theorem cover1231 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1231) 2411 2314 [2325, 2363, 2411] := triangleCover (by decide +kernel)
def src1232 : Request := ⟨⟨⟨560,781,172,25043⟩,5388141854720,10440670587⟩,1,4,1,514639,4⟩
theorem cover1232 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1232) 2411 2314 [2320, 2342, 2411] := triangleCover (by decide +kernel)
def src1233 : Request := ⟨⟨⟨690,962,212,28173⟩,10065769922560,23997864317⟩,3,4,1,514639,4⟩
theorem cover1233 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1233) 2411 2314 [2319, 2337, 2392, 2411] := triangleCover (by decide +kernel)
def src1234 : Request := ⟨⟨⟨1000,1395,307,45124⟩,30557599170560,105715278267⟩,10,4,1,514639,4⟩
theorem cover1234 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1234) 2411 2314 [2321, 2345, 2411] := triangleCover (by decide +kernel)
def src1235 : Request := ⟨⟨⟨1750,2441,527,64247⟩,161065121873920,973912060302⟩,20,4,1,514639,4⟩
theorem cover1235 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1235) 2411 2314 [2326, 2363, 2411] := triangleCover (by decide +kernel)
def src1236 : Request := ⟨⟨⟨2100,2929,645,91474⟩,282396798484480,2049139102608⟩,32,4,1,514639,4⟩
theorem cover1236 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1236) 2411 2314 [2319, 2336, 2384, 2411] := triangleCover (by decide +kernel)
def src1238 : Request := ⟨⟨⟨2100,2929,645,375939⟩,282396798484480,2049139102608⟩,50,4,1,514639,4⟩
theorem cover1238 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1238) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src1240 : Request := ⟨⟨⟨4800,6697,1474,146522⟩,3367547627110400,55891290082931⟩,65,4,1,514639,4⟩
theorem cover1240 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1240) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src1241 : Request := ⟨⟨⟨3200,4463,982,964572⟩,997767489781760,11028049925768⟩,85,4,1,514639,4⟩
theorem cover1241 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1241) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src1242 : Request := ⟨⟨⟨10000,13950,3070,422931⟩,30428373265940480,1051468979452278⟩,190,4,1,514639,4⟩
theorem cover1242 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1242) 2411 2314 [2316, 2325, 2349, 2411] := triangleCover (by decide +kernel)
def src1243 : Request := ⟨⟨⟨560,781,172,17590⟩,5388141854720,10440670587⟩,0,4,1,514639,9⟩
theorem cover1243 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1243) 2411 2314 [2319, 2338, 2398, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1590

-- Source: Research6969.PrefixRescueDataHigherHelperCases3
section Z6969Source1591
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases3
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,4,1,3⟩
  bank i := ![bank196 22261, bank195 25043, bank192 31694, bank222 40111, bank236 50764, bank242 64247, bank242 130242, bank312 130242, bank342 208621, bank379 334168] i
  reserve i := ![0, 1, 3, 8, 13, 20, 32, 50, 85, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514639
  seedFloor := 2

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank196 22261
    · exact rank195 25043
    · exact rank192 31694
    · exact rank222 40111
    · exact rank236 50764
    · exact rank242 64247
    · exact rank242 130242
    · exact rank312 130242
    · exact rank342 208621
    · exact rank379 334168
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1219⟩
    · exact ⟨_, cover1220⟩
    · exact ⟨_, cover1221⟩
    · exact ⟨_, cover1222⟩
    · exact ⟨_, cover1223⟩
    · exact ⟨_, cover1224⟩
    · exact ⟨_, cover1225⟩
    · exact ⟨_, cover1227⟩
    · exact ⟨_, cover1229⟩
    · exact ⟨_, cover1230⟩

def price : EarlyPrice := ⟨4, 3, 9, 95/100, 80/100, ![390269126344, 403048770466, 3515327830, 3515333850], 2788718958768361⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![4052/33, 171599/73, 689264/73, 501252/73] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases3
end Z6969Source1591

-- Source: Research6969.PrefixNearSavedHigherHelperCases3
section Z6969Source1592
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases3
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,5238,122,2350,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases3.plan Lower6960.Prefix6969RescueData.HigherHelperCases3.plan Lower6960.Prefix6969RescueData.HigherHelperCases3.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 4 2 3 514639 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases3.plan, Lower6960.Prefix6969MainCases.HigherHelperCases3.price, Lower6960.Prefix6969MainCases.HigherHelperCases3.valid, Lower6960.Prefix6969MainCases.HigherHelperCases3.priced, Lower6960.Prefix6969MainCases.HigherHelperCases3.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases3.plan, Lower6960.Prefix6969RescueData.HigherHelperCases3.price, Lower6960.Prefix6969RescueData.HigherHelperCases3.sources, Lower6960.Prefix6969RescueData.HigherHelperCases3.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 203629184383385635 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases3
end Z6969Source1592

-- Source: Research6969.PrefixMainDataHigherHelperCases4
section Z6969Source1593
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases4
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 7, 10, 15, 15, 21, 30, 65, 65, 75] i
  bank i := ![bank3 1490, bank10 1603, bank24 1838, bank33 2191, bank42 2497, bank52 2900, bank65 3612, bank93 2947, bank83 5597, bank139 4862, bank158 51722, bank198 9780, bank171 201573] i
  head := src1546
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15147, 169653, 786151, 3816318],
    ![24861/2, 267385/2, 2439541/4, 11677855/4],
    ![29433/8, 625715/16, 2832226/9, 13389830/9],
    ![5468/3, 361075/18, 816253/4, 15961435/16],
    ![36739/32, 102235/8, 1203554/9, 6235009/9],
    ![86036/121, 951955/121, 4300455/49, 21126500/49],
    ![86036/121, 951955/121, 4300455/49, 21126500/49],
    ![86036/121, 951955/121, 4300455/49, 8684809/25],
    ![254619/484, 3170570/441, 1091415/16, 8684809/25],
    ![254619/484, 186101/30, 8343014/147, 5909761/25],
    ![480716/1323, 186101/30, 8343014/147, 5909761/25],
    ![480716/1323, 6851140/1323, 1232854/27, 1899928/9],
    ![1826342/5329, 6851140/1323, 1232854/27, 1899928/9]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 4 4 514639 := by
  refine ⟨?_, rank154 7285, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1546⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free24_0
    · exact free33_1
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free93_0
    · exact free83_1
    · exact free139_0
    · exact free158_0
    · exact free198_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [346122671, 345270877, 345430546, 345152583, 345873125, 149155329, 147762750, 95114114, 116412957, 107506374, 106989428, 149401200, 240022637], [998108, 1000443, 1000005, 1000767, 998792, 2581491, 2604649, 4161779, 3364520, 3665391, 3683340, 2577402, 1530567],
  ![127408816172340, 1600511028508, 216020373300, 3756178560], 193551644602415673⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,7,7,11,9,10,10,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 6851140/1323, 1232854/27, 1899928/9] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases4
end Z6969Source1593

-- Source: Research6969.PrefixRescueDataHigherHelperCases4
section Z6969Source1594
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases4
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,4,1,8⟩
  bank i := ![bank155 22261, bank156 25043, bank193 28173, bank222 45124, bank241 64247, bank249 91474, bank329 146522, bank249 375939, bank297 964572, bank377 422931] i
  reserve i := ![0, 1, 3, 10, 20, 32, 65, 50, 85, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514639
  seedFloor := 4

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank155 22261
    · exact rank156 25043
    · exact rank193 28173
    · exact rank222 45124
    · exact rank241 64247
    · exact rank249 91474
    · exact rank329 146522
    · exact rank249 375939
    · exact rank297 964572
    · exact rank377 422931
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1231⟩
    · exact ⟨_, cover1232⟩
    · exact ⟨_, cover1233⟩
    · exact ⟨_, cover1234⟩
    · exact ⟨_, cover1235⟩
    · exact ⟨_, cover1236⟩
    · exact ⟨_, cover1240⟩
    · exact ⟨_, cover1238⟩
    · exact ⟨_, cover1241⟩
    · exact ⟨_, cover1242⟩

def price : EarlyPrice := ⟨4, 8, 9, 95/100, 80/100, ![3004010949912, 1137350208646, 9561042220, 3585406950], 5130861881661200⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![7409/86, 447491/191, 1803324/191, 3383448/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases4
end Z6969Source1594

-- Source: Research6969.PrefixNearSavedHigherHelperCases4
section Z6969Source1595
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases4
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,5178,86,2342,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases4.plan Lower6960.Prefix6969RescueData.HigherHelperCases4.plan Lower6960.Prefix6969RescueData.HigherHelperCases4.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 4 4 8 514639 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases4.plan, Lower6960.Prefix6969MainCases.HigherHelperCases4.price, Lower6960.Prefix6969MainCases.HigherHelperCases4.valid, Lower6960.Prefix6969MainCases.HigherHelperCases4.priced, Lower6960.Prefix6969MainCases.HigherHelperCases4.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases4.plan, Lower6960.Prefix6969RescueData.HigherHelperCases4.price, Lower6960.Prefix6969RescueData.HigherHelperCases4.sources, Lower6960.Prefix6969RescueData.HigherHelperCases4.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 213639140291148959 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases4
end Z6969Source1595

end Merged_Z6969Pack0710

-- merged module Z6969Pack0711
section Merged_Z6969Pack0711

-- Source: Research6969.PrefixMainDataHigherHelperCases5
section Z6969Source1596
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases5
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 12
  reserve i := ![0, 1, 3, 5, 7, 10, 15, 15, 21, 30, 65, 65, 75] i
  bank i := ![bank3 1490, bank10 1603, bank24 1838, bank36 2062, bank42 2497, bank52 2900, bank65 3612, bank93 2947, bank83 5597, bank139 4862, bank158 51722, bank199 9241, bank171 201573] i
  head := src1547
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9]
  historyValues := [![15193, 168304, 779015, 3732690],
    ![24861/2, 260239/2, 593509, 2760366],
    ![29433/8, 152161/4, 2755208/9, 4220048/3],
    ![34345/18, 173735/9, 197215, 887691],
    ![36739/32, 398221/32, 1203554/9, 17199336/25],
    ![86036/121, 926944/121, 4188104/49, 2853600/7],
    ![86036/121, 926944/121, 4188104/49, 2853600/7],
    ![86036/121, 926944/121, 4188104/49, 40597872/121],
    ![254619/484, 3101492/441, 1091415/16, 40597872/121],
    ![254619/484, 451159/75, 8092904/147, 1594736/7],
    ![480716/1323, 451159/75, 8092904/147, 1594736/7],
    ![480716/1323, 6654820/1323, 29958968/675, 42434672/225],
    ![1826342/5329, 6654820/1323, 29958968/675, 42434672/225]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 4 9 514639 := by
  refine ⟨?_, rank154 6888, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1547⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free24_0
    · exact free36_0
    · exact free42_1
    · exact free52_0
    · exact free65_0
    · exact free93_0
    · exact free83_1
    · exact free139_0
    · exact free158_0
    · exact free199_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [338400942, 337465849, 338217296, 337844960, 337161346, 133117717, 130741945, 83927935, 115491119, 105092174, 104683599, 147255537, 238385481], [1019275, 1021838, 1019778, 1020799, 1022673, 2921477, 2973576, 4749786, 3390295, 3749217, 3763403, 2613084, 1544031],
  ![126539781024420, 1602279445404, 214546932900, 3837825480], 188437017139371192⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,8,8,13,9,10,10,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 6654820/1323, 29958968/675, 42434672/225] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases5
end Z6969Source1596

-- Source: Research6969.PhysicalChecks091
section Z6969Source1597
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1244 : Request := ⟨⟨⟨690,963,208,19788⟩,9921631092736,23724874690⟩,1,4,1,514639,9⟩
theorem cover1244 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1244) 2411 2314 [2328, 2375, 2411] := triangleCover (by decide +kernel)
def src1245 : Request := ⟨⟨⟨690,962,208,22261⟩,9921631092736,23645774460⟩,2,4,1,514639,9⟩
theorem cover1245 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1245) 2411 2314 [2332, 2391, 2411] := triangleCover (by decide +kernel)
def src1246 : Request := ⟨⟨⟨690,962,208,28173⟩,9921631092736,23645774460⟩,4,4,1,514639,9⟩
theorem cover1246 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1246) 2411 2314 [2327, 2370, 2411] := triangleCover (by decide +kernel)
def src1247 : Request := ⟨⟨⟨825,1151,248,25043⟩,16903818182656,48256472894⟩,4,4,1,514639,9⟩
theorem cover1247 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1247) 2411 2314 [2324, 2357, 2411] := triangleCover (by decide +kernel)
def src1248 : Request := ⟨⟨⟨1000,1395,301,31694⟩,30103476895744,104105680031⟩,8,4,1,514639,9⟩
theorem cover1248 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1248) 2411 2314 [2318, 2333, 2377, 2411] := triangleCover (by decide +kernel)
def src1249 : Request := ⟨⟨⟨1200,1674,368,50764⟩,52718727069696,218807905514⟩,16,4,1,514639,9⟩
theorem cover1249 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1249) 2411 2314 [2317, 2329, 2364, 2411] := triangleCover (by decide +kernel)
def src1250 : Request := ⟨⟨⟨2100,2930,645,57109⟩,282396798484480,2051392203643⟩,25,4,1,514639,9⟩
theorem cover1250 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1250) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src1253 : Request := ⟨⟨⟨3200,4463,982,762132⟩,997767489781760,11028049925768⟩,85,4,1,514639,9⟩
theorem cover1253 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1253) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src1254 : Request := ⟨⟨⟨4800,6696,1474,164837⟩,3367547627110400,55864419956306⟩,85,4,1,514639,9⟩
theorem cover1254 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1254) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src1255 : Request := ⟨⟨⟨8300,11579,2548,264035⟩,17399709518790656,499124969898998⟩,145,4,1,514639,9⟩
theorem cover1255 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1255) 2411 2314 [2321, 2343, 2403, 2411] := triangleCover (by decide +kernel)
def src1258 : Request := ⟨⟨⟨690,963,212,12355⟩,10065769922560,24078187611⟩,0,4,1,514639,16⟩
theorem cover1258 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1258) 2411 2314 [2322, 2350, 2411] := triangleCover (by decide +kernel)
def src1259 : Request := ⟨⟨⟨690,963,208,13899⟩,9921631092736,23724874690⟩,1,4,1,514639,16⟩
theorem cover1259 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1259) 2411 2314 [2321, 2345, 2411] := triangleCover (by decide +kernel)
def src1260 : Request := ⟨⟨⟨825,1151,248,17590⟩,16903818182656,48256472894⟩,4,4,1,514639,16⟩
theorem cover1260 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1260) 2411 2314 [2317, 2329, 2365, 2411] := triangleCover (by decide +kernel)
def src1261 : Request := ⟨⟨⟨1000,1395,307,22261⟩,30557599170560,105715278267⟩,8,4,1,514639,16⟩
theorem cover1261 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1261) 2411 2314 [2322, 2349, 2411] := triangleCover (by decide +kernel)
def src1262 : Request := ⟨⟨⟨1450,2023,445,40111⟩,92998964346880,466511127281⟩,20,4,1,514639,16⟩
theorem cover1262 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1262) 2411 2314 [2322, 2348, 2411] := triangleCover (by decide +kernel)
def src1263 : Request := ⟨⟨⟨2100,2929,645,208621⟩,282396798484480,2049139102608⟩,50,4,1,514639,16⟩
theorem cover1263 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1263) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1597

-- Source: Research6969.PrefixRescueDataHigherHelperCases5
section Z6969Source1598
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases5
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,15⟩
  bank i := ![bank156 17590, bank195 19788, bank192 22261, bank203 25043, bank192 28173, bank221 31694, bank228 50764, bank253 57109, bank326 164837, bank297 762132, bank368 264035] i
  reserve i := ![0, 1, 2, 4, 4, 8, 16, 25, 85, 85, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514639
  seedFloor := 9

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank156 17590
    · exact rank195 19788
    · exact rank192 22261
    · exact rank203 25043
    · exact rank192 28173
    · exact rank221 31694
    · exact rank228 50764
    · exact rank253 57109
    · exact rank326 164837
    · exact rank297 762132
    · exact rank368 264035
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1243⟩
    · exact ⟨_, cover1244⟩
    · exact ⟨_, cover1245⟩
    · exact ⟨_, cover1247⟩
    · exact ⟨_, cover1246⟩
    · exact ⟨_, cover1248⟩
    · exact ⟨_, cover1249⟩
    · exact ⟨_, cover1250⟩
    · exact ⟨_, cover1254⟩
    · exact ⟨_, cover1253⟩
    · exact ⟨_, cover1255⟩

def price : EarlyPrice := ⟨4, 15, 10, 90/100, 80/100, ![4450390552272, 910409468296, 14878781008, 2975770980], 4377109202146004⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![7409/86, 302255/146, 1229825/146, 3960525/146] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases5
end Z6969Source1598

-- Source: Research6969.PrefixNearSavedHigherHelperCases5
section Z6969Source1599
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases5
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,5030,86,2070,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases5.plan Lower6960.Prefix6969RescueData.HigherHelperCases5.plan Lower6960.Prefix6969RescueData.HigherHelperCases5.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 4 9 15 514639 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases5.plan, Lower6960.Prefix6969MainCases.HigherHelperCases5.price, Lower6960.Prefix6969MainCases.HigherHelperCases5.valid, Lower6960.Prefix6969MainCases.HigherHelperCases5.priced, Lower6960.Prefix6969MainCases.HigherHelperCases5.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases5.plan, Lower6960.Prefix6969RescueData.HigherHelperCases5.price, Lower6960.Prefix6969RescueData.HigherHelperCases5.sources, Lower6960.Prefix6969RescueData.HigherHelperCases5.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 221726810115916798 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases5
end Z6969Source1599

-- Source: Research6969.PhysicalChecks105
section Z6969Source1600
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1548 : Request := ⟨⟨⟨556,772,170,6357⟩,5255817068544,9968090926⟩,10,5,2,643298,17⟩
theorem cover1548 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1548) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1549 : Request := ⟨⟨⟨556,772,170,5664⟩,5255817068544,9968090926⟩,10,5,2,643298,27⟩
theorem cover1549 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1549) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1550 : Request := ⟨⟨⟨556,772,170,5412⟩,5255817068544,9968090926⟩,10,5,2,643298,31⟩
theorem cover1550 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1550) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1551 : Request := ⟨⟨⟨556,772,170,5177⟩,5255817068544,9968090926⟩,10,5,2,643298,35⟩
theorem cover1551 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1551) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1552 : Request := ⟨⟨⟨556,772,170,4961⟩,5255817068544,9968090926⟩,10,5,2,643298,39⟩
theorem cover1552 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1552) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1553 : Request := ⟨⟨⟨556,772,170,4811⟩,5255817068544,9968090926⟩,10,5,2,643298,42⟩
theorem cover1553 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1553) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1554 : Request := ⟨⟨⟨556,772,170,4628⟩,5255817068544,9968090926⟩,10,5,2,643298,46⟩
theorem cover1554 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1554) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1555 : Request := ⟨⟨⟨556,772,170,4466⟩,5255817068544,9968090926⟩,10,5,2,643298,50⟩
theorem cover1555 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1555) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1556 : Request := ⟨⟨⟨556,772,170,4324⟩,5255817068544,9968090926⟩,10,5,2,643298,54⟩
theorem cover1556 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1556) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1557 : Request := ⟨⟨⟨325,453,100,7715⟩,1061047500800,1193036697⟩,0,6,1,771959,1⟩
theorem cover1557 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1557) 2411 2314 [2333, 2405, 2411] := triangleCover (by decide +kernel)
def src1558 : Request := ⟨⟨⟨325,453,100,8679⟩,1061047500800,1193036697⟩,1,6,1,771959,1⟩
theorem cover1558 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1558) 2411 2314 [2322, 2354, 2411] := triangleCover (by decide +kernel)
def src1559 : Request := ⟨⟨⟨400,558,120,9763⟩,1935519252480,2682384904⟩,2,6,1,771959,1⟩
theorem cover1559 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1559) 2411 2314 [2339, 2411] := triangleCover (by decide +kernel)
def src1560 : Request := ⟨⟨⟨470,655,141,10983⟩,3134317133824,5085275599⟩,4,6,1,771959,1⟩
theorem cover1560 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1560) 2411 2314 [2327, 2373, 2411] := triangleCover (by decide +kernel)
def src1561 : Request := ⟨⟨⟨560,781,172,13899⟩,5388141854720,10440670587⟩,8,6,1,771959,1⟩
theorem cover1561 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1561) 2411 2314 [2332, 2392, 2411] := triangleCover (by decide +kernel)
def src1562 : Request := ⟨⟨⟨690,962,212,17590⟩,10065769922560,23997864317⟩,13,6,1,771959,1⟩
theorem cover1562 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1562) 2411 2314 [2323, 2353, 2411] := triangleCover (by decide +kernel)
def src1563 : Request := ⟨⟨⟨1000,1395,307,22261⟩,30557599170560,105715278267⟩,20,6,1,771959,1⟩
theorem cover1563 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1563) 2411 2314 [2329, 2376, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1600

-- Source: Research6969.PrefixMainDataHigherHelperCases6
section Z6969Source1601
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HigherHelperCases6
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 11
  reserve i := ![0, 1, 2, 3, 5, 8, 12, 21, 21, 65, 65, 75] i
  bank i := ![bank3 1490, bank10 1603, bank19 1656, bank24 1838, bank37 2039, bank50 2450, bank63 2899, bank108 3859, bank83 5597, bank167 24691, bank199 9241, bank171 201573] i
  head := src1548
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8]
  historyValues := [![15589, 166130, 767227, 3566958],
    ![24861/2, 250681/2, 2286421/4, 2569609],
    ![6218, 180719/3, 2286421/4, 2569609],
    ![29433/8, 585811/16, 2652194/9, 3894722/3],
    ![17323/9, 670837/36, 3017147/16, 12961923/16],
    ![81680/81, 797920/81, 898769/9, 2595775/6],
    ![81680/81, 797920/81, 898769/9, 2595775/6],
    ![76938/121, 64184/11, 1863897/32, 14891881/64],
    ![254619/484, 64184/11, 1863897/32, 14891881/64],
    ![55840/147, 64184/11, 1863897/32, 14891881/64],
    ![55840/147, 6384010/1323, 10525499/242, 85396081/484],
    ![1826342/5329, 6384010/1323, 10525499/242, 85396081/484]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 4 16 514639 := by
  refine ⟨?_, rank154 6357, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1548⟩⟩
  · intro i; fin_cases i
    · exact free3_0
    · exact free10_0
    · exact free19_0
    · exact free24_0
    · exact free37_0
    · exact free50_0
    · exact free63_0
    · exact free108_0
    · exact free83_1
    · exact free167_0
    · exact free199_0
    · exact free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [329538123, 328312998, 329167890, 329505374, 328628561, 167229663, 167341177, 155408013, 100552859, 100222282, 148662189, 236912394], [1043570, 1046928, 1044585, 1043660, 1046063, 2280915, 2279061, 2477509, 3932185, 3946141, 2589692, 1556145],
  ![125757836983080, 1603871119536, 213221154600, 4024176420], 182756035399248709⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,7,7,7,11,11,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 6384010/1323, 10525499/242, 85396081/484] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HigherHelperCases6
end Z6969Source1601

-- Source: Research6969.PhysicalChecks092
section Z6969Source1602
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1264 : Request := ⟨⟨⟨3200,4464,982,72277⟩,997767489781760,11036007960531⟩,50,4,1,514639,16⟩
theorem cover1264 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1264) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src1265 : Request := ⟨⟨⟨8300,11579,2548,185441⟩,17399709518790656,499124969898998⟩,145,4,1,514639,16⟩
theorem cover1265 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1265) 2411 2314 [2318, 2332, 2370, 2411] := triangleCover (by decide +kernel)
def src1266 : Request := ⟨⟨⟨6900,9623,2118,762132⟩,9997036108906496,238176347849000⟩,190,4,1,514639,16⟩
theorem cover1266 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1266) 2411 2314 [2316, 2324, 2346, 2406, 2411] := triangleCover (by decide +kernel)
def src1267 : Request := ⟨⟨⟨8300,11575,2548,2784236⟩,17399709518790656,498569901356632⟩,245,4,1,514639,16⟩
theorem cover1267 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1267) 2411 2314 [2315, 2320, 2334, 2372, 2411] := triangleCover (by decide +kernel)
def src1274 : Request := ⟨⟨⟨470,655,144,7715⟩,3184589537280,5168862572⟩,0,4,1,514639,26⟩
theorem cover1274 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1274) 2411 2314 [2334, 2403, 2411] := triangleCover (by decide +kernel)
def src1275 : Request := ⟨⟨⟨560,781,172,7715⟩,5388141854720,10440670587⟩,1,4,1,514639,26⟩
theorem cover1275 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1275) 2411 2314 [2324, 2358, 2411] := triangleCover (by decide +kernel)
def src1276 : Request := ⟨⟨⟨560,781,172,8679⟩,5388141854720,10440670587⟩,2,4,1,514639,26⟩
theorem cover1276 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1276) 2411 2314 [2320, 2342, 2411] := triangleCover (by decide +kernel)
def src1277 : Request := ⟨⟨⟨690,962,212,12355⟩,10065769922560,23997864317⟩,6,4,1,514639,26⟩
theorem cover1277 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1277) 2411 2314 [2320, 2341, 2406, 2411] := triangleCover (by decide +kernel)
def src1278 : Request := ⟨⟨⟨1200,1674,361,19788⟩,51955677528064,215563369662⟩,16,4,1,514639,26⟩
theorem cover1278 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1278) 2411 2314 [2319, 2336, 2386, 2411] := triangleCover (by decide +kernel)
def src1279 : Request := ⟨⟨⟨2600,3627,798,45124⟩,535425056505856,4812227595495⟩,50,4,1,514639,26⟩
theorem cover1279 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1279) 2411 2314 [2322, 2348, 2411] := triangleCover (by decide +kernel)
def src1280 : Request := ⟨⟨⟨3200,4463,982,208621⟩,997767489781760,11028049925768⟩,85,4,1,514639,26⟩
theorem cover1280 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1280) 2411 2314 [2317, 2329, 2362, 2411] := triangleCover (by decide +kernel)
def src1281 : Request := ⟨⟨⟨8300,11577,2548,164837⟩,17399709518790656,498847383098023⟩,190,4,1,514639,26⟩
theorem cover1281 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1281) 2411 2314 [2329, 2373, 2411] := triangleCover (by decide +kernel)
def src1282 : Request := ⟨⟨⟨10000,13950,3150,130242⟩,31027650042265600,1072717072025530⟩,190,4,1,514639,26⟩
theorem cover1282 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1282) 2411 2314 [2316, 2324, 2346, 2406, 2411] := triangleCover (by decide +kernel)
def src1283 : Request := ⟨⟨⟨8300,11575,2548,1085143⟩,17399709518790656,498569901356632⟩,245,4,1,514639,26⟩
theorem cover1283 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1283) 2411 2314 [2316, 2324, 2346, 2406, 2411] := triangleCover (by decide +kernel)
def src1286 : Request := ⟨⟨⟨400,558,123,6858⟩,1971918995456,2734096379⟩,0,4,1,514639,30⟩
theorem cover1286 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1286) 2411 2314 [2332, 2396, 2411] := triangleCover (by decide +kernel)
def src1287 : Request := ⟨⟨⟨470,655,144,6858⟩,3184589537280,5168862572⟩,1,4,1,514639,30⟩
theorem cover1287 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1287) 2411 2314 [2336, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1602

-- Source: Research6969.PrefixRescueDataHigherHelperCases6
section Z6969Source1603
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases6
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,4,1,25⟩
  bank i := ![bank196 12355, bank195 13899, bank203 17590, bank222 22261, bank237 40111, bank300 72277, bank249 208621, bank368 185441, bank351 762132, bank362 2784236] i
  reserve i := ![0, 1, 4, 8, 20, 50, 50, 145, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514639
  seedFloor := 16

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank196 12355
    · exact rank195 13899
    · exact rank203 17590
    · exact rank222 22261
    · exact rank237 40111
    · exact rank300 72277
    · exact rank249 208621
    · exact rank368 185441
    · exact rank351 762132
    · exact rank362 2784236
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1258⟩
    · exact ⟨_, cover1259⟩
    · exact ⟨_, cover1260⟩
    · exact ⟨_, cover1261⟩
    · exact ⟨_, cover1262⟩
    · exact ⟨_, cover1264⟩
    · exact ⟨_, cover1263⟩
    · exact ⟨_, cover1265⟩
    · exact ⟨_, cover1266⟩
    · exact ⟨_, cover1267⟩

def price : EarlyPrice := ⟨4, 25, 9, 80/100, 70/100, ![27097084060228, 3339521140581, 24797959004, 2975770980], 9914923776730453⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![19219/246, 249141/146, 1031239/146, 4636025/146] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.HigherHelperCases6
end Z6969Source1603

-- Source: Research6969.PrefixNearSavedHigherHelperCases6
section Z6969Source1604
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedHigherHelperCases6
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨342,4825,78,1706,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.HigherHelperCases6.plan Lower6960.Prefix6969RescueData.HigherHelperCases6.plan Lower6960.Prefix6969RescueData.HigherHelperCases6.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 4 16 25 514639 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases6.plan, Lower6960.Prefix6969MainCases.HigherHelperCases6.price, Lower6960.Prefix6969MainCases.HigherHelperCases6.valid, Lower6960.Prefix6969MainCases.HigherHelperCases6.priced, Lower6960.Prefix6969MainCases.HigherHelperCases6.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases6.plan, Lower6960.Prefix6969RescueData.HigherHelperCases6.price, Lower6960.Prefix6969RescueData.HigherHelperCases6.sources, Lower6960.Prefix6969RescueData.HigherHelperCases6.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 231050145930463754 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases6
end Z6969Source1604

-- Source: Research6969.PrefixMainDataQuarticIntervals0
section Z6969Source1605
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.QuarticIntervals0
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 14, 18, 21, 21, 41, 30, 41, 76, 76, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank30 1953, bank40 2218, bank54 2755, bank68 3168, bank90 3666, bank84 5564, bank127 3592, bank152 6378, bank168 4492, bank125 29117, bank188 40375, bank212 10770, bank177 92547, bank173 184768, bank169 292467] i
  head := src1549
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15672, 161380, 743838, 3330327],
    ![25417/2, 236789/2, 537617, 2411809],
    ![54680/9, 516070/9, 537617, 2411448],
    ![29433/8, 139003/4, 2517752/9, 3470144/3],
    ![63824/25, 598218/25, 408177/2, 3814209/4],
    ![72196/49, 677252/49, 3054664/25, 4919524/9],
    ![89110/121, 836510/121, 3792076/49, 15604320/49],
    ![89110/121, 836510/121, 3792076/49, 15604320/49],
    ![254616/361, 2311272/361, 3050112/49, 13439556/49],
    ![63754/121, 2311272/361, 3050112/49, 13439556/49],
    ![63754/121, 670580/121, 2921456/49, 201601],
    ![63754/121, 8256528/1681, 2319858/49, 9031248/49],
    ![63754/121, 8256528/1681, 2319858/49, 8480896/49],
    ![675632/1681, 8256528/1681, 2319858/49, 8480896/49],
    ![486507/1369, 8256528/1681, 2319858/49, 8480896/49],
    ![486507/1369, 6048819/1369, 6865875/169, 47445440/289],
    ![935333/2738, 6048819/1369, 6865875/169, 47445440/289],
    ![461692/1369, 6048819/1369, 6865875/169, 47445440/289],
    ![459151/1369, 6048819/1369, 6865875/169, 47445440/289]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 4 26 514639 := by
  refine ⟨?_, rank154 5664, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1549⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free30_0
    · exact free40_0
    · exact free54_0
    · exact free68_0
    · exact free90_0
    · exact free84_0
    · exact free127_0
    · exact free152_0
    · exact free168_0
    · exact free125_0
    · exact free188_0
    · exact free212_0
    · exact free177_0
    · exact free173_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [312369428, 312321291, 310582973, 311818578, 310880062, 310226033, 149404041, 149310446, 149307550, 149399334, 78104594, 93450520, 60294637, 93264841, 93468242, 99853536, 130083661, 165598540, 229106458], [1127293, 1127539, 1136434, 1130112, 1134914, 1138261, 2577355, 2578911, 2578959, 2577433, 5117921, 4242266, 6686540, 4251632, 4241372, 3961707, 2988012, 2308041, 1620338],
  ![121614290035560, 1612303922492, 206195812200, 5058325860], 167929821239861259⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,7,7,7,7,14,12,18,12,12,11,8,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 6048819/1369, 6865875/169, 47445440/289] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.QuarticIntervals0
end Z6969Source1605

-- Source: Research6969.PrefixRescueDataQuarticIntervals0
section Z6969Source1606
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals0
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,29⟩
  bank i := ![bank142 7715, bank156 7715, bank156 8679, bank193 12355, bank227 19788, bank267 45124, bank297 208621, bank378 130242, bank362 1085143, bank378 130242, bank365 164837] i
  reserve i := ![0, 1, 2, 6, 16, 50, 85, 190, 245, 190, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514639
  seedFloor := 26

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 7715
    · exact rank156 7715
    · exact rank156 8679
    · exact rank193 12355
    · exact rank227 19788
    · exact rank267 45124
    · exact rank297 208621
    · exact rank378 130242
    · exact rank362 1085143
    · exact rank378 130242
    · exact rank365 164837
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1274⟩
    · exact ⟨_, cover1275⟩
    · exact ⟨_, cover1276⟩
    · exact ⟨_, cover1277⟩
    · exact ⟨_, cover1278⟩
    · exact ⟨_, cover1279⟩
    · exact ⟨_, cover1280⟩
    · exact ⟨_, cover1282⟩
    · exact ⟨_, cover1283⟩
    · exact ⟨_, cover1282⟩
    · exact ⟨_, cover1281⟩

def price : EarlyPrice := ⟨4, 29, 10, 75/100, 70/100, ![12250715387642, 1369232494893, 35561906100, 3678837750], 3775844912875168⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![19219/246, 221592/191, 925518/191, 3777018/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.QuarticIntervals0
end Z6969Source1606

-- Source: Research6969.PrefixNearSavedQuarticIntervals0
section Z6969Source1607
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedQuarticIntervals0
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨335,4418,78,1160,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.QuarticIntervals0.plan Lower6960.Prefix6969RescueData.QuarticIntervals0.plan Lower6960.Prefix6969RescueData.QuarticIntervals0.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 4 26 29 514639 :=
  ⟨Lower6960.Prefix6969MainCases.QuarticIntervals0.plan, Lower6960.Prefix6969MainCases.QuarticIntervals0.price, Lower6960.Prefix6969MainCases.QuarticIntervals0.valid, Lower6960.Prefix6969MainCases.QuarticIntervals0.priced, Lower6960.Prefix6969MainCases.QuarticIntervals0.sources,
   Lower6960.Prefix6969RescueData.QuarticIntervals0.plan, Lower6960.Prefix6969RescueData.QuarticIntervals0.price, Lower6960.Prefix6969RescueData.QuarticIntervals0.sources, Lower6960.Prefix6969RescueData.QuarticIntervals0.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 209709803386423093 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedQuarticIntervals0
end Z6969Source1607

end Merged_Z6969Pack0711

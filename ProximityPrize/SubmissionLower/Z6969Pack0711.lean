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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 21 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [324034594, 323819061, 322550678, 322929581, 322940475, 322263040, 322342300, 146144852, 146034675, 144604037, 143594103, 71257922, 67523490, 84871996, 95685823, 95595376, 148967944, 232016961], [1067368, 1068471, 1074960, 1073021, 1072965, 1076431, 1076026, 2635216, 2637631, 2668998, 2691140, 5626134, 5948968, 4692681, 4136733, 4140550, 2584037, 1596051],
  ![123159243238020, 1609159491744, 208815264900, 4927254500], 175565191139265096⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 21

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 21, 10, 80/100, 70/100, ![24525456000000, 2410017555312, 24607207520, 2343564930], 11526919819217150⟩
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

def data : NearCase 3 21 21 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons17.plan, Lower6960.Prefix6969MainCases.CubicSingletons17.price, Lower6960.Prefix6969MainCases.CubicSingletons17.valid, Lower6960.Prefix6969MainCases.CubicSingletons17.priced, Lower6960.Prefix6969MainCases.CubicSingletons17.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons17.plan, Lower6960.Prefix6969RescueData.CubicSingletons17.price, Lower6960.Prefix6969RescueData.CubicSingletons17.sources, Lower6960.Prefix6969RescueData.CubicSingletons17.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 217136761439371078 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 22 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [322729996, 321350307, 321600264, 322182507, 321551057, 321074936, 321472927, 161704338, 161777745, 103682379, 78611255, 75186064, 67289685, 84235857, 97247799, 97825452, 148524566, 231678753], [1074042, 1081100, 1079822, 1076843, 1080073, 1082509, 1080473, 2372278, 2371058, 3799237, 5081802, 5318356, 5970156, 4730455, 4070809, 4046429, 2591409, 1598832],
  ![122979715667460, 1609525027092, 208510877700, 4844262710], 174755575490885467⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src879 : Request := ⟨⟨⟨1200,1674,368,19788⟩,52718727069696,218807905514⟩,3,3,1,386045,22⟩
private theorem pass879_2293 : (Triangular src879) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass879_2297 : (Triangular src879) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass879_2309 : (Triangular src879) 2309 2343 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass879_2344 : (Triangular src879) 2344 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover879 : Cover (Triangular src879) 2389 2293 [2296,2308,2343,2389] := by
  exact ⟨by decide, by decide, pass879_2293, by decide, by decide, pass879_2297, by decide, by decide, pass879_2309, by decide, by decide, pass879_2344, rfl⟩
def src880 : Request := ⟨⟨⟨1200,1674,368,22261⟩,52718727069696,218807905514⟩,4,3,1,386045,22⟩
private theorem pass880_2293 : (Triangular src880) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass880_2302 : (Triangular src880) 2302 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass880_2328 : (Triangular src880) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover880 : Cover (Triangular src880) 2389 2293 [2301,2327,2389] := by
  exact ⟨by decide, by decide, pass880_2293, by decide, by decide, pass880_2302, by decide, by decide, pass880_2328, rfl⟩
def src881 : Request := ⟨⟨⟨1450,2023,445,28173⟩,92998964346880,466511127281⟩,8,3,1,386045,22⟩
private theorem pass881_2293 : (Triangular src881) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass881_2296 : (Triangular src881) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass881_2305 : (Triangular src881) 2305 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass881_2331 : (Triangular src881) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover881 : Cover (Triangular src881) 2389 2293 [2295,2304,2330,2389] := by
  exact ⟨by decide, by decide, pass881_2293, by decide, by decide, pass881_2296, by decide, by decide, pass881_2305, by decide, by decide, pass881_2331, rfl⟩
def src883 : Request := ⟨⟨⟨2600,3628,798,57109⟩,535425056505856,4816500515660⟩,25,3,1,386045,22⟩
private theorem pass883_2293 : (Triangular src883) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass883_2296 : (Triangular src883) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass883_2305 : (Triangular src883) 2305 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass883_2330 : (Triangular src883) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover883 : Cover (Triangular src883) 2389 2293 [2295,2304,2329,2389] := by
  exact ⟨by decide, by decide, pass883_2293, by decide, by decide, pass883_2296, by decide, by decide, pass883_2305, by decide, by decide, pass883_2330, rfl⟩
def src885 : Request := ⟨⟨⟨5700,7953,1750,115771⟩,5637370734182400,111115710437454⟩,65,3,1,386045,22⟩
private theorem pass885_2293 : (Triangular src885) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass885_2295 : (Triangular src885) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass885_2300 : (Triangular src885) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass885_2314 : (Triangular src885) 2314 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass885_2352 : (Triangular src885) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover885 : Cover (Triangular src885) 2389 2293 [2294,2299,2313,2351,2389] := by
  exact ⟨by decide, by decide, pass885_2293, by decide, by decide, pass885_2295, by decide, by decide, pass885_2300, by decide, by decide, pass885_2314, by decide, by decide, pass885_2352, rfl⟩
def src886 : Request := ⟨⟨⟨6900,9626,2077,475797⟩,9849424459857920,234809190715807⟩,110,3,1,386045,22⟩
private theorem pass886_2293 : (Triangular src886) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass886_2296 : (Triangular src886) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass886_2304 : (Triangular src886) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass886_2326 : (Triangular src886) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass886_2387 : (Triangular src886) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover886 : Cover (Triangular src886) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass886_2293, by decide, by decide, pass886_2296, by decide, by decide, pass886_2304, by decide, by decide, pass886_2326, by decide, by decide, pass886_2387, rfl⟩
def src887 : Request := ⟨⟨⟨10000,13953,3010,185441⟩,29974681586237440,1036125345444439⟩,110,3,1,386045,22⟩
private theorem pass887_2293 : (Triangular src887) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass887_2294 : (Triangular src887) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass887_2297 : (Triangular src887) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass887_2305 : (Triangular src887) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass887_2327 : (Triangular src887) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass887_2388 : (Triangular src887) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover887 : Cover (Triangular src887) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass887_2293, by decide, by decide, pass887_2294, by decide, by decide, pass887_2297, by decide, by decide, pass887_2305, by decide, by decide, pass887_2327, by decide, by decide, pass887_2388, rfl⟩
def src888 : Request := ⟨⟨⟨8300,11579,2498,2474877⟩,17139238515245056,491470625461013⟩,145,3,1,386045,22⟩
private theorem pass888_2293 : (Triangular src888) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass888_2294 : (Triangular src888) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass888_2296 : (Triangular src888) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass888_2302 : (Triangular src888) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass888_2319 : (Triangular src888) 2319 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass888_2365 : (Triangular src888) 2365 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover888 : Cover (Triangular src888) 2389 2293 [2293,2295,2301,2318,2364,2389] := by
  exact ⟨by decide, by decide, pass888_2293, by decide, by decide, pass888_2294, by decide, by decide, pass888_2296, by decide, by decide, pass888_2302, by decide, by decide, pass888_2319, by decide, by decide, pass888_2365, rfl⟩
def src889 : Request := ⟨⟨⟨1000,1395,307,13899⟩,30557599170560,105715278267⟩,0,3,1,386045,23⟩
private theorem pass889_2293 : (Triangular src889) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass889_2297 : (Triangular src889) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass889_2309 : (Triangular src889) 2309 2344 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass889_2345 : (Triangular src889) 2345 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover889 : Cover (Triangular src889) 2389 2293 [2296,2308,2344,2389] := by
  exact ⟨by decide, by decide, pass889_2293, by decide, by decide, pass889_2297, by decide, by decide, pass889_2309, by decide, by decide, pass889_2345, rfl⟩
def src890 : Request := ⟨⟨⟨1000,1395,307,15636⟩,30557599170560,105715278267⟩,1,3,1,386045,23⟩
private theorem pass890_2293 : (Triangular src890) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass890_2303 : (Triangular src890) 2303 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass890_2332 : (Triangular src890) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover890 : Cover (Triangular src890) 2389 2293 [2302,2331,2389] := by
  exact ⟨by decide, by decide, pass890_2293, by decide, by decide, pass890_2303, by decide, by decide, pass890_2332, rfl⟩
def src891 : Request := ⟨⟨⟨1000,1395,301,17590⟩,30103476895744,104105680031⟩,2,3,1,386045,23⟩
private theorem pass891_2293 : (Triangular src891) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass891_2295 : (Triangular src891) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass891_2301 : (Triangular src891) 2301 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass891_2319 : (Triangular src891) 2319 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass891_2372 : (Triangular src891) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover891 : Cover (Triangular src891) 2389 2293 [2294,2300,2318,2371,2389] := by
  exact ⟨by decide, by decide, pass891_2293, by decide, by decide, pass891_2295, by decide, by decide, pass891_2301, by decide, by decide, pass891_2319, by decide, by decide, pass891_2372, rfl⟩
def src892 : Request := ⟨⟨⟨1200,1674,368,19788⟩,52718727069696,218807905514⟩,4,3,1,386045,23⟩
private theorem pass892_2293 : (Triangular src892) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass892_2301 : (Triangular src892) 2301 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass892_2325 : (Triangular src892) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover892 : Cover (Triangular src892) 2389 2293 [2300,2324,2389] := by
  exact ⟨by decide, by decide, pass892_2293, by decide, by decide, pass892_2301, by decide, by decide, pass892_2325, rfl⟩
def src893 : Request := ⟨⟨⟨1450,2023,445,25043⟩,92998964346880,466511127281⟩,8,3,1,386045,23⟩
private theorem pass893_2293 : (Triangular src893) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass893_2297 : (Triangular src893) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass893_2308 : (Triangular src893) 2308 2339 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass893_2340 : (Triangular src893) 2340 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover893 : Cover (Triangular src893) 2389 2293 [2296,2307,2339,2389] := by
  exact ⟨by decide, by decide, pass893_2293, by decide, by decide, pass893_2297, by decide, by decide, pass893_2308, by decide, by decide, pass893_2340, rfl⟩
def src894 : Request := ⟨⟨⟨2100,2930,645,45124⟩,282396798484480,2051392203643⟩,20,3,1,386045,23⟩
private theorem pass894_2293 : (Triangular src894) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass894_2294 : (Triangular src894) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass894_2297 : (Triangular src894) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass894_2305 : (Triangular src894) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass894_2328 : (Triangular src894) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover894 : Cover (Triangular src894) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass894_2293, by decide, by decide, pass894_2294, by decide, by decide, pass894_2297, by decide, by decide, pass894_2305, by decide, by decide, pass894_2328, rfl⟩
def src899 : Request := ⟨⟨⟨4800,6697,1474,81311⟩,3367547627110400,55891290082931⟩,50,3,1,386045,23⟩
private theorem pass899_2293 : (Triangular src899) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass899_2297 : (Triangular src899) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass899_2308 : (Triangular src899) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass899_2339 : (Triangular src899) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover899 : Cover (Triangular src899) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass899_2293, by decide, by decide, pass899_2297, by decide, by decide, pass899_2308, by decide, by decide, pass899_2339, rfl⟩
def src900 : Request := ⟨⟨⟨4800,6697,1474,130242⟩,3367547627110400,55891290082931⟩,65,3,1,386045,23⟩
private theorem pass900_2293 : (Triangular src900) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass900_2294 : (Triangular src900) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass900_2297 : (Triangular src900) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass900_2305 : (Triangular src900) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass900_2327 : (Triangular src900) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass900_2388 : (Triangular src900) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover900 : Cover (Triangular src900) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass900_2293, by decide, by decide, pass900_2294, by decide, by decide, pass900_2297, by decide, by decide, pass900_2305, by decide, by decide, pass900_2327, by decide, by decide, pass900_2388, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 22

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 22, 10, 80/100, 80/100, ![21195947948265, 2004695633106, 25778979450, 2343564930], 9526465363499239⟩
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

def data : NearCase 3 22 22 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons18.plan, Lower6960.Prefix6969MainCases.CubicSingletons18.price, Lower6960.Prefix6969MainCases.CubicSingletons18.valid, Lower6960.Prefix6969MainCases.CubicSingletons18.priced, Lower6960.Prefix6969MainCases.CubicSingletons18.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons18.plan, Lower6960.Prefix6969RescueData.CubicSingletons18.price, Lower6960.Prefix6969RescueData.CubicSingletons18.sources, Lower6960.Prefix6969RescueData.CubicSingletons18.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 215864467429798874 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedCubicSingletons18
end Z6969Source1482

-- Source: Research6969.PhysicalChecks099
section Z6969Source1483
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1408 : Request := ⟨⟨⟨556,772,170,6204⟩,5255817068544,9968090926⟩,10,4,2,514726,24⟩
private theorem pass1408_2293 : (Triangular src1408) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1408_2294 : (Triangular src1408) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1408_2297 : (Triangular src1408) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1408_2306 : (Triangular src1408) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1408_2335 : (Triangular src1408) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1408 : Cover (Triangular src1408) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1408_2293, by decide, by decide, pass1408_2294, by decide, by decide, pass1408_2297, by decide, by decide, pass1408_2306, by decide, by decide, pass1408_2335, rfl⟩
def src1409 : Request := ⟨⟨⟨556,772,170,6124⟩,5255817068544,9968090926⟩,10,4,2,514726,25⟩
private theorem pass1409_2293 : (Triangular src1409) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1409_2294 : (Triangular src1409) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1409_2297 : (Triangular src1409) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1409_2306 : (Triangular src1409) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1409_2335 : (Triangular src1409) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1409 : Cover (Triangular src1409) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1409_2293, by decide, by decide, pass1409_2294, by decide, by decide, pass1409_2297, by decide, by decide, pass1409_2306, by decide, by decide, pass1409_2335, rfl⟩
def src1410 : Request := ⟨⟨⟨556,772,170,6046⟩,5255817068544,9968090926⟩,10,4,2,514726,26⟩
private theorem pass1410_2293 : (Triangular src1410) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1410_2294 : (Triangular src1410) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1410_2297 : (Triangular src1410) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1410_2306 : (Triangular src1410) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1410_2335 : (Triangular src1410) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1410 : Cover (Triangular src1410) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1410_2293, by decide, by decide, pass1410_2294, by decide, by decide, pass1410_2297, by decide, by decide, pass1410_2306, by decide, by decide, pass1410_2335, rfl⟩
def src1411 : Request := ⟨⟨⟨556,772,170,5969⟩,5255817068544,9968090926⟩,10,4,2,514726,27⟩
private theorem pass1411_2293 : (Triangular src1411) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1411_2294 : (Triangular src1411) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1411_2297 : (Triangular src1411) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1411_2306 : (Triangular src1411) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1411_2335 : (Triangular src1411) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1411 : Cover (Triangular src1411) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1411_2293, by decide, by decide, pass1411_2294, by decide, by decide, pass1411_2297, by decide, by decide, pass1411_2306, by decide, by decide, pass1411_2335, rfl⟩
def src1412 : Request := ⟨⟨⟨556,772,170,5893⟩,5255817068544,9968090926⟩,10,4,2,514726,28⟩
private theorem pass1412_2293 : (Triangular src1412) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1412_2294 : (Triangular src1412) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1412_2297 : (Triangular src1412) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1412_2306 : (Triangular src1412) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1412_2335 : (Triangular src1412) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1412 : Cover (Triangular src1412) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1412_2293, by decide, by decide, pass1412_2294, by decide, by decide, pass1412_2297, by decide, by decide, pass1412_2306, by decide, by decide, pass1412_2335, rfl⟩
def src1413 : Request := ⟨⟨⟨556,772,170,5818⟩,5255817068544,9968090926⟩,10,4,2,514726,29⟩
private theorem pass1413_2293 : (Triangular src1413) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1413_2294 : (Triangular src1413) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1413_2297 : (Triangular src1413) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1413_2306 : (Triangular src1413) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1413_2335 : (Triangular src1413) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1413 : Cover (Triangular src1413) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1413_2293, by decide, by decide, pass1413_2294, by decide, by decide, pass1413_2297, by decide, by decide, pass1413_2306, by decide, by decide, pass1413_2335, rfl⟩
def src1414 : Request := ⟨⟨⟨556,772,170,5744⟩,5255817068544,9968090926⟩,10,4,2,514726,30⟩
private theorem pass1414_2293 : (Triangular src1414) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1414_2294 : (Triangular src1414) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1414_2297 : (Triangular src1414) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1414_2306 : (Triangular src1414) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1414_2335 : (Triangular src1414) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1414 : Cover (Triangular src1414) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1414_2293, by decide, by decide, pass1414_2294, by decide, by decide, pass1414_2297, by decide, by decide, pass1414_2306, by decide, by decide, pass1414_2335, rfl⟩
def src1415 : Request := ⟨⟨⟨556,772,170,5671⟩,5255817068544,9968090926⟩,10,4,2,514726,31⟩
private theorem pass1415_2293 : (Triangular src1415) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1415_2294 : (Triangular src1415) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1415_2297 : (Triangular src1415) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1415_2306 : (Triangular src1415) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1415_2335 : (Triangular src1415) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1415 : Cover (Triangular src1415) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1415_2293, by decide, by decide, pass1415_2294, by decide, by decide, pass1415_2297, by decide, by decide, pass1415_2306, by decide, by decide, pass1415_2335, rfl⟩
def src1416 : Request := ⟨⟨⟨556,772,170,5600⟩,5255817068544,9968090926⟩,10,4,2,514726,32⟩
private theorem pass1416_2293 : (Triangular src1416) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1416_2294 : (Triangular src1416) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1416_2297 : (Triangular src1416) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1416_2306 : (Triangular src1416) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1416_2335 : (Triangular src1416) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1416 : Cover (Triangular src1416) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1416_2293, by decide, by decide, pass1416_2294, by decide, by decide, pass1416_2297, by decide, by decide, pass1416_2306, by decide, by decide, pass1416_2335, rfl⟩
def src1417 : Request := ⟨⟨⟨556,772,170,5530⟩,5255817068544,9968090926⟩,10,4,2,514726,33⟩
private theorem pass1417_2293 : (Triangular src1417) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1417_2294 : (Triangular src1417) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1417_2297 : (Triangular src1417) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1417_2306 : (Triangular src1417) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1417_2335 : (Triangular src1417) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1417 : Cover (Triangular src1417) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1417_2293, by decide, by decide, pass1417_2294, by decide, by decide, pass1417_2297, by decide, by decide, pass1417_2306, by decide, by decide, pass1417_2335, rfl⟩
def src1418 : Request := ⟨⟨⟨556,772,170,5462⟩,5255817068544,9968090926⟩,10,4,2,514726,34⟩
private theorem pass1418_2293 : (Triangular src1418) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1418_2294 : (Triangular src1418) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1418_2297 : (Triangular src1418) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1418_2306 : (Triangular src1418) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1418_2335 : (Triangular src1418) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1418 : Cover (Triangular src1418) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1418_2293, by decide, by decide, pass1418_2294, by decide, by decide, pass1418_2297, by decide, by decide, pass1418_2306, by decide, by decide, pass1418_2335, rfl⟩
def src1419 : Request := ⟨⟨⟨556,772,170,5395⟩,5255817068544,9968090926⟩,10,4,2,514726,35⟩
private theorem pass1419_2293 : (Triangular src1419) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1419_2294 : (Triangular src1419) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1419_2297 : (Triangular src1419) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1419_2306 : (Triangular src1419) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1419_2335 : (Triangular src1419) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1419 : Cover (Triangular src1419) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1419_2293, by decide, by decide, pass1419_2294, by decide, by decide, pass1419_2297, by decide, by decide, pass1419_2306, by decide, by decide, pass1419_2335, rfl⟩
def src1420 : Request := ⟨⟨⟨556,772,170,5329⟩,5255817068544,9968090926⟩,10,4,2,514726,36⟩
private theorem pass1420_2293 : (Triangular src1420) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1420_2294 : (Triangular src1420) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1420_2297 : (Triangular src1420) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1420_2306 : (Triangular src1420) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1420_2335 : (Triangular src1420) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1420 : Cover (Triangular src1420) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1420_2293, by decide, by decide, pass1420_2294, by decide, by decide, pass1420_2297, by decide, by decide, pass1420_2306, by decide, by decide, pass1420_2335, rfl⟩
def src1421 : Request := ⟨⟨⟨556,772,170,5265⟩,5255817068544,9968090926⟩,10,4,2,514726,37⟩
private theorem pass1421_2293 : (Triangular src1421) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1421_2294 : (Triangular src1421) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1421_2297 : (Triangular src1421) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1421_2306 : (Triangular src1421) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1421_2335 : (Triangular src1421) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1421 : Cover (Triangular src1421) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1421_2293, by decide, by decide, pass1421_2294, by decide, by decide, pass1421_2297, by decide, by decide, pass1421_2306, by decide, by decide, pass1421_2335, rfl⟩
def src1422 : Request := ⟨⟨⟨556,772,170,5202⟩,5255817068544,9968090926⟩,10,4,2,514726,38⟩
private theorem pass1422_2293 : (Triangular src1422) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1422_2294 : (Triangular src1422) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1422_2297 : (Triangular src1422) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1422_2306 : (Triangular src1422) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1422_2335 : (Triangular src1422) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1422 : Cover (Triangular src1422) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1422_2293, by decide, by decide, pass1422_2294, by decide, by decide, pass1422_2297, by decide, by decide, pass1422_2306, by decide, by decide, pass1422_2335, rfl⟩
def src1423 : Request := ⟨⟨⟨556,772,170,5140⟩,5255817068544,9968090926⟩,10,4,2,514726,39⟩
private theorem pass1423_2293 : (Triangular src1423) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1423_2294 : (Triangular src1423) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1423_2297 : (Triangular src1423) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1423_2306 : (Triangular src1423) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1423_2335 : (Triangular src1423) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1423 : Cover (Triangular src1423) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1423_2293, by decide, by decide, pass1423_2294, by decide, by decide, pass1423_2297, by decide, by decide, pass1423_2306, by decide, by decide, pass1423_2335, rfl⟩
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 23 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [320808526, 318844981, 318799168, 319158437, 320259467, 319677881, 319549375, 147094230, 147166767, 147105875, 147389078, 71051590, 67055881, 83599718, 97116219, 97457600, 148081189, 231340544], [1083872, 1093917, 1094151, 1092314, 1086681, 1089656, 1090314, 2615190, 2613984, 2614996, 2610288, 5642532, 5991344, 4768229, 4076363, 4061955, 2598781, 1601612],
  ![122800187566080, 1609890028336, 208206489600, 4863593580], 173600040945023903⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src901 : Request := ⟨⟨⟨6900,9626,2077,375939⟩,9849424459857920,234809190715807⟩,110,3,1,386045,23⟩
private theorem pass901_2293 : (Triangular src901) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass901_2294 : (Triangular src901) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass901_2297 : (Triangular src901) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass901_2305 : (Triangular src901) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass901_2327 : (Triangular src901) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass901_2388 : (Triangular src901) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover901 : Cover (Triangular src901) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass901_2293, by decide, by decide, pass901_2294, by decide, by decide, pass901_2297, by decide, by decide, pass901_2305, by decide, by decide, pass901_2327, by decide, by decide, pass901_2388, rfl⟩
def src902 : Request := ⟨⟨⟨10000,13953,3070,164837⟩,30428373265940480,1052197377228338⟩,110,3,1,386045,23⟩
private theorem pass902_2293 : (Triangular src902) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass902_2302 : (Triangular src902) 2302 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass902_2327 : (Triangular src902) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover902 : Cover (Triangular src902) 2389 2293 [2301,2326,2389] := by
  exact ⟨by decide, by decide, pass902_2293, by decide, by decide, pass902_2302, by decide, by decide, pass902_2327, rfl⟩
def src903 : Request := ⟨⟨⟨8300,11579,2498,1955459⟩,17139238515245056,491470625461013⟩,145,3,1,386045,23⟩
private theorem pass903_2293 : (Triangular src903) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass903_2294 : (Triangular src903) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass903_2297 : (Triangular src903) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass903_2305 : (Triangular src903) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass903_2327 : (Triangular src903) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass903_2388 : (Triangular src903) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover903 : Cover (Triangular src903) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass903_2293, by decide, by decide, pass903_2294, by decide, by decide, pass903_2297, by decide, by decide, pass903_2305, by decide, by decide, pass903_2327, by decide, by decide, pass903_2388, rfl⟩
def src904 : Request := ⟨⟨⟨825,1151,248,13899⟩,16903818182656,48256472894⟩,0,3,1,386045,24⟩
private theorem pass904_2293 : (Triangular src904) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass904_2301 : (Triangular src904) 2301 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass904_2325 : (Triangular src904) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover904 : Cover (Triangular src904) 2389 2293 [2300,2324,2389] := by
  exact ⟨by decide, by decide, pass904_2293, by decide, by decide, pass904_2301, by decide, by decide, pass904_2325, rfl⟩
def src905 : Request := ⟨⟨⟨1000,1395,307,13899⟩,30557599170560,105715278267⟩,1,3,1,386045,24⟩
private theorem pass905_2293 : (Triangular src905) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass905_2301 : (Triangular src905) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass905_2324 : (Triangular src905) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover905 : Cover (Triangular src905) 2389 2293 [2300,2323,2389] := by
  exact ⟨by decide, by decide, pass905_2293, by decide, by decide, pass905_2301, by decide, by decide, pass905_2324, rfl⟩
def src906 : Request := ⟨⟨⟨1000,1395,301,15636⟩,30103476895744,104105680031⟩,2,3,1,386045,24⟩
private theorem pass906_2293 : (Triangular src906) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass906_2294 : (Triangular src906) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass906_2297 : (Triangular src906) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass906_2306 : (Triangular src906) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass906_2332 : (Triangular src906) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover906 : Cover (Triangular src906) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass906_2293, by decide, by decide, pass906_2294, by decide, by decide, pass906_2297, by decide, by decide, pass906_2306, by decide, by decide, pass906_2332, rfl⟩
def src907 : Request := ⟨⟨⟨1200,1674,368,17590⟩,52718727069696,218807905514⟩,4,3,1,386045,24⟩
private theorem pass907_2293 : (Triangular src907) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass907_2301 : (Triangular src907) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass907_2324 : (Triangular src907) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover907 : Cover (Triangular src907) 2389 2293 [2300,2323,2389] := by
  exact ⟨by decide, by decide, pass907_2293, by decide, by decide, pass907_2301, by decide, by decide, pass907_2324, rfl⟩
def src908 : Request := ⟨⟨⟨1450,2023,445,22261⟩,92998964346880,466511127281⟩,8,3,1,386045,24⟩
private theorem pass908_2293 : (Triangular src908) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass908_2297 : (Triangular src908) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass908_2308 : (Triangular src908) 2308 2339 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass908_2340 : (Triangular src908) 2340 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover908 : Cover (Triangular src908) 2389 2293 [2296,2307,2339,2389] := by
  exact ⟨by decide, by decide, pass908_2293, by decide, by decide, pass908_2297, by decide, by decide, pass908_2308, by decide, by decide, pass908_2340, rfl⟩
def src909 : Request := ⟨⟨⟨2100,2930,645,40111⟩,282396798484480,2051392203643⟩,20,3,1,386045,24⟩
private theorem pass909_2293 : (Triangular src909) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass909_2297 : (Triangular src909) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass909_2308 : (Triangular src909) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass909_2339 : (Triangular src909) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover909 : Cover (Triangular src909) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass909_2293, by decide, by decide, pass909_2297, by decide, by decide, pass909_2308, by decide, by decide, pass909_2339, rfl⟩
def src914 : Request := ⟨⟨⟨5700,7953,1750,91474⟩,5637370734182400,111115710437454⟩,65,3,1,386045,24⟩
private theorem pass914_2293 : (Triangular src914) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass914_2296 : (Triangular src914) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass914_2304 : (Triangular src914) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass914_2326 : (Triangular src914) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass914_2387 : (Triangular src914) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover914 : Cover (Triangular src914) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass914_2293, by decide, by decide, pass914_2296, by decide, by decide, pass914_2304, by decide, by decide, pass914_2326, by decide, by decide, pass914_2387, rfl⟩
def src915 : Request := ⟨⟨⟨6900,9626,2118,297039⟩,9997036108906496,238415548481346⟩,110,3,1,386045,24⟩
private theorem pass915_2293 : (Triangular src915) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass915_2296 : (Triangular src915) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass915_2305 : (Triangular src915) 2305 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass915_2329 : (Triangular src915) 2329 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover915 : Cover (Triangular src915) 2389 2293 [2295,2304,2328,2389] := by
  exact ⟨by decide, by decide, pass915_2293, by decide, by decide, pass915_2296, by decide, by decide, pass915_2305, by decide, by decide, pass915_2329, rfl⟩
def src916 : Request := ⟨⟨⟨8300,11580,2548,164837⟩,17399709518790656,499263802703202⟩,110,3,1,386045,24⟩
private theorem pass916_2293 : (Triangular src916) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass916_2301 : (Triangular src916) 2301 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass916_2323 : (Triangular src916) 2323 2383 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass916_2384 : (Triangular src916) 2384 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover916 : Cover (Triangular src916) 2389 2293 [2300,2322,2383,2389] := by
  exact ⟨by decide, by decide, pass916_2293, by decide, by decide, pass916_2301, by decide, by decide, pass916_2323, by decide, by decide, pass916_2384, rfl⟩
def src917 : Request := ⟨⟨⟨10000,13953,3070,146522⟩,30428373265940480,1052197377228338⟩,110,3,1,386045,24⟩
private theorem pass917_2293 : (Triangular src917) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass917_2301 : (Triangular src917) 2301 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass917_2323 : (Triangular src917) 2323 2383 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass917_2384 : (Triangular src917) 2384 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover917 : Cover (Triangular src917) 2389 2293 [2300,2322,2383,2389] := by
  exact ⟨by decide, by decide, pass917_2293, by decide, by decide, pass917_2301, by decide, by decide, pass917_2323, by decide, by decide, pass917_2384, rfl⟩
def src918 : Request := ⟨⟨⟨8300,11579,2498,1545055⟩,17139238515245056,491470625461013⟩,145,3,1,386045,24⟩
private theorem pass918_2293 : (Triangular src918) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass918_2294 : (Triangular src918) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass918_2297 : (Triangular src918) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass918_2305 : (Triangular src918) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass918_2327 : (Triangular src918) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass918_2388 : (Triangular src918) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover918 : Cover (Triangular src918) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass918_2293, by decide, by decide, pass918_2294, by decide, by decide, pass918_2297, by decide, by decide, pass918_2305, by decide, by decide, pass918_2327, by decide, by decide, pass918_2388, rfl⟩
def src919 : Request := ⟨⟨⟨690,963,208,13899⟩,9921631092736,23724874690⟩,0,3,1,386045,25⟩
private theorem pass919_2293 : (Triangular src919) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass919_2298 : (Triangular src919) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass919_2313 : (Triangular src919) 2313 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass919_2360 : (Triangular src919) 2360 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover919 : Cover (Triangular src919) 2389 2293 [2297,2312,2359,2389] := by
  exact ⟨by decide, by decide, pass919_2293, by decide, by decide, pass919_2298, by decide, by decide, pass919_2313, by decide, by decide, pass919_2360, rfl⟩
def src920 : Request := ⟨⟨⟨825,1151,248,13899⟩,16903818182656,48256472894⟩,1,3,1,386045,25⟩
private theorem pass920_2293 : (Triangular src920) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass920_2297 : (Triangular src920) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass920_2309 : (Triangular src920) 2309 2345 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass920_2346 : (Triangular src920) 2346 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover920 : Cover (Triangular src920) 2389 2293 [2296,2308,2345,2389] := by
  exact ⟨by decide, by decide, pass920_2293, by decide, by decide, pass920_2297, by decide, by decide, pass920_2309, by decide, by decide, pass920_2346, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 23

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 23, 10, 75/100, 70/100, ![17508665600283, 1603815574884, 27487972590, 2390280510], 7643054076454978⟩
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

def data : NearCase 3 23 23 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons19.plan, Lower6960.Prefix6969MainCases.CubicSingletons19.price, Lower6960.Prefix6969MainCases.CubicSingletons19.valid, Lower6960.Prefix6969MainCases.CubicSingletons19.priced, Lower6960.Prefix6969MainCases.CubicSingletons19.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons19.plan, Lower6960.Prefix6969RescueData.CubicSingletons19.price, Lower6960.Prefix6969RescueData.CubicSingletons19.sources, Lower6960.Prefix6969RescueData.CubicSingletons19.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 214494392392839957 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 6 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [348553724, 347815214, 348197040, 348082630, 347231566, 346510877, 347483542, 346787961, 166902763, 166983885, 167637295, 167617990, 115999940, 74774265, 67242944, 91630721, 106576509, 106547194, 127364696, 174395108, 235638249], [991226, 993250, 992203, 992517, 994849, 996824, 994159, 996065, 2285848, 2284499, 2273635, 2273956, 3375324, 5346796, 5974392, 4333098, 3696863, 3697880, 3057632, 2179268, 1566277],
  ![125081495334180, 1605247166856, 212074424100, 4419759960], 192055099919228966⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src697 : Request := ⟨⟨⟨8300,11581,2498,475797⟩,17139238515245056,491743896877039⟩,85,3,1,386045,6⟩
private theorem pass697_2293 : (Triangular src697) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass697_2294 : (Triangular src697) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass697_2297 : (Triangular src697) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass697_2306 : (Triangular src697) 2306 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass697_2330 : (Triangular src697) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover697 : Cover (Triangular src697) 2389 2293 [2293,2296,2305,2329,2389] := by
  exact ⟨by decide, by decide, pass697_2293, by decide, by decide, pass697_2294, by decide, by decide, pass697_2297, by decide, by decide, pass697_2306, by decide, by decide, pass697_2330, rfl⟩
def src698 : Request := ⟨⟨⟨1000,1395,301,50764⟩,30103476895744,104105680031⟩,0,3,1,386045,7⟩
private theorem pass698_2293 : (Triangular src698) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass698_2302 : (Triangular src698) 2302 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass698_2328 : (Triangular src698) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover698 : Cover (Triangular src698) 2389 2293 [2301,2327,2389] := by
  exact ⟨by decide, by decide, pass698_2293, by decide, by decide, pass698_2302, by decide, by decide, pass698_2328, rfl⟩
def src699 : Request := ⟨⟨⟨1200,1674,361,57109⟩,51955677528064,215563369662⟩,2,3,1,386045,7⟩
private theorem pass699_2293 : (Triangular src699) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass699_2294 : (Triangular src699) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass699_2296 : (Triangular src699) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass699_2302 : (Triangular src699) 2302 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass699_2320 : (Triangular src699) 2320 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass699_2372 : (Triangular src699) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover699 : Cover (Triangular src699) 2389 2293 [2293,2295,2301,2319,2371,2389] := by
  exact ⟨by decide, by decide, pass699_2293, by decide, by decide, pass699_2294, by decide, by decide, pass699_2296, by decide, by decide, pass699_2302, by decide, by decide, pass699_2320, by decide, by decide, pass699_2372, rfl⟩
def src700 : Request := ⟨⟨⟨1200,1674,361,72277⟩,51955677528064,215563369662⟩,4,3,1,386045,7⟩
private theorem pass700_2293 : (Triangular src700) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass700_2296 : (Triangular src700) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass700_2305 : (Triangular src700) 2305 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass700_2331 : (Triangular src700) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover700 : Cover (Triangular src700) 2389 2293 [2295,2304,2330,2389] := by
  exact ⟨by decide, by decide, pass700_2293, by decide, by decide, pass700_2296, by decide, by decide, pass700_2305, by decide, by decide, pass700_2331, rfl⟩
def src701 : Request := ⟨⟨⟨1750,2442,527,102908⟩,161065121873920,975196209190⟩,10,3,1,386045,7⟩
private theorem pass701_2293 : (Triangular src701) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass701_2300 : (Triangular src701) 2300 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass701_2320 : (Triangular src701) 2320 2376 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass701_2377 : (Triangular src701) 2377 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover701 : Cover (Triangular src701) 2389 2293 [2299,2319,2376,2389] := by
  exact ⟨by decide, by decide, pass701_2293, by decide, by decide, pass701_2300, by decide, by decide, pass701_2320, by decide, by decide, pass701_2377, rfl⟩
def src702 : Request := ⟨⟨⟨2600,3628,770,130242⟩,521059839508480,4684185417862⟩,16,3,1,386045,7⟩
private theorem pass702_2293 : (Triangular src702) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass702_2297 : (Triangular src702) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass702_2308 : (Triangular src702) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass702_2339 : (Triangular src702) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover702 : Cover (Triangular src702) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass702_2293, by decide, by decide, pass702_2297, by decide, by decide, pass702_2308, by decide, by decide, pass702_2339, rfl⟩
def src703 : Request := ⟨⟨⟨3200,4465,963,164837⟩,983050615259136,10877088344236⟩,25,3,1,386045,7⟩
private theorem pass703_2293 : (Triangular src703) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass703_2294 : (Triangular src703) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass703_2296 : (Triangular src703) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass703_2302 : (Triangular src703) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass703_2319 : (Triangular src703) 2319 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass703_2367 : (Triangular src703) 2367 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover703 : Cover (Triangular src703) 2389 2293 [2293,2295,2301,2318,2366,2389] := by
  exact ⟨by decide, by decide, pass703_2293, by decide, by decide, pass703_2294, by decide, by decide, pass703_2296, by decide, by decide, pass703_2302, by decide, by decide, pass703_2319, by decide, by decide, pass703_2367, rfl⟩
def src704 : Request := ⟨⟨⟨3200,4464,963,422931⟩,983050615259136,10869251283552⟩,40,3,1,386045,7⟩
private theorem pass704_2293 : (Triangular src704) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass704_2297 : (Triangular src704) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass704_2308 : (Triangular src704) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass704_2339 : (Triangular src704) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover704 : Cover (Triangular src704) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass704_2293, by decide, by decide, pass704_2297, by decide, by decide, pass704_2308, by decide, by decide, pass704_2339, rfl⟩
def src705 : Request := ⟨⟨⟨6900,9628,2042,375939⟩,9722458861731840,231866079487253⟩,65,3,1,386045,7⟩
private theorem pass705_2293 : (Triangular src705) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass705_2294 : (Triangular src705) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass705_2297 : (Triangular src705) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass705_2306 : (Triangular src705) 2306 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass705_2331 : (Triangular src705) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover705 : Cover (Triangular src705) 2389 2293 [2293,2296,2305,2330,2389] := by
  exact ⟨by decide, by decide, pass705_2293, by decide, by decide, pass705_2294, by decide, by decide, pass705_2297, by decide, by decide, pass705_2306, by decide, by decide, pass705_2331, rfl⟩
def src706 : Request := ⟨⟨⟨10000,13953,3010,602179⟩,29974681586237440,1036125345444439⟩,110,3,1,386045,7⟩
private theorem pass706_2293 : (Triangular src706) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass706_2297 : (Triangular src706) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass706_2308 : (Triangular src706) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass706_2339 : (Triangular src706) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover706 : Cover (Triangular src706) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass706_2293, by decide, by decide, pass706_2297, by decide, by decide, pass706_2308, by decide, by decide, pass706_2339, rfl⟩
def src707 : Request := ⟨⟨⟨1000,1395,296,50764⟩,29722184515584,102755930405⟩,0,3,1,386045,8⟩
private theorem pass707_2293 : (Triangular src707) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass707_2300 : (Triangular src707) 2300 2320 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass707_2321 : (Triangular src707) 2321 2383 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass707_2384 : (Triangular src707) 2384 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover707 : Cover (Triangular src707) 2389 2293 [2299,2320,2383,2389] := by
  exact ⟨by decide, by decide, pass707_2293, by decide, by decide, pass707_2300, by decide, by decide, pass707_2321, by decide, by decide, pass707_2384, rfl⟩
def src708 : Request := ⟨⟨⟨1200,1674,361,50764⟩,51955677528064,215563369662⟩,1,3,1,386045,8⟩
private theorem pass708_2293 : (Triangular src708) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass708_2298 : (Triangular src708) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass708_2312 : (Triangular src708) 2312 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass708_2353 : (Triangular src708) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover708 : Cover (Triangular src708) 2389 2293 [2297,2311,2352,2389] := by
  exact ⟨by decide, by decide, pass708_2293, by decide, by decide, pass708_2298, by decide, by decide, pass708_2312, by decide, by decide, pass708_2353, rfl⟩
def src709 : Request := ⟨⟨⟨1200,1674,361,57109⟩,51955677528064,215563369662⟩,2,3,1,386045,8⟩
private theorem pass709_2293 : (Triangular src709) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass709_2301 : (Triangular src709) 2301 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass709_2325 : (Triangular src709) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover709 : Cover (Triangular src709) 2389 2293 [2300,2324,2389] := by
  exact ⟨by decide, by decide, pass709_2293, by decide, by decide, pass709_2301, by decide, by decide, pass709_2325, rfl⟩
def src710 : Request := ⟨⟨⟨1200,1674,361,72277⟩,51955677528064,215563369662⟩,4,3,1,386045,8⟩
private theorem pass710_2293 : (Triangular src710) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass710_2302 : (Triangular src710) 2302 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass710_2328 : (Triangular src710) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover710 : Cover (Triangular src710) 2389 2293 [2301,2327,2389] := by
  exact ⟨by decide, by decide, pass710_2293, by decide, by decide, pass710_2302, by decide, by decide, pass710_2328, rfl⟩
def src711 : Request := ⟨⟨⟨2100,2930,632,91474⟩,278060332482560,2019119590628⟩,10,3,1,386045,8⟩
private theorem pass711_2293 : (Triangular src711) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass711_2299 : (Triangular src711) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass711_2316 : (Triangular src711) 2316 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass711_2365 : (Triangular src711) 2365 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover711 : Cover (Triangular src711) 2389 2293 [2298,2315,2364,2389] := by
  exact ⟨by decide, by decide, pass711_2293, by decide, by decide, pass711_2299, by decide, by decide, pass711_2316, by decide, by decide, pass711_2365, rfl⟩
def src712 : Request := ⟨⟨⟨2600,3628,783,115771⟩,527755772952576,4745819470168⟩,16,3,1,386045,8⟩
private theorem pass712_2293 : (Triangular src712) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass712_2296 : (Triangular src712) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass712_2304 : (Triangular src712) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass712_2327 : (Triangular src712) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover712 : Cover (Triangular src712) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass712_2293, by decide, by decide, pass712_2296, by decide, by decide, pass712_2304, by decide, by decide, pass712_2327, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 6

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 6, 10, 95/100, 80/100, ![1111348076517, 391667930784, 5834730978, 1944925314], 8743254675041301⟩
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

def data : NearCase 3 6 6 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons2.plan, Lower6960.Prefix6969MainCases.CubicSingletons2.price, Lower6960.Prefix6969MainCases.CubicSingletons2.valid, Lower6960.Prefix6969MainCases.CubicSingletons2.priced, Lower6960.Prefix6969MainCases.CubicSingletons2.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons2.plan, Lower6960.Prefix6969RescueData.CubicSingletons2.price, Lower6960.Prefix6969RescueData.CubicSingletons2.sources, Lower6960.Prefix6969RescueData.CubicSingletons2.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 219990829202653859 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 24 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [320143882, 319861335, 320154543, 319392088, 317845377, 319089361, 318341639, 146815879, 146915063, 146867026, 146923616, 69875364, 69805957, 96925597, 96937676, 113163740, 168238037, 230660451], [1087272, 1088718, 1087218, 1091118, 1099031, 1092667, 1096492, 2620503, 2618329, 2619382, 2618141, 5736016, 5742126, 4084408, 4083898, 3468192, 2263647, 1607204],
  ![122439180599820, 1610624948364, 207594405900, 4860445520], 172581719273848798⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 24

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 24, 10, 75/100, 70/100, ![14435495216650, 1287813063045, 28683102100, 2390280510], 6262576189329055⟩
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

def data : NearCase 3 24 24 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons20.plan, Lower6960.Prefix6969MainCases.CubicSingletons20.price, Lower6960.Prefix6969MainCases.CubicSingletons20.valid, Lower6960.Prefix6969MainCases.CubicSingletons20.priced, Lower6960.Prefix6969MainCases.CubicSingletons20.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons20.plan, Lower6960.Prefix6969RescueData.CubicSingletons20.price, Lower6960.Prefix6969RescueData.CubicSingletons20.sources, Lower6960.Prefix6969RescueData.CubicSingletons20.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 213373711705749008 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 25 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [318560284, 318371886, 318238834, 317398389, 318353654, 317203932, 316262926, 147268297, 147357966, 147330602, 147319545, 70847491, 71022797, 83657280, 96809574, 96794715, 147216329, 230680829], [1095374, 1096337, 1097018, 1101318, 1096431, 1102312, 1107126, 2612296, 2610805, 2611260, 2611444, 5658754, 5644821, 4764811, 4089305, 4089932, 2613160, 1607036],
  ![122449997649780, 1610602691956, 207612746100, 4867019080], 171702813380571846⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src921 : Request := ⟨⟨⟨1000,1395,301,17590⟩,30103476895744,104105680031⟩,4,3,1,386045,25⟩
private theorem pass921_2293 : (Triangular src921) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass921_2294 : (Triangular src921) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass921_2297 : (Triangular src921) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass921_2306 : (Triangular src921) 2306 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass921_2333 : (Triangular src921) 2333 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover921 : Cover (Triangular src921) 2389 2293 [2293,2296,2305,2332,2389] := by
  exact ⟨by decide, by decide, pass921_2293, by decide, by decide, pass921_2294, by decide, by decide, pass921_2297, by decide, by decide, pass921_2306, by decide, by decide, pass921_2333, rfl⟩
def src922 : Request := ⟨⟨⟨1200,1674,368,22261⟩,52718727069696,218807905514⟩,8,3,1,386045,25⟩
private theorem pass922_2293 : (Triangular src922) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass922_2294 : (Triangular src922) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass922_2297 : (Triangular src922) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass922_2306 : (Triangular src922) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass922_2332 : (Triangular src922) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover922 : Cover (Triangular src922) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass922_2293, by decide, by decide, pass922_2294, by decide, by decide, pass922_2297, by decide, by decide, pass922_2306, by decide, by decide, pass922_2332, rfl⟩
def src923 : Request := ⟨⟨⟨2100,2930,645,35655⟩,282396798484480,2051392203643⟩,20,3,1,386045,25⟩
private theorem pass923_2293 : (Triangular src923) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass923_2299 : (Triangular src923) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass923_2316 : (Triangular src923) 2316 2363 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass923_2364 : (Triangular src923) 2364 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover923 : Cover (Triangular src923) 2389 2293 [2298,2315,2363,2389] := by
  exact ⟨by decide, by decide, pass923_2293, by decide, by decide, pass923_2299, by decide, by decide, pass923_2316, by decide, by decide, pass923_2364, rfl⟩
def src926 : Request := ⟨⟨⟨3950,5511,1213,72277⟩,1877062482395136,25637257621145⟩,50,3,1,386045,25⟩
private theorem pass926_2293 : (Triangular src926) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass926_2295 : (Triangular src926) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass926_2300 : (Triangular src926) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass926_2314 : (Triangular src926) 2314 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass926_2353 : (Triangular src926) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover926 : Cover (Triangular src926) 2389 2293 [2294,2299,2313,2352,2389] := by
  exact ⟨by decide, by decide, pass926_2293, by decide, by decide, pass926_2295, by decide, by decide, pass926_2300, by decide, by decide, pass926_2314, by decide, by decide, pass926_2353, rfl⟩
def src927 : Request := ⟨⟨⟨5700,7952,1750,146522⟩,5637370734182400,111070724916873⟩,85,3,1,386045,25⟩
private theorem pass927_2293 : (Triangular src927) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass927_2297 : (Triangular src927) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass927_2308 : (Triangular src927) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass927_2339 : (Triangular src927) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover927 : Cover (Triangular src927) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass927_2293, by decide, by decide, pass927_2297, by decide, by decide, pass927_2308, by decide, by decide, pass927_2339, rfl⟩
def src928 : Request := ⟨⟨⟨6900,9626,2118,234698⟩,9997036108906496,238415548481346⟩,110,3,1,386045,25⟩
private theorem pass928_2293 : (Triangular src928) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass928_2298 : (Triangular src928) 2298 2310 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass928_2311 : (Triangular src928) 2311 2346 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass928_2347 : (Triangular src928) 2347 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover928 : Cover (Triangular src928) 2389 2293 [2297,2310,2346,2389] := by
  exact ⟨by decide, by decide, pass928_2293, by decide, by decide, pass928_2298, by decide, by decide, pass928_2311, by decide, by decide, pass928_2347, rfl⟩
def src929 : Request := ⟨⟨⟨10000,13953,3070,130242⟩,30428373265940480,1052197377228338⟩,110,3,1,386045,25⟩
private theorem pass929_2293 : (Triangular src929) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass929_2299 : (Triangular src929) 2299 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass929_2315 : (Triangular src929) 2315 2358 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass929_2359 : (Triangular src929) 2359 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover929 : Cover (Triangular src929) 2389 2293 [2298,2314,2358,2389] := by
  exact ⟨by decide, by decide, pass929_2293, by decide, by decide, pass929_2299, by decide, by decide, pass929_2315, by decide, by decide, pass929_2359, rfl⟩
def src930 : Request := ⟨⟨⟨8300,11579,2498,964572⟩,17139238515245056,491470625461013⟩,145,3,1,386045,25⟩
private theorem pass930_2293 : (Triangular src930) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass930_2294 : (Triangular src930) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass930_2297 : (Triangular src930) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass930_2305 : (Triangular src930) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass930_2327 : (Triangular src930) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass930_2388 : (Triangular src930) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover930 : Cover (Triangular src930) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass930_2293, by decide, by decide, pass930_2294, by decide, by decide, pass930_2297, by decide, by decide, pass930_2305, by decide, by decide, pass930_2327, by decide, by decide, pass930_2388, rfl⟩
def src931 : Request := ⟨⟨⟨690,963,212,10983⟩,10065769922560,24078187611⟩,0,3,1,386045,26⟩
private theorem pass931_2293 : (Triangular src931) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass931_2296 : (Triangular src931) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass931_2305 : (Triangular src931) 2305 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass931_2333 : (Triangular src931) 2333 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover931 : Cover (Triangular src931) 2389 2293 [2295,2304,2332,2389] := by
  exact ⟨by decide, by decide, pass931_2293, by decide, by decide, pass931_2296, by decide, by decide, pass931_2305, by decide, by decide, pass931_2333, rfl⟩
def src932 : Request := ⟨⟨⟨825,1151,248,12355⟩,16903818182656,48256472894⟩,1,3,1,386045,26⟩
private theorem pass932_2293 : (Triangular src932) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass932_2298 : (Triangular src932) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass932_2313 : (Triangular src932) 2313 2357 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass932_2358 : (Triangular src932) 2358 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover932 : Cover (Triangular src932) 2389 2293 [2297,2312,2357,2389] := by
  exact ⟨by decide, by decide, pass932_2293, by decide, by decide, pass932_2298, by decide, by decide, pass932_2313, by decide, by decide, pass932_2358, rfl⟩
def src933 : Request := ⟨⟨⟨825,1151,253,13899⟩,17161575202816,49010625289⟩,2,3,1,386045,26⟩
private theorem pass933_2293 : (Triangular src933) 2293 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass933_2305 : (Triangular src933) 2305 2340 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass933_2341 : (Triangular src933) 2341 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover933 : Cover (Triangular src933) 2389 2293 [2304,2340,2389] := by
  exact ⟨by decide, by decide, pass933_2293, by decide, by decide, pass933_2305, by decide, by decide, pass933_2341, rfl⟩
def src934 : Request := ⟨⟨⟨1000,1395,301,13899⟩,30103476895744,104105680031⟩,3,3,1,386045,26⟩
private theorem pass934_2293 : (Triangular src934) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass934_2294 : (Triangular src934) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass934_2297 : (Triangular src934) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass934_2305 : (Triangular src934) 2305 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass934_2329 : (Triangular src934) 2329 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover934 : Cover (Triangular src934) 2389 2293 [2293,2296,2304,2328,2389] := by
  exact ⟨by decide, by decide, pass934_2293, by decide, by decide, pass934_2294, by decide, by decide, pass934_2297, by decide, by decide, pass934_2305, by decide, by decide, pass934_2329, rfl⟩
def src935 : Request := ⟨⟨⟨1000,1395,301,15636⟩,30103476895744,104105680031⟩,4,3,1,386045,26⟩
private theorem pass935_2293 : (Triangular src935) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass935_2296 : (Triangular src935) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass935_2304 : (Triangular src935) 2304 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass935_2328 : (Triangular src935) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover935 : Cover (Triangular src935) 2389 2293 [2295,2303,2327,2389] := by
  exact ⟨by decide, by decide, pass935_2293, by decide, by decide, pass935_2296, by decide, by decide, pass935_2304, by decide, by decide, pass935_2328, rfl⟩
def src936 : Request := ⟨⟨⟨1000,1395,307,19788⟩,30557599170560,105715278267⟩,6,3,1,386045,26⟩
private theorem pass936_2293 : (Triangular src936) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass936_2297 : (Triangular src936) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass936_2309 : (Triangular src936) 2309 2343 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass936_2344 : (Triangular src936) 2344 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover936 : Cover (Triangular src936) 2389 2293 [2296,2308,2343,2389] := by
  exact ⟨by decide, by decide, pass936_2293, by decide, by decide, pass936_2297, by decide, by decide, pass936_2309, by decide, by decide, pass936_2344, rfl⟩
def src937 : Request := ⟨⟨⟨1200,1674,368,19788⟩,52718727069696,218807905514⟩,8,3,1,386045,26⟩
private theorem pass937_2293 : (Triangular src937) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass937_2298 : (Triangular src937) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass937_2312 : (Triangular src937) 2312 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass937_2353 : (Triangular src937) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover937 : Cover (Triangular src937) 2389 2293 [2297,2311,2352,2389] := by
  exact ⟨by decide, by decide, pass937_2293, by decide, by decide, pass937_2298, by decide, by decide, pass937_2312, by decide, by decide, pass937_2353, rfl⟩
def src938 : Request := ⟨⟨⟨2100,2930,645,31694⟩,282396798484480,2051392203643⟩,20,3,1,386045,26⟩
private theorem pass938_2293 : (Triangular src938) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass938_2302 : (Triangular src938) 2302 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass938_2327 : (Triangular src938) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover938 : Cover (Triangular src938) 2389 2293 [2301,2326,2389] := by
  exact ⟨by decide, by decide, pass938_2293, by decide, by decide, pass938_2302, by decide, by decide, pass938_2327, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 25

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 25, 10, 80/100, 80/100, ![9387526260756, 839388232359, 29878231610, 2390280510], 4433412602674921⟩
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

def data : NearCase 3 25 25 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons21.plan, Lower6960.Prefix6969MainCases.CubicSingletons21.price, Lower6960.Prefix6969MainCases.CubicSingletons21.valid, Lower6960.Prefix6969MainCases.CubicSingletons21.priced, Lower6960.Prefix6969MainCases.CubicSingletons21.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons21.plan, Lower6960.Prefix6969RescueData.CubicSingletons21.price, Lower6960.Prefix6969RescueData.CubicSingletons21.sources, Lower6960.Prefix6969RescueData.CubicSingletons21.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 212462951588406732 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 26 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [316872722, 316244349, 316798935, 316582257, 315486706, 314634250, 315693019, 146097610, 146095435, 146065265, 146007353, 70444877, 70460683, 82187542, 95985255, 95184785, 146844197, 230359323], [1104007, 1107221, 1104384, 1105493, 1111097, 1115458, 1110042, 2636251, 2636299, 2636960, 2638230, 5690752, 5689496, 4852083, 4124095, 4157879, 2619883, 1609680],
  ![122279335834860, 1610950354332, 207323390700, 4949124660], 170775917923573689⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src941 : Request := ⟨⟨⟨4800,6697,1474,81311⟩,3367547627110400,55891290082931⟩,65,3,1,386045,26⟩
private theorem pass941_2293 : (Triangular src941) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass941_2296 : (Triangular src941) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass941_2304 : (Triangular src941) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass941_2327 : (Triangular src941) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover941 : Cover (Triangular src941) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass941_2293, by decide, by decide, pass941_2296, by decide, by decide, pass941_2304, by decide, by decide, pass941_2327, rfl⟩
def src942 : Request := ⟨⟨⟨8300,11579,2548,475797⟩,17399709518790656,499124969898998⟩,145,3,1,386045,26⟩
private theorem pass942_2293 : (Triangular src942) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass942_2294 : (Triangular src942) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass942_2296 : (Triangular src942) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass942_2302 : (Triangular src942) 2302 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass942_2318 : (Triangular src942) 2318 2361 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass942_2362 : (Triangular src942) 2362 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover942 : Cover (Triangular src942) 2389 2293 [2293,2295,2301,2317,2361,2389] := by
  exact ⟨by decide, by decide, pass942_2293, by decide, by decide, pass942_2294, by decide, by decide, pass942_2296, by decide, by decide, pass942_2302, by decide, by decide, pass942_2318, by decide, by decide, pass942_2362, rfl⟩
def src943 : Request := ⟨⟨⟨10000,13952,3070,164837⟩,30428373265940480,1051954539834997⟩,145,3,1,386045,26⟩
private theorem pass943_2293 : (Triangular src943) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass943_2296 : (Triangular src943) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass943_2304 : (Triangular src943) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass943_2326 : (Triangular src943) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass943_2387 : (Triangular src943) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover943 : Cover (Triangular src943) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass943_2293, by decide, by decide, pass943_2296, by decide, by decide, pass943_2304, by decide, by decide, pass943_2326, by decide, by decide, pass943_2387, rfl⟩
def src944 : Request := ⟨⟨⟨690,963,212,9763⟩,10065769922560,24078187611⟩,0,3,1,386045,27⟩
private theorem pass944_2293 : (Triangular src944) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass944_2299 : (Triangular src944) 2299 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass944_2317 : (Triangular src944) 2317 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass944_2372 : (Triangular src944) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover944 : Cover (Triangular src944) 2389 2293 [2298,2316,2371,2389] := by
  exact ⟨by decide, by decide, pass944_2293, by decide, by decide, pass944_2299, by decide, by decide, pass944_2317, by decide, by decide, pass944_2372, rfl⟩
def src945 : Request := ⟨⟨⟨825,1151,248,10983⟩,16903818182656,48256472894⟩,1,3,1,386045,27⟩
private theorem pass945_2293 : (Triangular src945) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass945_2296 : (Triangular src945) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass945_2305 : (Triangular src945) 2305 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass945_2333 : (Triangular src945) 2333 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover945 : Cover (Triangular src945) 2389 2293 [2295,2304,2332,2389] := by
  exact ⟨by decide, by decide, pass945_2293, by decide, by decide, pass945_2296, by decide, by decide, pass945_2305, by decide, by decide, pass945_2333, rfl⟩
def src946 : Request := ⟨⟨⟨825,1151,248,12355⟩,16903818182656,48256472894⟩,2,3,1,386045,27⟩
private theorem pass946_2293 : (Triangular src946) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass946_2295 : (Triangular src946) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass946_2301 : (Triangular src946) 2301 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass946_2319 : (Triangular src946) 2319 2373 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass946_2374 : (Triangular src946) 2374 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover946 : Cover (Triangular src946) 2389 2293 [2294,2300,2318,2373,2389] := by
  exact ⟨by decide, by decide, pass946_2293, by decide, by decide, pass946_2295, by decide, by decide, pass946_2301, by decide, by decide, pass946_2319, by decide, by decide, pass946_2374, rfl⟩
def src947 : Request := ⟨⟨⟨1000,1395,301,13899⟩,30103476895744,104105680031⟩,4,3,1,386045,27⟩
private theorem pass947_2293 : (Triangular src947) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass947_2296 : (Triangular src947) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass947_2305 : (Triangular src947) 2305 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass947_2331 : (Triangular src947) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover947 : Cover (Triangular src947) 2389 2293 [2295,2304,2330,2389] := by
  exact ⟨by decide, by decide, pass947_2293, by decide, by decide, pass947_2296, by decide, by decide, pass947_2305, by decide, by decide, pass947_2331, rfl⟩
def src948 : Request := ⟨⟨⟨1000,1395,307,17590⟩,30557599170560,105715278267⟩,6,3,1,386045,27⟩
private theorem pass948_2293 : (Triangular src948) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass948_2303 : (Triangular src948) 2303 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass948_2333 : (Triangular src948) 2333 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover948 : Cover (Triangular src948) 2389 2293 [2302,2332,2389] := by
  exact ⟨by decide, by decide, pass948_2293, by decide, by decide, pass948_2303, by decide, by decide, pass948_2333, rfl⟩
def src949 : Request := ⟨⟨⟨1200,1674,368,17590⟩,52718727069696,218807905514⟩,8,3,1,386045,27⟩
private theorem pass949_2293 : (Triangular src949) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass949_2301 : (Triangular src949) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass949_2324 : (Triangular src949) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover949 : Cover (Triangular src949) 2389 2293 [2300,2323,2389] := by
  exact ⟨by decide, by decide, pass949_2293, by decide, by decide, pass949_2301, by decide, by decide, pass949_2324, rfl⟩
def src950 : Request := ⟨⟨⟨1450,2023,445,22261⟩,92998964346880,466511127281⟩,13,3,1,386045,27⟩
private theorem pass950_2293 : (Triangular src950) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass950_2294 : (Triangular src950) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass950_2297 : (Triangular src950) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass950_2305 : (Triangular src950) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass950_2328 : (Triangular src950) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover950 : Cover (Triangular src950) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass950_2293, by decide, by decide, pass950_2294, by decide, by decide, pass950_2297, by decide, by decide, pass950_2305, by decide, by decide, pass950_2328, rfl⟩
def src951 : Request := ⟨⟨⟨2600,3627,783,45124⟩,527755772952576,4741611634368⟩,32,3,1,386045,27⟩
private theorem pass951_2293 : (Triangular src951) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass951_2294 : (Triangular src951) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass951_2297 : (Triangular src951) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass951_2305 : (Triangular src951) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass951_2328 : (Triangular src951) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover951 : Cover (Triangular src951) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass951_2293, by decide, by decide, pass951_2294, by decide, by decide, pass951_2297, by decide, by decide, pass951_2305, by decide, by decide, pass951_2328, rfl⟩
def src954 : Request := ⟨⟨⟨4800,6697,1474,72277⟩,3367547627110400,55891290082931⟩,65,3,1,386045,27⟩
private theorem pass954_2293 : (Triangular src954) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass954_2300 : (Triangular src954) 2300 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass954_2319 : (Triangular src954) 2319 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass954_2372 : (Triangular src954) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover954 : Cover (Triangular src954) 2389 2293 [2299,2318,2371,2389] := by
  exact ⟨by decide, by decide, pass954_2293, by decide, by decide, pass954_2300, by decide, by decide, pass954_2319, by decide, by decide, pass954_2372, rfl⟩
def src955 : Request := ⟨⟨⟨8300,11579,2548,264035⟩,17399709518790656,499124969898998⟩,145,3,1,386045,27⟩
private theorem pass955_2293 : (Triangular src955) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass955_2294 : (Triangular src955) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass955_2297 : (Triangular src955) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass955_2305 : (Triangular src955) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass955_2327 : (Triangular src955) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass955_2388 : (Triangular src955) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover955 : Cover (Triangular src955) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass955_2293, by decide, by decide, pass955_2294, by decide, by decide, pass955_2297, by decide, by decide, pass955_2305, by decide, by decide, pass955_2327, by decide, by decide, pass955_2388, rfl⟩
def src956 : Request := ⟨⟨⟨10000,13952,3070,146522⟩,30428373265940480,1051954539834997⟩,145,3,1,386045,27⟩
private theorem pass956_2293 : (Triangular src956) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass956_2299 : (Triangular src956) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass956_2316 : (Triangular src956) 2316 2361 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass956_2362 : (Triangular src956) 2362 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover956 : Cover (Triangular src956) 2389 2293 [2298,2315,2361,2389] := by
  exact ⟨by decide, by decide, pass956_2293, by decide, by decide, pass956_2299, by decide, by decide, pass956_2316, by decide, by decide, pass956_2362, rfl⟩
def src957 : Request := ⟨⟨⟨690,963,212,8679⟩,10065769922560,24078187611⟩,0,3,1,386045,28⟩
private theorem pass957_2293 : (Triangular src957) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass957_2299 : (Triangular src957) 2299 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass957_2318 : (Triangular src957) 2318 2375 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass957_2376 : (Triangular src957) 2376 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover957 : Cover (Triangular src957) 2389 2293 [2298,2317,2375,2389] := by
  exact ⟨by decide, by decide, pass957_2293, by decide, by decide, pass957_2299, by decide, by decide, pass957_2318, by decide, by decide, pass957_2376, rfl⟩
def src958 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,1,3,1,386045,28⟩
private theorem pass958_2293 : (Triangular src958) 2293 2309 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass958_2310 : (Triangular src958) 2310 2360 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass958_2361 : (Triangular src958) 2361 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover958 : Cover (Triangular src958) 2389 2293 [2309,2360,2389] := by
  exact ⟨by decide, by decide, pass958_2293, by decide, by decide, pass958_2310, by decide, by decide, pass958_2361, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 26

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 26, 10, 75/100, 70/100, ![4815834527952, 461860527717, 31073361120, 2390280510], 2915202721440075⟩
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

def data : NearCase 3 26 26 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons22.plan, Lower6960.Prefix6969MainCases.CubicSingletons22.price, Lower6960.Prefix6969MainCases.CubicSingletons22.valid, Lower6960.Prefix6969MainCases.CubicSingletons22.priced, Lower6960.Prefix6969MainCases.CubicSingletons22.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons22.plan, Lower6960.Prefix6969RescueData.CubicSingletons22.price, Lower6960.Prefix6969RescueData.CubicSingletons22.sources, Lower6960.Prefix6969RescueData.CubicSingletons22.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 210447544593432045 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 27 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [315519023, 313810136, 313831322, 313978013, 313751880, 314280867, 313808556, 146672199, 146460250, 146664988, 146587349, 72339958, 72750215, 81663118, 92851341, 93162524, 119591000, 166621412, 229695931], [1110932, 1119674, 1119566, 1118815, 1119972, 1117266, 1119682, 2623654, 2628301, 2623812, 2625514, 5540136, 5507530, 4883223, 4271546, 4255854, 3274939, 2290525, 1615134],
  ![121927194093420, 1611666867284, 206726337900, 5083139740], 169623273266097723⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 27

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 27, 10, 75/100, 70/100, ![2775247593780, 300499812903, 32268487560, 2390280510], 2158048694829431⟩
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

def data : NearCase 3 27 27 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons23.plan, Lower6960.Prefix6969MainCases.CubicSingletons23.price, Lower6960.Prefix6969MainCases.CubicSingletons23.valid, Lower6960.Prefix6969MainCases.CubicSingletons23.priced, Lower6960.Prefix6969MainCases.CubicSingletons23.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons23.plan, Lower6960.Prefix6969RescueData.CubicSingletons23.price, Lower6960.Prefix6969RescueData.CubicSingletons23.sources, Lower6960.Prefix6969RescueData.CubicSingletons23.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 209300732176453565 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 28 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [314065844, 313056431, 313739106, 313423910, 312550243, 311771873, 312234714, 146566664, 146522235, 146798929, 104439358, 74576199, 75486602, 94569194, 94633016, 119635706, 166210877, 229382775], [1118366, 1123530, 1120038, 1121650, 1126120, 1130102, 1127734, 2625967, 2626942, 2620875, 3771052, 5362406, 5297600, 4184920, 4181701, 3273689, 2297351, 1617709],
  ![121760964625500, 1612005324480, 206444497500, 4980054800], 168996151483309938⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src959 : Request := ⟨⟨⟨825,1151,248,10983⟩,16903818182656,48256472894⟩,2,3,1,386045,28⟩
private theorem pass959_2293 : (Triangular src959) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass959_2295 : (Triangular src959) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass959_2301 : (Triangular src959) 2301 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass959_2319 : (Triangular src959) 2319 2373 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass959_2374 : (Triangular src959) 2374 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover959 : Cover (Triangular src959) 2389 2293 [2294,2300,2318,2373,2389] := by
  exact ⟨by decide, by decide, pass959_2293, by decide, by decide, pass959_2295, by decide, by decide, pass959_2301, by decide, by decide, pass959_2319, by decide, by decide, pass959_2374, rfl⟩
def src960 : Request := ⟨⟨⟨825,1151,253,12355⟩,17161575202816,49010625289⟩,3,3,1,386045,28⟩
private theorem pass960_2293 : (Triangular src960) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass960_2306 : (Triangular src960) 2306 2344 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass960_2345 : (Triangular src960) 2345 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover960 : Cover (Triangular src960) 2389 2293 [2305,2344,2389] := by
  exact ⟨by decide, by decide, pass960_2293, by decide, by decide, pass960_2306, by decide, by decide, pass960_2345, rfl⟩
def src961 : Request := ⟨⟨⟨825,1151,253,13899⟩,17161575202816,49010625289⟩,4,3,1,386045,28⟩
private theorem pass961_2293 : (Triangular src961) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass961_2297 : (Triangular src961) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass961_2309 : (Triangular src961) 2309 2344 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass961_2345 : (Triangular src961) 2345 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover961 : Cover (Triangular src961) 2389 2293 [2296,2308,2344,2389] := by
  exact ⟨by decide, by decide, pass961_2293, by decide, by decide, pass961_2297, by decide, by decide, pass961_2309, by decide, by decide, pass961_2345, rfl⟩
def src962 : Request := ⟨⟨⟨1000,1395,307,13899⟩,30557599170560,105715278267⟩,6,3,1,386045,28⟩
private theorem pass962_2293 : (Triangular src962) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass962_2294 : (Triangular src962) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass962_2297 : (Triangular src962) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass962_2306 : (Triangular src962) 2306 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass962_2333 : (Triangular src962) 2333 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover962 : Cover (Triangular src962) 2389 2293 [2293,2296,2305,2332,2389] := by
  exact ⟨by decide, by decide, pass962_2293, by decide, by decide, pass962_2294, by decide, by decide, pass962_2297, by decide, by decide, pass962_2306, by decide, by decide, pass962_2333, rfl⟩
def src963 : Request := ⟨⟨⟨1200,1674,368,15636⟩,52718727069696,218807905514⟩,8,3,1,386045,28⟩
private theorem pass963_2293 : (Triangular src963) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass963_2302 : (Triangular src963) 2302 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass963_2329 : (Triangular src963) 2329 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover963 : Cover (Triangular src963) 2389 2293 [2301,2328,2389] := by
  exact ⟨by decide, by decide, pass963_2293, by decide, by decide, pass963_2302, by decide, by decide, pass963_2329, rfl⟩
def src964 : Request := ⟨⟨⟨1450,2023,445,19788⟩,92998964346880,466511127281⟩,13,3,1,386045,28⟩
private theorem pass964_2293 : (Triangular src964) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass964_2296 : (Triangular src964) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass964_2305 : (Triangular src964) 2305 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass964_2331 : (Triangular src964) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover964 : Cover (Triangular src964) 2389 2293 [2295,2304,2330,2389] := by
  exact ⟨by decide, by decide, pass964_2293, by decide, by decide, pass964_2296, by decide, by decide, pass964_2305, by decide, by decide, pass964_2331, rfl⟩
def src965 : Request := ⟨⟨⟨2600,3627,798,35655⟩,535425056505856,4812227595495⟩,32,3,1,386045,28⟩
private theorem pass965_2293 : (Triangular src965) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass965_2295 : (Triangular src965) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass965_2301 : (Triangular src965) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass965_2318 : (Triangular src965) 2318 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass965_2365 : (Triangular src965) 2365 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover965 : Cover (Triangular src965) 2389 2293 [2294,2300,2317,2364,2389] := by
  exact ⟨by decide, by decide, pass965_2293, by decide, by decide, pass965_2295, by decide, by decide, pass965_2301, by decide, by decide, pass965_2318, by decide, by decide, pass965_2365, rfl⟩
def src968 : Request := ⟨⟨⟨8300,11579,2548,185441⟩,17399709518790656,499124969898998⟩,145,3,1,386045,28⟩
private theorem pass968_2293 : (Triangular src968) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass968_2296 : (Triangular src968) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass968_2304 : (Triangular src968) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass968_2326 : (Triangular src968) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass968_2387 : (Triangular src968) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover968 : Cover (Triangular src968) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass968_2293, by decide, by decide, pass968_2296, by decide, by decide, pass968_2304, by decide, by decide, pass968_2326, by decide, by decide, pass968_2387, rfl⟩
def src969 : Request := ⟨⟨⟨10000,13952,3070,130242⟩,30428373265940480,1051954539834997⟩,145,3,1,386045,28⟩
private theorem pass969_2293 : (Triangular src969) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass969_2300 : (Triangular src969) 2300 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass969_2320 : (Triangular src969) 2320 2374 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass969_2375 : (Triangular src969) 2375 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover969 : Cover (Triangular src969) 2389 2293 [2299,2319,2374,2389] := by
  exact ⟨by decide, by decide, pass969_2293, by decide, by decide, pass969_2300, by decide, by decide, pass969_2320, by decide, by decide, pass969_2375, rfl⟩
def src970 : Request := ⟨⟨⟨690,963,212,7715⟩,10065769922560,24078187611⟩,0,3,1,386045,29⟩
private theorem pass970_2293 : (Triangular src970) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass970_2296 : (Triangular src970) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass970_2305 : (Triangular src970) 2305 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass970_2332 : (Triangular src970) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover970 : Cover (Triangular src970) 2389 2293 [2295,2304,2331,2389] := by
  exact ⟨by decide, by decide, pass970_2293, by decide, by decide, pass970_2296, by decide, by decide, pass970_2305, by decide, by decide, pass970_2332, rfl⟩
def src971 : Request := ⟨⟨⟨690,963,212,8679⟩,10065769922560,24078187611⟩,1,3,1,386045,29⟩
private theorem pass971_2293 : (Triangular src971) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass971_2294 : (Triangular src971) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass971_2297 : (Triangular src971) 2297 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass971_2307 : (Triangular src971) 2307 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass971_2337 : (Triangular src971) 2337 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover971 : Cover (Triangular src971) 2389 2293 [2293,2296,2306,2336,2389] := by
  exact ⟨by decide, by decide, pass971_2293, by decide, by decide, pass971_2294, by decide, by decide, pass971_2297, by decide, by decide, pass971_2307, by decide, by decide, pass971_2337, rfl⟩
def src972 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,2,3,1,386045,29⟩
private theorem pass972_2293 : (Triangular src972) 2293 2309 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass972_2310 : (Triangular src972) 2310 2360 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass972_2361 : (Triangular src972) 2361 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover972 : Cover (Triangular src972) 2389 2293 [2309,2360,2389] := by
  exact ⟨by decide, by decide, pass972_2293, by decide, by decide, pass972_2310, by decide, by decide, pass972_2361, rfl⟩
def src973 : Request := ⟨⟨⟨825,1151,253,10983⟩,17161575202816,49010625289⟩,3,3,1,386045,29⟩
private theorem pass973_2293 : (Triangular src973) 2293 2309 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass973_2310 : (Triangular src973) 2310 2360 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass973_2361 : (Triangular src973) 2361 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover973 : Cover (Triangular src973) 2389 2293 [2309,2360,2389] := by
  exact ⟨by decide, by decide, pass973_2293, by decide, by decide, pass973_2310, by decide, by decide, pass973_2361, rfl⟩
def src974 : Request := ⟨⟨⟨1000,1395,307,12355⟩,30557599170560,105715278267⟩,6,3,1,386045,29⟩
private theorem pass974_2293 : (Triangular src974) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass974_2295 : (Triangular src974) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass974_2301 : (Triangular src974) 2301 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass974_2319 : (Triangular src974) 2319 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass974_2372 : (Triangular src974) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover974 : Cover (Triangular src974) 2389 2293 [2294,2300,2318,2371,2389] := by
  exact ⟨by decide, by decide, pass974_2293, by decide, by decide, pass974_2295, by decide, by decide, pass974_2301, by decide, by decide, pass974_2319, by decide, by decide, pass974_2372, rfl⟩
def src975 : Request := ⟨⟨⟨1450,2023,445,22261⟩,92998964346880,466511127281⟩,16,3,1,386045,29⟩
private theorem pass975_2293 : (Triangular src975) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass975_2294 : (Triangular src975) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass975_2297 : (Triangular src975) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass975_2306 : (Triangular src975) 2306 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass975_2332 : (Triangular src975) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover975 : Cover (Triangular src975) 2389 2293 [2293,2296,2305,2331,2389] := by
  exact ⟨by decide, by decide, pass975_2293, by decide, by decide, pass975_2294, by decide, by decide, pass975_2297, by decide, by decide, pass975_2306, by decide, by decide, pass975_2332, rfl⟩
def src976 : Request := ⟨⟨⟨2600,3627,798,31694⟩,535425056505856,4812227595495⟩,32,3,1,386045,29⟩
private theorem pass976_2293 : (Triangular src976) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass976_2295 : (Triangular src976) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass976_2301 : (Triangular src976) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass976_2318 : (Triangular src976) 2318 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass976_2366 : (Triangular src976) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover976 : Cover (Triangular src976) 2389 2293 [2294,2300,2317,2365,2389] := by
  exact ⟨by decide, by decide, pass976_2293, by decide, by decide, pass976_2295, by decide, by decide, pass976_2301, by decide, by decide, pass976_2318, by decide, by decide, pass976_2366, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 28

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 28, 10, 75/100, 70/100, ![2021344173641, 242822779744, 33463617070, 2390280510], 1870657456027381⟩
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

def data : NearCase 3 28 28 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons24.plan, Lower6960.Prefix6969MainCases.CubicSingletons24.price, Lower6960.Prefix6969MainCases.CubicSingletons24.valid, Lower6960.Prefix6969MainCases.CubicSingletons24.priced, Lower6960.Prefix6969MainCases.CubicSingletons24.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons24.plan, Lower6960.Prefix6969RescueData.CubicSingletons24.price, Lower6960.Prefix6969RescueData.CubicSingletons24.sources, Lower6960.Prefix6969RescueData.CubicSingletons24.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 208942825303018119 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 29 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [312506094, 311290955, 311650254, 312339869, 311170535, 310377337, 311187118, 146561426, 146501767, 146524901, 146663812, 68194073, 68213549, 82117313, 94825360, 95297204, 118637596, 165976447, 229202843], [1126345, 1132562, 1130724, 1127196, 1133178, 1137236, 1133093, 2626082, 2627390, 2626883, 2623837, 5888198, 5886433, 4856253, 4173049, 4153135, 3301590, 2301249, 1619188],
  ![121665453121260, 1612199510572, 206282558700, 4965928310], 167887972543166587⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src979 : Request := ⟨⟨⟨4800,6696,1474,130242⟩,3367547627110400,55864419956306⟩,85,3,1,386045,29⟩
private theorem pass979_2293 : (Triangular src979) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass979_2294 : (Triangular src979) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass979_2297 : (Triangular src979) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass979_2305 : (Triangular src979) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass979_2327 : (Triangular src979) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass979_2388 : (Triangular src979) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover979 : Cover (Triangular src979) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass979_2293, by decide, by decide, pass979_2294, by decide, by decide, pass979_2297, by decide, by decide, pass979_2305, by decide, by decide, pass979_2327, by decide, by decide, pass979_2388, rfl⟩
def src980 : Request := ⟨⟨⟨5700,7952,1750,72277⟩,5637370734182400,111070724916873⟩,85,3,1,386045,29⟩
private theorem pass980_2293 : (Triangular src980) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass980_2296 : (Triangular src980) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass980_2304 : (Triangular src980) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass980_2326 : (Triangular src980) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass980_2387 : (Triangular src980) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover980 : Cover (Triangular src980) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass980_2293, by decide, by decide, pass980_2296, by decide, by decide, pass980_2304, by decide, by decide, pass980_2326, by decide, by decide, pass980_2387, rfl⟩
def src981 : Request := ⟨⟨⟨6900,9626,2118,102908⟩,9997036108906496,238415548481346⟩,110,3,1,386045,29⟩
private theorem pass981_2293 : (Triangular src981) 2293 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass981_2305 : (Triangular src981) 2305 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass981_2338 : (Triangular src981) 2338 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover981 : Cover (Triangular src981) 2389 2293 [2304,2337,2389] := by
  exact ⟨by decide, by decide, pass981_2293, by decide, by decide, pass981_2305, by decide, by decide, pass981_2338, rfl⟩
def src982 : Request := ⟨⟨⟨10000,13952,3070,115771⟩,30428373265940480,1051954539834997⟩,145,3,1,386045,29⟩
private theorem pass982_2293 : (Triangular src982) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass982_2298 : (Triangular src982) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass982_2312 : (Triangular src982) 2312 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass982_2351 : (Triangular src982) 2351 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover982 : Cover (Triangular src982) 2389 2293 [2297,2311,2350,2389] := by
  exact ⟨by decide, by decide, pass982_2293, by decide, by decide, pass982_2298, by decide, by decide, pass982_2312, by decide, by decide, pass982_2351, rfl⟩
def src983 : Request := ⟨⟨⟨560,781,169,8679⟩,5316921262080,10299257375⟩,0,3,1,386045,30⟩
private theorem pass983_2293 : (Triangular src983) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass983_2295 : (Triangular src983) 2295 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass983_2302 : (Triangular src983) 2302 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass983_2324 : (Triangular src983) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover983 : Cover (Triangular src983) 2389 2293 [2294,2301,2323,2389] := by
  exact ⟨by decide, by decide, pass983_2293, by decide, by decide, pass983_2295, by decide, by decide, pass983_2302, by decide, by decide, pass983_2324, rfl⟩
def src984 : Request := ⟨⟨⟨690,963,208,8679⟩,9921631092736,23724874690⟩,1,3,1,386045,30⟩
private theorem pass984_2293 : (Triangular src984) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass984_2301 : (Triangular src984) 2301 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass984_2325 : (Triangular src984) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover984 : Cover (Triangular src984) 2389 2293 [2300,2324,2389] := by
  exact ⟨by decide, by decide, pass984_2293, by decide, by decide, pass984_2301, by decide, by decide, pass984_2325, rfl⟩
def src985 : Request := ⟨⟨⟨690,962,208,9763⟩,9921631092736,23645774460⟩,2,3,1,386045,30⟩
private theorem pass985_2293 : (Triangular src985) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass985_2296 : (Triangular src985) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass985_2305 : (Triangular src985) 2305 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass985_2333 : (Triangular src985) 2333 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover985 : Cover (Triangular src985) 2389 2293 [2295,2304,2332,2389] := by
  exact ⟨by decide, by decide, pass985_2293, by decide, by decide, pass985_2296, by decide, by decide, pass985_2305, by decide, by decide, pass985_2333, rfl⟩
def src986 : Request := ⟨⟨⟨825,1151,253,10983⟩,17161575202816,49010625289⟩,4,3,1,386045,30⟩
private theorem pass986_2293 : (Triangular src986) 2293 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass986_2308 : (Triangular src986) 2308 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass986_2353 : (Triangular src986) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover986 : Cover (Triangular src986) 2389 2293 [2307,2352,2389] := by
  exact ⟨by decide, by decide, pass986_2293, by decide, by decide, pass986_2308, by decide, by decide, pass986_2353, rfl⟩
def src987 : Request := ⟨⟨⟨1000,1395,315,10983⟩,31157463285760,107844841957⟩,6,3,1,386045,30⟩
private theorem pass987_2293 : (Triangular src987) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass987_2294 : (Triangular src987) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass987_2297 : (Triangular src987) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass987_2305 : (Triangular src987) 2305 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass987_2329 : (Triangular src987) 2329 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover987 : Cover (Triangular src987) 2389 2293 [2293,2296,2304,2328,2389] := by
  exact ⟨by decide, by decide, pass987_2293, by decide, by decide, pass987_2294, by decide, by decide, pass987_2297, by decide, by decide, pass987_2305, by decide, by decide, pass987_2329, rfl⟩
def src988 : Request := ⟨⟨⟨1200,1674,378,13899⟩,53798525730816,223406703910⟩,10,3,1,386045,30⟩
private theorem pass988_2293 : (Triangular src988) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass988_2295 : (Triangular src988) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass988_2301 : (Triangular src988) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass988_2318 : (Triangular src988) 2318 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass988_2367 : (Triangular src988) 2367 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover988 : Cover (Triangular src988) 2389 2293 [2294,2300,2317,2366,2389] := by
  exact ⟨by decide, by decide, pass988_2293, by decide, by decide, pass988_2295, by decide, by decide, pass988_2301, by decide, by decide, pass988_2318, by decide, by decide, pass988_2367, rfl⟩
def src989 : Request := ⟨⟨⟨2100,2930,645,25043⟩,282396798484480,2051392203643⟩,25,3,1,386045,30⟩
private theorem pass989_2293 : (Triangular src989) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass989_2302 : (Triangular src989) 2302 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass989_2327 : (Triangular src989) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover989 : Cover (Triangular src989) 2389 2293 [2301,2326,2389] := by
  exact ⟨by decide, by decide, pass989_2293, by decide, by decide, pass989_2302, by decide, by decide, pass989_2327, rfl⟩
def src992 : Request := ⟨⟨⟨3950,5510,1213,64247⟩,1877062482395136,25622281045803⟩,65,3,1,386045,30⟩
private theorem pass992_2293 : (Triangular src992) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass992_2303 : (Triangular src992) 2303 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass992_2331 : (Triangular src992) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover992 : Cover (Triangular src992) 2389 2293 [2302,2330,2389] := by
  exact ⟨by decide, by decide, pass992_2293, by decide, by decide, pass992_2303, by decide, by decide, pass992_2331, rfl⟩
def src993 : Request := ⟨⟨⟨5700,7952,1796,64247⟩,5749327563587584,113334118485107⟩,85,3,1,386045,30⟩
private theorem pass993_2293 : (Triangular src993) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass993_2296 : (Triangular src993) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass993_2305 : (Triangular src993) 2305 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass993_2330 : (Triangular src993) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover993 : Cover (Triangular src993) 2389 2293 [2295,2304,2329,2389] := by
  exact ⟨by decide, by decide, pass993_2293, by decide, by decide, pass993_2296, by decide, by decide, pass993_2305, by decide, by decide, pass993_2330, rfl⟩
def src994 : Request := ⟨⟨⟨8300,11579,2548,115771⟩,17399709518790656,499124969898998⟩,145,3,1,386045,30⟩
private theorem pass994_2293 : (Triangular src994) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass994_2295 : (Triangular src994) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass994_2300 : (Triangular src994) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass994_2314 : (Triangular src994) 2314 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass994_2352 : (Triangular src994) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover994 : Cover (Triangular src994) 2389 2293 [2294,2299,2313,2351,2389] := by
  exact ⟨by decide, by decide, pass994_2293, by decide, by decide, pass994_2295, by decide, by decide, pass994_2300, by decide, by decide, pass994_2314, by decide, by decide, pass994_2352, rfl⟩
def src995 : Request := ⟨⟨⟨10000,13950,3070,185441⟩,30428373265940480,1051468979452278⟩,190,3,1,386045,30⟩
private theorem pass995_2293 : (Triangular src995) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass995_2295 : (Triangular src995) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass995_2300 : (Triangular src995) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass995_2314 : (Triangular src995) 2314 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass995_2352 : (Triangular src995) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover995 : Cover (Triangular src995) 2389 2293 [2294,2299,2313,2351,2389] := by
  exact ⟨by decide, by decide, pass995_2293, by decide, by decide, pass995_2295, by decide, by decide, pass995_2300, by decide, by decide, pass995_2314, by decide, by decide, pass995_2352, rfl⟩
def src996 : Request := ⟨⟨⟨560,781,172,6858⟩,5388141854720,10440670587⟩,0,3,1,386045,31⟩
private theorem pass996_2293 : (Triangular src996) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass996_2296 : (Triangular src996) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass996_2305 : (Triangular src996) 2305 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass996_2334 : (Triangular src996) 2334 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover996 : Cover (Triangular src996) 2389 2293 [2295,2304,2333,2389] := by
  exact ⟨by decide, by decide, pass996_2293, by decide, by decide, pass996_2296, by decide, by decide, pass996_2305, by decide, by decide, pass996_2334, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 29

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 29, 10, 70/100, 70/100, ![1470366277548, 212990763911, 34658746580, 2390280510], 1591754615281470⟩
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

def data : NearCase 3 29 29 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons25.plan, Lower6960.Prefix6969MainCases.CubicSingletons25.price, Lower6960.Prefix6969MainCases.CubicSingletons25.valid, Lower6960.Prefix6969MainCases.CubicSingletons25.priced, Lower6960.Prefix6969MainCases.CubicSingletons25.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons25.plan, Lower6960.Prefix6969RescueData.CubicSingletons25.price, Lower6960.Prefix6969RescueData.CubicSingletons25.sources, Lower6960.Prefix6969RescueData.CubicSingletons25.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 207938071148720859 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 30 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [311875365, 311746435, 310587576, 310690565, 310643824, 311272026, 309873456, 146715841, 146704182, 146247937, 103671694, 94406371, 62582396, 81061494, 93470509, 93422871, 146141226, 229460952], [1129572, 1130232, 1136160, 1135633, 1135872, 1132659, 1139813, 2622697, 2622952, 2632955, 3799688, 4193130, 6432106, 4918947, 4240323, 4242725, 2635295, 1617066],
  ![121802462540640, 1611920740488, 206514856800, 5048842750], 168077181306429268⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 30

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 30, 10, 70/100, 70/100, ![2165725940067, 271448267073, 35853876090, 2390280510], 1678048275153211⟩
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

def data : NearCase 3 30 30 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons26.plan, Lower6960.Prefix6969MainCases.CubicSingletons26.price, Lower6960.Prefix6969MainCases.CubicSingletons26.valid, Lower6960.Prefix6969MainCases.CubicSingletons26.priced, Lower6960.Prefix6969MainCases.CubicSingletons26.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons26.plan, Lower6960.Prefix6969RescueData.CubicSingletons26.price, Lower6960.Prefix6969RescueData.CubicSingletons26.sources, Lower6960.Prefix6969RescueData.CubicSingletons26.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 207424812741711833 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 31 386045 := by
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

def price : Pricing := ⟨55/100, 100/100, [310439674, 310156179, 310344758, 309746105, 309388479, 309969212, 308245210, 133093846, 133435236, 133260852, 103399239, 64222020, 61388972, 92617221, 92600980, 111031703, 166106000, 229029350], [1136917, 1138367, 1137402, 1140465, 1142295, 1139324, 1148143, 2921356, 2913871, 2917694, 3811187, 6264047, 6559102, 4283352, 4284171, 3542204, 2299095, 1620614],
  ![121573359567000, 1612386708880, 206126415000, 5098163490], 167076440117140997⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src997 : Request := ⟨⟨⟨690,963,208,7715⟩,9921631092736,23724874690⟩,1,3,1,386045,31⟩
private theorem pass997_2293 : (Triangular src997) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass997_2296 : (Triangular src997) 2296 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass997_2306 : (Triangular src997) 2306 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass997_2337 : (Triangular src997) 2337 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover997 : Cover (Triangular src997) 2389 2293 [2295,2305,2336,2389] := by
  exact ⟨by decide, by decide, pass997_2293, by decide, by decide, pass997_2296, by decide, by decide, pass997_2306, by decide, by decide, pass997_2337, rfl⟩
def src998 : Request := ⟨⟨⟨690,962,208,8679⟩,9921631092736,23645774460⟩,2,3,1,386045,31⟩
private theorem pass998_2293 : (Triangular src998) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass998_2297 : (Triangular src998) 2297 2309 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass998_2310 : (Triangular src998) 2310 2349 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass998_2350 : (Triangular src998) 2350 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover998 : Cover (Triangular src998) 2389 2293 [2296,2309,2349,2389] := by
  exact ⟨by decide, by decide, pass998_2293, by decide, by decide, pass998_2297, by decide, by decide, pass998_2310, by decide, by decide, pass998_2350, rfl⟩
def src999 : Request := ⟨⟨⟨690,962,212,9763⟩,10065769922560,23997864317⟩,3,3,1,386045,31⟩
private theorem pass999_2293 : (Triangular src999) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass999_2302 : (Triangular src999) 2302 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass999_2330 : (Triangular src999) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover999 : Cover (Triangular src999) 2389 2293 [2301,2329,2389] := by
  exact ⟨by decide, by decide, pass999_2293, by decide, by decide, pass999_2302, by decide, by decide, pass999_2330, rfl⟩
def src1000 : Request := ⟨⟨⟨825,1151,253,12355⟩,17161575202816,49010625289⟩,6,3,1,386045,31⟩
private theorem pass1000_2293 : (Triangular src1000) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1000_2298 : (Triangular src1000) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1000_2313 : (Triangular src1000) 2313 2357 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1000_2358 : (Triangular src1000) 2358 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1000 : Cover (Triangular src1000) 2389 2293 [2297,2312,2357,2389] := by
  exact ⟨by decide, by decide, pass1000_2293, by decide, by decide, pass1000_2298, by decide, by decide, pass1000_2313, by decide, by decide, pass1000_2358, rfl⟩
def src1001 : Request := ⟨⟨⟨1000,1395,307,12355⟩,30557599170560,105715278267⟩,8,3,1,386045,31⟩
private theorem pass1001_2293 : (Triangular src1001) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1001_2301 : (Triangular src1001) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1001_2324 : (Triangular src1001) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1001 : Cover (Triangular src1001) 2389 2293 [2300,2323,2389] := by
  exact ⟨by decide, by decide, pass1001_2293, by decide, by decide, pass1001_2301, by decide, by decide, pass1001_2324, rfl⟩
def src1002 : Request := ⟨⟨⟨1450,2023,445,17590⟩,92998964346880,466511127281⟩,16,3,1,386045,31⟩
private theorem pass1002_2293 : (Triangular src1002) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1002_2301 : (Triangular src1002) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1002_2324 : (Triangular src1002) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1002 : Cover (Triangular src1002) 2389 2293 [2300,2323,2389] := by
  exact ⟨by decide, by decide, pass1002_2293, by decide, by decide, pass1002_2301, by decide, by decide, pass1002_2324, rfl⟩
def src1003 : Request := ⟨⟨⟨2100,2929,645,31694⟩,282396798484480,2049139102608⟩,32,3,1,386045,31⟩
private theorem pass1003_2293 : (Triangular src1003) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1003_2296 : (Triangular src1003) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1003_2304 : (Triangular src1003) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1003_2327 : (Triangular src1003) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1003 : Cover (Triangular src1003) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass1003_2293, by decide, by decide, pass1003_2296, by decide, by decide, pass1003_2304, by decide, by decide, pass1003_2327, rfl⟩
def src1006 : Request := ⟨⟨⟨3950,5510,1213,50764⟩,1877062482395136,25622281045803⟩,65,3,1,386045,31⟩
private theorem pass1006_2293 : (Triangular src1006) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1006_2297 : (Triangular src1006) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1006_2308 : (Triangular src1006) 2308 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1006_2338 : (Triangular src1006) 2338 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1006 : Cover (Triangular src1006) 2389 2293 [2296,2307,2337,2389] := by
  exact ⟨by decide, by decide, pass1006_2293, by decide, by decide, pass1006_2297, by decide, by decide, pass1006_2308, by decide, by decide, pass1006_2338, rfl⟩
def src1007 : Request := ⟨⟨⟨5700,7951,1750,115771⟩,5637370734182400,111025751789870⟩,110,3,1,386045,31⟩
private theorem pass1007_2293 : (Triangular src1007) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1007_2294 : (Triangular src1007) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1007_2297 : (Triangular src1007) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1007_2305 : (Triangular src1007) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1007_2327 : (Triangular src1007) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1007_2388 : (Triangular src1007) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1007 : Cover (Triangular src1007) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass1007_2293, by decide, by decide, pass1007_2294, by decide, by decide, pass1007_2297, by decide, by decide, pass1007_2305, by decide, by decide, pass1007_2327, by decide, by decide, pass1007_2388, rfl⟩
def src1008 : Request := ⟨⟨⟨8300,11579,2548,102908⟩,17399709518790656,499124969898998⟩,145,3,1,386045,31⟩
private theorem pass1008_2293 : (Triangular src1008) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1008_2297 : (Triangular src1008) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1008_2308 : (Triangular src1008) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1008_2339 : (Triangular src1008) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1008 : Cover (Triangular src1008) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass1008_2293, by decide, by decide, pass1008_2297, by decide, by decide, pass1008_2308, by decide, by decide, pass1008_2339, rfl⟩
def src1009 : Request := ⟨⟨⟨560,781,176,6096⟩,5482316038144,10627925923⟩,0,3,1,386045,32⟩
private theorem pass1009_2293 : (Triangular src1009) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1009_2295 : (Triangular src1009) 2295 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1009_2302 : (Triangular src1009) 2302 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1009_2324 : (Triangular src1009) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1009 : Cover (Triangular src1009) 2389 2293 [2294,2301,2323,2389] := by
  exact ⟨by decide, by decide, pass1009_2293, by decide, by decide, pass1009_2295, by decide, by decide, pass1009_2302, by decide, by decide, pass1009_2324, rfl⟩
def src1010 : Request := ⟨⟨⟨690,963,212,6858⟩,10065769922560,24078187611⟩,1,3,1,386045,32⟩
private theorem pass1010_2293 : (Triangular src1010) 2293 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1010_2304 : (Triangular src1010) 2304 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1010_2337 : (Triangular src1010) 2337 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1010 : Cover (Triangular src1010) 2389 2293 [2303,2336,2389] := by
  exact ⟨by decide, by decide, pass1010_2293, by decide, by decide, pass1010_2304, by decide, by decide, pass1010_2337, rfl⟩
def src1011 : Request := ⟨⟨⟨690,962,208,7715⟩,9921631092736,23645774460⟩,2,3,1,386045,32⟩
private theorem pass1011_2293 : (Triangular src1011) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1011_2294 : (Triangular src1011) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1011_2297 : (Triangular src1011) 2297 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1011_2307 : (Triangular src1011) 2307 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1011_2338 : (Triangular src1011) 2338 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1011 : Cover (Triangular src1011) 2389 2293 [2293,2296,2306,2337,2389] := by
  exact ⟨by decide, by decide, pass1011_2293, by decide, by decide, pass1011_2294, by decide, by decide, pass1011_2297, by decide, by decide, pass1011_2307, by decide, by decide, pass1011_2338, rfl⟩
def src1012 : Request := ⟨⟨⟨690,962,212,9763⟩,10065769922560,23997864317⟩,4,3,1,386045,32⟩
private theorem pass1012_2293 : (Triangular src1012) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1012_2295 : (Triangular src1012) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1012_2301 : (Triangular src1012) 2301 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1012_2319 : (Triangular src1012) 2319 2374 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1012_2375 : (Triangular src1012) 2375 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1012 : Cover (Triangular src1012) 2389 2293 [2294,2300,2318,2374,2389] := by
  exact ⟨by decide, by decide, pass1012_2293, by decide, by decide, pass1012_2295, by decide, by decide, pass1012_2301, by decide, by decide, pass1012_2319, by decide, by decide, pass1012_2375, rfl⟩
def src1013 : Request := ⟨⟨⟨825,1151,253,10983⟩,17161575202816,49010625289⟩,6,3,1,386045,32⟩
private theorem pass1013_2293 : (Triangular src1013) 2293 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1013_2304 : (Triangular src1013) 2304 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1013_2337 : (Triangular src1013) 2337 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1013 : Cover (Triangular src1013) 2389 2293 [2303,2336,2389] := by
  exact ⟨by decide, by decide, pass1013_2293, by decide, by decide, pass1013_2304, by decide, by decide, pass1013_2337, rfl⟩
def src1014 : Request := ⟨⟨⟨1000,1395,307,13899⟩,30557599170560,105715278267⟩,10,3,1,386045,32⟩
private theorem pass1014_2293 : (Triangular src1014) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1014_2301 : (Triangular src1014) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1014_2324 : (Triangular src1014) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1014 : Cover (Triangular src1014) 2389 2293 [2300,2323,2389] := by
  exact ⟨by decide, by decide, pass1014_2293, by decide, by decide, pass1014_2301, by decide, by decide, pass1014_2324, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 31

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 31, 10, 70/100, 70/100, ![1397133573909, 189110269893, 30749465292, 1983854964], 1279454427222584⟩
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

def data : NearCase 3 31 31 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons27.plan, Lower6960.Prefix6969MainCases.CubicSingletons27.price, Lower6960.Prefix6969MainCases.CubicSingletons27.valid, Lower6960.Prefix6969MainCases.CubicSingletons27.priced, Lower6960.Prefix6969MainCases.CubicSingletons27.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons27.plan, Lower6960.Prefix6969RescueData.CubicSingletons27.price, Lower6960.Prefix6969RescueData.CubicSingletons27.sources, Lower6960.Prefix6969RescueData.CubicSingletons27.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 206373659531298022 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 32 386045 := by
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

def price : Pricing := ⟨55/100, 100/100, [308205222, 307788017, 308007106, 308049519, 308217248, 307803044, 311505554, 311291929, 155763541, 156718848, 156417023, 156572094, 156999023, 105414303, 71746476, 77178426, 91864131, 91934712, 118615190, 165645602, 228945013], [1148348, 1150482, 1149361, 1149144, 1148286, 1150405, 1131464, 1132557, 2471052, 2455168, 2460187, 2457608, 2450510, 3737208, 5587305, 5180757, 4321328, 4317769, 3302217, 2306750, 1621308],
  ![121528591800660, 1612478135252, 206050511700, 5142380320], 166757202063453745⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1015 : Request := ⟨⟨⟨1750,2441,537,22261⟩,163381988556800,988269431527⟩,25,3,1,386045,32⟩
private theorem pass1015_2293 : (Triangular src1015) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1015_2294 : (Triangular src1015) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1015_2297 : (Triangular src1015) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1015_2305 : (Triangular src1015) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1015_2328 : (Triangular src1015) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1015 : Cover (Triangular src1015) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass1015_2293, by decide, by decide, pass1015_2294, by decide, by decide, pass1015_2297, by decide, by decide, pass1015_2305, by decide, by decide, pass1015_2328, rfl⟩
def src1016 : Request := ⟨⟨⟨3950,5510,1213,45124⟩,1877062482395136,25622281045803⟩,65,3,1,386045,32⟩
private theorem pass1016_2293 : (Triangular src1016) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1016_2296 : (Triangular src1016) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1016_2305 : (Triangular src1016) 2305 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1016_2330 : (Triangular src1016) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1016 : Cover (Triangular src1016) 2389 2293 [2295,2304,2329,2389] := by
  exact ⟨by decide, by decide, pass1016_2293, by decide, by decide, pass1016_2296, by decide, by decide, pass1016_2305, by decide, by decide, pass1016_2330, rfl⟩
def src1017 : Request := ⟨⟨⟨4800,6696,1512,57109⟩,3433136573644800,56980856955989⟩,85,3,1,386045,32⟩
private theorem pass1017_2293 : (Triangular src1017) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1017_2294 : (Triangular src1017) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1017_2297 : (Triangular src1017) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1017_2305 : (Triangular src1017) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1017_2327 : (Triangular src1017) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1017_2388 : (Triangular src1017) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1017 : Cover (Triangular src1017) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass1017_2293, by decide, by decide, pass1017_2294, by decide, by decide, pass1017_2297, by decide, by decide, pass1017_2305, by decide, by decide, pass1017_2327, by decide, by decide, pass1017_2388, rfl⟩
def src1018 : Request := ⟨⟨⟨5700,7951,1750,91474⟩,5637370734182400,111025751789870⟩,110,3,1,386045,32⟩
private theorem pass1018_2293 : (Triangular src1018) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1018_2301 : (Triangular src1018) 2301 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1018_2323 : (Triangular src1018) 2323 2383 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1018_2384 : (Triangular src1018) 2384 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1018 : Cover (Triangular src1018) 2389 2293 [2300,2322,2383,2389] := by
  exact ⟨by decide, by decide, pass1018_2293, by decide, by decide, pass1018_2301, by decide, by decide, pass1018_2323, by decide, by decide, pass1018_2384, rfl⟩
def src1019 : Request := ⟨⟨⟨8300,11579,2548,91474⟩,17399709518790656,499124969898998⟩,145,3,1,386045,32⟩
private theorem pass1019_2293 : (Triangular src1019) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1019_2295 : (Triangular src1019) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1019_2300 : (Triangular src1019) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1019_2314 : (Triangular src1019) 2314 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1019_2353 : (Triangular src1019) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1019 : Cover (Triangular src1019) 2389 2293 [2294,2299,2313,2352,2389] := by
  exact ⟨by decide, by decide, pass1019_2293, by decide, by decide, pass1019_2295, by decide, by decide, pass1019_2300, by decide, by decide, pass1019_2314, by decide, by decide, pass1019_2353, rfl⟩
def src1020 : Request := ⟨⟨⟨560,781,169,6096⟩,5316921262080,10299257375⟩,0,3,1,386045,33⟩
private theorem pass1020_2293 : (Triangular src1020) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1020_2298 : (Triangular src1020) 2298 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1020_2314 : (Triangular src1020) 2314 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1020_2365 : (Triangular src1020) 2365 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1020 : Cover (Triangular src1020) 2389 2293 [2297,2313,2364,2389] := by
  exact ⟨by decide, by decide, pass1020_2293, by decide, by decide, pass1020_2298, by decide, by decide, pass1020_2314, by decide, by decide, pass1020_2365, rfl⟩
def src1021 : Request := ⟨⟨⟨560,781,172,6858⟩,5388141854720,10440670587⟩,1,3,1,386045,33⟩
private theorem pass1021_2293 : (Triangular src1021) 2293 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1021_2305 : (Triangular src1021) 2305 2342 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1021_2343 : (Triangular src1021) 2343 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1021 : Cover (Triangular src1021) 2389 2293 [2304,2342,2389] := by
  exact ⟨by decide, by decide, pass1021_2293, by decide, by decide, pass1021_2305, by decide, by decide, pass1021_2343, rfl⟩
def src1022 : Request := ⟨⟨⟨690,962,212,6858⟩,10065769922560,23997864317⟩,2,3,1,386045,33⟩
private theorem pass1022_2293 : (Triangular src1022) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1022_2302 : (Triangular src1022) 2302 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1022_2330 : (Triangular src1022) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1022 : Cover (Triangular src1022) 2389 2293 [2301,2329,2389] := by
  exact ⟨by decide, by decide, pass1022_2293, by decide, by decide, pass1022_2302, by decide, by decide, pass1022_2330, rfl⟩
def src1023 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,3,3,1,386045,33⟩
private theorem pass1023_2293 : (Triangular src1023) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1023_2306 : (Triangular src1023) 2306 2346 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1023_2347 : (Triangular src1023) 2347 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1023 : Cover (Triangular src1023) 2389 2293 [2305,2346,2389] := by
  exact ⟨by decide, by decide, pass1023_2293, by decide, by decide, pass1023_2306, by decide, by decide, pass1023_2347, rfl⟩
def src1024 : Request := ⟨⟨⟨690,962,212,8679⟩,10065769922560,23997864317⟩,4,3,1,386045,33⟩
private theorem pass1024_2293 : (Triangular src1024) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1024_2301 : (Triangular src1024) 2301 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1024_2325 : (Triangular src1024) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1024 : Cover (Triangular src1024) 2389 2293 [2300,2324,2389] := by
  exact ⟨by decide, by decide, pass1024_2293, by decide, by decide, pass1024_2301, by decide, by decide, pass1024_2325, rfl⟩
def src1025 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,6,3,1,386045,33⟩
private theorem pass1025_2293 : (Triangular src1025) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1025_2306 : (Triangular src1025) 2306 2344 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1025_2345 : (Triangular src1025) 2345 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1025 : Cover (Triangular src1025) 2389 2293 [2305,2344,2389] := by
  exact ⟨by decide, by decide, pass1025_2293, by decide, by decide, pass1025_2306, by decide, by decide, pass1025_2345, rfl⟩
def src1026 : Request := ⟨⟨⟨1000,1395,307,12355⟩,30557599170560,105715278267⟩,10,3,1,386045,33⟩
private theorem pass1026_2293 : (Triangular src1026) 2293 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1026_2305 : (Triangular src1026) 2305 2340 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1026_2341 : (Triangular src1026) 2341 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1026 : Cover (Triangular src1026) 2389 2293 [2304,2340,2389] := by
  exact ⟨by decide, by decide, pass1026_2293, by decide, by decide, pass1026_2305, by decide, by decide, pass1026_2341, rfl⟩
def src1027 : Request := ⟨⟨⟨1750,2441,537,19788⟩,163381988556800,988269431527⟩,25,3,1,386045,33⟩
private theorem pass1027_2293 : (Triangular src1027) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1027_2294 : (Triangular src1027) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1027_2296 : (Triangular src1027) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1027_2302 : (Triangular src1027) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1027_2319 : (Triangular src1027) 2319 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1027_2368 : (Triangular src1027) 2368 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1027 : Cover (Triangular src1027) 2389 2293 [2293,2295,2301,2318,2367,2389] := by
  exact ⟨by decide, by decide, pass1027_2293, by decide, by decide, pass1027_2294, by decide, by decide, pass1027_2296, by decide, by decide, pass1027_2302, by decide, by decide, pass1027_2319, by decide, by decide, pass1027_2368, rfl⟩
def src1030 : Request := ⟨⟨⟨3950,5510,1244,40111⟩,1913299978158080,26129827888718⟩,65,3,1,386045,33⟩
private theorem pass1030_2293 : (Triangular src1030) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1030_2295 : (Triangular src1030) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1030_2301 : (Triangular src1030) 2301 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1030_2317 : (Triangular src1030) 2317 2361 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1030_2362 : (Triangular src1030) 2362 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1030 : Cover (Triangular src1030) 2389 2293 [2294,2300,2316,2361,2389] := by
  exact ⟨by decide, by decide, pass1030_2293, by decide, by decide, pass1030_2295, by decide, by decide, pass1030_2301, by decide, by decide, pass1030_2317, by decide, by decide, pass1030_2362, rfl⟩
def src1031 : Request := ⟨⟨⟨6900,9625,2118,115771⟩,9997036108906496,238335796784464⟩,145,3,1,386045,33⟩
private theorem pass1031_2293 : (Triangular src1031) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1031_2296 : (Triangular src1031) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1031_2304 : (Triangular src1031) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1031_2326 : (Triangular src1031) 2326 2385 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1031_2386 : (Triangular src1031) 2386 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1031 : Cover (Triangular src1031) 2389 2293 [2295,2303,2325,2385,2389] := by
  exact ⟨by decide, by decide, pass1031_2293, by decide, by decide, pass1031_2296, by decide, by decide, pass1031_2304, by decide, by decide, pass1031_2326, by decide, by decide, pass1031_2386, rfl⟩
def src1032 : Request := ⟨⟨⟨10000,13950,3070,115771⟩,30428373265940480,1051468979452278⟩,190,3,1,386045,33⟩
private theorem pass1032_2293 : (Triangular src1032) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1032_2302 : (Triangular src1032) 2302 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1032_2327 : (Triangular src1032) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1032 : Cover (Triangular src1032) 2389 2293 [2301,2326,2389] := by
  exact ⟨by decide, by decide, pass1032_2293, by decide, by decide, pass1032_2302, by decide, by decide, pass1032_2327, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 32

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 32, 10, 70/100, 70/100, ![1139525646328, 183723542614, 31741383856, 1983854964], 1185237512126872⟩
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

def data : NearCase 3 32 32 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons28.plan, Lower6960.Prefix6969MainCases.CubicSingletons28.price, Lower6960.Prefix6969MainCases.CubicSingletons28.valid, Lower6960.Prefix6969MainCases.CubicSingletons28.priced, Lower6960.Prefix6969MainCases.CubicSingletons28.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons28.plan, Lower6960.Prefix6969RescueData.CubicSingletons28.price, Lower6960.Prefix6969RescueData.CubicSingletons28.sources, Lower6960.Prefix6969RescueData.CubicSingletons28.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 206578683753191315 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 33 386045 := by
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

def price : Pricing := ⟨55/100, 100/100, [307028450, 305521052, 305348989, 305899360, 304640487, 306295994, 308929757, 308309384, 154553315, 155235980, 154986133, 155349518, 155188396, 107939685, 66625567, 77178426, 91132091, 91004130, 118510061, 165540474, 228863086], [1154368, 1162079, 1162960, 1160144, 1166584, 1158115, 1144641, 1147815, 2491173, 2479823, 2483977, 2477935, 2480614, 3649541, 6030340, 5180757, 4358242, 4364695, 3305155, 2308497, 1621981],
  ![121485103310520, 1612566328844, 205976777400, 5193987050], 166176300069992785⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 33

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 33, 10, 70/100, 70/100, ![1487271253715, 229910205403, 39439261550, 2390280510], 1303899858285289⟩
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

def data : NearCase 3 33 33 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons29.plan, Lower6960.Prefix6969MainCases.CubicSingletons29.price, Lower6960.Prefix6969MainCases.CubicSingletons29.valid, Lower6960.Prefix6969MainCases.CubicSingletons29.priced, Lower6960.Prefix6969MainCases.CubicSingletons29.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons29.plan, Lower6960.Prefix6969RescueData.CubicSingletons29.price, Lower6960.Prefix6969RescueData.CubicSingletons29.sources, Lower6960.Prefix6969RescueData.CubicSingletons29.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 205317956650588046 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 7 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [346760768, 344984529, 346203362, 344815872, 345166996, 344260515, 345165402, 346509342, 170172458, 170501411, 170626914, 170566878, 115552091, 74211083, 66922384, 90925957, 104957189, 105015799, 126874474, 173904886, 235264231], [996139, 1001007, 997667, 1001470, 1000507, 1002992, 1000512, 996828, 2231485, 2226221, 2224707, 2225431, 3387843, 5391424, 6003442, 4368637, 3753076, 3751041, 3071336, 2185179, 1569353],
  ![124882959099420, 1605651694064, 211737807900, 4466160440], 190878449922097611⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 7

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 7, 8, 95/100, 80/100, ![1640970292666, 498672620069, 8202412540, 2343564930], 9694919084979652⟩
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

def data : NearCase 3 7 7 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons3.plan, Lower6960.Prefix6969MainCases.CubicSingletons3.price, Lower6960.Prefix6969MainCases.CubicSingletons3.valid, Lower6960.Prefix6969MainCases.CubicSingletons3.priced, Lower6960.Prefix6969MainCases.CubicSingletons3.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons3.plan, Lower6960.Prefix6969RescueData.CubicSingletons3.price, Lower6960.Prefix6969RescueData.CubicSingletons3.sources, Lower6960.Prefix6969RescueData.CubicSingletons3.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 222493025090777663 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 34 386045 := by
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

def price : Pricing := ⟨55/100, 100/100, [305639353, 304352756, 305081892, 305275379, 305617694, 305533518, 305018361, 304833414, 164085349, 163905416, 163881040, 164100723, 81970807, 54398749, 71911720, 79295524, 91517762, 91580920, 118861721, 165436891, 228782363], [1161474, 1168056, 1164326, 1163336, 1161585, 1162016, 1164651, 1165597, 2332691, 2335682, 2336088, 2332435, 4864953, 7430037, 5574172, 5034544, 4338794, 4335609, 3295325, 2310220, 1622645],
  ![121442253927660, 1612653698992, 205904126700, 5163164860], 164529227435451063⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 20 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1033 : Request := ⟨⟨⟨470,655,144,6096⟩,3184589537280,5168862572⟩,0,3,1,386045,34⟩
private theorem pass1033_2293 : (Triangular src1033) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1033_2300 : (Triangular src1033) 2300 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1033_2323 : (Triangular src1033) 2323 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1033 : Cover (Triangular src1033) 2389 2293 [2299,2322,2389] := by
  exact ⟨by decide, by decide, pass1033_2293, by decide, by decide, pass1033_2300, by decide, by decide, pass1033_2323, rfl⟩
def src1034 : Request := ⟨⟨⟨560,781,172,6096⟩,5388141854720,10440670587⟩,1,3,1,386045,34⟩
private theorem pass1034_2293 : (Triangular src1034) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1034_2303 : (Triangular src1034) 2303 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1034_2334 : (Triangular src1034) 2334 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1034 : Cover (Triangular src1034) 2389 2293 [2302,2333,2389] := by
  exact ⟨by decide, by decide, pass1034_2293, by decide, by decide, pass1034_2303, by decide, by decide, pass1034_2334, rfl⟩
def src1035 : Request := ⟨⟨⟨690,962,208,6858⟩,9921631092736,23645774460⟩,2,3,1,386045,34⟩
private theorem pass1035_2293 : (Triangular src1035) 2293 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1035_2304 : (Triangular src1035) 2304 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1035_2338 : (Triangular src1035) 2338 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1035 : Cover (Triangular src1035) 2389 2293 [2303,2337,2389] := by
  exact ⟨by decide, by decide, pass1035_2293, by decide, by decide, pass1035_2304, by decide, by decide, pass1035_2338, rfl⟩
def src1036 : Request := ⟨⟨⟨690,962,212,6858⟩,10065769922560,23997864317⟩,3,3,1,386045,34⟩
private theorem pass1036_2293 : (Triangular src1036) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1036_2297 : (Triangular src1036) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1036_2309 : (Triangular src1036) 2309 2345 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1036_2346 : (Triangular src1036) 2346 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1036 : Cover (Triangular src1036) 2389 2293 [2296,2308,2345,2389] := by
  exact ⟨by decide, by decide, pass1036_2293, by decide, by decide, pass1036_2297, by decide, by decide, pass1036_2309, by decide, by decide, pass1036_2346, rfl⟩
def src1037 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,4,3,1,386045,34⟩
private theorem pass1037_2293 : (Triangular src1037) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1037_2301 : (Triangular src1037) 2301 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1037_2325 : (Triangular src1037) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1037 : Cover (Triangular src1037) 2389 2293 [2300,2324,2389] := by
  exact ⟨by decide, by decide, pass1037_2293, by decide, by decide, pass1037_2301, by decide, by decide, pass1037_2325, rfl⟩
def src1038 : Request := ⟨⟨⟨825,1151,253,10983⟩,17161575202816,49010625289⟩,8,3,1,386045,34⟩
private theorem pass1038_2293 : (Triangular src1038) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1038_2299 : (Triangular src1038) 2299 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1038_2317 : (Triangular src1038) 2317 2370 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1038_2371 : (Triangular src1038) 2371 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1038 : Cover (Triangular src1038) 2389 2293 [2298,2316,2370,2389] := by
  exact ⟨by decide, by decide, pass1038_2293, by decide, by decide, pass1038_2299, by decide, by decide, pass1038_2317, by decide, by decide, pass1038_2371, rfl⟩
def src1039 : Request := ⟨⟨⟨1450,2023,457,15636⟩,94890063298560,476245648464⟩,20,3,1,386045,34⟩
private theorem pass1039_2293 : (Triangular src1039) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1039_2295 : (Triangular src1039) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1039_2300 : (Triangular src1039) 2300 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1039_2315 : (Triangular src1039) 2315 2357 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1039_2358 : (Triangular src1039) 2358 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1039 : Cover (Triangular src1039) 2389 2293 [2294,2299,2314,2357,2389] := by
  exact ⟨by decide, by decide, pass1039_2293, by decide, by decide, pass1039_2295, by decide, by decide, pass1039_2300, by decide, by decide, pass1039_2315, by decide, by decide, pass1039_2358, rfl⟩
def src1040 : Request := ⟨⟨⟨2600,3627,819,25043⟩,546063062138880,4910333421859⟩,40,3,1,386045,34⟩
private theorem pass1040_2293 : (Triangular src1040) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1040_2295 : (Triangular src1040) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1040_2300 : (Triangular src1040) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1040_2314 : (Triangular src1040) 2314 2353 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1040_2354 : (Triangular src1040) 2354 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1040 : Cover (Triangular src1040) 2389 2293 [2294,2299,2313,2353,2389] := by
  exact ⟨by decide, by decide, pass1040_2293, by decide, by decide, pass1040_2295, by decide, by decide, pass1040_2300, by decide, by decide, pass1040_2314, by decide, by decide, pass1040_2354, rfl⟩
def src1043 : Request := ⟨⟨⟨5700,7951,1750,64247⟩,5637370734182400,111025751789870⟩,110,3,1,386045,34⟩
private theorem pass1043_2293 : (Triangular src1043) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1043_2298 : (Triangular src1043) 2298 2310 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1043_2311 : (Triangular src1043) 2311 2346 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1043_2347 : (Triangular src1043) 2347 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1043 : Cover (Triangular src1043) 2389 2293 [2297,2310,2346,2389] := by
  exact ⟨by decide, by decide, pass1043_2293, by decide, by decide, pass1043_2298, by decide, by decide, pass1043_2311, by decide, by decide, pass1043_2347, rfl⟩
def src1044 : Request := ⟨⟨⟨6900,9625,2118,91474⟩,9997036108906496,238335796784464⟩,145,3,1,386045,34⟩
private theorem pass1044_2293 : (Triangular src1044) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1044_2297 : (Triangular src1044) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1044_2308 : (Triangular src1044) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1044_2339 : (Triangular src1044) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1044 : Cover (Triangular src1044) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass1044_2293, by decide, by decide, pass1044_2297, by decide, by decide, pass1044_2308, by decide, by decide, pass1044_2339, rfl⟩
def src1045 : Request := ⟨⟨⟨10000,13950,3070,102908⟩,30428373265940480,1051468979452278⟩,190,3,1,386045,34⟩
private theorem pass1045_2293 : (Triangular src1045) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1045_2296 : (Triangular src1045) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1045_2304 : (Triangular src1045) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1045_2326 : (Triangular src1045) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1045_2387 : (Triangular src1045) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1045 : Cover (Triangular src1045) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass1045_2293, by decide, by decide, pass1045_2296, by decide, by decide, pass1045_2304, by decide, by decide, pass1045_2326, by decide, by decide, pass1045_2387, rfl⟩
def src1046 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,0,3,1,386045,35⟩
private theorem pass1046_2293 : (Triangular src1046) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1046_2303 : (Triangular src1046) 2303 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1046_2335 : (Triangular src1046) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1046 : Cover (Triangular src1046) 2389 2293 [2302,2334,2389] := by
  exact ⟨by decide, by decide, pass1046_2293, by decide, by decide, pass1046_2303, by decide, by decide, pass1046_2335, rfl⟩
def src1047 : Request := ⟨⟨⟨560,781,176,5419⟩,5482316038144,10627925923⟩,1,3,1,386045,35⟩
private theorem pass1047_2293 : (Triangular src1047) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1047_2295 : (Triangular src1047) 2295 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1047_2302 : (Triangular src1047) 2302 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1047_2324 : (Triangular src1047) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1047 : Cover (Triangular src1047) 2389 2293 [2294,2301,2323,2389] := by
  exact ⟨by decide, by decide, pass1047_2293, by decide, by decide, pass1047_2295, by decide, by decide, pass1047_2302, by decide, by decide, pass1047_2324, rfl⟩
def src1048 : Request := ⟨⟨⟨560,781,176,6096⟩,5482316038144,10627925923⟩,2,3,1,386045,35⟩
private theorem pass1048_2293 : (Triangular src1048) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1048_2294 : (Triangular src1048) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1048_2297 : (Triangular src1048) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1048_2306 : (Triangular src1048) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1048_2335 : (Triangular src1048) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1048 : Cover (Triangular src1048) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1048_2293, by decide, by decide, pass1048_2294, by decide, by decide, pass1048_2297, by decide, by decide, pass1048_2306, by decide, by decide, pass1048_2335, rfl⟩
def src1049 : Request := ⟨⟨⟨690,962,208,6858⟩,9921631092736,23645774460⟩,3,3,1,386045,35⟩
private theorem pass1049_2293 : (Triangular src1049) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1049_2298 : (Triangular src1049) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1049_2313 : (Triangular src1049) 2313 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1049_2360 : (Triangular src1049) 2360 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1049 : Cover (Triangular src1049) 2389 2293 [2297,2312,2359,2389] := by
  exact ⟨by decide, by decide, pass1049_2293, by decide, by decide, pass1049_2298, by decide, by decide, pass1049_2313, by decide, by decide, pass1049_2360, rfl⟩
def src1050 : Request := ⟨⟨⟨690,962,217,6858⟩,10244384358400,24434817260⟩,4,3,1,386045,35⟩
private theorem pass1050_2293 : (Triangular src1050) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1050_2296 : (Triangular src1050) 2296 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1050_2306 : (Triangular src1050) 2306 2335 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1050_2336 : (Triangular src1050) 2336 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1050 : Cover (Triangular src1050) 2389 2293 [2295,2305,2335,2389] := by
  exact ⟨by decide, by decide, pass1050_2293, by decide, by decide, pass1050_2296, by decide, by decide, pass1050_2306, by decide, by decide, pass1050_2336, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 34

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 34, 10, 65/100, 60/100, ![1362085965864, 224130671484, 40634391060, 2390280510], 1184018490208312⟩
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

def data : NearCase 3 34 34 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons30.plan, Lower6960.Prefix6969MainCases.CubicSingletons30.price, Lower6960.Prefix6969MainCases.CubicSingletons30.valid, Lower6960.Prefix6969MainCases.CubicSingletons30.priced, Lower6960.Prefix6969MainCases.CubicSingletons30.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons30.plan, Lower6960.Prefix6969RescueData.CubicSingletons30.price, Lower6960.Prefix6969RescueData.CubicSingletons30.sources, Lower6960.Prefix6969RescueData.CubicSingletons30.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 204172713595211815 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 35 386045 := by
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

def price : Pricing := ⟨55/100, 100/100, [305329880, 305130587, 303980832, 303996140, 304332651, 303611047, 304023379, 304833414, 162801398, 162822377, 162678016, 162772102, 81615105, 81625947, 65406030, 78780736, 92893096, 92791505, 118258233, 165288645, 228667226], [1163057, 1164077, 1169959, 1169881, 1168159, 1171851, 1169741, 1165597, 2354038, 2353689, 2356089, 2354525, 4886074, 4885430, 6142688, 5070097, 4269440, 4274563, 3312195, 2312684, 1623592],
  ![121381136905320, 1612778275624, 205800503400, 5086729970], 164009547737592664⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1051 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,8,3,1,386045,35⟩
private theorem pass1051_2293 : (Triangular src1051) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1051_2302 : (Triangular src1051) 2302 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1051_2329 : (Triangular src1051) 2329 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1051 : Cover (Triangular src1051) 2389 2293 [2301,2328,2389] := by
  exact ⟨by decide, by decide, pass1051_2293, by decide, by decide, pass1051_2302, by decide, by decide, pass1051_2329, rfl⟩
def src1052 : Request := ⟨⟨⟨1200,1674,368,13899⟩,52718727069696,218807905514⟩,16,3,1,386045,35⟩
private theorem pass1052_2293 : (Triangular src1052) 2293 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1052_2305 : (Triangular src1052) 2305 2339 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1052_2340 : (Triangular src1052) 2340 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1052 : Cover (Triangular src1052) 2389 2293 [2304,2339,2389] := by
  exact ⟨by decide, by decide, pass1052_2293, by decide, by decide, pass1052_2305, by decide, by decide, pass1052_2340, rfl⟩
def src1053 : Request := ⟨⟨⟨2100,2929,662,19788⟩,288013660979200,2090961110089⟩,32,3,1,386045,35⟩
private theorem pass1053_2293 : (Triangular src1053) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1053_2294 : (Triangular src1053) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1053_2297 : (Triangular src1053) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1053_2305 : (Triangular src1053) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1053_2328 : (Triangular src1053) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1053 : Cover (Triangular src1053) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass1053_2293, by decide, by decide, pass1053_2294, by decide, by decide, pass1053_2297, by decide, by decide, pass1053_2305, by decide, by decide, pass1053_2328, rfl⟩
def src1056 : Request := ⟨⟨⟨3200,4464,1008,40111⟩,1017717693874176,11262426748352⟩,65,3,1,386045,35⟩
private theorem pass1056_2293 : (Triangular src1056) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1056_2295 : (Triangular src1056) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1056_2300 : (Triangular src1056) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1056_2314 : (Triangular src1056) 2314 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1056_2353 : (Triangular src1056) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1056 : Cover (Triangular src1056) 2389 2293 [2294,2299,2313,2352,2389] := by
  exact ⟨by decide, by decide, pass1056_2293, by decide, by decide, pass1056_2295, by decide, by decide, pass1056_2300, by decide, by decide, pass1056_2314, by decide, by decide, pass1056_2353, rfl⟩
def src1057 : Request := ⟨⟨⟨6900,9625,2118,81311⟩,9997036108906496,238335796784464⟩,145,3,1,386045,35⟩
private theorem pass1057_2293 : (Triangular src1057) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1057_2300 : (Triangular src1057) 2300 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1057_2319 : (Triangular src1057) 2319 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1057_2372 : (Triangular src1057) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1057 : Cover (Triangular src1057) 2389 2293 [2299,2318,2371,2389] := by
  exact ⟨by decide, by decide, pass1057_2293, by decide, by decide, pass1057_2300, by decide, by decide, pass1057_2319, by decide, by decide, pass1057_2372, rfl⟩
def src1058 : Request := ⟨⟨⟨8300,11577,2615,115771⟩,17745461310914560,509018341309343⟩,190,3,1,386045,35⟩
private theorem pass1058_2293 : (Triangular src1058) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1058_2294 : (Triangular src1058) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1058_2297 : (Triangular src1058) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1058_2305 : (Triangular src1058) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1058_2327 : (Triangular src1058) 2327 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1058_2387 : (Triangular src1058) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1058 : Cover (Triangular src1058) 2389 2293 [2293,2296,2304,2326,2386,2389] := by
  exact ⟨by decide, by decide, pass1058_2293, by decide, by decide, pass1058_2294, by decide, by decide, pass1058_2297, by decide, by decide, pass1058_2305, by decide, by decide, pass1058_2327, by decide, by decide, pass1058_2387, rfl⟩
def src1059 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,0,3,1,386045,36⟩
private theorem pass1059_2293 : (Triangular src1059) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1059_2296 : (Triangular src1059) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1059_2305 : (Triangular src1059) 2305 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1059_2335 : (Triangular src1059) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1059 : Cover (Triangular src1059) 2389 2293 [2295,2304,2334,2389] := by
  exact ⟨by decide, by decide, pass1059_2293, by decide, by decide, pass1059_2296, by decide, by decide, pass1059_2305, by decide, by decide, pass1059_2335, rfl⟩
def src1060 : Request := ⟨⟨⟨560,781,172,5419⟩,5388141854720,10440670587⟩,1,3,1,386045,36⟩
private theorem pass1060_2293 : (Triangular src1060) 2293 2310 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1060_2311 : (Triangular src1060) 2311 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1060_2368 : (Triangular src1060) 2368 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1060 : Cover (Triangular src1060) 2389 2293 [2310,2367,2389] := by
  exact ⟨by decide, by decide, pass1060_2293, by decide, by decide, pass1060_2311, by decide, by decide, pass1060_2368, rfl⟩
def src1061 : Request := ⟨⟨⟨560,781,172,6096⟩,5388141854720,10440670587⟩,2,3,1,386045,36⟩
private theorem pass1061_2293 : (Triangular src1061) 2293 2310 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1061_2311 : (Triangular src1061) 2311 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1061_2368 : (Triangular src1061) 2368 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1061 : Cover (Triangular src1061) 2389 2293 [2310,2367,2389] := by
  exact ⟨by decide, by decide, pass1061_2293, by decide, by decide, pass1061_2311, by decide, by decide, pass1061_2368, rfl⟩
def src1062 : Request := ⟨⟨⟨560,781,172,6858⟩,5388141854720,10440670587⟩,3,3,1,386045,36⟩
private theorem pass1062_2293 : (Triangular src1062) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1062_2298 : (Triangular src1062) 2298 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1062_2314 : (Triangular src1062) 2314 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1062_2365 : (Triangular src1062) 2365 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1062 : Cover (Triangular src1062) 2389 2293 [2297,2313,2364,2389] := by
  exact ⟨by decide, by decide, pass1062_2293, by decide, by decide, pass1062_2298, by decide, by decide, pass1062_2314, by decide, by decide, pass1062_2365, rfl⟩
def src1063 : Request := ⟨⟨⟨690,962,212,8679⟩,10065769922560,23997864317⟩,6,3,1,386045,36⟩
private theorem pass1063_2293 : (Triangular src1063) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1063_2306 : (Triangular src1063) 2306 2345 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1063_2346 : (Triangular src1063) 2346 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1063 : Cover (Triangular src1063) 2389 2293 [2305,2345,2389] := by
  exact ⟨by decide, by decide, pass1063_2293, by decide, by decide, pass1063_2306, by decide, by decide, pass1063_2346, rfl⟩
def src1064 : Request := ⟨⟨⟨825,1151,253,8679⟩,17161575202816,49010625289⟩,8,3,1,386045,36⟩
private theorem pass1064_2293 : (Triangular src1064) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1064_2298 : (Triangular src1064) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1064_2313 : (Triangular src1064) 2313 2357 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1064_2358 : (Triangular src1064) 2358 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1064 : Cover (Triangular src1064) 2389 2293 [2297,2312,2357,2389] := by
  exact ⟨by decide, by decide, pass1064_2293, by decide, by decide, pass1064_2298, by decide, by decide, pass1064_2313, by decide, by decide, pass1064_2358, rfl⟩
def src1065 : Request := ⟨⟨⟨1200,1674,368,12355⟩,52718727069696,218807905514⟩,16,3,1,386045,36⟩
private theorem pass1065_2293 : (Triangular src1065) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1065_2298 : (Triangular src1065) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1065_2313 : (Triangular src1065) 2313 2356 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1065_2357 : (Triangular src1065) 2357 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1065 : Cover (Triangular src1065) 2389 2293 [2297,2312,2356,2389] := by
  exact ⟨by decide, by decide, pass1065_2293, by decide, by decide, pass1065_2298, by decide, by decide, pass1065_2313, by decide, by decide, pass1065_2357, rfl⟩
def src1066 : Request := ⟨⟨⟨2100,2929,645,25043⟩,282396798484480,2049139102608⟩,40,3,1,386045,36⟩
private theorem pass1066_2293 : (Triangular src1066) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1066_2295 : (Triangular src1066) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1066_2301 : (Triangular src1066) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1066_2318 : (Triangular src1066) 2318 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1066_2366 : (Triangular src1066) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1066 : Cover (Triangular src1066) 2389 2293 [2294,2300,2317,2365,2389] := by
  exact ⟨by decide, by decide, pass1066_2293, by decide, by decide, pass1066_2295, by decide, by decide, pass1066_2301, by decide, by decide, pass1066_2318, by decide, by decide, pass1066_2366, rfl⟩
def src1069 : Request := ⟨⟨⟨4800,6695,1474,72277⟩,3367547627110400,55837558620681⟩,110,3,1,386045,36⟩
private theorem pass1069_2293 : (Triangular src1069) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1069_2297 : (Triangular src1069) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1069_2308 : (Triangular src1069) 2308 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1069_2338 : (Triangular src1069) 2338 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1069 : Cover (Triangular src1069) 2389 2293 [2296,2307,2337,2389] := by
  exact ⟨by decide, by decide, pass1069_2293, by decide, by decide, pass1069_2297, by decide, by decide, pass1069_2308, by decide, by decide, pass1069_2338, rfl⟩
def src1070 : Request := ⟨⟨⟨6900,9625,2118,72277⟩,9997036108906496,238335796784464⟩,145,3,1,386045,36⟩
private theorem pass1070_2293 : (Triangular src1070) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1070_2295 : (Triangular src1070) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1070_2301 : (Triangular src1070) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1070_2318 : (Triangular src1070) 2318 2363 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1070_2364 : (Triangular src1070) 2364 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1070 : Cover (Triangular src1070) 2389 2293 [2294,2300,2317,2363,2389] := by
  exact ⟨by decide, by decide, pass1070_2293, by decide, by decide, pass1070_2295, by decide, by decide, pass1070_2301, by decide, by decide, pass1070_2318, by decide, by decide, pass1070_2364, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 35

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 35, 10, 65/100, 60/100, ![1577408817750, 212247980703, 35630028750, 2036020695], 1092922023319813⟩
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

def data : NearCase 3 35 35 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons31.plan, Lower6960.Prefix6969MainCases.CubicSingletons31.price, Lower6960.Prefix6969MainCases.CubicSingletons31.valid, Lower6960.Prefix6969MainCases.CubicSingletons31.priced, Lower6960.Prefix6969MainCases.CubicSingletons31.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons31.plan, Lower6960.Prefix6969RescueData.CubicSingletons31.price, Lower6960.Prefix6969RescueData.CubicSingletons31.sources, Lower6960.Prefix6969RescueData.CubicSingletons31.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 203465670063713735 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 36 386045 := by
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

def price : Pricing := ⟨55/100, 100/100, [304172959, 303976140, 303857172, 302531021, 303138924, 303940900, 302715267, 162056251, 162133770, 161874340, 161614392, 75075630, 75510088, 78840451, 92185745, 91758567, 144723433, 228729603], [1168976, 1169983, 1170592, 1177376, 1174266, 1170163, 1176433, 2366427, 2365138, 2369452, 2373774, 5325983, 5295978, 5065973, 4305110, 4326651, 2666380, 1623079],
  ![121414247864460, 1612710811032, 205856642700, 5167292460], 163141840692202294⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 36

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 36, 9, 65/100, 70/100, ![1012929124411, 161481540562, 29682802074, 1649059974], 920940120408833⟩
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

def data : NearCase 3 36 36 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons32.plan, Lower6960.Prefix6969MainCases.CubicSingletons32.price, Lower6960.Prefix6969MainCases.CubicSingletons32.valid, Lower6960.Prefix6969MainCases.CubicSingletons32.priced, Lower6960.Prefix6969MainCases.CubicSingletons32.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons32.plan, Lower6960.Prefix6969RescueData.CubicSingletons32.price, Lower6960.Prefix6969RescueData.CubicSingletons32.sources, Lower6960.Prefix6969RescueData.CubicSingletons32.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 202896725322711207 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 37 386045 := by
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

def price : Pricing := ⟨55/100, 100/100, [302828350, 302486800, 300750102, 300679872, 302436629, 300771346, 301650577, 162885923, 162947141, 162938890, 162879889, 98121618, 81911160, 90381357, 90896204, 100963602, 165381949, 228104291], [1175855, 1177602, 1186487, 1186846, 1177859, 1186378, 1181880, 2352633, 2351615, 2351752, 2352733, 4033930, 4868495, 4396100, 4370138, 3913983, 2311133, 1628220],
  ![121082319748620, 1613386232044, 205293861900, 5231359000], 162334851372618251⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1071 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,0,3,1,386045,37⟩
private theorem pass1071_2293 : (Triangular src1071) 2293 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1071_2316 : (Triangular src1071) 2316 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1071 : Cover (Triangular src1071) 2389 2293 [2315,2389] := by
  exact ⟨by decide, by decide, pass1071_2293, by decide, by decide, pass1071_2316, rfl⟩
def src1072 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,1,3,1,386045,37⟩
private theorem pass1072_2293 : (Triangular src1072) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1072_2303 : (Triangular src1072) 2303 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1072_2335 : (Triangular src1072) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1072 : Cover (Triangular src1072) 2389 2293 [2302,2334,2389] := by
  exact ⟨by decide, by decide, pass1072_2293, by decide, by decide, pass1072_2303, by decide, by decide, pass1072_2335, rfl⟩
def src1073 : Request := ⟨⟨⟨560,781,172,5419⟩,5388141854720,10440670587⟩,2,3,1,386045,37⟩
private theorem pass1073_2293 : (Triangular src1073) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1073_2297 : (Triangular src1073) 2297 2309 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1073_2310 : (Triangular src1073) 2310 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1073_2351 : (Triangular src1073) 2351 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1073 : Cover (Triangular src1073) 2389 2293 [2296,2309,2350,2389] := by
  exact ⟨by decide, by decide, pass1073_2293, by decide, by decide, pass1073_2297, by decide, by decide, pass1073_2310, by decide, by decide, pass1073_2351, rfl⟩
def src1074 : Request := ⟨⟨⟨560,781,172,6096⟩,5388141854720,10440670587⟩,3,3,1,386045,37⟩
private theorem pass1074_2293 : (Triangular src1074) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1074_2297 : (Triangular src1074) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1074_2309 : (Triangular src1074) 2309 2346 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1074_2347 : (Triangular src1074) 2347 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1074 : Cover (Triangular src1074) 2389 2293 [2296,2308,2346,2389] := by
  exact ⟨by decide, by decide, pass1074_2293, by decide, by decide, pass1074_2297, by decide, by decide, pass1074_2309, by decide, by decide, pass1074_2347, rfl⟩
def src1075 : Request := ⟨⟨⟨560,781,172,7715⟩,5388141854720,10440670587⟩,4,3,1,386045,37⟩
private theorem pass1075_2293 : (Triangular src1075) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1075_2296 : (Triangular src1075) 2296 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1075_2306 : (Triangular src1075) 2306 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1075_2337 : (Triangular src1075) 2337 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1075 : Cover (Triangular src1075) 2389 2293 [2295,2305,2336,2389] := by
  exact ⟨by decide, by decide, pass1075_2293, by decide, by decide, pass1075_2296, by decide, by decide, pass1075_2306, by decide, by decide, pass1075_2337, rfl⟩
def src1076 : Request := ⟨⟨⟨690,962,212,7715⟩,10065769922560,23997864317⟩,6,3,1,386045,37⟩
private theorem pass1076_2293 : (Triangular src1076) 2293 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1076_2307 : (Triangular src1076) 2307 2349 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1076_2350 : (Triangular src1076) 2350 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1076 : Cover (Triangular src1076) 2389 2293 [2306,2349,2389] := by
  exact ⟨by decide, by decide, pass1076_2293, by decide, by decide, pass1076_2307, by decide, by decide, pass1076_2350, rfl⟩
def src1077 : Request := ⟨⟨⟨825,1151,253,9763⟩,17161575202816,49010625289⟩,10,3,1,386045,37⟩
private theorem pass1077_2293 : (Triangular src1077) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1077_2297 : (Triangular src1077) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1077_2309 : (Triangular src1077) 2309 2344 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1077_2345 : (Triangular src1077) 2345 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1077 : Cover (Triangular src1077) 2389 2293 [2296,2308,2344,2389] := by
  exact ⟨by decide, by decide, pass1077_2293, by decide, by decide, pass1077_2297, by decide, by decide, pass1077_2309, by decide, by decide, pass1077_2345, rfl⟩
def src1078 : Request := ⟨⟨⟨1450,2022,457,15636⟩,94890063298560,475487789910⟩,25,3,1,386045,37⟩
private theorem pass1078_2293 : (Triangular src1078) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1078_2294 : (Triangular src1078) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1078_2297 : (Triangular src1078) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1078_2306 : (Triangular src1078) 2306 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1078_2331 : (Triangular src1078) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1078 : Cover (Triangular src1078) 2389 2293 [2293,2296,2305,2330,2389] := by
  exact ⟨by decide, by decide, pass1078_2293, by decide, by decide, pass1078_2294, by decide, by decide, pass1078_2297, by decide, by decide, pass1078_2306, by decide, by decide, pass1078_2331, rfl⟩
def src1081 : Request := ⟨⟨⟨3950,5510,1213,45124⟩,1877062482395136,25622281045803⟩,85,3,1,386045,37⟩
private theorem pass1081_2293 : (Triangular src1081) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1081_2303 : (Triangular src1081) 2303 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1081_2331 : (Triangular src1081) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1081 : Cover (Triangular src1081) 2389 2293 [2302,2330,2389] := by
  exact ⟨by decide, by decide, pass1081_2293, by decide, by decide, pass1081_2303, by decide, by decide, pass1081_2331, rfl⟩
def src1082 : Request := ⟨⟨⟨8300,11577,2548,91474⟩,17399709518790656,498847383098023⟩,190,3,1,386045,37⟩
private theorem pass1082_2293 : (Triangular src1082) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1082_2297 : (Triangular src1082) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1082_2308 : (Triangular src1082) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1082_2339 : (Triangular src1082) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1082 : Cover (Triangular src1082) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass1082_2293, by decide, by decide, pass1082_2297, by decide, by decide, pass1082_2308, by decide, by decide, pass1082_2339, rfl⟩
def src1083 : Request := ⟨⟨⟨10000,13948,3070,130242⟩,30428373265940480,1050983571587703⟩,245,3,1,386045,37⟩
private theorem pass1083_2293 : (Triangular src1083) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1083_2297 : (Triangular src1083) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1083_2308 : (Triangular src1083) 2308 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1083_2338 : (Triangular src1083) 2338 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1083 : Cover (Triangular src1083) 2389 2293 [2296,2307,2337,2389] := by
  exact ⟨by decide, by decide, pass1083_2293, by decide, by decide, pass1083_2297, by decide, by decide, pass1083_2308, by decide, by decide, pass1083_2338, rfl⟩
def src1084 : Request := ⟨⟨⟨400,558,123,4817⟩,1971918995456,2734096379⟩,0,3,1,386045,38⟩
private theorem pass1084_2293 : (Triangular src1084) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1084_2295 : (Triangular src1084) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1084_2301 : (Triangular src1084) 2301 2321 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1084_2322 : (Triangular src1084) 2322 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1084 : Cover (Triangular src1084) 2389 2293 [2294,2300,2321,2389] := by
  exact ⟨by decide, by decide, pass1084_2293, by decide, by decide, pass1084_2295, by decide, by decide, pass1084_2301, by decide, by decide, pass1084_2322, rfl⟩
def src1085 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,1,3,1,386045,38⟩
private theorem pass1085_2293 : (Triangular src1085) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1085_2295 : (Triangular src1085) 2295 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1085_2302 : (Triangular src1085) 2302 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1085_2324 : (Triangular src1085) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1085 : Cover (Triangular src1085) 2389 2293 [2294,2301,2323,2389] := by
  exact ⟨by decide, by decide, pass1085_2293, by decide, by decide, pass1085_2295, by decide, by decide, pass1085_2302, by decide, by decide, pass1085_2324, rfl⟩
def src1086 : Request := ⟨⟨⟨560,781,169,6096⟩,5316921262080,10299257375⟩,3,3,1,386045,38⟩
private theorem pass1086_2293 : (Triangular src1086) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1086_2298 : (Triangular src1086) 2298 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1086_2314 : (Triangular src1086) 2314 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1086_2365 : (Triangular src1086) 2365 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1086 : Cover (Triangular src1086) 2389 2293 [2297,2313,2364,2389] := by
  exact ⟨by decide, by decide, pass1086_2293, by decide, by decide, pass1086_2298, by decide, by decide, pass1086_2314, by decide, by decide, pass1086_2365, rfl⟩
def src1087 : Request := ⟨⟨⟨560,781,172,6858⟩,5388141854720,10440670587⟩,4,3,1,386045,38⟩
private theorem pass1087_2293 : (Triangular src1087) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1087_2303 : (Triangular src1087) 2303 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1087_2335 : (Triangular src1087) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1087 : Cover (Triangular src1087) 2389 2293 [2302,2334,2389] := by
  exact ⟨by decide, by decide, pass1087_2293, by decide, by decide, pass1087_2303, by decide, by decide, pass1087_2335, rfl⟩
def src1088 : Request := ⟨⟨⟨690,962,212,6858⟩,10065769922560,23997864317⟩,6,3,1,386045,38⟩
private theorem pass1088_2293 : (Triangular src1088) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1088_2297 : (Triangular src1088) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1088_2309 : (Triangular src1088) 2309 2345 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1088_2346 : (Triangular src1088) 2346 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1088 : Cover (Triangular src1088) 2389 2293 [2296,2308,2345,2389] := by
  exact ⟨by decide, by decide, pass1088_2293, by decide, by decide, pass1088_2297, by decide, by decide, pass1088_2309, by decide, by decide, pass1088_2346, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 37

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 37, 10, 65/100, 70/100, ![1875984408312, 258090437514, 44219776520, 2390280510], 1148557371085573⟩
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

def data : NearCase 3 37 37 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons33.plan, Lower6960.Prefix6969MainCases.CubicSingletons33.price, Lower6960.Prefix6969MainCases.CubicSingletons33.valid, Lower6960.Prefix6969MainCases.CubicSingletons33.priced, Lower6960.Prefix6969MainCases.CubicSingletons33.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons33.plan, Lower6960.Prefix6969RescueData.CubicSingletons33.price, Lower6960.Prefix6969RescueData.CubicSingletons33.sources, Lower6960.Prefix6969RescueData.CubicSingletons33.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 201687127030135632 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 38 386045 := by
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

def price : Pricing := ⟨55/100, 100/100, [300379682, 300201069, 299878460, 300022359, 299959754, 299907905, 299739632, 150219189, 150146358, 150169921, 150448250, 150344926, 48388627, 62568867, 81353410, 93869446, 94190277, 118719391, 229276141], [1188382, 1189295, 1190946, 1190210, 1190530, 1190795, 1191656, 2563234, 2564445, 2564053, 2559425, 2561143, 8376129, 6433493, 4901614, 4220206, 4204027, 3299304, 1618585],
  ![121704361165620, 1612120136744, 206348526900, 5022045140], 161399458161933297⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 22 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1089 : Request := ⟨⟨⟨825,1151,260,8679⟩,17518948515840,50057971890⟩,10,3,1,386045,38⟩
private theorem pass1089_2293 : (Triangular src1089) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1089_2298 : (Triangular src1089) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1089_2313 : (Triangular src1089) 2313 2357 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1089_2358 : (Triangular src1089) 2358 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1089 : Cover (Triangular src1089) 2389 2293 [2297,2312,2357,2389] := by
  exact ⟨by decide, by decide, pass1089_2293, by decide, by decide, pass1089_2298, by decide, by decide, pass1089_2313, by decide, by decide, pass1089_2358, rfl⟩
def src1090 : Request := ⟨⟨⟨1000,1395,315,12355⟩,31157463285760,107844841957⟩,16,3,1,386045,38⟩
private theorem pass1090_2293 : (Triangular src1090) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1090_2296 : (Triangular src1090) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1090_2305 : (Triangular src1090) 2305 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1090_2331 : (Triangular src1090) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1090 : Cover (Triangular src1090) 2389 2293 [2295,2304,2330,2389] := by
  exact ⟨by decide, by decide, pass1090_2293, by decide, by decide, pass1090_2296, by decide, by decide, pass1090_2305, by decide, by decide, pass1090_2331, rfl⟩
def src1091 : Request := ⟨⟨⟨1750,2441,551,17590⟩,166595992223744,1008217465165⟩,32,3,1,386045,38⟩
private theorem pass1091_2293 : (Triangular src1091) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1091_2299 : (Triangular src1091) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1091_2316 : (Triangular src1091) 2316 2363 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1091_2364 : (Triangular src1091) 2364 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1091 : Cover (Triangular src1091) 2389 2293 [2298,2315,2363,2389] := by
  exact ⟨by decide, by decide, pass1091_2293, by decide, by decide, pass1091_2299, by decide, by decide, pass1091_2316, by decide, by decide, pass1091_2364, rfl⟩
def src1094 : Request := ⟨⟨⟨3950,5510,1213,40111⟩,1877062482395136,25622281045803⟩,85,3,1,386045,38⟩
private theorem pass1094_2293 : (Triangular src1094) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1094_2296 : (Triangular src1094) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1094_2304 : (Triangular src1094) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1094_2326 : (Triangular src1094) 2326 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1094_2388 : (Triangular src1094) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1094 : Cover (Triangular src1094) 2389 2293 [2295,2303,2325,2387,2389] := by
  exact ⟨by decide, by decide, pass1094_2293, by decide, by decide, pass1094_2296, by decide, by decide, pass1094_2304, by decide, by decide, pass1094_2326, by decide, by decide, pass1094_2388, rfl⟩
def src1095 : Request := ⟨⟨⟨5700,7950,1796,91474⟩,5749327563587584,113242283843565⟩,145,3,1,386045,38⟩
private theorem pass1095_2293 : (Triangular src1095) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1095_2294 : (Triangular src1095) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1095_2297 : (Triangular src1095) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1095_2305 : (Triangular src1095) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1095_2327 : (Triangular src1095) 2327 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1095_2387 : (Triangular src1095) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1095 : Cover (Triangular src1095) 2389 2293 [2293,2296,2304,2326,2386,2389] := by
  exact ⟨by decide, by decide, pass1095_2293, by decide, by decide, pass1095_2294, by decide, by decide, pass1095_2297, by decide, by decide, pass1095_2305, by decide, by decide, pass1095_2327, by decide, by decide, pass1095_2387, rfl⟩
def src1096 : Request := ⟨⟨⟨8300,11577,2615,81311⟩,17745461310914560,509018341309343⟩,190,3,1,386045,38⟩
private theorem pass1096_2293 : (Triangular src1096) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1096_2295 : (Triangular src1096) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1096_2300 : (Triangular src1096) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1096_2314 : (Triangular src1096) 2314 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1096_2353 : (Triangular src1096) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1096 : Cover (Triangular src1096) 2389 2293 [2294,2299,2313,2352,2389] := by
  exact ⟨by decide, by decide, pass1096_2293, by decide, by decide, pass1096_2295, by decide, by decide, pass1096_2300, by decide, by decide, pass1096_2314, by decide, by decide, pass1096_2353, rfl⟩
def src1097 : Request := ⟨⟨⟨400,558,126,4282⟩,2007957766144,2785382344⟩,0,3,1,386045,39⟩
private theorem pass1097_2293 : (Triangular src1097) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1097_2294 : (Triangular src1097) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1097_2297 : (Triangular src1097) 2297 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1097_2307 : (Triangular src1097) 2307 2340 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1097_2341 : (Triangular src1097) 2341 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1097 : Cover (Triangular src1097) 2389 2293 [2293,2296,2306,2340,2389] := by
  exact ⟨by decide, by decide, pass1097_2293, by decide, by decide, pass1097_2294, by decide, by decide, pass1097_2297, by decide, by decide, pass1097_2307, by decide, by decide, pass1097_2341, rfl⟩
def src1098 : Request := ⟨⟨⟨470,655,144,4817⟩,3184589537280,5168862572⟩,1,3,1,386045,39⟩
private theorem pass1098_2293 : (Triangular src1098) 2293 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1098_2315 : (Triangular src1098) 2315 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1098_2387 : (Triangular src1098) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1098 : Cover (Triangular src1098) 2389 2293 [2314,2386,2389] := by
  exact ⟨by decide, by decide, pass1098_2293, by decide, by decide, pass1098_2315, by decide, by decide, pass1098_2387, rfl⟩
def src1099 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,2,3,1,386045,39⟩
private theorem pass1099_2293 : (Triangular src1099) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1099_2301 : (Triangular src1099) 2301 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1099_2327 : (Triangular src1099) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1099 : Cover (Triangular src1099) 2389 2293 [2300,2326,2389] := by
  exact ⟨by decide, by decide, pass1099_2293, by decide, by decide, pass1099_2301, by decide, by decide, pass1099_2327, rfl⟩
def src1100 : Request := ⟨⟨⟨560,781,172,5419⟩,5388141854720,10440670587⟩,3,3,1,386045,39⟩
private theorem pass1100_2293 : (Triangular src1100) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1100_2302 : (Triangular src1100) 2302 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1100_2331 : (Triangular src1100) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1100 : Cover (Triangular src1100) 2389 2293 [2301,2330,2389] := by
  exact ⟨by decide, by decide, pass1100_2293, by decide, by decide, pass1100_2302, by decide, by decide, pass1100_2331, rfl⟩
def src1101 : Request := ⟨⟨⟨560,781,172,6096⟩,5388141854720,10440670587⟩,4,3,1,386045,39⟩
private theorem pass1101_2293 : (Triangular src1101) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1101_2302 : (Triangular src1101) 2302 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1101_2330 : (Triangular src1101) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1101 : Cover (Triangular src1101) 2389 2293 [2301,2329,2389] := by
  exact ⟨by decide, by decide, pass1101_2293, by decide, by decide, pass1101_2302, by decide, by decide, pass1101_2330, rfl⟩
def src1102 : Request := ⟨⟨⟨690,962,217,7715⟩,10244384358400,24434817260⟩,8,3,1,386045,39⟩
private theorem pass1102_2293 : (Triangular src1102) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1102_2296 : (Triangular src1102) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1102_2305 : (Triangular src1102) 2305 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1102_2333 : (Triangular src1102) 2333 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1102 : Cover (Triangular src1102) 2389 2293 [2295,2304,2332,2389] := by
  exact ⟨by decide, by decide, pass1102_2293, by decide, by decide, pass1102_2296, by decide, by decide, pass1102_2305, by decide, by decide, pass1102_2333, rfl⟩
def src1103 : Request := ⟨⟨⟨1450,2022,457,13899⟩,94890063298560,475487789910⟩,25,3,1,386045,39⟩
private theorem pass1103_2293 : (Triangular src1103) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1103_2300 : (Triangular src1103) 2300 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1103_2320 : (Triangular src1103) 2320 2377 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1103_2378 : (Triangular src1103) 2378 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1103 : Cover (Triangular src1103) 2389 2293 [2299,2319,2377,2389] := by
  exact ⟨by decide, by decide, pass1103_2293, by decide, by decide, pass1103_2300, by decide, by decide, pass1103_2320, by decide, by decide, pass1103_2378, rfl⟩
def src1106 : Request := ⟨⟨⟨4800,6695,1474,50764⟩,3367547627110400,55837558620681⟩,110,3,1,386045,39⟩
private theorem pass1106_2293 : (Triangular src1106) 2293 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1106_2307 : (Triangular src1106) 2307 2345 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1106_2346 : (Triangular src1106) 2346 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1106 : Cover (Triangular src1106) 2389 2293 [2306,2345,2389] := by
  exact ⟨by decide, by decide, pass1106_2293, by decide, by decide, pass1106_2307, by decide, by decide, pass1106_2346, rfl⟩
def src1107 : Request := ⟨⟨⟨5700,7950,1750,72277⟩,5637370734182400,110980791054694⟩,145,3,1,386045,39⟩
private theorem pass1107_2293 : (Triangular src1107) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1107_2299 : (Triangular src1107) 2299 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1107_2315 : (Triangular src1107) 2315 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1107_2360 : (Triangular src1107) 2360 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1107 : Cover (Triangular src1107) 2389 2293 [2298,2314,2359,2389] := by
  exact ⟨by decide, by decide, pass1107_2293, by decide, by decide, pass1107_2299, by decide, by decide, pass1107_2315, by decide, by decide, pass1107_2360, rfl⟩
def src1108 : Request := ⟨⟨⟨8300,11577,2548,81311⟩,17399709518790656,498847383098023⟩,190,3,1,386045,39⟩
private theorem pass1108_2293 : (Triangular src1108) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1108_2303 : (Triangular src1108) 2303 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1108_2330 : (Triangular src1108) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1108 : Cover (Triangular src1108) 2389 2293 [2302,2329,2389] := by
  exact ⟨by decide, by decide, pass1108_2293, by decide, by decide, pass1108_2303, by decide, by decide, pass1108_2330, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 38

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 38, 10, 65/100, 60/100, ![1353186590672, 195884188559, 38684029720, 2036020695], 939420121702229⟩
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

def data : NearCase 3 38 38 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons34.plan, Lower6960.Prefix6969MainCases.CubicSingletons34.price, Lower6960.Prefix6969MainCases.CubicSingletons34.valid, Lower6960.Prefix6969MainCases.CubicSingletons34.priced, Lower6960.Prefix6969MainCases.CubicSingletons34.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons34.plan, Lower6960.Prefix6969RescueData.CubicSingletons34.price, Lower6960.Prefix6969RescueData.CubicSingletons34.sources, Lower6960.Prefix6969RescueData.CubicSingletons34.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 201103651198539079 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 39 386045 := by
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

def price : Pricing := ⟨55/100, 100/100, [300080212, 298615597, 299924480, 298793822, 299785168, 298196344, 299827350, 303870521, 162037606, 162055162, 162159585, 162182314, 84853257, 84803697, 70449002, 70728502, 92038513, 92040086, 117272017, 163847188, 227567951], [1189914, 1197406, 1190710, 1196495, 1191423, 1199551, 1191207, 1170523, 2366737, 2366445, 2364709, 2364331, 4693794, 4696737, 5690424, 5668211, 4312534, 4312455, 3339764, 2336650, 1632630],
  ![120797619749820, 1613965807684, 204811155900, 5131915460], 160925895885246443⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 39

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 39, 10, 65/100, 60/100, ![1562392580268, 244063230402, 47824626150, 2452567950], 1046808744058354⟩
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

def data : NearCase 3 39 39 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons35.plan, Lower6960.Prefix6969MainCases.CubicSingletons35.price, Lower6960.Prefix6969MainCases.CubicSingletons35.valid, Lower6960.Prefix6969MainCases.CubicSingletons35.priced, Lower6960.Prefix6969MainCases.CubicSingletons35.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons35.plan, Lower6960.Prefix6969RescueData.CubicSingletons35.price, Lower6960.Prefix6969RescueData.CubicSingletons35.sources, Lower6960.Prefix6969RescueData.CubicSingletons35.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 201286072397461659 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 40 386045 := by
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

def price : Pricing := ⟨55/100, 100/100, [298849332, 297686968, 296729157, 298152266, 298738484, 297045943, 297534484, 301544676, 161410202, 161256956, 161425347, 161464292, 161493506, 94565103, 67841949, 67884706, 91459820, 91556563, 116929090, 163504260, 227306430], [1196211, 1202157, 1207057, 1199777, 1196778, 1205436, 1202937, 1182422, 2377169, 2379716, 2376917, 2376269, 2375784, 4185126, 5920109, 5916234, 4341716, 4336838, 3349350, 2342352, 1634780],
  ![120658799172600, 1614248235720, 204575787000, 5166642040], 160198038732519707⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 40

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 40, 10, 65/100, 60/100, ![1424406966436, 187214713668, 33852906236, 1692661182], 874113516183286⟩
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

def data : NearCase 3 40 40 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons36.plan, Lower6960.Prefix6969MainCases.CubicSingletons36.price, Lower6960.Prefix6969MainCases.CubicSingletons36.valid, Lower6960.Prefix6969MainCases.CubicSingletons36.priced, Lower6960.Prefix6969MainCases.CubicSingletons36.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons36.plan, Lower6960.Prefix6969RescueData.CubicSingletons36.price, Lower6960.Prefix6969RescueData.CubicSingletons36.sources, Lower6960.Prefix6969RescueData.CubicSingletons36.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 200780997010654257 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 8 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [344910724, 343543275, 343587378, 344813584, 343470304, 343956311, 343870609, 343751460, 170619178, 171284734, 171075623, 170652381, 82087383, 85661319, 66605234, 90228690, 103947573, 103747405, 126389466, 173419878, 234894192], [1001210, 1004957, 1004836, 1001476, 1005157, 1003825, 1004060, 1004387, 2224801, 2216775, 2219297, 2224400, 4858031, 4645812, 6032183, 4403798, 3788124, 3796492, 3084894, 2191028, 1572395],
  ![124686534997440, 1606051240428, 211404772800, 4517825480], 189716594817458431⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src713 : Request := ⟨⟨⟨2600,3627,783,375939⟩,527755772952576,4741611634368⟩,32,3,1,386045,8⟩
private theorem pass713_2293 : (Triangular src713) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass713_2294 : (Triangular src713) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass713_2297 : (Triangular src713) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass713_2305 : (Triangular src713) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass713_2328 : (Triangular src713) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover713 : Cover (Triangular src713) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass713_2293, by decide, by decide, pass713_2294, by decide, by decide, pass713_2297, by decide, by decide, pass713_2305, by decide, by decide, pass713_2328, rfl⟩
def src714 : Request := ⟨⟨⟨3950,5512,1189,185441⟩,1848744952463360,25255771038451⟩,32,3,1,386045,8⟩
private theorem pass714_2293 : (Triangular src714) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass714_2294 : (Triangular src714) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass714_2296 : (Triangular src714) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass714_2302 : (Triangular src714) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass714_2319 : (Triangular src714) 2319 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass714_2366 : (Triangular src714) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover714 : Cover (Triangular src714) 2389 2293 [2293,2295,2301,2318,2365,2389] := by
  exact ⟨by decide, by decide, pass714_2293, by decide, by decide, pass714_2294, by decide, by decide, pass714_2296, by decide, by decide, pass714_2302, by decide, by decide, pass714_2319, by decide, by decide, pass714_2366, rfl⟩
def src715 : Request := ⟨⟨⟨6900,9628,2077,334168⟩,9849424459857920,234966243278304⟩,65,3,1,386045,8⟩
private theorem pass715_2293 : (Triangular src715) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass715_2295 : (Triangular src715) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass715_2301 : (Triangular src715) 2301 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass715_2317 : (Triangular src715) 2317 2360 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass715_2361 : (Triangular src715) 2361 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover715 : Cover (Triangular src715) 2389 2293 [2294,2300,2316,2360,2389] := by
  exact ⟨by decide, by decide, pass715_2293, by decide, by decide, pass715_2295, by decide, by decide, pass715_2301, by decide, by decide, pass715_2317, by decide, by decide, pass715_2361, rfl⟩
def src716 : Request := ⟨⟨⟨10000,13954,3010,422931⟩,29974681586237440,1036364370066239⟩,85,3,1,386045,8⟩
private theorem pass716_2293 : (Triangular src716) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass716_2299 : (Triangular src716) 2299 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass716_2315 : (Triangular src716) 2315 2358 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass716_2359 : (Triangular src716) 2359 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover716 : Cover (Triangular src716) 2389 2293 [2298,2314,2358,2389] := by
  exact ⟨by decide, by decide, pass716_2293, by decide, by decide, pass716_2299, by decide, by decide, pass716_2315, by decide, by decide, pass716_2359, rfl⟩
def src717 : Request := ⟨⟨⟨1000,1395,301,45124⟩,30103476895744,104105680031⟩,0,3,1,386045,9⟩
private theorem pass717_2293 : (Triangular src717) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass717_2300 : (Triangular src717) 2300 2320 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass717_2321 : (Triangular src717) 2321 2382 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass717_2383 : (Triangular src717) 2383 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover717 : Cover (Triangular src717) 2389 2293 [2299,2320,2382,2389] := by
  exact ⟨by decide, by decide, pass717_2293, by decide, by decide, pass717_2300, by decide, by decide, pass717_2321, by decide, by decide, pass717_2383, rfl⟩
def src718 : Request := ⟨⟨⟨1000,1395,301,50764⟩,30103476895744,104105680031⟩,1,3,1,386045,9⟩
private theorem pass718_2293 : (Triangular src718) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass718_2298 : (Triangular src718) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass718_2313 : (Triangular src718) 2313 2357 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass718_2358 : (Triangular src718) 2358 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover718 : Cover (Triangular src718) 2389 2293 [2297,2312,2357,2389] := by
  exact ⟨by decide, by decide, pass718_2293, by decide, by decide, pass718_2298, by decide, by decide, pass718_2313, by decide, by decide, pass718_2358, rfl⟩
def src719 : Request := ⟨⟨⟨1000,1395,301,57109⟩,30103476895744,104105680031⟩,2,3,1,386045,9⟩
private theorem pass719_2293 : (Triangular src719) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass719_2295 : (Triangular src719) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass719_2301 : (Triangular src719) 2301 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass719_2319 : (Triangular src719) 2319 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass719_2372 : (Triangular src719) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover719 : Cover (Triangular src719) 2389 2293 [2294,2300,2318,2371,2389] := by
  exact ⟨by decide, by decide, pass719_2293, by decide, by decide, pass719_2295, by decide, by decide, pass719_2301, by decide, by decide, pass719_2319, by decide, by decide, pass719_2372, rfl⟩
def src720 : Request := ⟨⟨⟨1200,1674,361,64247⟩,51955677528064,215563369662⟩,4,3,1,386045,9⟩
private theorem pass720_2293 : (Triangular src720) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass720_2295 : (Triangular src720) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass720_2300 : (Triangular src720) 2300 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass720_2315 : (Triangular src720) 2315 2358 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass720_2359 : (Triangular src720) 2359 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover720 : Cover (Triangular src720) 2389 2293 [2294,2299,2314,2358,2389] := by
  exact ⟨by decide, by decide, pass720_2293, by decide, by decide, pass720_2295, by decide, by decide, pass720_2300, by decide, by decide, pass720_2315, by decide, by decide, pass720_2359, rfl⟩
def src721 : Request := ⟨⟨⟨1450,2023,436,72277⟩,91566841790464,459151377566⟩,6,3,1,386045,9⟩
private theorem pass721_2293 : (Triangular src721) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass721_2298 : (Triangular src721) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass721_2312 : (Triangular src721) 2312 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass721_2353 : (Triangular src721) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover721 : Cover (Triangular src721) 2389 2293 [2297,2311,2352,2389] := by
  exact ⟨by decide, by decide, pass721_2293, by decide, by decide, pass721_2298, by decide, by decide, pass721_2312, by decide, by decide, pass721_2353, rfl⟩
def src722 : Request := ⟨⟨⟨1750,2442,527,91474⟩,161065121873920,975196209190⟩,10,3,1,386045,9⟩
private theorem pass722_2293 : (Triangular src722) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass722_2298 : (Triangular src722) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass722_2313 : (Triangular src722) 2313 2355 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass722_2356 : (Triangular src722) 2356 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover722 : Cover (Triangular src722) 2389 2293 [2297,2312,2355,2389] := by
  exact ⟨by decide, by decide, pass722_2293, by decide, by decide, pass722_2298, by decide, by decide, pass722_2313, by decide, by decide, pass722_2356, rfl⟩
def src723 : Request := ⟨⟨⟨2600,3628,770,115771⟩,521059839508480,4684185417862⟩,16,3,1,386045,9⟩
private theorem pass723_2293 : (Triangular src723) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass723_2294 : (Triangular src723) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass723_2297 : (Triangular src723) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass723_2306 : (Triangular src723) 2306 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass723_2331 : (Triangular src723) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover723 : Cover (Triangular src723) 2389 2293 [2293,2296,2305,2330,2389] := by
  exact ⟨by decide, by decide, pass723_2293, by decide, by decide, pass723_2294, by decide, by decide, pass723_2297, by decide, by decide, pass723_2306, by decide, by decide, pass723_2331, rfl⟩
def src725 : Request := ⟨⟨⟨3950,5512,1189,146522⟩,1848744952463360,25255771038451⟩,25,3,1,386045,9⟩
private theorem pass725_2293 : (Triangular src725) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass725_2295 : (Triangular src725) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass725_2301 : (Triangular src725) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass725_2318 : (Triangular src725) 2318 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass725_2365 : (Triangular src725) 2365 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover725 : Cover (Triangular src725) 2389 2293 [2294,2300,2317,2364,2389] := by
  exact ⟨by decide, by decide, pass725_2293, by decide, by decide, pass725_2295, by decide, by decide, pass725_2301, by decide, by decide, pass725_2318, by decide, by decide, pass725_2365, rfl⟩
def src727 : Request := ⟨⟨⟨4800,6698,1445,208621⟩,3317023033262080,55058665830093⟩,40,3,1,386045,9⟩
private theorem pass727_2293 : (Triangular src727) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass727_2295 : (Triangular src727) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass727_2300 : (Triangular src727) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass727_2314 : (Triangular src727) 2314 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass727_2353 : (Triangular src727) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover727 : Cover (Triangular src727) 2389 2293 [2294,2299,2313,2352,2389] := by
  exact ⟨by decide, by decide, pass727_2293, by decide, by decide, pass727_2295, by decide, by decide, pass727_2300, by decide, by decide, pass727_2314, by decide, by decide, pass727_2353, rfl⟩
def src728 : Request := ⟨⟨⟨4800,6697,1445,535271⟩,3317023033262080,55032215749682⟩,65,3,1,386045,9⟩
private theorem pass728_2293 : (Triangular src728) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass728_2294 : (Triangular src728) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass728_2297 : (Triangular src728) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass728_2305 : (Triangular src728) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass728_2328 : (Triangular src728) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover728 : Cover (Triangular src728) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass728_2293, by decide, by decide, pass728_2294, by decide, by decide, pass728_2297, by decide, by decide, pass728_2305, by decide, by decide, pass728_2328, rfl⟩
def src729 : Request := ⟨⟨⟨10000,13953,3010,535271⟩,29974681586237440,1036125345444439⟩,110,3,1,386045,9⟩
private theorem pass729_2293 : (Triangular src729) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass729_2296 : (Triangular src729) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass729_2304 : (Triangular src729) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass729_2326 : (Triangular src729) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass729_2387 : (Triangular src729) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover729 : Cover (Triangular src729) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass729_2293, by decide, by decide, pass729_2296, by decide, by decide, pass729_2304, by decide, by decide, pass729_2326, by decide, by decide, pass729_2387, rfl⟩
def src730 : Request := ⟨⟨⟨1000,1395,296,45124⟩,29722184515584,102755930405⟩,0,3,1,386045,10⟩
private theorem pass730_2293 : (Triangular src730) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass730_2299 : (Triangular src730) 2299 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass730_2317 : (Triangular src730) 2317 2370 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass730_2371 : (Triangular src730) 2371 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover730 : Cover (Triangular src730) 2389 2293 [2298,2316,2370,2389] := by
  exact ⟨by decide, by decide, pass730_2293, by decide, by decide, pass730_2299, by decide, by decide, pass730_2317, by decide, by decide, pass730_2371, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 8

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 8, 9, 95/100, 80/100, ![1317153468126, 363374518707, 9374181460, 2343564930], 8777637794238153⟩
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

def data : NearCase 3 8 8 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons4.plan, Lower6960.Prefix6969MainCases.CubicSingletons4.price, Lower6960.Prefix6969MainCases.CubicSingletons4.valid, Lower6960.Prefix6969MainCases.CubicSingletons4.priced, Lower6960.Prefix6969MainCases.CubicSingletons4.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons4.plan, Lower6960.Prefix6969RescueData.CubicSingletons4.price, Lower6960.Prefix6969RescueData.CubicSingletons4.sources, Lower6960.Prefix6969RescueData.CubicSingletons4.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 223125203153572067 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 9 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [343641084, 340941862, 342408099, 342410683, 343110075, 343510802, 343026186, 147118620, 147358119, 147528797, 147159164, 74223356, 74411283, 89784125, 103179208, 103067425, 125904459, 172934871, 234524152], [1004689, 1012087, 1008068, 1008061, 1006144, 1005046, 1006374, 2614785, 2610803, 2607965, 2614110, 5390449, 5375513, 4426216, 3820473, 3825191, 3098452, 2196877, 1575437],
  ![124490110364640, 1606450783508, 211071736800, 4551977290], 187812098618473477⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 9

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 9, 10, 95/100, 80/100, ![1875396351169, 455098575280, 10545953390, 2343564930], 8362963765477525⟩
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

def data : NearCase 3 9 9 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons5.plan, Lower6960.Prefix6969MainCases.CubicSingletons5.price, Lower6960.Prefix6969MainCases.CubicSingletons5.valid, Lower6960.Prefix6969MainCases.CubicSingletons5.priced, Lower6960.Prefix6969MainCases.CubicSingletons5.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons5.plan, Lower6960.Prefix6969RescueData.CubicSingletons5.price, Lower6960.Prefix6969RescueData.CubicSingletons5.sources, Lower6960.Prefix6969RescueData.CubicSingletons5.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 223016717996659926 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 10 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [342402278, 341232983, 341292954, 341652789, 342004062, 340613795, 150440488, 150377921, 150469907, 150449223, 92897403, 114081140, 74770370, 69755332, 91927760, 106978032, 107005349, 151588154, 234483700], [1008084, 1011289, 1011124, 1010138, 1009176, 1012986, 2559554, 2560594, 2559065, 2559409, 4269223, 3436345, 5347065, 5746713, 4318119, 3682924, 3681976, 2540473, 1575770],
  ![124468637634000, 1606494702200, 211035330000, 4404481380], 187433523425525656⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src731 : Request := ⟨⟨⟨1200,1674,361,45124⟩,51955677528064,215563369662⟩,1,3,1,386045,10⟩
private theorem pass731_2293 : (Triangular src731) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass731_2296 : (Triangular src731) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass731_2305 : (Triangular src731) 2305 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass731_2332 : (Triangular src731) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover731 : Cover (Triangular src731) 2389 2293 [2295,2304,2331,2389] := by
  exact ⟨by decide, by decide, pass731_2293, by decide, by decide, pass731_2296, by decide, by decide, pass731_2305, by decide, by decide, pass731_2332, rfl⟩
def src732 : Request := ⟨⟨⟨1200,1674,361,50764⟩,51955677528064,215563369662⟩,2,3,1,386045,10⟩
private theorem pass732_2293 : (Triangular src732) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass732_2300 : (Triangular src732) 2300 2320 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass732_2321 : (Triangular src732) 2321 2381 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass732_2382 : (Triangular src732) 2382 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover732 : Cover (Triangular src732) 2389 2293 [2299,2320,2381,2389] := by
  exact ⟨by decide, by decide, pass732_2293, by decide, by decide, pass732_2300, by decide, by decide, pass732_2321, by decide, by decide, pass732_2382, rfl⟩
def src733 : Request := ⟨⟨⟨1450,2023,436,57109⟩,91566841790464,459151377566⟩,4,3,1,386045,10⟩
private theorem pass733_2293 : (Triangular src733) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass733_2296 : (Triangular src733) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass733_2305 : (Triangular src733) 2305 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass733_2331 : (Triangular src733) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover733 : Cover (Triangular src733) 2389 2293 [2295,2304,2330,2389] := by
  exact ⟨by decide, by decide, pass733_2293, by decide, by decide, pass733_2296, by decide, by decide, pass733_2305, by decide, by decide, pass733_2331, rfl⟩
def src734 : Request := ⟨⟨⟨1750,2442,527,72277⟩,161065121873920,975196209190⟩,8,3,1,386045,10⟩
private theorem pass734_2293 : (Triangular src734) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass734_2294 : (Triangular src734) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass734_2297 : (Triangular src734) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass734_2306 : (Triangular src734) 2306 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass734_2331 : (Triangular src734) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover734 : Cover (Triangular src734) 2389 2293 [2293,2296,2305,2330,2389] := by
  exact ⟨by decide, by decide, pass734_2293, by decide, by decide, pass734_2294, by decide, by decide, pass734_2297, by decide, by decide, pass734_2306, by decide, by decide, pass734_2331, rfl⟩
def src735 : Request := ⟨⟨⟨2600,3628,783,102908⟩,527755772952576,4745819470168⟩,16,3,1,386045,10⟩
private theorem pass735_2293 : (Triangular src735) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass735_2295 : (Triangular src735) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass735_2300 : (Triangular src735) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass735_2314 : (Triangular src735) 2314 2353 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass735_2354 : (Triangular src735) 2354 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover735 : Cover (Triangular src735) 2389 2293 [2294,2299,2313,2353,2389] := by
  exact ⟨by decide, by decide, pass735_2293, by decide, by decide, pass735_2295, by decide, by decide, pass735_2300, by decide, by decide, pass735_2314, by decide, by decide, pass735_2354, rfl⟩
def src736 : Request := ⟨⟨⟨4800,6698,1445,164837⟩,3317023033262080,55058665830093⟩,32,3,1,386045,10⟩
private theorem pass736_2293 : (Triangular src736) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass736_2294 : (Triangular src736) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass736_2297 : (Triangular src736) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass736_2305 : (Triangular src736) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass736_2328 : (Triangular src736) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover736 : Cover (Triangular src736) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass736_2293, by decide, by decide, pass736_2294, by decide, by decide, pass736_2297, by decide, by decide, pass736_2305, by decide, by decide, pass736_2328, rfl⟩
def src737 : Request := ⟨⟨⟨6900,9628,2077,297039⟩,9849424459857920,234966243278304⟩,65,3,1,386045,10⟩
private theorem pass737_2293 : (Triangular src737) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass737_2294 : (Triangular src737) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass737_2297 : (Triangular src737) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass737_2305 : (Triangular src737) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass737_2327 : (Triangular src737) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass737_2388 : (Triangular src737) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover737 : Cover (Triangular src737) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass737_2293, by decide, by decide, pass737_2294, by decide, by decide, pass737_2297, by decide, by decide, pass737_2305, by decide, by decide, pass737_2327, by decide, by decide, pass737_2388, rfl⟩
def src738 : Request := ⟨⟨⟨5700,7952,1716,857398⟩,5553838907981824,109384694947514⟩,85,3,1,386045,10⟩
private theorem pass738_2293 : (Triangular src738) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass738_2294 : (Triangular src738) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass738_2296 : (Triangular src738) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass738_2302 : (Triangular src738) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass738_2319 : (Triangular src738) 2319 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass738_2366 : (Triangular src738) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover738 : Cover (Triangular src738) 2389 2293 [2293,2295,2301,2318,2365,2389] := by
  exact ⟨by decide, by decide, pass738_2293, by decide, by decide, pass738_2294, by decide, by decide, pass738_2296, by decide, by decide, pass738_2302, by decide, by decide, pass738_2319, by decide, by decide, pass738_2366, rfl⟩
def src739 : Request := ⟨⟨⟨10000,13954,3010,375939⟩,29974681586237440,1036364370066239⟩,85,3,1,386045,10⟩
private theorem pass739_2293 : (Triangular src739) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass739_2297 : (Triangular src739) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass739_2309 : (Triangular src739) 2309 2341 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass739_2342 : (Triangular src739) 2342 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover739 : Cover (Triangular src739) 2389 2293 [2296,2308,2341,2389] := by
  exact ⟨by decide, by decide, pass739_2293, by decide, by decide, pass739_2297, by decide, by decide, pass739_2309, by decide, by decide, pass739_2342, rfl⟩
def src740 : Request := ⟨⟨⟨1000,1395,301,40111⟩,30103476895744,104105680031⟩,0,3,1,386045,11⟩
private theorem pass740_2293 : (Triangular src740) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass740_2300 : (Triangular src740) 2300 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass740_2320 : (Triangular src740) 2320 2379 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass740_2380 : (Triangular src740) 2380 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover740 : Cover (Triangular src740) 2389 2293 [2299,2319,2379,2389] := by
  exact ⟨by decide, by decide, pass740_2293, by decide, by decide, pass740_2300, by decide, by decide, pass740_2320, by decide, by decide, pass740_2380, rfl⟩
def src741 : Request := ⟨⟨⟨1000,1395,301,45124⟩,30103476895744,104105680031⟩,1,3,1,386045,11⟩
private theorem pass741_2293 : (Triangular src741) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass741_2298 : (Triangular src741) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass741_2313 : (Triangular src741) 2313 2357 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass741_2358 : (Triangular src741) 2358 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover741 : Cover (Triangular src741) 2389 2293 [2297,2312,2357,2389] := by
  exact ⟨by decide, by decide, pass741_2293, by decide, by decide, pass741_2298, by decide, by decide, pass741_2313, by decide, by decide, pass741_2358, rfl⟩
def src742 : Request := ⟨⟨⟨1000,1395,301,50764⟩,30103476895744,104105680031⟩,2,3,1,386045,11⟩
private theorem pass742_2293 : (Triangular src742) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass742_2295 : (Triangular src742) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass742_2301 : (Triangular src742) 2301 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass742_2319 : (Triangular src742) 2319 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass742_2372 : (Triangular src742) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover742 : Cover (Triangular src742) 2389 2293 [2294,2300,2318,2371,2389] := by
  exact ⟨by decide, by decide, pass742_2293, by decide, by decide, pass742_2295, by decide, by decide, pass742_2301, by decide, by decide, pass742_2319, by decide, by decide, pass742_2372, rfl⟩
def src743 : Request := ⟨⟨⟨1200,1674,361,57109⟩,51955677528064,215563369662⟩,4,3,1,386045,11⟩
private theorem pass743_2293 : (Triangular src743) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass743_2295 : (Triangular src743) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass743_2300 : (Triangular src743) 2300 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass743_2315 : (Triangular src743) 2315 2358 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass743_2359 : (Triangular src743) 2359 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover743 : Cover (Triangular src743) 2389 2293 [2294,2299,2314,2358,2389] := by
  exact ⟨by decide, by decide, pass743_2293, by decide, by decide, pass743_2295, by decide, by decide, pass743_2300, by decide, by decide, pass743_2315, by decide, by decide, pass743_2359, rfl⟩
def src744 : Request := ⟨⟨⟨1750,2442,527,81311⟩,161065121873920,975196209190⟩,10,3,1,386045,11⟩
private theorem pass744_2293 : (Triangular src744) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass744_2298 : (Triangular src744) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass744_2313 : (Triangular src744) 2313 2355 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass744_2356 : (Triangular src744) 2356 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover744 : Cover (Triangular src744) 2389 2293 [2297,2312,2355,2389] := by
  exact ⟨by decide, by decide, pass744_2293, by decide, by decide, pass744_2298, by decide, by decide, pass744_2313, by decide, by decide, pass744_2356, rfl⟩
def src745 : Request := ⟨⟨⟨2600,3628,783,102908⟩,527755772952576,4745819470168⟩,16,3,1,386045,11⟩
private theorem pass745_2293 : (Triangular src745) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass745_2303 : (Triangular src745) 2303 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass745_2331 : (Triangular src745) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover745 : Cover (Triangular src745) 2389 2293 [2302,2330,2389] := by
  exact ⟨by decide, by decide, pass745_2293, by decide, by decide, pass745_2303, by decide, by decide, pass745_2331, rfl⟩
def src746 : Request := ⟨⟨⟨3950,5512,1189,130242⟩,1848744952463360,25255771038451⟩,25,3,1,386045,11⟩
private theorem pass746_2293 : (Triangular src746) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass746_2295 : (Triangular src746) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass746_2301 : (Triangular src746) 2301 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass746_2317 : (Triangular src746) 2317 2361 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass746_2362 : (Triangular src746) 2362 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover746 : Cover (Triangular src746) 2389 2293 [2294,2300,2316,2361,2389] := by
  exact ⟨by decide, by decide, pass746_2293, by decide, by decide, pass746_2295, by decide, by decide, pass746_2301, by decide, by decide, pass746_2317, by decide, by decide, pass746_2362, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 10

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 10, 9, 95/100, 80/100, ![3337792110936, 691840404966, 11717725320, 2343564930], 9781829422427091⟩
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

def data : NearCase 3 10 10 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons6.plan, Lower6960.Prefix6969MainCases.CubicSingletons6.price, Lower6960.Prefix6969MainCases.CubicSingletons6.valid, Lower6960.Prefix6969MainCases.CubicSingletons6.priced, Lower6960.Prefix6969MainCases.CubicSingletons6.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons6.plan, Lower6960.Prefix6969RescueData.CubicSingletons6.price, Lower6960.Prefix6969RescueData.CubicSingletons6.sources, Lower6960.Prefix6969RescueData.CubicSingletons6.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 224127827806289869 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 11 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [339646300, 339388551, 338868966, 339352465, 337550263, 338544552, 338876011, 339208881, 169324804, 169596432, 169532204, 169607335, 80220871, 84541964, 67225139, 88470296, 102746252, 102457988, 125193031, 172223443, 233980418], [1015637, 1016344, 1017768, 1016443, 1021382, 1018657, 1017748, 1016836, 2245578, 2241062, 2242130, 2240881, 4970637, 4712279, 5976005, 4492469, 3838746, 3850912, 3118339, 2205455, 1579908],
  ![124201485482760, 1607038457272, 210582376200, 4582585280], 186371611678738908⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src747 : Request := ⟨⟨⟨4800,6698,1445,185441⟩,3317023033262080,55058665830093⟩,40,3,1,386045,11⟩
private theorem pass747_2293 : (Triangular src747) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass747_2294 : (Triangular src747) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass747_2297 : (Triangular src747) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass747_2305 : (Triangular src747) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass747_2328 : (Triangular src747) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover747 : Cover (Triangular src747) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass747_2293, by decide, by decide, pass747_2294, by decide, by decide, pass747_2297, by decide, by decide, pass747_2305, by decide, by decide, pass747_2328, rfl⟩
def src748 : Request := ⟨⟨⟨5700,7952,1716,857398⟩,5553838907981824,109384694947514⟩,85,3,1,386045,11⟩
private theorem pass748_2293 : (Triangular src748) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass748_2296 : (Triangular src748) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass748_2304 : (Triangular src748) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass748_2326 : (Triangular src748) 2326 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass748_2388 : (Triangular src748) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover748 : Cover (Triangular src748) 2389 2293 [2295,2303,2325,2387,2389] := by
  exact ⟨by decide, by decide, pass748_2293, by decide, by decide, pass748_2296, by decide, by decide, pass748_2304, by decide, by decide, pass748_2326, by decide, by decide, pass748_2388, rfl⟩
def src749 : Request := ⟨⟨⟨6900,9626,2077,1545055⟩,9849424459857920,234809190715807⟩,110,3,1,386045,11⟩
private theorem pass749_2293 : (Triangular src749) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass749_2296 : (Triangular src749) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass749_2304 : (Triangular src749) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass749_2326 : (Triangular src749) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass749_2387 : (Triangular src749) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover749 : Cover (Triangular src749) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass749_2293, by decide, by decide, pass749_2296, by decide, by decide, pass749_2304, by decide, by decide, pass749_2326, by decide, by decide, pass749_2387, rfl⟩
def src750 : Request := ⟨⟨⟨10000,13953,3010,475797⟩,29974681586237440,1036125345444439⟩,110,3,1,386045,11⟩
private theorem pass750_2293 : (Triangular src750) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass750_2296 : (Triangular src750) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass750_2304 : (Triangular src750) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass750_2326 : (Triangular src750) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass750_2387 : (Triangular src750) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover750 : Cover (Triangular src750) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass750_2293, by decide, by decide, pass750_2296, by decide, by decide, pass750_2304, by decide, by decide, pass750_2326, by decide, by decide, pass750_2387, rfl⟩
def src751 : Request := ⟨⟨⟨1000,1395,296,40111⟩,29722184515584,102755930405⟩,0,3,1,386045,12⟩
private theorem pass751_2293 : (Triangular src751) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass751_2299 : (Triangular src751) 2299 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass751_2317 : (Triangular src751) 2317 2370 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass751_2371 : (Triangular src751) 2371 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover751 : Cover (Triangular src751) 2389 2293 [2298,2316,2370,2389] := by
  exact ⟨by decide, by decide, pass751_2293, by decide, by decide, pass751_2299, by decide, by decide, pass751_2317, by decide, by decide, pass751_2371, rfl⟩
def src752 : Request := ⟨⟨⟨1200,1674,361,40111⟩,51955677528064,215563369662⟩,1,3,1,386045,12⟩
private theorem pass752_2293 : (Triangular src752) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass752_2297 : (Triangular src752) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass752_2309 : (Triangular src752) 2309 2343 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass752_2344 : (Triangular src752) 2344 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover752 : Cover (Triangular src752) 2389 2293 [2296,2308,2343,2389] := by
  exact ⟨by decide, by decide, pass752_2293, by decide, by decide, pass752_2297, by decide, by decide, pass752_2309, by decide, by decide, pass752_2344, rfl⟩
def src753 : Request := ⟨⟨⟨1200,1674,361,45124⟩,51955677528064,215563369662⟩,2,3,1,386045,12⟩
private theorem pass753_2293 : (Triangular src753) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass753_2301 : (Triangular src753) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass753_2324 : (Triangular src753) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover753 : Cover (Triangular src753) 2389 2293 [2300,2323,2389] := by
  exact ⟨by decide, by decide, pass753_2293, by decide, by decide, pass753_2301, by decide, by decide, pass753_2324, rfl⟩
def src754 : Request := ⟨⟨⟨1200,1674,361,57109⟩,51955677528064,215563369662⟩,4,3,1,386045,12⟩
private theorem pass754_2293 : (Triangular src754) 2293 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass754_2302 : (Triangular src754) 2302 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass754_2328 : (Triangular src754) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover754 : Cover (Triangular src754) 2389 2293 [2301,2327,2389] := by
  exact ⟨by decide, by decide, pass754_2293, by decide, by decide, pass754_2302, by decide, by decide, pass754_2328, rfl⟩
def src755 : Request := ⟨⟨⟨1450,2023,436,72277⟩,91566841790464,459151377566⟩,8,3,1,386045,12⟩
private theorem pass755_2293 : (Triangular src755) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass755_2295 : (Triangular src755) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass755_2301 : (Triangular src755) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass755_2318 : (Triangular src755) 2318 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass755_2368 : (Triangular src755) 2368 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover755 : Cover (Triangular src755) 2389 2293 [2294,2300,2317,2367,2389] := by
  exact ⟨by decide, by decide, pass755_2293, by decide, by decide, pass755_2295, by decide, by decide, pass755_2301, by decide, by decide, pass755_2318, by decide, by decide, pass755_2368, rfl⟩
def src756 : Request := ⟨⟨⟨2100,2930,632,72277⟩,278060332482560,2019119590628⟩,10,3,1,386045,12⟩
private theorem pass756_2293 : (Triangular src756) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass756_2299 : (Triangular src756) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass756_2316 : (Triangular src756) 2316 2363 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass756_2364 : (Triangular src756) 2364 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover756 : Cover (Triangular src756) 2389 2293 [2298,2315,2363,2389] := by
  exact ⟨by decide, by decide, pass756_2293, by decide, by decide, pass756_2299, by decide, by decide, pass756_2316, by decide, by decide, pass756_2364, rfl⟩
def src757 : Request := ⟨⟨⟨2600,3628,783,91474⟩,527755772952576,4745819470168⟩,16,3,1,386045,12⟩
private theorem pass757_2293 : (Triangular src757) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass757_2295 : (Triangular src757) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass757_2301 : (Triangular src757) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass757_2318 : (Triangular src757) 2318 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass757_2366 : (Triangular src757) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover757 : Cover (Triangular src757) 2389 2293 [2294,2300,2317,2365,2389] := by
  exact ⟨by decide, by decide, pass757_2293, by decide, by decide, pass757_2295, by decide, by decide, pass757_2301, by decide, by decide, pass757_2318, by decide, by decide, pass757_2366, rfl⟩
def src758 : Request := ⟨⟨⟨3950,5512,1213,146522⟩,1877062482395136,25652240151764⟩,32,3,1,386045,12⟩
private theorem pass758_2293 : (Triangular src758) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass758_2294 : (Triangular src758) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass758_2297 : (Triangular src758) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass758_2305 : (Triangular src758) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass758_2327 : (Triangular src758) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass758_2388 : (Triangular src758) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover758 : Cover (Triangular src758) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass758_2293, by decide, by decide, pass758_2294, by decide, by decide, pass758_2297, by decide, by decide, pass758_2305, by decide, by decide, pass758_2327, by decide, by decide, pass758_2388, rfl⟩
def src759 : Request := ⟨⟨⟨6900,9628,2077,264035⟩,9849424459857920,234966243278304⟩,65,3,1,386045,12⟩
private theorem pass759_2293 : (Triangular src759) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass759_2295 : (Triangular src759) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass759_2300 : (Triangular src759) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass759_2314 : (Triangular src759) 2314 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass759_2353 : (Triangular src759) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover759 : Cover (Triangular src759) 2389 2293 [2294,2299,2313,2352,2389] := by
  exact ⟨by decide, by decide, pass759_2293, by decide, by decide, pass759_2295, by decide, by decide, pass759_2300, by decide, by decide, pass759_2314, by decide, by decide, pass759_2353, rfl⟩
def src760 : Request := ⟨⟨⟨5700,7952,1716,762132⟩,5553838907981824,109384694947514⟩,85,3,1,386045,12⟩
private theorem pass760_2293 : (Triangular src760) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass760_2294 : (Triangular src760) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass760_2297 : (Triangular src760) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass760_2305 : (Triangular src760) 2305 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass760_2327 : (Triangular src760) 2327 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass760_2388 : (Triangular src760) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover760 : Cover (Triangular src760) 2389 2293 [2293,2296,2304,2326,2387,2389] := by
  exact ⟨by decide, by decide, pass760_2293, by decide, by decide, pass760_2294, by decide, by decide, pass760_2297, by decide, by decide, pass760_2305, by decide, by decide, pass760_2327, by decide, by decide, pass760_2388, rfl⟩
def src761 : Request := ⟨⟨⟨10000,13954,3010,334168⟩,29974681586237440,1036364370066239⟩,85,3,1,386045,12⟩
private theorem pass761_2293 : (Triangular src761) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass761_2298 : (Triangular src761) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass761_2312 : (Triangular src761) 2312 2349 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass761_2350 : (Triangular src761) 2350 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover761 : Cover (Triangular src761) 2389 2293 [2297,2311,2349,2389] := by
  exact ⟨by decide, by decide, pass761_2293, by decide, by decide, pass761_2298, by decide, by decide, pass761_2312, by decide, by decide, pass761_2350, rfl⟩
def src762 : Request := ⟨⟨⟨1000,1395,301,35655⟩,30103476895744,104105680031⟩,0,3,1,386045,13⟩
private theorem pass762_2293 : (Triangular src762) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass762_2301 : (Triangular src762) 2301 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass762_2325 : (Triangular src762) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover762 : Cover (Triangular src762) 2389 2293 [2300,2324,2389] := by
  exact ⟨by decide, by decide, pass762_2293, by decide, by decide, pass762_2301, by decide, by decide, pass762_2325, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 11

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 11, 10, 95/100, 80/100, ![6616273147375, 1235295524140, 12889497250, 2343564930], 11774938830138528⟩
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

def data : NearCase 3 11 11 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons7.plan, Lower6960.Prefix6969MainCases.CubicSingletons7.price, Lower6960.Prefix6969MainCases.CubicSingletons7.valid, Lower6960.Prefix6969MainCases.CubicSingletons7.priced, Lower6960.Prefix6969MainCases.CubicSingletons7.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons7.plan, Lower6960.Prefix6969RescueData.CubicSingletons7.price, Lower6960.Prefix6969RescueData.CubicSingletons7.sources, Lower6960.Prefix6969RescueData.CubicSingletons7.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 224504506107431076 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 12 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [337929640, 337203915, 336343554, 336973518, 337035968, 336473837, 336963882, 336056069, 167518851, 167678598, 167724165, 167978182, 65013774, 84196654, 65784139, 88125172, 102452891, 102308034, 125053890, 172084302, 233871985], [1020342, 1022331, 1024689, 1022962, 1022791, 1024332, 1022989, 1025477, 2275604, 2272948, 2272191, 2267967, 6182894, 4732783, 6106592, 4509872, 3851127, 3857241, 3122229, 2207133, 1580799],
  ![124143927077700, 1607155323920, 210484786500, 4600069440], 185356166028058433⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 12

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 12, 10, 90/100, 80/100, ![3560312594244, 622522220288, 14061266170, 2343564930], 8469166872017306⟩
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

def data : NearCase 3 12 12 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons8.plan, Lower6960.Prefix6969MainCases.CubicSingletons8.price, Lower6960.Prefix6969MainCases.CubicSingletons8.valid, Lower6960.Prefix6969MainCases.CubicSingletons8.priced, Lower6960.Prefix6969MainCases.CubicSingletons8.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons8.plan, Lower6960.Prefix6969RescueData.CubicSingletons8.price, Lower6960.Prefix6969RescueData.CubicSingletons8.sources, Lower6960.Prefix6969RescueData.CubicSingletons8.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 224872440712378249 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 13 386045 := by
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

def price : Pricing := ⟨55/100, 90/100, [336212980, 334985949, 334873450, 335233376, 334204762, 335120347, 335028610, 334363921, 167871179, 167963321, 168198603, 168319668, 81915988, 83851345, 65696987, 88667432, 102667053, 102888670, 124914750, 171945162, 233763552], [1025047, 1028409, 1028718, 1027731, 1030550, 1028041, 1028293, 1030114, 2269746, 2268214, 2264303, 2262290, 4868208, 4753287, 6114490, 4482528, 3842089, 3832735, 3126118, 2208811, 1581691],
  ![124086368672640, 1607272721388, 210387196800, 4572178560], 184345531981673311⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 13

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 13, 10, 90/100, 80/100, ![3857005246920, 624949851436, 15233038100, 2343564930], 7843537881376542⟩
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

def data : NearCase 3 13 13 386045 :=
  ⟨Lower6960.Prefix6969MainCases.CubicSingletons9.plan, Lower6960.Prefix6969MainCases.CubicSingletons9.price, Lower6960.Prefix6969MainCases.CubicSingletons9.valid, Lower6960.Prefix6969MainCases.CubicSingletons9.priced, Lower6960.Prefix6969MainCases.CubicSingletons9.sources,
   Lower6960.Prefix6969RescueData.CubicSingletons9.plan, Lower6960.Prefix6969RescueData.CubicSingletons9.price, Lower6960.Prefix6969RescueData.CubicSingletons9.sources, Lower6960.Prefix6969RescueData.CubicSingletons9.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 225258811970291901 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 1 386045 := by
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

def price : Pricing := ⟨55/100, 80/100, [358647564, 356396580, 357398106, 357571189, 357751774, 358365782, 188859074, 188866086, 188900511, 125852357, 87998777, 125917758, 76864796, 73151109, 99350135, 94048835, 109203280, 151720217, 241800140], [963562, 969731, 966987, 966512, 966017, 964335, 2004852, 2004768, 2004353, 3099908, 4516246, 3098080, 5202417, 5475668, 3982080, 4211160, 3605676, 2538277, 1515616],
  ![128352350314800, 1598590944880, 217620126000, 4295383200], 201874038042547494⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src643 : Request := ⟨⟨⟨1200,1674,355,102908⟩,51296765214720,212765123946⟩,4,3,1,386045,1⟩
private theorem pass643_2293 : (Triangular src643) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass643_2298 : (Triangular src643) 2298 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass643_2313 : (Triangular src643) 2313 2356 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass643_2357 : (Triangular src643) 2357 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover643 : Cover (Triangular src643) 2389 2293 [2297,2312,2356,2389] := by
  exact ⟨by decide, by decide, pass643_2293, by decide, by decide, pass643_2298, by decide, by decide, pass643_2313, by decide, by decide, pass643_2357, rfl⟩
def src644 : Request := ⟨⟨⟨1450,2023,436,102908⟩,91566841790464,459151377566⟩,6,3,1,386045,1⟩
private theorem pass644_2293 : (Triangular src644) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass644_2295 : (Triangular src644) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass644_2301 : (Triangular src644) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass644_2318 : (Triangular src644) 2318 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass644_2368 : (Triangular src644) 2368 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover644 : Cover (Triangular src644) 2389 2293 [2294,2300,2317,2367,2389] := by
  exact ⟨by decide, by decide, pass644_2293, by decide, by decide, pass644_2295, by decide, by decide, pass644_2301, by decide, by decide, pass644_2318, by decide, by decide, pass644_2368, rfl⟩
def src645 : Request := ⟨⟨⟨1750,2442,527,115771⟩,161065121873920,975196209190⟩,8,3,1,386045,1⟩
private theorem pass645_2293 : (Triangular src645) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass645_2300 : (Triangular src645) 2300 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass645_2320 : (Triangular src645) 2320 2376 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass645_2377 : (Triangular src645) 2377 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover645 : Cover (Triangular src645) 2389 2293 [2299,2319,2376,2389] := by
  exact ⟨by decide, by decide, pass645_2293, by decide, by decide, pass645_2300, by decide, by decide, pass645_2320, by decide, by decide, pass645_2377, rfl⟩
def src646 : Request := ⟨⟨⟨1750,2442,527,130242⟩,161065121873920,975196209190⟩,10,3,1,386045,1⟩
private theorem pass646_2293 : (Triangular src646) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass646_2296 : (Triangular src646) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass646_2304 : (Triangular src646) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass646_2327 : (Triangular src646) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover646 : Cover (Triangular src646) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass646_2293, by decide, by decide, pass646_2296, by decide, by decide, pass646_2304, by decide, by decide, pass646_2327, rfl⟩
def src647 : Request := ⟨⟨⟨2100,2930,632,146522⟩,278060332482560,2019119590628⟩,13,3,1,386045,1⟩
private theorem pass647_2293 : (Triangular src647) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass647_2297 : (Triangular src647) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass647_2308 : (Triangular src647) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass647_2339 : (Triangular src647) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover647 : Cover (Triangular src647) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass647_2293, by decide, by decide, pass647_2297, by decide, by decide, pass647_2308, by decide, by decide, pass647_2339, rfl⟩
def src648 : Request := ⟨⟨⟨3200,4465,963,185441⟩,983050615259136,10877088344236⟩,20,3,1,386045,1⟩
private theorem pass648_2293 : (Triangular src648) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass648_2298 : (Triangular src648) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass648_2312 : (Triangular src648) 2312 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass648_2352 : (Triangular src648) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover648 : Cover (Triangular src648) 2389 2293 [2297,2311,2351,2389] := by
  exact ⟨by decide, by decide, pass648_2293, by decide, by decide, pass648_2298, by decide, by decide, pass648_2312, by decide, by decide, pass648_2352, rfl⟩
def src651 : Request := ⟨⟨⟨5700,7953,1716,375939⟩,5553838907981824,109428971647179⟩,50,3,1,386045,1⟩
private theorem pass651_2293 : (Triangular src651) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass651_2299 : (Triangular src651) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass651_2316 : (Triangular src651) 2316 2362 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass651_2363 : (Triangular src651) 2363 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover651 : Cover (Triangular src651) 2389 2293 [2298,2315,2362,2389] := by
  exact ⟨by decide, by decide, pass651_2293, by decide, by decide, pass651_2299, by decide, by decide, pass651_2316, by decide, by decide, pass651_2363, rfl⟩
def src652 : Request := ⟨⟨⟨1000,1395,296,64247⟩,29722184515584,102755930405⟩,0,3,1,386045,2⟩
private theorem pass652_2293 : (Triangular src652) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass652_2295 : (Triangular src652) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass652_2301 : (Triangular src652) 2301 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass652_2319 : (Triangular src652) 2319 2372 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass652_2373 : (Triangular src652) 2373 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover652 : Cover (Triangular src652) 2389 2293 [2294,2300,2318,2372,2389] := by
  exact ⟨by decide, by decide, pass652_2293, by decide, by decide, pass652_2295, by decide, by decide, pass652_2301, by decide, by decide, pass652_2319, by decide, by decide, pass652_2373, rfl⟩
def src653 : Request := ⟨⟨⟨1000,1395,301,72277⟩,30103476895744,104105680031⟩,1,3,1,386045,2⟩
private theorem pass653_2293 : (Triangular src653) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass653_2301 : (Triangular src653) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass653_2324 : (Triangular src653) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover653 : Cover (Triangular src653) 2389 2293 [2300,2323,2389] := by
  exact ⟨by decide, by decide, pass653_2293, by decide, by decide, pass653_2301, by decide, by decide, pass653_2324, rfl⟩
def src654 : Request := ⟨⟨⟨1000,1395,301,81311⟩,30103476895744,104105680031⟩,2,3,1,386045,2⟩
private theorem pass654_2293 : (Triangular src654) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass654_2297 : (Triangular src654) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass654_2309 : (Triangular src654) 2309 2343 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass654_2344 : (Triangular src654) 2344 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover654 : Cover (Triangular src654) 2389 2293 [2296,2308,2343,2389] := by
  exact ⟨by decide, by decide, pass654_2293, by decide, by decide, pass654_2297, by decide, by decide, pass654_2309, by decide, by decide, pass654_2344, rfl⟩
def src655 : Request := ⟨⟨⟨1200,1674,361,91474⟩,51955677528064,215563369662⟩,4,3,1,386045,2⟩
private theorem pass655_2293 : (Triangular src655) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass655_2297 : (Triangular src655) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass655_2309 : (Triangular src655) 2309 2343 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass655_2344 : (Triangular src655) 2344 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover655 : Cover (Triangular src655) 2389 2293 [2296,2308,2343,2389] := by
  exact ⟨by decide, by decide, pass655_2293, by decide, by decide, pass655_2297, by decide, by decide, pass655_2309, by decide, by decide, pass655_2344, rfl⟩
def src656 : Request := ⟨⟨⟨1450,2023,436,102908⟩,91566841790464,459151377566⟩,6,3,1,386045,2⟩
private theorem pass656_2293 : (Triangular src656) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass656_2300 : (Triangular src656) 2300 2320 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass656_2321 : (Triangular src656) 2321 2381 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass656_2382 : (Triangular src656) 2382 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover656 : Cover (Triangular src656) 2389 2293 [2299,2320,2381,2389] := by
  exact ⟨by decide, by decide, pass656_2293, by decide, by decide, pass656_2300, by decide, by decide, pass656_2321, by decide, by decide, pass656_2382, rfl⟩
def src657 : Request := ⟨⟨⟨1750,2442,527,130242⟩,161065121873920,975196209190⟩,10,3,1,386045,2⟩
private theorem pass657_2293 : (Triangular src657) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass657_2301 : (Triangular src657) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass657_2324 : (Triangular src657) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover657 : Cover (Triangular src657) 2389 2293 [2300,2323,2389] := by
  exact ⟨by decide, by decide, pass657_2293, by decide, by decide, pass657_2301, by decide, by decide, pass657_2324, rfl⟩
def src658 : Request := ⟨⟨⟨2100,2930,622,146522⟩,274699477319680,1994139134137⟩,13,3,1,386045,2⟩
private theorem pass658_2293 : (Triangular src658) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass658_2295 : (Triangular src658) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass658_2300 : (Triangular src658) 2300 2314 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass658_2315 : (Triangular src658) 2315 2357 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass658_2358 : (Triangular src658) 2358 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover658 : Cover (Triangular src658) 2389 2293 [2294,2299,2314,2357,2389] := by
  exact ⟨by decide, by decide, pass658_2293, by decide, by decide, pass658_2295, by decide, by decide, pass658_2300, by decide, by decide, pass658_2315, by decide, by decide, pass658_2358, rfl⟩
def src659 : Request := ⟨⟨⟨2600,3628,783,185441⟩,527755772952576,4745819470168⟩,20,3,1,386045,2⟩
private theorem pass659_2293 : (Triangular src659) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass659_2296 : (Triangular src659) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass659_2304 : (Triangular src659) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass659_2327 : (Triangular src659) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover659 : Cover (Triangular src659) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass659_2293, by decide, by decide, pass659_2296, by decide, by decide, pass659_2304, by decide, by decide, pass659_2327, rfl⟩
def src661 : Request := ⟨⟨⟨3200,4465,963,208621⟩,983050615259136,10877088344236⟩,25,3,1,386045,2⟩
private theorem pass661_2293 : (Triangular src661) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass661_2295 : (Triangular src661) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass661_2300 : (Triangular src661) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass661_2314 : (Triangular src661) 2314 2353 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass661_2354 : (Triangular src661) 2354 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover661 : Cover (Triangular src661) 2389 2293 [2294,2299,2313,2353,2389] := by
  exact ⟨by decide, by decide, pass661_2293, by decide, by decide, pass661_2295, by decide, by decide, pass661_2300, by decide, by decide, pass661_2314, by decide, by decide, pass661_2354, rfl⟩
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
  physicalFloor := 386045
  seedFloor := 1

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 1, 9, 100/100, 80/100, ![146351924883, 295131519216, 668033652, 1336065588], 10479554191300970⟩
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

def data : NearCase 3 1 1 386045 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases0.plan, Lower6960.Prefix6969MainCases.HigherHelperCases0.price, Lower6960.Prefix6969MainCases.HigherHelperCases0.valid, Lower6960.Prefix6969MainCases.HigherHelperCases0.priced, Lower6960.Prefix6969MainCases.HigherHelperCases0.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases0.plan, Lower6960.Prefix6969RescueData.HigherHelperCases0.price, Lower6960.Prefix6969RescueData.HigherHelperCases0.sources, Lower6960.Prefix6969RescueData.HigherHelperCases0.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 214658272027375692 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 3 2 386045 := by
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

def price : Pricing := ⟨55/100, 80/100, [357350668, 357282902, 357279163, 357133150, 355390221, 356594952, 356888435, 162501166, 162477607, 162381925, 162428242, 78776582, 78759359, 98672379, 89848447, 103831948, 151567728, 241681304], [967117, 967302, 967313, 967713, 972489, 969188, 968383, 2359030, 2359422, 2361012, 2360242, 5070384, 5071573, 4010685, 4422973, 3792924, 2540812, 1516593],
  ![128289269789280, 1598719298596, 217513173600, 4513579560], 200591231401405081⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 386045
  seedFloor := 2

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨3, 3, 10, 95/100, 80/100, ![890081006556, 606170783945, 3515327830, 2343564930], 13254840508233937⟩
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

def data : NearCase 3 2 3 386045 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases1.plan, Lower6960.Prefix6969MainCases.HigherHelperCases1.price, Lower6960.Prefix6969MainCases.HigherHelperCases1.valid, Lower6960.Prefix6969MainCases.HigherHelperCases1.priced, Lower6960.Prefix6969MainCases.HigherHelperCases1.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases1.plan, Lower6960.Prefix6969RescueData.HigherHelperCases1.price, Lower6960.Prefix6969RescueData.HigherHelperCases1.sources, Lower6960.Prefix6969RescueData.HigherHelperCases1.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 222353717163634296 := by
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
    ∃ l u w : ℕ, l≤seed j ∧ seed j≤u ∧ w≤386045 ∧ ∃ c : NearCase 3 l u w, c.uniform := by
  fin_cases j
  · refine ⟨1, 1, 386045, by decide, by decide, by decide, NearSavedHigherHelperCases0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases0.fee_exact]; decide +kernel
  · refine ⟨2, 3, 386045, by decide, by decide, by decide, NearSavedHigherHelperCases1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases1.fee_exact]; decide +kernel
  · refine ⟨2, 3, 386045, by decide, by decide, by decide, NearSavedHigherHelperCases1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedHigherHelperCases1.fee_exact]; decide +kernel
  · refine ⟨4, 4, 386045, by decide, by decide, by decide, NearSavedCubicSingletons0.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons0.fee_exact]; decide +kernel
  · refine ⟨5, 5, 386045, by decide, by decide, by decide, NearSavedCubicSingletons1.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons1.fee_exact]; decide +kernel
  · refine ⟨6, 6, 386045, by decide, by decide, by decide, NearSavedCubicSingletons2.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons2.fee_exact]; decide +kernel
  · refine ⟨7, 7, 386045, by decide, by decide, by decide, NearSavedCubicSingletons3.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons3.fee_exact]; decide +kernel
  · refine ⟨8, 8, 386045, by decide, by decide, by decide, NearSavedCubicSingletons4.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons4.fee_exact]; decide +kernel
  · refine ⟨9, 9, 386045, by decide, by decide, by decide, NearSavedCubicSingletons5.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons5.fee_exact]; decide +kernel
  · refine ⟨10, 10, 386045, by decide, by decide, by decide, NearSavedCubicSingletons6.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons6.fee_exact]; decide +kernel
  · refine ⟨11, 11, 386045, by decide, by decide, by decide, NearSavedCubicSingletons7.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons7.fee_exact]; decide +kernel
  · refine ⟨12, 12, 386045, by decide, by decide, by decide, NearSavedCubicSingletons8.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons8.fee_exact]; decide +kernel
  · refine ⟨13, 13, 386045, by decide, by decide, by decide, NearSavedCubicSingletons9.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons9.fee_exact]; decide +kernel
  · refine ⟨14, 14, 386045, by decide, by decide, by decide, NearSavedCubicSingletons10.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons10.fee_exact]; decide +kernel
  · refine ⟨15, 15, 386045, by decide, by decide, by decide, NearSavedCubicSingletons11.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons11.fee_exact]; decide +kernel
  · refine ⟨16, 16, 386045, by decide, by decide, by decide, NearSavedCubicSingletons12.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons12.fee_exact]; decide +kernel
  · refine ⟨17, 17, 386045, by decide, by decide, by decide, NearSavedCubicSingletons13.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons13.fee_exact]; decide +kernel
  · refine ⟨18, 18, 386045, by decide, by decide, by decide, NearSavedCubicSingletons14.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons14.fee_exact]; decide +kernel
  · refine ⟨19, 19, 386045, by decide, by decide, by decide, NearSavedCubicSingletons15.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons15.fee_exact]; decide +kernel
  · refine ⟨20, 20, 386045, by decide, by decide, by decide, NearSavedCubicSingletons16.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons16.fee_exact]; decide +kernel
  · refine ⟨21, 21, 386045, by decide, by decide, by decide, NearSavedCubicSingletons17.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons17.fee_exact]; decide +kernel
  · refine ⟨22, 22, 386045, by decide, by decide, by decide, NearSavedCubicSingletons18.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons18.fee_exact]; decide +kernel
  · refine ⟨23, 23, 386045, by decide, by decide, by decide, NearSavedCubicSingletons19.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons19.fee_exact]; decide +kernel
  · refine ⟨24, 24, 386045, by decide, by decide, by decide, NearSavedCubicSingletons20.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons20.fee_exact]; decide +kernel
  · refine ⟨25, 25, 386045, by decide, by decide, by decide, NearSavedCubicSingletons21.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons21.fee_exact]; decide +kernel
  · refine ⟨26, 26, 386045, by decide, by decide, by decide, NearSavedCubicSingletons22.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons22.fee_exact]; decide +kernel
  · refine ⟨27, 27, 386045, by decide, by decide, by decide, NearSavedCubicSingletons23.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons23.fee_exact]; decide +kernel
  · refine ⟨28, 28, 386045, by decide, by decide, by decide, NearSavedCubicSingletons24.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons24.fee_exact]; decide +kernel
  · refine ⟨29, 29, 386045, by decide, by decide, by decide, NearSavedCubicSingletons25.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons25.fee_exact]; decide +kernel
  · refine ⟨30, 30, 386045, by decide, by decide, by decide, NearSavedCubicSingletons26.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons26.fee_exact]; decide +kernel
  · refine ⟨31, 31, 386045, by decide, by decide, by decide, NearSavedCubicSingletons27.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons27.fee_exact]; decide +kernel
  · refine ⟨32, 32, 386045, by decide, by decide, by decide, NearSavedCubicSingletons28.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons28.fee_exact]; decide +kernel
  · refine ⟨33, 33, 386045, by decide, by decide, by decide, NearSavedCubicSingletons29.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons29.fee_exact]; decide +kernel
  · refine ⟨34, 34, 386045, by decide, by decide, by decide, NearSavedCubicSingletons30.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons30.fee_exact]; decide +kernel
  · refine ⟨35, 35, 386045, by decide, by decide, by decide, NearSavedCubicSingletons31.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons31.fee_exact]; decide +kernel
  · refine ⟨36, 36, 386045, by decide, by decide, by decide, NearSavedCubicSingletons32.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons32.fee_exact]; decide +kernel
  · refine ⟨37, 37, 386045, by decide, by decide, by decide, NearSavedCubicSingletons33.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons33.fee_exact]; decide +kernel
  · refine ⟨38, 38, 386045, by decide, by decide, by decide, NearSavedCubicSingletons34.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons34.fee_exact]; decide +kernel
  · refine ⟨39, 39, 386045, by decide, by decide, by decide, NearSavedCubicSingletons35.data, ?_⟩
    unfold NearCase.uniform; rw [NearSavedCubicSingletons35.fee_exact]; decide +kernel
  · refine ⟨40, 40, 386045, by decide, by decide, by decide, NearSavedCubicSingletons36.data, ?_⟩
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 1 514727 := by
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

def price : Pricing := ⟨55/100, 90/100, [350218762, 348129386, 348903874, 349256091, 348344927, 149040181, 148902840, 133799260, 131871722, 108981331, 108615557, 150710995, 241021927], [986662, 992389, 990266, 989301, 991798, 2582836, 2585120, 2905890, 2948151, 3613381, 3626079, 2555057, 1522014],
  ![127939259290140, 1599431479748, 216919734300, 3698600580], 196308028084483853⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1206 : Request := ⟨⟨⟨560,781,169,25043⟩,5316921262080,10299257375⟩,0,4,1,514727,1⟩
private theorem pass1206_2293 : (Triangular src1206) 2293 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1206_2304 : (Triangular src1206) 2304 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1206_2339 : (Triangular src1206) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1206 : Cover (Triangular src1206) 2389 2293 [2303,2338,2389] := by
  exact ⟨by decide, by decide, pass1206_2293, by decide, by decide, pass1206_2304, by decide, by decide, pass1206_2339, rfl⟩
def src1207 : Request := ⟨⟨⟨560,781,169,28173⟩,5316921262080,10299257375⟩,1,4,1,514727,1⟩
private theorem pass1207_2293 : (Triangular src1207) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1207_2296 : (Triangular src1207) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1207_2305 : (Triangular src1207) 2305 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1207_2334 : (Triangular src1207) 2334 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1207 : Cover (Triangular src1207) 2389 2293 [2295,2304,2333,2389] := by
  exact ⟨by decide, by decide, pass1207_2293, by decide, by decide, pass1207_2296, by decide, by decide, pass1207_2305, by decide, by decide, pass1207_2334, rfl⟩
def src1208 : Request := ⟨⟨⟨690,962,208,28173⟩,9921631092736,23645774460⟩,2,4,1,514727,1⟩
private theorem pass1208_2293 : (Triangular src1208) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1208_2294 : (Triangular src1208) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1208_2297 : (Triangular src1208) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1208_2306 : (Triangular src1208) 2306 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1208_2334 : (Triangular src1208) 2334 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1208 : Cover (Triangular src1208) 2389 2293 [2293,2296,2305,2333,2389] := by
  exact ⟨by decide, by decide, pass1208_2293, by decide, by decide, pass1208_2294, by decide, by decide, pass1208_2297, by decide, by decide, pass1208_2306, by decide, by decide, pass1208_2334, rfl⟩
def src1209 : Request := ⟨⟨⟨560,781,169,45124⟩,5316921262080,10299257375⟩,3,4,1,514727,1⟩
private theorem pass1209_2293 : (Triangular src1209) 2293 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1209_2304 : (Triangular src1209) 2304 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1209_2339 : (Triangular src1209) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1209 : Cover (Triangular src1209) 2389 2293 [2303,2338,2389] := by
  exact ⟨by decide, by decide, pass1209_2293, by decide, by decide, pass1209_2304, by decide, by decide, pass1209_2339, rfl⟩
def src1210 : Request := ⟨⟨⟨690,962,208,31694⟩,9921631092736,23645774460⟩,3,4,1,514727,1⟩
private theorem pass1210_2293 : (Triangular src1210) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1210_2294 : (Triangular src1210) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1210_2297 : (Triangular src1210) 2297 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1210_2307 : (Triangular src1210) 2307 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1210_2337 : (Triangular src1210) 2337 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1210 : Cover (Triangular src1210) 2389 2293 [2293,2296,2306,2336,2389] := by
  exact ⟨by decide, by decide, pass1210_2293, by decide, by decide, pass1210_2294, by decide, by decide, pass1210_2297, by decide, by decide, pass1210_2307, by decide, by decide, pass1210_2337, rfl⟩
def src1211 : Request := ⟨⟨⟨825,1151,248,40111⟩,16903818182656,48256472894⟩,6,4,1,514727,1⟩
private theorem pass1211_2293 : (Triangular src1211) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1211_2296 : (Triangular src1211) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1211_2305 : (Triangular src1211) 2305 2331 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1211_2332 : (Triangular src1211) 2332 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1211 : Cover (Triangular src1211) 2389 2293 [2295,2304,2331,2389] := by
  exact ⟨by decide, by decide, pass1211_2293, by decide, by decide, pass1211_2296, by decide, by decide, pass1211_2305, by decide, by decide, pass1211_2332, rfl⟩
def src1212 : Request := ⟨⟨⟨1200,1674,368,45124⟩,52718727069696,218807905514⟩,10,4,1,514727,1⟩
private theorem pass1212_2293 : (Triangular src1212) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1212_2297 : (Triangular src1212) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1212_2308 : (Triangular src1212) 2308 2339 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1212_2340 : (Triangular src1212) 2340 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1212 : Cover (Triangular src1212) 2389 2293 [2296,2307,2339,2389] := by
  exact ⟨by decide, by decide, pass1212_2293, by decide, by decide, pass1212_2297, by decide, by decide, pass1212_2308, by decide, by decide, pass1212_2340, rfl⟩
def src1213 : Request := ⟨⟨⟨1450,2023,445,50764⟩,92998964346880,466511127281⟩,13,4,1,514727,1⟩
private theorem pass1213_2293 : (Triangular src1213) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1213_2294 : (Triangular src1213) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1213_2296 : (Triangular src1213) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1213_2302 : (Triangular src1213) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1213_2319 : (Triangular src1213) 2319 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1213_2368 : (Triangular src1213) 2368 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1213 : Cover (Triangular src1213) 2389 2293 [2293,2295,2301,2318,2367,2389] := by
  exact ⟨by decide, by decide, pass1213_2293, by decide, by decide, pass1213_2294, by decide, by decide, pass1213_2296, by decide, by decide, pass1213_2302, by decide, by decide, pass1213_2319, by decide, by decide, pass1213_2368, rfl⟩
def src1214 : Request := ⟨⟨⟨2100,2930,632,81311⟩,278060332482560,2019119590628⟩,25,4,1,514727,1⟩
private theorem pass1214_2293 : (Triangular src1214) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1214_2301 : (Triangular src1214) 2301 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1214_2324 : (Triangular src1214) 2324 2388 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1214_2389 : (Triangular src1214) 2389 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1214 : Cover (Triangular src1214) 2389 2293 [2300,2323,2388,2389] := by
  exact ⟨by decide, by decide, pass1214_2293, by decide, by decide, pass1214_2301, by decide, by decide, pass1214_2324, by decide, by decide, pass1214_2389, rfl⟩
def src1217 : Request := ⟨⟨⟨4800,6697,1474,164837⟩,3367547627110400,55891290082931⟩,65,4,1,514727,1⟩
private theorem pass1217_2293 : (Triangular src1217) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1217_2297 : (Triangular src1217) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1217_2308 : (Triangular src1217) 2308 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1217_2339 : (Triangular src1217) 2339 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1217 : Cover (Triangular src1217) 2389 2293 [2296,2307,2338,2389] := by
  exact ⟨by decide, by decide, pass1217_2293, by decide, by decide, pass1217_2297, by decide, by decide, pass1217_2308, by decide, by decide, pass1217_2339, rfl⟩
def src1218 : Request := ⟨⟨⟨6900,9626,2118,264035⟩,9997036108906496,238415548481346⟩,110,4,1,514727,1⟩
private theorem pass1218_2293 : (Triangular src1218) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1218_2295 : (Triangular src1218) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1218_2301 : (Triangular src1218) 2301 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1218_2317 : (Triangular src1218) 2317 2360 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1218_2361 : (Triangular src1218) 2361 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1218 : Cover (Triangular src1218) 2389 2293 [2294,2300,2316,2360,2389] := by
  exact ⟨by decide, by decide, pass1218_2293, by decide, by decide, pass1218_2295, by decide, by decide, pass1218_2301, by decide, by decide, pass1218_2317, by decide, by decide, pass1218_2361, rfl⟩
def src1219 : Request := ⟨⟨⟨690,963,212,22261⟩,10065769922560,24078187611⟩,0,4,1,514727,2⟩
private theorem pass1219_2293 : (Triangular src1219) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1219_2296 : (Triangular src1219) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1219_2305 : (Triangular src1219) 2305 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1219_2333 : (Triangular src1219) 2333 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1219 : Cover (Triangular src1219) 2389 2293 [2295,2304,2332,2389] := by
  exact ⟨by decide, by decide, pass1219_2293, by decide, by decide, pass1219_2296, by decide, by decide, pass1219_2305, by decide, by decide, pass1219_2333, rfl⟩
def src1220 : Request := ⟨⟨⟨690,963,208,25043⟩,9921631092736,23724874690⟩,1,4,1,514727,2⟩
private theorem pass1220_2293 : (Triangular src1220) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1220_2298 : (Triangular src1220) 2298 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1220_2314 : (Triangular src1220) 2314 2362 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1220_2363 : (Triangular src1220) 2363 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1220 : Cover (Triangular src1220) 2389 2293 [2297,2313,2362,2389] := by
  exact ⟨by decide, by decide, pass1220_2293, by decide, by decide, pass1220_2298, by decide, by decide, pass1220_2314, by decide, by decide, pass1220_2363, rfl⟩
def src1221 : Request := ⟨⟨⟨690,962,208,31694⟩,9921631092736,23645774460⟩,3,4,1,514727,2⟩
private theorem pass1221_2293 : (Triangular src1221) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1221_2301 : (Triangular src1221) 2301 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1221_2326 : (Triangular src1221) 2326 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1221 : Cover (Triangular src1221) 2389 2293 [2300,2325,2389] := by
  exact ⟨by decide, by decide, pass1221_2293, by decide, by decide, pass1221_2301, by decide, by decide, pass1221_2326, rfl⟩
def src1222 : Request := ⟨⟨⟨1000,1395,307,40111⟩,30557599170560,105715278267⟩,8,4,1,514727,2⟩
private theorem pass1222_2293 : (Triangular src1222) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1222_2295 : (Triangular src1222) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1222_2301 : (Triangular src1222) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1222_2318 : (Triangular src1222) 2318 2367 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1222_2368 : (Triangular src1222) 2368 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1222 : Cover (Triangular src1222) 2389 2293 [2294,2300,2317,2367,2389] := by
  exact ⟨by decide, by decide, pass1222_2293, by decide, by decide, pass1222_2295, by decide, by decide, pass1222_2301, by decide, by decide, pass1222_2318, by decide, by decide, pass1222_2368, rfl⟩
def src1223 : Request := ⟨⟨⟨1450,2023,436,50764⟩,91566841790464,459151377566⟩,13,4,1,514727,2⟩
private theorem pass1223_2293 : (Triangular src1223) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1223_2296 : (Triangular src1223) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1223_2304 : (Triangular src1223) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1223_2327 : (Triangular src1223) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1223 : Cover (Triangular src1223) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass1223_2293, by decide, by decide, pass1223_2296, by decide, by decide, pass1223_2304, by decide, by decide, pass1223_2327, rfl⟩
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
  physicalFloor := 514727
  seedFloor := 1

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨4, 1, 10, 95/100, 80/100, ![102788033395, 311285357851, 981624731, 2473580430], 2745452962359351⟩
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

def data : NearCase 4 1 1 514727 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases2.plan, Lower6960.Prefix6969MainCases.HigherHelperCases2.price, Lower6960.Prefix6969MainCases.HigherHelperCases2.valid, Lower6960.Prefix6969MainCases.HigherHelperCases2.priced, Lower6960.Prefix6969MainCases.HigherHelperCases2.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases2.plan, Lower6960.Prefix6969RescueData.HigherHelperCases2.price, Lower6960.Prefix6969RescueData.HigherHelperCases2.sources, Lower6960.Prefix6969RescueData.HigherHelperCases2.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 200493915197445689 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 2 514727 := by
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

def price : Pricing := ⟨55/100, 90/100, [348597622, 348141080, 348124473, 347963134, 348170671, 142394489, 139839785, 137715773, 135693494, 108451132, 107701110, 150272615, 240687471], [991105, 992356, 992402, 992844, 992275, 2717441, 2773453, 2820021, 2864359, 3631787, 3657823, 2562345, 1524764],
  ![127761723356220, 1599792881244, 216618723900, 3730979460], 195234572450179091⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1224 : Request := ⟨⟨⟨1750,2441,537,64247⟩,163381988556800,988269431527⟩,20,4,1,514727,2⟩
private theorem pass1224_2293 : (Triangular src1224) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1224_2294 : (Triangular src1224) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1224_2296 : (Triangular src1224) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1224_2302 : (Triangular src1224) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1224_2319 : (Triangular src1224) 2319 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1224_2367 : (Triangular src1224) 2367 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1224 : Cover (Triangular src1224) 2389 2293 [2293,2295,2301,2318,2366,2389] := by
  exact ⟨by decide, by decide, pass1224_2293, by decide, by decide, pass1224_2294, by decide, by decide, pass1224_2296, by decide, by decide, pass1224_2302, by decide, by decide, pass1224_2319, by decide, by decide, pass1224_2367, rfl⟩
def src1225 : Request := ⟨⟨⟨1750,2441,537,130242⟩,163381988556800,988269431527⟩,32,4,1,514727,2⟩
private theorem pass1225_2293 : (Triangular src1225) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1225_2299 : (Triangular src1225) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1225_2316 : (Triangular src1225) 2316 2363 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1225_2364 : (Triangular src1225) 2364 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1225 : Cover (Triangular src1225) 2389 2293 [2298,2315,2363,2389] := by
  exact ⟨by decide, by decide, pass1225_2293, by decide, by decide, pass1225_2299, by decide, by decide, pass1225_2316, by decide, by decide, pass1225_2364, rfl⟩
def src1227 : Request := ⟨⟨⟨3950,5511,1189,130242⟩,1848744952463360,25241028863276⟩,50,4,1,514727,2⟩
private theorem pass1227_2293 : (Triangular src1227) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1227_2296 : (Triangular src1227) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1227_2304 : (Triangular src1227) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1227_2327 : (Triangular src1227) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1227 : Cover (Triangular src1227) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass1227_2293, by decide, by decide, pass1227_2296, by decide, by decide, pass1227_2304, by decide, by decide, pass1227_2327, rfl⟩
def src1229 : Request := ⟨⟨⟨5700,7952,1716,208621⟩,5553838907981824,109384694947514⟩,85,4,1,514727,2⟩
private theorem pass1229_2293 : (Triangular src1229) 2293 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1229_2298 : (Triangular src1229) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1229_2312 : (Triangular src1229) 2312 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1229_2351 : (Triangular src1229) 2351 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1229 : Cover (Triangular src1229) 2389 2293 [2297,2311,2350,2389] := by
  exact ⟨by decide, by decide, pass1229_2293, by decide, by decide, pass1229_2298, by decide, by decide, pass1229_2312, by decide, by decide, pass1229_2351, rfl⟩
def src1230 : Request := ⟨⟨⟨10000,13952,3010,334168⟩,29974681586237440,1035886358306578⟩,145,4,1,514727,2⟩
private theorem pass1230_2293 : (Triangular src1230) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1230_2296 : (Triangular src1230) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1230_2304 : (Triangular src1230) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1230_2326 : (Triangular src1230) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1230_2387 : (Triangular src1230) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1230 : Cover (Triangular src1230) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass1230_2293, by decide, by decide, pass1230_2296, by decide, by decide, pass1230_2304, by decide, by decide, pass1230_2326, by decide, by decide, pass1230_2387, rfl⟩
def src1231 : Request := ⟨⟨⟨560,781,169,22261⟩,5316921262080,10299257375⟩,0,4,1,514727,4⟩
private theorem pass1231_2293 : (Triangular src1231) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1231_2300 : (Triangular src1231) 2300 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1231_2323 : (Triangular src1231) 2323 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1231 : Cover (Triangular src1231) 2389 2293 [2299,2322,2389] := by
  exact ⟨by decide, by decide, pass1231_2293, by decide, by decide, pass1231_2300, by decide, by decide, pass1231_2323, rfl⟩
def src1232 : Request := ⟨⟨⟨560,781,172,25043⟩,5388141854720,10440670587⟩,1,4,1,514727,4⟩
private theorem pass1232_2293 : (Triangular src1232) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1232_2296 : (Triangular src1232) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1232_2305 : (Triangular src1232) 2305 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1232_2333 : (Triangular src1232) 2333 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1232 : Cover (Triangular src1232) 2389 2293 [2295,2304,2332,2389] := by
  exact ⟨by decide, by decide, pass1232_2293, by decide, by decide, pass1232_2296, by decide, by decide, pass1232_2305, by decide, by decide, pass1232_2333, rfl⟩
def src1233 : Request := ⟨⟨⟨690,962,212,28173⟩,10065769922560,23997864317⟩,3,4,1,514727,4⟩
private theorem pass1233_2293 : (Triangular src1233) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1233_2295 : (Triangular src1233) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1233_2301 : (Triangular src1233) 2301 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1233_2320 : (Triangular src1233) 2320 2377 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1233_2378 : (Triangular src1233) 2378 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1233 : Cover (Triangular src1233) 2389 2293 [2294,2300,2319,2377,2389] := by
  exact ⟨by decide, by decide, pass1233_2293, by decide, by decide, pass1233_2295, by decide, by decide, pass1233_2301, by decide, by decide, pass1233_2320, by decide, by decide, pass1233_2378, rfl⟩
def src1234 : Request := ⟨⟨⟨1000,1395,307,45124⟩,30557599170560,105715278267⟩,10,4,1,514727,4⟩
private theorem pass1234_2293 : (Triangular src1234) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1234_2299 : (Triangular src1234) 2299 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1234_2316 : (Triangular src1234) 2316 2365 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1234_2366 : (Triangular src1234) 2366 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1234 : Cover (Triangular src1234) 2389 2293 [2298,2315,2365,2389] := by
  exact ⟨by decide, by decide, pass1234_2293, by decide, by decide, pass1234_2299, by decide, by decide, pass1234_2316, by decide, by decide, pass1234_2366, rfl⟩
def src1235 : Request := ⟨⟨⟨1750,2441,527,64247⟩,161065121873920,973912060302⟩,20,4,1,514727,4⟩
private theorem pass1235_2293 : (Triangular src1235) 2293 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1235_2304 : (Triangular src1235) 2304 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1235_2335 : (Triangular src1235) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1235 : Cover (Triangular src1235) 2389 2293 [2303,2334,2389] := by
  exact ⟨by decide, by decide, pass1235_2293, by decide, by decide, pass1235_2304, by decide, by decide, pass1235_2335, rfl⟩
def src1236 : Request := ⟨⟨⟨2100,2929,645,91474⟩,282396798484480,2049139102608⟩,32,4,1,514727,4⟩
private theorem pass1236_2293 : (Triangular src1236) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1236_2297 : (Triangular src1236) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1236_2309 : (Triangular src1236) 2309 2342 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1236_2343 : (Triangular src1236) 2343 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1236 : Cover (Triangular src1236) 2389 2293 [2296,2308,2342,2389] := by
  exact ⟨by decide, by decide, pass1236_2293, by decide, by decide, pass1236_2297, by decide, by decide, pass1236_2309, by decide, by decide, pass1236_2343, rfl⟩
def src1238 : Request := ⟨⟨⟨2100,2929,645,375939⟩,282396798484480,2049139102608⟩,50,4,1,514727,4⟩
private theorem pass1238_2293 : (Triangular src1238) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1238_2295 : (Triangular src1238) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1238_2300 : (Triangular src1238) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1238_2314 : (Triangular src1238) 2314 2353 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1238_2354 : (Triangular src1238) 2354 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1238 : Cover (Triangular src1238) 2389 2293 [2294,2299,2313,2353,2389] := by
  exact ⟨by decide, by decide, pass1238_2293, by decide, by decide, pass1238_2295, by decide, by decide, pass1238_2300, by decide, by decide, pass1238_2314, by decide, by decide, pass1238_2354, rfl⟩
def src1240 : Request := ⟨⟨⟨4800,6697,1474,146522⟩,3367547627110400,55891290082931⟩,65,4,1,514727,4⟩
private theorem pass1240_2293 : (Triangular src1240) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1240_2294 : (Triangular src1240) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1240_2296 : (Triangular src1240) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1240_2302 : (Triangular src1240) 2302 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1240_2319 : (Triangular src1240) 2319 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1240_2365 : (Triangular src1240) 2365 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1240 : Cover (Triangular src1240) 2389 2293 [2293,2295,2301,2318,2364,2389] := by
  exact ⟨by decide, by decide, pass1240_2293, by decide, by decide, pass1240_2294, by decide, by decide, pass1240_2296, by decide, by decide, pass1240_2302, by decide, by decide, pass1240_2319, by decide, by decide, pass1240_2365, rfl⟩
def src1241 : Request := ⟨⟨⟨3200,4463,982,964572⟩,997767489781760,11028049925768⟩,85,4,1,514727,4⟩
private theorem pass1241_2293 : (Triangular src1241) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1241_2296 : (Triangular src1241) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1241_2304 : (Triangular src1241) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1241_2326 : (Triangular src1241) 2326 2387 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1241_2388 : (Triangular src1241) 2388 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1241 : Cover (Triangular src1241) 2389 2293 [2295,2303,2325,2387,2389] := by
  exact ⟨by decide, by decide, pass1241_2293, by decide, by decide, pass1241_2296, by decide, by decide, pass1241_2304, by decide, by decide, pass1241_2326, by decide, by decide, pass1241_2388, rfl⟩
def src1242 : Request := ⟨⟨⟨10000,13950,3070,422931⟩,30428373265940480,1051468979452278⟩,190,4,1,514727,4⟩
private theorem pass1242_2293 : (Triangular src1242) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1242_2295 : (Triangular src1242) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1242_2301 : (Triangular src1242) 2301 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1242_2317 : (Triangular src1242) 2317 2360 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1242_2361 : (Triangular src1242) 2361 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1242 : Cover (Triangular src1242) 2389 2293 [2294,2300,2316,2360,2389] := by
  exact ⟨by decide, by decide, pass1242_2293, by decide, by decide, pass1242_2295, by decide, by decide, pass1242_2301, by decide, by decide, pass1242_2317, by decide, by decide, pass1242_2361, rfl⟩
def src1243 : Request := ⟨⟨⟨560,781,172,17590⟩,5388141854720,10440670587⟩,0,4,1,514727,9⟩
private theorem pass1243_2293 : (Triangular src1243) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1243_2295 : (Triangular src1243) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1243_2301 : (Triangular src1243) 2301 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1243_2320 : (Triangular src1243) 2320 2379 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1243_2380 : (Triangular src1243) 2380 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1243 : Cover (Triangular src1243) 2389 2293 [2294,2300,2319,2379,2389] := by
  exact ⟨by decide, by decide, pass1243_2293, by decide, by decide, pass1243_2295, by decide, by decide, pass1243_2301, by decide, by decide, pass1243_2320, by decide, by decide, pass1243_2380, rfl⟩
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
  physicalFloor := 514727
  seedFloor := 2

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨4, 3, 9, 95/100, 80/100, ![390269126344, 403048770466, 3515327830, 3515333850], 2788146972120211⟩
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

def data : NearCase 4 2 3 514727 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases3.plan, Lower6960.Prefix6969MainCases.HigherHelperCases3.price, Lower6960.Prefix6969MainCases.HigherHelperCases3.valid, Lower6960.Prefix6969MainCases.HigherHelperCases3.priced, Lower6960.Prefix6969MainCases.HigherHelperCases3.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases3.plan, Lower6960.Prefix6969RescueData.HigherHelperCases3.price, Lower6960.Prefix6969RescueData.HigherHelperCases3.sources, Lower6960.Prefix6969RescueData.HigherHelperCases3.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 203604923239934792 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 4 514727 := by
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

def price : Pricing := ⟨55/100, 90/100, [346122671, 345270877, 345430546, 345152583, 345873125, 149155329, 147762750, 95114114, 116412957, 107506374, 106989428, 149401200, 240022637], [997888, 1000223, 999785, 1000547, 998572, 2580922, 2604075, 4160862, 3363778, 3664583, 3682528, 2576834, 1530230],
  ![127408816172340, 1600511028508, 216020373300, 3756178560], 193530913974546135⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 514727
  seedFloor := 4

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨4, 8, 9, 95/100, 80/100, ![3004010949912, 1137350208646, 9561042220, 3585406950], 5129774221983556⟩
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

def data : NearCase 4 4 8 514727 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases4.plan, Lower6960.Prefix6969MainCases.HigherHelperCases4.price, Lower6960.Prefix6969MainCases.HigherHelperCases4.valid, Lower6960.Prefix6969MainCases.HigherHelperCases4.priced, Lower6960.Prefix6969MainCases.HigherHelperCases4.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases4.plan, Lower6960.Prefix6969RescueData.HigherHelperCases4.price, Lower6960.Prefix6969RescueData.HigherHelperCases4.sources, Lower6960.Prefix6969RescueData.HigherHelperCases4.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 213609431382787543 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 9 514727 := by
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

def price : Pricing := ⟨55/100, 90/100, [338400942, 337465849, 338217296, 337844960, 337161346, 133117717, 130741945, 83927935, 115491119, 105092174, 104683599, 147255537, 238385481], [1019050, 1021613, 1019554, 1020574, 1022448, 2920833, 2972921, 4748739, 3389547, 3748390, 3762574, 2612508, 1543690],
  ![126539781024420, 1602279445404, 214546932900, 3837825480], 188416617764182168⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1244 : Request := ⟨⟨⟨690,963,208,19788⟩,9921631092736,23724874690⟩,1,4,1,514727,9⟩
private theorem pass1244_2293 : (Triangular src1244) 2293 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1244_2305 : (Triangular src1244) 2305 2341 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1244_2342 : (Triangular src1244) 2342 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1244 : Cover (Triangular src1244) 2389 2293 [2304,2341,2389] := by
  exact ⟨by decide, by decide, pass1244_2293, by decide, by decide, pass1244_2305, by decide, by decide, pass1244_2342, rfl⟩
def src1245 : Request := ⟨⟨⟨690,962,208,22261⟩,9921631092736,23645774460⟩,2,4,1,514727,9⟩
private theorem pass1245_2293 : (Triangular src1245) 2293 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1245_2308 : (Triangular src1245) 2308 2354 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1245_2355 : (Triangular src1245) 2355 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1245 : Cover (Triangular src1245) 2389 2293 [2307,2354,2389] := by
  exact ⟨by decide, by decide, pass1245_2293, by decide, by decide, pass1245_2308, by decide, by decide, pass1245_2355, rfl⟩
def src1246 : Request := ⟨⟨⟨690,962,208,28173⟩,9921631092736,23645774460⟩,4,4,1,514727,9⟩
private theorem pass1246_2293 : (Triangular src1246) 2293 2302 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1246_2303 : (Triangular src1246) 2303 2333 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1246_2334 : (Triangular src1246) 2334 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1246 : Cover (Triangular src1246) 2389 2293 [2302,2333,2389] := by
  exact ⟨by decide, by decide, pass1246_2293, by decide, by decide, pass1246_2303, by decide, by decide, pass1246_2334, rfl⟩
def src1247 : Request := ⟨⟨⟨825,1151,248,25043⟩,16903818182656,48256472894⟩,4,4,1,514727,9⟩
private theorem pass1247_2293 : (Triangular src1247) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1247_2301 : (Triangular src1247) 2301 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1247_2325 : (Triangular src1247) 2325 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1247 : Cover (Triangular src1247) 2389 2293 [2300,2324,2389] := by
  exact ⟨by decide, by decide, pass1247_2293, by decide, by decide, pass1247_2301, by decide, by decide, pass1247_2325, rfl⟩
def src1248 : Request := ⟨⟨⟨1000,1395,301,31694⟩,30103476895744,104105680031⟩,8,4,1,514727,9⟩
private theorem pass1248_2293 : (Triangular src1248) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1248_2295 : (Triangular src1248) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1248_2301 : (Triangular src1248) 2301 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1248_2319 : (Triangular src1248) 2319 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1248_2372 : (Triangular src1248) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1248 : Cover (Triangular src1248) 2389 2293 [2294,2300,2318,2371,2389] := by
  exact ⟨by decide, by decide, pass1248_2293, by decide, by decide, pass1248_2295, by decide, by decide, pass1248_2301, by decide, by decide, pass1248_2319, by decide, by decide, pass1248_2372, rfl⟩
def src1249 : Request := ⟨⟨⟨1200,1674,368,50764⟩,52718727069696,218807905514⟩,16,4,1,514727,9⟩
private theorem pass1249_2293 : (Triangular src1249) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1249_2295 : (Triangular src1249) 2295 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1249_2301 : (Triangular src1249) 2301 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1249_2318 : (Triangular src1249) 2318 2366 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1249_2367 : (Triangular src1249) 2367 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1249 : Cover (Triangular src1249) 2389 2293 [2294,2300,2317,2366,2389] := by
  exact ⟨by decide, by decide, pass1249_2293, by decide, by decide, pass1249_2295, by decide, by decide, pass1249_2301, by decide, by decide, pass1249_2318, by decide, by decide, pass1249_2367, rfl⟩
def src1250 : Request := ⟨⟨⟨2100,2930,645,57109⟩,282396798484480,2051392203643⟩,25,4,1,514727,9⟩
private theorem pass1250_2293 : (Triangular src1250) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1250_2294 : (Triangular src1250) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1250_2297 : (Triangular src1250) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1250_2305 : (Triangular src1250) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1250_2328 : (Triangular src1250) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1250 : Cover (Triangular src1250) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass1250_2293, by decide, by decide, pass1250_2294, by decide, by decide, pass1250_2297, by decide, by decide, pass1250_2305, by decide, by decide, pass1250_2328, rfl⟩
def src1253 : Request := ⟨⟨⟨3200,4463,982,762132⟩,997767489781760,11028049925768⟩,85,4,1,514727,9⟩
private theorem pass1253_2293 : (Triangular src1253) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1253_2295 : (Triangular src1253) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1253_2300 : (Triangular src1253) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1253_2314 : (Triangular src1253) 2314 2352 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1253_2353 : (Triangular src1253) 2353 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1253 : Cover (Triangular src1253) 2389 2293 [2294,2299,2313,2352,2389] := by
  exact ⟨by decide, by decide, pass1253_2293, by decide, by decide, pass1253_2295, by decide, by decide, pass1253_2300, by decide, by decide, pass1253_2314, by decide, by decide, pass1253_2353, rfl⟩
def src1254 : Request := ⟨⟨⟨4800,6696,1474,164837⟩,3367547627110400,55864419956306⟩,85,4,1,514727,9⟩
private theorem pass1254_2293 : (Triangular src1254) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1254_2296 : (Triangular src1254) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1254_2304 : (Triangular src1254) 2304 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1254_2326 : (Triangular src1254) 2326 2386 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1254_2387 : (Triangular src1254) 2387 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1254 : Cover (Triangular src1254) 2389 2293 [2295,2303,2325,2386,2389] := by
  exact ⟨by decide, by decide, pass1254_2293, by decide, by decide, pass1254_2296, by decide, by decide, pass1254_2304, by decide, by decide, pass1254_2326, by decide, by decide, pass1254_2387, rfl⟩
def src1255 : Request := ⟨⟨⟨8300,11579,2548,264035⟩,17399709518790656,499124969898998⟩,145,4,1,514727,9⟩
private theorem pass1255_2293 : (Triangular src1255) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1255_2300 : (Triangular src1255) 2300 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1255_2319 : (Triangular src1255) 2319 2370 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1255_2371 : (Triangular src1255) 2371 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1255 : Cover (Triangular src1255) 2389 2293 [2299,2318,2370,2389] := by
  exact ⟨by decide, by decide, pass1255_2293, by decide, by decide, pass1255_2300, by decide, by decide, pass1255_2319, by decide, by decide, pass1255_2371, rfl⟩
def src1258 : Request := ⟨⟨⟨690,963,212,12355⟩,10065769922560,24078187611⟩,0,4,1,514727,16⟩
private theorem pass1258_2293 : (Triangular src1258) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1258_2299 : (Triangular src1258) 2299 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1258_2317 : (Triangular src1258) 2317 2371 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1258_2372 : (Triangular src1258) 2372 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1258 : Cover (Triangular src1258) 2389 2293 [2298,2316,2371,2389] := by
  exact ⟨by decide, by decide, pass1258_2293, by decide, by decide, pass1258_2299, by decide, by decide, pass1258_2317, by decide, by decide, pass1258_2372, rfl⟩
def src1259 : Request := ⟨⟨⟨690,963,208,13899⟩,9921631092736,23724874690⟩,1,4,1,514727,16⟩
private theorem pass1259_2293 : (Triangular src1259) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1259_2297 : (Triangular src1259) 2297 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1259_2309 : (Triangular src1259) 2309 2345 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1259_2346 : (Triangular src1259) 2346 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1259 : Cover (Triangular src1259) 2389 2293 [2296,2308,2345,2389] := by
  exact ⟨by decide, by decide, pass1259_2293, by decide, by decide, pass1259_2297, by decide, by decide, pass1259_2309, by decide, by decide, pass1259_2346, rfl⟩
def src1260 : Request := ⟨⟨⟨825,1151,248,17590⟩,16903818182656,48256472894⟩,4,4,1,514727,16⟩
private theorem pass1260_2293 : (Triangular src1260) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1260_2294 : (Triangular src1260) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1260_2297 : (Triangular src1260) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1260_2306 : (Triangular src1260) 2306 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1260_2333 : (Triangular src1260) 2333 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1260 : Cover (Triangular src1260) 2389 2293 [2293,2296,2305,2332,2389] := by
  exact ⟨by decide, by decide, pass1260_2293, by decide, by decide, pass1260_2294, by decide, by decide, pass1260_2297, by decide, by decide, pass1260_2306, by decide, by decide, pass1260_2333, rfl⟩
def src1261 : Request := ⟨⟨⟨1000,1395,307,22261⟩,30557599170560,105715278267⟩,8,4,1,514727,16⟩
private theorem pass1261_2293 : (Triangular src1261) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1261_2299 : (Triangular src1261) 2299 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1261_2317 : (Triangular src1261) 2317 2369 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1261_2370 : (Triangular src1261) 2370 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1261 : Cover (Triangular src1261) 2389 2293 [2298,2316,2369,2389] := by
  exact ⟨by decide, by decide, pass1261_2293, by decide, by decide, pass1261_2299, by decide, by decide, pass1261_2317, by decide, by decide, pass1261_2370, rfl⟩
def src1262 : Request := ⟨⟨⟨1450,2023,445,40111⟩,92998964346880,466511127281⟩,20,4,1,514727,16⟩
private theorem pass1262_2293 : (Triangular src1262) 2293 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1262_2300 : (Triangular src1262) 2300 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1262_2320 : (Triangular src1262) 2320 2377 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1262_2378 : (Triangular src1262) 2378 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1262 : Cover (Triangular src1262) 2389 2293 [2299,2319,2377,2389] := by
  exact ⟨by decide, by decide, pass1262_2293, by decide, by decide, pass1262_2300, by decide, by decide, pass1262_2320, by decide, by decide, pass1262_2378, rfl⟩
def src1263 : Request := ⟨⟨⟨2100,2929,645,208621⟩,282396798484480,2049139102608⟩,50,4,1,514727,16⟩
private theorem pass1263_2293 : (Triangular src1263) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1263_2294 : (Triangular src1263) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1263_2297 : (Triangular src1263) 2297 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1263_2305 : (Triangular src1263) 2305 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1263_2328 : (Triangular src1263) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1263 : Cover (Triangular src1263) 2389 2293 [2293,2296,2304,2327,2389] := by
  exact ⟨by decide, by decide, pass1263_2293, by decide, by decide, pass1263_2294, by decide, by decide, pass1263_2297, by decide, by decide, pass1263_2305, by decide, by decide, pass1263_2328, rfl⟩
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
  physicalFloor := 514727
  seedFloor := 9

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨4, 15, 10, 90/100, 80/100, ![4450390552272, 910409468296, 14878781008, 2975770980], 4376182056771256⟩
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

def data : NearCase 4 9 15 514727 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases5.plan, Lower6960.Prefix6969MainCases.HigherHelperCases5.price, Lower6960.Prefix6969MainCases.HigherHelperCases5.valid, Lower6960.Prefix6969MainCases.HigherHelperCases5.priced, Lower6960.Prefix6969MainCases.HigherHelperCases5.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases5.plan, Lower6960.Prefix6969RescueData.HigherHelperCases5.price, Lower6960.Prefix6969RescueData.HigherHelperCases5.sources, Lower6960.Prefix6969RescueData.HigherHelperCases5.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 221691729569023888 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedHigherHelperCases5
end Z6969Source1599

-- Source: Research6969.PhysicalChecks105
section Z6969Source1600
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1548 : Request := ⟨⟨⟨556,772,170,6357⟩,5255817068544,9968090926⟩,10,5,2,643408,17⟩
private theorem pass1548_2293 : (Triangular src1548) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1548_2294 : (Triangular src1548) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1548_2297 : (Triangular src1548) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1548_2306 : (Triangular src1548) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1548_2335 : (Triangular src1548) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1548 : Cover (Triangular src1548) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1548_2293, by decide, by decide, pass1548_2294, by decide, by decide, pass1548_2297, by decide, by decide, pass1548_2306, by decide, by decide, pass1548_2335, rfl⟩
def src1549 : Request := ⟨⟨⟨556,772,170,5664⟩,5255817068544,9968090926⟩,10,5,2,643408,27⟩
private theorem pass1549_2293 : (Triangular src1549) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1549_2294 : (Triangular src1549) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1549_2297 : (Triangular src1549) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1549_2306 : (Triangular src1549) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1549_2335 : (Triangular src1549) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1549 : Cover (Triangular src1549) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1549_2293, by decide, by decide, pass1549_2294, by decide, by decide, pass1549_2297, by decide, by decide, pass1549_2306, by decide, by decide, pass1549_2335, rfl⟩
def src1550 : Request := ⟨⟨⟨556,772,170,5412⟩,5255817068544,9968090926⟩,10,5,2,643408,31⟩
private theorem pass1550_2293 : (Triangular src1550) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1550_2294 : (Triangular src1550) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1550_2297 : (Triangular src1550) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1550_2306 : (Triangular src1550) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1550_2335 : (Triangular src1550) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1550 : Cover (Triangular src1550) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1550_2293, by decide, by decide, pass1550_2294, by decide, by decide, pass1550_2297, by decide, by decide, pass1550_2306, by decide, by decide, pass1550_2335, rfl⟩
def src1551 : Request := ⟨⟨⟨556,772,170,5177⟩,5255817068544,9968090926⟩,10,5,2,643408,35⟩
private theorem pass1551_2293 : (Triangular src1551) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1551_2294 : (Triangular src1551) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1551_2297 : (Triangular src1551) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1551_2306 : (Triangular src1551) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1551_2335 : (Triangular src1551) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1551 : Cover (Triangular src1551) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1551_2293, by decide, by decide, pass1551_2294, by decide, by decide, pass1551_2297, by decide, by decide, pass1551_2306, by decide, by decide, pass1551_2335, rfl⟩
def src1552 : Request := ⟨⟨⟨556,772,170,4961⟩,5255817068544,9968090926⟩,10,5,2,643408,39⟩
private theorem pass1552_2293 : (Triangular src1552) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1552_2294 : (Triangular src1552) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1552_2297 : (Triangular src1552) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1552_2306 : (Triangular src1552) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1552_2335 : (Triangular src1552) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1552 : Cover (Triangular src1552) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1552_2293, by decide, by decide, pass1552_2294, by decide, by decide, pass1552_2297, by decide, by decide, pass1552_2306, by decide, by decide, pass1552_2335, rfl⟩
def src1553 : Request := ⟨⟨⟨556,772,170,4811⟩,5255817068544,9968090926⟩,10,5,2,643408,42⟩
private theorem pass1553_2293 : (Triangular src1553) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1553_2294 : (Triangular src1553) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1553_2297 : (Triangular src1553) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1553_2306 : (Triangular src1553) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1553_2335 : (Triangular src1553) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1553 : Cover (Triangular src1553) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1553_2293, by decide, by decide, pass1553_2294, by decide, by decide, pass1553_2297, by decide, by decide, pass1553_2306, by decide, by decide, pass1553_2335, rfl⟩
def src1554 : Request := ⟨⟨⟨556,772,170,4628⟩,5255817068544,9968090926⟩,10,5,2,643408,46⟩
private theorem pass1554_2293 : (Triangular src1554) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1554_2294 : (Triangular src1554) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1554_2297 : (Triangular src1554) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1554_2306 : (Triangular src1554) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1554_2335 : (Triangular src1554) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1554 : Cover (Triangular src1554) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1554_2293, by decide, by decide, pass1554_2294, by decide, by decide, pass1554_2297, by decide, by decide, pass1554_2306, by decide, by decide, pass1554_2335, rfl⟩
def src1555 : Request := ⟨⟨⟨556,772,170,4466⟩,5255817068544,9968090926⟩,10,5,2,643408,50⟩
private theorem pass1555_2293 : (Triangular src1555) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1555_2294 : (Triangular src1555) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1555_2297 : (Triangular src1555) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1555_2306 : (Triangular src1555) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1555_2335 : (Triangular src1555) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1555 : Cover (Triangular src1555) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1555_2293, by decide, by decide, pass1555_2294, by decide, by decide, pass1555_2297, by decide, by decide, pass1555_2306, by decide, by decide, pass1555_2335, rfl⟩
def src1556 : Request := ⟨⟨⟨556,772,170,4324⟩,5255817068544,9968090926⟩,10,5,2,643408,54⟩
private theorem pass1556_2293 : (Triangular src1556) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1556_2294 : (Triangular src1556) 2294 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1556_2297 : (Triangular src1556) 2297 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1556_2306 : (Triangular src1556) 2306 2334 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1556_2335 : (Triangular src1556) 2335 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1556 : Cover (Triangular src1556) 2389 2293 [2293,2296,2305,2334,2389] := by
  exact ⟨by decide, by decide, pass1556_2293, by decide, by decide, pass1556_2294, by decide, by decide, pass1556_2297, by decide, by decide, pass1556_2306, by decide, by decide, pass1556_2335, rfl⟩
def src1557 : Request := ⟨⟨⟨325,453,100,7715⟩,1061047500800,1193036697⟩,0,6,1,772091,1⟩
private theorem pass1557_2293 : (Triangular src1557) 2293 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1557_2305 : (Triangular src1557) 2305 2347 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1557_2348 : (Triangular src1557) 2348 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1557 : Cover (Triangular src1557) 2389 2293 [2304,2347,2389] := by
  exact ⟨by decide, by decide, pass1557_2293, by decide, by decide, pass1557_2305, by decide, by decide, pass1557_2348, rfl⟩
def src1558 : Request := ⟨⟨⟨325,453,100,8679⟩,1061047500800,1193036697⟩,1,6,1,772091,1⟩
private theorem pass1558_2293 : (Triangular src1558) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1558_2294 : (Triangular src1558) 2294 2297 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1558_2298 : (Triangular src1558) 2298 2311 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1558_2312 : (Triangular src1558) 2312 2361 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1558_2362 : (Triangular src1558) 2362 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1558 : Cover (Triangular src1558) 2389 2293 [2293,2297,2311,2361,2389] := by
  exact ⟨by decide, by decide, pass1558_2293, by decide, by decide, pass1558_2294, by decide, by decide, pass1558_2298, by decide, by decide, pass1558_2312, by decide, by decide, pass1558_2362, rfl⟩
def src1559 : Request := ⟨⟨⟨400,558,120,9763⟩,1935519252480,2682384904⟩,2,6,1,772091,1⟩
private theorem pass1559_2293 : (Triangular src1559) 2293 2312 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1559_2313 : (Triangular src1559) 2313 2380 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1559_2381 : (Triangular src1559) 2381 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1559 : Cover (Triangular src1559) 2389 2293 [2312,2380,2389] := by
  exact ⟨by decide, by decide, pass1559_2293, by decide, by decide, pass1559_2313, by decide, by decide, pass1559_2381, rfl⟩
def src1560 : Request := ⟨⟨⟨470,655,141,10983⟩,3134317133824,5085275599⟩,4,6,1,772091,1⟩
private theorem pass1560_2293 : (Triangular src1560) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1560_2301 : (Triangular src1560) 2301 2327 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1560_2328 : (Triangular src1560) 2328 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1560 : Cover (Triangular src1560) 2389 2293 [2300,2327,2389] := by
  exact ⟨by decide, by decide, pass1560_2293, by decide, by decide, pass1560_2301, by decide, by decide, pass1560_2328, rfl⟩
def src1561 : Request := ⟨⟨⟨560,781,172,13899⟩,5388141854720,10440670587⟩,8,6,1,772091,1⟩
private theorem pass1561_2293 : (Triangular src1561) 2293 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1561_2307 : (Triangular src1561) 2307 2350 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1561_2351 : (Triangular src1561) 2351 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1561 : Cover (Triangular src1561) 2389 2293 [2306,2350,2389] := by
  exact ⟨by decide, by decide, pass1561_2293, by decide, by decide, pass1561_2307, by decide, by decide, pass1561_2351, rfl⟩
def src1562 : Request := ⟨⟨⟨690,962,212,17590⟩,10065769922560,23997864317⟩,13,6,1,772091,1⟩
private theorem pass1562_2293 : (Triangular src1562) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1562_2299 : (Triangular src1562) 2299 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1562_2318 : (Triangular src1562) 2318 2375 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1562_2376 : (Triangular src1562) 2376 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1562 : Cover (Triangular src1562) 2389 2293 [2298,2317,2375,2389] := by
  exact ⟨by decide, by decide, pass1562_2293, by decide, by decide, pass1562_2299, by decide, by decide, pass1562_2318, by decide, by decide, pass1562_2376, rfl⟩
def src1563 : Request := ⟨⟨⟨1000,1395,307,22261⟩,30557599170560,105715278267⟩,20,6,1,772091,1⟩
private theorem pass1563_2293 : (Triangular src1563) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1563_2306 : (Triangular src1563) 2306 2343 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1563_2344 : (Triangular src1563) 2344 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1563 : Cover (Triangular src1563) 2389 2293 [2305,2343,2389] := by
  exact ⟨by decide, by decide, pass1563_2293, by decide, by decide, pass1563_2306, by decide, by decide, pass1563_2344, rfl⟩
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 16 514727 := by
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

def price : Pricing := ⟨55/100, 90/100, [329538123, 328312998, 329167890, 329505374, 328628561, 167229663, 167341177, 155408013, 100552859, 100222282, 148662189, 236912394], [1043340, 1046697, 1044354, 1043429, 1045832, 2280412, 2278558, 2476963, 3931319, 3945271, 2589121, 1555802],
  ![125757836983080, 1603871119536, 213221154600, 4024176420], 182736403592182919⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1264 : Request := ⟨⟨⟨3200,4464,982,72277⟩,997767489781760,11036007960531⟩,50,4,1,514727,16⟩
private theorem pass1264_2293 : (Triangular src1264) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1264_2296 : (Triangular src1264) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1264_2305 : (Triangular src1264) 2305 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1264_2330 : (Triangular src1264) 2330 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1264 : Cover (Triangular src1264) 2389 2293 [2295,2304,2329,2389] := by
  exact ⟨by decide, by decide, pass1264_2293, by decide, by decide, pass1264_2296, by decide, by decide, pass1264_2305, by decide, by decide, pass1264_2330, rfl⟩
def src1265 : Request := ⟨⟨⟨8300,11579,2548,185441⟩,17399709518790656,499124969898998⟩,145,4,1,514727,16⟩
private theorem pass1265_2293 : (Triangular src1265) 2293 2296 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1265_2297 : (Triangular src1265) 2297 2307 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1265_2308 : (Triangular src1265) 2308 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1265_2338 : (Triangular src1265) 2338 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1265 : Cover (Triangular src1265) 2389 2293 [2296,2307,2337,2389] := by
  exact ⟨by decide, by decide, pass1265_2293, by decide, by decide, pass1265_2297, by decide, by decide, pass1265_2308, by decide, by decide, pass1265_2338, rfl⟩
def src1266 : Request := ⟨⟨⟨6900,9623,2118,762132⟩,9997036108906496,238176347849000⟩,190,4,1,514727,16⟩
private theorem pass1266_2293 : (Triangular src1266) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1266_2295 : (Triangular src1266) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1266_2300 : (Triangular src1266) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1266_2314 : (Triangular src1266) 2314 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1266_2352 : (Triangular src1266) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1266 : Cover (Triangular src1266) 2389 2293 [2294,2299,2313,2351,2389] := by
  exact ⟨by decide, by decide, pass1266_2293, by decide, by decide, pass1266_2295, by decide, by decide, pass1266_2300, by decide, by decide, pass1266_2314, by decide, by decide, pass1266_2352, rfl⟩
def src1267 : Request := ⟨⟨⟨8300,11575,2548,2784236⟩,17399709518790656,498569901356632⟩,245,4,1,514727,16⟩
private theorem pass1267_2293 : (Triangular src1267) 2293 2293 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1267_2294 : (Triangular src1267) 2294 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1267_2296 : (Triangular src1267) 2296 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1267_2302 : (Triangular src1267) 2302 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1267_2318 : (Triangular src1267) 2318 2361 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1267_2362 : (Triangular src1267) 2362 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1267 : Cover (Triangular src1267) 2389 2293 [2293,2295,2301,2317,2361,2389] := by
  exact ⟨by decide, by decide, pass1267_2293, by decide, by decide, pass1267_2294, by decide, by decide, pass1267_2296, by decide, by decide, pass1267_2302, by decide, by decide, pass1267_2318, by decide, by decide, pass1267_2362, rfl⟩
def src1274 : Request := ⟨⟨⟨470,655,144,7715⟩,3184589537280,5168862572⟩,0,4,1,514727,26⟩
private theorem pass1274_2293 : (Triangular src1274) 2293 2308 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1274_2309 : (Triangular src1274) 2309 2360 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1274_2361 : (Triangular src1274) 2361 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1274 : Cover (Triangular src1274) 2389 2293 [2308,2360,2389] := by
  exact ⟨by decide, by decide, pass1274_2293, by decide, by decide, pass1274_2309, by decide, by decide, pass1274_2361, rfl⟩
def src1275 : Request := ⟨⟨⟨560,781,172,7715⟩,5388141854720,10440670587⟩,1,4,1,514727,26⟩
private theorem pass1275_2293 : (Triangular src1275) 2293 2298 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1275_2299 : (Triangular src1275) 2299 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1275_2318 : (Triangular src1275) 2318 2377 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1275_2378 : (Triangular src1275) 2378 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1275 : Cover (Triangular src1275) 2389 2293 [2298,2317,2377,2389] := by
  exact ⟨by decide, by decide, pass1275_2293, by decide, by decide, pass1275_2299, by decide, by decide, pass1275_2318, by decide, by decide, pass1275_2378, rfl⟩
def src1276 : Request := ⟨⟨⟨560,781,172,8679⟩,5388141854720,10440670587⟩,2,4,1,514727,26⟩
private theorem pass1276_2293 : (Triangular src1276) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1276_2295 : (Triangular src1276) 2295 2301 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1276_2302 : (Triangular src1276) 2302 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1276_2324 : (Triangular src1276) 2324 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1276 : Cover (Triangular src1276) 2389 2293 [2294,2301,2323,2389] := by
  exact ⟨by decide, by decide, pass1276_2293, by decide, by decide, pass1276_2295, by decide, by decide, pass1276_2302, by decide, by decide, pass1276_2324, rfl⟩
def src1277 : Request := ⟨⟨⟨690,962,212,12355⟩,10065769922560,23997864317⟩,6,4,1,514727,26⟩
private theorem pass1277_2293 : (Triangular src1277) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1277_2296 : (Triangular src1277) 2296 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1277_2306 : (Triangular src1277) 2306 2335 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1277_2336 : (Triangular src1277) 2336 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1277 : Cover (Triangular src1277) 2389 2293 [2295,2305,2335,2389] := by
  exact ⟨by decide, by decide, pass1277_2293, by decide, by decide, pass1277_2296, by decide, by decide, pass1277_2306, by decide, by decide, pass1277_2336, rfl⟩
def src1278 : Request := ⟨⟨⟨1200,1674,361,19788⟩,51955677528064,215563369662⟩,16,4,1,514727,26⟩
private theorem pass1278_2293 : (Triangular src1278) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1278_2296 : (Triangular src1278) 2296 2304 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1278_2305 : (Triangular src1278) 2305 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1278_2331 : (Triangular src1278) 2331 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1278 : Cover (Triangular src1278) 2389 2293 [2295,2304,2330,2389] := by
  exact ⟨by decide, by decide, pass1278_2293, by decide, by decide, pass1278_2296, by decide, by decide, pass1278_2305, by decide, by decide, pass1278_2331, rfl⟩
def src1279 : Request := ⟨⟨⟨2600,3627,798,45124⟩,535425056505856,4812227595495⟩,50,4,1,514727,26⟩
private theorem pass1279_2293 : (Triangular src1279) 2293 2300 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1279_2301 : (Triangular src1279) 2301 2322 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1279_2323 : (Triangular src1279) 2323 2384 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1279_2385 : (Triangular src1279) 2385 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1279 : Cover (Triangular src1279) 2389 2293 [2300,2322,2384,2389] := by
  exact ⟨by decide, by decide, pass1279_2293, by decide, by decide, pass1279_2301, by decide, by decide, pass1279_2323, by decide, by decide, pass1279_2385, rfl⟩
def src1280 : Request := ⟨⟨⟨3200,4463,982,208621⟩,997767489781760,11028049925768⟩,85,4,1,514727,26⟩
private theorem pass1280_2293 : (Triangular src1280) 2293 2295 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1280_2296 : (Triangular src1280) 2296 2303 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1280_2304 : (Triangular src1280) 2304 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1280_2327 : (Triangular src1280) 2327 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1280 : Cover (Triangular src1280) 2389 2293 [2295,2303,2326,2389] := by
  exact ⟨by decide, by decide, pass1280_2293, by decide, by decide, pass1280_2296, by decide, by decide, pass1280_2304, by decide, by decide, pass1280_2327, rfl⟩
def src1281 : Request := ⟨⟨⟨8300,11577,2548,164837⟩,17399709518790656,498847383098023⟩,190,4,1,514727,26⟩
private theorem pass1281_2293 : (Triangular src1281) 2293 2306 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1281_2307 : (Triangular src1281) 2307 2345 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1281_2346 : (Triangular src1281) 2346 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1281 : Cover (Triangular src1281) 2389 2293 [2306,2345,2389] := by
  exact ⟨by decide, by decide, pass1281_2293, by decide, by decide, pass1281_2307, by decide, by decide, pass1281_2346, rfl⟩
def src1282 : Request := ⟨⟨⟨10000,13950,3150,130242⟩,31027650042265600,1072717072025530⟩,190,4,1,514727,26⟩
private theorem pass1282_2293 : (Triangular src1282) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1282_2295 : (Triangular src1282) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1282_2300 : (Triangular src1282) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1282_2314 : (Triangular src1282) 2314 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1282_2352 : (Triangular src1282) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1282 : Cover (Triangular src1282) 2389 2293 [2294,2299,2313,2351,2389] := by
  exact ⟨by decide, by decide, pass1282_2293, by decide, by decide, pass1282_2295, by decide, by decide, pass1282_2300, by decide, by decide, pass1282_2314, by decide, by decide, pass1282_2352, rfl⟩
def src1283 : Request := ⟨⟨⟨8300,11575,2548,1085143⟩,17399709518790656,498569901356632⟩,245,4,1,514727,26⟩
private theorem pass1283_2293 : (Triangular src1283) 2293 2294 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1283_2295 : (Triangular src1283) 2295 2299 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1283_2300 : (Triangular src1283) 2300 2313 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1283_2314 : (Triangular src1283) 2314 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1283_2352 : (Triangular src1283) 2352 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1283 : Cover (Triangular src1283) 2389 2293 [2294,2299,2313,2351,2389] := by
  exact ⟨by decide, by decide, pass1283_2293, by decide, by decide, pass1283_2295, by decide, by decide, pass1283_2300, by decide, by decide, pass1283_2314, by decide, by decide, pass1283_2352, rfl⟩
def src1286 : Request := ⟨⟨⟨400,558,123,6858⟩,1971918995456,2734096379⟩,0,4,1,514727,30⟩
private theorem pass1286_2293 : (Triangular src1286) 2293 2305 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1286_2306 : (Triangular src1286) 2306 2348 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1286_2349 : (Triangular src1286) 2349 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1286 : Cover (Triangular src1286) 2389 2293 [2305,2348,2389] := by
  exact ⟨by decide, by decide, pass1286_2293, by decide, by decide, pass1286_2306, by decide, by decide, pass1286_2349, rfl⟩
def src1287 : Request := ⟨⟨⟨470,655,144,6858⟩,3184589537280,5168862572⟩,1,4,1,514727,30⟩
private theorem pass1287_2293 : (Triangular src1287) 2293 2310 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1287_2311 : (Triangular src1287) 2311 2369 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem pass1287_2370 : (Triangular src1287) 2370 2389 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
theorem cover1287 : Cover (Triangular src1287) 2389 2293 [2310,2369,2389] := by
  exact ⟨by decide, by decide, pass1287_2293, by decide, by decide, pass1287_2311, by decide, by decide, pass1287_2370, rfl⟩
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
  physicalFloor := 514727
  seedFloor := 16

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨4, 25, 9, 80/100, 70/100, ![27097084060228, 3339521140581, 24797959004, 2975770980], 9912770232322119⟩
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

def data : NearCase 4 16 25 514727 :=
  ⟨Lower6960.Prefix6969MainCases.HigherHelperCases6.plan, Lower6960.Prefix6969MainCases.HigherHelperCases6.price, Lower6960.Prefix6969MainCases.HigherHelperCases6.valid, Lower6960.Prefix6969MainCases.HigherHelperCases6.priced, Lower6960.Prefix6969MainCases.HigherHelperCases6.sources,
   Lower6960.Prefix6969RescueData.HigherHelperCases6.plan, Lower6960.Prefix6969RescueData.HigherHelperCases6.price, Lower6960.Prefix6969RescueData.HigherHelperCases6.sources, Lower6960.Prefix6969RescueData.HigherHelperCases6.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 231007981425998990 := by
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

theorem sources : plan.Sources 2293 (Band.near).last Prefix6969Helper.helperBank 128681 4 26 514727 := by
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

def price : Pricing := ⟨55/100, 90/100, [312369428, 312321291, 310582973, 311818578, 310880062, 310226033, 149404041, 149310446, 149307550, 149399334, 78104594, 93450520, 60294637, 93264841, 93468242, 99853536, 130083661, 165598540, 229106458], [1127045, 1127291, 1136184, 1129863, 1134664, 1138010, 2576786, 2578343, 2578391, 2576865, 5116793, 4241331, 6685066, 4250694, 4240437, 3960834, 2987354, 2307532, 1619981],
  ![121614290035560, 1612303922492, 206195812200, 5058325860], 167911077303670909⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  physicalFloor := 514727
  seedFloor := 26

theorem sources : plan.Sources 2293 (Band.near).last := by
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

def price : EarlyPrice := ⟨4, 29, 10, 75/100, 70/100, ![12250715387642, 1369232494893, 35561906100, 3678837750], 3775035387457175⟩
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

def data : NearCase 4 26 29 514727 :=
  ⟨Lower6960.Prefix6969MainCases.QuarticIntervals0.plan, Lower6960.Prefix6969MainCases.QuarticIntervals0.price, Lower6960.Prefix6969MainCases.QuarticIntervals0.valid, Lower6960.Prefix6969MainCases.QuarticIntervals0.priced, Lower6960.Prefix6969MainCases.QuarticIntervals0.sources,
   Lower6960.Prefix6969RescueData.QuarticIntervals0.plan, Lower6960.Prefix6969RescueData.QuarticIntervals0.price, Lower6960.Prefix6969RescueData.QuarticIntervals0.sources, Lower6960.Prefix6969RescueData.QuarticIntervals0.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 209672363053787736 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedQuarticIntervals0
end Z6969Source1607

end Merged_Z6969Pack0711

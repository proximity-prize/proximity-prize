import ProximityPrize.SubmissionLower.Z6970NativeNearLightData
import ProximityPrize.SubmissionLower.Z6969FastTri

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lower6960.Prefix6969MainCases.NativeLight2308
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks

open Research6969

private theorem head_2308 : (PhysicalWindow.Triangular head) 2308 2308 :=
  Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem head_2309 : (PhysicalWindow.Triangular head) 2309 2312 :=
  Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem head_2313 : (PhysicalWindow.Triangular head) 2313 2324 :=
  Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem head_2325 : (PhysicalWindow.Triangular head) 2325 2363 :=
  Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem head_2364 : (PhysicalWindow.Triangular head) 2364 2411 :=
  Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)

theorem head_cover : PhysicalWindow.Cover (PhysicalWindow.Triangular head) 2411 2308 [2308, 2312, 2324, 2363, 2411] := by
  exact ⟨by decide, by decide, head_2308, by decide, by decide, head_2309, by decide, by decide, head_2313, by decide, by decide, head_2325, by decide, by decide, head_2364, rfl⟩

private theorem free_0 : TransitionSources.Free 2308 0 (bank2 1526) := by
  have left : TransitionArithmetic.value (TransitionSources.request 0 (bank2 1526)) 2308 = 41929770840 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 0 (bank2 1526)) 2309 = 412835737584 := by decide +kernel
  refine ⟨rank2 1526, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_1 : TransitionSources.Free 2308 10 (bank61 2550) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank61 2550)) 2308 = 697798478792 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank61 2550)) 2309 = 9395604288646 := by decide +kernel
  refine ⟨rank61 2550, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_2 : TransitionSources.Free 2308 1 (bank8 1693) := by
  have left : TransitionArithmetic.value (TransitionSources.request 1 (bank8 1693)) 2308 = 59501285844 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 1 (bank8 1693)) 2309 = 621780951792 := by decide +kernel
  refine ⟨rank8 1693, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_3 : TransitionSources.Free 2308 8 (bank41 3006) := by
  have left : TransitionArithmetic.value (TransitionSources.request 8 (bank41 3006)) 2308 = 131809102616 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 8 (bank41 3006)) 2309 = 5716791036790 := by decide +kernel
  refine ⟨rank41 3006, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_4 : TransitionSources.Free 2308 21 (bank113 3744) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank113 3744)) 2308 = 5312713519540 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank113 3744)) 2309 = 77701702531670 := by decide +kernel
  refine ⟨rank113 3744, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_5 : TransitionSources.Free 2308 8 (bank48 2495) := by
  have left : TransitionArithmetic.value (TransitionSources.request 8 (bank48 2495)) 2308 = 269229527424 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 8 (bank48 2495)) 2309 = 5371958921472 := by decide +kernel
  refine ⟨rank48 2495, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_6 : TransitionSources.Free 2308 20 (bank73 5732) := by
  have left : TransitionArithmetic.value (TransitionSources.request 20 (bank73 5732)) 2308 = 1129174557966 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 20 (bank73 5732)) 2309 = 71151567220188 := by decide +kernel
  refine ⟨rank73 5732, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_7 : TransitionSources.Free 2308 41 (bank145 8026) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank145 8026)) 2308 = 7897751782532 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank145 8026)) 2309 = 748502136826786 := by decide +kernel
  refine ⟨rank145 8026, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_8 : TransitionSources.Free 2308 21 (bank74 6640) := by
  have left : TransitionArithmetic.value (TransitionSources.request 21 (bank74 6640)) 2308 = 1877092642587 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 21 (bank74 6640)) 2309 = 96892186785756 := by decide +kernel
  refine ⟨rank74 6640, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_9 : TransitionSources.Free 2308 10 (bank42 4592) := by
  have left : TransitionArithmetic.value (TransitionSources.request 10 (bank42 4592)) 2308 = 211388080431 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 10 (bank42 4592)) 2309 = 13458040934943 := by decide +kernel
  refine ⟨rank42 4592, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_10 : TransitionSources.Free 2308 5 (bank32 2251) := by
  have left : TransitionArithmetic.value (TransitionSources.request 5 (bank32 2251)) 2308 = 211025470608 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 5 (bank32 2251)) 2309 = 2484094317840 := by decide +kernel
  refine ⟨rank32 2251, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_11 : TransitionSources.Free 2308 25 (bank140 4025) := by
  have left : TransitionArithmetic.value (TransitionSources.request 25 (bank140 4025)) 2308 = 13888276978092 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 25 (bank140 4025)) 2309 = 172129141934013 := by decide +kernel
  refine ⟨rank140 4025, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_12 : TransitionSources.Free 2308 14 (bank85 2922) := by
  have left : TransitionArithmetic.value (TransitionSources.request 14 (bank85 2922)) 2308 = 3037892133674 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 14 (bank85 2922)) 2309 = 24723915429832 := by decide +kernel
  refine ⟨rank85 2922, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_13 : TransitionSources.Free 2308 41 (bank119 45346) := by
  have left : TransitionArithmetic.value (TransitionSources.request 41 (bank119 45346)) 2308 = 9723297300726 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 41 (bank119 45346)) 2309 = 12154532857444350 := by decide +kernel
  refine ⟨rank119 45346, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_14 : TransitionSources.Free 2308 3 (bank23 1901) := by
  have left : TransitionArithmetic.value (TransitionSources.request 3 (bank23 1901)) 2308 = 36387388338 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 3 (bank23 1901)) 2309 = 1202528099412 := by decide +kernel
  refine ⟨rank23 1901, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_15 : TransitionSources.Free 2308 65 (bank198 9892) := by
  have left : TransitionArithmetic.value (TransitionSources.request 65 (bank198 9892)) 2308 = 23890005907196 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 65 (bank198 9892)) 2309 = 4593909168086485 := by decide +kernel
  refine ⟨rank198 9892, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_16 : TransitionSources.Free 2308 76 (bank180 68470) := by
  have left : TransitionArithmetic.value (TransitionSources.request 76 (bank180 68470)) 2308 = 5713319386008 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 76 (bank180 68470)) 2309 = 124734132475944966 := by decide +kernel
  refine ⟨rank180 68470, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_17 : TransitionSources.Free 2308 2 (bank14 1832) := by
  have left : TransitionArithmetic.value (TransitionSources.request 2 (bank14 1832)) 2308 = 6550373973 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 2 (bank14 1832)) 2309 = 832414156782 := by decide +kernel
  refine ⟨rank14 1832, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_18 : TransitionSources.Free 2308 76 (bank212 10890) := by
  have left : TransitionArithmetic.value (TransitionSources.request 76 (bank212 10890)) 2308 = 287263133384656 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 76 (bank212 10890)) 2309 = 9372249866203484 := by decide +kernel
  refine ⟨rank212 10890, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

private theorem free_19 : TransitionSources.Free 2308 76 (bank174 186283) := by
  have left : TransitionArithmetic.value (TransitionSources.request 76 (bank174 186283)) 2308 = 23747604473180 := by decide +kernel
  have right : TransitionArithmetic.value (TransitionSources.request 76 (bank174 186283)) 2309 = 862230603778391680 := by decide +kernel
  refine ⟨rank174 186283, by decide, by decide, by unfold Lower6960.HelperSource.WidthGuard; decide +kernel, ?_, ?_⟩
  · rw [left]; decide
  · rw [left, right]; decide

theorem sources : plan.Sources 2308 (Band.near).last Prefix6969Helper.helperBank 128659 2 1 257319 := by
  refine ⟨?_, rank154 9078, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, head_cover⟩⟩
  · intro i; fin_cases i
    · exact free_0
    · exact free_1
    · exact free_2
    · exact free_3
    · exact free_4
    · exact free_5
    · exact free_6
    · exact free_7
    · exact free_8
    · exact free_9
    · exact free_10
    · exact free_11
    · exact free_12
    · exact free_13
    · exact free_14
    · exact free_15
    · exact free_16
    · exact free_17
    · exact free_18
    · exact free_19
  · unfold HelperSource.WidthGuard; decide +kernel


end Lower6960.Prefix6969MainCases.NativeLight2308

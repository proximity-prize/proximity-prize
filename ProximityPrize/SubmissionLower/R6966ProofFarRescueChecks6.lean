import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks

set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue2_14_first : value (rescue 2 14) 2500 = 132421732336759075896678 := by decide +kernel
private theorem rescue2_14_next : value (rescue 2 14) 2501 = 136529221910182029945303 := by decide +kernel
theorem rescue2_14 : Checked (rescue 2 14) := by
  refine ⟨(Lower6960.RescueSource.checked 2 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_14_first]; decide
  · rw [rescue2_14_first, rescue2_14_next]; decide

private theorem rescue2_15_first : value (rescue 2 15) 2500 = 156019239887049031420806 := by decide +kernel
private theorem rescue2_15_next : value (rescue 2 15) 2501 = 160858151451924683588028 := by decide +kernel
theorem rescue2_15 : Checked (rescue 2 15) := by
  refine ⟨(Lower6960.RescueSource.checked 2 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_15_first]; decide
  · rw [rescue2_15_first, rescue2_15_next]; decide

private theorem rescue2_16_first : value (rescue 2 16) 2500 = 614715813423326003510791 := by decide +kernel
private theorem rescue2_16_next : value (rescue 2 16) 2501 = 633908731043816422908990 := by decide +kernel
theorem rescue2_16 : Checked (rescue 2 16) := by
  refine ⟨(Lower6960.RescueSource.checked 2 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_16_first]; decide
  · rw [rescue2_16_first, rescue2_16_next]; decide

private theorem rescue3_0_first : value (rescue 3 0) 2500 = 571054573537562328 := by decide +kernel
private theorem rescue3_0_next : value (rescue 3 0) 2501 = 585704731900737520 := by decide +kernel
theorem rescue3_0 : Checked (rescue 3 0) := by
  refine ⟨(Lower6960.RescueSource.checked 3 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_0_first]; decide
  · rw [rescue3_0_first, rescue3_0_next]; decide

private theorem rescue3_1_first : value (rescue 3 1) 2500 = 853158943489220016 := by decide +kernel
private theorem rescue3_1_next : value (rescue 3 1) 2501 = 875317802416239028 := by decide +kernel
theorem rescue3_1 : Checked (rescue 3 1) := by
  refine ⟨(Lower6960.RescueSource.checked 3 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_1_first]; decide
  · rw [rescue3_1_first, rescue3_1_next]; decide

private theorem rescue3_2_first : value (rescue 3 2) 2500 = 1238642956876396036 := by decide +kernel
private theorem rescue3_2_next : value (rescue 3 2) 2501 = 1271166478557783815 := by decide +kernel
theorem rescue3_2 : Checked (rescue 3 2) := by
  refine ⟨(Lower6960.RescueSource.checked 3 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_2_first]; decide
  · rw [rescue3_2_first, rescue3_2_next]; decide

private theorem rescue3_3_first : value (rescue 3 3) 2500 = 1754076337755194773 := by decide +kernel
private theorem rescue3_3_next : value (rescue 3 3) 2501 = 1800583117170771125 := by decide +kernel
theorem rescue3_3 : Checked (rescue 3 3) := by
  refine ⟨(Lower6960.RescueSource.checked 3 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_3_first]; decide
  · rw [rescue3_3_first, rescue3_3_next]; decide

private theorem rescue3_4_first : value (rescue 3 4) 2500 = 3373904140539229960 := by decide +kernel
private theorem rescue3_4_next : value (rescue 3 4) 2501 = 3470057852182746812 := by decide +kernel
theorem rescue3_4 : Checked (rescue 3 4) := by
  refine ⟨(Lower6960.RescueSource.checked 3 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_4_first]; decide
  · rw [rescue3_4_first, rescue3_4_next]; decide

end Research6966.FarSourceData

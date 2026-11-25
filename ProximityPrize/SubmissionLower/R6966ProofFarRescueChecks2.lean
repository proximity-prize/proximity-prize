import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks

set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue0_16_first : value (rescue 0 16) 2500 = 1269885253216927929045076 := by decide +kernel
private theorem rescue0_16_next : value (rescue 0 16) 2501 = 1309537058206900886939694 := by decide +kernel
theorem rescue0_16 : Checked (rescue 0 16) := by
  refine ⟨(Lower6960.RescueSource.checked 0 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_16_first]; decide
  · rw [rescue0_16_first, rescue0_16_next]; decide

private theorem rescue1_0_first : value (rescue 1 0) 2500 = 9446580998809001817 := by decide +kernel
private theorem rescue1_0_next : value (rescue 1 0) 2501 = 9705082483429291370 := by decide +kernel
theorem rescue1_0 : Checked (rescue 1 0) := by
  refine ⟨(Lower6960.RescueSource.checked 1 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_0_first]; decide
  · rw [rescue1_0_first, rescue1_0_next]; decide

private theorem rescue1_1_first : value (rescue 1 1) 2500 = 14001958875307809660 := by decide +kernel
private theorem rescue1_1_next : value (rescue 1 1) 2501 = 14388322663096921616 := by decide +kernel
theorem rescue1_1 : Checked (rescue 1 1) := by
  refine ⟨(Lower6960.RescueSource.checked 1 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_1_first]; decide
  · rw [rescue1_1_first, rescue1_1_next]; decide

private theorem rescue1_2_first : value (rescue 1 2) 2500 = 19950139527325206572 := by decide +kernel
private theorem rescue1_2_next : value (rescue 1 2) 2501 = 20497810475344631758 := by decide +kernel
theorem rescue1_2 : Checked (rescue 1 2) := by
  refine ⟨(Lower6960.RescueSource.checked 1 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_2_first]; decide
  · rw [rescue1_2_first, rescue1_2_next]; decide

private theorem rescue1_3_first : value (rescue 1 3) 2500 = 29882043561175012619 := by decide +kernel
private theorem rescue1_3_next : value (rescue 1 3) 2501 = 30706977620205041764 := by decide +kernel
theorem rescue1_3 : Checked (rescue 1 3) := by
  refine ⟨(Lower6960.RescueSource.checked 1 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_3_first]; decide
  · rw [rescue1_3_first, rescue1_3_next]; decide

private theorem rescue1_4_first : value (rescue 1 4) 2500 = 45312293568469815162 := by decide +kernel
private theorem rescue1_4_next : value (rescue 1 4) 2501 = 46549285067623238248 := by decide +kernel
theorem rescue1_4 : Checked (rescue 1 4) := by
  refine ⟨(Lower6960.RescueSource.checked 1 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_4_first]; decide
  · rw [rescue1_4_first, rescue1_4_next]; decide

private theorem rescue1_5_first : value (rescue 1 5) 2500 = 58228505240814797814 := by decide +kernel
private theorem rescue1_5_next : value (rescue 1 5) 2501 = 59867177249803167019 := by decide +kernel
theorem rescue1_5 : Checked (rescue 1 5) := by
  refine ⟨(Lower6960.RescueSource.checked 1 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_5_first]; decide
  · rw [rescue1_5_first, rescue1_5_next]; decide

private theorem rescue1_6_first : value (rescue 1 6) 2500 = 105275161144409123357 := by decide +kernel
private theorem rescue1_6_next : value (rescue 1 6) 2501 = 108238543347595130254 := by decide +kernel
theorem rescue1_6 : Checked (rescue 1 6) := by
  refine ⟨(Lower6960.RescueSource.checked 1 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_6_first]; decide
  · rw [rescue1_6_first, rescue1_6_next]; decide

#print axioms rescue1_6
end Research6966.FarSourceData

import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks

set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue1_15_first : value (rescue 1 15) 2500 = 290393054611504529897787 := by decide +kernel
private theorem rescue1_15_next : value (rescue 1 15) 2501 = 299400074637871109439686 := by decide +kernel
theorem rescue1_15 : Checked (rescue 1 15) := by
  refine ⟨(Lower6960.RescueSource.checked 1 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_15_first]; decide
  · rw [rescue1_15_first, rescue1_15_next]; decide

private theorem rescue1_16_first : value (rescue 1 16) 2500 = 1143526957312259120039221 := by decide +kernel
private theorem rescue1_16_next : value (rescue 1 16) 2501 = 1179232953644946594618255 := by decide +kernel
theorem rescue1_16 : Checked (rescue 1 16) := by
  refine ⟨(Lower6960.RescueSource.checked 1 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_16_first]; decide
  · rw [rescue1_16_first, rescue1_16_next]; decide

private theorem rescue2_0_first : value (rescue 2 0) 2500 = 5031044487045557125 := by decide +kernel
private theorem rescue2_0_next : value (rescue 2 0) 2501 = 5168669874666108655 := by decide +kernel
theorem rescue2_0 : Checked (rescue 2 0) := by
  refine ⟨(Lower6960.RescueSource.checked 2 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_0_first]; decide
  · rw [rescue2_0_first, rescue2_0_next]; decide

private theorem rescue2_1_first : value (rescue 2 1) 2500 = 7447174124101057390 := by decide +kernel
private theorem rescue2_1_next : value (rescue 2 1) 2501 = 7652594532929012776 := by decide +kernel
theorem rescue2_1 : Checked (rescue 2 1) := by
  refine ⟨(Lower6960.RescueSource.checked 2 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_1_first]; decide
  · rw [rescue2_1_first, rescue2_1_next]; decide

private theorem rescue2_2_first : value (rescue 2 2) 2500 = 10674293380368463808 := by decide +kernel
private theorem rescue2_2_next : value (rescue 2 2) 2501 = 10967306893534922548 := by decide +kernel
theorem rescue2_2 : Checked (rescue 2 2) := by
  refine ⟨(Lower6960.RescueSource.checked 2 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_2_first]; decide
  · rw [rescue2_2_first, rescue2_2_next]; decide

private theorem rescue2_3_first : value (rescue 2 3) 2500 = 15812472779339573914 := by decide +kernel
private theorem rescue2_3_next : value (rescue 2 3) 2501 = 16248896162591045289 := by decide +kernel
theorem rescue2_3 : Checked (rescue 2 3) := by
  refine ⟨(Lower6960.RescueSource.checked 2 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_3_first]; decide
  · rw [rescue2_3_first, rescue2_3_next]; decide

private theorem rescue2_4_first : value (rescue 2 4) 2500 = 24489961659828102396 := by decide +kernel
private theorem rescue2_4_next : value (rescue 2 4) 2501 = 25158397091824896031 := by decide +kernel
theorem rescue2_4 : Checked (rescue 2 4) := by
  refine ⟨(Lower6960.RescueSource.checked 2 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_4_first]; decide
  · rw [rescue2_4_first, rescue2_4_next]; decide

private theorem rescue2_5_first : value (rescue 2 5) 2500 = 31286295617483879916 := by decide +kernel
private theorem rescue2_5_next : value (rescue 2 5) 2501 = 32166689881104109306 := by decide +kernel
theorem rescue2_5 : Checked (rescue 2 5) := by
  refine ⟨(Lower6960.RescueSource.checked 2 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_5_first]; decide
  · rw [rescue2_5_first, rescue2_5_next]; decide

#print axioms rescue2_5
end Research6966.FarSourceData

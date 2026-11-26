import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks

set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue3_13_first : value (rescue 3 13) 2500 = 3426300973429294155110 := by decide +kernel
private theorem rescue3_13_next : value (rescue 3 13) 2501 = 3536005756630677942176 := by decide +kernel
theorem rescue3_13 : Checked (rescue 3 13) := by
  refine ⟨(Lower6960.RescueSource.checked 3 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_13_first]; decide
  · rw [rescue3_13_first, rescue3_13_next]; decide

private theorem rescue3_14_first : value (rescue 3 14) 2500 = 29439486548858626005840 := by decide +kernel
private theorem rescue3_14_next : value (rescue 3 14) 2501 = 30395574250841928123084 := by decide +kernel
theorem rescue3_14 : Checked (rescue 3 14) := by
  refine ⟨(Lower6960.RescueSource.checked 3 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_14_first]; decide
  · rw [rescue3_14_first, rescue3_14_next]; decide

private theorem rescue3_15_first : value (rescue 3 15) 2500 = 31020158890438917462528 := by decide +kernel
private theorem rescue3_15_next : value (rescue 3 15) 2501 = 32027695557008749827528 := by decide +kernel
theorem rescue3_15 : Checked (rescue 3 15) := by
  refine ⟨(Lower6960.RescueSource.checked 3 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_15_first]; decide
  · rw [rescue3_15_first, rescue3_15_next]; decide

private theorem rescue3_16_first : value (rescue 3 16) 2500 = 139121037464327994105625 := by decide +kernel
private theorem rescue3_16_next : value (rescue 3 16) 2501 = 143671876465115519119505 := by decide +kernel
theorem rescue3_16 : Checked (rescue 3 16) := by
  refine ⟨(Lower6960.RescueSource.checked 3 16).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_16_first]; decide
  · rw [rescue3_16_first, rescue3_16_next]; decide

end Research6966.FarSourceData

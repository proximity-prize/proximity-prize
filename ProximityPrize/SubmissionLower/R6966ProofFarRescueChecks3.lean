import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks

set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue1_7_first : value (rescue 1 7) 2500 = 233422341187846868928 := by decide +kernel
private theorem rescue1_7_next : value (rescue 1 7) 2501 = 240189899884662811344 := by decide +kernel
theorem rescue1_7 : Checked (rescue 1 7) := by
  refine ⟨(Lower6960.RescueSource.checked 1 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_7_first]; decide
  · rw [rescue1_7_first, rescue1_7_next]; decide

private theorem rescue1_8_first : value (rescue 1 8) 2500 = 821365910173302514846 := by decide +kernel
private theorem rescue1_8_next : value (rescue 1 8) 2501 = 845512826842987886588 := by decide +kernel
theorem rescue1_8 : Checked (rescue 1 8) := by
  refine ⟨(Lower6960.RescueSource.checked 1 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_8_first]; decide
  · rw [rescue1_8_first, rescue1_8_next]; decide

private theorem rescue1_9_first : value (rescue 1 9) 2500 = 231758248375551757734 := by decide +kernel
private theorem rescue1_9_next : value (rescue 1 9) 2501 = 238367500397426289232 := by decide +kernel
theorem rescue1_9 : Checked (rescue 1 9) := by
  refine ⟨(Lower6960.RescueSource.checked 1 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_9_first]; decide
  · rw [rescue1_9_first, rescue1_9_next]; decide

private theorem rescue1_10_first : value (rescue 1 10) 2500 = 2097555160088184952298 := by decide +kernel
private theorem rescue1_10_next : value (rescue 1 10) 2501 = 2163058113226408993868 := by decide +kernel
theorem rescue1_10 : Checked (rescue 1 10) := by
  refine ⟨(Lower6960.RescueSource.checked 1 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_10_first]; decide
  · rw [rescue1_10_first, rescue1_10_next]; decide

private theorem rescue1_11_first : value (rescue 1 11) 2500 = 10748297243627875180629 := by decide +kernel
private theorem rescue1_11_next : value (rescue 1 11) 2501 = 11090373346079633610905 := by decide +kernel
theorem rescue1_11 : Checked (rescue 1 11) := by
  refine ⟨(Lower6960.RescueSource.checked 1 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_11_first]; decide
  · rw [rescue1_11_first, rescue1_11_next]; decide

private theorem rescue1_12_first : value (rescue 1 12) 2500 = 7592333631044703731098 := by decide +kernel
private theorem rescue1_12_next : value (rescue 1 12) 2501 = 7819542522739321389704 := by decide +kernel
theorem rescue1_12 : Checked (rescue 1 12) := by
  refine ⟨(Lower6960.RescueSource.checked 1 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_12_first]; decide
  · rw [rescue1_12_first, rescue1_12_next]; decide

private theorem rescue1_13_first : value (rescue 1 13) 2500 = 29308852925721156821476 := by decide +kernel
private theorem rescue1_13_next : value (rescue 1 13) 2501 = 30206371674240607729652 := by decide +kernel
theorem rescue1_13 : Checked (rescue 1 13) := by
  refine ⟨(Lower6960.RescueSource.checked 1 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_13_first]; decide
  · rw [rescue1_13_first, rescue1_13_next]; decide

private theorem rescue1_14_first : value (rescue 1 14) 2500 = 246356693317397817437802 := by decide +kernel
private theorem rescue1_14_next : value (rescue 1 14) 2501 = 253998762909327923502483 := by decide +kernel
theorem rescue1_14 : Checked (rescue 1 14) := by
  refine ⟨(Lower6960.RescueSource.checked 1 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue1_14_first]; decide
  · rw [rescue1_14_first, rescue1_14_next]; decide

end Research6966.FarSourceData

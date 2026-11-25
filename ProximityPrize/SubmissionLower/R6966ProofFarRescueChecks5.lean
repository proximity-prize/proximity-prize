import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks

set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue2_6_first : value (rescue 2 6) 2500 = 56554010939252338012 := by decide +kernel
private theorem rescue2_6_next : value (rescue 2 6) 2501 = 58159095225425908478 := by decide +kernel
theorem rescue2_6 : Checked (rescue 2 6) := by
  refine ⟨(Lower6960.RescueSource.checked 2 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_6_first]; decide
  · rw [rescue2_6_first, rescue2_6_next]; decide

private theorem rescue2_7_first : value (rescue 2 7) 2500 = 125389383643885901947 := by decide +kernel
private theorem rescue2_7_next : value (rescue 2 7) 2501 = 129024462748550222803 := by decide +kernel
theorem rescue2_7 : Checked (rescue 2 7) := by
  refine ⟨(Lower6960.RescueSource.checked 2 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_7_first]; decide
  · rw [rescue2_7_first, rescue2_7_next]; decide

private theorem rescue2_8_first : value (rescue 2 8) 2500 = 439989294265627393651 := by decide +kernel
private theorem rescue2_8_next : value (rescue 2 8) 2501 = 452923574151052020716 := by decide +kernel
theorem rescue2_8 : Checked (rescue 2 8) := by
  refine ⟨(Lower6960.RescueSource.checked 2 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_8_first]; decide
  · rw [rescue2_8_first, rescue2_8_next]; decide

private theorem rescue2_9_first : value (rescue 2 9) 2500 = 125610982215366456807 := by decide +kernel
private theorem rescue2_9_next : value (rescue 2 9) 2501 = 129192245794332386604 := by decide +kernel
theorem rescue2_9 : Checked (rescue 2 9) := by
  refine ⟨(Lower6960.RescueSource.checked 2 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_9_first]; decide
  · rw [rescue2_9_first, rescue2_9_next]; decide

private theorem rescue2_10_first : value (rescue 2 10) 2500 = 1055612922482978680346 := by decide +kernel
private theorem rescue2_10_next : value (rescue 2 10) 2501 = 1088575010666752872580 := by decide +kernel
theorem rescue2_10 : Checked (rescue 2 10) := by
  refine ⟨(Lower6960.RescueSource.checked 2 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_10_first]; decide
  · rw [rescue2_10_first, rescue2_10_next]; decide

private theorem rescue2_11_first : value (rescue 2 11) 2500 = 5418264560832903526446 := by decide +kernel
private theorem rescue2_11_next : value (rescue 2 11) 2501 = 5590692198590890295100 := by decide +kernel
theorem rescue2_11 : Checked (rescue 2 11) := by
  refine ⟨(Lower6960.RescueSource.checked 2 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_11_first]; decide
  · rw [rescue2_11_first, rescue2_11_next]; decide

private theorem rescue2_12_first : value (rescue 2 12) 2500 = 4078791219813825109952 := by decide +kernel
private theorem rescue2_12_next : value (rescue 2 12) 2501 = 4201998622377786379260 := by decide +kernel
theorem rescue2_12 : Checked (rescue 2 12) := by
  refine ⟨(Lower6960.RescueSource.checked 2 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_12_first]; decide
  · rw [rescue2_12_first, rescue2_12_next]; decide

private theorem rescue2_13_first : value (rescue 2 13) 2500 = 15750887035699472247560 := by decide +kernel
private theorem rescue2_13_next : value (rescue 2 13) 2501 = 16233189396354780503020 := by decide +kernel
theorem rescue2_13 : Checked (rescue 2 13) := by
  refine ⟨(Lower6960.RescueSource.checked 2 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue2_13_first]; decide
  · rw [rescue2_13_first, rescue2_13_next]; decide

#print axioms rescue2_13
end Research6966.FarSourceData

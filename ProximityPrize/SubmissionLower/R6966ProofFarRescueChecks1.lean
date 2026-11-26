import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks

set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue0_8_first : value (rescue 0 8) 2500 = 912427661893587705799 := by decide +kernel
private theorem rescue0_8_next : value (rescue 0 8) 2501 = 939251876096981101666 := by decide +kernel
theorem rescue0_8 : Checked (rescue 0 8) := by
  refine ⟨(Lower6960.RescueSource.checked 0 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_8_first]; decide
  · rw [rescue0_8_first, rescue0_8_next]; decide

private theorem rescue0_9_first : value (rescue 0 9) 2500 = 257034987547554581055 := by decide +kernel
private theorem rescue0_9_next : value (rescue 0 9) 2501 = 264365328801503474158 := by decide +kernel
theorem rescue0_9 : Checked (rescue 0 9) := by
  refine ⟨(Lower6960.RescueSource.checked 0 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_9_first]; decide
  · rw [rescue0_9_first, rescue0_9_next]; decide

private theorem rescue0_10_first : value (rescue 0 10) 2500 = 2350580671494326962932 := by decide +kernel
private theorem rescue0_10_next : value (rescue 0 10) 2501 = 2423986017714281426824 := by decide +kernel
theorem rescue0_10 : Checked (rescue 0 10) := by
  refine ⟨(Lower6960.RescueSource.checked 0 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_10_first]; decide
  · rw [rescue0_10_first, rescue0_10_next]; decide

private theorem rescue0_11_first : value (rescue 0 11) 2500 = 12042490607355333949626 := by decide +kernel
private theorem rescue0_11_next : value (rescue 0 11) 2501 = 12425760753592068549196 := by decide +kernel
theorem rescue0_11 : Checked (rescue 0 11) := by
  refine ⟨(Lower6960.RescueSource.checked 0 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_11_first]; decide
  · rw [rescue0_11_first, rescue0_11_next]; decide

private theorem rescue0_12_first : value (rescue 0 12) 2500 = 8419425329442702445664 := by decide +kernel
private theorem rescue0_12_next : value (rescue 0 12) 2501 = 8671395886040534647942 := by decide +kernel
theorem rescue0_12 : Checked (rescue 0 12) := by
  refine ⟨(Lower6960.RescueSource.checked 0 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_12_first]; decide
  · rw [rescue0_12_first, rescue0_12_next]; decide

private theorem rescue0_13_first : value (rescue 0 13) 2500 = 32547715487452834841286 := by decide +kernel
private theorem rescue0_13_next : value (rescue 0 13) 2501 = 33544428708249865045030 := by decide +kernel
theorem rescue0_13 : Checked (rescue 0 13) := by
  refine ⟨(Lower6960.RescueSource.checked 0 13).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_13_first]; decide
  · rw [rescue0_13_first, rescue0_13_next]; decide

private theorem rescue0_14_first : value (rescue 0 14) 2500 = 273578179010343667143012 := by decide +kernel
private theorem rescue0_14_next : value (rescue 0 14) 2501 = 282064749013297117834402 := by decide +kernel
theorem rescue0_14 : Checked (rescue 0 14) := by
  refine ⟨(Lower6960.RescueSource.checked 0 14).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_14_first]; decide
  · rw [rescue0_14_first, rescue0_14_next]; decide

private theorem rescue0_15_first : value (rescue 0 15) 2500 = 322480502313854216370543 := by decide +kernel
private theorem rescue0_15_next : value (rescue 0 15) 2501 = 332482850079789965273574 := by decide +kernel
theorem rescue0_15 : Checked (rescue 0 15) := by
  refine ⟨(Lower6960.RescueSource.checked 0 15).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_15_first]; decide
  · rw [rescue0_15_first, rescue0_15_next]; decide

end Research6966.FarSourceData

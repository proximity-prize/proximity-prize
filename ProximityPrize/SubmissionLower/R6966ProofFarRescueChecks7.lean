import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks

set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue3_5_first : value (rescue 3 5) 2500 = 7234917591785099579 := by decide +kernel
private theorem rescue3_5_next : value (rescue 3 5) 2501 = 7446446027841214042 := by decide +kernel
theorem rescue3_5 : Checked (rescue 3 5) := by
  refine ⟨(Lower6960.RescueSource.checked 3 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_5_first]; decide
  · rw [rescue3_5_first, rescue3_5_next]; decide

private theorem rescue3_6_first : value (rescue 3 6) 2500 = 10778515783766270260 := by decide +kernel
private theorem rescue3_6_next : value (rescue 3 6) 2501 = 11096791618677810416 := by decide +kernel
theorem rescue3_6 : Checked (rescue 3 6) := by
  refine ⟨(Lower6960.RescueSource.checked 3 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_6_first]; decide
  · rw [rescue3_6_first, rescue3_6_next]; decide

private theorem rescue3_7_first : value (rescue 3 7) 2500 = 29923925157609053915 := by decide +kernel
private theorem rescue3_7_next : value (rescue 3 7) 2501 = 30826326476262669865 := by decide +kernel
theorem rescue3_7 : Checked (rescue 3 7) := by
  refine ⟨(Lower6960.RescueSource.checked 3 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_7_first]; decide
  · rw [rescue3_7_first, rescue3_7_next]; decide

private theorem rescue3_8_first : value (rescue 3 8) 2500 = 75739281428015823970 := by decide +kernel
private theorem rescue3_8_next : value (rescue 3 8) 2501 = 78056490935257730231 := by decide +kernel
theorem rescue3_8 : Checked (rescue 3 8) := by
  refine ⟨(Lower6960.RescueSource.checked 3 8).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_8_first]; decide
  · rw [rescue3_8_first, rescue3_8_next]; decide

private theorem rescue3_9_first : value (rescue 3 9) 2500 = 22190573565964535350 := by decide +kernel
private theorem rescue3_9_next : value (rescue 3 9) 2501 = 22855453625777264084 := by decide +kernel
theorem rescue3_9 : Checked (rescue 3 9) := by
  refine ⟨(Lower6960.RescueSource.checked 3 9).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_9_first]; decide
  · rw [rescue3_9_first, rescue3_9_next]; decide

private theorem rescue3_10_first : value (rescue 3 10) 2500 = 120675090489418488200 := by decide +kernel
private theorem rescue3_10_next : value (rescue 3 10) 2501 = 124132577991603564052 := by decide +kernel
theorem rescue3_10 : Checked (rescue 3 10) := by
  refine ⟨(Lower6960.RescueSource.checked 3 10).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_10_first]; decide
  · rw [rescue3_10_first, rescue3_10_next]; decide

private theorem rescue3_11_first : value (rescue 3 11) 2500 = 658268072256700279500 := by decide +kernel
private theorem rescue3_11_next : value (rescue 3 11) 2501 = 677496680588562185784 := by decide +kernel
theorem rescue3_11 : Checked (rescue 3 11) := by
  refine ⟨(Lower6960.RescueSource.checked 3 11).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_11_first]; decide
  · rw [rescue3_11_first, rescue3_11_next]; decide

private theorem rescue3_12_first : value (rescue 3 12) 2500 = 710030447432995484000 := by decide +kernel
private theorem rescue3_12_next : value (rescue 3 12) 2501 = 732442180436809828444 := by decide +kernel
theorem rescue3_12 : Checked (rescue 3 12) := by
  refine ⟨(Lower6960.RescueSource.checked 3 12).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue3_12_first]; decide
  · rw [rescue3_12_first, rescue3_12_next]; decide

#print axioms rescue3_12
end Research6966.FarSourceData

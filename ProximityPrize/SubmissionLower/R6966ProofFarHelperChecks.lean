import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks

set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem helper_twoSlopes_first : value (helper .twoSlopes) 2500 = 6080496006636510 := by decide +kernel
private theorem helper_twoSlopes_next : value (helper .twoSlopes) 2501 = 6214822928196240 := by decide +kernel
theorem helper_twoSlopes : Checked (helper .twoSlopes) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_twoSlopes_first]; decide
  · rw [helper_twoSlopes_first, helper_twoSlopes_next]; decide

private theorem helper_seedBoundary_first : value (helper .seedBoundary) 2500 = 7086781651814660 := by decide +kernel
private theorem helper_seedBoundary_next : value (helper .seedBoundary) 2501 = 7221506482073278 := by decide +kernel
theorem helper_seedBoundary : Checked (helper .seedBoundary) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_seedBoundary_first]; decide
  · rw [helper_seedBoundary_first, helper_seedBoundary_next]; decide

private theorem helper_mixedBoundary_first : value (helper .mixedBoundary) 2500 = 6890632660446510 := by decide +kernel
private theorem helper_mixedBoundary_next : value (helper .mixedBoundary) 2501 = 7025283636667764 := by decide +kernel
theorem helper_mixedBoundary : Checked (helper .mixedBoundary) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_mixedBoundary_first]; decide
  · rw [helper_mixedBoundary_first, helper_mixedBoundary_next]; decide

private theorem helper_jetBoundary_first : value (helper .jetBoundary) 2500 = 13339034061441510 := by decide +kernel
private theorem helper_jetBoundary_next : value (helper .jetBoundary) 2501 = 13476264398223162 := by decide +kernel
theorem helper_jetBoundary : Checked (helper .jetBoundary) := by
  refine ⟨Lower6960.HelperSource.helper_bank_checked, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [helper_jetBoundary_first]; decide
  · rw [helper_jetBoundary_first, helper_jetBoundary_next]; decide

#print axioms helper_jetBoundary
end Research6966.FarSourceData

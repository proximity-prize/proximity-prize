import ProximityPrize.SubmissionLower.R6966ProofFarFreeChecks

set_option Elab.async false

namespace Research6966.FarSourceData
open FarSourceArithmetic (Checked value)
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem rescue0_0_first : value (rescue 0 0) 2500 = 10505766189606195061 := by decide +kernel
private theorem rescue0_0_next : value (rescue 0 0) 2501 = 10793268565957207597 := by decide +kernel
theorem rescue0_0 : Checked (rescue 0 0) := by
  refine ⟨(Lower6960.RescueSource.checked 0 0).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_0_first]; decide
  · rw [rescue0_0_first, rescue0_0_next]; decide

private theorem rescue0_1_first : value (rescue 0 1) 2500 = 15574478826192316168 := by decide +kernel
private theorem rescue0_1_next : value (rescue 0 1) 2501 = 16004250785028507558 := by decide +kernel
theorem rescue0_1 : Checked (rescue 0 1) := by
  refine ⟨(Lower6960.RescueSource.checked 0 1).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_1_first]; decide
  · rw [rescue0_1_first, rescue0_1_next]; decide

private theorem rescue0_2_first : value (rescue 0 2) 2500 = 22168233743209321838 := by decide +kernel
private theorem rescue0_2_next : value (rescue 0 2) 2501 = 22776805033227124196 := by decide +kernel
theorem rescue0_2 : Checked (rescue 0 2) := by
  refine ⟨(Lower6960.RescueSource.checked 0 2).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_2_first]; decide
  · rw [rescue0_2_first, rescue0_2_next]; decide

private theorem rescue0_3_first : value (rescue 0 3) 2500 = 33251329977009224722 := by decide +kernel
private theorem rescue0_3_next : value (rescue 0 3) 2501 = 34169300650617939114 := by decide +kernel
theorem rescue0_3 : Checked (rescue 0 3) := by
  refine ⟨(Lower6960.RescueSource.checked 0 3).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_3_first]; decide
  · rw [rescue0_3_first, rescue0_3_next]; decide

private theorem rescue0_4_first : value (rescue 0 4) 2500 = 50267517639787383310 := by decide +kernel
private theorem rescue0_4_next : value (rescue 0 4) 2501 = 51639826555203254336 := by decide +kernel
theorem rescue0_4 : Checked (rescue 0 4) := by
  refine ⟨(Lower6960.RescueSource.checked 0 4).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_4_first]; decide
  · rw [rescue0_4_first, rescue0_4_next]; decide

private theorem rescue0_5_first : value (rescue 0 5) 2500 = 64666749246345675912 := by decide +kernel
private theorem rescue0_5_next : value (rescue 0 5) 2501 = 66486628551539604283 := by decide +kernel
theorem rescue0_5 : Checked (rescue 0 5) := by
  refine ⟨(Lower6960.RescueSource.checked 0 5).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_5_first]; decide
  · rw [rescue0_5_first, rescue0_5_next]; decide

private theorem rescue0_6_first : value (rescue 0 6) 2500 = 116769067225652875307 := by decide +kernel
private theorem rescue0_6_next : value (rescue 0 6) 2501 = 120056129343609753202 := by decide +kernel
theorem rescue0_6 : Checked (rescue 0 6) := by
  refine ⟨(Lower6960.RescueSource.checked 0 6).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_6_first]; decide
  · rw [rescue0_6_first, rescue0_6_next]; decide

private theorem rescue0_7_first : value (rescue 0 7) 2500 = 259251431271776906495 := by decide +kernel
private theorem rescue0_7_next : value (rescue 0 7) 2501 = 266767880593701807818 := by decide +kernel
theorem rescue0_7 : Checked (rescue 0 7) := by
  refine ⟨(Lower6960.RescueSource.checked 0 7).bank_ok, (by unfold Lower6960.HelperSource.WidthGuard; decide),
    (by decide), (by decide), (by decide), ?_, ?_⟩
  · rw [rescue0_7_first]; decide
  · rw [rescue0_7_first, rescue0_7_next]; decide

#print axioms rescue0_7
end Research6966.FarSourceData

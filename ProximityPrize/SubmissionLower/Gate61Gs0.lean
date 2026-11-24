import ProximityPrize.SubmissionLower.Gate61Fin
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem c_0_2 : one 0 2 = true := by decide +kernel
theorem c_0_3 : one 0 3 = true := by decide +kernel
theorem c_0_4 : one 0 4 = true := by decide +kernel
theorem c_0_5 : one 0 5 = true := by decide +kernel
end Gate61Fin

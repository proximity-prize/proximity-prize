import ProximityPrize.SubmissionLower.Gate61Fin
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem c_0_2 : one 0 2 = true := by decide +kernel
theorem c_0_10 : one 0 10 = true := by decide +kernel
theorem c_2_5 : one 2 5 = true := by decide +kernel
theorem c_2_11 : one 2 11 = true := by decide +kernel
theorem c_3_11 : one 3 11 = true := by decide +kernel
theorem c_4_4 : one 4 4 = true := by decide +kernel
theorem c_4_9 : one 4 9 = true := by decide +kernel
theorem c_5_7 : one 5 7 = true := by decide +kernel
theorem c_5_9 : one 5 9 = true := by decide +kernel
theorem c_6_5 : one 6 5 = true := by decide +kernel
theorem c_7_10 : one 7 10 = true := by decide +kernel
end Gate61Fin

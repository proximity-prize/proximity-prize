import ProximityPrize.SubmissionLower.Gate61Fin
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem g_0_2 : gtOne 0 2 = true := by decide +kernel
theorem g_0_10 : gtOne 0 10 = true := by decide +kernel
theorem g_2_5 : gtOne 2 5 = true := by decide +kernel
theorem g_2_11 : gtOne 2 11 = true := by decide +kernel
theorem g_3_11 : gtOne 3 11 = true := by decide +kernel
theorem g_4_4 : gtOne 4 4 = true := by decide +kernel
theorem g_4_9 : gtOne 4 9 = true := by decide +kernel
theorem g_5_7 : gtOne 5 7 = true := by decide +kernel
theorem g_5_9 : gtOne 5 9 = true := by decide +kernel
theorem g_6_5 : gtOne 6 5 = true := by decide +kernel
theorem g_7_10 : gtOne 7 10 = true := by decide +kernel
end Gate61Fin

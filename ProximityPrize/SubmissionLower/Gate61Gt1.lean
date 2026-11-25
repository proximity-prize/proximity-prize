import ProximityPrize.SubmissionLower.Gate61Fin
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem g_0_12 : gtOne 0 12 = true := by decide +kernel
theorem g_1_2 : gtOne 1 2 = true := by decide +kernel
theorem g_1_5 : gtOne 1 5 = true := by decide +kernel
theorem g_1_9 : gtOne 1 9 = true := by decide +kernel
theorem g_1_11 : gtOne 1 11 = true := by decide +kernel
theorem g_2_9 : gtOne 2 9 = true := by decide +kernel
theorem g_3_3 : gtOne 3 3 = true := by decide +kernel
theorem g_4_6 : gtOne 4 6 = true := by decide +kernel
theorem g_4_8 : gtOne 4 8 = true := by decide +kernel
theorem g_4_12 : gtOne 4 12 = true := by decide +kernel
theorem g_6_9 : gtOne 6 9 = true := by decide +kernel
theorem g_9_13 : gtOne 9 13 = true := by decide +kernel
end Gate61Fin

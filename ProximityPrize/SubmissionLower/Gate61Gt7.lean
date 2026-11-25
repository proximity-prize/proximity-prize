import ProximityPrize.SubmissionLower.Gate61Fin
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem g_0_5 : gtOne 0 5 = true := by decide +kernel
theorem g_0_6 : gtOne 0 6 = true := by decide +kernel
theorem g_1_7 : gtOne 1 7 = true := by decide +kernel
theorem g_3_5 : gtOne 3 5 = true := by decide +kernel
theorem g_3_6 : gtOne 3 6 = true := by decide +kernel
theorem g_3_13 : gtOne 3 13 = true := by decide +kernel
theorem g_4_13 : gtOne 4 13 = true := by decide +kernel
theorem g_6_11 : gtOne 6 11 = true := by decide +kernel
theorem g_7_9 : gtOne 7 9 = true := by decide +kernel
theorem g_7_11 : gtOne 7 11 = true := by decide +kernel
theorem g_8_9 : gtOne 8 9 = true := by decide +kernel
end Gate61Fin

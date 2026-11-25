import ProximityPrize.SubmissionLower.Gate61Fin
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem g_0_3 : gtOne 0 3 = true := by decide +kernel
theorem g_0_9 : gtOne 0 9 = true := by decide +kernel
theorem g_2_7 : gtOne 2 7 = true := by decide +kernel
theorem g_2_12 : gtOne 2 12 = true := by decide +kernel
theorem g_3_8 : gtOne 3 8 = true := by decide +kernel
theorem g_4_7 : gtOne 4 7 = true := by decide +kernel
theorem g_5_12 : gtOne 5 12 = true := by decide +kernel
theorem g_6_10 : gtOne 6 10 = true := by decide +kernel
theorem g_7_8 : gtOne 7 8 = true := by decide +kernel
theorem g_7_12 : gtOne 7 12 = true := by decide +kernel
theorem g_9_11 : gtOne 9 11 = true := by decide +kernel
end Gate61Fin

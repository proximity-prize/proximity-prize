import ProximityPrize.SubmissionLower.Gate61Fin
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem g_0_4 : gtOne 0 4 = true := by decide +kernel
theorem g_0_8 : gtOne 0 8 = true := by decide +kernel
theorem g_2_6 : gtOne 2 6 = true := by decide +kernel
theorem g_2_10 : gtOne 2 10 = true := by decide +kernel
theorem g_3_4 : gtOne 3 4 = true := by decide +kernel
theorem g_4_11 : gtOne 4 11 = true := by decide +kernel
theorem g_5_6 : gtOne 5 6 = true := by decide +kernel
theorem g_5_13 : gtOne 5 13 = true := by decide +kernel
theorem g_6_6 : gtOne 6 6 = true := by decide +kernel
theorem g_6_12 : gtOne 6 12 = true := by decide +kernel
theorem g_7_7 : gtOne 7 7 = true := by decide +kernel
end Gate61Fin

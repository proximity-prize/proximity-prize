import ProximityPrize.SubmissionLower.Gate61Fin
set_option maxHeartbeats 20000000
set_option Elab.async false
set_option maxRecDepth 200000
namespace Gate61Fin

theorem g_12_11 : gtOne 12 11 = true := by decide +kernel
theorem g_12_12 : gtOne 12 12 = true := by decide +kernel
theorem g_12_13 : gtOne 12 13 = true := by decide +kernel
theorem g_13_5 : gtOne 13 5 = true := by decide +kernel
theorem g_13_6 : gtOne 13 6 = true := by decide +kernel
theorem g_13_7 : gtOne 13 7 = true := by decide +kernel
theorem g_13_8 : gtOne 13 8 = true := by decide +kernel
theorem g_13_9 : gtOne 13 9 = true := by decide +kernel
end Gate61Fin

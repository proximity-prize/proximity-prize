import ProximityPrize.SubmissionLower.Gate61Fin
set_option maxHeartbeats 20000000
set_option Elab.async false
set_option maxRecDepth 200000
namespace Gate61Fin

theorem g_10_10 : gtOne 10 10 = true := by decide +kernel
theorem g_10_11 : gtOne 10 11 = true := by decide +kernel
theorem g_10_12 : gtOne 10 12 = true := by decide +kernel
theorem g_10_13 : gtOne 10 13 = true := by decide +kernel
theorem g_11_9 : gtOne 11 9 = true := by decide +kernel
theorem g_11_10 : gtOne 11 10 = true := by decide +kernel
theorem g_11_11 : gtOne 11 11 = true := by decide +kernel
theorem g_11_12 : gtOne 11 12 = true := by decide +kernel
end Gate61Fin

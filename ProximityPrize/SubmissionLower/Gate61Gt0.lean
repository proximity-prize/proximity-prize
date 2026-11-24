import ProximityPrize.SubmissionLower.Gate61Fin
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem g_0_2 : gtOne 0 2 = true := by decide +kernel
theorem g_0_3 : gtOne 0 3 = true := by decide +kernel
theorem g_0_4 : gtOne 0 4 = true := by decide +kernel
theorem g_0_5 : gtOne 0 5 = true := by decide +kernel
end Gate61Fin

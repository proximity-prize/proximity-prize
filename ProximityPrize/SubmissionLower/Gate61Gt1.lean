import ProximityPrize.SubmissionLower.Gate61Fin
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem g_0_6 : gtOne 0 6 = true := by decide +kernel
theorem g_0_7 : gtOne 0 7 = true := by decide +kernel
end Gate61Fin

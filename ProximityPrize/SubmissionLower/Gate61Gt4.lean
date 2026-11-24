import ProximityPrize.SubmissionLower.Gate61Fin
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem g_0_11 : gtOne 0 11 = true := by decide +kernel
end Gate61Fin

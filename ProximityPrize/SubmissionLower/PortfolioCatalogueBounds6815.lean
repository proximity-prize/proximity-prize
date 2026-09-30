import ProximityPrize.SubmissionLower.PortfolioUniformBudgets6815
namespace ProximityPrize.SubmissionLower.PortfolioSourceCatalogue6815
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

theorem small (i : Fin 75) : (profile i).B≤256 ∧ (profile i).U≤512 ∧
    (profile i).L≤4096 ∧ (profile i).s≤64 ∧ (profile i).L+(profile i).s≤8192 := by
  fin_cases i <;> decide +kernel

end ProximityPrize.SubmissionLower.PortfolioSourceCatalogue6815

import ProximityPrize.SubmissionLower.FirstCutValuation6807
import ProximityPrize.SubmissionLower.BoundaryTailPole
namespace ProximityPrize.SubmissionLower.ActualFirstCutPole6807
open scoped BigOperators
open RCN055 RCN057 RCN095 RCN136 RCN156 RCN204 RCN234 RCN313
open BoundaryTailAlgebra FirstCutValuation6807
set_option autoImplicit false
noncomputable section
variable {K Ω L : Type} [Field K] [Field Ω] [Field L]

theorem pole_le_of_value_le
    (V : Valuation L (WithZero (Multiplicative ℤ)))
    (a : L) (bound : ℤ) (hb : 0 ≤ bound)
    (ha : V a ≤ WithZero.exp bound) : RCN187.poleOrder V a ≤ bound := by
  unfold RCN187.poleOrder
  apply max_le hb
  by_cases hz : V a = 0
  · simpa [hz] using hb
  · simpa only [WithZero.log_exp] using
      (WithZero.log_le_log hz WithZero.exp_ne_zero).mpr ha

end
end ProximityPrize.SubmissionLower.ActualFirstCutPole6807

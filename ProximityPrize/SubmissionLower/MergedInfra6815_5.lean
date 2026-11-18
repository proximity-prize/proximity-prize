import ProximityPrize.SubmissionLower.MergedInfra6815_4
import ProximityPrize.SubmissionLower.MergedInfra6815_2
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Field
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.FirstCutValuation6807
open scoped BigOperators
set_option autoImplicit false
variable {L : Type*} [Field L]

end ProximityPrize.SubmissionLower.FirstCutValuation6807
end MergedPart0
section MergedPart1
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
end MergedPart1

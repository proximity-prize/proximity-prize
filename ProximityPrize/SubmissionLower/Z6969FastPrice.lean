import ProximityPrize.SubmissionLower.Z6969Pack0560
set_option Elab.async false
set_option autoImplicit false

namespace Lower6960.Prefix6969Main
noncomputable section
open K1 (p)
open P1_7_4 (dotQ)

/-- First two conjuncts of `Pricing.Valid.rates`, decided once for all stages
(the shared `seedLimit` is then evaluated a single time). -/
def RatesAB (x : Pricing) (s : Plan) : Prop :=
  ∀ i : Fin s.count, ((p+1 : ℕ) : ℚ)/81 ≤ (x.degreeRate i.val : ℚ) ∧
      min s.seedLimit (dotQ (s.cutWeight 0 i.val) (s.history i.val)) ≤ (x.degreeRate i.val : ℚ)

instance (x : Pricing) (s : Plan) : Decidable (RatesAB x s) := by unfold RatesAB; infer_instance

end
end Lower6960.Prefix6969Main

import ProximityPrize.SubmissionLower.R6966ProofSpreadReceipts0

set_option Elab.async false

namespace Research6966.SpreadCatalogue
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge34_3_31_2373_2414_cost : SpreadInterval.costSum shape 179769 34 3 31 2373 2414 ≤ 3392457228 := by
  decide +kernel

theorem edge34_3_31_2373_2414 : SpreadInterval.Positive shape 179769 34 3 31 nodes moment 2373 2414 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_3_31_2373_2414_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_19_25_2415_2499_cost : SpreadInterval.costSum shape 179769 25 19 25 2415 2499 ≤ 3393938951 := by
  decide +kernel

theorem edge25_19_25_2415_2499 : SpreadInterval.Positive shape 179769 25 19 25 nodes moment 2415 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_19_25_2415_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_3_31_2415_2499_cost : SpreadInterval.costSum shape 179769 34 3 31 2415 2499 ≤ 3395482463 := by
  decide +kernel

theorem edge34_3_31_2415_2499 : SpreadInterval.Positive shape 179769 34 3 31 nodes moment 2415 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_3_31_2415_2499_cost) _).trans_lt <;>
    decide +kernel

end Research6966.SpreadCatalogue

import ProximityPrize.SubmissionLower.R6966ProofSpreadReceipts0

set_option Elab.async false

namespace Research6966.SpreadCatalogue
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge34_24_34_2330_2499_cost : SpreadInterval.costSum shape 179769 34 24 34 2330 2499 ≤ 3050408279 := by
  decide +kernel

theorem edge34_24_34_2330_2499 : SpreadInterval.Positive shape 179769 34 24 34 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_24_34_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_25_34_2330_2499_cost : SpreadInterval.costSum shape 179769 34 25 34 2330 2499 ≤ 3128221108 := by
  decide +kernel

theorem edge34_25_34_2330_2499 : SpreadInterval.Positive shape 179769 34 25 34 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_25_34_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_26_34_2330_2499_cost : SpreadInterval.costSum shape 179769 34 26 34 2330 2499 ≤ 3207872808 := by
  decide +kernel

theorem edge34_26_34_2330_2499 : SpreadInterval.Positive shape 179769 34 26 34 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_26_34_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_27_34_2330_2499_cost : SpreadInterval.costSum shape 179769 34 27 34 2330 2499 ≤ 3288975664 := by
  decide +kernel

theorem edge34_27_34_2330_2499 : SpreadInterval.Positive shape 179769 34 27 34 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_27_34_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_28_34_2330_2499_cost : SpreadInterval.costSum shape 179769 34 28 34 2330 2499 ≤ 3371531908 := by
  decide +kernel

theorem edge34_28_34_2330_2499 : SpreadInterval.Positive shape 179769 34 28 34 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_28_34_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_3_31_2341_2351_cost : SpreadInterval.costSum shape 179769 34 3 31 2341 2351 ≤ 3389971284 := by
  decide +kernel

theorem edge34_3_31_2341_2351 : SpreadInterval.Positive shape 179769 34 3 31 nodes moment 2341 2351 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_3_31_2341_2351_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_3_31_2352_2372_cost : SpreadInterval.costSum shape 179769 34 3 31 2352 2372 ≤ 3390816708 := by
  decide +kernel

theorem edge34_3_31_2352_2372 : SpreadInterval.Positive shape 179769 34 3 31 nodes moment 2352 2372 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_3_31_2352_2372_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_19_25_2373_2414_cost : SpreadInterval.costSum shape 179769 25 19 25 2373 2414 ≤ 3390924487 := by
  decide +kernel

theorem edge25_19_25_2373_2414 : SpreadInterval.Positive shape 179769 25 19 25 nodes moment 2373 2414 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_19_25_2373_2414_cost) _).trans_lt <;>
    decide +kernel

end Research6966.SpreadCatalogue

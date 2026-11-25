import ProximityPrize.SubmissionLower.R6966ProofSpreadReceipts0

set_option Elab.async false

namespace Research6966.SpreadCatalogue
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge25_6_25_2330_2499_cost : SpreadInterval.costSum shape 179769 25 6 25 2330 2499 ≤ 2961174822 := by
  decide +kernel

theorem edge25_6_25_2330_2499 : SpreadInterval.Positive shape 179769 25 6 25 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_6_25_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_13_25_2330_2499_cost : SpreadInterval.costSum shape 179769 25 13 25 2330 2499 ≤ 2898592239 := by
  decide +kernel

theorem edge25_13_25_2330_2499 : SpreadInterval.Positive shape 179769 25 13 25 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_13_25_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_14_25_2330_2499_cost : SpreadInterval.costSum shape 179769 25 14 25 2330 2499 ≤ 2963570709 := by
  decide +kernel

theorem edge25_14_25_2330_2499 : SpreadInterval.Positive shape 179769 25 14 25 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_14_25_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_15_25_2330_2499_cost : SpreadInterval.costSum shape 179769 25 15 25 2330 2499 ≤ 3037434851 := by
  decide +kernel

theorem edge25_15_25_2330_2499 : SpreadInterval.Positive shape 179769 25 15 25 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_15_25_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_16_25_2330_2499_cost : SpreadInterval.costSum shape 179769 25 16 25 2330 2499 ≤ 3118661402 := by
  decide +kernel

theorem edge25_16_25_2330_2499 : SpreadInterval.Positive shape 179769 25 16 25 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_16_25_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_17_25_2330_2499_cost : SpreadInterval.costSum shape 179769 25 17 25 2330 2499 ≤ 3206053118 := by
  decide +kernel

theorem edge25_17_25_2330_2499 : SpreadInterval.Positive shape 179769 25 17 25 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_17_25_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_18_25_2330_2499_cost : SpreadInterval.costSum shape 179769 25 18 25 2330 2499 ≤ 3298685645 := by
  decide +kernel

theorem edge25_18_25_2330_2499 : SpreadInterval.Positive shape 179769 25 18 25 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_18_25_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_4_32_2330_2499_cost : SpreadInterval.costSum shape 179769 34 4 32 2330 2499 ≤ 3147910001 := by
  decide +kernel

theorem edge34_4_32_2330_2499 : SpreadInterval.Positive shape 179769 34 4 32 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_4_32_2330_2499_cost) _).trans_lt <;>
    decide +kernel

end Research6966.SpreadCatalogue

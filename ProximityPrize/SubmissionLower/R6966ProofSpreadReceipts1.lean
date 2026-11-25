import ProximityPrize.SubmissionLower.R6966ProofSpreadReceipts0

set_option Elab.async false

namespace Research6966.SpreadCatalogue
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge21_6_20_2330_2499_cost : SpreadInterval.costSum shape 179769 21 6 20 2330 2499 ≤ 3189889402 := by
  decide +kernel

theorem edge21_6_20_2330_2499 : SpreadInterval.Positive shape 179769 21 6 20 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_6_20_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge21_7_21_2330_2499_cost : SpreadInterval.costSum shape 179769 21 7 21 2330 2499 ≤ 3059322792 := by
  decide +kernel

theorem edge21_7_21_2330_2499 : SpreadInterval.Positive shape 179769 21 7 21 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_7_21_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge21_11_21_2330_2499_cost : SpreadInterval.costSum shape 179769 21 11 21 2330 2499 ≤ 3101940611 := by
  decide +kernel

theorem edge21_11_21_2330_2499 : SpreadInterval.Positive shape 179769 21 11 21 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_11_21_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge21_12_21_2330_2499_cost : SpreadInterval.costSum shape 179769 21 12 21 2330 2499 ≤ 3167968851 := by
  decide +kernel

theorem edge21_12_21_2330_2499 : SpreadInterval.Positive shape 179769 21 12 21 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_12_21_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge21_13_21_2330_2499_cost : SpreadInterval.costSum shape 179769 21 13 21 2330 2499 ≤ 3247487099 := by
  decide +kernel

theorem edge21_13_21_2330_2499 : SpreadInterval.Positive shape 179769 21 13 21 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_13_21_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge21_14_21_2330_2499_cost : SpreadInterval.costSum shape 179769 21 14 21 2330 2499 ≤ 3337925119 := by
  decide +kernel

theorem edge21_14_21_2330_2499 : SpreadInterval.Positive shape 179769 21 14 21 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_14_21_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_4_23_2330_2499_cost : SpreadInterval.costSum shape 179769 25 4 23 2330 2499 ≤ 3367614645 := by
  decide +kernel

theorem edge25_4_23_2330_2499 : SpreadInterval.Positive shape 179769 25 4 23 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_4_23_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_5_24_2330_2499_cost : SpreadInterval.costSum shape 179769 25 5 24 2330 2499 ≤ 3147118853 := by
  decide +kernel

theorem edge25_5_24_2330_2499 : SpreadInterval.Positive shape 179769 25 5 24 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_5_24_2330_2499_cost) _).trans_lt <;>
    decide +kernel

end Research6966.SpreadCatalogue

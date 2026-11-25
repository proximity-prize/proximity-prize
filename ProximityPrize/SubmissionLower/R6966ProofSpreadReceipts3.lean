import ProximityPrize.SubmissionLower.R6966ProofSpreadReceipts0

set_option Elab.async false

namespace Research6966.SpreadCatalogue
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge34_5_33_2330_2499_cost : SpreadInterval.costSum shape 179769 34 5 33 2330 2499 ≤ 2914232977 := by
  decide +kernel

theorem edge34_5_33_2330_2499 : SpreadInterval.Positive shape 179769 34 5 33 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_5_33_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_6_34_2330_2499_cost : SpreadInterval.costSum shape 179769 34 6 34 2330 2499 ≤ 2713416436 := by
  decide +kernel

theorem edge34_6_34_2330_2499 : SpreadInterval.Positive shape 179769 34 6 34 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_6_34_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_18_34_2330_2499_cost : SpreadInterval.costSum shape 179769 34 18 34 2330 2499 ≤ 2635167444 := by
  decide +kernel

theorem edge34_18_34_2330_2499 : SpreadInterval.Positive shape 179769 34 18 34 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_18_34_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_19_34_2330_2499_cost : SpreadInterval.costSum shape 179769 34 19 34 2330 2499 ≤ 2696385646 := by
  decide +kernel

theorem edge34_19_34_2330_2499 : SpreadInterval.Positive shape 179769 34 19 34 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_19_34_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_20_34_2330_2499_cost : SpreadInterval.costSum shape 179769 34 20 34 2330 2499 ≤ 2761405288 := by
  decide +kernel

theorem edge34_20_34_2330_2499 : SpreadInterval.Positive shape 179769 34 20 34 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_20_34_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_21_34_2330_2499_cost : SpreadInterval.costSum shape 179769 34 21 34 2330 2499 ≤ 2829700148 := by
  decide +kernel

theorem edge34_21_34_2330_2499 : SpreadInterval.Positive shape 179769 34 21 34 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_21_34_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_22_34_2330_2499_cost : SpreadInterval.costSum shape 179769 34 22 34 2330 2499 ≤ 2900857796 := by
  decide +kernel

theorem edge34_22_34_2330_2499 : SpreadInterval.Positive shape 179769 34 22 34 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_22_34_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge34_23_34_2330_2499_cost : SpreadInterval.costSum shape 179769 34 23 34 2330 2499 ≤ 2974545301 := by
  decide +kernel

theorem edge34_23_34_2330_2499 : SpreadInterval.Positive shape 179769 34 23 34 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_23_34_2330_2499_cost) _).trans_lt <;>
    decide +kernel

end Research6966.SpreadCatalogue

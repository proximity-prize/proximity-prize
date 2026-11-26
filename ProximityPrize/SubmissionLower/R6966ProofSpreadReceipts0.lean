import ProximityPrize.SubmissionLower.R6966ProofSpreadInterval
import ProximityPrize.SubmissionLower.R6966ProofSpreadMoment

set_option Elab.async false

-- merged module R6966ProofSpreadRanks
section Merged_R6966ProofSpreadRanks

namespace Research6966.SpreadCatalogue
open K1_14 (Shape)
def shape : Shape := ⟨4000, 5585, 1200, 510000⟩
def box : Fin 2 → ℕ := ![255000, 255000]
def nodes : ℕ := 1914889096396800
def moment : ℕ := 26538075533683

theorem node_eq : P1_7_1.nodeRows shape = nodes := by
  have rank := P1_7_1_2.six_nodeRows shape (by decide) (by decide)
  have closed : 262144*P1_7_1_2.sixPerNode (shape.m-2*shape.J) shape.J = 6*nodes := by decide
  rw [closed] at rank
  omega

theorem pole_cap : P1_7_1.groupedPoleMoment shape.B shape.J ≤ moment :=
  Research6966.HelperWindowCatalogue.moment5585_1200

end Research6966.SpreadCatalogue

end Merged_R6966ProofSpreadRanks

-- merged module R6966ProofSpreadReceipts0
section Merged_R6966ProofSpreadReceipts0

namespace Research6966.SpreadCatalogue
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge34_3_31_2330_2340_cost : SpreadInterval.costSum shape 179769 34 3 31 2330 2340 ≤ 3389618477 := by
  decide +kernel

theorem edge34_3_31_2330_2340 : SpreadInterval.Positive shape 179769 34 3 31 nodes moment 2330 2340 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge34_3_31_2330_2340_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_19_25_2330_2372_cost : SpreadInterval.costSum shape 179769 25 19 25 2330 2372 ≤ 3389772380 := by
  decide +kernel

theorem edge25_19_25_2330_2372 : SpreadInterval.Positive shape 179769 25 19 25 nodes moment 2330 2372 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_19_25_2330_2372_cost) _).trans_lt <;>
    decide +kernel

private theorem edge19_6_18_2330_2499_cost : SpreadInterval.costSum shape 179769 19 6 18 2330 2499 ≤ 3317754791 := by
  decide +kernel

theorem edge19_6_18_2330_2499 : SpreadInterval.Positive shape 179769 19 6 18 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge19_6_18_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge19_7_19_2330_2499_cost : SpreadInterval.costSum shape 179769 19 7 19 2330 2499 ≤ 3191364370 := by
  decide +kernel

theorem edge19_7_19_2330_2499 : SpreadInterval.Positive shape 179769 19 7 19 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge19_7_19_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge19_10_19_2330_2499_cost : SpreadInterval.costSum shape 179769 19 10 19 2330 2499 ≤ 3232532412 := by
  decide +kernel

theorem edge19_10_19_2330_2499 : SpreadInterval.Positive shape 179769 19 10 19 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge19_10_19_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge19_11_19_2330_2499_cost : SpreadInterval.costSum shape 179769 19 11 19 2330 2499 ≤ 3298129966 := by
  decide +kernel

theorem edge19_11_19_2330_2499 : SpreadInterval.Positive shape 179769 19 11 19 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge19_11_19_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge19_12_19_2330_2499_cost : SpreadInterval.costSum shape 179769 19 12 19 2330 2499 ≤ 3380711383 := by
  decide +kernel

theorem edge19_12_19_2330_2499 : SpreadInterval.Positive shape 179769 19 12 19 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge19_12_19_2330_2499_cost) _).trans_lt <;>
    decide +kernel

private theorem edge21_5_19_2330_2499_cost : SpreadInterval.costSum shape 179769 21 5 19 2330 2499 ≤ 3363394990 := by
  decide +kernel

theorem edge21_5_19_2330_2499 : SpreadInterval.Positive shape 179769 21 5 19 nodes moment 2330 2499 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge21_5_19_2330_2499_cost) _).trans_lt <;>
    decide +kernel

end Research6966.SpreadCatalogue

end Merged_R6966ProofSpreadReceipts0

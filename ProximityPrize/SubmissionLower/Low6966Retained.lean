import ProximityPrize.SubmissionLower.R6960Low6960Retained
import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.Low6966Order

set_option Elab.async false

namespace Final50PriceLayer
open K1_13 (Shape)
open K1_13_8 (zeroShape zeroMass fastRemaining)
open Final50Price (remaining symbolCount)
open P0_9_8 (symbol_count)
open scoped BigOperators



end Final50PriceLayer


-- merged module R6960Low6966Retained
section Merged_R6960Low6966Retained

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace Low6966Retained
open K1_13 (Shape InBox)
open K1_13_8 (Valid zeroShape zeroMass)
open P0_9_8 (symbol_count)

local notation "layerNeed" => LowProfile6966.need
open Final50PriceLayer (layerTerm)
open scoped BigOperators
open P3_6_8 (shapeSum shapeSum_empty shapeSum_valid_or_empty spend_le)
open P3_6_8_1 (sumBelow term mass_eq extend)


def Box (a : Shape) : Prop :=
  a.b ≤ 27 ∧ a.j ≤ 8 ∧ (4 ≤ a.j → a.b ≤ 25) ∧ (5 ≤ a.j → a.b ≤ 22) ∧
  (6 ≤ a.j → a.b ≤ 19) ∧ (7 ≤ a.j → a.b ≤ 14) ∧ (8 ≤ a.j → a.b ≤ 6)


local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl























































































































































































































end Low6966Retained

end Merged_R6960Low6966Retained

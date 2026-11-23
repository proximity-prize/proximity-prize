import ProximityPrize.SubmissionLower.Final50PriceLayer

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace Final50PriceRetained
open K1_13 (Shape InBox)
open K1_13_8 (Valid zeroShape zeroMass)
open P0_9_8 (symbol_count)
open Final50Price (layerNeed)
open Final50PriceLayer (layerTerm layerCount)
open scoped BigOperators
open private P3_6_8.shapeSum P3_6_8.shapeSum_empty P3_6_8.shapeSum_valid_or_empty P3_6_8.spend_le
  P3_6_8_1.sumBelow P3_6_8_1.term P3_6_8_1.mass_eq P3_6_8_1.extend
  from ProximityPrize.SubmissionLower.GoldBranch6N8


def combined {n : ℕ} (a : Fin n → Shape) (z : Finset (Fin n)) := P3_6_8.shapeSum a z

local notation "row!" h "," len "," nxt "," v "," z =>
  P3_6_8_1.extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl










end Final50PriceRetained

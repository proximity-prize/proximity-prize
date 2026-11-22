import ProximityPrize.SubmissionLower.Low53At2389PriceCaps
import ProximityPrize.SubmissionLower.Low53At2389PriceLayer

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Low53At2389PriceMass
open Low53At2389PriceCaps (Band start thresholds order)
open Low53At2389Price (layerNeed)
open K1_13 (Shape remaining)
open K1_13_8 (zeroShape)
open Low53At2389PriceLayer (fastLayer availableMass)
open K1_13_8_2 (Threshold)
open P0_9_8 (symbol_count)
open private P3_6_8_1.sumBelow P3_6_8_1.sumBelow_eq
  from ProximityPrize.SubmissionLower.GoldBranch6N8

theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  rw [P3_6_8_1.sumBelow_eq, Low53At2389PriceLayer.availableMass_eq_sum hr hj le_rfl]

end Low53At2389PriceMass

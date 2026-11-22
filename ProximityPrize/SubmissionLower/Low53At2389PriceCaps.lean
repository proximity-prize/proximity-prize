import ProximityPrize.SubmissionLower.Low53At2389PriceThresholds

set_option Elab.async false
namespace Low53At2389PriceCaps
open K1_13 (Shape)
open K1_13_8_2 (orderFor)

abbrev thresholds := Low53At2389PriceThresholds.thresholds

def order (k : Band) (x : Shape) : ℕ := orderFor x.b x.j (thresholds k)

theorem order_pos (k : Band) (x : Shape) : 0 < order k x :=
  (P0_9_8.orderFor_select x.b x.j (thresholds k)).1

theorem order_mono (k : Band) {x y : Shape} (hb : x.b ≤ y.b) (hj : x.j ≤ y.j) :
    order k x ≤ order k y := P0_9_8.orderFor_mono hb hj _

end Low53At2389PriceCaps

import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand0
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand1
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand2
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand3
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand4
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand5
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand6
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand7
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand8
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand9
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand10
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand11
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand12
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand13
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand14
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand15
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand16
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand17
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand18
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand19
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand20
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand21
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand22
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand23
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand24
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand25
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand26
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand27
import ProximityPrize.SubmissionLower.Low53At2389PriceMassBand28

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
open K1_13 (Shape)
open K1_13_8 (zeroShape)
open Low53At2389PriceCaps (order)
private theorem thresholds_valid (k : Band) (q : Threshold) (hq : q ∈ thresholds k) :
    0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  cases k with
  | empty => exact checked0 q hq
  | one3 => exact checked1 q hq
  | one4 => exact checked2 q hq
  | one5 => exact checked3 q hq
  | one6 => exact checked4 q hq
  | one7 => exact checked5 q hq
  | two6 w =>
    fin_cases w
    · exact checked6 q hq
    · exact checked7 q hq
    · exact checked8 q hq
    · exact checked9 q hq
    · exact checked10 q hq
    · exact checked11 q hq
    · exact checked12 q hq
    · exact checked13 q hq
    · exact checked14 q hq
    · exact checked15 q hq
    · exact checked16 q hq
    · exact checked17 q hq
    · exact checked18 q hq
    · exact checked19 q hq
    · exact checked20 q hq
  | two7 w =>
    fin_cases w
    · exact checked21 q hq
    · exact checked22 q hq
    · exact checked23 q hq
    · exact checked24 q hq
    · exact checked25 q hq
    · exact checked26 q hq
    · exact checked27 q hq
    · exact checked28 q hq

theorem order_valid (k : Band) (x : Shape) : order k x = 1 ∨
    availableMass (start k) x (order k x - 1) < layerNeed := by
  rcases (P0_9_8.orderFor_select x.b x.j (thresholds k)).2 with h | ⟨q,hq,hb,hj,he⟩
  · exact Or.inl h
  · right
    change order k x = q.l at he
    rw [he]
    obtain ⟨hpos, hsmall⟩ := thresholds_valid k q hq
    have hr : start k = zeroShape ∨ 0 < (start k).j := Low53At2389PriceCaps.start_or_index k
    have hi : 0 < (start k).j + q.j := by omega
    exact (Low53At2389PriceLayer.availableMass_anti_prefix (y := ⟨q.b,q.j,0⟩) hr hi hb hj).trans_lt hsmall
#print axioms order_valid
end Low53At2389PriceMass

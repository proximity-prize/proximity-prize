import ProximityPrize.SubmissionLower.Z6970H2307AllocationGlue
import ProximityPrize.SubmissionLower.Z6970H2307CountEndpoint
import ProximityPrize.SubmissionLower.Z6970H2307OrderLookup
import ProximityPrize.SubmissionLower.Z6970H2307OrderExclusions

namespace Height2307Count6970
open K1_13 (Shape)
open Height2307Allocation (Order Companion PointTable Exclusions)
open Height2307Orders

def order : Order := fun k x => Height2307Orders.order k x.b x.j

theorem exclusions : Exclusions :=
  ⟨excludeB28J3,excludeB3J9,excludeB26J4,excludeB23J5,excludeB20J6,excludeB15J7,excludeB8J8⟩

theorem count_with_table {G : Shape → ℕ} {Gated : ℕ → Shape → Prop}
    {book : Height2307Bands.Band → Shape → Option ℕ}
    (gate : GateProof G Gated) (validOrder : Height2307Allocation.OrderValid order)
    (companions : Companion order book)
    (points : PointTable order book G Gated)
    (hceil : Height2307Inventory.layerWidth*(Height2307Inventory.layerNeed-1) <
      ExpandedOrderH2307.sourceRank)
    {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179730 M Γ)
    (lo : 1≤M.overhead) (hi : M.overhead≤2307) :
    Γ.card≤274779381266040420 := by
  have alloc : Allocation Height2307Bands.budget 179 G Gated :=
    Height2307Allocation.allocation_of_tables exclusions validOrder companions points hceil
  exact count_from_certificates gate alloc hceil Low6969FatFactors.proof M F lo hi

end Height2307Count6970

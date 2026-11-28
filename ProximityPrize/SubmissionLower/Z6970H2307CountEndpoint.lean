import ProximityPrize.SubmissionLower.Z6970H2307CountCore
import ProximityPrize.SubmissionLower.Z6970H2307Leading
import ProximityPrize.SubmissionLower.E6970EulerAnchor

namespace Height2307Count6970
open K1_13 (Shape)
open Low6969Prices (TrueWeightLE anchorCutoff)
open LowProfile6969 (trueWeight_iff differentialWeight_eq)
open scoped BigOperators Polynomial

theorem count_from_certificates {G : Shape → ℕ} {Gated : ℕ → Shape → Prop}
    (gate : GateProof G Gated) (allocate : Allocation 274779381265980820 179 G Gated)
    (hceil : Height2307Inventory.layerWidth*(Height2307Inventory.layerNeed-1) <
      ExpandedOrderH2307.sourceRank)
    (hfat : Low6969Fat.c2) {cap u del Γ}
    (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179730 M Γ)
    (lo : 1 ≤ M.overhead) (hi : M.overhead ≤ 2307) :
    Γ.card ≤ 274779381266040420 := by
  have messages := Low6969Order.messages_of_family M F hi
  obtain ⟨P,nz,box,active,weight,zero⟩ := LowAnchor6970.anchor_of_family M F hi
  have hw : TrueWeightLE P anchorCutoff := by
    apply (trueWeight_iff P).mpr
    rw [←differentialWeight_eq,←PolynomialDifferential.differentialWeightedDegree]
    exact weight
  obtain ⟨book,E,booked,fat⟩ := LowProfile6969.fat_of_family hfat M F lo hi
  exact count_of_data gate allocate messages hceil
    P nz box hw active zero (fun _ ht => Height2307LeadingLeading.lower_count ht) book E booked fat

end Height2307Count6970

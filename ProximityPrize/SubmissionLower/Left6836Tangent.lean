/- Apache-2.0. Bome2017, price one live seed per normalized polynomial using the full hard-case hypotheses. -/
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the independent full-domain primary proof of Bome2017 after Lucieno (PR 618) and BitWonka. Exact 68.33 constants and physical hypotheses are new. -/
import ProximityPrize.SubmissionLower.Koala6831MovingSources
import ProximityPrize.SubmissionLower.Left6836Count

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped Classical BigOperators
open Koala6831MovingSources LocatorLowQuotient

noncomputable section

variable {K I : Type} [Field K] [CharP K Left6836List.prime] [Fintype I]

private def FlowData.left6836TangentFactors (B : FlowData K) (H : P4 K) : Finset (P4 K) :=
  (RCN167.positiveRFactors H).filter (fun F => F ∣ B.flow F)

theorem FlowData.left6836_screen_tangent_seeds
    (B : FlowData K) (H : P4 K) (hH : H ≠ 0)
    (hbox : H ∈ nestedCoefficientBox K (322 * 181039) weight 83491 444 99)
    (Γ : Finset K) (selected normalized : K → Polynomial K)
    (nodes : Finset I) (points received : I → K)
    (hinj : Set.InjOn points nodes) (hnodes : nodes.card = Left6836List.n)
    (hd0 : B.d0 ≠ 0) (ha : B.A ≠ 0)
    (hden : ∀ g ∈ Γ, B.seedDenominator g ≠ 0)
    (hselected : ∀ g ∈ Γ, (selected g).natDegree ≤ weight)
    (hnorm : ∀ g ∈ Γ,
      B.d0 * selected g + B.seedOffset g = B.seedDenominator g * normalized g)
    (hdegree : ∀ g ∈ Γ, (normalized g).natDegree ≤ Left6836List.w)
    (hagreement : ∀ g ∈ Γ, Left6836List.agreements ≤
      (nodes.filter (fun i => (normalized g).eval (points i) = received i)).card)
    (nondiv : ¬ B.d0 ∣ B.a0*B.c1-B.a1*B.c0) :
    ∃ retained ⊆ Γ, Γ.card ≤ retained.card + left6836_tangentSeedBudget ∧
      ∀ g ∈ retained, ∀ F : RCN266.RegularIndex H,
        RCN319.specialization K (selected g) g F.1 = 0 → ¬F.1 ∣ B.flow F.1 := by
  classical
  let factors := B.left6836TangentFactors H
  let hits (g : K) := ∃ F ∈ factors, RCN319.specialization K (selected g) g F = 0
  let removed := Γ.filter hits
  let retained := Γ.filter (fun g => ¬ hits g)
  have hremoved : removed ⊆ Γ := Finset.filter_subset _ _
  have hretained : retained ⊆ Γ := Finset.filter_subset _ _
  have hproduct : (∏ F ∈ factors, F) ∣ H :=
    (Finset.prod_dvd_prod_of_subset factors (RCN167.positiveRFactors H) id
      (Finset.filter_subset _ _)).trans (RCN167.positiveRFactors_product_dvd H hH)
  have htangent : ∀ F ∈ factors, F ∣ B.flow F :=
    fun F hF => (Finset.mem_filter.mp hF).2
  have hweights := nested_mem_weights hbox hH
  have hcap : H.weightedTotalDegree ![0, 1, 1, 1] < Left6836List.prime :=
    hweights.1.trans_lt (by decide +kernel : 83491 < Left6836List.prime)
  have hbound : removed.card ≤ left6836_tangentSeedBudget :=
    B.left6836_tangent_seed_card_le H hH factors hproduct htangent hcap hweights.2.1 hweights.2.2.1
      removed selected normalized nodes points received hinj hnodes hd0 ha
      (fun g hg => hden g (hremoved hg)) (fun g hg => hselected g (hremoved hg))
      (fun g hg => hnorm g (hremoved hg)) (fun g hg => hdegree g (hremoved hg))
      (fun g hg => hagreement g (hremoved hg)) (fun g hg => (Finset.mem_filter.mp hg).2)
      nondiv
  have hsplit : removed.card + retained.card = Γ.card :=
    Finset.card_filter_add_card_filter_not _
  refine ⟨retained, hretained, by omega, ?_⟩
  intro g hg F hvanish ht
  exact (Finset.mem_filter.mp hg).2 ⟨F.1, Finset.mem_filter.mpr ⟨F.2, ht⟩, hvanish⟩

end

end ProximityPrize.SubmissionLower.Koala6831Moving
#print axioms ProximityPrize.SubmissionLower.Koala6831Moving.FlowData.left6836_screen_tangent_seeds

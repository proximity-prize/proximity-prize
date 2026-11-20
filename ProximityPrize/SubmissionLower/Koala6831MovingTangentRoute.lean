import ProximityPrize.SubmissionLower.Koala6831MovingSources
import ProximityPrize.SubmissionLower.Koala6831MovingTangentCount

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped Classical BigOperators
open Koala6831MovingSources LocatorLowQuotient

noncomputable section

variable {K I : Type} [Field K] [CharP K TangentList.prime] [Fintype I]

def FlowData.tangentFactors (B : FlowData K) (H : P4 K) : Finset (P4 K) :=
  (RCN167.positiveRFactors H).filter (fun F => F ∣ B.flow F)

theorem FlowData.screen_tangent_seeds
    (B : FlowData K) (H : P4 K) (hH : H ≠ 0)
    (hbox : H ∈ nestedCoefficientBox K Stage.primary.cutoff weight 41882 418 93)
    (Γ : Finset K) (selected normalized : K → Polynomial K)
    (nodes : Finset I) (points received : I → K)
    (hinj : Set.InjOn points nodes) (hnodes : nodes.card = TangentList.n)
    (hd0 : B.d0 ≠ 0) (ha : B.A ≠ 0)
    (hden : ∀ g ∈ Γ, B.seedDenominator g ≠ 0)
    (hselected : ∀ g ∈ Γ, (selected g).natDegree ≤ weight)
    (hnorm : ∀ g ∈ Γ,
      B.d0 * selected g + B.seedOffset g = B.seedDenominator g * normalized g)
    (hdegree : ∀ g ∈ Γ, (normalized g).natDegree ≤ TangentList.w)
    (hagreement : ∀ g ∈ Γ, TangentList.agreements ≤
      (nodes.filter (fun i => (normalized g).eval (points i) = received i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Γ weight 81066) :
    ∃ retained ⊆ Γ, Γ.card ≤ retained.card + tangentSeedBudget ∧
      ∀ g ∈ retained, ∀ F : RCN266.RegularIndex H,
        RCN319.specialization K (selected g) g F.1 = 0 → ¬F.1 ∣ B.flow F.1 := by
  classical
  let factors := B.tangentFactors H
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
  have hcap : H.weightedTotalDegree ![0, 1, 1, 1] < TangentList.prime :=
    hweights.1.trans_lt (by decide +kernel : 41882 < TangentList.prime)
  have hbound : removed.card ≤ tangentSeedBudget :=
    B.tangent_seed_card_le H hH factors hproduct htangent hcap hweights.2.1 hweights.2.2.1
      removed selected normalized nodes points received hinj hnodes hd0 ha
      (fun g hg => hden g (hremoved hg)) (fun g hg => hselected g (hremoved hg))
      (fun g hg => hnorm g (hremoved hg)) (fun g hg => hdegree g (hremoved hg))
      (fun g hg => hagreement g (hremoved hg)) (fun g hg => (Finset.mem_filter.mp hg).2)
      (RCN243.noLargeSelectedPencil_mono selected Γ removed weight 81066 hremoved hno)
  have hsplit : removed.card + retained.card = Γ.card :=
    Finset.card_filter_add_card_filter_not _
  refine ⟨retained, hretained, by omega, ?_⟩
  intro g hg F hvanish ht
  exact (Finset.mem_filter.mp hg).2 ⟨F.1, Finset.mem_filter.mpr ⟨F.2, ht⟩, hvanish⟩

end

end ProximityPrize.SubmissionLower.Koala6831Moving

/- Retuned for the full 68.32 domain and the m=303 primary, November 2026. -/

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/

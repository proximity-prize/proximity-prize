/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the independent full-domain primary proof of Bome2017 after Lucieno (PR 618) and BitWonka. Exact 68.33 constants and physical hypotheses are new. -/
import ProximityPrize.SubmissionLower.Mid6833K6833PrimaryFree
import ProximityPrize.SubmissionLower.Koala6831MovingFoldCount
namespace ProximityPrize.SubmissionLower.Koala6831MovingFoldCount

open scoped Classical BigOperators
open Koala6831Moving Koala6831MovingPairIncidence
open Koala6831OrdinaryIncidence (lengthAverage nodeAverage)
open RCN081 RCN095 RCN130 RCN135 RCN136 RCN137 RCN138 RCN156 RCN167 RCN222 RCN234 RCN243
open RCN238 RCN263 RCN266 RCN267 RCN275 RCN293 RCN319
open LocatorDerivativeChain

noncomputable section

variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

private def primary319FoldSupport : ResidualSupportParameters :=
  ⟨98, 440, 65864, by decide, by decide, by decide, by decide⟩

open Koala6831MovingSources LocatorLowQuotient

theorem primary319_fold_count [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    (hbox : H ∈ nestedCoefficientBox K 57754631 weight 65864 440 98)
    (Γ : Finset K) (selected : K → Polynomial K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (hnodes : nodes.card = 262144)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hagreement : ∀ γ ∈ Γ, 181049 ≤
      (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81095) :
    (foldedSeeds H Γ selected).card ≤ 5660594337602432 := by
  have hweights := nested_mem_weights hbox hH
  have hData : ResidualSupportData primary319FoldSupport H :=
    ⟨hweights.2.2.1, hweights.2.1, hweights.1⟩
  have hAn : 181049 ≤ nodes.card := by rw [hnodes]; decide +kernel
  have h := folded_seed_card_le primary319FoldSupport (by decide +kernel) (by decide +kernel)
    H hH hData 2130706433 selected Γ nodes x u₀ u₁ hx weight 181049 81095
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hAn
    (by decide +kernel) (by decide +kernel) hdegree hagreement hnoPencil
  rw [hnodes] at h
  exact h.trans (by decide +kernel)

theorem primary319_regular_seeds [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    (hbox : H ∈ nestedCoefficientBox K 57754631 weight 65864 440 98)
    (Γ : Finset K) (selected : K → Polynomial K)
    {Node : Type} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (hnodes : nodes.card = 262144)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ H = 0)
    (hagreement : ∀ γ ∈ Γ, 181049 ≤
      (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81095) :
    ∃ Γreg : Finset K, Γreg ⊆ Γ ∧ Γ.card ≤ Γreg.card + 5720374391906461 ∧
      ∀ γ ∈ Γreg, ∃ F : RegularIndex H, specialization K (selected γ) γ F.1 = 0 ∧
        specialization K (selected γ) γ (RCN313.polyH K F.1) ≠ 0 := by
  classical
  let free := Γ.filter fun γ => specialization K (selected γ) γ (freeAndTailCarrier H) = 0
  let fold := foldedSeeds H Γ selected
  let discarded := free ∪ fold
  let regular := Γ \ discarded
  have hfreeSub : free ⊆ Γ := Finset.filter_subset _ _
  have hfoldSub : fold ⊆ Γ := fun γ hγ => (mem_foldedSeeds.mp hγ).1
  have hdiscSub : discarded ⊆ Γ := Finset.union_subset hfreeSub hfoldSub
  have hfree := primary319_free_count H hH hbox free selected nodes x u₀ u₁ hx hnodes
    (fun γ hγ => hdegree γ (hfreeSub hγ)) (fun γ hγ => (Finset.mem_filter.mp hγ).2)
    (fun γ hγ => hagreement γ (hfreeSub hγ))
    (noLargeSelectedPencil_mono selected Γ free weight 81095 hfreeSub hnoPencil)
  have hfold := primary319_fold_count H hH hbox Γ selected nodes x u₀ u₁ hx hnodes
    hdegree hagreement hnoPencil
  have hdisc : discarded.card ≤ 5720374391906461 :=
    (Finset.card_union_le free fold).trans (Nat.add_le_add hfree hfold)
  refine ⟨regular, Finset.sdiff_subset, ?_, ?_⟩
  · have h := Finset.card_sdiff_of_subset hdiscSub
    have hle := Finset.card_le_card hdiscSub
    change regular.card = Γ.card - discarded.card at h
    omega
  · intro γ hγ
    obtain ⟨hΓ, hdis⟩ := Finset.mem_sdiff.mp hγ
    rcases primary_regular_fold_or_free H hH (selected γ) γ (hsolution γ hΓ) with h | ⟨F, hF, h⟩
    · exact (hdis (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hΓ, h⟩))).elim
    · rcases h with h | ⟨hfold, htail⟩
      · exact ⟨F, hF, h⟩
      · exact (hdis (Finset.mem_union_right _ (mem_foldedSeeds.mpr ⟨hΓ, F, hF, hfold, htail⟩))).elim

end

end ProximityPrize.SubmissionLower.Koala6831MovingFoldCount
#print axioms ProximityPrize.SubmissionLower.Koala6831MovingFoldCount.primary319_regular_seeds

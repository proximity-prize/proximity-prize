import ProximityPrize.SubmissionLower.Koala6844TerminalAdaptivePass
import ProximityPrize.SubmissionLower.Koala6831MovingPartition

namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN140 RCN156 RCN167 RCN234 RCN266 RCN286
open LocatorBatchProductRoute LocatorFactorAggregate LocatorLowQuotient
open LocatorPhase6800Oracle (sumFlag_all)
open Koala6831Moving (contactFlag_regularProduct contactFlag_below_of_dvd)
open Koala6831MovingAdaptive (aggregateFlag)
open Koala6844Receipts

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000

variable {K : Type} [Field K]

def phaseSeeds [DecidableEq K] (H : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (seeds : Finset K) (factors : Finset (RegularIndex H)) : Finset K :=
  factors.biUnion (regularSeeds H selected seeds)

theorem phaseSeeds_subset [DecidableEq K] (H : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (seeds : Finset K) (factors : Finset (RegularIndex H)) :
    phaseSeeds H selected seeds factors ⊆ seeds := by
  intro g hg
  obtain ⟨F,_,hF⟩ := Finset.mem_biUnion.mp hg
  exact regularSeeds_subset H selected seeds F hF

theorem phaseSeeds_regular_cover [DecidableEq K] (H : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (seeds : Finset K) (factors : Finset (RegularIndex H)) :
    phaseSeeds H selected seeds factors ⊆
      factors.biUnion (regularSeeds H selected (phaseSeeds H selected seeds factors)) := by
  intro g hg
  obtain ⟨F,hmem,hF⟩ := Finset.mem_biUnion.mp hg
  have hsol : RegularSolution F.1 (selected g) g := (Finset.mem_filter.mp hF).2
  exact Finset.mem_biUnion.mpr ⟨F,hmem,(@Finset.mem_filter _ _ _ _ _).mpr ⟨hg,hsol⟩⟩

theorem phaseSeeds_card_split [DecidableEq K] (H : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (seeds : Finset K) (A B : Finset (RegularIndex H)) :
    (phaseSeeds H selected seeds A).card ≤
      (phaseSeeds H selected seeds (A \ B)).card + (phaseSeeds H selected seeds B).card := by
  have hc : phaseSeeds H selected seeds A ⊆
      phaseSeeds H selected seeds (A \ B) ∪ phaseSeeds H selected seeds B := by
    intro g hg
    obtain ⟨F,hmem,hF⟩ := Finset.mem_biUnion.mp hg
    by_cases h : F ∈ B
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨F,h,hF⟩)
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨F,Finset.mem_sdiff.mpr ⟨hmem,h⟩,hF⟩)
  exact (Finset.card_le_card hc).trans (Finset.card_union_le _ _)

def transverseRegularFactors (H : MvPolynomial (Fin 4) K)
    (D : MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K) : Finset (RegularIndex H) :=
  Finset.univ.filter (fun F => ¬ F.1 ∣ D F.1)

theorem transverseRegularFactors_transverse (H : MvPolynomial (Fin 4) K)
    (D : MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) K) :
    ∀ F ∈ transverseRegularFactors H D, ¬ F.1 ∣ D F.1 :=
  fun _ h => (Finset.mem_filter.mp h).2

theorem short_regular_product_dvd (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    (A : Finset (RegularIndex H)) : regularProduct H A ∣ H := by
  have hp : (∏ F : RegularIndex H, F.1) ∣ H := by
    rw [← Finset.attach_eq_univ]
    change (∏ F ∈ (positiveRFactors H).attach, id F.1) ∣ H
    rw [Finset.prod_attach (positiveRFactors H) id]
    exact positiveRFactors_product_dvd H hH
  exact (Finset.prod_dvd_prod_of_subset A Finset.univ (fun F => F.1) (Finset.subset_univ _)).trans hp

theorem short_regular_card_le_slope (H : MvPolynomial (Fin 4) K) (A : Finset (RegularIndex H)) :
    A.card ≤ (aggregateFlag H A).all := by
  have hs := congrArg FlagDegree.all (contactFlag_regularProduct H A)
  have hh : (aggregateFlag H A).all = ∑ F ∈ A, (originalCumulativeFlag F.1).all :=
    hs.trans (sumFlag_all A (fun F => originalCumulativeFlag F.1))
  calc
    A.card = ∑ _F ∈ A, (1 : Nat) := by simp
    _ ≤ ∑ F ∈ A, (originalCumulativeFlag F.1).all :=
      Finset.sum_le_sum fun F _ => regularCumulativeFlag_positive H F
    _ = _ := hh.symm

theorem short_primary_box_caps (H : MvPolynomial (Fin 4) K) (D : Nat)
    (hbox : H ∈ nestedCoefficientBox K D 131071 42072 829 185) :
    wt residualSWeights H ≤ 185 ∧ wt residualYSWeights H ≤ 829 ∧
      wt residualTotalWeights H ≤ 42072 ∧
      MvPolynomial.weightedTotalDegree (contactWeights 131071) H ≤ D-1 := by
  refine ⟨?_,?_,?_,?_⟩
  · apply (weightedTotalDegree_le_iff _ _ _).mpr
    intro d hd
    have he := (hbox hd).2.2.1
    rw [weight_fin4]
    simpa [residualSWeights] using he
  · apply (weightedTotalDegree_le_iff _ _ _).mpr
    intro d hd
    have he := (hbox hd).2.1
    rw [weight_fin4]
    simpa [residualYSWeights] using he
  · apply (weightedTotalDegree_le_iff _ _ _).mpr
    intro d hd
    have he := (hbox hd).1
    rw [weight_fin4]
    simpa [residualTotalWeights] using he
  · apply (weightedTotalDegree_le_iff _ _ _).mpr
    intro d hd
    rw [contact_weight]
    have he := (hbox hd).2.2.2
    omega

theorem short_primary_fit (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    (A : Finset (RegularIndex H)) (D : Nat)
    (hbox : H ∈ nestedCoefficientBox K D 131071 42072 829 185) :
    Below (aggregateFlag H A) primaryFlag.toFlagDegree := by
  obtain ⟨hr,hy,ht,_⟩ := short_primary_box_caps H D hbox
  have hs : Below (originalCumulativeFlag H) primaryFlag.toFlagDegree := by
    obtain ⟨hr',hy',ht'⟩ := originalCumulativeFlag_cumulative H
    change (originalCumulativeFlag H).all ≤ 185 ∧
      (originalCumulativeFlag H).yz+(originalCumulativeFlag H).all ≤ 829 ∧
      (originalCumulativeFlag H).zOnly+(originalCumulativeFlag H).yz+(originalCumulativeFlag H).all ≤ 42072
    rw [ht',hy',hr']
    exact ⟨hr,hy,ht⟩
  have h := contactFlag_below_of_dvd hH (short_regular_product_dvd H hH A)
  exact ⟨h.1.trans hs.1, h.2.1.trans hs.2.1, h.2.2.trans hs.2.2⟩

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort

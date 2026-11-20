import ProximityPrize.SubmissionLower.Koala6844VirtualShortDirectGerm
import ProximityPrize.SubmissionLower.Koala6844VirtualShortPrimaryCover
import ProximityPrize.SubmissionLower.Koala6844VirtualShortPrimaryFree
import ProximityPrize.SubmissionLower.Koala6844VirtualShortSingular
import ProximityPrize.SubmissionLower.Koala6844VirtualShortTangentCount


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped Classical BigOperators Matrix
open Koala6844Normalization RCN081 RCN082 RCN156 RCN167 RCN234 LocatorDerivativeChain

noncomputable section

set_option maxHeartbeats 2600000

variable {K I : Type} [Field K]

def shortSymbolicBudget : ℕ := 580871082808028

private theorem degree_total_of_support (J : MvPolynomial (Fin 3) K) (t : ℕ)
    (ht : ∀ e ∈ J.support, e 1+e 2 ≤ t) :
    J.weightedTotalDegree ![0,1,1] ≤ t := by
  apply Finset.sup_le
  intro e he
  rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (fun _ => by simp),Fin.sum_univ_three]
  change e 0*0+e 1*1+e 2*1 ≤ t
  simpa using ht e he

theorem card_short_primary_excluded [CharP K 2130706433] [Fintype I]
    [DecidableEq I] [DecidableEq K]
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ 131071 180961 errors excess)
    (support : data.d0.natDegree + affineDegree data.A0 ≤ 6674)
    (H : ShortCarrier K) (hH : H ≠ 0)
    (hr : wt residualSWeights H ≤ 185) (hy : wt residualYSWeights H ≤ 829)
    (ht : wt residualTotalWeights H ≤ 40642)
    (hnodes : nodes.card ≤ 262144) (germ : DirectGermCount data.seeds data.selected) :
    (shortPrimaryExcluded data.seeds data.selected H (centeredFlow data).flow).card ≤
      shortSymbolicBudget := by
  let A := data.seeds
  let selected := data.selected
  let free := shortFactorSeeds A selected (rfreeProduct H)
  let sing := (positiveRFactors H).biUnion (shortSingularSeeds A selected)
  let tangent := tangentFactors H (centeredFlow data).flow
  let tangentSeeds := tangent.biUnion (shortFactorSeeds A selected)
  have hfree : free.card ≤ 40642+2130706433*829 := by
    have div := rfreeProduct_dvd H hH
    obtain ⟨J,hJ,hcap,hspec⟩ := exists_direct_of_slope_degree_zero (rfreeProduct H)
      (rfreeProduct_ne_zero H hH) (rfreeProduct_R_degree H) 829 40642
      ((weightedTotalDegree_le_of_dvd _ _ _ div hH).trans hy)
      ((weightedTotalDegree_le_of_dvd _ _ _ div hH).trans ht)
    have hfreeSub : free ⊆ A := by
      intro g hg
      simp [free, shortFactorSeeds] at hg
      exact hg.1
    apply germ J free hfreeSub hJ 829 40642
      (MvPolynomial.degreeOf_le_iff.mpr fun e he => (hcap e he).1)
      (degree_total_of_support J 40642 fun e he => (hcap e he).2) (by decide)
    intro g hg
    change MvPolynomial.aeval ![Polynomial.X,selected g,Polynomial.C g] J = 0
    rw [hspec]
    simp [free, shortFactorSeeds] at hg
    exact hg.2
  have hsing : sing.card ≤ singularPrice 185 829 40642 := by
    apply card_biUnion_le_short_singular H hH _ _ (positiveRFactors_product_dvd H hH) hr hy ht
    intro F hF
    obtain ⟨hirr,hdvd,hpositive⟩ := positiveRFactors_spec H F hF
    have hrF : F.degreeOf 2 ≤ 185 := by
      rw [← slope_weight_eq_degree]
      exact (weightedTotalDegree_le_of_dvd _ _ _ hdvd hH).trans hr
    have hyF := (weightedTotalDegree_le_of_dvd residualYSWeights F H hdvd hH).trans hy
    have htF := (weightedTotalDegree_le_of_dvd residualTotalWeights F H hdvd hH).trans ht
    obtain ⟨J,hJ,hJy,hJt,hvanish⟩ := singular_germ_cut F hirr hpositive hrF hyF htF
    have small : singularTotal (F.degreeOf 2) (wt residualTotalWeights F) < 2130706433 := by
      change wt residualTotalWeights F ≤ 40642 at htF
      unfold singularTotal
      omega
    have subF : shortSingularSeeds A selected F ⊆ A := by
      intro g hg
      simp [shortSingularSeeds,shortFactorSeeds,and_assoc] at hg
      exact hg.1
    apply germ J (shortSingularSeeds A selected F) subF hJ _ _ hJy hJt small
    intro g hg
    simp [shortSingularSeeds,shortFactorSeeds,and_assoc] at hg
    exact hvanish _ _ hg.2.1 hg.2.2
  have htan : tangentSeeds.card ≤ TangentList.listBudget := by
    have sub : tangent ⊆ positiveRFactors H := Finset.filter_subset _ _
    have prodDiv : (∏ F ∈ tangent, F) ∣ H :=
      (Finset.prod_dvd_prod_of_subset _ _ id sub).trans (positiveRFactors_product_dvd H hH)
    have tan : ∀ F ∈ tangent, F ∣ (centeredFlow data).flow F :=
      fun F hF => (Finset.mem_filter.mp hF).2
    have amin : tangentSeeds ⊆ A := by
      intro g hg
      obtain ⟨F,_,hF⟩ := Finset.mem_biUnion.mp hg
      simp [shortFactorSeeds] at hF
      exact hF.1
    apply centered_tangent_seed_count data support H hH tangent prodDiv tan
      (ht.trans_lt (by decide)) hy hr tangentSeeds amin hnodes
    intro g hg
    obtain ⟨F,hF,hh⟩ := Finset.mem_biUnion.mp hg
    simp [shortFactorSeeds] at hh
    exact ⟨F,hF,hh.2⟩
  have coverEq : shortPrimaryExcluded data.seeds data.selected H (centeredFlow data).flow =
      free ∪ sing ∪ tangentSeeds := by
    ext g
    simp [shortPrimaryExcluded,free,sing,tangentSeeds,tangent,A,selected]
  rw [coverEq]
  calc
    _ ≤ free.card+sing.card+tangentSeeds.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ (40642+2130706433*829)+singularPrice 185 829 40642+TangentList.listBudget :=
      Nat.add_le_add (Nat.add_le_add hfree hsing) htan
    _ = _ := by norm_num [singularPrice, singularTotal, singularMiddle, TangentList.listBudget,
      shortSymbolicBudget]

theorem centered_direct_germ_count [DecidableEq I] [DecidableEq K]
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w agreement errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ w agreement errors excess)
    (hσ : ∀ g ∈ data.seeds, σ g = g^2130706433) :
    DirectGermCount data.seeds data.selected := by
  let embed : K →+* AlgebraicClosure K := algebraMap _ _
  obtain ⟨germ⟩ := exists_active_resultant_germ data embed
  intro J A hA hJ y t hy ht hd hz
  exact direct_germ_card_le data embed germ 2130706433 y t hd
    (fun g hg => by rw [hσ g hg,map_pow]) J hJ hy ht A hA hz

theorem centered_short_primary_cover_and_budget [CharP K 2130706433] [Fintype I]
    [DecidableEq I] [DecidableEq K]
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ 131071 180961 errors excess)
    (hσ : ∀ g ∈ data.seeds, σ g = g^2130706433)
    (support : data.d0.natDegree + affineDegree data.A0 ≤ 6674)
    (H : ShortCarrier K) (hH : H ≠ 0)
    (hr : wt residualSWeights H ≤ 185) (hy : wt residualYSWeights H ≤ 829)
    (ht : wt residualTotalWeights H ≤ 40642)
    (hnodes : nodes.card ≤ 262144)
    (hzero : ∀ g ∈ data.seeds, RCN319.specialization K (data.selected g) g H = 0) :
    data.seeds ⊆ shortPrimaryExcluded data.seeds data.selected H (centeredFlow data).flow ∪
      (transverseFactors H (centeredFlow data).flow).biUnion (shortRegularSeeds data.seeds data.selected) ∧
    (shortPrimaryExcluded data.seeds data.selected H (centeredFlow data).flow).card ≤
      shortSymbolicBudget := by
  refine ⟨?_, card_short_primary_excluded data support H hH hr hy ht hnodes
    (centered_direct_germ_count data hσ)⟩
  intro g hg
  simpa only [Finset.mem_union,Finset.mem_biUnion] using
    short_primary_regular_cover H hH data.seeds data.selected (centeredFlow data).flow hzero hg

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort

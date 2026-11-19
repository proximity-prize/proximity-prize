/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Retuned from the frozen 68.32 submission of Bome2017, building on Lucieno
(PR 618) and BitWonka (PRs 581 and 582). KoalaBear 68.33 long branch, November 18. -/
/- Adapted from Lucieno, Proximity Prize PR 618, commit dbaea1b59ca9d7311bc98b5fb6d18eb9e1b7603a. Changes for 81,66 errors, right cap 167 and sharper persistent-curve charge. Research pilot. -/
import ProximityPrize.SubmissionLower.Koala6831BenchmarkResidual
import ProximityPrize.SubmissionLower.Mid6833K6833SepLongFactorCount
import ProximityPrize.SubmissionLower.Mid6833K6833SepLongPersistentSurface

namespace ProximityPrize.SubmissionLower.K6833FactorCount
open Koala6831Intrinsic

open Koala6831BenchmarkPrimitive Koala6831BenchmarkRetention Koala6831BenchmarkResidual
open Koala6831OrdinaryIncidence RCN135 RCN136 RCN137
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4200000

variable {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]

theorem count_81076_long_factors_6833
    (x : I ↪ K) (hcard : Fintype.card I = 262144) (hp : Nat.Prime 2130706433)
    (Q : Carrier K) (hQ : Q ≠ 0)
    (hc : ∀ d ∈ Q.support, d 1 ≤ 22 ∧ d 1 + d 2 ≤ 198 ∧ d 3 ≤ 167 ∧ d 0 + 131071 * d 1 < 4000000)
    (seeds : Finset K) (selected : K → Polynomial K) (u₀ u₁ : I → K)
    (hvan : ∀ g ∈ seeds, graphSpecialize (selected g) g (g ^ 2130706433) Q = 0)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hagree : ∀ g ∈ seeds, 181049 ≤ ((Finset.univ : Finset I).filter
      (fun i => (selected g).eval (x i) = u₀ i + g * u₁ i)).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ 131071 → P₁.natDegree ≤ 131071 →
      (RCN050.pencilSeeds seeds selected P₀ P₁).card ≤ 81096) :
    seeds.card ≤ 274584755586524048 := by
  let nodes := (Finset.univ : Finset I)
  have hn : nodes.card = 262144 := Finset.card_univ.trans hcard
  have hAn : 181049 ≤ nodes.card := hn.symm ▸ (by decide)
  have haverage : nodeAverage nodes.card 131071 181049 ≤ 3 := by
    rw [hn]
    norm_num [nodeAverage]
  apply long_retained_seed_budget_of_factor_counts_lp32 Q hQ
    (fun d hd => ⟨(hc d hd).1, (hc d hd).2.1, (hc d hd).2.2.1⟩) seeds selected hvan
  intro F hF G hG
  obtain ⟨hiF, _⟩ := normalizedFactorSet_spec Q F hF
  obtain ⟨hiG, hdiv⟩ := surfaceFactors_spec (polynomialEmbedding K) F G hG
  obtain ⟨hy, ht, hz, hcode⟩ := long_native_factor_caps_lp32 Q F hQ hF hc
  obtain ⟨hGy, hGt, hGz, hyt, hmid⟩ := long_geometric_factor_caps_lp32 F hiF.ne_zero G hdiv hy ht hz
  by_cases hfirst : G ∣ surfaceMap (polynomialEmbedding K) (tailNumerator F 131071)
  · let part := longFactorSeeds_lp32 F G seeds selected
    have hs : part ⊆ seeds := Finset.filter_subset _ _
    have hgeom := long_persistent_surface_selected_count_lp32 F hiF hcode
      (fun d hd => (long_native_seed_support_lp32 F ht hz d hd).1)
      (fun d hd => (long_native_seed_support_lp32 F ht hz d hd).2)
      G hiG hdiv hfirst hGy hGz x (u₀) (u₁) nodes hAn haverage
      part seeds hs selected (fun g hg => hdegree g (hs hg))
      (fun g hg => (Finset.mem_filter.mp hg).2.2.1)
      (fun g hg => (Finset.mem_filter.mp hg).2.2.2)
      (fun g hg => (Finset.mem_filter.mp hg).2.1)
      (fun g hg => hagree g (hs hg)) hpencil
    exact hgeom.trans (by rw [longFactorCharge_eq_lp32 _ _ _ hyt]; exact Nat.le_add_left _ _)
  · exact long_proper_first_tail_factor_count_lp32 F hp hiF hy ht hz G hiG hdiv hfirst
      (G.degreeOf 0) (longMiddleDegree_lp32 G) (G.degreeOf 2) hyt hGy hGt hGz le_rfl hmid le_rfl
      4000000 81095 (by decide) (by decide) le_rfl hcode
      x (u₀) (u₁) nodes hAn haverage seeds selected
      hdegree hagree hpencil


#print axioms count_81076_long_factors_6833
end
end ProximityPrize.SubmissionLower.K6833FactorCount

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/

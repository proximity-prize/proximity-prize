import ProximityPrize.SubmissionLower.Koala6844VirtualHighMappedResidual
import ProximityPrize.SubmissionLower.Koala6844VirtualHighPersistentResidual
import ProximityPrize.SubmissionLower.Koala6844VirtualHighCenteredTrim
import ProximityPrize.SubmissionLower.Koala6844VirtualHighInvariantSurfaceTrimmed


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical
open Polynomial Koala6831Intrinsic Koala6831OrdinaryIncidence Koala6844Normalization RCN135 RCN136 RCN137

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {K E I : Type} [Field K] [Field E] [DecidableEq K] [DecidableEq I]
variable {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
variable {w agreement errors excess : ℕ}

theorem mapped_regular_proper_carrier_count
    (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (p first plain J bound : ℕ) [CharP E p] (hp : p.Prime)
    (hσ : ∀ g ∈ D.seeds, embed (σ g) = (embed g)^p)
    (A : Finset K) (hA : A ⊆ D.seeds)
    (trimData : CenteredTrimCarrier D first plain)
    (F : Carrier E) (hF : Irreducible F)
    (hFpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3)
    (properOriginal : ¬ F ∣ rawTrimmedTail F
      (MvPolynomial.map embed trimData.V) (MvPolynomial.map embed trimData.W) first)
    (f : Rectangle) (hy : 1 ≤ f.value) (hfirst : first+1 ≤ J) (hJ : 2 ≤ J)
    (hFcap : F.degreeOf 1 ≤ f.value ∧ F.degreeOf 2 ≤ f.first ∧ F.degreeOf 3 ≤ f.second)
    (hbound : 2 ≤ bound) (hplain : plain+1 ≤ bound) (hchar : bound < p)
    (hweight : RCN234.wt (![1,plain,0,0] : Fin 4 → ℕ) F < bound)
    (hselected : w + D.d0.natDegree - affineDegree D.A0 ≤ plain)
    (hgap : plain < agreement) (haverage : nodeAverage nodes.card plain agreement ≤ 4) :
    (regularSurfaceSeeds embed p D.normalized A F).card ≤
      mixedDegree f (tailRectangle J f) (tailRectangle (J+1) f) := by
  classical
  let B := regularSurfaceSeeds embed p D.normalized A F
  have sub : B ⊆ D.seeds := (regularSurfaceSeeds_subset embed p D.normalized A F).trans hA
  obtain ⟨hcard, hdegree, hinj, hagree⟩ := mapped_normalized_family D embed B sub
  rw [← hcard]
  let V := MvPolynomial.map embed trimData.V
  let W := MvPolynomial.map embed trimData.W
  let data := trimData.invariant.map embed
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP (GenericField E) p := genericField_charP E p
  letI : ExpChar (GenericField E) p := .prime hp
  letI : PerfectRing (GenericField E) p := inferInstance
  have hAn : agreement ≤ nodes.card :=
    (D.normalized_agreements 0 D.zero_mem).trans (Finset.card_filter_le _ _)
  have hV : V.degreeOf 1 ≤ 0 ∧ V.degreeOf 2 ≤ 0 ∧ V.degreeOf 3 ≤ 0 :=
    ⟨(degreeOf_coefficient_map_le embed _ 1).trans trimData.divisor_caps.1,
     (degreeOf_coefficient_map_le embed _ 2).trans trimData.divisor_caps.2.1,
     (degreeOf_coefficient_map_le embed _ 3).trans trimData.divisor_caps.2.2⟩
  have hW : W.degreeOf 1 ≤ 1 ∧ W.degreeOf 2 ≤ 10000 ∧ W.degreeOf 3 ≤ 10000 :=
    ⟨(degreeOf_coefficient_map_le embed _ 1).trans trimData.trim_caps.1,
     (degreeOf_coefficient_map_le embed _ 2).trans trimData.trim_caps.2.1,
     (degreeOf_coefficient_map_le embed _ 3).trans trimData.trim_caps.2.2⟩
  have graph := mapped_regular_trimmed_graphs D embed p first A hA hσ F trimData.V trimData.W
    trimData.reduced trimData.scale (fun g _ => trimData.divisor_spec g) trimData.trim_spec
    trimData.reduced_degree
  have denom := mapped_graph_nonzero_of_original D embed p B sub hσ trimData.invariant.denominator
    (fun g hg => by
      rw [trimData.denom_spec g hg]
      exact Polynomial.C_ne_zero.mpr (trimData.scale_ne g hg))
  exact selected_trimmed_proper_carrier_count F V W first plain J bound p hp data hF hFpos
    properOriginal f hy hfirst hJ hFcap hV hW hbound hplain hchar hweight
    (mappedNodes embed x) (embed ∘ D.fixedWord) nodes agreement hgap hAn haverage
    (B.image embed) (mappedPolynomialFamily embed D.normalized)
    (mappedPolynomialFamily embed trimData.reduced) (mappedScalarFamily embed trimData.scale)
    (fun g hg => (graph g hg).1) (fun g hg => (graph g hg).2.1) denom
    (fun g hg => (graph g hg).2.2.1) (fun g hg => (graph g hg).2.2.2)
    (fun g hg => (hdegree g hg).trans hselected) hagree hinj

theorem mapped_regular_whole_carrier_count
    (D : CenteredVirtualData x nodes σ w agreement errors excess)
    (embed : K →+* E) (p first plain bound : ℕ) [CharP E p]
    (hσ : ∀ g ∈ D.seeds, embed (σ g) = (embed g)^p)
    (A : Finset K) (hA : A ⊆ D.seeds)
    (trimData : CenteredTrimCarrier D first plain)
    (F : Carrier E) (hF : Irreducible F)
    (whole : F ∣ rawTrimmedTail F
      (MvPolynomial.map embed trimData.V) (MvPolynomial.map embed trimData.W) first)
    (f : Rectangle) (hy : f.value < p) (hz : f.second < p)
    (hFcap : F.degreeOf 1 ≤ f.value ∧ F.degreeOf 2 ≤ f.first ∧ F.degreeOf 3 ≤ f.second)
    (hbound : 2 ≤ bound) (hplain : plain+1 ≤ bound) (hchar : bound < p)
    (hweight : RCN234.wt (![1,plain,0,0] : Fin 4 → ℕ) F < bound)
    (hselected : w + D.d0.natDegree - affineDegree D.A0 ≤ plain)
    (hgap : plain < agreement) (haverage : nodeAverage nodes.card plain agreement ≤ 4) :
    (regularSurfaceSeeds embed p D.normalized A F).card ≤
      (4*(f.first+1+p*f.second)+1) * F.degreeOf 1 := by
  classical
  let B := regularSurfaceSeeds embed p D.normalized A F
  have sub : B ⊆ D.seeds := (regularSurfaceSeeds_subset embed p D.normalized A F).trans hA
  obtain ⟨hcard, hdegree, hinj, hagree⟩ := mapped_normalized_family D embed B sub
  rw [← hcard]
  let V := MvPolynomial.map embed trimData.V
  let W := MvPolynomial.map embed trimData.W
  let data := trimData.invariant.map embed
  letI : CharP (GenericField E) p := genericField_charP E p
  have hAn : agreement ≤ nodes.card :=
    (D.normalized_agreements 0 D.zero_mem).trans (Finset.card_filter_le _ _)
  have graph := mapped_regular_trimmed_graphs D embed p first A hA hσ F trimData.V trimData.W
    trimData.reduced trimData.scale (fun g _ => trimData.divisor_spec g) trimData.trim_spec
    trimData.reduced_degree
  have denom := mapped_graph_nonzero_of_original D embed p B sub hσ trimData.invariant.denominator
    (fun g hg => by
      rw [trimData.denom_spec g hg]
      exact Polynomial.C_ne_zero.mpr (trimData.scale_ne g hg))
  let selected := mappedPolynomialFamily embed D.normalized
  refine selected_carrier_invariant_count_of_geometric_factors F hF.ne_zero p
    (B.image embed) selected (fun g hg => (graph g hg).1) _ ?_
  intro G hG
  obtain ⟨irr, dvd⟩ := surfaceFactors_spec (polynomialEmbedding E) F G hG
  have hdegreeGeo (i : Fin 3) : G.degreeOf i ≤ F.degreeOf i.succ :=
    (coordinate_degree_le_of_dvd i G _ dvd (surfaceMap_ne_zero _
      (polynomialEmbedding_injective E) F hF.ne_zero)).trans (surfaceMap_degreeOf_le _ F i)
  have hyp : G.degreeOf 0 < p := ((hdegreeGeo 0).trans hFcap.1).trans_lt hy
  have hzp : G.degreeOf 2 < p := ((hdegreeGeo 2).trans hFcap.2.2).trans_lt hz
  let S := geometricFactorSeeds (B.image embed) selected p G
  have hsub : S ⊆ B.image embed := Finset.filter_subset _ _
  exact persistent_trimmed_geometric_factor_bound F V W first plain bound p f.first f.second
    data G irr dvd hyp hzp whole hbound hplain hchar hweight
    (fun d hd => (MvPolynomial.monomial_le_degreeOf 2 hd).trans hFcap.2.1)
    (fun d hd => (MvPolynomial.monomial_le_degreeOf 3 hd).trans hFcap.2.2)
    (mappedNodes embed x) (embed ∘ D.fixedWord) nodes agreement hgap hAn haverage S selected
    (fun g hg => (hdegree g (hsub hg)).trans hselected)
    (fun g hg => (graph g (hsub hg)).1) (fun g hg => (Finset.mem_filter.mp hg).2)
    (fun g hg => (graph g (hsub hg)).2.1) (fun g hg => denom g (hsub hg))
    (fun g hg => hagree g (hsub hg)) (hinj.mono hsub)


end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh



import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactCumulativeWeightedDegreeResearch
import ProximityPrize.SubmissionLower.ContactOriginalRegularResidualStage6600Research
import ProximityPrize.SubmissionLower.ContactFlagTriangularProjectionResearch

/-! .
 -/

namespace ProximityPrize.SubmissionLower.ContactGCDCumulativeFlagsResearch

open scoped Classical BigOperators
open ContactFactorCaps ContactGenericSurface ContactGenericInitialPoint
open ContactGeometricFactorCover ContactOriginalRegularSeedCount
open ContactRegularFactorFlag6600Research ContactImplicitContactLift
open ContactIdentityResidualGlobalFlagResearch ContactFlagBezout6543Research
open ContactFlagTriangularProjectionResearch (sWeight ysWeight totalWeight)
open ContactCumulativeWeightedDegreeResearch ContactPost6464MinkowskiRecurrenceResearch
open ContactResidualSupportParametersResearch ContactIdentityResidualIterationResearch

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

variable {K L : Type} [Field K] [Field L]

def flagFromCaps (total middle inner : ℕ) : FlagDegree :=
  ⟨total - middle, middle - inner, inner⟩

theorem flagFromCaps_cumulative (total middle inner : ℕ)
    (hi : inner ≤ middle) (hm : middle ≤ total) :
    (flagFromCaps total middle inner).all = inner ∧
      (flagFromCaps total middle inner).yz +
        (flagFromCaps total middle inner).all = middle ∧
      (flagFromCaps total middle inner).zOnly +
        (flagFromCaps total middle inner).yz +
        (flagFromCaps total middle inner).all = total := by
  dsimp [flagFromCaps]
  omega

theorem residual_weight_nested (F : MvPolynomial (Fin 4) K) :
    wt residualSWeights F ≤ wt residualYSWeights F ∧
      wt residualYSWeights F ≤ wt residualTotalWeights F := by
  constructor
  · apply (weightedTotalDegree_le_iff residualSWeights F _).mpr
    intro d hd
    have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
    rw [weight_fin4] at h ⊢
    simp [wt, residualSWeights, residualYSWeights] at h ⊢
    omega
  · apply (weightedTotalDegree_le_iff residualYSWeights F _).mpr
    intro d hd
    have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
    rw [weight_fin4] at h ⊢
    simp [wt, residualYSWeights, residualTotalWeights] at h ⊢
    omega

theorem surface_weight_nested (G : MvPolynomial (Fin 3) L) :
    MvPolynomial.weightedTotalDegree sWeight G ≤
        MvPolynomial.weightedTotalDegree ysWeight G ∧
      MvPolynomial.weightedTotalDegree ysWeight G ≤
        MvPolynomial.weightedTotalDegree totalWeight G := by
  constructor
  · unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro d hd
    exact (show Finsupp.weight sWeight d ≤ Finsupp.weight ysWeight d by
      rw [TrivariateShearResearch.weight_fin3, TrivariateShearResearch.weight_fin3]
      simp [sWeight, ysWeight]).trans (Finset.le_sup hd)
  · unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro d hd
    exact (show Finsupp.weight ysWeight d ≤ Finsupp.weight totalWeight d by
      rw [TrivariateShearResearch.weight_fin3, TrivariateShearResearch.weight_fin3]
      simp [ysWeight, totalWeight]).trans (Finset.le_sup hd)

def originalCumulativeFlag (F : MvPolynomial (Fin 4) K) : FlagDegree :=
  flagFromCaps (wt residualTotalWeights F) (wt residualYSWeights F)
    (wt residualSWeights F)

def surfaceCumulativeFlag (G : MvPolynomial (Fin 3) L) : FlagDegree :=
  flagFromCaps (MvPolynomial.weightedTotalDegree totalWeight G)
    (MvPolynomial.weightedTotalDegree ysWeight G)
    (MvPolynomial.weightedTotalDegree sWeight G)

abbrev regularCumulativeFlag (Q : MvPolynomial (Fin 4) K) (R : RegularIndex Q) :=
  originalCumulativeFlag R.1

abbrev geometricCumulativeFlag (K : Type) [Field K]
    {F : MvPolynomial (Fin 4) K} (g : GeometricFactor K F) :=
  surfaceCumulativeFlag g.1

def supportCumulativeFlag (P : ResidualSupportParameters) : FlagDegree :=
  flagFromCaps P.total P.ys P.s

theorem originalCumulativeFlag_cumulative (F : MvPolynomial (Fin 4) K) :
    (originalCumulativeFlag F).all = wt residualSWeights F ∧
      (originalCumulativeFlag F).yz + (originalCumulativeFlag F).all =
        wt residualYSWeights F ∧
      (originalCumulativeFlag F).zOnly + (originalCumulativeFlag F).yz +
        (originalCumulativeFlag F).all = wt residualTotalWeights F :=
  flagFromCaps_cumulative _ _ _ (residual_weight_nested F).1
    (residual_weight_nested F).2

theorem surfaceCumulativeFlag_cumulative (G : MvPolynomial (Fin 3) L) :
    (surfaceCumulativeFlag G).all = MvPolynomial.weightedTotalDegree sWeight G ∧
      (surfaceCumulativeFlag G).yz + (surfaceCumulativeFlag G).all =
        MvPolynomial.weightedTotalDegree ysWeight G ∧
      (surfaceCumulativeFlag G).zOnly + (surfaceCumulativeFlag G).yz +
        (surfaceCumulativeFlag G).all = MvPolynomial.weightedTotalDegree totalWeight G :=
  flagFromCaps_cumulative _ _ _ (surface_weight_nested G).1
    (surface_weight_nested G).2

theorem polynomialIn_surfaceCumulativeFlag (G : MvPolynomial (Fin 3) L) :
    PolynomialInFlag (surfaceCumulativeFlag G) G := by
  intro d hd
  have hs := MvPolynomial.le_weightedTotalDegree sWeight hd
  have hm := MvPolynomial.le_weightedTotalDegree ysWeight hd
  have ht := MvPolynomial.le_weightedTotalDegree totalWeight hd
  rw [TrivariateShearResearch.weight_fin3] at hs hm ht
  simp [sWeight, ysWeight, totalWeight] at hs hm ht
  have hc := surfaceCumulativeFlag_cumulative G
  change d 1 ≤ (surfaceCumulativeFlag G).all ∧
    d 0 + d 1 ≤ (surfaceCumulativeFlag G).yz + (surfaceCumulativeFlag G).all ∧
    d 0 + d 1 + d 2 ≤ (surfaceCumulativeFlag G).zOnly +
      (surfaceCumulativeFlag G).yz + (surfaceCumulativeFlag G).all
  rw [hc.2.2, hc.2.1, hc.1]
  exact ⟨hs, hm, ht⟩

theorem surfaceMap_nested_weights_le (phi : Polynomial K →+* L)
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.weightedTotalDegree sWeight (surfaceMap phi F) ≤
        wt residualSWeights F ∧
      MvPolynomial.weightedTotalDegree ysWeight (surfaceMap phi F) ≤
        wt residualYSWeights F ∧
      MvPolynomial.weightedTotalDegree totalWeight (surfaceMap phi F) ≤
        wt residualTotalWeights F := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_surfaceMap_subset phi F he)
    rw [TrivariateShearResearch.weight_fin3]
  · have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
    rw [weight_fin4] at h
    simpa [wt, sWeight, residualSWeights, Finsupp.tail_apply] using h
  · have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
    rw [weight_fin4] at h
    simpa [wt, ysWeight, residualYSWeights, Finsupp.tail_apply] using h
  · have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
    rw [weight_fin4] at h
    simpa [wt, totalWeight, residualTotalWeights, Finsupp.tail_apply] using h

theorem surfaceMap_in_originalCumulativeFlag (phi : Polynomial K →+* L)
    (F : MvPolynomial (Fin 4) K) :
    PolynomialInFlag (originalCumulativeFlag F) (surfaceMap phi F) := by
  have hm := surfaceMap_nested_weights_le phi F
  have hc := originalCumulativeFlag_cumulative F
  apply (support_subset_flagSupport_iff _ _).mp
  apply support_subset_flagSupport_of_weighted_degrees
  · rw [hc.1]; exact hm.1
  · rw [hc.2.1]; exact hm.2.1
  · rw [hc.2.2]; exact hm.2.2

/-- . -/
theorem regularCumulativeFlag_budgets
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {P : ResidualSupportParameters} (H : ResidualSupportData P Q) :
    (∑ R : RegularIndex Q, (regularCumulativeFlag Q R).all) ≤ P.s ∧
      (∑ R : RegularIndex Q, ((regularCumulativeFlag Q R).yz +
        (regularCumulativeFlag Q R).all)) ≤ P.ys ∧
      (∑ R : RegularIndex Q, ((regularCumulativeFlag Q R).zOnly +
        (regularCumulativeFlag Q R).yz + (regularCumulativeFlag Q R).all)) ≤ P.total := by
  have hp := positiveRFactors_product_dvd Q hQ
  have hs := sum_weightedTotalDegree_le_of_prod_dvd residualSWeights
    (positiveRFactors Q) id Q hQ hp
  have hm := sum_weightedTotalDegree_le_of_prod_dvd residualYSWeights
    (positiveRFactors Q) id Q hQ hp
  have ht := sum_weightedTotalDegree_le_of_prod_dvd residualTotalWeights
    (positiveRFactors Q) id Q hQ hp
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_congr rfl (fun R _ ↦ (originalCumulativeFlag_cumulative R.1).1),
      Finset.sum_coe_sort]
    exact hs.trans H.s_weight
  · rw [Finset.sum_congr rfl (fun R _ ↦ (originalCumulativeFlag_cumulative R.1).2.1),
      Finset.sum_coe_sort]
    exact hm.trans H.ys_weight
  · rw [Finset.sum_congr rfl (fun R _ ↦ (originalCumulativeFlag_cumulative R.1).2.2),
      Finset.sum_coe_sort]
    exact ht.trans H.total_weight

/-- . -/
theorem geometricCumulativeFlag_budgets (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) :
    (∑ g : GeometricFactor K F, (geometricCumulativeFlag K g).all) ≤
        (originalCumulativeFlag F).all ∧
      (∑ g : GeometricFactor K F, ((geometricCumulativeFlag K g).yz +
        (geometricCumulativeFlag K g).all)) ≤
        (originalCumulativeFlag F).yz + (originalCumulativeFlag F).all ∧
      (∑ g : GeometricFactor K F, ((geometricCumulativeFlag K g).zOnly +
        (geometricCumulativeFlag K g).yz + (geometricCumulativeFlag K g).all)) ≤
        (originalCumulativeFlag F).zOnly + (originalCumulativeFlag F).yz +
          (originalCumulativeFlag F).all := by
  let phi := polynomialEmbedding K
  have hSF := surfaceMap_ne_zero phi (polynomialEmbedding_injective K) F hF
  have hp := normalizedFactorSet_product_dvd (surfaceMap phi F) hSF
  have hs := sum_weightedTotalDegree_le_of_prod_dvd_fin3 sWeight
    (surfaceFactors phi F) id (surfaceMap phi F) hSF hp
  have hm := sum_weightedTotalDegree_le_of_prod_dvd_fin3 ysWeight
    (surfaceFactors phi F) id (surfaceMap phi F) hSF hp
  have ht := sum_weightedTotalDegree_le_of_prod_dvd_fin3 totalWeight
    (surfaceFactors phi F) id (surfaceMap phi F) hSF hp
  have hmap := surfaceMap_nested_weights_le phi F
  have hc := originalCumulativeFlag_cumulative F
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_congr rfl (fun g _ ↦ (surfaceCumulativeFlag_cumulative g.1).1),
      Finset.sum_coe_sort, hc.1]
    exact hs.trans hmap.1
  · rw [Finset.sum_congr rfl (fun g _ ↦ (surfaceCumulativeFlag_cumulative g.1).2.1),
      Finset.sum_coe_sort, hc.2.1]
    exact hm.trans hmap.2.1
  · rw [Finset.sum_congr rfl (fun g _ ↦ (surfaceCumulativeFlag_cumulative g.1).2.2),
      Finset.sum_coe_sort, hc.2.2]
    exact ht.trans hmap.2.2

theorem geometricCumulativeFlag_le_support
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    {P : ResidualSupportParameters} (H : ResidualSupportData P F)
    (g : GeometricFactor K F) :
    (geometricCumulativeFlag K g).all ≤ P.s ∧
      (geometricCumulativeFlag K g).yz + (geometricCumulativeFlag K g).all ≤ P.ys ∧
      (geometricCumulativeFlag K g).zOnly + (geometricCumulativeFlag K g).yz +
        (geometricCumulativeFlag K g).all ≤ P.total := by
  have hb := geometricCumulativeFlag_budgets F hF
  have hc := originalCumulativeFlag_cumulative F
  rw [hc.2.2, hc.2.1, hc.1] at hb
  refine ⟨?_, ?_, ?_⟩
  · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ g)).trans (hb.1.trans H.s_weight)
  · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ g)).trans (hb.2.1.trans H.ys_weight)
  · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ g)).trans (hb.2.2.trans H.total_weight)

theorem originalCumulativeFlag_all (F : MvPolynomial (Fin 4) K) :
    (originalCumulativeFlag F).all = F.degreeOf 2 := by
  change MvPolynomial.weightedTotalDegree residualSWeights F = _
  have hw : residualSWeights = Pi.single (2 : Fin 4) 1 := by
    funext i
    fin_cases i <;> simp [residualSWeights]
  rw [hw, MvPolynomial.weightedTotalDegree_piSingle]

theorem regularCumulativeFlag_positive
    (Q : MvPolynomial (Fin 4) K) (R : RegularIndex Q) :
    0 < (regularCumulativeFlag Q R).all := by
  rw [originalCumulativeFlag_all]
  exact (positiveRFactors_spec Q R.1 R.2).2.2

theorem surfaceCumulativeFlag_all (G : MvPolynomial (Fin 3) L) :
    (surfaceCumulativeFlag G).all = G.degreeOf 1 := by
  change MvPolynomial.weightedTotalDegree sWeight G = _
  have hw : sWeight = Pi.single (1 : Fin 3) 1 := by
    funext i
    fin_cases i <;> simp [sWeight]
  rw [hw, MvPolynomial.weightedTotalDegree_piSingle]

/-- .
 -/
def reflagResidualStage {Iota : Type} {phi : Polynomial K →+* L}
    {Gamma : Finset K} {x : Iota → K} {p e d : ℕ} [CharP L p]
    {oldFlag newFlag : FlagDegree} {support : ResidualSupportParameters}
    (S : ResidualStage phi Gamma x p e oldFlag d support)
    (hflag : PolynomialInFlag newFlag S.G) :
    ResidualStage phi Gamma x p e newFlag d support :=
  { S with flag_support := hflag }

end
end ProximityPrize.SubmissionLower.ContactGCDCumulativeFlagsResearch

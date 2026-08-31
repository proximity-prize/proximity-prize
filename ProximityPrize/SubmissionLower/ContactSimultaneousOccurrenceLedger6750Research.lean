import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSimultaneousFactorMultiplicity6750Research
import ProximityPrize.SubmissionLower.ContactGCDCumulativeFlagsResearch
import ProximityPrize.SubmissionLower.ContactFactoredFlagCount6676Research

 








namespace ProximityPrize.SubmissionLower.ContactSimultaneousOccurrenceLedger6750Research

open scoped Classical BigOperators
open UniqueFactorizationMonoid
open ContactTranslation ContactSelectedSeedDecomposition
open ContactSimultaneousFactorMultiplicity6750Research
open ContactCumulativeWeightedDegreeResearch
open ContactGCDCumulativeFlagsResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactFactoredFlagCount6676Research ContactFlagBezout6543Research
open ContactResidualSupportParametersResearch

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

 

abbrev NormalizedOccurrence (Q : MvPolynomial (Fin 4) K) := normalizedFactors Q

def occurrenceFactor (Q : MvPolynomial (Fin 4) K)
    (R : NormalizedOccurrence Q) : MvPolynomial (Fin 4) K := R

theorem occurrenceFactor_mem (Q : MvPolynomial (Fin 4) K)
    (R : NormalizedOccurrence Q) : occurrenceFactor Q R ∈ normalizedFactors Q := by
  exact Multiset.coe_mem

theorem occurrenceFactor_irreducible (Q : MvPolynomial (Fin 4) K)
    (R : NormalizedOccurrence Q) : Irreducible (occurrenceFactor Q R) :=
  irreducible_of_normalized_factor _ (occurrenceFactor_mem Q R)

def occurrenceRegularSeeds
    (Q : MvPolynomial (Fin 4) K) (selected : K -> Polynomial K)
    (Gamma : Finset K) (R : NormalizedOccurrence Q) : Finset K := by
  classical
  exact Gamma.filter
    (fun gamma => RegularSolution (occurrenceFactor Q R) (selected gamma) gamma)

theorem occurrenceRegularSeeds_subset
    (Q : MvPolynomial (Fin 4) K) (selected : K -> Polynomial K)
    (Gamma : Finset K) (R : NormalizedOccurrence Q) :
    occurrenceRegularSeeds Q selected Gamma R ⊆ Gamma := by
  classical
  exact Finset.filter_subset _ _

 

theorem pointwise_two_occurrence_cover
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (gamma : K) (hgamma : gamma ∈ Gamma)
    (hQzero : specialization K (selected gamma) gamma Q = 0)
    (hQderiv : specialization K (selected gamma) gamma
      (MvPolynomial.pderiv (2 : Fin 4) Q) = 0)
    (haux : specialization K (selected gamma) gamma
      (ContactSingularAuxiliary.singularAuxiliary Q) ≠ 0) :
    2 <= ((Finset.univ : Finset (NormalizedOccurrence Q)).filter
      (fun R => gamma ∈ occurrenceRegularSeeds Q selected Gamma R)).card := by
  classical
  have htwo := two_regular_normalized_factor_occurrences Q hQ
    (selected gamma) gamma hQzero hQderiv haux
  have hfiber :
      (Finset.univ : Finset (NormalizedOccurrence Q)).filter
          (fun R => gamma ∈ occurrenceRegularSeeds Q selected Gamma R) =
        (Finset.univ : Finset (NormalizedOccurrence Q)).filter
          (fun R => RegularSolution (occurrenceFactor Q R)
            (selected gamma) gamma) := by
    ext R
    simp [occurrenceRegularSeeds, hgamma]
  rw [hfiber]
  change 2 <= ((Finset.univ.filter (fun R : NormalizedOccurrence Q =>
    RegularSolution (occurrenceFactor Q R) (selected gamma) gamma)).val).card
  rw [← Multiset.card_map (occurrenceFactor Q)]
  rw [Finset.filter_val]
  change 2 <= (Multiset.map (occurrenceFactor Q)
    (Multiset.filter
      ((fun F => RegularSolution F (selected gamma) gamma) ∘ occurrenceFactor Q)
      (Finset.univ : Finset (NormalizedOccurrence Q)).val)).card
  rw [← Multiset.filter_map]
  simpa [occurrenceFactor] using htwo

theorem twice_card_le_occurrence_regular_sum
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (hQzero : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hQderiv : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) Q) = 0)
    (haux : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (ContactSingularAuxiliary.singularAuxiliary Q) ≠ 0) :
    2 * Gamma.card <=
      ∑ R : NormalizedOccurrence Q,
        (occurrenceRegularSeeds Q selected Gamma R).card := by
  apply twice_card_le_sum_card_of_two_cover Gamma
    (occurrenceRegularSeeds Q selected Gamma)
  · exact occurrenceRegularSeeds_subset Q selected Gamma
  · intro gamma hgamma
    exact pointwise_two_occurrence_cover Q hQ selected Gamma gamma hgamma
      (hQzero gamma hgamma) (hQderiv gamma hgamma) (haux gamma hgamma)

 
theorem normalizedOccurrence_product_dvd
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) :
    (∏ R : NormalizedOccurrence Q, occurrenceFactor Q R) ∣ Q := by
  change (∏ R : normalizedFactors Q, (R : MvPolynomial (Fin 4) K)) ∣ Q
  rw [← Multiset.prod_eq_prod_coe]
  exact (prod_normalizedFactors hQ).dvd

abbrev occurrenceCumulativeFlag (Q : MvPolynomial (Fin 4) K)
    (R : NormalizedOccurrence Q) : FlagDegree :=
  originalCumulativeFlag (occurrenceFactor Q R)

 


theorem occurrenceCumulativeFlag_budgets
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {P : ResidualSupportParameters} (H : ResidualSupportData P Q) :
    (∑ R : NormalizedOccurrence Q,
        (occurrenceCumulativeFlag Q R).all) <= P.s ∧
      (∑ R : NormalizedOccurrence Q,
        ((occurrenceCumulativeFlag Q R).yz +
          (occurrenceCumulativeFlag Q R).all)) <= P.ys ∧
      (∑ R : NormalizedOccurrence Q,
        ((occurrenceCumulativeFlag Q R).zOnly +
          (occurrenceCumulativeFlag Q R).yz +
          (occurrenceCumulativeFlag Q R).all)) <= P.total := by
  have hprod := normalizedOccurrence_product_dvd Q hQ
  have hs := sum_weightedTotalDegree_le_of_prod_dvd residualSWeights
    (Finset.univ : Finset (NormalizedOccurrence Q)) (occurrenceFactor Q) Q hQ hprod
  have hm := sum_weightedTotalDegree_le_of_prod_dvd residualYSWeights
    (Finset.univ : Finset (NormalizedOccurrence Q)) (occurrenceFactor Q) Q hQ hprod
  have ht := sum_weightedTotalDegree_le_of_prod_dvd residualTotalWeights
    (Finset.univ : Finset (NormalizedOccurrence Q)) (occurrenceFactor Q) Q hQ hprod
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_congr rfl
      (fun R _ => (originalCumulativeFlag_cumulative (occurrenceFactor Q R)).1)]
    exact hs.trans H.s_weight
  · rw [Finset.sum_congr rfl
      (fun R _ => (originalCumulativeFlag_cumulative (occurrenceFactor Q R)).2.1)]
    exact hm.trans H.ys_weight
  · rw [Finset.sum_congr rfl
      (fun R _ => (originalCumulativeFlag_cumulative (occurrenceFactor Q R)).2.2)]
    exact ht.trans H.total_weight

 


theorem occurrence_regular_card_le_half_flagMixed
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (p q r : FlagDegree)
    (hQzero : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hQderiv : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) Q) = 0)
    (haux : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (ContactSingularAuxiliary.singularAuxiliary Q) ≠ 0)
    (hfactor : ∀ R : NormalizedOccurrence Q,
      (occurrenceRegularSeeds Q selected Gamma R).card <=
        flagMixed (occurrenceCumulativeFlag Q R) q r)
    (hs : (∑ R : NormalizedOccurrence Q,
      (occurrenceCumulativeFlag Q R).all) <= p.all)
    (hm : (∑ R : NormalizedOccurrence Q,
      ((occurrenceCumulativeFlag Q R).yz +
        (occurrenceCumulativeFlag Q R).all)) <= p.yz + p.all)
    (ht : (∑ R : NormalizedOccurrence Q,
      ((occurrenceCumulativeFlag Q R).zOnly +
        (occurrenceCumulativeFlag Q R).yz +
        (occurrenceCumulativeFlag Q R).all)) <=
          p.zOnly + p.yz + p.all) :
    Gamma.card <= flagMixed p q r / 2 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  rw [Nat.mul_comm]
  calc
    2 * Gamma.card <= ∑ R : NormalizedOccurrence Q,
        (occurrenceRegularSeeds Q selected Gamma R).card :=
      twice_card_le_occurrence_regular_sum Q hQ selected Gamma
        hQzero hQderiv haux
    _ <= ∑ R : NormalizedOccurrence Q,
        flagMixed (occurrenceCumulativeFlag Q R) q r :=
      Finset.sum_le_sum (fun R _ => hfactor R)
    _ <= flagMixed p q r :=
      sum_flagMixed_le_of_cumulative (occurrenceCumulativeFlag Q) p q r hs hm ht

end

end ProximityPrize.SubmissionLower.ContactSimultaneousOccurrenceLedger6750Research

#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOccurrenceLedger6750Research.pointwise_two_occurrence_cover
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOccurrenceLedger6750Research.twice_card_le_occurrence_regular_sum
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOccurrenceLedger6750Research.normalizedOccurrence_product_dvd
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOccurrenceLedger6750Research.occurrenceCumulativeFlag_budgets
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousOccurrenceLedger6750Research.occurrence_regular_card_le_half_flagMixed

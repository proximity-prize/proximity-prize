import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredOccurrenceUnion6750Research

 









namespace ProximityPrize.SubmissionLower.ContactAnchoredProductOccurrenceCover6800Research

open scoped Classical BigOperators
open UniqueFactorizationMonoid
open ContactTranslation ContactSelectedSeedDecomposition
open ContactSimultaneousFactorMultiplicity6750Research
open ContactSimultaneousOccurrenceLedger6750Research
open ContactAnchoredOccurrenceUnion6750Research

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

 

theorem one_regular_normalized_factor_occurrence
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (P : Polynomial K) (gamma : K)
    (hQzero : specialization K P gamma Q = 0)
    (haux : specialization K P gamma
      (ContactSingularAuxiliary.singularAuxiliary Q) ≠ 0) :
    1 <= ((normalizedFactors Q).filter
      (fun F => RegularSolution F P gamma)).card := by
  classical
  obtain ⟨F, hFmem, hFzero⟩ :=
    ContactFactorCover.exists_normalized_factor_of_map_zero
    (specialization K P gamma).toRingHom Q hQ hQzero
  have hFregular : RegularSolution F P gamma :=
    (normalized_factor_regular_of_auxiliary_ne_zero
      Q F P gamma hFmem hFzero haux).2
  have hmem : F ∈ (normalizedFactors Q).filter
      (fun T => RegularSolution T P gamma) :=
    Multiset.mem_filter.mpr ⟨hFmem, hFregular⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨F, hmem⟩

 


theorem anchored_product_regular_occurrence_split
    (G Q : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (hQ : Q ≠ 0)
    (P : Polynomial K) (gamma : K)
    (hGzero : specialization K P gamma G = 0)
    (hproductDerivative : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) (G * Q)) = 0)
    (hauxG : specialization K P gamma
      (ContactSingularAuxiliary.singularAuxiliary G) ≠ 0)
    (hauxQ : specialization K P gamma
      (ContactSingularAuxiliary.singularAuxiliary Q) ≠ 0) :
    (2 <= ((normalizedFactors G).filter
      (fun F => RegularSolution F P gamma)).card) ∨
    (1 <= ((normalizedFactors G).filter
        (fun F => RegularSolution F P gamma)).card ∧
      1 <= ((normalizedFactors Q).filter
        (fun F => RegularSolution F P gamma)).card) := by
  have honeG := one_regular_normalized_factor_occurrence
    G hG P gamma hGzero hauxG
  have hproduct :
      specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) G) *
        specialization K P gamma Q = 0 := by
    simpa only [MvPolynomial.pderiv_mul, map_add, map_mul, hGzero,
      zero_mul, add_zero] using hproductDerivative
  by_cases hGderivative :
      specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) G) = 0
  · exact Or.inl (two_regular_normalized_factor_occurrences
      G hG P gamma hGzero hGderivative hauxG)
  · have hQzero : specialization K P gamma Q = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left hGderivative
    exact Or.inr ⟨honeG,
      one_regular_normalized_factor_occurrence Q hQ P gamma hQzero hauxQ⟩

 

theorem two_regular_anchored_product_occurrences
    (G Q : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (hQ : Q ≠ 0)
    (P : Polynomial K) (gamma : K)
    (hGzero : specialization K P gamma G = 0)
    (hproductDerivative : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) (G * Q)) = 0)
    (hauxG : specialization K P gamma
      (ContactSingularAuxiliary.singularAuxiliary G) ≠ 0)
    (hauxQ : specialization K P gamma
      (ContactSingularAuxiliary.singularAuxiliary Q) ≠ 0) :
    2 <= ((normalizedFactors G + normalizedFactors Q).filter
      (fun F => RegularSolution F P gamma)).card := by
  rw [Multiset.filter_add, Multiset.card_add]
  rcases anchored_product_regular_occurrence_split
      G Q hG hQ P gamma hGzero hproductDerivative hauxG hauxQ with
    htwoG | ⟨honeG, honeQ⟩
  · omega
  · omega

 


theorem specialization_anchor_derivative_zero_or_quotient_zero
    (G Q : MvPolynomial (Fin 4) K) (P : Polynomial K) (gamma : K)
    (hGzero : specialization K P gamma G = 0)
    (hproductDerivative : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) (G * Q)) = 0) :
    specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) G) = 0 ∨
      specialization K P gamma Q = 0 := by
  have hproduct :
      specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) G) *
        specialization K P gamma Q = 0 := by
    simpa only [MvPolynomial.pderiv_mul, map_add, map_mul, hGzero,
      zero_mul, add_zero] using hproductDerivative
  exact mul_eq_zero.mp hproduct

 


theorem twice_card_le_anchored_occurrence_sum_of_product_derivative
    (G Q : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (hQ : Q ≠ 0)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (hGzero : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma G = 0)
    (hproductDerivative : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (G * Q)) = 0)
    (hauxG : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (ContactSingularAuxiliary.singularAuxiliary G) ≠ 0)
    (hauxQ : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (ContactSingularAuxiliary.singularAuxiliary Q) ≠ 0) :
    2 * Gamma.card <=
      (∑ R : NormalizedOccurrence G,
        (occurrenceRegularSeeds G selected Gamma R).card) +
      ∑ R : NormalizedOccurrence Q,
        (occurrenceRegularSeeds Q selected Gamma R).card := by
  apply twice_card_le_anchored_occurrence_regular_sum G Q hG hQ
    selected Gamma hGzero
  · intro gamma hgamma
    exact specialization_anchor_derivative_zero_or_quotient_zero
      G Q (selected gamma) gamma (hGzero gamma hgamma)
        (hproductDerivative gamma hgamma)
  · exact hauxG
  · exact hauxQ

 


theorem anchored_card_le_add_div_two_of_product_derivative
    (G Q : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (hQ : Q ≠ 0)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (regularG regularQ : Nat)
    (hGzero : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma G = 0)
    (hproductDerivative : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) (G * Q)) = 0)
    (hauxG : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (ContactSingularAuxiliary.singularAuxiliary G) ≠ 0)
    (hauxQ : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (ContactSingularAuxiliary.singularAuxiliary Q) ≠ 0)
    (hGsum : (∑ R : NormalizedOccurrence G,
      (occurrenceRegularSeeds G selected Gamma R).card) <= regularG)
    (hQsum : (∑ R : NormalizedOccurrence Q,
      (occurrenceRegularSeeds Q selected Gamma R).card) <= regularQ) :
    Gamma.card <= (regularG + regularQ) / 2 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  rw [Nat.mul_comm]
  exact (twice_card_le_anchored_occurrence_sum_of_product_derivative
    G Q hG hQ selected Gamma hGzero hproductDerivative hauxG hauxQ).trans
      (Nat.add_le_add hGsum hQsum)

end

end ProximityPrize.SubmissionLower.ContactAnchoredProductOccurrenceCover6800Research

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredProductOccurrenceCover6800Research.one_regular_normalized_factor_occurrence
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredProductOccurrenceCover6800Research.anchored_product_regular_occurrence_split
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredProductOccurrenceCover6800Research.two_regular_anchored_product_occurrences
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredProductOccurrenceCover6800Research.specialization_anchor_derivative_zero_or_quotient_zero
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredProductOccurrenceCover6800Research.twice_card_le_anchored_occurrence_sum_of_product_derivative
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredProductOccurrenceCover6800Research.anchored_card_le_add_div_two_of_product_derivative

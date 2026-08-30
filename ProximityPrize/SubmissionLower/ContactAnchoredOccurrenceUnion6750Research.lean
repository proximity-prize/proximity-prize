import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSimultaneousOccurrenceLedger6750Research

 















namespace ProximityPrize.SubmissionLower.ContactAnchoredOccurrenceUnion6750Research

open scoped Classical BigOperators
open UniqueFactorizationMonoid
open ContactTranslation ContactSelectedSeedDecomposition
open ContactSimultaneousFactorMultiplicity6750Research
open ContactSimultaneousOccurrenceLedger6750Research

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

 

theorem pointwise_one_occurrence_cover
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (gamma : K) (hgamma : gamma ∈ Gamma)
    (hQzero : specialization K (selected gamma) gamma Q = 0)
    (haux : specialization K (selected gamma) gamma
      (ContactSingularAuxiliary.singularAuxiliary Q) ≠ 0) :
    1 <= ((Finset.univ : Finset (NormalizedOccurrence Q)).filter
      (fun R => gamma ∈ occurrenceRegularSeeds Q selected Gamma R)).card := by
  classical
  obtain ⟨F, hFmem, hFzero⟩ :=
    ContactFactorCover.exists_normalized_factor_of_map_zero
      (specialization K (selected gamma) gamma).toRingHom Q hQ hQzero
  have hFregular : RegularSolution F (selected gamma) gamma :=
    (normalized_factor_regular_of_auxiliary_ne_zero
      Q F (selected gamma) gamma hFmem hFzero haux).2
  have hone : 1 <= ((normalizedFactors Q).filter
      (fun F => RegularSolution F (selected gamma) gamma)).card := by
    exact Multiset.card_pos_iff_exists_mem.mpr
      ⟨F, Multiset.mem_filter.mpr ⟨hFmem, hFregular⟩⟩
  have hfiber :
      (Finset.univ : Finset (NormalizedOccurrence Q)).filter
          (fun R => gamma ∈ occurrenceRegularSeeds Q selected Gamma R) =
        (Finset.univ : Finset (NormalizedOccurrence Q)).filter
          (fun R => RegularSolution (occurrenceFactor Q R)
            (selected gamma) gamma) := by
    ext R
    simp [occurrenceRegularSeeds, hgamma]
  rw [hfiber]
  change 1 <= ((Finset.univ.filter (fun R : NormalizedOccurrence Q =>
    RegularSolution (occurrenceFactor Q R) (selected gamma) gamma)).val).card
  rw [← Multiset.card_map (occurrenceFactor Q)]
  rw [Finset.filter_val]
  change 1 <= (Multiset.map (occurrenceFactor Q)
    (Multiset.filter
      ((fun F => RegularSolution F (selected gamma) gamma) ∘ occurrenceFactor Q)
      (Finset.univ : Finset (NormalizedOccurrence Q)).val)).card
  rw [← Multiset.filter_map]
  simpa [occurrenceFactor] using hone

 

theorem twice_card_le_anchored_sum_of_cover
    {Seed Left Right : Type} [Fintype Left] [Fintype Right]
    (Gamma : Finset Seed) (L : Left -> Finset Seed)
    (R : Right -> Finset Seed)
    (hLsubset : ∀ i, L i ⊆ Gamma)
    (hRsubset : ∀ i, R i ⊆ Gamma)
    (hone : ∀ gamma ∈ Gamma,
      1 <= ((Finset.univ : Finset Left).filter
        (fun i => gamma ∈ L i)).card)
    (hextra : ∀ gamma ∈ Gamma,
      2 <= ((Finset.univ : Finset Left).filter
          (fun i => gamma ∈ L i)).card ∨
        1 <= ((Finset.univ : Finset Right).filter
          (fun i => gamma ∈ R i)).card) :
    2 * Gamma.card <=
      (∑ i, (L i).card) + ∑ i, (R i).card := by
  classical
  have hpoint : ∀ gamma ∈ Gamma,
      2 <= ((Finset.univ : Finset Left).filter
          (fun i => gamma ∈ L i)).card +
        ((Finset.univ : Finset Right).filter
          (fun i => gamma ∈ R i)).card := by
    intro gamma hgamma
    rcases hextra gamma hgamma with htwo | hright
    · exact htwo.trans (Nat.le_add_right _ _)
    · exact Nat.add_le_add (hone gamma hgamma) hright
  calc
    2 * Gamma.card = ∑ gamma ∈ Gamma, 2 := by simp [Nat.mul_comm]
    _ <= ∑ gamma ∈ Gamma,
        (((Finset.univ : Finset Left).filter
            (fun i => gamma ∈ L i)).card +
          ((Finset.univ : Finset Right).filter
            (fun i => gamma ∈ R i)).card) :=
      Finset.sum_le_sum (fun gamma hgamma => hpoint gamma hgamma)
    _ = (∑ i : Left, (L i).card) + ∑ i : Right, (R i).card := by
      rw [Finset.sum_add_distrib]
      congr 1
      · calc
          (∑ gamma ∈ Gamma,
              ((Finset.univ : Finset Left).filter
                (fun i => gamma ∈ L i)).card) =
              ∑ gamma ∈ Gamma, ∑ i : Left,
                if gamma ∈ L i then 1 else 0 := by
                  apply Finset.sum_congr rfl
                  intro gamma hgamma
                  simpa using
                    (Finset.sum_boole (fun i : Left => gamma ∈ L i)
                      (Finset.univ : Finset Left)).symm
          _ = ∑ i : Left, ∑ gamma ∈ Gamma,
                if gamma ∈ L i then 1 else 0 := Finset.sum_comm
          _ = ∑ i : Left, (L i).card := by
                apply Finset.sum_congr rfl
                intro i hi
                exact (Finset.card_eq_sum_ite (hLsubset i)).symm
      · calc
          (∑ gamma ∈ Gamma,
              ((Finset.univ : Finset Right).filter
                (fun i => gamma ∈ R i)).card) =
              ∑ gamma ∈ Gamma, ∑ i : Right,
                if gamma ∈ R i then 1 else 0 := by
                  apply Finset.sum_congr rfl
                  intro gamma hgamma
                  simpa using
                    (Finset.sum_boole (fun i : Right => gamma ∈ R i)
                      (Finset.univ : Finset Right)).symm
          _ = ∑ i : Right, ∑ gamma ∈ Gamma,
                if gamma ∈ R i then 1 else 0 := Finset.sum_comm
          _ = ∑ i : Right, (R i).card := by
                apply Finset.sum_congr rfl
                intro i hi
                exact (Finset.card_eq_sum_ite (hRsubset i)).symm

 

theorem twice_card_le_anchored_occurrence_regular_sum
    (G Q : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (hQ : Q ≠ 0)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (hGzero : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma G = 0)
    (hroute : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2 : Fin 4) G) = 0 ∨
        specialization K (selected gamma) gamma Q = 0)
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
  apply twice_card_le_anchored_sum_of_cover Gamma
    (occurrenceRegularSeeds G selected Gamma)
    (occurrenceRegularSeeds Q selected Gamma)
    (occurrenceRegularSeeds_subset G selected Gamma)
    (occurrenceRegularSeeds_subset Q selected Gamma)
  · intro gamma hgamma
    exact pointwise_one_occurrence_cover G hG selected Gamma gamma hgamma
      (hGzero gamma hgamma) (hauxG gamma hgamma)
  · intro gamma hgamma
    rcases hroute gamma hgamma with hGderiv | hQzero
    · exact Or.inl (pointwise_two_occurrence_cover G hG selected Gamma
        gamma hgamma (hGzero gamma hgamma) hGderiv (hauxG gamma hgamma))
    · exact Or.inr (pointwise_one_occurrence_cover Q hQ selected Gamma
        gamma hgamma hQzero (hauxQ gamma hgamma))

 

theorem anchored_card_le_add_div_two
    (G Q : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (hQ : Q ≠ 0)
    (selected : K -> Polynomial K) (Gamma : Finset K)
    (regularG regularQ : Nat)
    (hGzero : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma G = 0)
    (hroute : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
          (MvPolynomial.pderiv (2 : Fin 4) G) = 0 ∨
        specialization K (selected gamma) gamma Q = 0)
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
  exact (twice_card_le_anchored_occurrence_regular_sum G Q hG hQ
    selected Gamma hGzero hroute hauxG hauxQ).trans
      (Nat.add_le_add hGsum hQsum)

end

end ProximityPrize.SubmissionLower.ContactAnchoredOccurrenceUnion6750Research

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOccurrenceUnion6750Research.pointwise_one_occurrence_cover
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOccurrenceUnion6750Research.twice_card_le_anchored_sum_of_cover
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOccurrenceUnion6750Research.twice_card_le_anchored_occurrence_regular_sum
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOccurrenceUnion6750Research.anchored_card_le_add_div_two

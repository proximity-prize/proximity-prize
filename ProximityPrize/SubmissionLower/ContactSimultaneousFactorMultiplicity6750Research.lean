import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition

 













namespace ProximityPrize.SubmissionLower.ContactSimultaneousFactorMultiplicity6750Research

open scoped Classical BigOperators
open UniqueFactorizationMonoid
open ContactFactorCover ContactGenericInitialPoint ContactGenericSurface
open ContactGeometricFirstTail
open ContactImplicitContactLift ContactInterpolation ContactSelectedSeedDecomposition
open ContactSingularAuxiliary ContactTranslation

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

 

theorem specialization_cofactor_zero_of_simultaneous
    (Q F H : MvPolynomial (Fin 4) K) (P : Polynomial K) (gamma : K)
    (hprod : Q = F * H)
    (hFzero : specialization K P gamma F = 0)
    (hFregular :
      specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hQderiv :
      specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) Q) = 0) :
    specialization K P gamma H = 0 := by
  rw [hprod, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
    hFzero, zero_mul, add_zero] at hQderiv
  exact (mul_eq_zero.mp hQderiv).resolve_left hFregular

 

theorem normalized_factor_active_of_specialization_zero
    (Q F : MvPolynomial (Fin 4) K) (P : Polynomial K) (gamma : K)
    (hFmem : F ∈ normalizedFactors Q)
    (hFzero : specialization K P gamma F = 0) :
    F ∈ activeFactors Q := by
  classical
  let phi := polynomialEmbedding K
  let v : Fin 3 -> GenericField K :=
    fun i => initialPoint K P gamma i.succ
  have hsurface : MvPolynomial.eval v (surfaceMap phi F) = 0 := by
    simpa only [canonical_geometricSurfaceMap] using
      (actual_generic_initial_zero_iff K P gamma F).mpr hFzero
  have hpositive : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 :=
    positive_seed_degree_of_surface_zero phi (polynomialEmbedding_injective K)
      F (ne_zero_of_mem_normalizedFactors hFmem) v hsurface
  exact Finset.mem_filter.mpr
    <| ⟨Multiset.mem_toFinset.mpr hFmem, hpositive⟩

 

theorem normalized_factor_regular_of_auxiliary_ne_zero
    (Q F : MvPolynomial (Fin 4) K) (P : Polynomial K) (gamma : K)
    (hFmem : F ∈ normalizedFactors Q)
    (hFzero : specialization K P gamma F = 0)
    (haux : specialization K P gamma (singularAuxiliary Q) ≠ 0) :
    0 < F.degreeOf 2 ∧ RegularSolution F P gamma := by
  classical
  have hactive := normalized_factor_active_of_specialization_zero
    Q F P gamma hFmem hFzero
  have hRpos : 0 < F.degreeOf 2 := by
    by_contra hnot
    have hRzero : F.degreeOf 2 = 0 := Nat.eq_zero_of_not_pos hnot
    exact haux (singularAuxiliary_map_zero
      (specialization K P gamma).toRingHom Q F hactive hFzero (Or.inl hRzero))
  have hregular :
      specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0 := by
    intro hderiv
    exact haux (singularAuxiliary_map_zero
      (specialization K P gamma).toRingHom Q F hactive hFzero (Or.inr hderiv))
  exact ⟨hRpos, hFzero, hregular⟩

 


theorem two_vanishing_normalized_factor_occurrences
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (P : Polynomial K) (gamma : K)
    (hQzero : specialization K P gamma Q = 0)
    (hQderiv :
      specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) Q) = 0)
    (haux : specialization K P gamma (singularAuxiliary Q) ≠ 0) :
    2 <= ((normalizedFactors Q).filter
      (fun F => specialization K P gamma F = 0)).card := by
  classical
  obtain hauxzero | ⟨F, hFpositive, hFzero, hFregular⟩ :=
    solution_regular_or_auxiliary Q hQ P gamma hQzero
  · exact False.elim (haux hauxzero)
  · have hFspec := positiveRFactors_spec Q F hFpositive
    obtain ⟨H, hprod⟩ := hFspec.2.1
    have hFne : F ≠ 0 := hFspec.1.ne_zero
    have hHne : H ≠ 0 := by
      intro hHzero
      apply hQ
      rw [hprod, hHzero, mul_zero]
    have hHzero : specialization K P gamma H = 0 :=
      specialization_cofactor_zero_of_simultaneous Q F H P gamma hprod
        hFzero hFregular hQderiv
    obtain ⟨T, hTmem, hTzero⟩ := exists_normalized_factor_of_map_zero
      (specialization K P gamma).toRingHom H hHne hHzero
    have hFactive : F ∈ activeFactors Q :=
      (Finset.mem_filter.mp hFpositive).1
    have hFmem : F ∈ normalizedFactors Q :=
      Multiset.mem_toFinset.mp (Finset.mem_filter.mp hFactive).1
    have hFnorm : normalize F = F := normalize_normalized_factor F hFmem
    have hFcard :
        ((normalizedFactors F).filter
          (fun G => specialization K P gamma G = 0)).card = 1 := by
      rw [normalizedFactors_irreducible hFspec.1, hFnorm]
      simp only [Multiset.filter_singleton, if_pos hFzero, Multiset.card_singleton]
    have hHcard :
        1 <= ((normalizedFactors H).filter
          (fun G => specialization K P gamma G = 0)).card := by
      have hmem : T ∈ (normalizedFactors H).filter
          (fun G => specialization K P gamma G = 0) :=
        Multiset.mem_filter.mpr ⟨hTmem, hTzero⟩
      exact (Multiset.card_pos_iff_exists_mem.mpr ⟨T, hmem⟩)
    rw [hprod, normalizedFactors_mul hFne hHne, Multiset.filter_add,
      Multiset.card_add, hFcard]
    omega

 

theorem two_regular_normalized_factor_occurrences
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (P : Polynomial K) (gamma : K)
    (hQzero : specialization K P gamma Q = 0)
    (hQderiv :
      specialization K P gamma (MvPolynomial.pderiv (2 : Fin 4) Q) = 0)
    (haux : specialization K P gamma (singularAuxiliary Q) ≠ 0) :
    2 <= ((normalizedFactors Q).filter
      (fun F => RegularSolution F P gamma)).card := by
  classical
  have htwo := two_vanishing_normalized_factor_occurrences
    Q hQ P gamma hQzero hQderiv haux
  have heq :
      (normalizedFactors Q).filter
          (fun F => specialization K P gamma F = 0) =
        (normalizedFactors Q).filter (fun F => RegularSolution F P gamma) := by
    apply Multiset.filter_congr
    intro F hFmem
    constructor
    · intro hFzero
      exact (normalized_factor_regular_of_auxiliary_ne_zero
        Q F P gamma hFmem hFzero haux).2
    · exact fun hregular => hregular.1
  rwa [heq] at htwo

 

theorem twice_card_le_sum_card_of_two_cover
    {Seed Index : Type*} [Fintype Index]
    (Gamma : Finset Seed) (S : Index -> Finset Seed)
    (hsubset : ∀ i, S i ⊆ Gamma)
    (htwo : ∀ gamma ∈ Gamma,
      2 <= ((Finset.univ : Finset Index).filter
        (fun i => gamma ∈ S i)).card) :
    2 * Gamma.card <= ∑ i, (S i).card := by
  classical
  calc
    2 * Gamma.card = ∑ gamma ∈ Gamma, 2 := by
      simp [Nat.mul_comm]
    _ <= ∑ gamma ∈ Gamma,
        ((Finset.univ : Finset Index).filter
          (fun i => gamma ∈ S i)).card :=
      Finset.sum_le_sum (fun gamma hgamma => htwo gamma hgamma)
    _ = ∑ gamma ∈ Gamma, ∑ i : Index,
        if gamma ∈ S i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro gamma hgamma
      simpa using
        (Finset.sum_boole (fun i : Index => gamma ∈ S i)
          (Finset.univ : Finset Index)).symm
    _ = ∑ i : Index, ∑ gamma ∈ Gamma,
        if gamma ∈ S i then 1 else 0 := Finset.sum_comm
    _ = ∑ i, (S i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.card_eq_sum_ite (hsubset i)).symm

end

end ProximityPrize.SubmissionLower.ContactSimultaneousFactorMultiplicity6750Research

#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousFactorMultiplicity6750Research.specialization_cofactor_zero_of_simultaneous
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousFactorMultiplicity6750Research.normalized_factor_regular_of_auxiliary_ne_zero
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousFactorMultiplicity6750Research.two_vanishing_normalized_factor_occurrences
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousFactorMultiplicity6750Research.two_regular_normalized_factor_occurrences
#print axioms ProximityPrize.SubmissionLower.ContactSimultaneousFactorMultiplicity6750Research.twice_card_le_sum_card_of_two_cover

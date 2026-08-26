import ProximityPrize.SubmissionLower.BCHKSWeightedSubstitution

namespace ProximityPrize.SubmissionLower
namespace BCHKSResidual6400

open BCHKSSubstitutionVanish
open BCHKSWeightedSubstitution
open scoped BigOperators

/-!
Residual form of the exact-boundary interpolation argument.

When the root count misses the interpolation `X` cap, the substituted
polynomial is not arbitrary: it contains the full agreement locator to the
interpolation multiplicity.  At the `5150/+7` candidate the remaining quotient
has degree below `36050`.
-/

/-- A common lower bound on the multiplicities of distinct roots makes the
corresponding powered locator divide the polynomial. -/
theorem locator_pow_dvd_of_rootMultiplicity
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (R : Polynomial F) (ω : ι ↪ F) (A : Finset ι) (m : ℕ)
    (hmult : ∀ i ∈ A, m ≤ R.rootMultiplicity (ω i)) :
    (∏ i ∈ A, (Polynomial.X - Polynomial.C (ω i))) ^ m ∣ R := by
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact ((Polynomial.pairwise_coprime_X_sub_C ω.injective) hij).pow
  · intro i hi
    exact (pow_dvd_pow (Polynomial.X - Polynomial.C (ω i)) (hmult i hi)).trans
      (Polynomial.pow_rootMultiplicity_dvd R (ω i))

/-- Factoring all guaranteed distinct roots leaves only the degree gap. -/
theorem exists_locator_residual
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (R : Polynomial F) (ω : ι ↪ F) (A : Finset ι) (m gap : ℕ)
    (hgap : 0 < gap)
    (hmult : ∀ i ∈ A, m ≤ R.rootMultiplicity (ω i))
    (hdegree : R.natDegree < m * A.card + gap) :
    ∃ E : Polynomial F,
      R = (∏ i ∈ A, (Polynomial.X - Polynomial.C (ω i))) ^ m * E ∧
      E.natDegree < gap := by
  by_cases hR : R = 0
  · refine ⟨0, by simp [hR], ?_⟩
    simpa using hgap
  · obtain ⟨E, hfac⟩ := locator_pow_dvd_of_rootMultiplicity R ω A m hmult
    have hE : E ≠ 0 := by
      intro hE
      simp [hE] at hfac
      exact hR hfac
    let G : Polynomial F := ∏ i ∈ A,
      (Polynomial.X - Polynomial.C (ω i))
    have hG : G.Monic := by
      exact Polynomial.monic_prod_X_sub_C ω A
    have hGdeg : G.natDegree = A.card := by
      simpa [G] using
        (Polynomial.natDegree_finsetProd_X_sub_C_eq_card A ω)
    have hdegfac : R.natDegree = m * A.card + E.natDegree := by
      rw [hfac]
      rw [(hG.pow m).natDegree_mul' hE, hG.natDegree_pow, hGdeg]
    refine ⟨E, ?_, ?_⟩
    · simpa only [G] using hfac
    · omega

/-- Uniform order-`m` shift vanishing at the matched coordinates gives a
powered-locator factorization of the substituted polynomial. -/
theorem exists_triEval_locator_residual
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F)
    (P : Polynomial F) (ω : ι ↪ F) (A : Finset ι)
    (yZ : ι → Polynomial F) (m k DX gap : ℕ)
    (hDX : 0 < DX) (hgap : 0 < gap)
    (hvan : ∀ i ∈ A, ∀ s t h, s + t < m →
      ((((Polynomial.Bivariate.shift Q (Polynomial.C (ω i)) (yZ i)).coeff t).coeff s).coeff h) = 0)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (ω i) P = Polynomial.eval z (yZ i))
    (hP : P.natDegree ≤ k)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 → a + k * j < DX)
    (hroom : DX ≤ m * A.card + gap) :
    ∃ E : Polynomial F,
      triEval Q z P =
        (∏ i ∈ A, (Polynomial.X - Polynomial.C (ω i))) ^ m * E ∧
      E.natDegree < gap := by
  let R := triEval Q z P
  by_cases hR : R = 0
  · refine ⟨0, by simp [R, hR], ?_⟩
    simpa using hgap
  · have hmult : ∀ i ∈ A, m ≤ R.rootMultiplicity (ω i) := by
      intro i hi
      exact rootMultiplicity_triEval_ge_of_shift_coeff_zero
        Q (ω i) z (yZ i) P m (hvan i hi) (hmatch i hi) hR
    have hdegree : R.natDegree < m * A.card + gap := by
      have hlt := triEval_natDegree_lt_of_weighted_X_cap
        Q z P k DX hDX hP hcap
      exact hlt.trans_le hroom
    exact exists_locator_residual R ω A m gap hgap hmult hdegree

/-- Exact `5150/+7` residual statement.  An agreement set of size at least
`185364` leaves a quotient of degree at most `36049`. -/
theorem exists_triEval_residual6400
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F)
    (P : Polynomial F) (ω : ι ↪ F) (A : Finset ι)
    (yZ : ι → Polynomial F)
    (hA : 185364 ≤ A.card)
    (hvan : ∀ i ∈ A, ∀ s t h, s + t < 5150 →
      ((((Polynomial.Bivariate.shift Q (Polynomial.C (ω i)) (yZ i)).coeff t).coeff s).coeff h) = 0)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (ω i) P = Polynomial.eval z (yZ i))
    (hP : P.natDegree ≤ 131071)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
      a + 131071 * j < 954660650) :
    ∃ E : Polynomial F,
      triEval Q z P =
        (∏ i ∈ A, (Polynomial.X - Polynomial.C (ω i))) ^ 5150 * E ∧
      E.natDegree ≤ 36049 := by
  obtain ⟨E, hfac, hE⟩ := exists_triEval_locator_residual
    Q z P ω A yZ 5150 131071 954660650 36050
    (by norm_num) (by norm_num) hvan hmatch hP hcap (by omega)
  exact ⟨E, hfac, by omega⟩

/-- Any `42325` exact-boundary residues are linearly dependent, simply because
they lie in the `36050`-dimensional space of polynomials of degree below
`36050`.  This records the tempting `36050 < 42324` coincidence precisely;
the relation alone does not identify the challenge-dependent locators. -/
theorem residual_family_linearDependent6400
    {F : Type*} [Field F]
    (E : Fin 42325 → Polynomial F)
    (hE : ∀ z, (E z).natDegree ≤ 36049) :
    ¬ LinearIndependent F E := by
  intro hLI
  have hmem : ∀ z, E z ∈ Polynomial.degreeLT F 36050 := by
    intro z
    by_cases hz : E z = 0
    · simp [hz]
    · rw [Polynomial.mem_degreeLT, Polynomial.degree_eq_natDegree hz]
      exact WithBot.coe_lt_coe.mpr ((hE z).trans_lt (by norm_num))
  let E' : Fin 42325 → Polynomial.degreeLT F 36050 :=
    fun z => ⟨E z, hmem z⟩
  have hLI' : LinearIndependent F E' := by
    have hmapped : LinearIndependent F
        ((Polynomial.degreeLT F 36050).subtype ∘ E') := by
      rw [show (Polynomial.degreeLT F 36050).subtype ∘ E' = E by
        funext z
        rfl]
      exact hLI
    exact LinearIndependent.of_comp
      (Polynomial.degreeLT F 36050).subtype hmapped
  have hcard := hLI'.fintype_card_le_finrank
  rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F 36050)] at hcard
  norm_num at hcard

end BCHKSResidual6400
end ProximityPrize.SubmissionLower

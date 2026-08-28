import ProximityPrize.SubmissionLower.BCHKSFactorPigeon

namespace ProximityPrize.SubmissionLower

open Polynomial

/-- The sharp nested positive-factor count does not require every outer
specialization to be nonzero.  A vanished outer specialization contributes no
normalized inner factors; otherwise the usual normalized-factor degree sum
applies. -/
theorem positiveNormalizedFactorPairs_card_le_unconditional
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0) (x₀ : F) (M : ℕ)
    (hQdeg : Q.natDegree ≤ M) :
    (positiveNormalizedFactorPairs Q x₀).card ≤ M := by
  let s := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset
  let u := fun R : Polynomial (Polynomial (Polynomial F)) =>
    (UniqueFactorizationMonoid.normalizedFactors (triSpecializeX R x₀)).toFinset
  let upos := fun R : Polynomial (Polynomial (Polynomial F)) =>
    (u R).filter fun H => 0 < H.natDegree
  let pairs := fun R : Polynomial (Polynomial (Polynomial F)) =>
    (upos R).image fun H => (R, H)
  have hinner : ∀ R ∈ s, (pairs R).card ≤ R.natDegree := by
    intro R hR
    by_cases hspec : triSpecializeX R x₀ = 0
    · simp [pairs, upos, u, hspec]
    · calc
        (pairs R).card ≤ (upos R).card := Finset.card_image_le
        _ = (upos R).card • (1 : ℕ) := by simp
        _ ≤ ∑ H ∈ upos R, H.natDegree := by
          apply Finset.card_nsmul_le_sum
          intro H hH
          exact (Finset.mem_filter.mp hH).2
        _ ≤ ∑ H ∈ u R, H.natDegree := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          simp
        _ ≤ (triSpecializeX R x₀).natDegree := by
          exact normalizedFactors_toFinset_sum_natDegree_le
            (triSpecializeX R x₀) hspec
        _ ≤ R.natDegree := triSpecializeX_natDegree_le R x₀
  calc
    (positiveNormalizedFactorPairs Q x₀).card = (s.biUnion pairs).card := by rfl
    _ ≤ ∑ R ∈ s, (pairs R).card := Finset.card_biUnion_le
    _ ≤ ∑ R ∈ s, R.natDegree := Finset.sum_le_sum hinner
    _ ≤ Q.natDegree := normalizedFactors_toFinset_sum_natDegree_le Q hQ
    _ ≤ M := hQdeg

end ProximityPrize.SubmissionLower

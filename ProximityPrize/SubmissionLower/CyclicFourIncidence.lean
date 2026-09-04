import ProximityPrize.SubmissionLower.CyclicFourResidues

namespace ProximityPrize.SubmissionLower.CyclicFourIncidence

open ProximityPrize.Benchmark
open CyclicFourFibre CyclicFourResidues
open scoped BigOperators

set_option autoImplicit false

/-- Number of selected roots in the four-point bundle above `j`. -/
def bundleAgreementCount (S : Finset IRSProfile.Index) (j : Fin quarterSize) : ℕ :=
  ∑ t : Fin 4, if rootIndex j t ∈ S then 1 else 0

/-- The four-root bundles containing at least three selected coordinates. -/
def denseBundles (S : Finset IRSProfile.Index) : Finset (Fin quarterSize) :=
  Finset.univ.filter fun j => 3 ≤ bundleAgreementCount S j

/-- Agreements beyond the first two in a four-point bundle.  Unlike the
indicator `denseBundles`, this keeps both units contributed by a full bundle. -/
def bundleExcess (S : Finset IRSProfile.Index) (j : Fin quarterSize) : ℕ :=
  bundleAgreementCount S j - 2

theorem sum_bundleAgreementCount (S : Finset IRSProfile.Index) :
    (∑ j : Fin quarterSize, bundleAgreementCount S j) = S.card := by
  simp only [bundleAgreementCount]
  rw [← Fintype.sum_prod_type']
  change (∑ p : Fin quarterSize × Fin 4,
    if rootFibreEquiv p ∈ S then 1 else 0) = S.card
  calc
    (∑ p : Fin quarterSize × Fin 4,
        if rootFibreEquiv p ∈ S then 1 else 0) =
        ∑ i : IRSProfile.Index, if i ∈ S then 1 else 0 := by
      apply Fintype.sum_equiv rootFibreEquiv
      intro p
      rfl
    _ = S.card := by simp

theorem bundleAgreementCount_le_four (S : Finset IRSProfile.Index)
    (j : Fin quarterSize) : bundleAgreementCount S j ≤ 4 := by
  unfold bundleAgreementCount
  calc
    (∑ t : Fin 4, if rootIndex j t ∈ S then 1 else 0) ≤ ∑ _t : Fin 4, 1 := by
      apply Finset.sum_le_sum
      intro t ht
      split <;> omega
    _ = 4 := by simp

theorem card_le_two_domain_add_two_dense (S : Finset IRSProfile.Index) :
    S.card ≤ 2 * quarterSize + 2 * (denseBundles S).card := by
  rw [← sum_bundleAgreementCount]
  calc
    (∑ j : Fin quarterSize, bundleAgreementCount S j) ≤
        ∑ j : Fin quarterSize,
          (2 + if 3 ≤ bundleAgreementCount S j then 2 else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases h : 3 ≤ bundleAgreementCount S j
      · simp only [h, ↓reduceIte]
        exact bundleAgreementCount_le_four S j
      · simp only [h, ↓reduceIte, add_zero]
        omega
    _ = 2 * quarterSize + 2 * (denseBundles S).card := by
      rw [Finset.sum_add_distrib]
      simp [denseBundles, mul_comm]

/-- The exact weighted statistic retained by four-root folding: after charging
two agreements to every bundle, every remaining agreement is recorded in
`bundleExcess`. -/
theorem card_le_two_domain_add_bundleExcess (S : Finset IRSProfile.Index) :
    S.card ≤ 2 * quarterSize + ∑ j : Fin quarterSize, bundleExcess S j := by
  rw [← sum_bundleAgreementCount]
  calc
    (∑ j : Fin quarterSize, bundleAgreementCount S j) ≤
        ∑ j : Fin quarterSize, (2 + bundleExcess S j) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [bundleExcess]
      omega
    _ = 2 * quarterSize + ∑ j : Fin quarterSize, bundleExcess S j := by
      rw [Finset.sum_add_distrib]
      simp [mul_comm]

/-- At the prospective 68.03 agreement threshold, at least 25,146 bundles
carry three or four agreements. -/
theorem denseBundles_card_ge_6803 (S : Finset IRSProfile.Index)
    (hS : 181363 ≤ S.card) : 25146 ≤ (denseBundles S).card := by
  have hcap := card_le_two_domain_add_two_dense S
  norm_num [quarterSize] at hcap
  omega

/-- At the prospective 68.03 agreement threshold, the four-root bundles carry
at least 50,291 agreements beyond the baseline of two per bundle. -/
theorem bundleExcess_sum_ge_6803 (S : Finset IRSProfile.Index)
    (hS : 181363 ≤ S.card) :
    50291 ≤ ∑ j : Fin quarterSize, bundleExcess S j := by
  have hcap := card_le_two_domain_add_bundleExcess S
  norm_num [quarterSize] at hcap
  omega

end ProximityPrize.SubmissionLower.CyclicFourIncidence

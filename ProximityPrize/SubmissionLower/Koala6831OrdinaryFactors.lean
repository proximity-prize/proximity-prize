import ProximityPrize.SubmissionLower.Koala6831OrdinarySurface
import ProximityPrize.SubmissionLower.Koala6831OrdinaryFactorExceptions

namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open RCN137 MvPolynomial
open scoped BigOperators Classical

variable {E Seed : Type*} [Field E]

theorem factor_degree_budgets (Q : MvPolynomial (Fin 3) E) (hQ : Q ≠ 0) :
    (∑ F ∈ normalizedFactorSet Q, F.degreeOf 1) ≤ Q.degreeOf 1 ∧
    (∑ F ∈ normalizedFactorSet Q, F.totalDegree) ≤ Q.totalDegree := by
  refine ⟨normalizedFactorSet_degree_budget Q hQ 1, ?_⟩
  simpa only [MvPolynomial.weightedTotalDegree_one, id_eq] using
    RCN071.sum_weightedTotalDegree_le_of_prod_dvd_fin3 (1 : Fin 3 → ℕ)
      (normalizedFactorSet Q) id Q hQ (normalizedFactorSet_product_dvd Q hQ)

noncomputable def singularSeeds (seeds : Finset Seed) (point : Seed → Fin 3 → E)
    (F : MvPolynomial (Fin 3) E) : Finset Seed :=
  seeds.filter fun g ↦ MvPolynomial.eval (point g) F = 0 ∧
    MvPolynomial.eval (point g) (MvPolynomial.pderiv 1 F) = 0

theorem factor_cover_after_singular_discard
    (Q : MvPolynomial (Fin 3) E) (hQ : Q ≠ 0) (seeds : Finset Seed)
    (point : Seed → Fin 3 → E) (multiplier : ℕ)
    (hzero : ∀ g ∈ seeds, MvPolynomial.eval (point g) Q = 0)
    (hcount : ∀ F ∈ normalizedFactorSet Q,
      (singularSeeds seeds point F).card ≤ multiplier * F.totalDegree) :
    ∃ bad : Finset Seed, bad ⊆ seeds ∧ bad.card ≤ multiplier * Q.totalDegree ∧
      ∀ g ∈ seeds \ bad, ∃ F ∈ normalizedFactorSet Q,
        MvPolynomial.eval (point g) F = 0 ∧
          MvPolynomial.eval (point g) (MvPolynomial.pderiv 1 F) ≠ 0 := by
  classical
  let bad := (normalizedFactorSet Q).biUnion (singularSeeds seeds point)
  refine ⟨bad, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨F, _, hgF⟩ := Finset.mem_biUnion.mp hg
    exact (Finset.mem_filter.mp hgF).1
  · calc
      bad.card ≤ ∑ F ∈ normalizedFactorSet Q, (singularSeeds seeds point F).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ F ∈ normalizedFactorSet Q, multiplier * F.totalDegree :=
        Finset.sum_le_sum hcount
      _ = multiplier * (∑ F ∈ normalizedFactorSet Q, F.totalDegree) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ multiplier * Q.totalDegree :=
        Nat.mul_le_mul_left _ (factor_degree_budgets Q hQ).2
  · intro g hg
    have hmem := Finset.mem_sdiff.mp hg
    obtain ⟨F, hF, hz⟩ := exists_normalizedFactorSet_zero (MvPolynomial.eval (point g))
      Q hQ (hzero g hmem.1)
    refine ⟨F, hF, hz, ?_⟩
    intro hsing
    apply hmem.2
    exact Finset.mem_biUnion.mpr ⟨F, hF, Finset.mem_filter.mpr ⟨hmem.1, hz, hsing⟩⟩

theorem discard_singular_ordinary_seeds {K : Type*} [Field K] (p : ℕ) [CharP E p]
    (φ : Polynomial K →+* E) (hφ : Function.Injective φ) (F : Carrier K) (hF : F ≠ 0)
    (y t : ℕ) (hy : y < p) (ht : t < p) (hSylvester : (2 * y - 1) * t < p)
    (hcap : ∀ d ∈ F.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hvanish : ∀ g ∈ seeds, MvPolynomial.aeval
      ![Polynomial.X, selected g, Polynomial.C g, Polynomial.C (g ^ p)] F = 0) :
    ∃ bad : Finset K, bad ⊆ seeds ∧ bad.card ≤ p * (2 * y + 2) * t ∧
      ∀ g ∈ seeds \ bad, ∃ H ∈ normalizedFactorSet (ordinarySurface φ F),
        MvPolynomial.eval (ordinaryPoint φ selected p g) H = 0 ∧
          MvPolynomial.eval (ordinaryPoint φ selected p g) (MvPolynomial.pderiv 1 H) ≠ 0 := by
  classical
  let Q := ordinarySurface φ F
  let point := ordinaryPoint φ selected p
  have hQ : Q ≠ 0 := by
    intro hz
    apply hF
    apply ordinarySurface_injective φ hφ
    simpa only [map_zero] using hz
  have hQbounds := ordinarySurface_degree_caps φ F y t hcap
  have hQroots : ∀ g ∈ seeds, MvPolynomial.eval (point g) Q = 0 := by
    intro g hg
    rw [show MvPolynomial.eval (point g) Q = _ from eval_ordinarySurface φ selected p g F,
      hvanish g hg, map_zero]
  have hcount (H : MvPolynomial (Fin 3) E) (hH : H ∈ normalizedFactorSet Q) :
      (singularSeeds seeds point H).card ≤ p * (2 * y + 2) * H.totalDegree := by
    have hspec := normalizedFactorSet_spec Q H hH
    have hHy := (coordinate_degree_le_of_dvd 1 H Q hspec.2 hQ).trans hQbounds.1
    have hHt : H.totalDegree ≤ t :=
      (Finset.single_le_sum (fun J _ ↦ Nat.zero_le J.totalDegree) hH).trans
        ((factor_degree_budgets Q hQ).2.trans hQbounds.2)
    let bad := singularSeeds seeds point H
    have hroot (g : K) (hg : g ∈ bad) := (Finset.mem_filter.mp hg).2.1
    have hsing (g : K) (hg : g ∈ bad) := (Finset.mem_filter.mp hg).2.2
    by_cases h0 : H.degreeOf 1 = 0
    · have hb := Koala6831OrdinaryFactorExceptions.pure_embedded_seed_card_le
        (φ.comp Polynomial.C) H hspec.1.ne_zero h0 (hHt.trans_lt ht) bad (φ ∘ selected) hroot
      have hm : p ≤ p * (2 * y + 2) := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left p (show 1 ≤ 2 * y + 2 by omega)
      exact hb.trans (Nat.mul_le_mul_right _ hm)
    · have hmul : (2 * H.degreeOf 1 - 1) * H.totalDegree ≤ (2 * y - 1) * t :=
        Nat.mul_le_mul (by omega) hHt
      have hb := Koala6831OrdinaryFactorExceptions.singular_embedded_seed_card_le
        (φ.comp Polynomial.C) H hspec.1 (Nat.pos_of_ne_zero h0) (hHy.trans_lt hy)
        (hmul.trans_lt hSylvester) bad (φ ∘ selected) hroot hsing
      rw [← Nat.mul_assoc] at hb
      exact hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
  obtain ⟨bad, hsub, hbad, hregular⟩ :=
    factor_cover_after_singular_discard Q hQ seeds point (p * (2 * y + 2)) hQroots hcount
  exact ⟨bad, hsub, hbad.trans (Nat.mul_le_mul_left _ hQbounds.2), hregular⟩

end ProximityPrize.SubmissionLower.Koala6831Ordinary

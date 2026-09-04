import ProximityPrize.SubmissionLower.LocatorDerivativeMultiplicityDichotomy6803

/-!
# Exact derivative-chain strata

`LocatorDerivativeChain.chainSeeds` remembers only the original equation
`F = 0`.  For the multiplicity refinement we retain every preceding derivative
equation.  In particular, a stage-`j` seed lies on the immediate predecessor
`dR (j - 1) F`; that extra equation drives the proper-intersection versus
repeated-component dichotomy.
-/

namespace ProximityPrize.SubmissionLower.LocatorExactDerivativeChain6803

open scoped Classical
open RCN052 RCN138 RCN167 RCN174 RCN286 RCN319
open LocatorDerivativeChain

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

/-- The first regular derivative stage, with all earlier vanishing equations
retained. -/
def exactChainSeeds (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun gamma =>
    RegularSolution (dR j F) (selected gamma) gamma ∧
      ∀ i ≤ j, specialization K (selected gamma) gamma (dR i F) = 0

theorem exactChainSeeds_subset (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    exactChainSeeds F j selected Gamma ⊆ Gamma :=
  Finset.filter_subset _ _

/-- Exact strengthening of `chain_split`: the regular alternative carries the
whole lower-derivative vanishing history. -/
theorem chain_split_exact (F : MvPolynomial (Fin 4) K)
    (P : Polynomial K) (gamma : K)
    (h0 : specialization K P gamma F = 0)
    (h1 : specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) = 0)
    (m : ℕ) (hm : 1 ≤ m) :
    (∃ j, 1 ≤ j ∧ j < m ∧ RegularSolution (dR j F) P gamma ∧
      ∀ i ≤ j, specialization K P gamma (dR i F) = 0) ∨
      (∀ i ≤ m, specialization K P gamma (dR i F) = 0) := by
  induction m with
  | zero => omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst k
        right
        intro i hi
        interval_cases i
        · simpa using h0
        · rw [dR_succ]
          simpa using h1
      · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
        rcases ih hk1 with ⟨j, hj1, hjk, hreg, hall⟩ | hall
        · exact Or.inl ⟨j, hj1, by omega, hreg, hall⟩
        · by_cases hnext : specialization K P gamma (dR (k + 1) F) = 0
          · right
            intro i hi
            rcases Nat.lt_or_ge i (k + 1) with hlt | hge
            · exact hall i (by omega)
            · have : i = k + 1 := by omega
              subst i
              exact hnext
          · left
            refine ⟨k, hk1, by omega, ⟨hall k le_rfl, ?_⟩, hall⟩
            simpa only [dR_succ] using hnext

/-- Forgetting the history recovers the existing broad chain stratum. -/
theorem exactChainSeeds_subset_chainSeeds
    (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    exactChainSeeds F j selected Gamma ⊆
      chainSeeds F j selected Gamma := by
  intro gamma hgamma
  obtain ⟨hGamma, hreg, hall⟩ := Finset.mem_filter.mp hgamma
  apply Finset.mem_filter.mpr
  refine ⟨hGamma, hreg, ?_⟩
  simpa using hall 0 (Nat.zero_le j)

/-- The original derivative-chain cover remains valid with exact strata. -/
theorem cover_exact (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (p : ℕ) [CharP K p] (s : ℕ) (hsmall : s < p)
    (hR : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ s)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hQsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hTsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma T = 0) :
    Gamma ⊆
      (Finset.univ.biUnion fun F : RegularIndex Q =>
          regularPairSeeds Q T selected Gamma F) ∪
        ((positiveRFactors Q).biUnion fun F =>
          (Finset.Ico 1 (chainLength F)).biUnion fun j =>
            exactChainSeeds F j selected Gamma) ∪
        ((positiveRFactors Q).biUnion fun F =>
          tailSeeds F selected Gamma) ∪
        rfreeSeeds Q selected Gamma := by
  classical
  intro gamma hgamma
  obtain ⟨F, hFactive, hFzero⟩ :=
    exists_active_factor_of_solution Q hQ (selected gamma) gamma
      (hQsolution gamma hgamma)
  by_cases hRfree : F.degreeOf 2 = 0
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨hgamma, ?_⟩
    have hdiv : F ∣ rfreeProduct Q := by
      unfold rfreeProduct
      exact Finset.dvd_prod_of_mem _
        (Finset.mem_filter.mpr ⟨hFactive, hRfree⟩)
    obtain ⟨c, hc⟩ := hdiv
    rw [hc, map_mul, hFzero, zero_mul]
  · have hpos : 0 < F.degreeOf 2 := Nat.pos_of_ne_zero hRfree
    have hFpos : F ∈ positiveRFactors Q := by
      unfold positiveRFactors
      exact Finset.mem_filter.mpr ⟨hFactive, hpos⟩
    by_cases hreg : specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) = 0
    · have hm := chainLength_pos F hpos
      rcases chain_split_exact F (selected gamma) gamma hFzero hreg
          (chainLength F) hm with
        ⟨j, hj1, hjm, hjreg, hall⟩ | hall
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨F, hFpos, ?_⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨j, Finset.mem_Ico.mpr ⟨hj1, hjm⟩, ?_⟩
        exact Finset.mem_filter.mpr ⟨hgamma, hjreg, hall⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨F, hFpos, ?_⟩
        exact Finset.mem_filter.mpr
          ⟨hgamma, hall (chainLength F) le_rfl⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨F, hFpos⟩, Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨hgamma, ⟨hFzero, hreg⟩, hTsolution gamma hgamma⟩

end

end ProximityPrize.SubmissionLower.LocatorExactDerivativeChain6803

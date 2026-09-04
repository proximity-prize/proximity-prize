import ProximityPrize.SubmissionLower.LocatorGroupedDerivativeChain6803

/-!
# The first escaping derivative on one singular base component

Fix a prime curve containing the first derivative of `F`.  If the curve
meets an exact derivative-chain stratum, some later derivative is proper on
the curve.  Well-ordering therefore supplies a first such derivative.  Its
predecessor belongs to the curve ideal, which gives a canonical split into a
regular generic part and one proper exceptional zero fibre.

This is deliberately a local component API.  It makes no choice on empty
components, so a later aggregate proof can discharge those components
trivially and choose an escape only after obtaining a seed.
-/

namespace ProximityPrize.SubmissionLower.LocatorGroupedDerivativeComponent6803

open scoped Classical
open RCN135 RCN136 RCN222 RCN238 RCN286 RCN319
open LocatorDerivativeChain
open LocatorExactDerivativeChain6803
open LocatorGroupedDerivativeChain6803

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

/-- A derivative-chain escape records the first proper derivative and the
membership of its immediate predecessor. -/
structure FirstEscape
    (P : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    (F : MvPolynomial (Fin 4) K) where
  index : ℕ
  two_le : 2 ≤ index
  below_mem : ∀ i, 2 ≤ i → i < index →
    surfaceMap (polynomialEmbedding K) (dR i F) ∈ P
  predecessor_mem :
    surfaceMap (polynomialEmbedding K) (dR (index - 1) F) ∈ P
  escape_not_mem :
    surfaceMap (polynomialEmbedding K) (dR index F) ∉ P

/-- The derivative following an exact stage is proper on every curve ideal
through the selected point. -/
theorem next_derivative_not_mem_of_exactChainSeed
    (P : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (selected : K → Polynomial K) (Gamma : Finset K)
    {gamma : K} (hgamma : gamma ∈ exactChainSeeds F j selected Gamma)
    (hpoint : P ≤ RingHom.ker
      (MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) selected gamma)).toRingHom) :
    surfaceMap (polynomialEmbedding K) (dR (j + 1) F) ∉ P := by
  intro hmem
  exact exactChainSeeds_next_ne F j selected Gamma hgamma
    (specialization_zero_of_surface_mem P F (j + 1) selected gamma
      hpoint hmem)

/-- Well-ordering upgrades the existence of any escaping derivative to a
first escape.  The predecessor membership at index two is the supplied base
equation; at larger indices it follows from minimality. -/
theorem exists_firstEscape_of_exists
    (P : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    (F : MvPolynomial (Fin 4) K)
    (hfirst : surfaceMap (polynomialEmbedding K) (dR 1 F) ∈ P)
    (hexists : ∃ k, 2 ≤ k ∧
      surfaceMap (polynomialEmbedding K) (dR k F) ∉ P) :
    Nonempty (FirstEscape P F) := by
  let k := Nat.find hexists
  have hk : 2 ≤ k ∧
      surfaceMap (polynomialEmbedding K) (dR k F) ∉ P :=
    Nat.find_spec hexists
  have hbelow : ∀ i, 2 ≤ i → i < k →
      surfaceMap (polynomialEmbedding K) (dR i F) ∈ P := by
    intro i hi hik
    by_contra hnot
    exact (Nat.find_min hexists hik) ⟨hi, hnot⟩
  have hpred :
      surfaceMap (polynomialEmbedding K) (dR (k - 1) F) ∈ P := by
    by_cases hk2 : k = 2
    · rw [hk2]
      simpa using hfirst
    · have hkgt : 2 < k := by omega
      by_contra hnot
      have hearlier : 2 ≤ k - 1 ∧
          surfaceMap (polynomialEmbedding K) (dR (k - 1) F) ∉ P :=
        ⟨by omega, hnot⟩
      exact (Nat.find_min hexists (by omega : k - 1 < k)) hearlier
  exact ⟨⟨k, hk.1, hbelow, hpred, hk.2⟩⟩

/-- A nonempty collection of exact-stage seeds on a base component has a
first escape.  The witness is chosen only after a seed of the component has
been produced. -/
theorem exists_firstEscape_of_nonempty_exact_component
    (P : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma Delta : Finset K)
    (hDelta : Delta.Nonempty)
    (hstage : ∀ gamma ∈ Delta,
      ∃ j, 1 ≤ j ∧ gamma ∈ exactChainSeeds F j selected Gamma)
    (hpoint : ∀ gamma ∈ Delta, P ≤ RingHom.ker
      (MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) selected gamma)).toRingHom)
    (hfirst : surfaceMap (polynomialEmbedding K) (dR 1 F) ∈ P) :
    Nonempty (FirstEscape P F) := by
  obtain ⟨gamma, hgamma⟩ := hDelta
  obtain ⟨j, hj, hjstage⟩ := hstage gamma hgamma
  apply exists_firstEscape_of_exists P F hfirst
  exact ⟨j + 1, by omega,
    next_derivative_not_mem_of_exactChainSeed P F j selected Gamma
      hjstage (hpoint gamma hgamma)⟩

/-- The proper zero fibre of the first escaping derivative. -/
def escapeExceptionalSeeds
    (F : MvPolynomial (Fin 4) K) (k : ℕ)
    (selected : K → Polynomial K) (Delta : Finset K) : Finset K :=
  Delta.filter fun gamma =>
    specialization K (selected gamma) gamma (dR k F) = 0

/-- The complementary open part, on which the predecessor is regular. -/
def escapeGenericSeeds
    (F : MvPolynomial (Fin 4) K) (k : ℕ)
    (selected : K → Polynomial K) (Delta : Finset K) : Finset K :=
  Delta.filter fun gamma =>
    specialization K (selected gamma) gamma (dR k F) ≠ 0

@[simp] theorem mem_escapeExceptionalSeeds
    (F : MvPolynomial (Fin 4) K) (k : ℕ)
    (selected : K → Polynomial K) (Delta : Finset K) (gamma : K) :
    gamma ∈ escapeExceptionalSeeds F k selected Delta ↔
      gamma ∈ Delta ∧
        specialization K (selected gamma) gamma (dR k F) = 0 := by
  simp [escapeExceptionalSeeds]

@[simp] theorem mem_escapeGenericSeeds
    (F : MvPolynomial (Fin 4) K) (k : ℕ)
    (selected : K → Polynomial K) (Delta : Finset K) (gamma : K) :
    gamma ∈ escapeGenericSeeds F k selected Delta ↔
      gamma ∈ Delta ∧
        specialization K (selected gamma) gamma (dR k F) ≠ 0 := by
  simp [escapeGenericSeeds]

/-- The generic and exceptional fibres form an exact cardinality partition. -/
theorem escape_partition_card
    (F : MvPolynomial (Fin 4) K) (k : ℕ)
    (selected : K → Polynomial K) (Delta : Finset K) :
    (escapeExceptionalSeeds F k selected Delta).card +
        (escapeGenericSeeds F k selected Delta).card = Delta.card := by
  classical
  simpa only [escapeExceptionalSeeds, escapeGenericSeeds] using
    Finset.card_filter_add_card_filter_not (s := Delta)
      (fun gamma => specialization K (selected gamma) gamma (dR k F) = 0)

/-- Every exceptional seed zeros the proper escaping derivative. -/
theorem escapeExceptionalSeeds_solution
    (F : MvPolynomial (Fin 4) K) (k : ℕ)
    (selected : K → Polynomial K) (Delta : Finset K)
    {gamma : K} (hgamma : gamma ∈
      escapeExceptionalSeeds F k selected Delta) :
    specialization K (selected gamma) gamma (dR k F) = 0 :=
  (mem_escapeExceptionalSeeds F k selected Delta gamma).mp hgamma |>.2

/-- On the generic fibre of a first escape, the predecessor is a regular
solution.  This pointwise statement no longer depends on the original exact
stage index. -/
theorem escapeGenericSeeds_regularSolution
    (P : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    (F : MvPolynomial (Fin 4) K) (E : FirstEscape P F)
    (selected : K → Polynomial K) (Delta : Finset K)
    (hpoint : ∀ gamma ∈ Delta, P ≤ RingHom.ker
      (MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) selected gamma)).toRingHom)
    {gamma : K} (hgamma : gamma ∈
      escapeGenericSeeds F E.index selected Delta) :
    RegularSolution (dR (E.index - 1) F) (selected gamma) gamma := by
  have hdata := (mem_escapeGenericSeeds F E.index selected Delta gamma).mp hgamma
  refine ⟨specialization_zero_of_surface_mem P F (E.index - 1)
    selected gamma (hpoint gamma hdata.1) E.predecessor_mem, ?_⟩
  have htwo := E.two_le
  have hsucc : E.index - 1 + 1 = E.index := by omega
  rw [← hsucc, dR_succ] at hdata
  exact hdata.2

/-- Pointwise form of the generic/exceptional split. -/
theorem escape_zero_or_regular_predecessor
    (P : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    (F : MvPolynomial (Fin 4) K) (E : FirstEscape P F)
    (selected : K → Polynomial K) (Delta : Finset K)
    (hpoint : ∀ gamma ∈ Delta, P ≤ RingHom.ker
      (MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) selected gamma)).toRingHom)
    {gamma : K} (hgamma : gamma ∈ Delta) :
    specialization K (selected gamma) gamma (dR E.index F) = 0 ∨
      RegularSolution (dR (E.index - 1) F) (selected gamma) gamma := by
  by_cases hzero : specialization K (selected gamma) gamma
      (dR E.index F) = 0
  · exact Or.inl hzero
  · exact Or.inr (escapeGenericSeeds_regularSolution P F E selected Delta
      hpoint (mem_escapeGenericSeeds F E.index selected Delta gamma |>.mpr
        ⟨hgamma, hzero⟩))

end

end ProximityPrize.SubmissionLower.LocatorGroupedDerivativeComponent6803

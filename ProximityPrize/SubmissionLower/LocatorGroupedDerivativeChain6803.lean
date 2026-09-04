import ProximityPrize.SubmissionLower.LocatorPredecessorIncidence6803

/-!
# Grouping derivative-chain strata on the first singular curve

The old chain ledger pays once for every derivative order.  An exact stage
remembers all preceding equations, so the stages can instead be grouped on a
component of the single pair `(F, dR 1 F)`.  On such a component choose the
first derivative which is proper.  Points where it is nonzero are regular
solutions of its predecessor; its zero fibre is a finite exceptional cut.

This file records the pointwise part of that regrouping.  The remaining
geometric assembly is an aggregation over regular components of
`(surfaceMap F, surfaceMap (dR 1 F))`.
-/

namespace ProximityPrize.SubmissionLower.LocatorGroupedDerivativeChain6803

open scoped Classical
open RCN135 RCN136 RCN222 RCN238 RCN286 RCN319
open LocatorDerivativeChain
open LocatorExactDerivativeChain6803

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

/-- The derivative following an exact stage is nonzero at that seed. -/
theorem exactChainSeeds_next_ne
    (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (selected : K → Polynomial K) (Gamma : Finset K)
    {gamma : K} (hgamma : gamma ∈ exactChainSeeds F j selected Gamma) :
    specialization K (selected gamma) gamma (dR (j + 1) F) ≠ 0 := by
  obtain ⟨_, hregular, _⟩ := Finset.mem_filter.mp hgamma
  simpa only [dR_succ] using hregular.2

/-- Every derivative at or below the exact stage vanishes. -/
theorem exactChainSeeds_history
    (F : MvPolynomial (Fin 4) K) (j : ℕ)
    (selected : K → Polynomial K) (Gamma : Finset K)
    {gamma : K} (hgamma : gamma ∈ exactChainSeeds F j selected Gamma)
    (i : ℕ) (hi : i ≤ j) :
    specialization K (selected gamma) gamma (dR i F) = 0 := by
  exact (Finset.mem_filter.mp hgamma).2.2 i hi

/-- Membership of a derivative surface in a curve ideal forces the exact
specialization equation at every selected point of that curve. -/
theorem specialization_zero_of_surface_mem
    (P : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    (F : MvPolynomial (Fin 4) K) (k : ℕ)
    (selected : K → Polynomial K) (gamma : K)
    (hpoint : P ≤ RingHom.ker
      (MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) selected gamma)).toRingHom)
    (hmem : surfaceMap (polynomialEmbedding K) (dR k F) ∈ P) :
    specialization K (selected gamma) gamma (dR k F) = 0 := by
  have heval : MvPolynomial.eval
      (selectedPoint (polynomialEmbedding K) selected gamma)
      (surfaceMap (polynomialEmbedding K) (dR k F)) = 0 := by
    change MvPolynomial.aeval
      (selectedPoint (polynomialEmbedding K) selected gamma)
        (surfaceMap (polynomialEmbedding K) (dR k F)) = 0
    exact hpoint hmem
  have hmap : polynomialEmbedding K
      (specialization K (selected gamma) gamma (dR k F)) = 0 := by
    rw [← selectedPoint_surface_evaluation]
    exact heval
  exact (polynomialEmbedding_injective K)
    (by simpa only [map_zero] using hmap)

/-- If all derivatives strictly before `k` belong to the base singular curve,
then an exact stage meeting that curve cannot terminate before `k`. -/
theorem first_proper_derivative_le_stage_succ
    (P : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    (F : MvPolynomial (Fin 4) K) (j k : ℕ)
    (selected : K → Polynomial K) (Gamma : Finset K)
    {gamma : K} (hgamma : gamma ∈ exactChainSeeds F j selected Gamma)
    (hpoint : P ≤ RingHom.ker
      (MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) selected gamma)).toRingHom)
    (hbelow : ∀ i < k,
      surfaceMap (polynomialEmbedding K) (dR i F) ∈ P) :
    k ≤ j + 1 := by
  by_contra hnot
  have hjk : j + 1 < k := by omega
  have hzero := specialization_zero_of_surface_mem P F (j + 1)
    selected gamma hpoint (hbelow (j + 1) hjk)
  exact exactChainSeeds_next_ne F j selected Gamma hgamma hzero

/-- Off the first proper derivative's zero fibre, every exact stage on the
base curve becomes a regular solution of the immediately preceding
derivative.  This is the generic branch paid only once by curve incidence. -/
theorem regularSolution_predecessor_of_first_proper
    (P : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    (F : MvPolynomial (Fin 4) K) (j k : ℕ)
    (hk : 1 ≤ k)
    (selected : K → Polynomial K) (Gamma : Finset K)
    {gamma : K} (hgamma : gamma ∈ exactChainSeeds F j selected Gamma)
    (hpoint : P ≤ RingHom.ker
      (MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) selected gamma)).toRingHom)
    (hbelow : ∀ i < k,
      surfaceMap (polynomialEmbedding K) (dR i F) ∈ P)
    (hnonzero : specialization K (selected gamma) gamma (dR k F) ≠ 0) :
    RegularSolution (dR (k - 1) F) (selected gamma) gamma := by
  have hkj : k ≤ j + 1 :=
    first_proper_derivative_le_stage_succ P F j k selected Gamma hgamma
      hpoint hbelow
  have hpred : k - 1 ≤ j := by omega
  refine ⟨exactChainSeeds_history F j selected Gamma hgamma (k - 1) hpred, ?_⟩
  have hsucc : k - 1 + 1 = k := by omega
  rw [← hsucc, dR_succ] at hnonzero
  exact hnonzero

end

end ProximityPrize.SubmissionLower.LocatorGroupedDerivativeChain6803

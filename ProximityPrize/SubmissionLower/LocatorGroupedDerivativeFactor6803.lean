import ProximityPrize.SubmissionLower.LocatorGroupedDerivativeComponent6803
import ProximityPrize.SubmissionLower.LocatorDerivativeDegreeCaps6803

/-!
# Exact derivative-chain cover on one geometric surface factor

This file connects the exact derivative strata to the single base curve
family cut out by `g = dR F = 0`.  Every nonempty base component then has a
first escaping derivative, so it can be charged once by the grouped
incidence theorem.
-/

namespace ProximityPrize.SubmissionLower.LocatorGroupedDerivativeFactor6803

open scoped Classical BigOperators
open RCN052 RCN135 RCN136 RCN167 RCN222 RCN238 RCN243 RCN264 RCN286 RCN319
open LocatorDerivativeChain LocatorExactDerivativeChain6803
open LocatorGroupedDerivativeChain6803 LocatorGroupedDerivativeComponent6803

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

/-- All exact nonterminal derivative strata of one irreducible factor. -/
def exactChainUnion (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) : Finset K :=
  (Finset.Ico 1 (chainLength F)).biUnion fun j =>
    exactChainSeeds F j selected Gamma

theorem mem_exactChainUnion_iff
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) (gamma : K) :
    gamma ∈ exactChainUnion F selected Gamma ↔
      ∃ j, 1 ≤ j ∧ j < chainLength F ∧
        gamma ∈ exactChainSeeds F j selected Gamma := by
  classical
  simp only [exactChainUnion, Finset.mem_biUnion, Finset.mem_Ico]
  aesop

theorem exactChainUnion_subset
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K) :
    exactChainUnion F selected Gamma ⊆ Gamma := by
  intro gamma hgamma
  obtain ⟨j, _, _, hj⟩ :=
    (mem_exactChainUnion_iff F selected Gamma gamma).mp hgamma
  exact exactChainSeeds_subset F j selected Gamma hj

theorem exactChainUnion_history
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    {gamma : K} (hgamma : gamma ∈ exactChainUnion F selected Gamma)
    (i : ℕ) (hi : i ≤ 1) :
    specialization K (selected gamma) gamma (dR i F) = 0 := by
  obtain ⟨j, hj1, _, hj⟩ :=
    (mem_exactChainUnion_iff F selected Gamma gamma).mp hgamma
  exact exactChainSeeds_history F j selected Gamma hj i (hi.trans hj1)

/-- Dummy relation whose regularity surface is the unit polynomial.  It lets
the standard component budget enumerate every component of `(g,dR F)`. -/
def unitRegularityRelation : MvPolynomial (Fin 4) K :=
  MvPolynomial.X (2 : Fin 4)

@[simp] theorem unitRegularityRelation_surface :
    regularitySurface (polynomialEmbedding K)
      (unitRegularityRelation (K := K)) = 1 := by
  simp [unitRegularityRelation, regularitySurface]

/-- Exact-chain seeds assigned to one geometric factor of `surfaceMap F`. -/
def geometricExactSeeds
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) : Finset K :=
  geometricSeeds K F selected (exactChainUnion F selected Gamma) g

theorem geometricExactSeeds_subset_union
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) :
    geometricExactSeeds F selected Gamma g ⊆
      exactChainUnion F selected Gamma :=
  geometricSeeds_subset K F selected (exactChainUnion F selected Gamma) g

/-- A geometric exact-chain population is covered by the components of the
single initial singular pair `(g, surfaceMap (dR 1 F))`. -/
theorem geometricExactSeeds_card_le_base_components
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) :
    (geometricExactSeeds F selected Gamma g).card ≤
      ∑ C : RegularComponent (GenericField K) g.1
          (surfaceMap (polynomialEmbedding K) (dR 1 F))
          (regularitySurface (polynomialEmbedding K)
            (unitRegularityRelation (K := K))),
        (componentSeeds (GenericField K) g.1
          (surfaceMap (polynomialEmbedding K) (dR 1 F))
          (regularitySurface (polynomialEmbedding K)
            (unitRegularityRelation (K := K)))
          (geometricExactSeeds F selected Gamma g)
          (selectedPoint (polynomialEmbedding K) selected) C).card := by
  let S := geometricExactSeeds F selected Gamma g
  let point := selectedPoint (polynomialEmbedding K) selected
  apply card_le_sum_componentSeeds (GenericField K) g.1
    (surfaceMap (polynomialEmbedding K) (dR 1 F))
    (regularitySurface (polynomialEmbedding K)
      (unitRegularityRelation (K := K))) S point
  · intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).2
  · intro gamma hgamma
    have hunion : gamma ∈ exactChainUnion F selected Gamma :=
      geometricExactSeeds_subset_union F selected Gamma g hgamma
    rw [selectedPoint_surface_evaluation,
      exactChainUnion_history F selected Gamma hunion 1 le_rfl, map_zero]
  · intro gamma hgamma
    simp

/-- Every nonempty base component admits the first-escape certificate needed
by the grouped generic/exceptional split. -/
theorem baseComponent_firstEscape
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F)
    (C : RegularComponent (GenericField K) g.1
      (surfaceMap (polynomialEmbedding K) (dR 1 F))
      (regularitySurface (polynomialEmbedding K)
        (unitRegularityRelation (K := K))))
    (hnonempty : (componentSeeds (GenericField K) g.1
      (surfaceMap (polynomialEmbedding K) (dR 1 F))
      (regularitySurface (polynomialEmbedding K)
        (unitRegularityRelation (K := K)))
      (geometricExactSeeds F selected Gamma g)
      (selectedPoint (polynomialEmbedding K) selected) C).Nonempty) :
    Nonempty (FirstEscape C.1 F) := by
  let Delta := componentSeeds (GenericField K) g.1
    (surfaceMap (polynomialEmbedding K) (dR 1 F))
    (regularitySurface (polynomialEmbedding K)
      (unitRegularityRelation (K := K)))
    (geometricExactSeeds F selected Gamma g)
    (selectedPoint (polynomialEmbedding K) selected) C
  apply exists_firstEscape_of_nonempty_exact_component C.1 F selected Gamma Delta
    hnonempty
  · intro gamma hgamma
    have hgeom : gamma ∈ geometricExactSeeds F selected Gamma g :=
      componentSeeds_subset (GenericField K) g.1
        (surfaceMap (polynomialEmbedding K) (dR 1 F))
        (regularitySurface (polynomialEmbedding K)
          (unitRegularityRelation (K := K)))
        (geometricExactSeeds F selected Gamma g)
        (selectedPoint (polynomialEmbedding K) selected) C hgamma
    have hunion := geometricExactSeeds_subset_union F selected Gamma g hgeom
    obtain ⟨j, hj1, _, hj⟩ :=
      (mem_exactChainUnion_iff F selected Gamma gamma).mp hunion
    exact ⟨j, hj1, hj⟩
  · intro gamma hgamma
    exact componentSeeds_on_prime (GenericField K) g.1
      (surfaceMap (polynomialEmbedding K) (dR 1 F))
      (regularitySurface (polynomialEmbedding K)
        (unitRegularityRelation (K := K)))
      (geometricExactSeeds F selected Gamma g)
      (selectedPoint (polynomialEmbedding K) selected) C gamma hgamma
  · exact regularComponent_T_mem (GenericField K) g.1
      (surfaceMap (polynomialEmbedding K) (dR 1 F))
      (regularitySurface (polynomialEmbedding K)
        (unitRegularityRelation (K := K))) C

end

end ProximityPrize.SubmissionLower.LocatorGroupedDerivativeFactor6803

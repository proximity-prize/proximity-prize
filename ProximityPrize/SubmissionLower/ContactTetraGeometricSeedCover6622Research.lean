import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGenericInitialPoint
import ProximityPrize.SubmissionLower.ContactGenericSurface
import ProximityPrize.SubmissionLower.ContactGeometricFactorCover
import ProximityPrize.SubmissionLower.ContactProperCutSeedCount
import ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence
import ProximityPrize.SubmissionLower.ContactTranslation
import ProximityPrize.SubmissionLower.ContactGeometricFirstTail

/-! Minimal geometric-factor cover used by the tetrahedral score-66.22 chain. -/

namespace ProximityPrize.SubmissionLower.ContactTetraGeometricSeedCover6622Research

open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface ContactGeometricFactorCover
open ContactPolynomialSolutions ContactProperCutSeedCount
open ContactPrimeSeedIncidence ContactTranslation ContactGeometricFirstTail

noncomputable section

variable (K : Type) [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

theorem selectedPoint_eq_initialPoint (selected : K → Polynomial K) (gamma : K) :
    selectedPoint (polynomialEmbedding K) selected gamma =
      fun i : Fin 3 => initialPoint K (selected gamma) gamma i.succ := rfl

theorem selectedPoint_surface_evaluation
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K) (gamma : K) :
    MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected gamma)
      (surfaceMap (polynomialEmbedding K) F) =
        polynomialEmbedding K (specialization K (selected gamma) gamma F) := by
  rw [selectedPoint_eq_initialPoint]
  simpa only [canonical_geometricSurfaceMap] using
    eval_at_actual_generic_initial_point K (selected gamma) gamma F

theorem selectedPoint_regular_of_specialization
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K) (gamma : K)
    (hregular : specialization K (selected gamma) gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    MvPolynomial.eval₂Hom ((polynomialEmbedding K).comp Polynomial.C)
      (polynomialPoint ((polynomialEmbedding K).comp Polynomial.C)
        (selected gamma) gamma ((polynomialEmbedding K) Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0 :=
  (initialPoint_regular_iff K F (selected gamma) gamma).mpr hregular

abbrev GeometricFactor (F : MvPolynomial (Fin 4) K) :=
  {g : MvPolynomial (Fin 3) (GenericField K) //
    g ∈ surfaceFactors (polynomialEmbedding K) F}

def geometricSeeds (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) : Finset K := by
  classical
  exact Gamma.filter (fun gamma =>
    MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected gamma) g.1 = 0)

theorem geometricSeeds_subset
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Gamma : Finset K) (g : GeometricFactor K F) :
    geometricSeeds K F selected Gamma g ⊆ Gamma :=
  Finset.filter_subset _ _

theorem card_le_sum_geometricSeeds
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hsolutions : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0) :
    Gamma.card ≤ ∑ g : GeometricFactor K F,
      (geometricSeeds K F selected Gamma g).card := by
  classical
  have hcover : Gamma ⊆ Finset.univ.biUnion
      (geometricSeeds K F selected Gamma) := by
    intro gamma hgamma
    have hz : MvPolynomial.eval
        (selectedPoint (polynomialEmbedding K) selected gamma)
        (surfaceMap (polynomialEmbedding K) F) = 0 := by
      rw [selectedPoint_surface_evaluation, hsolutions gamma hgamma, map_zero]
    obtain ⟨g, hg, hzg⟩ := exists_surfaceFactor_zero (polynomialEmbedding K)
      (polynomialEmbedding_injective K) F hF
      (selectedPoint (polynomialEmbedding K) selected gamma) hz
    exact Finset.mem_biUnion.mpr ⟨⟨g, hg⟩, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hgamma, hzg⟩⟩
  exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le

end

end ProximityPrize.SubmissionLower.ContactTetraGeometricSeedCover6622Research

#print axioms ProximityPrize.SubmissionLower.ContactTetraGeometricSeedCover6622Research.card_le_sum_geometricSeeds

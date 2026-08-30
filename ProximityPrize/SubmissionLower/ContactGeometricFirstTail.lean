import ProximityPrize.SubmissionLower.ContactGaussLocalization
import ProximityPrize.SubmissionLower.GeometricFactorContraction
import ProximityPrize.SubmissionLower.ContactTailClosure
import ProximityPrize.SubmissionLower.ContactGenericInitialPoint

namespace ProximityPrize.SubmissionLower.ContactGeometricFirstTail

open ContactGenericSurface ContactGaussLocalization ContactTaylorNumerators
open ContactTailClosure ContactInterpolation ContactTranslation
open ContactGenericInitialPoint

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra (RationalCoefficients K) L]

def geometricPolynomialEmbedding : Polynomial K →+* L :=
  (algebraMap (RationalCoefficients K) L).comp
    (algebraMap (Polynomial K) (RationalCoefficients K))

def geometricSurfaceMap : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 3) L :=
  (MvPolynomial.map (algebraMap (RationalCoefficients K) L)).comp (rationalSurfaceMap K)

theorem geometricSurfaceMap_eq_surfaceMap :
    geometricSurfaceMap K L = surfaceMap (geometricPolynomialEmbedding K L) := by
  apply RingHom.ext
  intro F
  change MvPolynomial.map (algebraMap (RationalCoefficients K) L)
      (MvPolynomial.map (algebraMap (Polynomial K) (RationalCoefficients K)) (collectX K F)) =
    MvPolynomial.map ((algebraMap (RationalCoefficients K) L).comp
      (algebraMap (Polynomial K) (RationalCoefficients K))) (collectX K F)
  exact MvPolynomial.map_map _ _ _

theorem geometric_factor_dvd_iff
    (F M : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (hpos : 0 < F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3)
    (g : MvPolynomial (Fin 3) L) (hg : Irreducible g)
    (hdivF : g ∣ geometricSurfaceMap K L F) :
    g ∣ geometricSurfaceMap K L M ↔ F ∣ M := by
  constructor
  · intro hdivM
    have hfrac : rationalSurfaceMap K F ∣ rationalSurfaceMap K M :=
      GeometricFactorContraction.original_dvd_of_geometric_factor_dvd
        (rationalSurfaceMap K F) (rationalSurfaceMap K M)
        (rationalSurfaceMap_irreducible K F hF hpos) g hg hdivF hdivM
    exact (rationalSurfaceMap_dvd_iff K F M hF hpos).mp hfrac
  · intro hdiv
    exact hdivF.trans (map_dvd (geometricSurfaceMap K L) hdiv)

section CanonicalGenericField

theorem canonical_geometricPolynomialEmbedding :
    geometricPolynomialEmbedding K (GenericField K) = polynomialEmbedding K := rfl

theorem canonical_geometricSurfaceMap :
    geometricSurfaceMap K (GenericField K) = surfaceMap (polynomialEmbedding K) := by
  rw [geometricSurfaceMap_eq_surfaceMap, canonical_geometricPolynomialEmbedding]

theorem eval_at_actual_generic_initial_point
    (P : Polynomial K) (γ : K) (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval (fun i : Fin 3 => initialPoint K P γ i.succ)
      (geometricSurfaceMap K (GenericField K) F) =
      polynomialEmbedding K (specialization K P γ F) := by
  rw [canonical_geometricSurfaceMap, eval_surfaceMap]
  change MvPolynomial.eval₂Hom (coefficientEmbedding K)
      (Fin.cases (initialCoordinate K) (fun i : Fin 3 => initialPoint K P γ i.succ)) F = _
  have hv : Fin.cases (initialCoordinate K) (fun i : Fin 3 => initialPoint K P γ i.succ) =
      initialPoint K P γ := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [hv]
  exact evaluation_at_initialPoint K P γ F

theorem actual_generic_initial_zero_iff
    (P : Polynomial K) (γ : K) (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval (fun i : Fin 3 => initialPoint K P γ i.succ)
      (geometricSurfaceMap K (GenericField K) F) = 0 ↔ specialization K P γ F = 0 := by
  rw [eval_at_actual_generic_initial_point, polynomialEmbedding_eq_zero_iff]

end CanonicalGenericField

end
end ProximityPrize.SubmissionLower.ContactGeometricFirstTail

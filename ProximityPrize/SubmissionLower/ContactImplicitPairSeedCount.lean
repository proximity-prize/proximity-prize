import ProximityPrize.SubmissionLower.ContactProperCutSeedCount
import ProximityPrize.SubmissionLower.ContactCountingCaps
import ProximityPrize.SubmissionLower.ContactImplicitPairBudgets
namespace ProximityPrize.SubmissionLower.ContactImplicitPairSeedCount

open scoped Classical BigOperators
open ContactAlignmentParameters  ContactCountingCaps
open  ContactImplicitPairBudgets ContactGenericSurface
open ContactGenericInitialPoint ContactGeometricFirstTail ContactGeometricFactorCover
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactFactorCaps
open ContactInterpolation ContactTranslation ActualCoordinateDegreeSum

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω]

def pairCost (A G : MvPolynomial (Fin 4) K) : DegreeVector :=
  ⟨pairYCost ⟨A, G⟩, pairRCost ⟨A, G⟩, pairZCost ⟨A, G⟩⟩

def geometricPairCost (A : MvPolynomial (Fin 4) K)
    (g : MvPolynomial (Fin 3) Ω) : DegreeVector :=
  ⟨g.degreeOf 1 * A.degreeOf 3,
    g.degreeOf 0 * A.degreeOf 3 + g.degreeOf 2 * A.degreeOf 1,
    g.degreeOf 1 * A.degreeOf 1⟩

theorem coordinateMixedDegree_le_geometricPairCost
    (φ : Polynomial K →+* Ω) (A : MvPolynomial (Fin 4) K)
    (hAR : A.degreeOf 2 = 0) (g : MvPolynomial (Fin 3) Ω) (i : Fin 3) :
    coordinateMixedDegree Ω g (surfaceMap φ A) i ≤ capAt (geometricPairCost A g) i := by
  have hTY : (surfaceMap φ A).degreeOf (0 : Fin 3) ≤ A.degreeOf (1 : Fin 4) :=
    surfaceMap_degreeOf_le φ A (0 : Fin 3)
  have hTRle : (surfaceMap φ A).degreeOf (1 : Fin 3) ≤ A.degreeOf (2 : Fin 4) :=
    surfaceMap_degreeOf_le φ A (1 : Fin 3)
  rw [hAR] at hTRle
  have hTR : (surfaceMap φ A).degreeOf (1 : Fin 3) = 0 :=
    Nat.eq_zero_of_le_zero hTRle
  have hTZ : (surfaceMap φ A).degreeOf (2 : Fin 3) ≤ A.degreeOf (3 : Fin 4) :=
    surfaceMap_degreeOf_le φ A (2 : Fin 3)
  fin_cases i
  · simpa [coordinateMixedDegree_zero, hTR, capAt, geometricPairCost] using
      Nat.mul_le_mul_left (g.degreeOf 1) hTZ
  · have h := Nat.add_le_add
      (Nat.mul_le_mul_right (g.degreeOf 2) hTY)
      (Nat.mul_le_mul_left (g.degreeOf 0) hTZ)
    simpa [coordinateMixedDegree_one, capAt, geometricPairCost,
      Nat.mul_comm, Nat.add_comm] using h
  · simpa [coordinateMixedDegree_two, hTR, capAt, geometricPairCost, Nat.mul_comm] using
      Nat.mul_le_mul_right (g.degreeOf 1) hTY

theorem sum_geometricPairCost_le
    (φ : Polynomial K →+* Ω) (hφ : Function.Injective φ)
    (A G : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (i : Fin 3) :
    (∑ g ∈ surfaceFactors φ G, capAt (geometricPairCost A g) i) ≤ capAt (pairCost A G) i := by
  have hY := surfaceFactors_degree_budget φ hφ G hG (0 : Fin 3)
  have hR := surfaceFactors_degree_budget φ hφ G hG (1 : Fin 3)
  have hZ := surfaceFactors_degree_budget φ hφ G hG (2 : Fin 3)
  fin_cases i
  · simpa [capAt, geometricPairCost, pairCost, pairYCost, ← Finset.sum_mul] using
      Nat.mul_le_mul_right (A.degreeOf 3) hR
  · simpa [capAt, geometricPairCost, pairCost, pairRCost,
      Finset.sum_add_distrib, ← Finset.sum_mul] using
      Nat.add_le_add (Nat.mul_le_mul_right (A.degreeOf 3) hY)
        (Nat.mul_le_mul_right (A.degreeOf 1) hZ)
  · simpa [capAt, geometricPairCost, pairCost, pairZCost, ← Finset.sum_mul] using
      Nat.mul_le_mul_right (A.degreeOf 1) hR

theorem canonical_selectedPoint_surface_evaluation
    (selected : K → Polynomial K) (γ : K) (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
      (surfaceMap (polynomialEmbedding K) F) =
        polynomialEmbedding K (specialization K (selected γ) γ F) := by
  rw [selectedPoint_evaluation]
  exact evaluation_at_initialPoint K (selected γ) γ F

theorem geometric_factor_proper_cut
    (A G : MvPolynomial (Fin 4) K) (hG : Irreducible G)
    (hGR : G.degreeOf 2 = 1) (hproper : ¬ G ∣ A)
    (g : MvPolynomial (Fin 3) (GenericField K))
    (hg : g ∈ surfaceFactors (polynomialEmbedding K) G) :
    ¬ g ∣ surfaceMap (polynomialEmbedding K) A := by
  obtain ⟨hgi, hdiv⟩ := surfaceFactors_spec (polynomialEmbedding K) G g hg
  have hpos : 0 < G.degreeOf 1 + G.degreeOf 2 + G.degreeOf 3 := by omega
  have hgeo : g ∣ geometricSurfaceMap K (GenericField K) G := by
    simpa only [canonical_geometricSurfaceMap] using hdiv
  intro h
  apply hproper
  apply (geometric_factor_dvd_iff K (GenericField K) G A hG hpos g hgi hgeo).mp
  simpa only [canonical_geometricSurfaceMap] using h

variable {ι : Type*}

end

end ProximityPrize.SubmissionLower.ContactImplicitPairSeedCount

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGlobalShearSurfaceSeedCount6533
import ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount

/-!
# Actual original-factor regular count for the 65.67 global-shear row

Every selected solution is covered by the actual geometric factor family.
The characteristic-free sheared whole-surface estimate is applied factor by
factor, then summed using the genuine coordinate-degree budgets.
-/

namespace ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount6533

open scoped Classical BigOperators
open ContactParameters6533 ContactShearLedger6533
open ContactGlobalShearSurfaceSeedCount6533
open ContactGenericInitialPoint ContactGenericSurface ContactGeometricFirstTail
open ContactGeometricFactorCover ContactRegularFactorGate ContactFactorCaps
open ContactPrimeSeedIncidence ContactPolynomialSolutions ContactInterpolation
open ContactTranslation ContactFullTriangleAgreement

noncomputable section

variable (K : Type) [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

def originalDegreeVector (F : MvPolynomial (Fin 4) K) : DegreeVector :=
  ⟨F.degreeOf 1, F.degreeOf 2, F.degreeOf 3⟩

theorem sum_shearedWhole_geometricFactors_le
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0) :
    (∑ g : ContactOriginalRegularSeedCount.GeometricFactor K F,
      shearedWholeNumerator (degreeVector g.1)) ≤
        shearedWholeNumerator (originalDegreeVector K F) := by
  classical
  rw [← sum_shearedWhole
    (fun g : ContactOriginalRegularSeedCount.GeometricFactor K F ↦ degreeVector g.1)]
  rw [shearedWhole_eq_dot, shearedWhole_eq_dot]
  apply dot_mono_left
  refine ⟨?_, ?_, ?_⟩
  · simpa [sumVector, degreeVector, originalDegreeVector] using
      ContactOriginalRegularSeedCount.geometricFactor_sum_degree_le K F hF 0
  · simpa [sumVector, degreeVector, originalDegreeVector] using
      ContactOriginalRegularSeedCount.geometricFactor_sum_degree_le K F hF 1
  · simpa [sumVector, degreeVector, originalDegreeVector] using
      ContactOriginalRegularSeedCount.geometricFactor_sum_degree_le K F hF 2

variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

theorem original_regular_seed_bound
    [CharP K prime]
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (hRpos : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hfull : MvPolynomial.weightedTotalDegree fullSurfaceWeights F ≤ seedTotalCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset ι) (x u0 u1 : ι → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolutions : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors) :
    Gamma.card * gap ^ 2 ≤ shearedWholeNumerator (originalDegreeVector K F) := by
  classical
  letI : CharP (GenericField K) prime := genericField_charP K prime
  have hc := degree_bounds_of_mem_box F weightedCap w seedTotalCap slopeCap
    (by norm_num [w]) hbox
  have hY : F.degreeOf 1 ≤ yCap := hc.1
  have hR : F.degreeOf 2 ≤ slopeCap := hc.2.1
  have hZ : F.degreeOf 3 ≤ seedTotalCap := hc.2.2
  have hsmall : F.degreeOf 2 < prime :=
    hR.trans_lt (by norm_num [slopeCap, prime])
  have hcount (g : ContactOriginalRegularSeedCount.GeometricFactor K F) :
      (ContactOriginalRegularSeedCount.geometricSeeds K F selected Gamma g).card *
          gap ^ 2 ≤ shearedWholeNumerator (degreeVector g.1) := by
    obtain ⟨hgirred, hgdiv⟩ :=
      surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
    have hgate := geometric_factor_regular_gate K (GenericField K) F hF prime
      hRpos hsmall g.1 hgirred
      (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
    have hHproper : ¬ g.1 ∣ surfaceMap (polynomialEmbedding K)
        (MvPolynomial.pderiv (2 : Fin 4) F) := by
      simpa only [canonical_geometricSurfaceMap] using hgate.2.2.2.2
    have hsub := ContactOriginalRegularSeedCount.geometricSeeds_subset
      K F selected Gamma g
    apply whole_surface_seed_bound_fixed (polynomialEmbedding K)
      F g.1 hgirred hgdiv hgate.1 hHproper hbox hfull
    · exact (ContactOriginalRegularSeedCount.geometricFactor_degree_le
        K F hF.ne_zero g 0).trans hY
    · exact (ContactOriginalRegularSeedCount.geometricFactor_degree_le
        K F hF.ne_zero g 1).trans hR
    · exact (ContactOriginalRegularSeedCount.geometricFactor_degree_le
        K F hF.ne_zero g 2).trans hZ
    · exact hY
    · exact hR
    · exact hZ
    · exact hinj
    · exact hnodes
    · intro gamma hgamma
      exact hdegree gamma (hsub hgamma)
    · intro gamma hgamma
      exact hsolutions gamma (hsub hgamma)
    · intro gamma hgamma
      exact ContactOriginalRegularSeedCount.selectedPoint_regular_of_specialization
        K F selected gamma (hregular gamma (hsub hgamma))
    · intro gamma hgamma
      exact (Finset.mem_filter.mp hgamma).2
    · intro gamma hgamma
      exact hagreement gamma (hsub hgamma)
    · exact ContactProperCutSeedCount.noLargeSelectedPencil_mono
        selected Gamma _ w errors hsub hnoPencil
  calc
    Gamma.card * gap ^ 2 ≤
        (∑ g : ContactOriginalRegularSeedCount.GeometricFactor K F,
          (ContactOriginalRegularSeedCount.geometricSeeds K F selected Gamma g).card) *
          gap ^ 2 := Nat.mul_le_mul_right _
      (ContactOriginalRegularSeedCount.card_le_sum_geometricSeeds
        K F hF.ne_zero selected Gamma hsolutions)
    _ = ∑ g : ContactOriginalRegularSeedCount.GeometricFactor K F,
        (ContactOriginalRegularSeedCount.geometricSeeds K F selected Gamma g).card *
          gap ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ∑ g : ContactOriginalRegularSeedCount.GeometricFactor K F,
        shearedWholeNumerator (degreeVector g.1) :=
      Finset.sum_le_sum (fun g _ ↦ hcount g)
    _ ≤ shearedWholeNumerator (originalDegreeVector K F) :=
      sum_shearedWhole_geometricFactors_le K F hF.ne_zero

end
end ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount6533

#print axioms ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount6533.sum_shearedWhole_geometricFactors_le
#print axioms ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount6533.original_regular_seed_bound

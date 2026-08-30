import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.L0
import ProximityPrize.SubmissionLower.AD
import ProximityPrize.SubmissionLower.B2
namespace ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount
open scoped Classical BigOperators
open ContactAlignmentParameters ContactCountingCaps ContactCountingLedger
open ContactGenericInitialPoint ContactGenericSurface ContactGeometricFirstTail
open ContactGeometricFactorCover ContactRegularFactorGate ContactFactorCaps
open ContactSurfaceSeedCount ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactPolynomialSolutions ContactInterpolation ContactTranslation
open ContactJointSurfaceSeedCount ContactJointSeedCaps
noncomputable section
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
def originalDegreeVector (F:MvPolynomial (Fin 4) K):DegreeVector:=
 ⟨F.degreeOf 1,F.degreeOf 2,F.degreeOf 3⟩
theorem selectedPoint_eq_initialPoint (selected:K → Polynomial K) (γ:K):
   selectedPoint (polynomialEmbedding K) selected γ=
     fun i:Fin 3 => initialPoint K (selected γ) γ i.succ:=rfl
theorem selectedPoint_surface_evaluation
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (γ:K):
   MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
     (surfaceMap (polynomialEmbedding K) F)=
       polynomialEmbedding K (specialization K (selected γ) γ F):=by
 rw [selectedPoint_eq_initialPoint]
 simpa only [canonical_geometricSurfaceMap] using
   eval_at_actual_generic_initial_point K (selected γ) γ F
theorem selectedPoint_regular_of_specialization
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (γ:K)
   (hregular:specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   MvPolynomial.eval₂Hom ((polynomialEmbedding K).comp Polynomial.C)
     (polynomialPoint ((polynomialEmbedding K).comp Polynomial.C)
       (selected γ) γ ((polynomialEmbedding K) Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0:=
 (initialPoint_regular_iff K F (selected γ) γ).mpr hregular
abbrev GeometricFactor (F:MvPolynomial (Fin 4) K):=
 {g:MvPolynomial (Fin 3) (GenericField K)//g∈surfaceFactors (polynomialEmbedding K) F}
def geometricSeeds (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (g:GeometricFactor K F):Finset K:=by
 classical
 exact Γ.filter (fun γ =>
   MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ) g.1=0)
theorem geometricSeeds_subset
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (g:GeometricFactor K F):geometricSeeds K F selected Γ g ⊆ Γ:=by
 classical
 exact Finset.filter_subset _ _
theorem card_le_sum_geometricSeeds
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (selected:K → Polynomial K) (Γ:Finset K)
   (hsolutions:∀ γ∈Γ,specialization K (selected γ) γ F=0):
   Γ.card ≤ ∑ g:GeometricFactor K F,(geometricSeeds K F selected Γ g).card:=by
 classical
 have hcover:Γ ⊆ Finset.univ.biUnion (geometricSeeds K F selected Γ):=by
   intro γ hγ
   have hz:MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
       (surfaceMap (polynomialEmbedding K) F)=0:=by
     rw [selectedPoint_surface_evaluation,hsolutions γ hγ,map_zero]
   obtain ⟨g,hg,hzg⟩:=exists_surfaceFactor_zero (polynomialEmbedding K)
     (polynomialEmbedding_injective K) F hF
     (selectedPoint (polynomialEmbedding K) selected γ) hz
   exact Finset.mem_biUnion.mpr ⟨⟨g,hg⟩,Finset.mem_univ _,
     Finset.mem_filter.mpr ⟨hγ,hzg⟩⟩
 exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
theorem geometricFactor_degree_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (g:GeometricFactor K F) (i:Fin 3):
   g.1.degreeOf i ≤ F.degreeOf i.succ:=by
 have hdiv:=(surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2).2
 exact (coordinate_degree_le_of_dvd i g.1 _ hdiv
   (surfaceMap_ne_zero (polynomialEmbedding K) (polynomialEmbedding_injective K) F hF)).trans
     (surfaceMap_degreeOf_le (polynomialEmbedding K) F i)
theorem geometricFactor_sum_degree_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (i:Fin 3):
   (∑ g:GeometricFactor K F,g.1.degreeOf i) ≤ F.degreeOf i.succ:=by
 classical
 have hb:=surfaceFactors_degree_budget (polynomialEmbedding K)
   (polynomialEmbedding_injective K) F hF i
 rw [←Finset.sum_attach (surfaceFactors (polynomialEmbedding K) F)
   (fun g => g.degreeOf i)] at hb
 simpa only [Finset.attach_eq_univ] using hb
theorem sum_wholeNumerator_geometricFactors_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0):
   (∑ g:GeometricFactor K F,wholeNumerator (degreeVector g.1)) ≤
     wholeNumerator (originalDegreeVector K F):=by
 classical
 rw [←whole_sum (fun g:GeometricFactor K F => degreeVector g.1)]
 rw [whole_eq_dot,whole_eq_dot]
 exact dot_mono_left _ ⟨geometricFactor_sum_degree_le K F hF 0,
   geometricFactor_sum_degree_le K F hF 1,geometricFactor_sum_degree_le K F hF 2⟩
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount

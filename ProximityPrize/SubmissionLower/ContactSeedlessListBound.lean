import ProximityPrize.SubmissionLower.ContactSeedlessInterpolation
import ProximityPrize.SubmissionLower.ContactSeedlessProperCut
import ProximityPrize.SubmissionLower.ContactOriginalRegularSeedCount
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition

namespace ProximityPrize.SubmissionLower.ContactSeedlessListBound

open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactTranslation ContactInterpolation ContactPolynomialSolutions
open ContactFactorCaps ContactImplicitContactLift ContactTaylorNumerators
open ContactGenericSurface ContactGenericInitialPoint ContactGeometricFirstTail
open ContactGeometricFactorCover ContactRegularFactorGate
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactOriginalRegularSeedCount ContactSingularAuxiliary
open ContactSingularDegreeBounds
open ContactSelectedSeedDecomposition
open ContactSeedlessInterpolation
open ContactSeedlessPrimeIncidence ContactSeedlessProperCut
open ActualCoordinateDegreeSum

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

variable (K : Type) [Field K]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)

def geometricPolynomials (F : MvPolynomial (Fin 4) K)
    (Gamma : Finset (Polynomial K)) (g : GeometricFactor K F) :
    Finset (Polynomial K) := by
  classical
  exact Gamma.filter (fun S =>
    MvPolynomial.eval (seedlessPoint (polynomialEmbedding K) S) g.1 = 0)

theorem geometricPolynomials_subset
    (F : MvPolynomial (Fin 4) K) (Gamma : Finset (Polynomial K))
    (g : GeometricFactor K F) : geometricPolynomials K F Gamma g ⊆ Gamma := by
  classical
  exact Finset.filter_subset _ _

theorem card_le_sum_geometricPolynomials
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (Gamma : Finset (Polynomial K))
    (hsolutions : ∀ S ∈ Gamma, specialization K S 0 F = 0) :
    Gamma.card ≤ ∑ g : GeometricFactor K F,
      (geometricPolynomials K F Gamma g).card := by
  classical
  have hcover : Gamma ⊆ Finset.univ.biUnion (geometricPolynomials K F Gamma) := by
    intro S hS
    have hz : MvPolynomial.eval (seedlessPoint (polynomialEmbedding K) S)
        (surfaceMap (polynomialEmbedding K) F) = 0 := by
      rw [seedlessPoint_surface_evaluation,
        eval_polynomialPoint_eq_specialization, hsolutions S hS]
      simp
    obtain ⟨g, hg, hzg⟩ := exists_surfaceFactor_zero (polynomialEmbedding K)
      (polynomialEmbedding_injective K) F hF
      (seedlessPoint (polynomialEmbedding K) S) hz
    exact Finset.mem_biUnion.mpr ⟨⟨g, hg⟩, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hS, hzg⟩⟩
  exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le

theorem geometric_seedless_cut_proper
    (g : MvPolynomial (Fin 3) (GenericField K))
    (hR : 0 < g.degreeOf 1) :
    ¬ g ∣ (seedlessCut : MvPolynomial (Fin 3) (GenericField K)) := by
  intro hdvd
  have hle := coordinate_degree_le_of_dvd 1 g seedlessCut hdvd
    (by simp [seedlessCut])
  have hx : (seedlessCut : MvPolynomial (Fin 3) (GenericField K)).degreeOf 1 = 0 := by
    simp [seedlessCut, MvPolynomial.degreeOf_X_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  rw [hx] at hle
  omega

def yProjection (T : Type*) [Field T] :
    MvPolynomial (Fin 3) T →+* Polynomial T :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 0, 0]

def yEmbedding (T : Type*) [Field T] :
    Polynomial T →+* MvPolynomial (Fin 3) T :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)

theorem y_only_vars {T : Type*} [Field T]
    (S : MvPolynomial (Fin 3) T)
    (hR : S.degreeOf 1 = 0) (hZ : S.degreeOf 2 = 0)
    (i : Fin 3) (hi : i ∈ S.vars) : i = 0 := by
  fin_cases i
  · rfl
  · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hR)
  · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hZ)

theorem yProjection_reconstruct {T : Type*} [Field T]
    (S : MvPolynomial (Fin 3) T)
    (hR : S.degreeOf 1 = 0) (hZ : S.degreeOf 2 = 0) :
    yEmbedding T (yProjection T S) = S := by
  change ((yEmbedding T).comp (yProjection T)) S = (RingHom.id _) S
  apply MvPolynomial.hom_congr_vars
  · ext a
    simp [yEmbedding, yProjection]
  · intro i hi _
    rw [y_only_vars S hR hZ i hi]
    simp [yEmbedding, yProjection]
  · rfl

theorem yProjection_nonzero {T : Type*} [Field T]
    (S : MvPolynomial (Fin 3) T) (hS : S ≠ 0)
    (hR : S.degreeOf 1 = 0) (hZ : S.degreeOf 2 = 0) :
    yProjection T S ≠ 0 := by
  intro hz
  apply hS
  rw [← yProjection_reconstruct S hR hZ, hz, map_zero]

theorem yProjection_natDegree_le {T : Type*} [Field T]
    (S : MvPolynomial (Fin 3) T) :
    (yProjection T S).natDegree ≤ S.degreeOf 0 := by
  classical
  have hsum : yProjection T S =
      ∑ d ∈ S.support, yProjection T (MvPolynomial.monomial d (S.coeff d)) := by
    rw [← map_sum, MvPolynomial.support_sum_monomial_coeff]
  rw [hsum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  have hmono : (yProjection T (MvPolynomial.monomial d (S.coeff d))).natDegree ≤
      d 0 := by
    have heq : MvPolynomial.monomial d (S.coeff d) =
        MvPolynomial.C (S.coeff d) * MvPolynomial.X 0 ^ d 0 *
          MvPolynomial.X 1 ^ d 1 * MvPolynomial.X 2 ^ d 2 := by
      exact ContactExceptionalSeedCount.monomial_fin3 d (S.coeff d)
    rw [heq]
    by_cases h1 : d 1 = 0 <;> by_cases h2 : d 2 = 0 <;>
      simp [yProjection, h1, h2]
    have hc : (Polynomial.C (S.coeff d)).natDegree ≤ 0 := by simp
    have hx : ((Polynomial.X : Polynomial T) ^ d 0).natDegree ≤ d 0 := by simp
    simpa only [Nat.zero_add] using Polynomial.natDegree_mul_le_of_le hc hx
  exact hmono.trans (MvPolynomial.monomial_le_degreeOf 0 hd)

theorem yProjection_eval {T : Type*} [Field T]
    (S : MvPolynomial (Fin 3) T)
    (hR : S.degreeOf 1 = 0) (hZ : S.degreeOf 2 = 0)
    (v : Fin 3 → T) :
    (yProjection T S).eval (v 0) = MvPolynomial.eval v S := by
  change ((Polynomial.evalRingHom (v 0)).comp (yProjection T)) S =
    (MvPolynomial.eval v) S
  apply MvPolynomial.hom_congr_vars
  · ext a
    simp [yProjection]
  · intro i hi _
    rw [y_only_vars S hR hZ i hi]
    simp [yProjection]
  · rfl

def yWeights : Fin 4 → ℕ := ![0, 1, 0, 0]
def zWeights : Fin 4 → ℕ := ![0, 0, 0, 1]

theorem degreeY_le_yWeight (Q : MvPolynomial (Fin 4) K) :
    Q.degreeOf 1 ≤ MvPolynomial.weightedTotalDegree yWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree yWeights hd
  rw [weight_fin4] at h
  simpa [yWeights] using h

theorem degreeZ_le_zWeight (Q : MvPolynomial (Fin 4) K) :
    Q.degreeOf 3 ≤ MvPolynomial.weightedTotalDegree zWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree zWeights hd
  rw [weight_fin4] at h
  simpa [zWeights] using h

def singularPolynomials (Q : MvPolynomial (Fin 4) K)
    (Gamma : Finset (Polynomial K)) : Finset (Polynomial K) := by
  classical
  exact Gamma.filter (fun S => specialization K S 0 (singularAuxiliary Q) = 0)

def regularPolynomials (Q : MvPolynomial (Fin 4) K)
    (Gamma : Finset (Polynomial K)) (F : ↥(positiveRFactors Q)) :
    Finset (Polynomial K) := by
  classical
  exact Gamma.filter (fun S => RegularSolution F.1 S 0)

theorem seedless_solution_cover
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (Gamma : Finset (Polynomial K))
    (hsolutions : ∀ S ∈ Gamma, specialization K S 0 Q = 0) :
    Gamma.card ≤ (singularPolynomials K Q Gamma).card +
      ∑ F : ↥(positiveRFactors Q), (regularPolynomials K Q Gamma F).card := by
  classical
  let regularUnion := Finset.univ.biUnion (regularPolynomials K Q Gamma)
  have hcover : Gamma ⊆ singularPolynomials K Q Gamma ∪ regularUnion := by
    intro S hS
    obtain hsing | ⟨F, hF, hreg⟩ := solution_regular_or_auxiliary
      Q hQ S 0 (hsolutions S hS)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS, hsing⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨⟨F, hF⟩, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hS, hreg⟩⟩
  calc
    Gamma.card ≤ (singularPolynomials K Q Gamma ∪ regularUnion).card :=
      Finset.card_le_card hcover
    _ ≤ (singularPolynomials K Q Gamma).card + regularUnion.card :=
      Finset.card_union_le _ _
    _ ≤ (singularPolynomials K Q Gamma).card +
        ∑ F : ↥(positiveRFactors Q), (regularPolynomials K Q Gamma F).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _

end

end ProximityPrize.SubmissionLower.ContactSeedlessListBound

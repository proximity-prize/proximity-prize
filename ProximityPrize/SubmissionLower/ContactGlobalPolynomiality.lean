import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactPolynomiality
import ProximityPrize.SubmissionLower.ContactTranslation

/-!
# Global polynomial reconstruction from a weighted contact equation

Model label: gpt-5.

This module discharges the substituted-degree premise in ContactPolynomiality
using the actual weighted support box. Translation back from the initial
point gives a genuine polynomial in the original X coordinate, with the
prescribed value and derivative. Geometric counting is a separate obligation.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalPolynomiality

open ContactDifferentialRing ContactRegularPoint ContactPolynomiality
open DifferentialTaylorCoefficients ContactInterpolation ContactTranslation

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable {K L : Type*} [Field K] [Field L]

theorem derivative_taylor (r : L) (P : Polynomial L) :
    (Polynomial.taylor r P).derivative = Polynomial.taylor r P.derivative := by
  simp [Polynomial.taylor_apply, Polynomial.derivative_comp]

/-- Translating the actual reconstructed equation restores the original
independent variable and commutes with the actual polynomial derivative. -/
theorem taylor_reconstruction_eq_specialization
    (coefficients : K →+* L) (F : Poly4 K) (v : Fin 4 → L) (P : Polynomial L) :
    Polynomial.taylor (-(v 0))
        (MvPolynomial.eval₂Hom (Polynomial.C.comp coefficients)
          (reconstructionSubstitution v P) F) =
      specialization L (Polynomial.taylor (-(v 0)) P) (v 3)
        (MvPolynomial.map coefficients F) := by
  have hhom :
      (Polynomial.taylorAlgHom (-(v 0))).toRingHom.comp
          (MvPolynomial.eval₂Hom (Polynomial.C.comp coefficients)
            (reconstructionSubstitution v P)) =
        (specialization L (Polynomial.taylor (-(v 0)) P) (v 3)).toRingHom.comp
          (MvPolynomial.map coefficients) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply, reconstructionSubstitution, specialization]
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, reconstructionSubstitution, specialization,
          derivative_taylor]
  exact DFunLike.congr_fun hhom F

theorem map_mem_globalCoefficientBox
    (coefficients : K →+* L) (F : Poly4 K) (bound w seedCap slopeCap : ℕ)
    (hcaps : F ∈ globalCoefficientBox K bound w seedCap slopeCap) :
    MvPolynomial.map coefficients F ∈ globalCoefficientBox L bound w seedCap slopeCap := by
  intro d hd
  exact hcaps (MvPolynomial.support_map_subset coefficients F hd)

noncomputable def globalPolynomial
    (coefficients : K →+* L) (F : Poly4 K) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coefficients v F = 0)
    (hregular : MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) (w : ℕ) : Polynomial L :=
  Polynomial.taylor (-(v 0)) (reconstructedPolynomial coefficients F v hF hregular w)

theorem globalPolynomial_natDegree_le
    (coefficients : K →+* L) (F : Poly4 K) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coefficients v F = 0)
    (hregular : MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) (w : ℕ) :
    (globalPolynomial coefficients F v hF hregular w).natDegree ≤ w := by
  simpa only [globalPolynomial, Polynomial.natDegree_taylor] using
    reconstructedPolynomial_natDegree_le coefficients F v hF hregular w

theorem globalPolynomial_eval
    (coefficients : K →+* L) (F : Poly4 K) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coefficients v F = 0)
    (hregular : MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) (w : ℕ) (x : L) :
    (globalPolynomial coefficients F v hF hregular w).eval x =
      (reconstructedPolynomial coefficients F v hF hregular w).eval (x - v 0) := by
  simp only [globalPolynomial, Polynomial.taylor_eval, sub_eq_add_neg]

theorem globalPolynomial_initial_value
    (coefficients : K →+* L) (F : Poly4 K) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coefficients v F = 0)
    (hregular : MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) (w : ℕ) :
    (globalPolynomial coefficients F v hF hregular w).eval (v 0) = v 1 := by
  rw [globalPolynomial_eval, sub_self, ← Polynomial.taylor_coeff_zero (0 : L),
    Polynomial.taylor_zero]
  exact reconstructedPolynomial_coeff_zero coefficients F v hF hregular w

theorem globalPolynomial_initial_slope
    (coefficients : K →+* L) (F : Poly4 K) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coefficients v F = 0)
    (hregular : MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) (w : ℕ) (hw : 1 ≤ w) :
    (globalPolynomial coefficients F v hF hregular w).derivative.eval (v 0) = v 2 := by
  rw [globalPolynomial, derivative_taylor, Polynomial.taylor_eval, add_neg_cancel]
  rw [← Polynomial.taylor_coeff_one (0 : L), Polynomial.taylor_zero]
  exact reconstructedPolynomial_coeff_one coefficients F v hF hregular w hw

/-- The actual support inequalities supply the previously explicit degree
premise. No vanishing or geometric assertion is needed for this lemma. -/
theorem reconstructedEquation_natDegree_lt
    (coefficients : K →+* L) (F : Poly4 K) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coefficients v F = 0)
    (hregular : MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (bound w seedCap slopeCap : ℕ) (hbound : 0 < bound)
    (hcaps : F ∈ globalCoefficientBox K bound w seedCap slopeCap) :
    (reconstructedEquation coefficients F v hF hregular w).natDegree < bound := by
  have hdeg := specialization_natDegree_lt L bound w seedCap slopeCap
    (MvPolynomial.map coefficients F) (globalPolynomial coefficients F v hF hregular w)
    (v 3) hbound (map_mem_globalCoefficientBox coefficients F bound w seedCap slopeCap hcaps)
    (globalPolynomial_natDegree_le coefficients F v hF hregular w)
  have heq := taylor_reconstruction_eq_specialization coefficients F v
    (reconstructedPolynomial coefficients F v hF hregular w)
  change Polynomial.taylor (-(v 0)) (reconstructedEquation coefficients F v hF hregular w) =
    specialization L (globalPolynomial coefficients F v hF hregular w) (v 3)
      (MvPolynomial.map coefficients F) at heq
  rw [← heq, Polynomial.natDegree_taylor] at hdeg
  exact hdeg

/-- Actual all-tail equations imply a genuine polynomial solution in the
original X coordinate; the weighted degree cap is discharged internally. -/
theorem global_polynomiality_of_all_tails
    (coefficients : K →+* L) (F : Poly4 K) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coefficients v F = 0)
    (hregular : MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (p bound w seedCap slopeCap : ℕ) [CharP L p] (hw : 1 ≤ w)
    (hshort : w + 1 ≤ bound) (hchar : bound < p)
    (hcaps : F ∈ globalCoefficientBox K bound w seedCap slopeCap)
    (htails : ∀ j, w < j → j ≤ bound →
      jetCoefficient (contactDerivation K F)
        (regularPointValue coefficients F v hF hregular)
        (contactCoordinate K F (1 : Fin 4)) j = 0) :
    specialization L (globalPolynomial coefficients F v hF hregular w) (v 3)
      (MvPolynomial.map coefficients F) = 0 := by
  have hdegree := reconstructedEquation_natDegree_lt coefficients F v hF hregular
    bound w seedCap slopeCap (by omega) hcaps
  have hzero := polynomiality_of_all_tails coefficients F v hF hregular p bound w
    hw hshort hchar htails hdegree
  have heq := taylor_reconstruction_eq_specialization coefficients F v
    (reconstructedPolynomial coefficients F v hF hregular w)
  change Polynomial.taylor (-(v 0)) (reconstructedEquation coefficients F v hF hregular w) =
    specialization L (globalPolynomial coefficients F v hF hregular w) (v 3)
      (MvPolynomial.map coefficients F) at heq
  rw [← heq, hzero, map_zero]

theorem exists_global_polynomial_of_all_tails
    (coefficients : K →+* L) (F : Poly4 K) (v : Fin 4 → L)
    (hF : MvPolynomial.eval₂Hom coefficients v F = 0)
    (hregular : MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (p bound w seedCap slopeCap : ℕ) [CharP L p] (hw : 1 ≤ w)
    (hshort : w + 1 ≤ bound) (hchar : bound < p)
    (hcaps : F ∈ globalCoefficientBox K bound w seedCap slopeCap)
    (htails : ∀ j, w < j → j ≤ bound →
      jetCoefficient (contactDerivation K F)
        (regularPointValue coefficients F v hF hregular)
        (contactCoordinate K F (1 : Fin 4)) j = 0) :
    ∃ P : Polynomial L, P.natDegree ≤ w ∧
      specialization L P (v 3) (MvPolynomial.map coefficients F) = 0 ∧
      P.eval (v 0) = v 1 ∧ P.derivative.eval (v 0) = v 2 := by
  refine ⟨globalPolynomial coefficients F v hF hregular w,
    globalPolynomial_natDegree_le coefficients F v hF hregular w, ?_,
    globalPolynomial_initial_value coefficients F v hF hregular w,
    globalPolynomial_initial_slope coefficients F v hF hregular w hw⟩
  exact global_polynomiality_of_all_tails coefficients F v hF hregular p bound w seedCap
    slopeCap hw hshort hchar hcaps htails

end

end ProximityPrize.SubmissionLower.ContactGlobalPolynomiality

#print axioms ProximityPrize.SubmissionLower.ContactGlobalPolynomiality.taylor_reconstruction_eq_specialization
#print axioms ProximityPrize.SubmissionLower.ContactGlobalPolynomiality.map_mem_globalCoefficientBox
#print axioms ProximityPrize.SubmissionLower.ContactGlobalPolynomiality.globalPolynomial_initial_value
#print axioms ProximityPrize.SubmissionLower.ContactGlobalPolynomiality.globalPolynomial_initial_slope
#print axioms ProximityPrize.SubmissionLower.ContactGlobalPolynomiality.reconstructedEquation_natDegree_lt
#print axioms ProximityPrize.SubmissionLower.ContactGlobalPolynomiality.global_polynomiality_of_all_tails
#print axioms ProximityPrize.SubmissionLower.ContactGlobalPolynomiality.exists_global_polynomial_of_all_tails

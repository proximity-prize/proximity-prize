import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualCurveCoordinateField

import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_MvPolynomial_Localization



/-!
# Ordered trivariate collection and actual-component Gauss localization

Model label: gpt-5.

Any ordering of the three original coordinates collects its first variable
into K[T] and leaves the other two as polynomial variables. Coefficients
are then localized into the actual RatFunc K.

For an irreducible g in an actual prime component, transcendence of the
selected coordinate proves denominator disjointness by evaluation in the
actual quotient fraction field. Hence irreducibility and proper
divisibility survive localization. No separate positive-other-degree or
generic-projection hypothesis is assumed.

Conversion to nested bivariate polynomials, numerical degree caps, and the
final summed geometric budget are separate later steps.
-/

namespace ProximityPrize.SubmissionLower.TrivariateRationalCollection

open ActualCurveCoordinateField

noncomputable section

variable (K : Type) [Field K]

abbrev Original := MvPolynomial (Fin 3) K
abbrev Collected := MvPolynomial (Fin 2) (Polynomial K)
abbrev RationalPolynomials := MvPolynomial (Fin 2) (RatFunc K)

def collectFirst : Original K ≃ₐ[K] Collected K :=
  (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 2)).trans
    (MvPolynomial.optionEquivRight K (Fin 2))

/-- The ordering maps the new ordered coordinates to their original labels. -/
def collect (order : Fin 3 ≃ Fin 3) : Original K ≃ₐ[K] Collected K :=
  (MvPolynomial.renameEquiv K order.symm).trans (collectFirst K)

@[simp] theorem collect_C (order : Fin 3 ≃ Fin 3) (a : K) :
    collect K order (MvPolynomial.C a) = MvPolynomial.C (Polynomial.C a) := by
  simp [collect, collectFirst, MvPolynomial.renameEquiv_apply]

@[simp] theorem collect_X_first (order : Fin 3 ≃ Fin 3) :
    collect K order (MvPolynomial.X (order 0)) = MvPolynomial.C Polynomial.X := by
  simp [collect, collectFirst, MvPolynomial.renameEquiv_apply]

@[simp] theorem collect_X_other (order : Fin 3 ≃ Fin 3) (j : Fin 2) :
    collect K order (MvPolynomial.X (order j.succ)) = MvPolynomial.X j := by
  simp [collect, collectFirst, MvPolynomial.renameEquiv_apply]

def coefficientLift (order : Fin 3 ≃ Fin 3) : Polynomial K →+* Original K :=
  (collect K order).symm.toRingHom.comp MvPolynomial.C

@[simp] theorem coefficientLift_C (order : Fin 3 ≃ Fin 3) (a : K) :
    coefficientLift K order (Polynomial.C a) = MvPolynomial.C a := by
  apply (collect K order).injective
  simp [coefficientLift]

@[simp] theorem coefficientLift_X (order : Fin 3 ≃ Fin 3) :
    coefficientLift K order Polynomial.X = MvPolynomial.X (order 0) := by
  apply (collect K order).injective
  simp [coefficientLift]

def rationalMap (order : Fin 3 ≃ Fin 3) : Original K →+* RationalPolynomials K :=
  (MvPolynomial.map (algebraMap (Polynomial K) (RatFunc K))).comp
    (collect K order).toRingHom

theorem rationalMap_injective (order : Fin 3 ≃ Fin 3) :
    Function.Injective (rationalMap K order) :=
  (MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).comp
    (collect K order).injective

theorem rationalMap_ne_zero (order : Fin 3 ≃ Fin 3) (F : Original K) (hF : F ≠ 0) :
    rationalMap K order F ≠ 0 := by
  intro h
  apply hF
  apply rationalMap_injective K order
  simpa only [map_zero] using h

attribute [local instance] MvPolynomial.algebraMvPolynomial

def coefficientDenominators : Submonoid (Collected K) :=
  (nonZeroDivisors (Polynomial K)).map MvPolynomial.C

local instance : IsLocalization (coefficientDenominators K) (RationalPolynomials K) :=
  MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)

theorem rationalMap_eq (order : Fin 3 ≃ Fin 3) (F : Original K) :
    rationalMap K order F =
      algebraMap (Collected K) (RationalPolynomials K) (collect K order F) := rfl

theorem collected_principal_isPrime (order : Fin 3 ≃ Fin 3)
    (G : Original K) (hG : Irreducible G) :
    (Ideal.span ({collect K order G} : Set (Collected K))).IsPrime := by
  have hi : Irreducible (collect K order G) :=
    (MulEquiv.irreducible_iff (collect K order)).mpr hG
  exact Ideal.isPrime_span_singleton_of_prime hi.prime

section ActualComponent

variable (order : Fin 3 ≃ Fin 3) (P : Ideal (Original K)) [P.IsPrime]

def collectedEvaluation : Collected K →+* CoordinateField K P :=
  (coordinateEvaluation K P).toRingHom.comp (collect K order).symm.toRingHom

@[simp] theorem collectedEvaluation_collect (F : Original K) :
    collectedEvaluation K order P (collect K order F) = coordinateEvaluation K P F := by
  simp [collectedEvaluation]

/-- The actual coefficient map is polynomial evaluation at the selected
original coordinate, proved on C and X. -/
@[simp] theorem collectedEvaluation_C (H : Polynomial K) :
    collectedEvaluation K order P (MvPolynomial.C H) =
      Polynomial.aeval (coordinate K P (order 0)) H := by
  have hhom : (coordinateEvaluation K P).toRingHom.comp (coefficientLift K order) =
      (Polynomial.aeval (coordinate K P (order 0))).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change coordinateEvaluation K P (coefficientLift K order (Polynomial.C a)) =
        Polynomial.aeval (coordinate K P (order 0)) (Polynomial.C a)
      rw [coefficientLift_C, Polynomial.aeval_C]
      exact MvPolynomial.algHom_C (coordinateEvaluation K P) a
    · change coordinateEvaluation K P (coefficientLift K order Polynomial.X) =
        Polynomial.aeval (coordinate K P (order 0)) Polynomial.X
      rw [coefficientLift_X, Polynomial.aeval_X]
      rfl
  exact RingHom.congr_fun hhom H

/-- A nonzero coefficient denominator cannot lie in the principal ideal
of an actual component equation: that would annihilate the actual
transcendental coordinate by a nonzero polynomial. -/
theorem coefficientDenominators_disjoint_of_component
    (G : Original K) (hmem : G ∈ P)
    (ht : Transcendental K (coordinate K P (order 0))) :
    Disjoint (coefficientDenominators K : Set (Collected K))
      (Ideal.span ({collect K order G} : Set (Collected K)) : Set (Collected K)) := by
  have hGzero : coordinateEvaluation K P G = 0 := by
    change G ∈ RingHom.ker (coordinateEvaluation K P).toRingHom
    rw [coordinateEvaluation_ker]
    exact hmem
  rw [Set.disjoint_left]
  intro a ha hI
  obtain ⟨H, hH, rfl⟩ := Submonoid.mem_map.mp ha
  have hH0 : H ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hH
  obtain ⟨U, hU⟩ := Ideal.mem_span_singleton.mp hI
  have hroot : Polynomial.aeval (coordinate K P (order 0)) H = 0 := by
    have heval := congrArg (collectedEvaluation K order P) hU
    simpa only [map_mul, collectedEvaluation_collect, collectedEvaluation_C,
      hGzero, zero_mul] using heval
  exact hH0 (transcendental_iff.mp ht H hroot)

theorem localized_principal_isPrime_of_component
    (G : Original K) (hG : Irreducible G) (hmem : G ∈ P)
    (ht : Transcendental K (coordinate K P (order 0))) :
    (Ideal.span ({rationalMap K order G} : Set (RationalPolynomials K))).IsPrime := by
  have hp := IsLocalization.isPrime_of_isPrime_disjoint
    (coefficientDenominators K) (RationalPolynomials K)
    (Ideal.span ({collect K order G} : Set (Collected K)))
    (collected_principal_isPrime K order G hG)
    (coefficientDenominators_disjoint_of_component K order P G hmem ht)
  simpa only [Ideal.map_span, Set.image_singleton, ← rationalMap_eq] using hp

/-- Actual Gauss irreducibility, with denominator disjointness DERIVED
from the actual prime and transcendental coordinate. -/
theorem rationalMap_irreducible_of_component
    (G : Original K) (hG : Irreducible G) (hmem : G ∈ P)
    (ht : Transcendental K (coordinate K P (order 0))) :
    Irreducible (rationalMap K order G) := by
  exact ((Ideal.span_singleton_prime (rationalMap_ne_zero K order G hG.ne_zero)).mp
    (localized_principal_isPrime_of_component K order P G hG hmem ht)).irreducible

/-- The actual localized principal prime contracts to the original one,
so a proper cut remains proper over the selected rational-function base. -/
theorem rationalMap_dvd_iff_of_component
    (G H : Original K) (hG : Irreducible G) (hmem : G ∈ P)
    (ht : Transcendental K (coordinate K P (order 0))) :
    rationalMap K order G ∣ rationalMap K order H ↔ G ∣ H := by
  constructor
  · intro hdiv
    have hm : algebraMap (Collected K) (RationalPolynomials K) (collect K order H) ∈
        Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
          (Ideal.span ({collect K order G} : Set (Collected K))) := by
      simpa only [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton,
        ← rationalMap_eq] using hdiv
    have hu : collect K order H ∈
        (Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
          (Ideal.span ({collect K order G} : Set (Collected K)))).under (Collected K) := hm
    rw [IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K)
      (RationalPolynomials K) (collected_principal_isPrime K order G hG)
      (coefficientDenominators_disjoint_of_component K order P G hmem ht)] at hu
    obtain ⟨U, hU⟩ := Ideal.mem_span_singleton.mp hu
    refine ⟨(collect K order).symm U, ?_⟩
    apply (collect K order).injective
    simpa only [map_mul, AlgEquiv.apply_symm_apply] using hU
  · intro hdiv
    exact map_dvd (rationalMap K order) hdiv

theorem rationalMap_proper_of_component
    (G H : Original K) (hG : Irreducible G) (hmem : G ∈ P)
    (ht : Transcendental K (coordinate K P (order 0))) (hproper : ¬ G ∣ H) :
    ¬ rationalMap K order G ∣ rationalMap K order H := by
  intro h
  exact hproper ((rationalMap_dvd_iff_of_component K order P G H hG hmem ht).mp h)

end ActualComponent

end


end ProximityPrize.SubmissionLower.TrivariateRationalCollection

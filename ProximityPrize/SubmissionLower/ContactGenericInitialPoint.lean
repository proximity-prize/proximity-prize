import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactPolynomialRecovery



/-!
# One actual generic initial coordinate for every selected solution

Model label: gpt-5.

The point is constructed in the algebraic closure of the fraction field
of K[X]. Evaluation at it is the actual injective polynomial embedding.
Thus every nonzero regularity polynomial stays nonzero simultaneously,
and retaining only value and seed still identifies the original polynomial
and seed. No generic-point existence or injectivity premise is assumed.
-/

namespace ProximityPrize.SubmissionLower.ContactGenericInitialPoint

open ContactDifferentialRing ContactRegularPoint ContactPolynomiality
open ContactPolynomialSolutions ContactPolynomialRecovery ContactGlobalPolynomiality
open ContactTaylorNumerators ContactTranslation

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

variable (K : Type*) [Field K]

abbrev RationalBase := FractionRing (Polynomial K)
abbrev GenericField := AlgebraicClosure (RationalBase K)

def polynomialEmbedding : Polynomial K →+* GenericField K :=
  (algebraMap (RationalBase K) (GenericField K)).comp
    (algebraMap (Polynomial K) (RationalBase K))

def coefficientEmbedding : K →+* GenericField K :=
  (polynomialEmbedding K).comp Polynomial.C

def initialCoordinate : GenericField K := polynomialEmbedding K Polynomial.X

theorem polynomialEmbedding_injective : Function.Injective (polynomialEmbedding K) :=
  (algebraMap (RationalBase K) (GenericField K)).injective.comp
    (IsFractionRing.injective (Polynomial K) (RationalBase K))

theorem coefficientEmbedding_injective : Function.Injective (coefficientEmbedding K) :=
  (coefficientEmbedding K).injective

theorem genericField_isAlgClosed : IsAlgClosed (GenericField K) := by
  infer_instance

theorem genericField_charP (p : ℕ) [CharP K p] : CharP (GenericField K) p := by
  infer_instance

theorem generic_eval_eq (P : Polynomial K) :
    P.eval₂ (coefficientEmbedding K) (initialCoordinate K) = polynomialEmbedding K P := by
  have hhom : Polynomial.eval₂RingHom (coefficientEmbedding K) (initialCoordinate K) =
      polynomialEmbedding K := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [coefficientEmbedding, RingHom.comp_apply]
    · simp [initialCoordinate]
  exact DFunLike.congr_fun hhom P

@[simp] theorem polynomialEmbedding_eq_zero_iff (P : Polynomial K) :
    polynomialEmbedding K P = 0 ↔ P = 0 := by
  constructor
  · intro h
    apply polynomialEmbedding_injective K
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

theorem generic_eval_eq_zero_iff (P : Polynomial K) :
    P.eval₂ (coefficientEmbedding K) (initialCoordinate K) = 0 ↔ P = 0 := by
  rw [generic_eval_eq, polynomialEmbedding_eq_zero_iff]

/-- A single constructed coordinate avoids all nonzero base-field
polynomials, not merely a prescribed finite collection. -/
theorem generic_eval_ne_zero (P : Polynomial K) (hP : P ≠ 0) :
    P.eval₂ (coefficientEmbedding K) (initialCoordinate K) ≠ 0 :=
  (generic_eval_eq_zero_iff K P).not.mpr hP

def initialPoint (P : Polynomial K) (γ : K) : Fin 4 → GenericField K :=
  polynomialPoint (coefficientEmbedding K) P γ (initialCoordinate K)

@[simp] theorem initialPoint_X (P : Polynomial K) (γ : K) :
    initialPoint K P γ 0 = initialCoordinate K := rfl

@[simp] theorem initialPoint_Y (P : Polynomial K) (γ : K) :
    initialPoint K P γ 1 = polynomialEmbedding K P := by
  exact generic_eval_eq K P

@[simp] theorem initialPoint_R (P : Polynomial K) (γ : K) :
    initialPoint K P γ 2 = polynomialEmbedding K P.derivative := by
  exact generic_eval_eq K P.derivative

@[simp] theorem initialPoint_Z (P : Polynomial K) (γ : K) :
    initialPoint K P γ 3 = coefficientEmbedding K γ := rfl

theorem evaluation_at_initialPoint (P : Polynomial K) (γ : K) (Q : Poly4 K) :
    MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ) Q =
      polynomialEmbedding K (specialization K P γ Q) := by
  change MvPolynomial.eval₂Hom (coefficientEmbedding K)
      (polynomialPoint (coefficientEmbedding K) P γ (initialCoordinate K)) Q = _
  rw [eval_polynomialPoint_eq_specialization, generic_eval_eq]

theorem initialPoint_relation (F : Poly4 K) (P : Polynomial K) (γ : K)
    (hsolution : specialization K P γ F = 0) :
    MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ) F = 0 := by
  rw [evaluation_at_initialPoint, hsolution, map_zero]

theorem initialPoint_regular_iff (F : Poly4 K) (P : Polynomial K) (γ : K) :
    MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ)
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0 ↔
      specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0 := by
  simp only [evaluation_at_initialPoint, ne_eq, polynomialEmbedding_eq_zero_iff]

def valueSeedProjection (pair : Polynomial K × K) : GenericField K × GenericField K :=
  (initialPoint K pair.1 pair.2 1, initialPoint K pair.1 pair.2 3)

/-- The slope coordinate can be discarded without identifying two
base-field polynomial/seed pairs at the actual generic initial point. -/
theorem valueSeedProjection_injective : Function.Injective (valueSeedProjection K) := by
  intro a b hab
  have hy := congrArg Prod.fst hab
  have hz := congrArg Prod.snd hab
  simp only [valueSeedProjection, initialPoint_Y, initialPoint_Z] at hy hz
  exact Prod.ext (polynomialEmbedding_injective K hy) (coefficientEmbedding_injective K hz)

theorem initialPoint_injective :
    Function.Injective (fun pair : Polynomial K × K => initialPoint K pair.1 pair.2) := by
  intro a b hab
  apply valueSeedProjection_injective K
  exact Prod.ext (congrFun hab 1) (congrFun hab 3)

theorem selectedProjection_injective {ι : Type*} (seed : ι → K)
    (hseed : Function.Injective seed) (P : ι → Polynomial K) :
    Function.Injective (fun i => valueSeedProjection K (P i, seed i)) := by
  intro a b hab
  have hpair := valueSeedProjection_injective K hab
  exact hseed (congrArg Prod.snd hpair)

theorem initialPoint_all_tail_numerators_zero
    (F : Poly4 K) (P : Polynomial K) (γ : K)
    (hsolution : specialization K P γ F = 0) (w : ℕ) (hdegree : P.natDegree ≤ w) :
    ∀ b, w < b →
      MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ)
        (numerator K F b) = 0 := by
  intro b hb
  exact polynomialPoint_numerator_zero (coefficientEmbedding K) F P γ
    (initialCoordinate K) hsolution b (hdegree.trans_lt hb)

theorem global_recovery_at_initialPoint
    (F : Poly4 K) (P : Polynomial K) (γ : K)
    (hsolution : specialization K P γ F = 0)
    (hregular : specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (p w : ℕ) [CharP K p] (hchar : w < p) (hdegree : P.natDegree ≤ w) :
    globalPolynomial (coefficientEmbedding K) F (initialPoint K P γ)
      (initialPoint_relation K F P γ hsolution)
      ((initialPoint_regular_iff K F P γ).mpr hregular) w =
      P.map (coefficientEmbedding K) := by
  letI : CharP (GenericField K) p := genericField_charP K p
  exact globalPolynomial_eq_map_of_solution (coefficientEmbedding K) F P γ
    (initialCoordinate K) hsolution ((initialPoint_regular_iff K F P γ).mpr hregular)
    p w hchar hdegree

end

end ProximityPrize.SubmissionLower.ContactGenericInitialPoint

import ProximityPrize.SubmissionLower.ContactPolynomialRecovery

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

def initialPoint (P : Polynomial K) (γ : K) : Fin 4 → GenericField K :=
  polynomialPoint (coefficientEmbedding K) P γ (initialCoordinate K)

theorem evaluation_at_initialPoint (P : Polynomial K) (γ : K) (Q : Poly4 K) :
    MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ) Q =
      polynomialEmbedding K (specialization K P γ Q) := by
  change MvPolynomial.eval₂Hom (coefficientEmbedding K)
      (polynomialPoint (coefficientEmbedding K) P γ (initialCoordinate K)) Q = _
  rw [eval_polynomialPoint_eq_specialization, generic_eval_eq]

theorem initialPoint_regular_iff (F : Poly4 K) (P : Polynomial K) (γ : K) :
    MvPolynomial.eval₂Hom (coefficientEmbedding K) (initialPoint K P γ)
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0 ↔
      specialization K P γ (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0 := by
  simp only [evaluation_at_initialPoint, ne_eq, polynomialEmbedding_eq_zero_iff]

end

end ProximityPrize.SubmissionLower.ContactGenericInitialPoint

import ProximityPrize.SubmissionLower.ContactIdentityResidualPrimeTransport

namespace ProximityPrize.SubmissionLower.ContactFieldPlaceTransport

open scoped Classical BigOperators WithZero
open CoordinateBoxZeroCount ActualCurveCoordinateField
open ContactFlagAffineResidualAutomorphism
open ContactIdentityResidualPrimeTransport

noncomputable section

section Places

variable {K L M : Type} [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra K M]

def placeComap (e : L ≃ₐ[K] M) (v : Place K M) : Place K L := by
  refine ⟨v.val.comap e.toRingHom, ?_, ?_⟩
  · exact v.property.1.comp e.surjective
  · refine ⟨?_⟩
    intro a ha
    change v.val (e (algebraMap K L a)) = 1
    rw [e.commutes]
    exact v.property.2.eq_one a ha

def placeEquiv (e : L ≃ₐ[K] M) : Place K M ≃ Place K L where
  toFun := placeComap e
  invFun := placeComap e.symm
  left_inv v := by
    apply Subtype.ext
    ext x
    change v.val (e (e.symm x)) = v.val x
    rw [e.apply_symm_apply]
  right_inv v := by
    apply Subtype.ext
    ext x
    change v.val (e.symm (e x)) = v.val x
    rw [e.symm_apply_apply]

theorem sum_poleOrder_image (e : L ≃ₐ[K] M) (S : Finset (Place K M)) (x : L) :
    (∑ v ∈ S.image (placeComap e), CoordinatePoleMass.poleOrder K L v x) =
      ∑ v ∈ S, CoordinatePoleMass.poleOrder K M v (e x) := by
  classical
  rw [Finset.sum_image]
  · rfl
  · intro v _ w _ h
    exact (placeEquiv e).injective h

theorem finite_pole_bound_transport (e : L ≃ₐ[K] M) (x : L) (cost : ℕ)
    (h : ∀ S : Finset (Place K L),
      (∑ v ∈ S, CoordinatePoleMass.poleOrder K L v x) ≤ (cost : ℤ)) :
    ∀ S : Finset (Place K M),
      (∑ v ∈ S, CoordinatePoleMass.poleOrder K M v (e x)) ≤ (cost : ℤ) := by
  intro S
  rw [← sum_poleOrder_image e S x]
  exact h _

end Places

section Curves

variable {K : Type} [Field K]
variable (P Q : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime] [Q.IsPrime]

def coordinateFieldEquiv (e : MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K)
    (hQ : Q = P.map e.toRingHom) : CoordinateField K P ≃ₐ[K] CoordinateField K Q :=
  IsFractionRing.algEquivOfAlgEquiv (Ideal.quotientEquivAlg P Q e hQ)

omit [P.IsPrime] [Q.IsPrime] in
theorem coordinateFieldEquiv_eval
    (e : MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K)
    (hQ : Q = P.map e.toRingHom) (A : MvPolynomial (Fin 3) K) :
    coordinateFieldEquiv P Q e hQ (coordinateEvaluation K P A) =
      coordinateEvaluation K Q (e A) := by
  simp only [coordinateFieldEquiv, coordinateEvaluation_eq_aeval,
    aeval_coordinate_eq_quotient, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    Ideal.quotientEquivAlg_mk]

omit [P.IsPrime] [Q.IsPrime] in
theorem coordinateFieldEquiv_coordinate
    (e : MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K)
    (hQ : Q = P.map e.toRingHom) (i : Fin 3) :
    coordinateFieldEquiv P Q e hQ (coordinate K P i) =
      coordinateEvaluation K Q (e (MvPolynomial.X i)) :=
  coordinateFieldEquiv_eval P Q e hQ _

omit [P.IsPrime] in
theorem coordinateFieldEquiv_residual_coordinate
    (aY v bY aS bS cS : K) (hv : v ≠ 0)
    (hQ : Q = P.map (residualEquiv aY v bY aS bS cS hv).toRingHom) (i : Fin 3) :
    coordinateFieldEquiv P Q (residualEquiv aY v bY aS bS cS hv) hQ
        (coordinate K P i) =
      forwardResidualPoint (algebraMap K (CoordinateField K Q) aY)
        (algebraMap K (CoordinateField K Q) v)
        (algebraMap K (CoordinateField K Q) bY)
        (algebraMap K (CoordinateField K Q) aS)
        (algebraMap K (CoordinateField K Q) bS)
        (algebraMap K (CoordinateField K Q) cS) (coordinate K Q) i := by
  rw [coordinateFieldEquiv_coordinate]
  fin_cases i <;>
    simp [residualEquiv, residualAlgHom, residualImage, forwardResidualPoint,
      coordinateEvaluation_eq_aeval]

end Curves

end

end ProximityPrize.SubmissionLower.ContactFieldPlaceTransport

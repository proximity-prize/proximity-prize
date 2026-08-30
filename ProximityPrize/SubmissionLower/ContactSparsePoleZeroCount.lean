import ProximityPrize.SubmissionLower.ContactSparsePoleSupport
import ProximityPrize.SubmissionLower.ActualCurveZeroCount

namespace ProximityPrize.SubmissionLower.ContactSparsePoleZeroCount

open scoped Classical BigOperators WithZero
open IsDedekindDomain
open ContactSparsePoleSupport
open CoordinateBoxZeroCount
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveScalarTowers
open ActualCurveZeroCount

noncomputable section

variable {K L σ : Type} [Field K] [Field L] [Fintype σ]
variable [Algebra K L] [IsAlgClosed K]
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L]
variable [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L]
variable [Algebra.IsSeparable (RatFunc K) L]

local instance : DecidableEq (Place K L) := Classical.decEq _

variable (A : Type) [CommRing A] [IsDomain A]
variable [Algebra K A] [Algebra A L] [IsFractionRing A L]
variable [Algebra (Polynomial K) A]
variable [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
variable [IsScalarTower (Polynomial K) A L]

omit [IsDomain A] in
omit [IsScalarTower K (Polynomial K) A] in
theorem finite_model_zero_points_le_exponentSet
    (x : σ → A) (E : Finset (σ →₀ ℕ))
    (F : MvPolynomial σ K) (hFE : F.support ⊆ E)
    (hF : MvPolynomial.eval₂Hom (algebraMap K A) x F ≠ 0)
    (q : ℕ)
    (hpole : ∀ W : Finset (Place K L),
      (∑ v ∈ W, exponentSetPoleWeight v.val
        (fun i ↦ algebraMap A L (x i)) E) ≤ (q : ℤ))
    (S : Finset (A →ₐ[K] K))
    (hS : ∀ ψ ∈ S, ψ (MvPolynomial.eval₂Hom (algebraMap K A) x F) = 0) :
    S.card ≤ q := by
  classical
  have heval : MvPolynomial.eval₂Hom (algebraMap K L)
      (fun i ↦ algebraMap A L (x i)) F =
        algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F) :=
    (map_model_eval K L A x F).symm
  have hnonzero : MvPolynomial.eval₂Hom (algebraMap K L)
      (fun i ↦ algebraMap A L (x i)) F ≠ 0 := by
    rw [heval]
    intro hz
    apply hF
    apply IsFractionRing.injective A L
    simpa only [map_zero] using hz
  let U := S.image (modelPlace K L A)
  have hU : ∀ v ∈ U, 1 ≤ CommonPlaceBalance.order K L v
      (MvPolynomial.eval₂Hom (algebraMap K L)
        (fun i ↦ algebraMap A L (x i)) F) := by
    intro v hv
    obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp hv
    rw [heval]
    exact ActualAffineModelPlaces.actual_model_zero_order_ge_one
      K A L ψ _ hF (hS ψ hψ)
  let W := CommonPlaceBalance.placesFor K L _ hnonzero
  have hcount := CommonPlaceBalance.finite_zero_places_le_poleMass
    K L _ hnonzero U hU
  have hsupport := weighted_poleOrder_eval_le_exponentSet W
    (fun _ ↦ 1) (fun v ↦ v.val) (algebraMap K L)
    (fun v _ c ↦ constant_value_le_one K L v c)
    (fun i ↦ algebraMap A L (x i)) E F hFE
  have hcard : U.card = S.card :=
    Finset.card_image_of_injective _ (modelPlace_injective K L A)
  have hq : (S.card : ℤ) ≤ q := by
    calc
      (S.card : ℤ) = (U.card : ℤ) := by rw [hcard]
      _ ≤ ∑ v ∈ W, CoordinatePoleMass.poleOrder K L v
          (MvPolynomial.eval₂Hom (algebraMap K L)
            (fun i ↦ algebraMap A L (x i)) F) := hcount
      _ ≤ ∑ v ∈ W, exponentSetPoleWeight v.val
          (fun i ↦ algebraMap A L (x i)) E := by
        simpa only [CoordinatePoleMass.poleOrder, Nat.cast_one, one_mul] using hsupport
      _ ≤ (q : ℤ) := hpole W
  exact_mod_cast hq

section ActualCurve

variable (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]

end ActualCurve

end

end ProximityPrize.SubmissionLower.ContactSparsePoleZeroCount

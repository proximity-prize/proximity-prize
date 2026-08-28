import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.SmallProjectionPoleMass
import ProximityPrize.SubmissionLower.CoordinateBoxZeroCount

/-!
# Coordinate-box zero counts below twice the characteristic

This is the existing common-place box argument with one input changed:
nonconstant coordinates need only have finite projection degree below
`2p`, rather than a separable projection.  The fixed separator used to
construct the common projective curve remains finite and separable.
-/

namespace ProximityPrize.SubmissionLower.SmallCoordinateBoxZeroCount

open scoped Classical BigOperators WithZero

noncomputable section

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable (p : ℕ) [ExpChar K p]

abbrev Place := CoordinatePlaceClassification.NormalizedValuation K L

structure SmallCoordinate where
  embedding : RatFunc K →ₐ[K] L
  finite : letI : Algebra (RatFunc K) L := embedding.toRingHom.toAlgebra
    FiniteDimensional (RatFunc K) L
  degree_lt_two : letI : Algebra (RatFunc K) L := embedding.toRingHom.toAlgebra
    Module.finrank (RatFunc K) L < 2 * p

namespace SmallCoordinate

def value (c : SmallCoordinate K L p) : L :=
  c.embedding (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)

def degree (c : SmallCoordinate K L p) : ℕ :=
  letI : Algebra (RatFunc K) L := c.embedding.toRingHom.toAlgebra
  Module.finrank (RatFunc K) L

variable [IsAlgClosed K]

theorem finite_sum_pole_le_degree (hp : p.Prime)
    (c : SmallCoordinate K L p) (W : Finset (Place K L)) :
    (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v (value K L p c)) ≤
      (degree K L p c : ℤ) := by
  exact SmallProjectionPoleMass.finite_sum_pole_le_finrank
    K L p hp c.embedding c.finite c.degree_lt_two W

end SmallCoordinate

abbrev Coordinate := K ⊕ SmallCoordinate K L p

def coordinateValue : Coordinate K L p → L :=
  Sum.elim (algebraMap K L) (SmallCoordinate.value K L p)

def coordinateDegree : Coordinate K L p → ℕ :=
  Sum.elim (fun _ ↦ 0) (SmallCoordinate.degree K L p)

theorem constant_value_le_one (v : Place K L) (c : K) :
    v.val (algebraMap K L c) ≤ 1 := by
  letI : v.val.IsTrivialOn K := v.property.2
  exact Valuation.IsTrivialOn.valuation_algebraMap_le_one v.val c

variable [IsAlgClosed K]

theorem finite_sum_coordinate_pole_le_degree (hp : p.Prime)
    (c : Coordinate K L p) (W : Finset (Place K L)) :
    (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v (coordinateValue K L p c)) ≤
      (coordinateDegree K L p c : ℤ) := by
  rcases c with a | c
  · have hz : ∀ v : Place K L,
        CoordinatePoleMass.poleOrder K L v (algebraMap K L a) = 0 :=
      fun v ↦ CoordinatePoleMass.poleOrder_eq_zero_of_le_one K L v _
        (constant_value_le_one K L v a)
    simp only [coordinateValue, coordinateDegree, Sum.elim_inl, hz,
      Finset.sum_const_zero, Nat.cast_zero, le_refl]
  · exact SmallCoordinate.finite_sum_pole_le_degree K L p hp c W

variable {p}
variable {σ : Type*} [Fintype σ]

theorem finite_sum_polynomial_pole_le_box (hp : p.Prime)
    (W : Finset (Place K L)) (c : σ → Coordinate K L p)
    (cap : σ → ℕ) (F : MvPolynomial σ K)
    (hcap : ∀ i, F.degreeOf i ≤ cap i) :
    (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v
      (MvPolynomial.eval₂Hom (algebraMap K L)
        (fun i ↦ coordinateValue K L p (c i)) F)) ≤
      ∑ i, (cap i : ℤ) * (coordinateDegree K L p (c i) : ℤ) := by
  have hlocal := ContactLocalPoleBound.weighted_poleOrder_eval_le_box
    W (fun _ ↦ 1) (fun v ↦ v.val) (algebraMap K L)
    (fun v _ a ↦ constant_value_le_one K L v a)
    (fun i ↦ coordinateValue K L p (c i)) cap F hcap
  simp only [Nat.cast_one, one_mul] at hlocal
  calc
    _ ≤ ∑ i, (cap i : ℤ) *
        ∑ v ∈ W, CoordinatePoleMass.poleOrder K L v
          (coordinateValue K L p (c i)) := hlocal
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (finite_sum_coordinate_pole_le_degree K L p hp (c i) W)
        (Int.natCast_nonneg _)

section FixedSeparator

variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L]
variable [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L]
variable [Algebra.IsSeparable (RatFunc K) L]

theorem finite_zero_places_le_box (hp : p.Prime)
    (c : σ → Coordinate K L p) (cap : σ → ℕ)
    (F : MvPolynomial σ K) (hcap : ∀ i, F.degreeOf i ≤ cap i)
    (hF : MvPolynomial.eval₂Hom (algebraMap K L)
      (fun i ↦ coordinateValue K L p (c i)) F ≠ 0)
    (U : Finset (Place K L))
    (hU : ∀ v ∈ U, 1 ≤ CommonPlaceBalance.order K L v
      (MvPolynomial.eval₂Hom (algebraMap K L)
        (fun i ↦ coordinateValue K L p (c i)) F)) :
    (U.card : ℤ) ≤
      ∑ i, (cap i : ℤ) * (coordinateDegree K L p (c i) : ℤ) := by
  let value := MvPolynomial.eval₂Hom (algebraMap K L)
    (fun i ↦ coordinateValue K L p (c i)) F
  let W := CommonPlaceBalance.placesFor K L value hF
  exact (CommonPlaceBalance.finite_zero_places_le_poleMass
    K L value hF U hU).trans
      (finite_sum_polynomial_pole_le_box K L hp W c cap F hcap)

section AffineModel

variable (A : Type*) [CommRing A] [IsDomain A]
variable [Algebra K A] [Algebra A L] [IsFractionRing A L]
variable [Algebra (Polynomial K) A]
variable [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
variable [IsScalarTower (Polynomial K) A L]

theorem finite_model_zero_points_le_box (hp : p.Prime)
    (x : σ → A) (c : σ → Coordinate K L p)
    (hc : ∀ i, coordinateValue K L p (c i) = algebraMap A L (x i))
    (cap : σ → ℕ) (F : MvPolynomial σ K)
    (hcap : ∀ i, F.degreeOf i ≤ cap i)
    (hF : MvPolynomial.eval₂Hom (algebraMap K A) x F ≠ 0)
    (S : Finset (A →ₐ[K] K))
    (hS : ∀ φ ∈ S, φ (MvPolynomial.eval₂Hom (algebraMap K A) x F) = 0) :
    (S.card : ℤ) ≤
      ∑ i, (cap i : ℤ) * (coordinateDegree K L p (c i) : ℤ) := by
  classical
  have heval : MvPolynomial.eval₂Hom (algebraMap K L)
      (fun i ↦ coordinateValue K L p (c i)) F =
        algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F) := by
    simp_rw [hc]
    exact (CoordinateBoxZeroCount.map_model_eval K L A x F).symm
  have hnonzero : MvPolynomial.eval₂Hom (algebraMap K L)
      (fun i ↦ coordinateValue K L p (c i)) F ≠ 0 := by
    rw [heval]
    intro hz
    apply hF
    apply IsFractionRing.injective A L
    simpa only [map_zero] using hz
  let U := S.image (CoordinateBoxZeroCount.modelPlace K L A)
  have hU : ∀ v ∈ U, 1 ≤ CommonPlaceBalance.order K L v
      (MvPolynomial.eval₂Hom (algebraMap K L)
        (fun i ↦ coordinateValue K L p (c i)) F) := by
    intro v hv
    obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hv
    rw [heval]
    exact ActualAffineModelPlaces.actual_model_zero_order_ge_one
      K A L φ _ hF (hS φ hφ)
  have h := finite_zero_places_le_box K L hp c cap F hcap hnonzero U hU
  have hcard : U.card = S.card := Finset.card_image_of_injective _
    (CoordinateBoxZeroCount.modelPlace_injective K L A)
  rwa [hcard] at h

end AffineModel
end FixedSeparator

end

end ProximityPrize.SubmissionLower.SmallCoordinateBoxZeroCount

#print axioms ProximityPrize.SubmissionLower.SmallCoordinateBoxZeroCount.finite_sum_polynomial_pole_le_box
#print axioms ProximityPrize.SubmissionLower.SmallCoordinateBoxZeroCount.finite_model_zero_points_le_box

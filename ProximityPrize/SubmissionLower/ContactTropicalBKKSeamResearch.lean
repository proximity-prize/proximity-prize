import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactResidualSparsePoleProviderResearch

/-!
# Exact formal seam for the residual tropical BKK theorem

This module separates the two genuinely geometric operations still needed
by the sparse post-6464 route.

1. A single polynomial `B` supported on `E` must have no leading-face
   cancellation at any component pole.  This turns its actual pole order
   into the support function `h_E`.
2. The sum of the resulting principal-divisor degrees over the curve
   components must be bounded by the mixed volume of `G`, `T`, and `E`.

Everything after those operations is proved below.  In particular, an exact
leading-pole identity only has to be checked on the finite product-formula
support of `B`; it then bounds the support function on *every* finite set of
places.  The last theorem packages a generic `B` plus a global BKK cycle
budget into the production-facing residual pole provider.
-/

namespace ProximityPrize.SubmissionLower.ContactTropicalBKKSeamResearch

open scoped Classical BigOperators WithZero
open IsDedekindDomain
open ContactSparsePoleSupportResearch
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveScalarTowers ActualCurveZeroCount
open CoordinateBoxZeroCount
open ContactRegularComponentCover
open ContactResidualSparsePoleProviderResearch

noncomputable section

variable {K L σ : Type} [Field K] [Field L] [Fintype σ]
variable [Algebra K L] [IsAlgClosed K]
variable [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L]
variable [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L]
variable [Algebra.IsSeparable (RatFunc K) L]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq (Place K L) := Classical.decEq _

theorem exponentSetPoleWeight_nonneg
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (x : σ → L) (E : Finset (σ →₀ ℕ)) :
    0 ≤ exponentSetPoleWeight v x E := by
  unfold exponentSetPoleWeight
  exact Finset.le_max' _ _ (Finset.mem_insert_self (0 : ℤ) _)

/-- If a test polynomial realizes the support function at every normalized
place, the support-function sum on an arbitrary finite family is bounded by
the actual principal-divisor pole mass of that one polynomial.

This is the precise reduction from tropical leading terms to the already
proved common-place product formula. -/
theorem support_sum_le_principal_poleMass_of_exact
    (x : σ → L) (E : Finset (σ →₀ ℕ)) (b : L) (hb : b ≠ 0)
    (hexact : ∀ v : Place K L,
      ContactLocalPoleBound.poleOrder v.val b =
        exponentSetPoleWeight v.val x E)
    (W : Finset (Place K L)) :
    (∑ v ∈ W, exponentSetPoleWeight v.val x E) ≤
      ∑ v ∈ CommonPlaceBalance.placesFor K L b hb,
        CoordinatePoleMass.poleOrder K L v b := by
  classical
  let P := CommonPlaceBalance.placesFor K L b hb
  have hout : ∀ v ∈ W, v ∉ P →
      exponentSetPoleWeight v.val x E = 0 := by
    intro v hvW hvP
    have hpole : ContactLocalPoleBound.poleOrder v.val b = 0 := by
      by_contra hpole
      apply hvP
      apply CommonPlaceBalance.placesFor_covers K L b hb v
      unfold CommonPlaceBalance.order ContactLocalPoleBound.poleOrder at *
      omega
    rw [← hexact v, hpole]
  calc
    (∑ v ∈ W, exponentSetPoleWeight v.val x E) =
        ∑ v ∈ W ∩ P, exponentSetPoleWeight v.val x E := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro v hvW hvnot
      apply hout v hvW
      intro hvP
      exact hvnot (Finset.mem_inter.mpr ⟨hvW, hvP⟩)
    _ ≤ ∑ v ∈ P, exponentSetPoleWeight v.val x E := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro v _ _
      exact exponentSetPoleWeight_nonneg v.val x E
    _ = ∑ v ∈ P, CoordinatePoleMass.poleOrder K L v b := by
      apply Finset.sum_congr rfl
      intro v _
      exact (hexact v).symm

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem coordinate_eval_ne_zero_of_not_mem
    (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (F : MvPolynomial (Fin 3) Ω) (hF : F ∉ P) :
    MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateField Ω P))
      (coordinate Ω P) F ≠ 0 := by
  intro hz
  apply hF
  rw [← aeval_coordinate_ker Ω P]
  exact hz

/-- The weakest single-polynomial geometric witness that remains after the
local valuation and product-formula layers.

`exact_pole` is supplied by generic leading-face avoidance.  `cycle_le`
and `sum_cost_le` are the residual affine/toric BKK zero-cycle theorem. -/
structure GenericSparseBKKWitness
    (G T H : MvPolynomial (Fin 3) Ω)
    (E : Finset (Fin 3 →₀ ℕ)) (separator : Fin 3) (wholeCost : ℕ)
    (hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator))
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1) where
  polynomial : MvPolynomial (Fin 3) Ω
  support_subset : polynomial.support ⊆ E
  proper : ∀ C : RegularComponent Ω G T H, polynomial ∉ C.1
  cost : RegularComponent Ω G T H → ℕ
  exact_pole : ∀ C : RegularComponent Ω G T H,
    let htr := hseparator C
    letI : Algebra (Polynomial Ω) (CoordinateRing Ω C.1) :=
      quotientPolynomialAlgebra Ω C.1 separator
    letI : Algebra (Polynomial Ω) (CoordinateField Ω C.1) :=
      polynomialBaseAlgebra Ω C.1 separator
    letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
      rationalBaseAlgebra Ω C.1 separator htr
    letI := quotientBaseScalarTower Ω C.1 separator
    letI := polynomialBaseScalarTower Ω C.1 separator
    letI := quotientFractionScalarTower Ω C.1 separator
    letI := polynomialRationalScalarTower Ω C.1 separator htr
    letI := rationalBaseScalarTower Ω C.1 separator htr
    letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1) :=
      (hproj C separator htr).1
    letI : Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1) :=
      (hproj C separator htr).2
    ∀ v : Place Ω (CoordinateField Ω C.1),
      ContactLocalPoleBound.poleOrder v.val
          (MvPolynomial.eval₂Hom
            (algebraMap Ω (CoordinateField Ω C.1))
            (coordinate Ω C.1) polynomial) =
        exponentSetPoleWeight v.val (coordinate Ω C.1) E
  cycle_le : ∀ C : RegularComponent Ω G T H,
    let htr := hseparator C
    letI : Algebra (Polynomial Ω) (CoordinateRing Ω C.1) :=
      quotientPolynomialAlgebra Ω C.1 separator
    letI : Algebra (Polynomial Ω) (CoordinateField Ω C.1) :=
      polynomialBaseAlgebra Ω C.1 separator
    letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
      rationalBaseAlgebra Ω C.1 separator htr
    letI := quotientBaseScalarTower Ω C.1 separator
    letI := polynomialBaseScalarTower Ω C.1 separator
    letI := quotientFractionScalarTower Ω C.1 separator
    letI := polynomialRationalScalarTower Ω C.1 separator htr
    letI := rationalBaseScalarTower Ω C.1 separator htr
    letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1) :=
      (hproj C separator htr).1
    letI : Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1) :=
      (hproj C separator htr).2
    let b := MvPolynomial.eval₂Hom
      (algebraMap Ω (CoordinateField Ω C.1))
      (coordinate Ω C.1) polynomial
    let hb : b ≠ 0 := coordinate_eval_ne_zero_of_not_mem C.1 polynomial (proper C)
    (∑ v ∈ CommonPlaceBalance.placesFor Ω (CoordinateField Ω C.1) b hb,
      CoordinatePoleMass.poleOrder Ω (CoordinateField Ω C.1) v b) ≤
        (cost C : ℤ)
  sum_cost_le : (∑ C : RegularComponent Ω G T H, cost C) ≤ wholeCost

/-- A generic leading-term witness plus the residual BKK cycle inequality
constructs the exact provider consumed by the sharp incidence theorem. -/
def GenericSparseBKKWitness.toResidualPoleComponentBudget
    {G T H : MvPolynomial (Fin 3) Ω}
    {E : Finset (Fin 3 →₀ ℕ)} {separator : Fin 3} {wholeCost : ℕ}
    {hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator)}
    {hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1}
    (B : GenericSparseBKKWitness G T H E separator wholeCost
      hseparator hproj) :
    ResidualPoleComponentBudget G T H E separator wholeCost where
  cost := B.cost
  separator_transcendental := hseparator
  pole_le := by
    intro C
    dsimp only
    let htr := hseparator C
    letI : Algebra (Polynomial Ω) (CoordinateRing Ω C.1) :=
      quotientPolynomialAlgebra Ω C.1 separator
    letI : Algebra (Polynomial Ω) (CoordinateField Ω C.1) :=
      polynomialBaseAlgebra Ω C.1 separator
    letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
      rationalBaseAlgebra Ω C.1 separator htr
    letI := quotientBaseScalarTower Ω C.1 separator
    letI := polynomialBaseScalarTower Ω C.1 separator
    letI := quotientFractionScalarTower Ω C.1 separator
    letI := polynomialRationalScalarTower Ω C.1 separator htr
    letI := rationalBaseScalarTower Ω C.1 separator htr
    letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1) :=
      (hproj C separator htr).1
    letI : Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1) :=
      (hproj C separator htr).2
    intro W
    let b := MvPolynomial.eval₂Hom
      (algebraMap Ω (CoordinateField Ω C.1))
      (coordinate Ω C.1) B.polynomial
    have hb : b ≠ 0 :=
      coordinate_eval_ne_zero_of_not_mem C.1 B.polynomial (B.proper C)
    exact (support_sum_le_principal_poleMass_of_exact
      (K := Ω) (L := CoordinateField Ω C.1)
      (coordinate Ω C.1) E b hb (B.exact_pole C) W).trans
        (B.cycle_le C)
  sum_cost_le := B.sum_cost_le

end

end ProximityPrize.SubmissionLower.ContactTropicalBKKSeamResearch

#print axioms ProximityPrize.SubmissionLower.ContactTropicalBKKSeamResearch.support_sum_le_principal_poleMass_of_exact
#print axioms ProximityPrize.SubmissionLower.ContactTropicalBKKSeamResearch.GenericSparseBKKWitness.toResidualPoleComponentBudget

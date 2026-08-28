import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactWeakSeparableSeparatorResearch
import ProximityPrize.SubmissionLower.ContactFlagPoleInequality6543Research
import ProximityPrize.SubmissionLower.ContactPrimeFlagBudgetFamilyResearch

/-! .






 -/

namespace ProximityPrize.SubmissionLower.ContactWeakPrimeFlagBudgetResearch

open scoped Classical BigOperators WithZero
open IsDedekindDomain
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveScalarTowers
open CoordinateBoxZeroCount ContactRegularComponentCover
open ContactFlagBezout6543Research ContactFlagPoleInequality6543Research
open ContactSparsePoleSupportResearch
open ContactWeakSeparableSeparatorResearch
open ContactPrimeFlagBudgetFamilyResearch
open ContactIdentityResidualZeroBudgetTransportResearch

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H : MvPolynomial (Fin 3) Omega}

/-- .

 -/
def LiteralSupportPoleBound
    {P : Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
    (D : SeparableLiteralCoordinate P)
    (E : Finset (Fin 3 →₀ ℕ)) (cost : ℕ) : Prop :=
  let i0 := D.index
  let htr := D.transcendental
  letI : Algebra (Polynomial Omega) (CoordinateRing Omega P) :=
    quotientPolynomialAlgebra Omega P i0
  letI : Algebra (Polynomial Omega) (CoordinateField Omega P) :=
    polynomialBaseAlgebra Omega P i0
  letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
    rationalBaseAlgebra Omega P i0 htr
  letI := quotientBaseScalarTower Omega P i0
  letI := polynomialBaseScalarTower Omega P i0
  letI := quotientFractionScalarTower Omega P i0
  letI := polynomialRationalScalarTower Omega P i0 htr
  letI := rationalBaseScalarTower Omega P i0 htr
  letI : FiniteDimensional (RatFunc Omega) (CoordinateField Omega P) :=
    D.finite
  letI : Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P) :=
    D.separable
  ∀ W : Finset (Place Omega (CoordinateField Omega P)),
    (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Omega P) E) ≤
      (cost : ℤ)

/-- .

 -/
structure AdaptiveUnitPoleBudget
    (base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1)
    (p q : FlagDegree) where
  zCost : RegularComponent Omega G T H → ℕ
  yzCost : RegularComponent Omega G T H → ℕ
  allCost : RegularComponent Omega G T H → ℕ
  zPole : ∀ C : RegularComponent Omega G T H,
    LiteralSupportPoleBound (base C) (flagSupport unitZFlag) (zCost C)
  yzPole : ∀ C : RegularComponent Omega G T H,
    LiteralSupportPoleBound (base C) (flagSupport unitYZFlag) (yzCost C)
  allPole : ∀ C : RegularComponent Omega G T H,
    LiteralSupportPoleBound (base C) (flagSupport unitAllFlag) (allCost C)
  sum_zCost_le : (∑ C : RegularComponent Omega G T H, zCost C) ≤
    flagMixed p q unitZFlag
  sum_yzCost_le : (∑ C : RegularComponent Omega G T H, yzCost C) ≤
    flagMixed p q unitYZFlag
  sum_allCost_le : (∑ C : RegularComponent Omega G T H, allCost C) ≤
    flagMixed p q unitAllFlag

/-- .
 -/
def AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily
    {base : ∀ C : RegularComponent Omega G T H,
      SeparableLiteralCoordinate C.1}
    {p q : FlagDegree} (U : AdaptiveUnitPoleBudget base p q) :
    PrimeFlagBudgetFamily (G := G) (T := T) (H := H) p q where
  zCost := U.zCost
  yzCost := U.yzCost
  allCost := U.allCost
  sum_zCost_le := U.sum_zCost_le
  sum_yzCost_le := U.sum_yzCost_le
  sum_allCost_le := U.sum_allCost_le
  primeBudget := by
    intro C
    refine ⟨?_⟩
    intro r A hA hproper points hpointsP hpointsA
    let D := base C
    let i0 := D.index
    let htr := D.transcendental
    letI : Algebra (Polynomial Omega) (CoordinateRing Omega C.1) :=
      quotientPolynomialAlgebra Omega C.1 i0
    letI : Algebra (Polynomial Omega) (CoordinateField Omega C.1) :=
      polynomialBaseAlgebra Omega C.1 i0
    letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
      rationalBaseAlgebra Omega C.1 i0 htr
    letI := quotientBaseScalarTower Omega C.1 i0
    letI := polynomialBaseScalarTower Omega C.1 i0
    letI := quotientFractionScalarTower Omega C.1 i0
    letI := polynomialRationalScalarTower Omega C.1 i0 htr
    letI := rationalBaseScalarTower Omega C.1 i0 htr
    letI : FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1) :=
      D.finite
    letI : Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1) :=
      D.separable
    have hz := U.zPole C
    have hyz := U.yzPole C
    have hall := U.allPole C
    change ∀ W : Finset (Place Omega (CoordinateField Omega C.1)),
      (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Omega C.1)
        (flagSupport unitZFlag)) ≤ (U.zCost C : ℤ) at hz
    change ∀ W : Finset (Place Omega (CoordinateField Omega C.1)),
      (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Omega C.1)
        (flagSupport unitYZFlag)) ≤ (U.yzCost C : ℤ) at hyz
    change ∀ W : Finset (Place Omega (CoordinateField Omega C.1)),
      (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Omega C.1)
        (flagSupport unitAllFlag)) ≤ (U.allCost C : ℤ) at hall
    have hpole : ∀ W : Finset (Place Omega (CoordinateField Omega C.1)),
        (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Omega C.1)
          (flagSupport r)) ≤
        ((r.zOnly * U.zCost C + r.yz * U.yzCost C +
          r.all * U.allCost C : ℕ) : ℤ) := by
      intro W
      calc
        (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Omega C.1)
            (flagSupport r)) ≤
            ∑ v ∈ W,
              ((r.zOnly : ℤ) * exponentSetPoleWeight v.val
                  (coordinate Omega C.1) (flagSupport unitZFlag) +
               (r.yz : ℤ) * exponentSetPoleWeight v.val
                  (coordinate Omega C.1) (flagSupport unitYZFlag) +
               (r.all : ℤ) * exponentSetPoleWeight v.val
                  (coordinate Omega C.1) (flagSupport unitAllFlag)) := by
          apply Finset.sum_le_sum
          intro v _
          exact exponentSetPoleWeight_flagSupport_le_three v.val
            (coordinate Omega C.1) r
        _ = (r.zOnly : ℤ) *
              (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Omega C.1)
                (flagSupport unitZFlag)) +
            (r.yz : ℤ) *
              (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Omega C.1)
                (flagSupport unitYZFlag)) +
            (r.all : ℤ) *
              (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Omega C.1)
                (flagSupport unitAllFlag)) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ (r.zOnly : ℤ) * (U.zCost C : ℤ) +
            (r.yz : ℤ) * (U.yzCost C : ℤ) +
            (r.all : ℤ) * (U.allCost C : ℤ) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (hz W) (by positivity))
              (mul_le_mul_of_nonneg_left (hyz W) (by positivity)))
            (mul_le_mul_of_nonneg_left (hall W) (by positivity))
        _ = ((r.zOnly * U.zCost C + r.yz * U.yzCost C +
            r.all * U.allCost C : ℕ) : ℤ) := by
          push_cast
          ring
    exact finite_zero_points_le_exponentSet_of_literalCoordinate C.1 D
      (flagSupport r)
      (r.zOnly * U.zCost C + r.yz * U.yzCost C + r.all * U.allCost C)
      hpole A ((support_subset_flagSupport_iff r A).2 hA) hproper
      points hpointsP hpointsA

end

end ProximityPrize.SubmissionLower.ContactWeakPrimeFlagBudgetResearch

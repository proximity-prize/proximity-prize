import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research
import ProximityPrize.SubmissionLower.ContactFlagPoleInequality6543Research
import ProximityPrize.SubmissionLower.ContactDependentGenericity6543Research

/-!
# Three-projection residual provider for the 65.43 flag route

For a flag support `Flag(a,b,c)`, the only global intersection input needed
after generic leading-term avoidance is a budget for three ordinary affine
projections:

* `Z` with coefficient `a`;
* a generic linear form in `(Y,Z)` with coefficient `b`;
* a generic linear form in `(Y,S,Z)` with coefficient `c`.

This module states that narrow interface componentwise and proves its exact
conversion to the residual provider consumed by the agreement-first caller.
No general toric intersection theorem is assumed here.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagProjectionProvider6543Research

open scoped Classical BigOperators WithZero
open IsDedekindDomain
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveScalarTowers ActualCurveZeroCount
open CoordinateBoxZeroCount ContactRegularComponentCover
open ContactResidualSparseComponentAdapterResearch
  ContactResidualSparsePoleProviderResearch
open ContactTropicalBKKSeamResearch
open ContactDependentGenericity6543Research
open ContactFlagBezout6543Research
open ContactFlagPoleInequality6543Research
open ContactLocalPoleBound ContactSparsePoleSupportResearch

noncomputable section

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

/-- Principal-cycle budget for one generic support polynomial.  For the flag
route this is instantiated only at the three unit supports, so each instance
is an ordinary affine-projection/resultant bound. -/
structure PrincipalCycleBudget
    {G T H : MvPolynomial (Fin 3) Ω}
    (E : Finset (Fin 3 →₀ ℕ)) (separator : Fin 3)
    (hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator))
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1)
    (B : GenericExactPolePolynomial G T H E separator hseparator hproj)
    (wholeCap : ℕ) where
  cost : RegularComponent Ω G T H → ℕ
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
      (coordinate Ω C.1) B.polynomial
    let hb : b ≠ 0 := coordinate_eval_ne_zero_of_not_mem
      C.1 B.polynomial (B.proper C)
    (∑ v ∈ CommonPlaceBalance.placesFor Ω
        (CoordinateField Ω C.1) b hb,
      CoordinatePoleMass.poleOrder Ω (CoordinateField Ω C.1) v b) ≤
        (cost C : ℤ)
  sum_cost_le : (∑ C : RegularComponent Ω G T H, cost C) ≤ wholeCap

/-- The exact geometric residue after generic flag leading terms have been
constructed.  Each component receives three ordinary projection costs.  The
local cycle bound uses their flag-weighted sum, while the three global fields
are the only resultant/degree inequalities still required. -/
structure FlagProjectionCycleBudget
    {G T H : MvPolynomial (Fin 3) Ω}
    (p : FlagDegree) (separator : Fin 3)
    (hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator))
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1)
    (B : GenericExactPolePolynomial G T H (flagSupport p) separator
      hseparator hproj)
    (zCap yzCap allCap : ℕ) where
  zCost : RegularComponent Ω G T H → ℕ
  yzCost : RegularComponent Ω G T H → ℕ
  allCost : RegularComponent Ω G T H → ℕ
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
      (coordinate Ω C.1) B.polynomial
    let hb : b ≠ 0 := coordinate_eval_ne_zero_of_not_mem
      C.1 B.polynomial (B.proper C)
    (∑ v ∈ CommonPlaceBalance.placesFor Ω
        (CoordinateField Ω C.1) b hb,
      CoordinatePoleMass.poleOrder Ω (CoordinateField Ω C.1) v b) ≤
        ((p.zOnly * zCost C + p.yz * yzCost C +
          p.all * allCost C : ℕ) : ℤ)
  sum_zCost_le : (∑ C : RegularComponent Ω G T H, zCost C) ≤ zCap
  sum_yzCost_le : (∑ C : RegularComponent Ω G T H, yzCost C) ≤ yzCap
  sum_allCost_le : (∑ C : RegularComponent Ω G T H, allCost C) ≤ allCap

/-- Three unit-support principal-cycle budgets imply the combined flag-cycle
inequality.  The proof compares the full flag support at the places of `B`
with the three unit support functions, then uses each unit polynomial's full
principal pole divisor.  The unit polynomials are never multiplied, so zeros
cannot cancel poles. -/
def FlagProjectionCycleBudget.ofNestedProjectionBudgets
    {G T H : MvPolynomial (Fin 3) Ω}
    {p : FlagDegree} {separator : Fin 3}
    {hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator)}
    {hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1}
    (B : GenericExactPolePolynomial G T H (flagSupport p) separator
      hseparator hproj)
    (BZ : GenericExactPolePolynomial G T H (flagSupport unitZFlag) separator
      hseparator hproj)
    (BYZ : GenericExactPolePolynomial G T H (flagSupport unitYZFlag) separator
      hseparator hproj)
    (BAll : GenericExactPolePolynomial G T H (flagSupport unitAllFlag) separator
      hseparator hproj)
    {zCap yzCap allCap : ℕ}
    (zBudget : PrincipalCycleBudget (flagSupport unitZFlag) separator
      hseparator hproj BZ zCap)
    (yzBudget : PrincipalCycleBudget (flagSupport unitYZFlag) separator
      hseparator hproj BYZ yzCap)
    (allBudget : PrincipalCycleBudget (flagSupport unitAllFlag) separator
      hseparator hproj BAll allCap) :
    FlagProjectionCycleBudget p separator hseparator hproj B
      zCap yzCap allCap where
  zCost := zBudget.cost
  yzCost := yzBudget.cost
  allCost := allBudget.cost
  sum_zCost_le := zBudget.sum_cost_le
  sum_yzCost_le := yzBudget.sum_cost_le
  sum_allCost_le := allBudget.sum_cost_le
  cycle_le := by
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
    let b := MvPolynomial.eval₂Hom
      (algebraMap Ω (CoordinateField Ω C.1))
      (coordinate Ω C.1) B.polynomial
    let hb : b ≠ 0 := coordinate_eval_ne_zero_of_not_mem
      C.1 B.polynomial (B.proper C)
    let bZ := MvPolynomial.eval₂Hom
      (algebraMap Ω (CoordinateField Ω C.1))
      (coordinate Ω C.1) BZ.polynomial
    let hbZ : bZ ≠ 0 := coordinate_eval_ne_zero_of_not_mem
      C.1 BZ.polynomial (BZ.proper C)
    let bYZ := MvPolynomial.eval₂Hom
      (algebraMap Ω (CoordinateField Ω C.1))
      (coordinate Ω C.1) BYZ.polynomial
    let hbYZ : bYZ ≠ 0 := coordinate_eval_ne_zero_of_not_mem
      C.1 BYZ.polynomial (BYZ.proper C)
    let bAll := MvPolynomial.eval₂Hom
      (algebraMap Ω (CoordinateField Ω C.1))
      (coordinate Ω C.1) BAll.polynomial
    let hbAll : bAll ≠ 0 := coordinate_eval_ne_zero_of_not_mem
      C.1 BAll.polynomial (BAll.proper C)
    let W := CommonPlaceBalance.placesFor Ω
      (CoordinateField Ω C.1) b hb
    have hZsupport :
        (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Ω C.1)
          (flagSupport unitZFlag)) ≤
        ∑ v ∈ CommonPlaceBalance.placesFor Ω
            (CoordinateField Ω C.1) bZ hbZ,
          CoordinatePoleMass.poleOrder Ω (CoordinateField Ω C.1) v bZ := by
      exact support_sum_le_principal_poleMass_of_exact
        (coordinate Ω C.1) (flagSupport unitZFlag) bZ hbZ
        (BZ.exact_pole C) W
    have hYZsupport :
        (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Ω C.1)
          (flagSupport unitYZFlag)) ≤
        ∑ v ∈ CommonPlaceBalance.placesFor Ω
            (CoordinateField Ω C.1) bYZ hbYZ,
          CoordinatePoleMass.poleOrder Ω (CoordinateField Ω C.1) v bYZ := by
      exact support_sum_le_principal_poleMass_of_exact
        (coordinate Ω C.1) (flagSupport unitYZFlag) bYZ hbYZ
        (BYZ.exact_pole C) W
    have hAllsupport :
        (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Ω C.1)
          (flagSupport unitAllFlag)) ≤
        ∑ v ∈ CommonPlaceBalance.placesFor Ω
            (CoordinateField Ω C.1) bAll hbAll,
          CoordinatePoleMass.poleOrder Ω (CoordinateField Ω C.1) v bAll := by
      exact support_sum_le_principal_poleMass_of_exact
        (coordinate Ω C.1) (flagSupport unitAllFlag) bAll hbAll
        (BAll.exact_pole C) W
    have hZcycle :
        (∑ v ∈ CommonPlaceBalance.placesFor Ω
            (CoordinateField Ω C.1) bZ hbZ,
          CoordinatePoleMass.poleOrder Ω (CoordinateField Ω C.1) v bZ) ≤
        (zBudget.cost C : ℤ) := by
      simpa only using zBudget.cycle_le C
    have hYZcycle :
        (∑ v ∈ CommonPlaceBalance.placesFor Ω
            (CoordinateField Ω C.1) bYZ hbYZ,
          CoordinatePoleMass.poleOrder Ω (CoordinateField Ω C.1) v bYZ) ≤
        (yzBudget.cost C : ℤ) := by
      simpa only using yzBudget.cycle_le C
    have hAllcycle :
        (∑ v ∈ CommonPlaceBalance.placesFor Ω
            (CoordinateField Ω C.1) bAll hbAll,
          CoordinatePoleMass.poleOrder Ω (CoordinateField Ω C.1) v bAll) ≤
        (allBudget.cost C : ℤ) := by
      simpa only using allBudget.cycle_le C
    have hlocal : ∀ v ∈ W,
        poleOrder v.val b ≤
          (p.zOnly : ℤ) * exponentSetPoleWeight v.val (coordinate Ω C.1)
              (flagSupport unitZFlag) +
          (p.yz : ℤ) * exponentSetPoleWeight v.val (coordinate Ω C.1)
              (flagSupport unitYZFlag) +
          (p.all : ℤ) * exponentSetPoleWeight v.val (coordinate Ω C.1)
              (flagSupport unitAllFlag) := by
      intro v _
      rw [B.exact_pole C v]
      exact exponentSetPoleWeight_flagSupport_le_three v.val
        (coordinate Ω C.1) p
    calc
      (∑ v ∈ W, CoordinatePoleMass.poleOrder Ω
          (CoordinateField Ω C.1) v b) ≤
          ∑ v ∈ W,
            ((p.zOnly : ℤ) * exponentSetPoleWeight v.val
                (coordinate Ω C.1) (flagSupport unitZFlag) +
             (p.yz : ℤ) * exponentSetPoleWeight v.val
                (coordinate Ω C.1) (flagSupport unitYZFlag) +
             (p.all : ℤ) * exponentSetPoleWeight v.val
                (coordinate Ω C.1) (flagSupport unitAllFlag)) := by
        apply Finset.sum_le_sum
        intro v hv
        exact hlocal v hv
      _ = (p.zOnly : ℤ) *
            (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Ω C.1)
              (flagSupport unitZFlag)) +
          (p.yz : ℤ) *
            (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Ω C.1)
              (flagSupport unitYZFlag)) +
          (p.all : ℤ) *
            (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Ω C.1)
              (flagSupport unitAllFlag)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (p.zOnly : ℤ) * (zBudget.cost C : ℤ) +
          (p.yz : ℤ) * (yzBudget.cost C : ℤ) +
          (p.all : ℤ) * (allBudget.cost C : ℤ) := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left (hZsupport.trans hZcycle) (by positivity))
            (mul_le_mul_of_nonneg_left (hYZsupport.trans hYZcycle) (by positivity)))
          (mul_le_mul_of_nonneg_left (hAllsupport.trans hAllcycle) (by positivity))
      _ = ((p.zOnly * zBudget.cost C + p.yz * yzBudget.cost C +
          p.all * allBudget.cost C : ℕ) : ℤ) := by
        push_cast
        ring

/-- Flag-weighted component cost supplied to the existing residual seam. -/
def FlagProjectionCycleBudget.combinedCost
    {G T H : MvPolynomial (Fin 3) Ω}
    {p : FlagDegree} {separator : Fin 3}
    {hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator)}
    {hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1}
    {B : GenericExactPolePolynomial G T H (flagSupport p) separator
      hseparator hproj}
    {zCap yzCap allCap : ℕ}
    (P : FlagProjectionCycleBudget p separator hseparator hproj B
      zCap yzCap allCap)
    (C : RegularComponent Ω G T H) : ℕ :=
  p.zOnly * P.zCost C + p.yz * P.yzCost C + p.all * P.allCost C

theorem FlagProjectionCycleBudget.sum_combinedCost_le
    {G T H : MvPolynomial (Fin 3) Ω}
    {p : FlagDegree} {separator : Fin 3}
    {hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator)}
    {hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1}
    {B : GenericExactPolePolynomial G T H (flagSupport p) separator
      hseparator hproj}
    {zCap yzCap allCap : ℕ}
    (P : FlagProjectionCycleBudget p separator hseparator hproj B
      zCap yzCap allCap) :
    (∑ C : RegularComponent Ω G T H, P.combinedCost C) ≤
      p.zOnly * zCap + p.yz * yzCap + p.all * allCap := by
  rw [show (∑ C : RegularComponent Ω G T H, P.combinedCost C) =
      p.zOnly * (∑ C, P.zCost C) +
      p.yz * (∑ C, P.yzCost C) +
      p.all * (∑ C, P.allCost C) by
    simp only [FlagProjectionCycleBudget.combinedCost,
      Finset.sum_add_distrib, Finset.mul_sum]]
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.mul_le_mul_left p.zOnly P.sum_zCost_le)
      (Nat.mul_le_mul_left p.yz P.sum_yzCost_le))
    (Nat.mul_le_mul_left p.all P.sum_allCost_le)

/-- The three projection budgets produce the exact residual component
provider, with no further geometric hypothesis. -/
def FlagProjectionCycleBudget.toResidualComponentBudget
    {G T H : MvPolynomial (Fin 3) Ω}
    {p : FlagDegree} {separator : Fin 3}
    {hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator)}
    {hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1}
    {B : GenericExactPolePolynomial G T H (flagSupport p) separator
      hseparator hproj}
    {zCap yzCap allCap : ℕ}
    (P : FlagProjectionCycleBudget p separator hseparator hproj B
      zCap yzCap allCap) :
    ResidualComponentBudget G T H
      (fun A ↦ A.support ⊆ flagSupport p)
      (p.zOnly * zCap + p.yz * yzCap + p.all * allCap) :=
  (B.toGenericSparseBKKWitness P.combinedCost P.cycle_le
      P.sum_combinedCost_le).toResidualPoleComponentBudget
    |>.toResidualComponentBudget hproj

/-- Numeric 65.43 specialization.  The exact polarization identity rewrites
the weighted sum of the three ordinary projection caps to the whole flag
mixed cost expected by the outer incidence ledger. -/
def FlagProjectionCycleBudget.toResidualComponentBudget6543
    {G T H : MvPolynomial (Fin 3) Ω} {separator : Fin 3}
    {hseparator : ∀ C : RegularComponent Ω G T H,
      Transcendental Ω (coordinate Ω C.1 separator)}
    {hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1}
    {B : GenericExactPolePolynomial G T H
      (flagSupport shearedAgreementFlag) separator hseparator hproj}
    (P : FlagProjectionCycleBudget shearedAgreementFlag separator
      hseparator hproj B flagZMixedCap flagYZMixedCap flagAllMixedCap) :
    ResidualComponentBudget G T H
      (fun A ↦ A.support ⊆ flagSupport shearedAgreementFlag)
      flagWholeMixedCap := by
  rw [flag_projection_decomposition]
  exact P.toResidualComponentBudget

end

end ProximityPrize.SubmissionLower.ContactFlagProjectionProvider6543Research

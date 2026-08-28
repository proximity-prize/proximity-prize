import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagProjectionProvider6543Research
import ProximityPrize.SubmissionLower.ContactFlagAffineFamilyDegree6543Research

/-!
# Separable-coordinate adapter for the 65.43 flag principal cycles

The three flag projections are ordinary rational parameters on every retained
curve component.  This module isolates the exact interface between those
parameters and `PrincipalCycleBudget`:

* locally, the pole divisor of the generic unit-support polynomial agrees
  with the pole divisor of the chosen separable parameter on the finite
  common-place support;
* globally, the sum of the actual parameter degrees is at most the relevant
  trapezoid-resultant cap.

The first item is supplied by common leading-term avoidance and the second by
`finite_sum_flag_finrank_trapezoid`.  No intersection inequality is assumed
in this adapter.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagPrincipalCycleAdapter6543Research

open scoped Classical BigOperators
open IsDedekindDomain
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveScalarTowers ActualCurveZeroCount
open CoordinateBoxZeroCount
open ContactRegularComponentCover
open ContactDependentGenericity6543Research
open ContactTropicalBKKSeamResearch
open ContactFlagProjectionProvider6543Research
open ContactFlagAffineFamilyDegree6543Research
open ContactFlagTriangularProjectionResearch
open TrivariateRationalCollection ActualPlaneCoordinateKernel
  ArbitraryRationalProjectionResearch

noncomputable section

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]

/-- One actual separable rational parameter on each retained component,
whose poles agree with the chosen generic unit-support polynomial wherever
that polynomial has nonzero order. -/
structure SeparablePrincipalProjection
    {G T H : MvPolynomial (Fin 3) Omega}
    (E : Finset (Fin 3 →₀ ℕ)) (separator : Fin 3)
    (hseparator : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega (coordinate Omega C.1 separator))
    (hproj : ∀ C : RegularComponent Omega G T H,
      ProjectionsFiniteSeparable Omega C.1)
    (B : GenericExactPolePolynomial G T H E separator hseparator hproj) where
  parameter : ∀ C : RegularComponent Omega G T H,
    SeparableCoordinate Omega (CoordinateField Omega C.1)
  pole_eq : ∀ (C : RegularComponent Omega G T H)
      (v : Place Omega (CoordinateField Omega C.1)),
    let b := MvPolynomial.eval₂Hom
      (algebraMap Omega (CoordinateField Omega C.1))
      (coordinate Omega C.1) B.polynomial
    CoordinatePoleMass.poleOrder Omega (CoordinateField Omega C.1) v b =
      CoordinatePoleMass.poleOrder Omega (CoordinateField Omega C.1) v
        (SeparableCoordinate.value Omega (CoordinateField Omega C.1)
          (parameter C))

/-- The cost attached to a component is its actual function-field degree in
the selected affine parameter. -/
def SeparablePrincipalProjection.cost
    {G T H : MvPolynomial (Fin 3) Omega}
    {E : Finset (Fin 3 →₀ ℕ)} {separator : Fin 3}
    {hseparator : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega (coordinate Omega C.1 separator)}
    {hproj : ∀ C : RegularComponent Omega G T H,
      ProjectionsFiniteSeparable Omega C.1}
    {B : GenericExactPolePolynomial G T H E separator hseparator hproj}
    (P : SeparablePrincipalProjection E separator hseparator hproj B)
    (C : RegularComponent Omega G T H) : ℕ :=
  SeparableCoordinate.degree Omega (CoordinateField Omega C.1) (P.parameter C)

/-- Exact pole agreement plus the proved coordinate pole theorem converts a
summed affine-family degree cap into the principal-cycle budget used by the
three-projection flag provider. -/
def SeparablePrincipalProjection.toPrincipalCycleBudget
    {G T H : MvPolynomial (Fin 3) Omega}
    {E : Finset (Fin 3 →₀ ℕ)} {separator : Fin 3}
    {hseparator : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega (coordinate Omega C.1 separator)}
    {hproj : ∀ C : RegularComponent Omega G T H,
      ProjectionsFiniteSeparable Omega C.1}
    {B : GenericExactPolePolynomial G T H E separator hseparator hproj}
    (P : SeparablePrincipalProjection E separator hseparator hproj B)
    (wholeCap : ℕ)
    (hsum : (∑ C : RegularComponent Omega G T H, P.cost C) ≤ wholeCap) :
    PrincipalCycleBudget E separator hseparator hproj B wholeCap where
  cost := P.cost
  cycle_le := by
    intro C
    dsimp only
    let htr := hseparator C
    letI : Algebra (Polynomial Omega) (CoordinateRing Omega C.1) :=
      quotientPolynomialAlgebra Omega C.1 separator
    letI : Algebra (Polynomial Omega) (CoordinateField Omega C.1) :=
      polynomialBaseAlgebra Omega C.1 separator
    letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
      rationalBaseAlgebra Omega C.1 separator htr
    letI := quotientBaseScalarTower Omega C.1 separator
    letI := polynomialBaseScalarTower Omega C.1 separator
    letI := quotientFractionScalarTower Omega C.1 separator
    letI := polynomialRationalScalarTower Omega C.1 separator htr
    letI := rationalBaseScalarTower Omega C.1 separator htr
    letI : FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1) :=
      (hproj C separator htr).1
    letI : Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1) :=
      (hproj C separator htr).2
    let b := MvPolynomial.eval₂Hom
      (algebraMap Omega (CoordinateField Omega C.1))
      (coordinate Omega C.1) B.polynomial
    let hb : b ≠ 0 := coordinate_eval_ne_zero_of_not_mem
      C.1 B.polynomial (B.proper C)
    let W := CommonPlaceBalance.placesFor Omega
      (CoordinateField Omega C.1) b hb
    calc
      (∑ v ∈ W, CoordinatePoleMass.poleOrder Omega
          (CoordinateField Omega C.1) v b) =
          ∑ v ∈ W, CoordinatePoleMass.poleOrder Omega
            (CoordinateField Omega C.1) v
            (SeparableCoordinate.value Omega (CoordinateField Omega C.1)
              (P.parameter C)) := by
        apply Finset.sum_congr rfl
        intro v _
        exact P.pole_eq C v
      _ ≤ (SeparableCoordinate.degree Omega (CoordinateField Omega C.1)
          (P.parameter C) : ℤ) :=
        SeparableCoordinate.finite_sum_pole_le_degree Omega
          (CoordinateField Omega C.1) (P.parameter C) W
      _ = (P.cost C : ℤ) := rfl
  sum_cost_le := hsum

/-- The separable coordinate represented by one literal flag coordinate in
the transformed evaluation family. -/
def flagSeparableCoordinate
    {G T H : MvPolynomial (Fin 3) Omega}
    (lam mu nu : Omega) (order : Fin 3 ≃ Fin 3)
    (ht : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega
        (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
    (hfinite : ∀ C : RegularComponent Omega G T H,
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
          (ht C)).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))
    (hsep : ∀ C : RegularComponent Omega G T H,
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
          (ht C)).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
    (C : RegularComponent Omega G T H) :
    SeparableCoordinate Omega (CoordinateField Omega C.1) where
  embedding := elementEmbedding Omega (CoordinateField Omega C.1)
    (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))) (ht C)
  finite := hfinite C
  separable := hsep C

@[simp] theorem flagSeparableCoordinate_value
    {G T H : MvPolynomial (Fin 3) Omega}
    (lam mu nu : Omega) (order : Fin 3 ≃ Fin 3)
    (ht : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega
        (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
    (hfinite : ∀ C : RegularComponent Omega G T H,
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
          (ht C)).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))
    (hsep : ∀ C : RegularComponent Omega G T H,
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
          (ht C)).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
    (C : RegularComponent Omega G T H) :
    SeparableCoordinate.value Omega (CoordinateField Omega C.1)
        (flagSeparableCoordinate lam mu nu order ht hfinite hsep C) =
      flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)) := by
  exact elementEmbedding_variable Omega (CoordinateField Omega C.1)
    (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))) (ht C)

/-- Literal wiring of the exact trapezoid family-degree theorem into a
principal-cycle budget.  The only hypotheses not discharged by the
resultant calculation are separability of the common affine parameter and
the local pole equality supplied by common coefficient avoidance. -/
def principalCycleBudget_of_flag_trapezoid
    {G T H : MvPolynomial (Fin 3) Omega}
    {E : Finset (Fin 3 →₀ ℕ)} {separator : Fin 3}
    {hseparator : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega (coordinate Omega C.1 separator)}
    {hproj : ∀ C : RegularComponent Omega G T H,
      ProjectionsFiniteSeparable Omega C.1}
    (B : GenericExactPolePolynomial G T H E separator hseparator hproj)
    (lam mu nu : Omega) (order : Fin 3 ≃ Fin 3)
    (ht : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega
        (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
    (hgen : ∀ C : RegularComponent Omega G T H,
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
          (ht C)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc Omega)
        ({flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 2)),
          flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 1))} :
          Set (CoordinateField Omega C.1)) = ⊤)
    (hsep : ∀ C : RegularComponent Omega G T H,
      letI : Algebra (RatFunc Omega) (CoordinateField Omega C.1) :=
        (elementEmbedding Omega (CoordinateField Omega C.1)
          (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
          (ht C)).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
    (hpole : ∀ (C : RegularComponent Omega G T H)
        (v : Place Omega (CoordinateField Omega C.1)),
      let b := MvPolynomial.eval₂Hom
        (algebraMap Omega (CoordinateField Omega C.1))
        (coordinate Omega C.1) B.polynomial
      CoordinatePoleMass.poleOrder Omega (CoordinateField Omega C.1) v b =
        CoordinatePoleMass.poleOrder Omega (CoordinateField Omega C.1) v
          (flagEvaluation Omega C.1 lam mu nu
            (MvPolynomial.X (order 0))))
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (hpositive : 0 <
      (planeMap Omega order (flagAlgHom lam mu nu G)).natDegree)
    (n mCap totalG totalT cap : ℕ) (hTne : T ≠ 0)
    (hGouter : (planeMap Omega order
      (flagAlgHom lam mu nu G)).natDegree ≤ n)
    (hTouter : (planeMap Omega order
      (flagAlgHom lam mu nu T)).natDegree ≤ mCap)
    (hGsupport : ∀ d ∈ (rationalMap Omega order
      (flagAlgHom lam mu nu G)).support, d 0 + d 1 ≤ totalG)
    (hTsupport : ∀ d ∈ (rationalMap Omega order
      (flagAlgHom lam mu nu T)).support, d 0 + d 1 ≤ totalT)
    (hbudget : ∀ m, m ≤ mCap →
      m * totalG + n * totalT - m * n ≤ cap) :
    PrincipalCycleBudget E separator hseparator hproj B cap := by
  have hinj : Function.Injective
      (fun C : RegularComponent Omega G T H ↦ C.1) := by
    intro C D hCD
    exact Subtype.ext hCD
  have hfamily := finite_sum_flag_finrank_trapezoid
    (K := Omega) (Q := fun C : RegularComponent Omega G T H ↦ C.1)
    hinj lam mu nu order ht hgen G T hG
    (fun C ↦ regularComponent_G_mem Omega G T H C)
    (fun C ↦ regularComponent_T_mem Omega G T H C)
    hproper hpositive n mCap totalG totalT cap hTne
    hGouter hTouter hGsupport hTsupport hbudget
  let hfinite := hfamily.1
  let P : SeparablePrincipalProjection E separator hseparator hproj B := {
    parameter := fun C ↦
      flagSeparableCoordinate lam mu nu order ht hfinite hsep C
    pole_eq := by
      intro C v
      simpa only [flagSeparableCoordinate_value] using hpole C v }
  apply P.toPrincipalCycleBudget cap
  change (∑ C : RegularComponent Omega G T H,
    SeparableCoordinate.degree Omega (CoordinateField Omega C.1)
      (flagSeparableCoordinate lam mu nu order ht hfinite hsep C)) ≤ cap
  convert hfamily.2 using 1
  apply Finset.sum_congr rfl
  intro C _
  rfl

end

end ProximityPrize.SubmissionLower.ContactFlagPrincipalCycleAdapter6543Research

#print axioms ProximityPrize.SubmissionLower.ContactFlagPrincipalCycleAdapter6543Research.SeparablePrincipalProjection.toPrincipalCycleBudget
#print axioms ProximityPrize.SubmissionLower.ContactFlagPrincipalCycleAdapter6543Research.principalCycleBudget_of_flag_trapezoid

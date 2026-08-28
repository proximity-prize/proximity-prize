import ProximityPrize.SubmissionLower.BCHKSPrimitiveTripleQuotient6400

/-!
# The normalized rank-one triple outside a fixed coordinate container

The primitive full gcd can vanish identically after evaluating the locator
variable at a few source coordinates.  Those coordinates form one fixed
container of size at most the locator degree.  Everywhere else, cancellation
is valid already over the polynomial challenge ring.  Consequently the
normalized triple describes both the received affine word and every retained
decoded polynomial, so their difference obeys one homogeneous semilinear
relation at every coordinate outside that fixed container.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSPrimitiveTripleRelation6400

open Polynomial
open Polynomial.Bivariate
open ProximityPrize.Benchmark
open BCHKSTwoAxisResultant6400
open BCHKSExactSparsification6400
open BCHKSRecursiveTwoAxisDescent6400
open BCHKSPrimitiveTripleQuotient6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- Source coordinates where a bivariate factor vanishes identically as a
polynomial in the challenge. -/
noncomputable def fixedCoordinateDefect
    (H : IRSProfile.Field[X][X]) : Finset IRSProfile.Index :=
  Finset.univ.filter fun i ↦
    (swap H).map (Polynomial.evalRingHom (IRSProfile.domain i)) = 0

/-- A nonzero bivariate polynomial has at most its locator degree many fixed
source-coordinate zeros. -/
theorem fixedCoordinateDefect_card_le
    (H : IRSProfile.Field[X][X]) (hH : H ≠ 0) :
    (fixedCoordinateDefect H).card ≤ H.natDegree := by
  classical
  have hswap : swap H ≠ 0 := by
    simpa using swap.injective.ne hH
  have hraw := card_le_filter_bivariate_map_ne_zero_add_degreeX
    (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain (swap H) hswap
  have hpartition := Finset.card_filter_add_card_filter_not
    (fun i : IRSProfile.Index ↦
      (swap H).map (Polynomial.evalRingHom (IRSProfile.domain i)) ≠ 0)
    (s := Finset.univ)
  have hpartition' :
      ((Finset.univ : Finset IRSProfile.Index).filter fun i ↦
          (swap H).map
            (Polynomial.evalRingHom (IRSProfile.domain i)) ≠ 0).card +
        (fixedCoordinateDefect H).card =
          (Finset.univ : Finset IRSProfile.Index).card := by
    simpa only [fixedCoordinateDefect, not_ne_iff] using hpartition
  have hswapDegree : degreeX (swap H) = H.natDegree :=
    degreeX_swap H
  rw [hswapDegree] at hraw
  omega

theorem swap_map_eval_ne_zero_of_not_mem_fixedCoordinateDefect
    (H : IRSProfile.Field[X][X]) (i : IRSProfile.Index)
    (hi : i ∉ fixedCoordinateDefect H) :
    (swap H).map (Polynomial.evalRingHom (IRSProfile.domain i)) ≠ 0 := by
  intro hzero
  apply hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hzero⟩

/-- Evaluating the locator variable and then the challenge agrees with first
specializing the challenge and then evaluating the locator variable. -/
theorem eval_C_eval_eq_map_eval_eval
    {F : Type} [Field F] (Q : F[X][X]) (x z : F) :
    (Q.eval (Polynomial.C x)).eval z =
      (Q.map (Polynomial.evalRingHom z)).eval x := by
  have h := (Polynomial.eval_map_apply
    (p := Q) (f := Polynomial.evalRingHom z) (Polynomial.C x)).symm
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C] using h

/-- Outside the fixed zero container, the prescribed quotient triple still
represents the original polynomial-valued received relation at a source
coordinate. -/
theorem quotient_relationWord_at_coordinate
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A' B' C' : IRSProfile.Field[X][X])
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q).1.1 = H * A')
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q).2.1 = H * B')
    (hCfactor :
      score6400PolynomialLocatorPairToCode f₀ f₁ q = H * C')
    (i : IRSProfile.Index) (hi : i ∉ fixedCoordinateDefect H) :
    C'.eval (Polynomial.C (IRSProfile.domain i)) =
      A'.eval (Polynomial.C (IRSProfile.domain i)) *
          score6400ReceivedPolynomial f₀ f₁ i +
        B'.eval (Polynomial.C (IRSProfile.domain i)) *
          score6400FrobeniusReceivedPolynomial f₀ f₁ i := by
  have hHcoord :
      H.eval (Polynomial.C (IRSProfile.domain i)) ≠ 0 := by
    rw [← bivariate_swap_map_eval_eq_eval_C]
    exact swap_map_eval_ne_zero_of_not_mem_fixedCoordinateDefect H i hi
  apply mul_left_cancel₀ hHcoord
  calc
    H.eval (Polynomial.C (IRSProfile.domain i)) *
          C'.eval (Polynomial.C (IRSProfile.domain i)) =
        (score6400PolynomialLocatorPairToCode f₀ f₁ q).eval
          (Polynomial.C (IRSProfile.domain i)) := by
            rw [hCfactor, Polynomial.eval_mul]
    _ = score6400PolynomialPairRelationWord f₀ f₁ q i :=
      score6400PolynomialLocatorPairToCode_eval_coordinate f₀ f₁ q i
    _ = H.eval (Polynomial.C (IRSProfile.domain i)) *
          (A'.eval (Polynomial.C (IRSProfile.domain i)) *
              score6400ReceivedPolynomial f₀ f₁ i +
            B'.eval (Polynomial.C (IRSProfile.domain i)) *
              score6400FrobeniusReceivedPolynomial f₀ f₁ i) := by
            rw [score6400PolynomialPairRelationWord,
              polynomialBilinearWord, hAfactor, hBfactor,
              Polynomial.eval_mul, Polynomial.eval_mul]
            ring

/-- Subtracting a decoded-owner equation from the global received relation
gives a homogeneous semilinear error equation at every coordinate outside
the fixed container. -/
theorem homogeneous_error_relation_at_coordinate
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A' B' C' : IRSProfile.Field[X][X])
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q).1.1 = H * A')
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q).2.1 = H * B')
    (hCfactor :
      score6400PolynomialLocatorPairToCode f₀ f₁ q = H * C')
    (z : IRSProfile.Field) (P : IRSProfile.Field[X])
    (howner :
      C'.map (Polynomial.evalRingHom z) =
        A'.map (Polynomial.evalRingHom z) * P +
          B'.map (Polynomial.evalRingHom z) *
            P.map koalaSexticFrobenius.toRingHom)
    (i : IRSProfile.Index) (hi : i ∉ fixedCoordinateDefect H) :
    (A'.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
          ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
        (B'.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
          (koalaSexticFrobenius (f₀ i + z * f₁ i) -
            (P.map koalaSexticFrobenius.toRingHom).eval
              (IRSProfile.domain i)) = 0 := by
  have hreceivedRaw := congrArg
    (fun R : IRSProfile.Field[X] ↦ R.eval z)
    (quotient_relationWord_at_coordinate
      f₀ f₁ q H A' B' C' hAfactor hBfactor hCfactor i hi)
  have hreceived :
      (C'.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) =
        (A'.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
            (f₀ i + z * f₁ i) +
          (B'.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
            koalaSexticFrobenius (f₀ i + z * f₁ i) := by
    simpa only [Polynomial.eval_add, Polynomial.eval_mul,
      score6400ReceivedPolynomial_eval,
      score6400FrobeniusReceivedPolynomial_eval,
      eval_C_eval_eq_map_eval_eval] using hreceivedRaw
  have hdecoded := congrArg
    (fun R : IRSProfile.Field[X] ↦ R.eval (IRSProfile.domain i)) howner
  simp only [Polynomial.eval_add, Polynomial.eval_mul] at hdecoded
  calc
    _ =
        ((A'.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
            (f₀ i + z * f₁ i) +
          (B'.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
            koalaSexticFrobenius (f₀ i + z * f₁ i)) -
        ((A'.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
            P.eval (IRSProfile.domain i) +
          (B'.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
            (P.map koalaSexticFrobenius.toRingHom).eval
              (IRSProfile.domain i)) := by ring
    _ = 0 := by rw [← hreceived, ← hdecoded, sub_self]

/-- Production endpoint: the normalized rank-one triple has a single fixed
coordinate defect set, independent of both the challenge and the decoded
owner.  Its size is bounded by the degree of the cancelled full gcd, and the
received-minus-owner word satisfies the normalized homogeneous semilinear
equation at every other source coordinate. -/
theorem exists_score6400_rankOne_fixedCoordinateSemilinearRelation
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLtwo : 2 ≤ L)
    (hrankOne : ∀ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 = 0)
    (T : Finset IRSProfile.Field)
    (hTcard : ownerFloor ≤ T.card)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    ∃ q : Score6400LocatorMinorIndex → IRSProfile.Field[X],
      ∃ H A' B' C' : IRSProfile.Field[X][X],
        ∃ Fixed : Finset IRSProfile.Index,
          q ∈ LinearMap.ker
              (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin ∧
          (∀ n, (q n).natDegree ≤ 76779 * 2130706433) ∧
          H.IsPrimitive ∧ 0 < H.natDegree ∧
          H.natDegree ≤ homogeneousLocatorCap ∧
          (score6400PolynomialLocatorRelationPair q).1.1 = H * A' ∧
          (score6400PolynomialLocatorRelationPair q).2.1 = H * B' ∧
          score6400PolynomialLocatorPairToCode f₀ f₁ q = H * C' ∧
          IsCoprime
            (A'.map (algebraMap IRSProfile.Field[X]
              (FractionRing IRSProfile.Field[X])))
            (B'.map (algebraMap IRSProfile.Field[X]
              (FractionRing IRSProfile.Field[X]))) ∧
          (A' ≠ 0 ∨ B' ≠ 0) ∧
          Fixed = fixedCoordinateDefect H ∧
          Fixed.card ≤ H.natDegree ∧
          ∀ z ∈ T,
            ∀ A : Finset IRSProfile.Index, ∀ P : IRSProfile.Field[X],
              185364 ≤ A.card →
              P.natDegree ≤ 131071 →
              (∀ i ∈ A,
                P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) →
              C'.map (Polynomial.evalRingHom z) =
                  A'.map (Polynomial.evalRingHom z) * P +
                    B'.map (Polynomial.evalRingHom z) *
                      P.map koalaSexticFrobenius.toRingHom ∧
                ∀ i, i ∉ Fixed →
                  (A'.map (Polynomial.evalRingHom z)).eval
                        (IRSProfile.domain i) *
                      ((f₀ i + z * f₁ i) -
                        P.eval (IRSProfile.domain i)) +
                    (B'.map (Polynomial.evalRingHom z)).eval
                        (IRSProfile.domain i) *
                      (koalaSexticFrobenius (f₀ i + z * f₁ i) -
                        (P.map koalaSexticFrobenius.toRingHom).eval
                          (IRSProfile.domain i)) = 0 := by
  classical
  obtain ⟨q, H, A', B', C', hqker, hqdegree, hHprimitive,
      hHpositive, hHcap, hAfactor, hBfactor, hCfactor, hcoprime,
      hpairNe, howners⟩ :=
    exists_score6400_rankOne_primitiveTripleQuotient
      f₀ f₁ L hkernelRank hLtwo hrankOne T hTcard hbad hnotOld
  let Fixed := fixedCoordinateDefect H
  have hHne : H ≠ 0 := by
    intro hzero
    subst H
    simpa using hHpositive
  have hFixedCard : Fixed.card ≤ H.natDegree := by
    simpa only [Fixed] using fixedCoordinateDefect_card_le H hHne
  refine ⟨q, H, A', B', C', Fixed, hqker, hqdegree, hHprimitive,
    hHpositive, hHcap, hAfactor, hBfactor, hCfactor, hcoprime,
    hpairNe, rfl, hFixedCard, ?_⟩
  intro z hz A P hAcard hPdegree hagree
  have howner := howners z hz A P hAcard hPdegree hagree
  refine ⟨howner, ?_⟩
  intro i hi
  apply homogeneous_error_relation_at_coordinate
    f₀ f₁ q H A' B' C' hAfactor hBfactor hCfactor z P howner i
  simpa only [Fixed] using hi

end BCHKSPrimitiveTripleRelation6400
end ProximityPrize.SubmissionLower

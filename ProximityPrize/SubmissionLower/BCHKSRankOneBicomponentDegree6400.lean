import ProximityPrize.SubmissionLower.BCHKSPrimitiveTripleBicomponent6400
import ProximityPrize.SubmissionLower.BCHKSRankOneDegreeProduction6400

/-!
# Rank-one bicomponent endpoint with nullity degree descent

This wrapper preserves every output of the production primitive-triple
endpoint and adds the dimension rebate for its Frobenius direction:

```text
deg_X B' <= 22489 - L.
```
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneBicomponentDegree6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSTwoAxisResultant6400
open BCHKSPrimitiveTripleRelation6400
open BCHKSPrimitiveTripleBicomponent6400
open BCHKSRankOneDegreeProduction6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

private abbrev CramerChallengeCap : Nat := 76779 * 2130706433

/-- The selected bicomponent primitive triple inherits the full kernel
nullity rebate on its Frobenius quotient direction. -/
theorem exists_score6400_rankOne_bicomponentPrimitiveTriple_with_degree
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
          (∀ n, (q n).natDegree ≤ CramerChallengeCap) ∧
          H.IsPrimitive ∧ 0 < H.natDegree ∧
          H.natDegree ≤ 22488 ∧
          (score6400PolynomialLocatorRelationPair q).1.1 = H * A' ∧
          (score6400PolynomialLocatorRelationPair q).2.1 = H * B' ∧
          score6400PolynomialLocatorPairToCode f₀ f₁ q = H * C' ∧
          IsCoprime
            (A'.map (algebraMap IRSProfile.Field[X]
              (FractionRing IRSProfile.Field[X])))
            (B'.map (algebraMap IRSProfile.Field[X]
              (FractionRing IRSProfile.Field[X]))) ∧
          A' ≠ 0 ∧ B' ≠ 0 ∧
          B'.natDegree ≤ locatorFrobeniusRows6400 - L ∧
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
  obtain ⟨q, H, A', B', C', Fixed, hqker, hqdegree, hHprimitive,
      hHpositive, hHcap, hAfactor, hBfactor, hCfactor, hcoprime,
      hAne, hBne, hFixed, hFixedCard, howners⟩ :=
    exists_score6400_rankOne_bicomponentPrimitiveTriple
      f₀ f₁ L hkernelRank hLtwo hrankOne T hTcard hbad hnotOld
  have hHne : H ≠ 0 := by
    intro hzero
    rw [hzero] at hHpositive
    simp at hHpositive
  have hBdegree :
      B'.natDegree ≤ locatorFrobeniusRows6400 - L :=
    score6400_primitiveFrobenius_natDegree_le_sub_nullity
      f₀ f₁ L q H A' B' hkernelRank hqker hHne hBne
        hAfactor hBfactor hcoprime hrankOne
  exact ⟨q, H, A', B', C', Fixed, hqker, hqdegree, hHprimitive,
    hHpositive, hHcap, hAfactor, hBfactor, hCfactor, hcoprime,
    hAne, hBne, hBdegree, hFixed, hFixedCard, howners⟩

end BCHKSRankOneBicomponentDegree6400
end ProximityPrize.SubmissionLower

import ProximityPrize.SubmissionLower.BCHKSRecursiveTwoAxisDescent6400

/-!
# Cancelling a primitive global triple factor

A primitive polynomial over `F[Z]` cannot become the zero polynomial after
specializing `Z` to a field element.  Consequently a primitive factor common
to all three lanes of a locator relation cancels from every owner equation,
with no exceptional challenge specializations.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSPrimitiveTripleQuotient6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSTwoAxisResultant6400
open BCHKSRecursiveTwoAxisDescent6400
open BCHKSExactSparsification6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- A primitive polynomial over `F[Z]` has a nonzero specialization at every
field element.  Otherwise `Z-z` divides every coefficient, contradicting
primitivity. -/
theorem map_eval_ne_zero_of_isPrimitive
    {F : Type} [Field F]
    (H : F[X][X]) (hHprimitive : H.IsPrimitive) (z : F) :
    H.map (Polynomial.evalRingHom z) ≠ 0 := by
  intro hmap
  have hcoeff : ∀ n, (H.coeff n).eval z = 0 := by
    intro n
    have hn := congrArg (fun P : F[X] ↦ P.coeff n) hmap
    change (Polynomial.evalRingHom z) (H.coeff n) = 0
    simpa only [Polynomial.coeff_map, map_zero, Polynomial.coeff_zero] using hn
  have hdivCoeff : ∀ n, Polynomial.X - Polynomial.C z ∣ H.coeff n := by
    intro n
    rw [Polynomial.dvd_iff_isRoot]
    exact hcoeff n
  have hconstantDiv :
      Polynomial.C (Polynomial.X - Polynomial.C z) ∣ H :=
    (Polynomial.C_dvd_iff_dvd_coeff
      (Polynomial.X - Polynomial.C z) H).mpr hdivCoeff
  exact Polynomial.not_isUnit_X_sub_C z
    (hHprimitive (Polynomial.X - Polynomial.C z) hconstantDiv)

/-- Cancel a primitive factor from a prescribed pair of homogeneous
quotients and choose only the affine quotient.  This form preserves any
normalization property already proved about the homogeneous pair. -/
theorem exists_primitiveTripleQuotient_of_factors
    {F : Type} [Field F]
    (H A B C A' B' : F[X][X])
    (hHprimitive : H.IsPrimitive)
    (hAfactor : A = H * A') (hBfactor : B = H * B')
    (hHC : H ∣ C) :
    ∃ C' : F[X][X], C = H * C' ∧
      ∀ (z : F) (P S : F[X]),
        C.map (Polynomial.evalRingHom z) =
            A.map (Polynomial.evalRingHom z) * P +
              B.map (Polynomial.evalRingHom z) * S →
          C'.map (Polynomial.evalRingHom z) =
            A'.map (Polynomial.evalRingHom z) * P +
              B'.map (Polynomial.evalRingHom z) * S := by
  let C' : F[X][X] := Classical.choose hHC
  have hCfactor : C = H * C' := Classical.choose_spec hHC
  refine ⟨C', hCfactor, ?_⟩
  intro z P S howner
  have hHmap : H.map (Polynomial.evalRingHom z) ≠ 0 :=
    map_eval_ne_zero_of_isPrimitive H hHprimitive z
  apply mul_left_cancel₀ hHmap
  calc
    H.map (Polynomial.evalRingHom z) *
          C'.map (Polynomial.evalRingHom z) =
        C.map (Polynomial.evalRingHom z) := by
          rw [hCfactor, Polynomial.map_mul]
    _ = A.map (Polynomial.evalRingHom z) * P +
          B.map (Polynomial.evalRingHom z) * S := howner
    _ = H.map (Polynomial.evalRingHom z) *
          (A'.map (Polynomial.evalRingHom z) * P +
            B'.map (Polynomial.evalRingHom z) * S) := by
          rw [hAfactor, hBfactor, Polynomial.map_mul, Polynomial.map_mul]
          ring

/-- Abstract cancellation of a primitive factor common to three bivariate
lanes.  The quotients obey the specialized affine relation at every
challenge, not merely away from a bounded exceptional set. -/
theorem exists_primitiveTripleQuotients
    {F : Type} [Field F]
    (H A B C : F[X][X])
    (hHprimitive : H.IsPrimitive)
    (hHA : H ∣ A) (hHB : H ∣ B) (hHC : H ∣ C) :
    ∃ A' B' C' : F[X][X],
      A = H * A' ∧ B = H * B' ∧ C = H * C' ∧
      ∀ (z : F) (P S : F[X]),
        C.map (Polynomial.evalRingHom z) =
            A.map (Polynomial.evalRingHom z) * P +
              B.map (Polynomial.evalRingHom z) * S →
          C'.map (Polynomial.evalRingHom z) =
            A'.map (Polynomial.evalRingHom z) * P +
              B'.map (Polynomial.evalRingHom z) * S := by
  let A' : F[X][X] := Classical.choose hHA
  let B' : F[X][X] := Classical.choose hHB
  have hAfactor : A = H * A' := Classical.choose_spec hHA
  have hBfactor : B = H * B' := Classical.choose_spec hHB
  obtain ⟨C', hCfactor, hcancel⟩ :=
    exists_primitiveTripleQuotient_of_factors
      H A B C A' B' hHprimitive hAfactor hBfactor hHC
  exact ⟨A', B', C', hAfactor, hBfactor, hCfactor, hcancel⟩

/-- Production endpoint: every retained rank-one branch supplies a nonzero
quotient pair whose specialized lanes satisfy the decoded-polynomial owner
identity at every retained challenge. -/
theorem exists_score6400_rankOne_primitiveTripleQuotient
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
        ∀ z ∈ T,
          ∀ A : Finset IRSProfile.Index, ∀ P : IRSProfile.Field[X],
            185364 ≤ A.card →
            P.natDegree ≤ 131071 →
            (∀ i ∈ A,
              P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) →
            C'.map (Polynomial.evalRingHom z) =
              A'.map (Polynomial.evalRingHom z) * P +
                B'.map (Polynomial.evalRingHom z) *
                  P.map koalaSexticFrobenius.toRingHom := by
  classical
  obtain ⟨q, H, A', B', hqker, hqdegree, hHprimitive, hHpositive,
      hAfactorRaw, hBfactorRaw, hcoprime, hpairNe, hHcap, hHdivC⟩ :=
    exists_score6400_rankOne_globalTripleCoprimeFactor
      f₀ f₁ L hkernelRank hLtwo hrankOne T hTcard hbad hnotOld
  let A₀ := (score6400PolynomialLocatorRelationPair q).1.1
  let B₀ := (score6400PolynomialLocatorRelationPair q).2.1
  let C₀ := score6400PolynomialLocatorPairToCode f₀ f₁ q
  have hAfactor : A₀ = H * A' := by
    simpa only [A₀] using hAfactorRaw
  have hBfactor : B₀ = H * B' := by
    simpa only [B₀] using hBfactorRaw
  obtain ⟨C', hCfactor, hcancel⟩ :=
    exists_primitiveTripleQuotient_of_factors
      H A₀ B₀ C₀ A' B' hHprimitive hAfactor hBfactor
        (by simpa only [C₀] using hHdivC)
  have hquotientNe : A' ≠ 0 ∨ B' ≠ 0 := by
    rcases hpairNe with hAne | hBne
    · left
      intro hzero
      apply hAne
      change A₀ = 0
      rw [hAfactor, hzero, mul_zero]
    · right
      intro hzero
      apply hBne
      change B₀ = 0
      rw [hBfactor, hzero, mul_zero]
  refine ⟨q, H, A', B', C', hqker, hqdegree, hHprimitive,
    hHpositive, hHcap, ?_, ?_, ?_, hcoprime, hquotientNe, ?_⟩
  · simpa only [A₀] using hAfactor
  · simpa only [B₀] using hBfactor
  · simpa only [C₀] using hCfactor
  · intro z _hz A P hAcard hPdegree hagree
    apply hcancel z P (P.map koalaSexticFrobenius.toRingHom)
    simpa only [A₀, B₀, C₀] using
      score6400PolynomialLocatorPairToCode_map_eval_eq_owner_mapped
        f₀ f₁ q hqker z A P hAcard hPdegree hagree

end BCHKSPrimitiveTripleQuotient6400
end ProximityPrize.SubmissionLower

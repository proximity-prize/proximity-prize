import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveChallengeRatioRigidity6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveCommonContentFixedPair6401
open Polynomial
open BCHKSFrobeniusOffsetProductDegreeAudit6401
open BCHKSFrobeniusGraphHilbert90Audit6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveGraphNormRigidity6401
open BCHKSExtremePrimitiveGraphNormFixedContent6401
open BCHKSExtremePrimitiveChallengeRatioRigidity6401
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
section TwistCompatibility
variable {F : Type} [Field F] [DecidableEq F]
theorem graphTwistSix_C_eq_C_challengeTwistSix6401
    (sigma : F →+* F) (q : Nat) (c : F[X]) :
    graphTwistSix6401 sigma q (Polynomial.C c) =
      Polynomial.C (challengeTwistSixRingHom6401 sigma q c) := by
  simp [graphTwistSix6401, graphTwistFive6401,
    graphTwistFour6401, graphTwistThree6401, graphTwistTwo6401,
    graphTwist6401, challengeTwistSixRingHom6401,
    challengeFrobeniusIterateRingHom6401]
theorem graphTwistSix_mul6401
    (sigma : F →+* F) (q : Nat) (P Q : F[X][X]) :
    graphTwistSix6401 sigma q (P * Q) =
      graphTwistSix6401 sigma q P * graphTwistSix6401 sigma q Q := by
  simp [graphTwistSix6401, graphTwistFive6401,
    graphTwistFour6401, graphTwistThree6401, graphTwistTwo6401,
    graphTwist6401, Polynomial.map_mul]
theorem graphTwistSix_fixedLocator6401
    (sigma : F →+* F) (q : Nat)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (P : F[X]) :
    graphTwistSix6401 sigma q (P.map Polynomial.C) =
      P.map Polynomial.C := by
  ext n m
  simp [graphTwistSix6401, graphTwistFive6401,
    graphTwistFour6401, graphTwistThree6401, graphTwistTwo6401,
    graphTwist6401, challengeFrobeniusRingHom6401,
    challengeFrobenius, horder]
end TwistCompatibility
section ContentCross
variable {F : Type} [Field F] [DecidableEq F]
theorem content_sixthTwist_cross_of_fixedLaneDecomposition6401
    (sigma : F →+* F) (q : Nat)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (A B : F[X][X]) (cA cB : F[X]) (A0 B0 : F[X])
    (hA0 : A0 ≠ 0) (hB0 : B0 ≠ 0)
    (hAdecomp : A = Polynomial.C cA * A0.map Polynomial.C)
    (hBdecomp : B = Polynomial.C cB * B0.map Polynomial.C)
    (hcross : B * graphTwistSix6401 sigma q A =
      A * graphTwistSix6401 sigma q B) :
    cB * challengeTwistSixRingHom6401 sigma q cA =
      cA * challengeTwistSixRingHom6401 sigma q cB := by
  let A0C : F[X][X] := A0.map Polynomial.C
  let B0C : F[X][X] := B0.map Polynomial.C
  let T := challengeTwistSixRingHom6401 sigma q
  have hA0C : A0C ≠ 0 :=
    (Polynomial.map_ne_zero_iff Polynomial.C_injective).2 hA0
  have hB0C : B0C ≠ 0 :=
    (Polynomial.map_ne_zero_iff Polynomial.C_injective).2 hB0
  have hfixed : A0C * B0C ≠ 0 := mul_ne_zero hA0C hB0C
  have htwistA : graphTwistSix6401 sigma q A =
      Polynomial.C (T cA) * A0C := by
    calc
      graphTwistSix6401 sigma q A =
          graphTwistSix6401 sigma q (Polynomial.C cA) *
            graphTwistSix6401 sigma q (A0.map Polynomial.C) := by
              rw [hAdecomp, graphTwistSix_mul6401]
      _ = Polynomial.C (T cA) * A0C := by
        rw [graphTwistSix_C_eq_C_challengeTwistSix6401,
          graphTwistSix_fixedLocator6401 sigma q horder]
  have htwistB : graphTwistSix6401 sigma q B =
      Polynomial.C (T cB) * B0C := by
    calc
      graphTwistSix6401 sigma q B =
          graphTwistSix6401 sigma q (Polynomial.C cB) *
            graphTwistSix6401 sigma q (B0.map Polynomial.C) := by
              rw [hBdecomp, graphTwistSix_mul6401]
      _ = Polynomial.C (T cB) * B0C := by
        rw [graphTwistSix_C_eq_C_challengeTwistSix6401,
          graphTwistSix_fixedLocator6401 sigma q horder]
  have hCcross :
      Polynomial.C (cB * T cA) = Polynomial.C (cA * T cB) := by
    apply mul_right_cancel₀ hfixed
    calc
      Polynomial.C (cB * T cA) * (A0C * B0C) =
          B * graphTwistSix6401 sigma q A := by
            rw [hBdecomp, htwistA]
            simp only [map_mul]
            ring
      _ = A * graphTwistSix6401 sigma q B := hcross
      _ = Polynomial.C (cA * T cB) * (A0C * B0C) := by
            rw [hAdecomp, htwistB]
            simp only [map_mul]
            ring
  exact Polynomial.C_injective hCcross
theorem exists_commonContent_fixedPair_of_fixedLaneDecomposition6401
    (sigma : F →+* F) (q : Nat) (hq : 1 < q)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (A B : F[X][X]) (cA cB : F[X]) (A0 B0 : F[X])
    (hcA : cA ≠ 0) (hcB : cB ≠ 0)
    (hA0 : A0 ≠ 0) (hB0 : B0 ≠ 0)
    (hAdecomp : A = Polynomial.C cA * A0.map Polynomial.C)
    (hBdecomp : B = Polynomial.C cB * B0.map Polynomial.C)
    (hcross : B * graphTwistSix6401 sigma q A =
      A * graphTwistSix6401 sigma q B) :
    ∃ G U0 U1 : F[X],
      G ≠ 0 ∧ U0 ≠ 0 ∧ U1 ≠ 0 ∧
        A = Polynomial.C G * U0.map Polynomial.C ∧
        B = Polynomial.C G * U1.map Polynomial.C := by
  have hcontentCross :=
    content_sixthTwist_cross_of_fixedLaneDecomposition6401
      sigma q horder A B cA cB A0 B0 hA0 hB0
      hAdecomp hBdecomp hcross
  obtain ⟨G, a, b, hG, ha, hb, hcAfactor, hcBfactor⟩ :=
    exists_commonPolynomial_constantMultiples_of_sixthTwist_cross6401
      sigma q hq cA cB hcA hcB hcontentCross
  let U0 : F[X] := Polynomial.C a * A0
  let U1 : F[X] := Polynomial.C b * B0
  have hU0 : U0 ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr ha) hA0
  have hU1 : U1 ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hb) hB0
  refine ⟨G, U0, U1, hG, hU0, hU1, ?_, ?_⟩
  · rw [hAdecomp, hcAfactor]
    dsimp only [U0]
    simp only [map_mul]
    rw [Polynomial.map_mul, Polynomial.map_C]
    ring
  · rw [hBdecomp, hcBfactor]
    dsimp only [U1]
    simp only [map_mul]
    rw [Polynomial.map_mul, Polynomial.map_C]
    ring
end ContentCross
end BCHKSExtremePrimitiveCommonContentFixedPair6401
end ProximityPrize.SubmissionLower

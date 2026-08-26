import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveTerminalCommonContentCoprime6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveRecursiveNormObstruction6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveTerminalFixedPairOrbit6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSFrobeniusGraphHilbert90Audit6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveRecursiveNormObstruction6401
open BCHKSExtremePrimitiveTerminalCommonContentCoprime6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
section FixedLocatorOrbit
variable {F : Type} [Field F] [DecidableEq F]
theorem graphTwist_fixedLocator_eq6401
    (sigma : F →+* F) (q : Nat) (U : F[X]) :
    graphTwist6401 sigma q (U.map Polynomial.C) =
      (U.map sigma).map Polynomial.C := by
  ext n m
  simp [graphTwist6401, challengeFrobeniusRingHom6401,
    Polynomial.map_map]
theorem graphFrobeniusNormSix_fixedLocator_eq6401
    (sigma : F →+* F) (q : Nat) (U : F[X]) :
    graphFrobeniusNormSix6401 sigma q (U.map Polynomial.C) =
      (polynomialFrobeniusNormSix sigma U).map Polynomial.C := by
  simp only [graphFrobeniusNormSix6401, graphTwistTwo6401,
    graphTwistThree6401, graphTwistFour6401, graphTwistFive6401]
  rw [graphTwist_fixedLocator_eq6401]
  rw [graphTwist_fixedLocator_eq6401]
  rw [graphTwist_fixedLocator_eq6401]
  rw [graphTwist_fixedLocator_eq6401]
  rw [graphTwist_fixedLocator_eq6401]
  simp only [polynomialFrobeniusNormSix, Polynomial.map_mul]
theorem fixedPair_coefficientNorm_eq_of_commonContent_of_graphNorm_eq6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q)
    (A B : F[X][X]) (G U0 U1 : F[X])
    (hG : G ≠ 0)
    (hA : A = Polynomial.C G * U0.map Polynomial.C)
    (hB : B = Polynomial.C G * U1.map Polynomial.C)
    (hnorm : graphFrobeniusNormSix6401 sigma q A =
      graphFrobeniusNormSix6401 sigma q B) :
    polynomialFrobeniusNormSix sigma U0 =
      polynomialFrobeniusNormSix sigma U1 := by
  have hCG : (Polynomial.C G : F[X][X]) ≠ 0 :=
    Polynomial.C_ne_zero.mpr hG
  have hnormG : graphFrobeniusNormSix6401 sigma q
      (Polynomial.C G) ≠ 0 :=
    graphFrobeniusNormSix_ne_zero6401 sigma q hq _ hCG
  have hfixedGraph :
      graphFrobeniusNormSix6401 sigma q (U0.map Polynomial.C) =
        graphFrobeniusNormSix6401 sigma q (U1.map Polynomial.C) := by
    apply mul_left_cancel₀ hnormG
    rw [← graphFrobeniusNormSix_mul6401,
      ← graphFrobeniusNormSix_mul6401, ← hA, ← hB]
    exact hnorm
  rw [graphFrobeniusNormSix_fixedLocator_eq6401,
    graphFrobeniusNormSix_fixedLocator_eq6401] at hfixedGraph
  exact (Polynomial.map_injective Polynomial.C Polynomial.C_injective)
    hfixedGraph
end FixedLocatorOrbit
section RecursiveTerminalOrbit
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
variable {W : PrimitivePuncturedOwnerWindow6401
  sigma alpha u0 u1 S Aset Owner}
theorem exists_recursiveCommonContent_coprimeFixedPair_normEq6401
    (C : RecursivePrimitiveLaneState6401 W)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hresultant : C.laneResultant6401 ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q6401 C.laneZero6401 =
      graphFrobeniusNormSix6401 sigma q6401 C.laneOne6401) :
    ∃ G U0 U1 : F[X],
      G ≠ 0 ∧ U0 ≠ 0 ∧ U1 ≠ 0 ∧ IsCoprime U0 U1 ∧
        polynomialFrobeniusNormSix sigma U0 =
          polynomialFrobeniusNormSix sigma U1 ∧
        C.laneZero6401 = Polynomial.C G * U0.map Polynomial.C ∧
        C.laneOne6401 = Polynomial.C G * U1.map Polynomial.C := by
  obtain ⟨G, U0, U1, hG, hU0, hU1, hcop, hzero, hone⟩ :=
    exists_recursiveCommonContent_coprimeFixedPair_of_resultant_ne_zero_of_graphNorm_eq6401
      C horder hresultant hnorm
  have hfixedNorm :=
    fixedPair_coefficientNorm_eq_of_commonContent_of_graphNorm_eq6401
      sigma q6401 (by native_decide)
        C.laneZero6401 C.laneOne6401 G U0 U1 hG hzero hone hnorm
  exact ⟨G, U0, U1, hG, hU0, hU1, hcop, hfixedNorm, hzero, hone⟩
end RecursiveTerminalOrbit
end BCHKSExtremePrimitiveTerminalFixedPairOrbit6401
end ProximityPrize.SubmissionLower

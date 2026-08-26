import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveCommonContentFixedPair6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveTerminalCommonContent6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSFrobeniusGraphHilbert90Audit6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveGraphNormRigidity6401
open BCHKSExtremePrimitiveGraphNormFixedContent6401
open BCHKSExtremePrimitiveCommonContentFixedPair6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
section GenericTerminal
variable {F : Type} [Field F] [DecidableEq F]
theorem exists_commonContent_fixedPair_of_resultant_ne_zero_of_graphNorm_eq6401
    (sigma : F →+* F) (q : Nat) (hq : 1 < q)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (A B : F[X][X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hresultant : Polynomial.resultant A B ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q A =
      graphFrobeniusNormSix6401 sigma q B) :
    ∃ G U0 U1 : F[X],
      G ≠ 0 ∧ U0 ≠ 0 ∧ U1 ≠ 0 ∧
        A = Polynomial.C G * U0.map Polynomial.C ∧
        B = Polynomial.C G * U1.map Polynomial.C := by
  obtain ⟨A0, B0, hA0fixed, hB0fixed⟩ :=
    exists_fixedPrimitiveParts_of_resultant_ne_zero_of_graphNorm_eq6401
      sigma q hq A B hA hB hresultant hnorm
  have hA0 : A0 ≠ 0 := by
    intro hzero
    apply A.primPart_ne_zero
    rw [hA0fixed, hzero]
    simp
  have hB0 : B0 ≠ 0 := by
    intro hzero
    apply B.primPart_ne_zero
    rw [hB0fixed, hzero]
    simp
  have hcA : A.content ≠ 0 := by
    rwa [Ne, Polynomial.content_eq_zero_iff]
  have hcB : B.content ≠ 0 := by
    rwa [Ne, Polynomial.content_eq_zero_iff]
  have hAdecomp : A = Polynomial.C A.content * A0.map Polynomial.C := by
    calc
      A = Polynomial.C A.content * A.primPart :=
        A.eq_C_content_mul_primPart
      _ = Polynomial.C A.content * A0.map Polynomial.C := by
        rw [hA0fixed]
  have hBdecomp : B = Polynomial.C B.content * B0.map Polynomial.C := by
    calc
      B = Polynomial.C B.content * B.primPart :=
        B.eq_C_content_mul_primPart
      _ = Polynomial.C B.content * B0.map Polynomial.C := by
        rw [hB0fixed]
  have hcross : B * graphTwistSix6401 sigma q A =
      A * graphTwistSix6401 sigma q B :=
    graphNorm_eq_imp_sixthTwist_cross6401
      sigma q (Nat.zero_lt_of_lt hq) A B hA hB hnorm
  exact exists_commonContent_fixedPair_of_fixedLaneDecomposition6401
    sigma q hq horder A B A.content B.content A0 B0
    hcA hcB hA0 hB0 hAdecomp hBdecomp hcross
end GenericTerminal
section RecursiveTerminal
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
variable {W : PrimitivePuncturedOwnerWindow6401
  sigma alpha u0 u1 S Aset Owner}
theorem exists_recursiveCommonContent_fixedPair_of_resultant_ne_zero_of_graphNorm_eq6401
    (C : RecursivePrimitiveLaneState6401 W)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hresultant : C.laneResultant6401 ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q6401 C.laneZero6401 =
      graphFrobeniusNormSix6401 sigma q6401 C.laneOne6401) :
    ∃ G U0 U1 : F[X],
      G ≠ 0 ∧ U0 ≠ 0 ∧ U1 ≠ 0 ∧
        C.laneZero6401 = Polynomial.C G * U0.map Polynomial.C ∧
        C.laneOne6401 = Polynomial.C G * U1.map Polynomial.C := by
  obtain ⟨hA, hB⟩ := recursiveLanes_ne_zero_of_graphNorm_eq6401 C hnorm
  exact exists_commonContent_fixedPair_of_resultant_ne_zero_of_graphNorm_eq6401
    sigma q6401 (by native_decide) horder
    C.laneZero6401 C.laneOne6401 hA hB hresultant hnorm
end RecursiveTerminal
end BCHKSExtremePrimitiveTerminalCommonContent6401
end ProximityPrize.SubmissionLower

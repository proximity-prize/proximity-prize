import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveTerminalCommonContent6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveResultantFractionField6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveTerminalCommonContentCoprime6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveResultantFractionField6401
open BCHKSExtremePrimitiveTerminalCommonContent6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section GenericCoprimeFixedPair
variable {F : Type} [Field F] [DecidableEq F]
theorem fixedPair_isCoprime_of_commonContent_of_resultant_ne_zero6401
    (A B : F[X][X]) (G U0 U1 : F[X])
    (hG : G ≠ 0) (hU0 : U0 ≠ 0) (_hU1 : U1 ≠ 0)
    (hA : A = Polynomial.C G * U0.map Polynomial.C)
    (hB : B = Polynomial.C G * U1.map Polynomial.C)
    (hresultant : Polynomial.resultant A B ≠ 0) :
    IsCoprime U0 U1 := by
  let K := FractionRing F[X]
  let f : F[X] →+* K := algebraMap F[X] K
  have hf : Function.Injective f := IsFractionRing.injective F[X] K
  have hcopAB : IsCoprime
      (A.map f) (B.map f) :=
    resultant_ne_zero_isCoprime_fractionMap6401 A B
      (Or.inl (by
        rw [hA]
        exact mul_ne_zero (Polynomial.C_ne_zero.mpr hG)
          ((Polynomial.map_ne_zero_iff Polynomial.C_injective).2 hU0)))
      hresultant
  have hfG : f G ≠ 0 := (map_ne_zero_iff f hf).2 hG
  have hunitG : IsUnit (Polynomial.C (f G) : K[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hfG)
  have hcopFixedK : IsCoprime
      ((U0.map Polynomial.C).map f)
      ((U1.map Polynomial.C).map f) := by
    apply (isCoprime_mul_unit_left hunitG _ _).mp
    simpa [hA, hB, Polynomial.map_mul] using hcopAB
  let g : F →+* K := f.comp Polynomial.C
  have hg : Function.Injective g := hf.comp Polynomial.C_injective
  have hcopMapped : IsCoprime (U0.map g) (U1.map g) := by
    simpa [g, Polynomial.map_map] using hcopFixedK
  have hresMapped : Polynomial.resultant (U0.map g) (U1.map g) ≠ 0 :=
    Polynomial.resultant_ne_zero (U0.map g) (U1.map g) hcopMapped
  have hdeg0 : (U0.map g).natDegree = U0.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hg U0
  have hdeg1 : (U1.map g).natDegree = U1.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hg U1
  have hresMappedFixed :
      Polynomial.resultant (U0.map g) (U1.map g)
        U0.natDegree U1.natDegree ≠ 0 := by
    simpa only [hdeg0, hdeg1] using hresMapped
  have hmapRes : g (Polynomial.resultant U0 U1) ≠ 0 := by
    rw [← Polynomial.resultant_map_map]
    exact hresMappedFixed
  have hres : Polynomial.resultant U0 U1 ≠ 0 :=
    (map_ne_zero_iff g hg).mp hmapRes
  by_contra hnot
  exact hres (Polynomial.resultant_eq_zero_iff.mpr
    ⟨Or.inl hU0, hnot⟩)
theorem exists_commonContent_coprimeFixedPair_of_resultant_ne_zero_of_graphNorm_eq6401
    (sigma : F →+* F) (q : Nat) (hq : 1 < q)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (A B : F[X][X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hresultant : Polynomial.resultant A B ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q A =
      graphFrobeniusNormSix6401 sigma q B) :
    ∃ G U0 U1 : F[X],
      G ≠ 0 ∧ U0 ≠ 0 ∧ U1 ≠ 0 ∧ IsCoprime U0 U1 ∧
        A = Polynomial.C G * U0.map Polynomial.C ∧
        B = Polynomial.C G * U1.map Polynomial.C := by
  obtain ⟨G, U0, U1, hG, hU0, hU1, hdecompA, hdecompB⟩ :=
    exists_commonContent_fixedPair_of_resultant_ne_zero_of_graphNorm_eq6401
      sigma q hq horder A B hA hB hresultant hnorm
  have hcop :=
    fixedPair_isCoprime_of_commonContent_of_resultant_ne_zero6401
      A B G U0 U1 hG hU0 hU1 hdecompA hdecompB hresultant
  exact ⟨G, U0, U1, hG, hU0, hU1, hcop, hdecompA, hdecompB⟩
end GenericCoprimeFixedPair
section RecursiveCoprimeFixedPair
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
variable {W : PrimitivePuncturedOwnerWindow6401
  sigma alpha u0 u1 S Aset Owner}
theorem exists_recursiveCommonContent_coprimeFixedPair_of_resultant_ne_zero_of_graphNorm_eq6401
    (C : RecursivePrimitiveLaneState6401 W)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hresultant : C.laneResultant6401 ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q6401 C.laneZero6401 =
      graphFrobeniusNormSix6401 sigma q6401 C.laneOne6401) :
    ∃ G U0 U1 : F[X],
      G ≠ 0 ∧ U0 ≠ 0 ∧ U1 ≠ 0 ∧ IsCoprime U0 U1 ∧
        C.laneZero6401 = Polynomial.C G * U0.map Polynomial.C ∧
        C.laneOne6401 = Polynomial.C G * U1.map Polynomial.C := by
  obtain ⟨G, U0, U1, hG, hU0, hU1, hzero, hone⟩ :=
    exists_recursiveCommonContent_fixedPair_of_resultant_ne_zero_of_graphNorm_eq6401
      C horder hresultant hnorm
  have hcop :=
    fixedPair_isCoprime_of_commonContent_of_resultant_ne_zero6401
      C.laneZero6401 C.laneOne6401 G U0 U1
        hG hU0 hU1 hzero hone hresultant
  exact ⟨G, U0, U1, hG, hU0, hU1, hcop, hzero, hone⟩
end RecursiveCoprimeFixedPair
end BCHKSExtremePrimitiveTerminalCommonContentCoprime6401
end ProximityPrize.SubmissionLower

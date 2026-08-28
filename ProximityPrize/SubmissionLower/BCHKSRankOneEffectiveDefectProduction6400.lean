import ProximityPrize.SubmissionLower.BCHKSRankOneCramerAffineRoots6400
import ProximityPrize.SubmissionLower.BCHKSPrimitiveTripleBicomponent6400
import ProximityPrize.SubmissionLower.BCHKSGlobalInhomogeneousKeyEquation6400
import ProximityPrize.SubmissionLower.BCHKSGlobalResidualDegreeAbstract6400

/-! # Production rank-one effective-defect degree rebate -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneEffectiveDefectProduction6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSTwoAxisResultant6400
open BCHKSPrimitiveTripleRelation6400
open BCHKSPrimitiveTripleBicomponent6400
open BCHKSGlobalInhomogeneousKeyEquation6400
open BCHKSLocatorAffineMultiplierCompatibility6400
open BCHKSMultiplierDefectAbstract6400
open BCHKSRankOneCramerMultiplierFamily6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Eliminate the selected-family implementation details from the main
effective-defect inequality. -/
theorem score6400_rankOne_effectiveDefect_add_frobeniusDegree_le
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
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B C K : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
    (hq : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin)
    (hH : H ≠ 0) (hB : B ≠ 0)
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q).1.1 = H * A)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q).2.1 = H * B)
    (hCfactor :
      score6400PolynomialLocatorPairToCode f₀ f₁ q = H * C)
    (hcoprime : IsCoprime
      (A.map (algebraMap IRSProfile.Field[X]
        (FractionRing IRSProfile.Field[X])))
      (B.map (algebraMap IRSProfile.Field[X]
        (FractionRing IRSProfile.Field[X]))))
    (hFixed : Fixed = fixedCoordinateDefect H)
    (hFixedCard : Fixed.card ≤ 22488)
    (hCdegree : C.natDegree < 185363)
    (hglobal :
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
            (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C) :
    (effectiveNodalDefect score6400ChallengeFractionDomain Fixed
        (K.map score6400ChallengeIota)).card + B.natDegree ≤
      locatorFrobeniusRows6400 - L := by
  obtain ⟨selection, ⟨family⟩⟩ :=
    exists_score6400_rankOne_Cramer_multiplierFamily
      f₀ f₁ L q H A B hkernelRank hLtwo hq hH hB
      hAfactor hBfactor hcoprime hrankOne
  exact score6400_effectiveDefect_add_frobeniusDegree_le_sub_nullity
    f₀ f₁ L hLtwo selection q H A B C K Fixed family
    hAfactor hBfactor hCfactor hFixed hFixedCard hCdegree hglobal

/-- Compact production witness retaining the owner equations together with
the new effective-defect rebate. -/
structure Score6400RankOneEffectiveDefectData
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (T : Finset IRSProfile.Field) where
  q : Score6400LocatorMinorIndex → IRSProfile.Field[X]
  H : IRSProfile.Field[X][X]
  A : IRSProfile.Field[X][X]
  B : IRSProfile.Field[X][X]
  C : IRSProfile.Field[X][X]
  K : IRSProfile.Field[X][X]
  Fixed : Finset IRSProfile.Index
  q_kernel : q ∈ LinearMap.ker
    (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin
  q_degree : ∀ n, (q n).natDegree ≤ 76779 * 2130706433
  H_primitive : H.IsPrimitive
  H_positive : 0 < H.natDegree
  H_degree : H.natDegree ≤ 22488
  A_factor : (score6400PolynomialLocatorRelationPair q).1.1 = H * A
  B_factor : (score6400PolynomialLocatorRelationPair q).2.1 = H * B
  C_factor : score6400PolynomialLocatorPairToCode f₀ f₁ q = H * C
  coprime : IsCoprime
    (A.map (algebraMap IRSProfile.Field[X]
      (FractionRing IRSProfile.Field[X])))
    (B.map (algebraMap IRSProfile.Field[X]
      (FractionRing IRSProfile.Field[X])))
  A_ne : A ≠ 0
  B_ne : B ≠ 0
  Fixed_eq : Fixed = fixedCoordinateDefect H
  Fixed_card : Fixed.card ≤ H.natDegree
  C_degree : C.natDegree < 185363
  global :
    (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
      A * score6400ReceivedBivariate f₀ f₁ +
        B * score6400FrobeniusReceivedBivariate f₀ f₁ - C
  effective_rebate :
    (effectiveNodalDefect score6400ChallengeFractionDomain Fixed
        (K.map score6400ChallengeIota)).card + B.natDegree ≤
      locatorFrobeniusRows6400 - L
  owners : ∀ z ∈ T,
    ∀ Agreement : Finset IRSProfile.Index, ∀ P : IRSProfile.Field[X],
      185364 ≤ Agreement.card →
      P.natDegree ≤ 131071 →
      (∀ i ∈ Agreement,
        P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) →
      C.map (Polynomial.evalRingHom z) =
          A.map (Polynomial.evalRingHom z) * P +
            B.map (Polynomial.evalRingHom z) *
              P.map koalaSexticFrobenius.toRingHom ∧
        ∀ i, i ∉ Fixed →
          (A.map (Polynomial.evalRingHom z)).eval
                (IRSProfile.domain i) *
              ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
            (B.map (Polynomial.evalRingHom z)).eval
                (IRSProfile.domain i) *
              (koalaSexticFrobenius (f₀ i + z * f₁ i) -
                (P.map koalaSexticFrobenius.toRingHom).eval
                  (IRSProfile.domain i)) = 0

/-- The existing bicomponent primitive-triple constructor always admits the
common global quotient and the stronger effective-defect degree rebate. -/
theorem exists_score6400_rankOne_effectiveDefectData
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
    Nonempty (Score6400RankOneEffectiveDefectData f₀ f₁ L T) := by
  classical
  obtain ⟨q, H, A, B, C, Fixed, hq, hqdegree, hHprimitive,
      hHpositive, hHdegree, hAfactor, hBfactor, hCfactor, hcoprime,
      hAne, hBne, hFixed, hFixedCard, howners⟩ :=
    exists_score6400_rankOne_bicomponentPrimitiveTriple
      f₀ f₁ L hkernelRank hLtwo hrankOne T hTcard hbad hnotOld
  have hHne : H ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hHpositive
    omega
  have hfield :
      76779 * 2130706433 + 2130706433 <
        Fintype.card IRSProfile.Field := by
    rw [CompPoly.Extension.Ext.card_ext]
    norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]
  have hRawCdegree :
      (score6400PolynomialLocatorPairToCode f₀ f₁ q).natDegree <
        185363 :=
    score6400PolynomialLocatorPairToCode_natDegree_lt
      f₀ f₁ q hq (76779 * 2130706433) hqdegree hfield
  have hCdegree : C.natDegree < 185363 :=
    (right_factor_natDegree_le
      (score6400PolynomialLocatorPairToCode f₀ f₁ q)
      H C hHne hCfactor).trans_lt hRawCdegree
  obtain ⟨K, hglobalDefect⟩ :=
    exists_score6400_globalNormalizedResidualQuotient
      f₀ f₁ q H A B C hAfactor hBfactor hCfactor
  have hglobal :
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
            (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C := by
    simpa only [hFixed] using hglobalDefect
  have hFixedSharp : Fixed.card ≤ 22488 := hFixedCard.trans hHdegree
  have hrebat :=
    score6400_rankOne_effectiveDefect_add_frobeniusDegree_le
      f₀ f₁ L hkernelRank hLtwo hrankOne q H A B C K Fixed
      hq hHne hBne hAfactor hBfactor hCfactor hcoprime
      hFixed hFixedSharp hCdegree hglobal
  exact ⟨{
    q := q
    H := H
    A := A
    B := B
    C := C
    K := K
    Fixed := Fixed
    q_kernel := hq
    q_degree := hqdegree
    H_primitive := hHprimitive
    H_positive := hHpositive
    H_degree := hHdegree
    A_factor := hAfactor
    B_factor := hBfactor
    C_factor := hCfactor
    coprime := hcoprime
    A_ne := hAne
    B_ne := hBne
    Fixed_eq := hFixed
    Fixed_card := hFixedCard
    C_degree := hCdegree
    global := hglobal
    effective_rebate := hrebat
    owners := howners }⟩

end BCHKSRankOneEffectiveDefectProduction6400
end ProximityPrize.SubmissionLower

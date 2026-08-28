import ProximityPrize.SubmissionLower.BCHKSEffectiveFixedScaledRelation6400
import ProximityPrize.SubmissionLower.BCHKSCyclicNormMultiplicative6400
import ProximityPrize.SubmissionLower.BCHKSRankOneNullityNormSplit6400

/-! # Cyclic-norm equality from the effective fixed defect -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneEffectiveNorm6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSPrimitiveTripleRelation6400
open BCHKSGlobalInhomogeneousKeyEquation6400
open BCHKSLocatorAffineMultiplierCompatibility6400
open BCHKSMultiplierDefectAbstract6400
open BCHKSEffectiveFixedRelation6400
open BCHKSCyclicNormErrorEvaluator6400
open BCHKSRankOneNullityNormSplit6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Once `L ≥ 9694`, the effective-set rebate gives enough degree room to
scale away every remaining fixed defect and force cyclic-norm equality. -/
theorem score6400_rankOne_specializedNorm_eq_of_effectiveDefect
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B C K : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
    (T : Finset IRSProfile.Field) (L : Nat)
    (hLlarge : 9694 ≤ L)
    (hAdegree : A.natDegree ≤ B.natDegree)
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q).1.1 = H * A)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q).2.1 = H * B)
    (hCfactor :
      score6400PolynomialLocatorPairToCode f₀ f₁ q = H * C)
    (hFixed : Fixed = fixedCoordinateDefect H)
    (hglobal :
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
            (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C)
    (hrebat :
      (score6400EffectiveFixedDefect Fixed K).card + B.natDegree ≤
        locatorFrobeniusRows6400 - L)
    (howners : ∀ z ∈ T,
      ∀ Agreement : Finset IRSProfile.Index, ∀ P : IRSProfile.Field[X],
        185364 ≤ Agreement.card →
        P.natDegree ≤ 131071 →
        (∀ i ∈ Agreement,
          P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) →
        C.map (Polynomial.evalRingHom z) =
          A.map (Polynomial.evalRingHom z) * P +
            B.map (Polynomial.evalRingHom z) *
              P.map koalaSexticFrobenius.toRingHom)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    ∀ z ∈ T,
      koalaCyclicNormSix (A.map (Polynomial.evalRingHom z)) =
        koalaCyclicNormSix (B.map (Polynomial.evalRingHom z)) := by
  let R := score6400EffectiveFixedLocator Fixed K
  let Rlift := score6400EffectiveFixedLocatorLift Fixed K
  let Abar := Rlift * A
  let Bbar := Rlift * B
  let d := (score6400EffectiveFixedDefect Fixed K).card + B.natDegree
  have hroom : 6 * d < 76771 := by
    have hrebat' : d ≤ 22489 - L := by
      simpa only [d, locatorFrobeniusRows6400] using hrebat
    omega
  have hAbarDegree : Abar.natDegree ≤ d := by
    have hraw := score6400_effectiveLocatorLift_mul_natDegree_le
      Fixed K A
    dsimp only [Abar, d]
    exact hraw.trans (Nat.add_le_add_left hAdegree _)
  have hBbarDegree : Bbar.natDegree ≤ d := by
    simpa only [Bbar, d] using
      score6400_effectiveLocatorLift_mul_natDegree_le Fixed K B
  have hscaledRelations :
      ∀ z ∈ T,
        ∀ Agreement : Finset IRSProfile.Index,
          ∀ P : IRSProfile.Field[X],
          185364 ≤ Agreement.card →
          P.natDegree ≤ 131071 →
          (∀ i ∈ Agreement,
            P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) →
          ∀ i, i ∉ (∅ : Finset IRSProfile.Index) →
            (Abar.map (Polynomial.evalRingHom z)).eval
                  (IRSProfile.domain i) *
                ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
              (Bbar.map (Polynomial.evalRingHom z)).eval
                  (IRSProfile.domain i) *
                (koalaSexticFrobenius (f₀ i + z * f₁ i) -
                  (P.map koalaSexticFrobenius.toRingHom).eval
                    (IRSProfile.domain i)) = 0 := by
    intro z hz Agreement P hAgreement hP hagree i _hi
    have howner := howners z hz Agreement P hAgreement hP hagree
    have houtside : ∀ j,
        j ∉ score6400EffectiveFixedDefect Fixed K →
        (A.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain j) *
              ((f₀ j + z * f₁ j) - P.eval (IRSProfile.domain j)) +
            (B.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain j) *
              (koalaSexticFrobenius (f₀ j + z * f₁ j) -
                (P.map koalaSexticFrobenius.toRingHom).eval
                  (IRSProfile.domain j)) = 0 := by
      intro j hj
      exact score6400_homogeneous_error_relation_outside_effective
        f₀ f₁ q H A B C K Fixed hAfactor hBfactor hCfactor
        hFixed hglobal z P howner j hj
    simpa only [Abar, Bbar, Rlift] using
      score6400_effectiveLocator_scaled_relation_everywhere
        f₀ f₁ Fixed K A B z P houtside i
  have hscaledNorm := score6400_rankOne_specializedNorm_eq_of_degreeRoom
    f₀ f₁ Abar Bbar (∅ : Finset IRSProfile.Index) T 0 d
    (by simp) (by simpa using hroom) hAbarDegree hBbarDegree
    hscaledRelations hbad hnotOld
  intro z hz
  have hscaledNormZ := hscaledNorm z hz
  have hscaledNormZ' :
      koalaCyclicNormSix
          (R * A.map (Polynomial.evalRingHom z)) =
        koalaCyclicNormSix
          (R * B.map (Polynomial.evalRingHom z)) := by
    simpa only [Abar, Bbar, Rlift, Polynomial.map_mul,
      score6400EffectiveFixedLocatorLift_map_eval] using hscaledNormZ
  exact koalaCyclicNormSix_cancel_left R
    (A.map (Polynomial.evalRingHom z))
    (B.map (Polynomial.evalRingHom z))
    (by simpa only [R] using
      score6400EffectiveFixedLocator_ne_zero Fixed K)
    hscaledNormZ'

end BCHKSRankOneEffectiveNorm6400
end ProximityPrize.SubmissionLower

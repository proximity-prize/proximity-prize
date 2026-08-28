import ProximityPrize.SubmissionLower.BCHKSRankOneEffectiveDefectProduction6400
import ProximityPrize.SubmissionLower.BCHKSRankOneEffectiveNorm6400

/-! # Production degree split after the effective-defect norm descent -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneEffectiveNormProduction6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSTwoAxisResultant6400
open BCHKSGlobalInhomogeneousKeyEquation6400
open BCHKSMultiplierDefectAbstract6400
open BCHKSEffectiveFixedRelation6400
open BCHKSCyclicNormErrorEvaluator6400
open BCHKSCyclicNormSpecialization6400
open BCHKSRankOneNormSplit6400
open BCHKSRankOneEffectiveDefectProduction6400
open BCHKSRankOneEffectiveNorm6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The compact production witness exposes the effective-defect norm theorem
without requiring downstream callers to unpack its construction fields. -/
theorem Score6400RankOneEffectiveDefectData.specializedNorm_eq
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T)
    (hLlarge : 9694 ≤ L)
    (hAdegree : data.A.natDegree ≤ data.B.natDegree)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    ∀ z ∈ T,
      koalaCyclicNormSix
          (data.A.map (Polynomial.evalRingHom z)) =
        koalaCyclicNormSix
          (data.B.map (Polynomial.evalRingHom z)) := by
  apply score6400_rankOne_specializedNorm_eq_of_effectiveDefect
    f₀ f₁ data.q data.H data.A data.B data.C data.K data.Fixed
      T L hLlarge hAdegree data.A_factor data.B_factor data.C_factor
      data.Fixed_eq data.global
  · simpa only [score6400EffectiveFixedDefect] using
      data.effective_rebate
  · intro z hz Agreement P hAgreement hP hagree
    exact (data.owners z hz Agreement P hAgreement hP hagree).1
  · exact hbad
  · exact hnotOld

/-- Once all retained specializations have equal norms, the nominally low
direction cannot remain strictly asymmetric: the leading challenge
coefficient of the larger Frobenius lane would have too many roots. -/
theorem Score6400RankOneEffectiveDefectData.locatorDegree_eq_of_specializedNorm
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T)
    (hTcard : ownerFloor ≤ T.card)
    (hAdirection : data.A.natDegree ≤ data.B.natDegree)
    (hnorm : ∀ z ∈ T,
      koalaCyclicNormSix
          (data.A.map (Polynomial.evalRingHom z)) =
        koalaCyclicNormSix
          (data.B.map (Polynomial.evalRingHom z))) :
    data.A.natDegree = data.B.natDegree := by
  by_contra hne
  have hstrict : data.A.natDegree < data.B.natDegree := by omega
  have hH : data.H ≠ 0 := by
    have hpositive := data.H_positive
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hpositive
    omega
  have hBchallenge :
      data.B.leadingCoeff.natDegree ≤ 76779 * 2130706433 := by
    simpa only [Polynomial.leadingCoeff] using
      (quotient_coeff_natDegree_le
        (score6400PolynomialLocatorRelationPair data.q).2.1
        data.H data.B (76779 * 2130706433) data.B.natDegree
        data.B_factor hH data.B_ne
        (fun n ↦
          score6400PolynomialLocatorRelationPair_snd_coeff_natDegree_le
            data.q (76779 * 2130706433) n data.q_degree))
  have hsmall := cyclicNormEqual_filter_card_le_of_natDegree_lt
    data.B data.A T (76779 * 2130706433) data.B_ne hstrict hBchallenge
  have hfilter :
      T.filter (fun z ↦
        koalaCyclicNormSix
            (data.B.map (Polynomial.evalRingHom z)) =
          koalaCyclicNormSix
            (data.A.map (Polynomial.evalRingHom z))) = T := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    exact (hnorm z hz).symm
  rw [hfilter] at hsmall
  have hcap : 76779 * 2130706433 < ownerFloor := by
    norm_num [ownerFloor]
  omega

/-- In the effective-defect range, the low branch therefore has equal
primitive locator degrees as well as equal specialized cyclic norms. -/
theorem Score6400RankOneEffectiveDefectData.locatorDegree_eq
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T)
    (hLlarge : 9694 ≤ L)
    (hTcard : ownerFloor ≤ T.card)
    (hAdirection : data.A.natDegree ≤ data.B.natDegree)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    data.A.natDegree = data.B.natDegree := by
  apply Score6400RankOneEffectiveDefectData.locatorDegree_eq_of_specializedNorm
    data hTcard hAdirection
  exact Score6400RankOneEffectiveDefectData.specializedNorm_eq
    data hLlarge hAdirection hbad hnotOld

/-- Every production rank-one branch of nullity at least `9694` has an exact
cyclic-norm degree split.  In the low ordinary direction all retained owners
have equal norms; in the high direction the equal-norm owners occupy at most
one Cramer challenge-degree budget. -/
theorem exists_score6400_rankOne_effectiveNorm_degreeSplit
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLlarge : 9694 ≤ L)
    (hrankOne : ∀ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 = 0)
    (T : Finset IRSProfile.Field)
    (hTcard : ownerFloor ≤ T.card)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    ∃ data : Score6400RankOneEffectiveDefectData f₀ f₁ L T,
      (data.A.natDegree ≤ data.B.natDegree ∧
        ∀ z ∈ T,
          koalaCyclicNormSix
              (data.A.map (Polynomial.evalRingHom z)) =
            koalaCyclicNormSix
              (data.B.map (Polynomial.evalRingHom z))) ∨
      (data.B.natDegree < data.A.natDegree ∧
        (T.filter (fun z ↦
          koalaCyclicNormSix
              (data.A.map (Polynomial.evalRingHom z)) =
            koalaCyclicNormSix
              (data.B.map (Polynomial.evalRingHom z)))).card ≤
          76779 * 2130706433) := by
  have hLtwo : 2 ≤ L := hLlarge.trans' (by norm_num)
  obtain ⟨data⟩ := exists_score6400_rankOne_effectiveDefectData
    f₀ f₁ L hkernelRank hLtwo hrankOne T hTcard hbad hnotOld
  refine ⟨data, ?_⟩
  by_cases hdegree : data.A.natDegree ≤ data.B.natDegree
  · exact Or.inl ⟨hdegree,
      Score6400RankOneEffectiveDefectData.specializedNorm_eq
        data hLlarge hdegree hbad hnotOld⟩
  · have hdegree' : data.B.natDegree < data.A.natDegree := by omega
    refine Or.inr ⟨hdegree', ?_⟩
    simpa using score6400_rankOne_normEqual_filter_card_le_of_degree_gt
      data.q data.H data.A data.B T data.q_degree data.H_positive
        data.A_factor data.A_ne hdegree'

end BCHKSRankOneEffectiveNormProduction6400
end ProximityPrize.SubmissionLower

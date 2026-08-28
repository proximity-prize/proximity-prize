import ProximityPrize.SubmissionLower.BCHKSEffectiveGlobalQuotient6400
import ProximityPrize.SubmissionLower.BCHKSRankOneEffectiveDefectProduction6400
import ProximityPrize.SubmissionLower.BCHKSGlobalOwnerKeyEquation6400

/-! # The reduced common quotient in the production rank-one branch -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneReducedGlobalQuotient6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSTwoAxisResultant6400
open BCHKSErrorEvaluatorSemilinear6400
open BCHKSErrorLocatorKeyEquation6400
open BCHKSGlobalInhomogeneousKeyEquation6400
open BCHKSMultiplierDefectAbstract6400
open BCHKSEffectiveFixedRelation6400
open BCHKSEffectiveGlobalQuotient6400
open BCHKSRankOneEffectiveDefectProduction6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The production global residual can be written directly over the
effective defect, after cancelling every inactive fixed-node root from `K`. -/
theorem Score6400RankOneEffectiveDefectData.reducedGlobal
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T) :
    (outsideAgreementLocator IRSProfile.domain Finset.univ
        (score6400EffectiveFixedDefect data.Fixed data.K)).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) *
        score6400ReducedGlobalQuotient data.Fixed data.K =
      data.A * score6400ReceivedBivariate f₀ f₁ +
        data.B * score6400FrobeniusReceivedBivariate f₀ f₁ -
          data.C := by
  exact score6400_reducedGlobalQuotient_factorization
    f₀ f₁ data.Fixed data.A data.B data.C data.K data.global

/-- In the low ordinary direction, the reduced quotient fits in exactly the
same effective-defect-plus-Frobenius-degree budget as the scaled lanes. -/
theorem Score6400RankOneEffectiveDefectData.reducedGlobal_natDegree_lt
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T)
    (hAdirection : data.A.natDegree ≤ data.B.natDegree)
    (hK : data.K ≠ 0) :
    (score6400ReducedGlobalQuotient data.Fixed data.K).natDegree <
      (score6400EffectiveFixedDefect data.Fixed data.K).card +
        data.B.natDegree := by
  have hCdegree : data.C.natDegree < 262144 + data.B.natDegree :=
    data.C_degree.trans_le (by omega)
  have hKdegree := score6400_globalResidualQuotient_natDegree_lt
    f₀ f₁ data.Fixed data.A data.B data.C data.K data.B.natDegree
      hAdirection (Nat.le_refl _) hCdegree hK data.global
  exact score6400ReducedGlobalQuotient_natDegree_lt_of_Kdegree
    data.Fixed data.K data.B.natDegree hK hKdegree

/-- Consequently the reduced quotient has locator degree strictly below the
nullity-rebated Frobenius window. -/
theorem Score6400RankOneEffectiveDefectData.reducedGlobal_natDegree_lt_sub_nullity
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T)
    (hAdirection : data.A.natDegree ≤ data.B.natDegree)
    (hK : data.K ≠ 0) :
    (score6400ReducedGlobalQuotient data.Fixed data.K).natDegree <
      locatorFrobeniusRows6400 - L := by
  exact (Score6400RankOneEffectiveDefectData.reducedGlobal_natDegree_lt
      data hAdirection hK).trans_le
    (by simpa only [score6400EffectiveFixedDefect] using
      data.effective_rebate)

/-- Every owner now satisfies the exact common-quotient key equation with
only the effective fixed nodes on the right-hand locator. -/
theorem Score6400RankOneEffectiveDefectData.reducedOwner_keyEquation
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T)
    (z : IRSProfile.Field) (hz : z ∈ T)
    (Agreement E : Finset IRSProfile.Index)
    (P D : IRSProfile.Field[X])
    (hAgreement : 185364 ≤ Agreement.card)
    (hP : P.natDegree ≤ 131071)
    (hagree : ∀ i ∈ Agreement,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i)
    (herrorFactor :
      outsideAgreementLocator IRSProfile.domain Finset.univ E * D =
        score6400ReceivedInterpolator f₀ f₁ z - P) :
    Lagrange.nodal E (fun i ↦ IRSProfile.domain i) *
          (score6400ReducedGlobalQuotient data.Fixed data.K).map
            (Polynomial.evalRingHom z) =
      Lagrange.nodal
          (score6400EffectiveFixedDefect data.Fixed data.K)
          (fun i ↦ IRSProfile.domain i) *
        (data.A.map (Polynomial.evalRingHom z) * D +
          data.B.map (Polynomial.evalRingHom z) *
            D.map koalaSexticFrobenius.toRingHom) := by
  apply score6400_globalOwner_errorLocator_keyEquation
    f₀ f₁ (score6400EffectiveFixedDefect data.Fixed data.K) E
      data.A data.B data.C
      (score6400ReducedGlobalQuotient data.Fixed data.K) z P D
      (Score6400RankOneEffectiveDefectData.reducedGlobal data)
  · exact (data.owners z hz Agreement P hAgreement hP hagree).1
  · exact herrorFactor

end BCHKSRankOneReducedGlobalQuotient6400
end ProximityPrize.SubmissionLower

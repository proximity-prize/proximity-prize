import ProximityPrize.SubmissionLower.BCHKSRankOneEffectiveNormProduction6400
import ProximityPrize.SubmissionLower.BCHKSRankOneReducedGlobalQuotient6400
import ProximityPrize.SubmissionLower.BCHKSInhomogeneousCyclicCompatibility6400

/-! # Owner-independent cyclic compatibility of the reduced quotient -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneReducedCompatibility6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSErrorEvaluatorSemilinear6400
open BCHKSCyclicNormErrorEvaluator6400
open BCHKSRankOneEffectiveDefectProduction6400
open BCHKSRankOneEffectiveNormProduction6400
open BCHKSEffectiveFixedRelation6400
open BCHKSEffectiveGlobalQuotient6400
open BCHKSRankOneReducedGlobalQuotient6400
open BCHKSInhomogeneousCyclicCompatibility6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Any one owner key equation turns specialized norm equality into a
compatibility equation for the common reduced quotient. -/
theorem Score6400RankOneEffectiveDefectData.reducedOwner_compatibility_eq_zero
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
        score6400ReceivedInterpolator f₀ f₁ z - P)
    (hnorm :
      koalaCyclicNormSix
          (data.A.map (Polynomial.evalRingHom z)) =
        koalaCyclicNormSix
          (data.B.map (Polynomial.evalRingHom z))) :
    koalaCyclicCompatibilitySix
        (data.A.map (Polynomial.evalRingHom z))
        (data.B.map (Polynomial.evalRingHom z))
        ((score6400ReducedGlobalQuotient data.Fixed data.K).map
          (Polynomial.evalRingHom z)) = 0 := by
  apply score6400_koalaCyclicCompatibilitySix_eq_zero_of_nodal_keyEquation
    E (score6400EffectiveFixedDefect data.Fixed data.K)
    (data.A.map (Polynomial.evalRingHom z))
    (data.B.map (Polynomial.evalRingHom z)) D
    ((score6400ReducedGlobalQuotient data.Fixed data.K).map
      (Polynomial.evalRingHom z)) hnorm
  exact Score6400RankOneEffectiveDefectData.reducedOwner_keyEquation
    data z hz Agreement E P D hAgreement hP hagree herrorFactor

/-- In the low primitive direction and nullity at least `9694`, the reduced
quotient satisfies its owner-independent six-cycle compatibility equation at
every retained challenge.  No owner, agreement set, error set, or evaluator
appears in the conclusion. -/
theorem Score6400RankOneEffectiveDefectData.reducedGlobal_compatibility_eq_zero
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T)
    (hLlarge : 9694 ≤ L)
    (hAdirection : data.A.natDegree ≤ data.B.natDegree)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    ∀ z ∈ T,
      koalaCyclicCompatibilitySix
          (data.A.map (Polynomial.evalRingHom z))
          (data.B.map (Polynomial.evalRingHom z))
          ((score6400ReducedGlobalQuotient data.Fixed data.K).map
            (Polynomial.evalRingHom z)) = 0 := by
  intro z hz
  have hnorm := Score6400RankOneEffectiveDefectData.specializedNorm_eq
    data hLlarge hAdirection hbad hnotOld z hz
  obtain ⟨Agreement, P, E, hAgreement, hP, hagree,
      _hunexplained, hEdef, hElower, _hEupper⟩ :=
    exists_score6400_large_error_witness
      f₀ f₁ z (hbad z hz) (hnotOld z hz)
  have hEnonempty : E.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    rw [hEmpty, Finset.card_empty] at hElower
    omega
  obtain ⟨D, herrorFactor, _hDne, _hDdegree, _hDnonzero⟩ :=
    exists_score6400_errorEvaluator f₀ f₁ z P E hP hEdef hEnonempty
  exact Score6400RankOneEffectiveDefectData.reducedOwner_compatibility_eq_zero
    data z hz Agreement E P D hAgreement hP hagree herrorFactor hnorm

end BCHKSRankOneReducedCompatibility6400
end ProximityPrize.SubmissionLower

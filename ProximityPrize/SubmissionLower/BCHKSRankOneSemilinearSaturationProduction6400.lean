import ProximityPrize.SubmissionLower.BCHKSRankOneReducedCompatibility6400
import ProximityPrize.SubmissionLower.BCHKSSemilinearLocatorSaturation6400

/-!
# Production saturation of the rank-one semilinear residual

The reduced owner equation says that the squarefree error locator kills the
class of the reduced common quotient in the semilinear cokernel.  The generic
simple-root saturation theorem therefore makes that quotient an exact
semilinear image at every specialization whose primitive coefficient pair
remains coprime.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneSemilinearSaturationProduction6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSTwoAxisResultant6400
open BCHKSPrimitiveTripleRelation6400
open BCHKSPrimitiveTripleBicomponent6400
open BCHKSErrorEvaluatorSemilinear6400
open BCHKSCyclicNormErrorEvaluator6400
open BCHKSInhomogeneousCyclicCompatibility6400
open BCHKSRankOneEffectiveDefectProduction6400
open BCHKSRankOneEffectiveNormProduction6400
open BCHKSEffectiveFixedRelation6400
open BCHKSEffectiveGlobalQuotient6400
open BCHKSRankOneReducedGlobalQuotient6400
open BCHKSSemilinearPolynomialDescent6400
open BCHKSSemilinearLocatorSaturation6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Witnessed form of production saturation.  It exposes the exact algebraic
bridge from one owner key equation to an exact semilinear quotient. -/
theorem Score6400RankOneEffectiveDefectData.reducedOwner_semilinear_exact_of_isCoprime
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T)
    (hLlarge : 9694 ≤ L)
    (hAdirection : data.A.natDegree ≤ data.B.natDegree)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z)
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
    (hcoprime : IsCoprime
      (data.A.map (Polynomial.evalRingHom z))
      (data.B.map (Polynomial.evalRingHom z))) :
    ∃ Q : IRSProfile.Field[X],
      (score6400ReducedGlobalQuotient data.Fixed data.K).map
          (Polynomial.evalRingHom z) =
        koalaPolynomialSemilinear6400
          (data.A.map (Polynomial.evalRingHom z))
          (data.B.map (Polynomial.evalRingHom z)) Q := by
  let Az := data.A.map (Polynomial.evalRingHom z)
  let Bz := data.B.map (Polynomial.evalRingHom z)
  let Kz := (score6400ReducedGlobalQuotient data.Fixed data.K).map
    (Polynomial.evalRingHom z)
  let LE := Lagrange.nodal E (fun i ↦ IRSProfile.domain i)
  let LF := Lagrange.nodal
    (score6400EffectiveFixedDefect data.Fixed data.K)
    (fun i ↦ IRSProfile.domain i)
  have howner := Score6400RankOneEffectiveDefectData.reducedOwner_keyEquation
    data z hz Agreement E P D hAgreement hP hagree herrorFactor
  have hLFfixed : LF.map koalaSexticFrobenius.toRingHom = LF := by
    simpa only [LF] using score6400_nodal_map_frobenius
      (score6400EffectiveFixedDefect data.Fixed data.K)
  have hkey :
      LE * Kz = koalaPolynomialSemilinear6400 Az Bz (LF * D) := by
    calc
      LE * Kz = LF * koalaPolynomialSemilinear6400 Az Bz D := by
        simpa only [LE, LF, Az, Bz, Kz,
          koalaPolynomialSemilinear6400] using howner
      _ = koalaPolynomialSemilinear6400 Az Bz (LF * D) := by
        rw [koalaPolynomialSemilinear6400_mul_fixed Az Bz LF D hLFfixed]
  have hnorm := Score6400RankOneEffectiveDefectData.specializedNorm_eq
    data hLlarge hAdirection hbad hnotOld z hz
  obtain ⟨Q, hKexact⟩ :=
    exists_semilinear_of_isCoprime_nodal_mul_eq6400
      (fun i ↦ IRSProfile.domain i) koalaSexticFrobenius_fixed_domain
      E Az Bz Kz (LF * D) hcoprime hnorm
      (by simpa only [LE] using hkey)
  exact ⟨Q, by simpa only [Az, Bz, Kz] using hKexact⟩

/-- Owner-free production endpoint: every coprime retained
specialization makes the reduced common quotient an exact semilinear image. -/
theorem Score6400RankOneEffectiveDefectData.reducedGlobal_semilinear_exact_of_isCoprime
    {f₀ f₁ : IRSProfile.Index → IRSProfile.Field}
    {L : Nat} {T : Finset IRSProfile.Field}
    (data : Score6400RankOneEffectiveDefectData f₀ f₁ L T)
    (hLlarge : 9694 ≤ L)
    (hAdirection : data.A.natDegree ≤ data.B.natDegree)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z)
    (z : IRSProfile.Field) (hz : z ∈ T)
    (hcoprime : IsCoprime
      (data.A.map (Polynomial.evalRingHom z))
      (data.B.map (Polynomial.evalRingHom z))) :
    ∃ Q : IRSProfile.Field[X],
      (score6400ReducedGlobalQuotient data.Fixed data.K).map
          (Polynomial.evalRingHom z) =
        koalaPolynomialSemilinear6400
          (data.A.map (Polynomial.evalRingHom z))
          (data.B.map (Polynomial.evalRingHom z)) Q := by
  obtain ⟨Agreement, P, E, hAgreement, hP, hagree,
      _hunexplained, hEdef, hElower, _hEupper⟩ :=
    exists_score6400_large_error_witness
      f₀ f₁ z (hbad z hz) (hnotOld z hz)
  have hEnonempty : E.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨D, herrorFactor, _hDne, _hDdegree, _hDnonzero⟩ :=
    exists_score6400_errorEvaluator f₀ f₁ z P E hP hEdef hEnonempty
  exact Score6400RankOneEffectiveDefectData.reducedOwner_semilinear_exact_of_isCoprime
    data hLlarge hAdirection hbad hnotOld z hz
      Agreement E P D hAgreement hP hagree
      herrorFactor hcoprime

end BCHKSRankOneSemilinearSaturationProduction6400
end ProximityPrize.SubmissionLower

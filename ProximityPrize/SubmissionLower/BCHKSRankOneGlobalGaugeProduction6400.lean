import ProximityPrize.SubmissionLower.BCHKSHilbert90GlobalGauge6400
import ProximityPrize.SubmissionLower.BCHKSRankOneEffectiveNormProduction6400

/-!
# Production rank-one global gauge

For every coprime retained owner in the equal-norm branch, one explicit
Hilbert--90 polynomial is nonzero at every production node.  The owner error
divided by this common nodewise gauge is Frobenius-fixed away from the one
fixed coordinate defect.  The polynomial gauge has degree at most five times
the primitive Frobenius direction.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneGlobalGaugeProduction6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSCyclicNormErrorEvaluator6400
open BCHKSRankOneEffectiveDefectProduction6400
open BCHKSRankOneEffectiveNormProduction6400
open BCHKSSemilinearPolynomialDescent6400
open BCHKSSemilinearLocatorSaturation6400
open BCHKSHilbert90GlobalGauge6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- A retained coprime owner admits one bounded polynomial gauge, nonzero on
the whole NTT domain, which normalizes every error outside the fixed defect
to the Frobenius-fixed base field. -/
theorem Score6400RankOneEffectiveDefectData.exists_globalGauge_normalizing_owner6400
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
    (Agreement : Finset IRSProfile.Index) (P : IRSProfile.Field[X])
    (hAgreement : 185364 ≤ Agreement.card)
    (hP : P.natDegree ≤ 131071)
    (hagree : ∀ i ∈ Agreement,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i)
    (hcoprime : IsCoprime
      (data.A.map (Polynomial.evalRingHom z))
      (data.B.map (Polynomial.evalRingHom z))) :
    ∃ H : IRSProfile.Field[X],
      H.natDegree ≤ 5 * data.B.natDegree ∧
      koalaPolynomialSemilinear6400
        (data.A.map (Polynomial.evalRingHom z))
        (data.B.map (Polynomial.evalRingHom z)) H = 0 ∧
      (∀ i : IRSProfile.Index,
        H.eval (IRSProfile.domain i) ≠ 0) ∧
      ∀ i : IRSProfile.Index, i ∉ data.Fixed →
        koalaSexticFrobenius
            (((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) /
              H.eval (IRSProfile.domain i)) =
          ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) /
            H.eval (IRSProfile.domain i) := by
  let Az := data.A.map (Polynomial.evalRingHom z)
  let Bz := data.B.map (Polynomial.evalRingHom z)
  have hnorm : koalaCyclicNormSix Az = koalaCyclicNormSix Bz := by
    simpa only [Az, Bz] using
      Score6400RankOneEffectiveDefectData.specializedNorm_eq
        data hLlarge hAdirection hbad hnotOld z hz
  obtain ⟨t, ht⟩ :=
    exists_koalaHomogeneousHilbert90Kernel_eval_ne_zero_on_domain6400
      Az Bz (by simpa only [Az, Bz] using hcoprime) hnorm
  let H := koalaHomogeneousHilbert90Kernel6400 Az Bz t
  have hHdegree : H.natDegree ≤ 5 * data.B.natDegree := by
    apply koalaHomogeneousHilbert90Kernel_natDegree_le_of_le6400
    · exact Polynomial.natDegree_map_le.trans hAdirection
    · exact Polynomial.natDegree_map_le
  have hHsemi : koalaPolynomialSemilinear6400 Az Bz H = 0 := by
    simpa only [H] using
      koalaHomogeneousHilbert90Kernel_semilinear_eq_zero6400
        Az Bz t hnorm
  have howner :=
    (data.owners z hz Agreement P hAgreement hP hagree).2
  refine ⟨H, hHdegree, hHsemi, ?_, ?_⟩
  · intro i
    simpa only [H] using ht i
  · intro i hiFixed
    let x := IRSProfile.domain i
    let e := (f₀ i + z * f₁ i) - P.eval x
    have hBne : Bz.eval x ≠ 0 := by
      exact (eval_pair_ne_zero_of_norm_eq6400 Az Bz x
        (koalaSexticFrobenius_fixed_domain i) hnorm
        (not_both_eval_eq_zero_of_isCoprime Az Bz
          (by simpa only [Az, Bz] using hcoprime) x)).2
    have herrorFrobenius :
        koalaSexticFrobenius e =
          koalaSexticFrobenius (f₀ i + z * f₁ i) -
            (P.map koalaSexticFrobenius.toRingHom).eval x := by
      dsimp only [e]
      rw [map_sub,
        polynomial_map_eval_of_fixed_locator
          koalaSexticFrobenius P x
            (koalaSexticFrobenius_fixed_domain i)]
    have heq :
        Az.eval x * e + Bz.eval x * koalaSexticFrobenius e = 0 := by
      have hrel := howner i hiFixed
      rw [← herrorFrobenius] at hrel
      simpa only [Az, Bz, x, e] using hrel
    have hHeq :
        Az.eval x * H.eval x +
          Bz.eval x * koalaSexticFrobenius (H.eval x) = 0 := by
      have heval := congrArg
        (fun R : IRSProfile.Field[X] => R.eval x) hHsemi
      rw [koalaPolynomialSemilinear6400,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
        polynomial_map_eval_of_fixed_locator
          koalaSexticFrobenius H x
            (koalaSexticFrobenius_fixed_domain i),
        Polynomial.eval_zero] at heval
      exact heval
    have hHne : H.eval x ≠ 0 := by
      simpa only [x] using ht i
    simpa only [e, x] using
      frobenius_div_eq_self_of_common_semilinear_zero6400
        (Az.eval x) (Bz.eval x) e (H.eval x)
        hBne hHne heq hHeq

end BCHKSRankOneGlobalGaugeProduction6400
end ProximityPrize.SubmissionLower

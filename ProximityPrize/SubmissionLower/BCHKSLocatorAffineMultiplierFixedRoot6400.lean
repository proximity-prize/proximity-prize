import ProximityPrize.SubmissionLower.BCHKSGlobalFractionNodes6400
import ProximityPrize.SubmissionLower.BCHKSLocatorAffineMultiplierCompatibility6400

/-! # Fixed-node roots forced by an affine multiplier -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSLocatorAffineMultiplierCompatibility6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSGlobalInhomogeneousKeyEquation6400
open BCHKSMultiplierDefectAbstract6400

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- If a raw locator relation is an exact multiplier of the normalized
triple, the multiplier times the common global quotient vanishes at every
coordinate in the fixed primitive-factor defect. -/
theorem score6400_affineMultiplier_globalQuotient_fixed_root
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (Fixed : Finset IRSProfile.Index)
    (A B C K : IRSProfile.Field[X][X])
    (M : Score6400ChallengeFraction[X])
    (hglobal :
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
            (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]) * K =
        A * score6400ReceivedBivariate f₀ f₁ +
          B * score6400FrobeniusReceivedBivariate f₀ f₁ - C)
    (hA :
      (score6400PolynomialLocatorRelationPair q).1.1.map
          score6400ChallengeIota =
        M * A.map score6400ChallengeIota)
    (hB :
      (score6400PolynomialLocatorRelationPair q).2.1.map
          score6400ChallengeIota =
        M * B.map score6400ChallengeIota)
    (hC :
      (score6400PolynomialLocatorPairToCode f₀ f₁ q).map
          score6400ChallengeIota =
        M * C.map score6400ChallengeIota)
    (i : IRSProfile.Index) (hi : i ∈ Fixed) :
    (M * K.map score6400ChallengeIota).eval
        (score6400ChallengeFractionDomain i) = 0 := by
  let Lf :=
    ((outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
      (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X])).map
        score6400ChallengeIota
  let Kf := K.map score6400ChallengeIota
  let Af := A.map score6400ChallengeIota
  let Bf := B.map score6400ChallengeIota
  let Cf := C.map score6400ChallengeIota
  let Wf := (score6400ReceivedBivariate f₀ f₁).map
    score6400ChallengeIota
  let Vf := (score6400FrobeniusReceivedBivariate f₀ f₁).map
    score6400ChallengeIota
  let C₁f := (score6400PolynomialLocatorPairToCode f₀ f₁ q).map
    score6400ChallengeIota
  let A₁f := (score6400PolynomialLocatorRelationPair q).1.1.map
    score6400ChallengeIota
  let B₁f := (score6400PolynomialLocatorRelationPair q).2.1.map
    score6400ChallengeIota
  let x := score6400ChallengeFractionDomain i
  let w := score6400ChallengeIota (score6400ReceivedPolynomial f₀ f₁ i)
  let v := score6400ChallengeIota
    (score6400FrobeniusReceivedPolynomial f₀ f₁ i)
  have hglobalMap : Lf * Kf = Af * Wf + Bf * Vf - Cf := by
    simpa only [Lf, Kf, Af, Bf, Cf, Wf, Vf] using
      map_inhomogeneous_factorization score6400ChallengeIota
        ((outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
          (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X]))
        K A B C (score6400ReceivedBivariate f₀ f₁)
        (score6400FrobeniusReceivedBivariate f₀ f₁) hglobal
  have hW : Wf.eval x = w := by
    simpa only [Wf, x, w] using
      score6400_receivedBivariate_fraction_eval_coordinate f₀ f₁ i
  have hV : Vf.eval x = v := by
    simpa only [Vf, x, v] using
      score6400_frobeniusReceivedBivariate_fraction_eval_coordinate f₀ f₁ i
  have hraw : C₁f.eval x = A₁f.eval x * w + B₁f.eval x * v := by
    simpa only [C₁f, A₁f, B₁f, x, w, v] using
      score6400_affineLane_fraction_eval_coordinate f₀ f₁ q i
  have hC' : C₁f = M * Cf := by simpa only [C₁f, Cf] using hC
  have hA' : A₁f = M * Af := by simpa only [A₁f, Af] using hA
  have hB' : B₁f = M * Bf := by simpa only [B₁f, Bf] using hB
  have hL : Lf.eval x ≠ 0 := by
    simpa only [Lf, x] using
      score6400_mappedComplement_fraction_eval_ne_zero Fixed i hi
  have hroot := multiplier_quotient_eval_eq_zero
    Lf Kf Af Bf Cf Wf Vf C₁f A₁f B₁f M x w v
    hglobalMap hW hV hraw hC' hA' hB' hL
  simpa only [Kf, x] using hroot

/-- The fixed roots package into one common divisor of the multiplier after
discarding precisely the fixed nodes at which the common quotient vanishes. -/
theorem score6400_effectiveNodalLocator_dvd_multiplier
    (Fixed : Finset IRSProfile.Index)
    (K : IRSProfile.Field[X][X])
    (M : Score6400ChallengeFraction[X])
    (hroot : ∀ i ∈ Fixed,
      (M * K.map score6400ChallengeIota).eval
        (score6400ChallengeFractionDomain i) = 0) :
    Lagrange.nodal
        (effectiveNodalDefect score6400ChallengeFractionDomain Fixed
          (K.map score6400ChallengeIota))
        (fun i ↦ score6400ChallengeFractionDomain i) ∣ M := by
  exact effectiveNodalLocator_dvd_multiplier
    score6400ChallengeFractionDomain Fixed
    (K.map score6400ChallengeIota) M hroot

end BCHKSLocatorAffineMultiplierCompatibility6400
end ProximityPrize.SubmissionLower

import ProximityPrize.SubmissionLower.BCHKSChallengePolynomialFactorizationNode6400
import ProximityPrize.SubmissionLower.BCHKSGlobalFractionNodes6400
import ProximityPrize.SubmissionLower.BCHKSMultiplierDefectAbstract6400
import ProximityPrize.SubmissionLower.BCHKSPrimitiveTripleRelation6400

/-! # Restoring the normalized relation outside the effective fixed defect -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSEffectiveFixedRelation6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSPrimitiveTripleRelation6400
open BCHKSGlobalInhomogeneousKeyEquation6400
open BCHKSLocatorAffineMultiplierCompatibility6400
open BCHKSMultiplierDefectAbstract6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable def score6400EffectiveFixedDefect
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    Finset IRSProfile.Index :=
  effectiveNodalDefect score6400ChallengeFractionDomain Fixed
    (K.map score6400ChallengeIota)

noncomputable def score6400EffectiveFixedLocator
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    IRSProfile.Field[X] :=
  Lagrange.nodal (score6400EffectiveFixedDefect Fixed K)
    (fun i ↦ IRSProfile.domain i)

@[simp]
theorem mem_score6400EffectiveFixedDefect
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X])
    (i : IRSProfile.Index) :
    i ∈ score6400EffectiveFixedDefect Fixed K ↔
      i ∈ Fixed ∧
        (K.map score6400ChallengeIota).eval
          (score6400ChallengeFractionDomain i) ≠ 0 := by
  exact mem_effectiveNodalDefect
    score6400ChallengeFractionDomain Fixed
    (K.map score6400ChallengeIota) i

@[simp]
theorem score6400EffectiveFixedLocator_natDegree
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    (score6400EffectiveFixedLocator Fixed K).natDegree =
      (score6400EffectiveFixedDefect Fixed K).card := by
  exact Lagrange.natDegree_nodal

theorem score6400EffectiveFixedLocator_ne_zero
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X]) :
    score6400EffectiveFixedLocator Fixed K ≠ 0 :=
  Lagrange.nodal_ne_zero

theorem score6400_globalQuotient_eval_zero_of_fixed_not_effective
    (Fixed : Finset IRSProfile.Index) (K : IRSProfile.Field[X][X])
    (i : IRSProfile.Index) (hiFixed : i ∈ Fixed)
    (hiEffective : i ∉ score6400EffectiveFixedDefect Fixed K) :
    K.eval (Polynomial.C (IRSProfile.domain i)) = 0 := by
  have hmapZero :
      (K.map score6400ChallengeIota).eval
          (score6400ChallengeFractionDomain i) = 0 := by
    by_contra hne
    apply hiEffective
    exact (mem_score6400EffectiveFixedDefect Fixed K i).mpr
      ⟨hiFixed, hne⟩
  have himage : score6400ChallengeIota
      (K.eval (Polynomial.C (IRSProfile.domain i))) = 0 := by
    rw [← score6400ChallengeIota_eval_map]
    simpa only [score6400ChallengeFractionDomain_apply] using hmapZero
  have hiota : Function.Injective score6400ChallengeIota := by
    simpa only [score6400ChallengeIota] using
      (IsFractionRing.injective IRSProfile.Field[X]
        Score6400ChallengeFraction)
  apply hiota
  simpa only [map_zero] using himage

/-- The global quotient removes every original fixed node except those where
it is nonzero: at quotient-zero fixed nodes the normalized received relation
is restored exactly. -/
theorem score6400_normalized_received_relation_outside_effective
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B C K : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
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
    (i : IRSProfile.Index)
    (hi : i ∉ score6400EffectiveFixedDefect Fixed K) :
    C.eval (Polynomial.C (IRSProfile.domain i)) =
      A.eval (Polynomial.C (IRSProfile.domain i)) *
          score6400ReceivedPolynomial f₀ f₁ i +
        B.eval (Polynomial.C (IRSProfile.domain i)) *
          score6400FrobeniusReceivedPolynomial f₀ f₁ i := by
  by_cases hiFixed : i ∈ Fixed
  · have hKzero :=
      score6400_globalQuotient_eval_zero_of_fixed_not_effective
        Fixed K i hiFixed hi
    let Lf :=
      (outsideAgreementLocator IRSProfile.domain Finset.univ Fixed).map
        (Polynomial.C : IRSProfile.Field →+* IRSProfile.Field[X])
    let W := score6400ReceivedBivariate f₀ f₁
    let V := score6400FrobeniusReceivedBivariate f₀ f₁
    let x := Polynomial.C (IRSProfile.domain i)
    let w := score6400ReceivedPolynomial f₀ f₁ i
    let v := score6400FrobeniusReceivedPolynomial f₀ f₁ i
    have hglobal' : Lf * K = A * W + B * V - C := by
      simpa only [Lf, W, V] using hglobal
    have hW : W.eval x = w := by
      simpa only [W, x, w] using
        (score6400ReceivedBivariate_eval_coordinate_wrapped
          f₀ f₁ i).trans (score6400ReceivedNode_eq f₀ f₁ i)
    have hV : V.eval x = v := by
      simpa only [V, x, v] using
        (score6400FrobeniusReceivedBivariate_eval_coordinate_wrapped
          f₀ f₁ i).trans (score6400FrobeniusReceivedNode_eq f₀ f₁ i)
    have hrelation : C.eval x = A.eval x * w + B.eval x * v :=
      score6400ChallengePolynomial_bilinear_relation_of_factorization
        Lf K A B C W V x w v hglobal' hW hV
        (by simpa only [x] using hKzero)
    simpa only [x, w, v] using hrelation
  · apply quotient_relationWord_at_coordinate
      f₀ f₁ q H A B C hAfactor hBfactor hCfactor i
    simpa only [← hFixed] using hiFixed

/-- Subtract an arbitrary decoded-owner equation from any supplied normalized
received relation at a coordinate. -/
theorem homogeneous_error_relation_of_received_relation
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (A B C : IRSProfile.Field[X][X])
    (z : IRSProfile.Field) (P : IRSProfile.Field[X])
    (howner :
      C.map (Polynomial.evalRingHom z) =
        A.map (Polynomial.evalRingHom z) * P +
          B.map (Polynomial.evalRingHom z) *
            P.map koalaSexticFrobenius.toRingHom)
    (i : IRSProfile.Index)
    (hreceivedRaw :
      C.eval (Polynomial.C (IRSProfile.domain i)) =
        A.eval (Polynomial.C (IRSProfile.domain i)) *
            score6400ReceivedPolynomial f₀ f₁ i +
          B.eval (Polynomial.C (IRSProfile.domain i)) *
            score6400FrobeniusReceivedPolynomial f₀ f₁ i) :
    (A.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
          ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
        (B.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
          (koalaSexticFrobenius (f₀ i + z * f₁ i) -
            (P.map koalaSexticFrobenius.toRingHom).eval
              (IRSProfile.domain i)) = 0 := by
  have hreceivedRaw' := congrArg
    (fun R : IRSProfile.Field[X] ↦ R.eval z) hreceivedRaw
  have hreceived :
      (C.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) =
        (A.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
            (f₀ i + z * f₁ i) +
          (B.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
            koalaSexticFrobenius (f₀ i + z * f₁ i) := by
    simpa only [Polynomial.eval_add, Polynomial.eval_mul,
      score6400ReceivedPolynomial_eval,
      score6400FrobeniusReceivedPolynomial_eval,
      eval_C_eval_eq_map_eval_eval] using hreceivedRaw'
  have hdecoded := congrArg
    (fun R : IRSProfile.Field[X] ↦ R.eval (IRSProfile.domain i)) howner
  simp only [Polynomial.eval_add, Polynomial.eval_mul] at hdecoded
  calc
    _ = ((A.map (Polynomial.evalRingHom z)).eval
            (IRSProfile.domain i) * (f₀ i + z * f₁ i) +
          (B.map (Polynomial.evalRingHom z)).eval
            (IRSProfile.domain i) *
              koalaSexticFrobenius (f₀ i + z * f₁ i)) -
        ((A.map (Polynomial.evalRingHom z)).eval
            (IRSProfile.domain i) * P.eval (IRSProfile.domain i) +
          (B.map (Polynomial.evalRingHom z)).eval
            (IRSProfile.domain i) *
              (P.map koalaSexticFrobenius.toRingHom).eval
                (IRSProfile.domain i)) := by ring
    _ = 0 := by rw [← hreceived, ← hdecoded, sub_self]

theorem score6400_homogeneous_error_relation_outside_effective
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B C K : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
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
    (z : IRSProfile.Field) (P : IRSProfile.Field[X])
    (howner :
      C.map (Polynomial.evalRingHom z) =
        A.map (Polynomial.evalRingHom z) * P +
          B.map (Polynomial.evalRingHom z) *
            P.map koalaSexticFrobenius.toRingHom)
    (i : IRSProfile.Index)
    (hi : i ∉ score6400EffectiveFixedDefect Fixed K) :
    (A.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
          ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
        (B.map (Polynomial.evalRingHom z)).eval (IRSProfile.domain i) *
          (koalaSexticFrobenius (f₀ i + z * f₁ i) -
            (P.map koalaSexticFrobenius.toRingHom).eval
              (IRSProfile.domain i)) = 0 := by
  exact homogeneous_error_relation_of_received_relation
    f₀ f₁ A B C z P howner i
    (score6400_normalized_received_relation_outside_effective
      f₀ f₁ q H A B C K Fixed hAfactor hBfactor hCfactor
      hFixed hglobal i hi)

end BCHKSEffectiveFixedRelation6400
end ProximityPrize.SubmissionLower

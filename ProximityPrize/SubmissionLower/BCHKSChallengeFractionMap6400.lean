import ProximityPrize.SubmissionLower.BCHKSLocatorAffineLaneNodes6400

/-! # Opaque transport primitives for the score-64 challenge fraction field -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSLocatorAffineMultiplierCompatibility6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

abbrev Score6400ChallengeFraction :=
  FractionRing IRSProfile.Field[X]

noncomputable def score6400ChallengeIota :
    IRSProfile.Field[X] →+* Score6400ChallengeFraction :=
  algebraMap IRSProfile.Field[X] Score6400ChallengeFraction

noncomputable def score6400ChallengeFractionDomain :
    IRSProfile.Index ↪ Score6400ChallengeFraction where
  toFun i := score6400ChallengeIota
    (Polynomial.C (IRSProfile.domain i))
  inj' := by
    intro i j hij
    apply IRSProfile.domain.injective
    apply Polynomial.C_injective
    exact (IsFractionRing.injective IRSProfile.Field[X]
      Score6400ChallengeFraction) hij

@[simp]
theorem score6400ChallengeFractionDomain_apply
    (i : IRSProfile.Index) :
    score6400ChallengeFractionDomain i =
      score6400ChallengeIota (Polynomial.C (IRSProfile.domain i)) := rfl

/-- Specialized value-level bilinear transport.  Keeping the concrete
fraction-field instances behind this theorem avoids re-running their large
typeclass normalization in production node proofs. -/
theorem score6400ChallengeIota_bilinear
    (a b r s : IRSProfile.Field[X]) :
    score6400ChallengeIota (a * r + b * s) =
      score6400ChallengeIota a * score6400ChallengeIota r +
        score6400ChallengeIota b * score6400ChallengeIota s := by
  rw [map_add, map_mul, map_mul]

/-- Specialized coefficient-map/evaluation compatibility. -/
theorem score6400ChallengeIota_eval_map
    (P : IRSProfile.Field[X][X]) (x : IRSProfile.Field[X]) :
    (P.map score6400ChallengeIota).eval (score6400ChallengeIota x) =
      score6400ChallengeIota (P.eval x) := by
  exact Polynomial.eval_map_apply score6400ChallengeIota x

/-- Specialized polynomial-level bilinear transport. -/
theorem score6400ChallengeIota_bilinear_eval
    (C A B : IRSProfile.Field[X][X])
    (x r s : IRSProfile.Field[X])
    (h : C.eval x = A.eval x * r + B.eval x * s) :
    (C.map score6400ChallengeIota).eval (score6400ChallengeIota x) =
      (A.map score6400ChallengeIota).eval (score6400ChallengeIota x) *
          score6400ChallengeIota r +
        (B.map score6400ChallengeIota).eval (score6400ChallengeIota x) *
          score6400ChallengeIota s := by
  calc
    (C.map score6400ChallengeIota).eval (score6400ChallengeIota x) =
        score6400ChallengeIota (C.eval x) :=
      score6400ChallengeIota_eval_map C x
    _ = score6400ChallengeIota (A.eval x * r + B.eval x * s) :=
      congrArg score6400ChallengeIota h
    _ = score6400ChallengeIota (A.eval x) * score6400ChallengeIota r +
          score6400ChallengeIota (B.eval x) * score6400ChallengeIota s :=
      score6400ChallengeIota_bilinear (A.eval x) (B.eval x) r s
    _ = (A.map score6400ChallengeIota).eval
            (score6400ChallengeIota x) * score6400ChallengeIota r +
          (B.map score6400ChallengeIota).eval
            (score6400ChallengeIota x) * score6400ChallengeIota s :=
      congrArg₂ (· + ·)
        (congrArg (fun y ↦ y * score6400ChallengeIota r)
          (score6400ChallengeIota_eval_map A x).symm)
        (congrArg (fun y ↦ y * score6400ChallengeIota s)
          (score6400ChallengeIota_eval_map B x).symm)

end BCHKSLocatorAffineMultiplierCompatibility6400
end ProximityPrize.SubmissionLower

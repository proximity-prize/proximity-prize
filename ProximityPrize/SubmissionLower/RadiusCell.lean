/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.Benchmark.TargetLower
import Mathlib.Tactic

namespace ProximityPrize.SubmissionLower.RadiusCell

open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

/-- The extractor bound depends only on the number of erroneous coordinates that the radius admits. -/
theorem reduction_eq {r s : ℝ≥0}
    (cell : ⌊r * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ =
            ⌊s * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊) :
    certifiedGammaError IRSProfile.code r = certifiedGammaError IRSProfile.code s := by
  have realCell : ⌊(r : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
                  ⌊(s : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ := by
    exact_mod_cast cell
  unfold certifiedGammaError
  rw [mcaError_eq_of_floor_eq (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        r.coe_nonneg s.coe_nonneg realCell,
      GrandChallenges.lambda_eq_of_floor_eq cell]

/-- A certificate can be moved to any larger admissible radius in the same Hamming cell. -/
theorem extend {bits p q p' q' : ℕ} (h : ProtocolClaim bits p q)
    (admissible : claimedRadius p' q' ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance)
    (larger : claimedRadius p q ≤ claimedRadius p' q')
    (cell : ⌊claimedRadius p' q' * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ =
            ⌊claimedRadius p q * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊) :
    ProtocolClaim bits p' q' where
  admissible := admissible
  reduction := (reduction_eq cell).le.trans h.reduction
  score := (pow_le_pow_left' (tsub_le_tsub_left larger (1 : ℝ≥0)) _).trans h.score

end ProximityPrize.SubmissionLower.RadiusCell

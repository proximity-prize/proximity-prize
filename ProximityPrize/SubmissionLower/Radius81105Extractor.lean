/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.Original6836
import ProximityPrize.SubmissionLower.ScalarCappedProfile
import ProximityPrize.SubmissionLower.Radius81105

namespace ProximityPrize.SubmissionLower.Radius81105
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal
noncomputable section

/-- Preserve Bome2017's MCA count and use the squarefree scalar list to tighten
the numerator of the extractor error at the larger radius. -/
theorem extractor_error :
    certifiedGammaError IRSProfile.code (claimedRadius numerator denominator) ≤
      (274980676793458959 : ℝ≥0) / 2130706433^6 := by
  let r := JointProtocol6836.radius
  have cell : ⌊claimedRadius numerator denominator * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ =
      ⌊r * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ := by
    rw [IRSProfile.card_index]
    norm_num [r, JointProtocol6836.radius, claimedRadius, JointProtocol6836.radiusNumerator,
      JointProtocol6836.radiusDenominator]
  rw [RadiusCell.reduction_eq cell]
  have family := JointProtocol6836.at_of_joint_short
    (Night6836Terminal.short_of_slabs KoalaOriginal6836.original_slabs)
  have given := Intermediate.given_of_at (r := r) (by decide) (by decide) (by decide)
    (by norm_num [r, JointProtocol6836.radius, claimedRadius, JointProtocol6836.radiusNumerator,
      JointProtocol6836.radiusDenominator]) family
  have projection : 15 * (35994575649 + 1).choose 2 < Fintype.card IRSProfile.Field :=
    (Nat.mul_le_mul_left 15 (Nat.choose_le_pow (35994575649+1) 2)).trans_lt
      ((by decide : 15 * (35994575649 + 1 : ℕ)^2 < 2130706433^6).trans_eq
        RCN284.field_cardinality.symm)
  have bound := JointProtocol6836.error_le_of_bounds given _ ScalarCappedProfile.words_81105 projection
  rw [RCN284.field_cardinality, show JointProtocol6836.mcaBudget + 35994575649 =
    274980676793458959 by decide] at bound
  simpa only [JointProtocol6836.mcaBudget, Nat.cast_pow, Nat.cast_ofNat] using bound

/-- The exact rational bound is strictly below the track's fixed extractor target. -/
theorem extractor_error_lt_target :
    certifiedGammaError IRSProfile.code (claimedRadius numerator denominator) < reductionTarget :=
  extractor_error.trans_lt (by norm_num [reductionTarget, ProximityGap.prizeThreshold])

#print axioms extractor_error_lt_target
end
end ProximityPrize.SubmissionLower.Radius81105

/- Extends Lucieno's promoted 68.44 certificate. Apache-2.0. -/
import ProximityPrize.SubmissionLower.Koala6844Submission
import ProximityPrize.SubmissionLower.ScalarCappedProfile
import ProximityPrize.SubmissionLower.Radius81186Score
import ProximityPrize.SubmissionLower.NormalizedSeedCount

namespace ProximityPrize.SubmissionLower.Radius81186
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option Elab.async false

private theorem seed_bound : Koala6844Protocol.ScalarSeedBound := by
  exact Koala6844BenchmarkCases.seed_bound_of_rank_one
    (Koala6844BenchmarkGeometry.rank_one_bound_of_geometry
      (Koala6844GeometryDispatch.remaining_geometry_of_separated
        (Koala6844VirtualDispatch.separated_bound_of_active_counts
          Koala6844VirtualHigh.benchmark_large_support Koala6844Submission.checked_short_support)))

private theorem filter_card (P : IRSProfile.Index → Prop) (d e : DecidablePred P)
    (S : Finset IRSProfile.Index) : (@Finset.filter _ P d S).card ≤ (@Finset.filter _ P e S).card := by
  rw [Subsingleton.elim d e]

private theorem word_list : Koala6844Protocol.ScalarListBoundAt 113387658701 := by
  intro word L code near
  apply ScalarCappedProfile.words_81186 word L code
  intro c hc
  have h := near c hc
  rw [IRSProfile.card_index] at h
  exact h.trans (filter_card (fun i => c i = word i) _ _ _)

private theorem projectable : 15 * (113387658701+1).choose 2 < Fintype.card IRSProfile.Field :=
  (Nat.mul_le_mul_left 15 (Nat.choose_le_pow (113387658701+1) 2)).trans_lt
    ((by decide : 15 * (113387658701+1 : ℕ)^2 < 2130706433^6).trans_eq
      RCN284.field_cardinality.symm)

/-- Combine the promoted alignment estimate with the sharper squarefree scalar list. -/
theorem extractor_error :
    certifiedGammaError IRSProfile.code (claimedRadius numerator denominator) ≤
      (274426266738327370 : ℝ≥0) / 2130706433^6 := by
  let r := Koala6844Protocol.radius
  have cell : ⌊claimedRadius numerator denominator * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ =
      ⌊r * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ := by
    rw [IRSProfile.card_index]
    norm_num [r, Koala6844Protocol.radius, Koala6844Protocol.radiusNumerator,
      Koala6844Protocol.radiusDenominator, claimedRadius]
  rw [RadiusCell.reduction_eq cell]
  have bound := Koala6844Protocol.extractor_error_le_of_selected (B := 113387658701)
    seed_bound word_list projectable
  rw [RCN284.field_cardinality, show Koala6844Protocol.mcaBudget + 113387658701 =
    274426266738327370 by decide] at bound
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using bound

theorem claim : ProtocolClaim 6844 numerator denominator where
  admissible := (improve Koala6844Submission.claim).admissible
  reduction := extractor_error.trans (by
    rw [reductionTarget, ProximityGap.prizeThreshold]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    norm_num)
  score := (improve Koala6844Submission.claim).score

#print axioms claim
end
end ProximityPrize.SubmissionLower.Radius81186

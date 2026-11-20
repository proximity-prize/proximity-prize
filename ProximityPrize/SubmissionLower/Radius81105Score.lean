/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.Radius81105
import ProximityPrize.SubmissionLower.DyadicScore

namespace ProximityPrize.SubmissionLower.Radius81105
open ProximityPrize.Benchmark
open scoped NNReal

private def digits : List (ℕ × ℕ) := [
  (0, 606615685934693470789976),
  (1, 735965180844037331940459),
  (0, 541644747414796574568959),
  (1, 586758064804077561099595),
  (1, 688570053225252165519642),
  (1, 948257436397253200302376),
  (0, 899192165682690698480862),
  (0, 808546550825127479850804),
  (0, 653747524851210454967960),
  (1, 854771652498168062801988),
  (0, 730634577914448980277962),
  (0, 533826886444225017623158),
  (1, 569942289381471023758934),
  (1, 649668426450784916164402),
  (1, 844138128654077860202691),
  (0, 712569180247608505383309),
  (0, 507754836638748779345331),
  (1, 515629948260084919622755),
  (1, 531748487085395702457950),
  (1, 565512907035214480327854),
  (1, 639609696046838270557277),
  (1, 818201126554257679973611),
  (0, 669453083494656392004314),
  (1, 896334862001006765101149),
  (0, 803416184838363841316011),
  (0, 645477566060232013090237),
  (1, 833282576574082364826322),
  (0, 694359852421941439926870),
  (1, 964271209310840591477223),
  (0, 929818965105790946996656),
  (0, 864563307870404082696793)]

/-- A fractional-bit spot-check estimate for the extremal representable radius. -/
theorem fine_score :
    (1 - claimedRadius numerator denominator)^IRSProfile.repetitions ≤
      (2 : ℝ≥0)^(-(146803211924 : ℝ) / 2147483648) := by
  let r := claimedRadius numerator denominator
  have small : r ≤ 1 := by
    unfold r claimedRadius
    exact (div_le_one (by positivity)).mpr (by norm_num)
  have diff : (1 - r : ℝ≥0) = 6369708354217914197 / 9223372036854698457 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub small]
    norm_num [r, claimedRadius]
  have start : ((1-r)^128) * 2^68 ≤ (778855369073548513847740 : ℝ≥0) / 1000000000000000000000000 := by
    rw [diff, div_pow, div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast (show (6369708354217914197 : ℕ)^128 * 2^68 * 1000000000000000000000000 ≤
      778855369073548513847740 * 9223372036854698457^128 by decide +kernel)
  have cert := DyadicScore.score digits (by decide : 0 < 1000000000000000000000000) start (by decide +kernel)
  have length_eq : digits.length = 31 := by decide
  have prefix_eq : DyadicScore.bitNumerator 68 digits = 146803211924 := by decide +kernel
  rw [length_eq, prefix_eq] at cert
  exact cert

#print axioms fine_score
end ProximityPrize.SubmissionLower.Radius81105

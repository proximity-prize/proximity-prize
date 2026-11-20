/- Released under the Apache License, Version 2.0. -/
import ProximityPrize.SubmissionLower.Radius81879
import ProximityPrize.SubmissionLower.DyadicScore

namespace ProximityPrize.SubmissionLower.Radius81879
open ProximityPrize.Benchmark
open scoped NNReal

private def digits : List (ℕ × ℕ) := [
  (0, 810259864609136633914970434848),
  (0, 656521048196416428677770902986),
  (1, 862039773449842686476948457039),
  (0, 743112571009456103874956077854),
  (0, 552216293192283940324412764953),
  (1, 609885668934052996991467965271),
  (1, 743921058342274593815083723578),
  (0, 553418541045089920032026577577),
  (1, 612544163144951753035789489121),
  (1, 750420703605898538996783548048),
  (0, 563131232400371824528391489289),
  (1, 634233569809523163539638869119),
  (1, 804504442146662584110318836345),
  (0, 647227397433712764805410157330),
  (1, 837806607977634353618928835295),
  (0, 701919912370989491339994806322),
  (1, 985383126765795132732442071506),
  (0, 970979906514735080121399565386),
  (0, 942801978855363675687310239882),
  (0, 888875571333589615426340225007),
  (0, 790099781313615360894799183408),
  (0, 624257664431822817020788192289),
  (1, 779395263203748604434128596028),
  (0, 607456976304440563319154740363),
  (1, 738007956121867328047729159017),
  (0, 544655743299176051366223779821),
  (1, 593299757417555916357719731033),
  (1, 704009204303461393184495652555),
  (1, 991257919487985687626368872294),
  (0, 982592262947649915674726947082),
  (0, 965487555204583593351918777010),
  (0, 932166219254923851718771075817),
  (0, 868933860320018767044193140317),
  (0, 755046053610649885142715083263),
  (0, 570094543073016380456714012868),
  (1, 650015576083262658202600809421),
  (1, 845040498301711650937284099838),
  (0, 714093443770005131611919365301),
  (0, 509929446435305480713755181522),
  (1, 520056080683634162863497180252),
  (1, 540916654112045212506199011880),
  (1, 585181653391539917807396754349)]

/-- A fractional-bit spot-check estimate for the extremal representable radius. -/
theorem fine_score :
    (1 - claimedRadius numerator denominator)^IRSProfile.repetitions ≤
      (2 : ℝ≥0)^(-(304132708294759 : ℝ) / 4398046511104) := by
  let r := claimedRadius numerator denominator
  have small : r ≤ 1 := by
    unfold r claimedRadius
    exact (div_le_one (by positivity)).mpr (by norm_num)
  have diff : (1 - r : ℝ≥0) = 6342475650221202353 / 9223372036854762291 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub small]
    norm_num [r, claimedRadius]
  have start : ((1-r)^128) * 2^69 ≤ (900144357650003066392864388377 : ℝ≥0) / 1000000000000000000000000000000 := by
    rw [diff, div_pow, div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast (show (6342475650221202353 : ℕ)^128 * 2^69 * 1000000000000000000000000000000 ≤
      900144357650003066392864388377 * 9223372036854762291^128 by decide +kernel)
  have cert := DyadicScore.score digits (by decide : 0 < 1000000000000000000000000000000) start (by decide +kernel)
  have length_eq : digits.length = 42 := by decide
  have prefix_eq : DyadicScore.bitNumerator 69 digits = 304132708294759 := by decide +kernel
  rw [length_eq, prefix_eq] at cert
  exact cert

/-- The extractor estimate at the integer radius is the only remaining input. -/
theorem of_reduction
    (h : ToyProblem.Impl.IRS.certifiedGammaError IRSProfile.totalDimension IRSProfile.interleaving
      IRSProfile.domain (claimedRadius 81879 262144) ≤ reductionTarget) :
    ProtocolClaim 6915 numerator denominator where
  admissible := by constructor <;> norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have cell : ⌊claimedRadius numerator denominator * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ =
        ⌊claimedRadius 81879 262144 * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ := by
      rw [IRSProfile.card_index]
      norm_num [claimedRadius]
    exact (RadiusCell.reduction_eq cell).le.trans h
  score := by
    apply fine_score.trans
    unfold claimedError
    apply NNReal.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num

#print axioms of_reduction
#print axioms fine_score
end ProximityPrize.SubmissionLower.Radius81879

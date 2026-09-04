import ProximityPrize.Benchmark.TargetLower

/-! Small natural-number adapters for the 68.03 divisor caps. -/

namespace ProximityPrize.SubmissionLower.LocatorCapArithmetic6803

set_option autoImplicit false

theorem index_card :
    Fintype.card ProximityPrize.Benchmark.IRSProfile.Index = 262144 := by
  norm_num [ProximityPrize.Benchmark.IRSProfile.Index]

theorem lt_of_sub_eq_pos {a b gap : ℕ} (hgap : 0 < gap)
    (h : b - a = gap) : a < b := by
  apply Nat.sub_pos_iff_lt.mp
  simpa only [h] using hgap

theorem A_middle_le {ys contact slope : ℕ}
    (hweighted : 131071 * ys ≤ contact + slope)
    (hcontact : contact ≤ 17773573) (hslope : slope ≤ 29) :
    ys ≤ 135 := by
  omega

theorem B_middle_le {ys contact slope : ℕ}
    (hweighted : 131071 * ys ≤ contact + slope)
    (hcontact : contact ≤ 20131292) (hslope : slope ≤ 34) :
    ys ≤ 153 := by
  omega

end ProximityPrize.SubmissionLower.LocatorCapArithmetic6803

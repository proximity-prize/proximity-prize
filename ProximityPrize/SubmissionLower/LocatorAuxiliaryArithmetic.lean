import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

open RCN100 RCN119 RCN302

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem auxiliary72_rank :
    localRankBound 72 130000 21 = 5782993381 := by decide

theorem auxiliary72_nullity :
    coefficientCount 13072968 131071 130000 21 -
      262144 * localRankBound 72 130000 21 = 534293974082 := by
  rw [auxiliary72_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13072968 131071 130000 21 100 (by decide) (by decide)]
  decide

theorem auxiliary72_shape :
    13072968 + 21 ≤ 131071 * (99 + 1) := by decide

theorem auxiliary72_capacity :
    13072968 - 50499 ≤ (72 - 1) * 181569 + (131071 - 1) := by decide

/-- These names are retained to minimize invalidation in the replacement
    proof; their witness is the retuned multiplicity-400 C source. -/
theorem auxiliary176_shape :
    72627600 + 120 ≤ 131071 * (554 + 1) := by decide

theorem auxiliary176_capacity :
    72627600 - 50499 ≤ (400 - 1) * 181569 + (131071 - 1) := by decide

theorem auxiliary176_double_capacity :
    72627600 - 2 * 50499 ≤
      (400 - 2) * 181569 + 2 * (131071 - 1) := by decide

/-- The stage-`j` capacity identity of the C source holds with equality for
    every `j ≤ 400`, because `181569 - (131071 - 1) = 50499`. -/
theorem auxiliary176_stage_capacity (j : ℕ) (hj : j ≤ 400) :
    72627600 - j * 50499 ≤ (400 - j) * 181569 + j * (131071 - 1) := by
  omega

/-- Route-depth capacity chain.  If the ambient weighted degree fits inside
`m` full agreement blocks, then after `j` repeated projections -- each shedding
one `delta = a - w + 1` band and one contact block -- the remaining degree still
fits inside `m - j` blocks plus `j` locator degrees. -/
theorem chain_capacity (D a w m : ℕ) (hbase : D ≤ m * a) (hwa : w ≤ a) :
    ∀ j : ℕ, j ≤ m → D - j * (a - w + 1) ≤ (m - j) * a + j * (w - 1) := by
  intro j
  induction j with
  | zero => intro _; simpa using hbase
  | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have h1 : (m - j) * a = (m - (j + 1)) * a + a := by
        have h : m - j = (m - (j + 1)) + 1 := by omega
        rw [h]; ring
      have h2 : (j + 1) * (w - 1) = j * (w - 1) + (w - 1) := by ring
      have h3 : (j + 1) * (a - w + 1) = j * (a - w + 1) + (a - w + 1) := by ring
      omega

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorRankClosed

namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

open RCN100 RCN119 RCN302

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem auxiliary72_rank :
    localRankBound 73 130000 22 = 6166888547 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 73 130000 22 (by decide)]
  decide +kernel

theorem auxiliary72_nullity :
    coefficientCount 13253150 131071 130000 22 -
      262144 * localRankBound 73 130000 22 = 441366390587 := by
  rw [auxiliary72_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13253150 131071 130000 22 102 (by decide) (by decide)]
  decide

theorem auxiliary72_shape :
    13253150 + 22 ≤ 131071 * (101 + 1) := by decide

theorem auxiliary72_capacity :
    13253150 - 50480 ≤ (73 - 1) * 181550 + (131071 - 1) := by decide

/-- These names are retained to minimize invalidation in the replacement
    proof; their witness is the retuned multiplicity-285 C source. -/
theorem auxiliary176_shape :
    51741750 + 85 ≤ 131071 * (394 + 1) := by decide

theorem auxiliary176_capacity :
    51741750 - 50480 ≤ (285 - 1) * 181550 + (131071 - 1) := by decide

theorem auxiliary176_double_capacity :
    51741750 - 2 * 50480 ≤
      (285 - 2) * 181550 + 2 * (131071 - 1) := by decide

/-- The stage-`j` capacity identity of the C source holds with equality for
    every `j ≤ 285`, because `181550 - (131071 - 1) = 50480`. -/
theorem auxiliary176_stage_capacity (j : ℕ) (hj : j ≤ 285) :
    51741750 - j * 50480 ≤ (285 - j) * 181550 + j * (131071 - 1) := by
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

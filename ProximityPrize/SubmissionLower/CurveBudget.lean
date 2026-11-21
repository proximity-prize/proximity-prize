import Mathlib.Tactic

namespace CurveBudget

/-- Combine two bounds on the same labels. The parameter k counts how many
    copies of the seed degree fit into the total degree. -/
theorem combine {labels seedDegree degree height seedPrice beta unitRate : ℚ} {k : ℕ}
    (hk : 1 ≤ k) (hmax : k ≤ 8) (hpaid : (k : ℚ) * seedDegree ≤ degree)
    (hs : 0 ≤ seedPrice) (hd : 0 ≤ degree) (hh : 0 ≤ height)
    (hb : 0 ≤ beta) (hu : 0 ≤ unitRate)
    (seed : labels ≤ seedPrice * seedDegree)
    (root : labels ≤ ((2 * (k : ℚ) - 1) * unitRate + beta) * height + degree) :
    labels ≤ (seedPrice / 9) * degree + (4 * unitRate + 8/9 * beta) * height + degree := by
  have dk : 0 ≤ (9 : ℚ) - k := by exact_mod_cast (show (k : ℤ) ≤ 9 by omega) |> sub_nonneg.mpr
  have hhead : (k : ℚ)*labels ≤ seedPrice*degree := calc
    _ ≤ (k : ℚ)*(seedPrice*seedDegree) := mul_le_mul_of_nonneg_left seed (by positivity)
    _ = seedPrice*((k : ℚ)*seedDegree) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpaid hs
  have hcoeff : (9 - (k : ℚ)) * ((2*(k : ℚ)-1)*unitRate + beta) ≤
      36*unitRate+8*beta := by
    interval_cases k <;> norm_num at * <;> linarith
  have htail := mul_le_mul_of_nonneg_left root dk
  have hy := mul_le_mul_of_nonneg_right hcoeff hh
  have hd' : (9 - (k : ℚ))*degree ≤ 9*degree := mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) hd
  linarith only [hhead, htail, hy, hd']

end CurveBudget

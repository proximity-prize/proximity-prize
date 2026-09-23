import ProximityPrize.SubmissionLower.BoundaryTailDegrees
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProximityPrize.SubmissionLower.BoundaryTail

theorem weighted_tail_bound {n j a b c : ℤ}
    (hn : 2 ≤ n) (hj0 : 0 ≤ j) (hjn : j ≤ n - 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a - b ≤ 2 * c) :
    2 * (j * a + (n - 1 - j) * b + max (n - 2 - 2 * j) 0 * c) ≥
      2 * (n - 1) * a - n * max (a - b) 0 := by
  by_cases hpos : 0 ≤ n - 2 - 2 * j
  · rw [max_eq_left hpos]
    by_cases hd : 0 ≤ a - b
    · rw [max_eq_left hd]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hd)]
      nlinarith
  · rw [max_eq_right (le_of_not_ge hpos)]
    by_cases hd : 0 ≤ a - b
    · rw [max_eq_left hd]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hd)]
      nlinarith

theorem leading_separation {n j a b c : ℤ}
    (hn : 2 ≤ n) (hj0 : 1 ≤ j) (hjn : j ≤ n - 1)
    (hc : 0 ≤ c) (hgap : 2 * c < a - b) :
    j * a + (n - 1 - j) * b + max (n - 2 - 2 * j) 0 * c >
      (n - 1) * b + (n - 2) * c := by
  by_cases hpos : 0 ≤ n - 2 - 2 * j
  · rw [max_eq_left hpos]
    nlinarith
  · rw [max_eq_right (le_of_not_ge hpos)]
    nlinarith

theorem max_shift_identity {u v p : ℤ}
    (hv : 0 ≤ v) (hvu : v ≤ u) :
    max (max (2 * u) (v + max p 0) - 2 * u) 0 =
      max (p - (2 * u - v)) 0 := by
  simp [max_def]
  omega

end ProximityPrize.SubmissionLower.BoundaryTail

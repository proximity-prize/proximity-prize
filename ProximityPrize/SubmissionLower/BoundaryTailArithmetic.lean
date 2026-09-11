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
theorem normalized_tail_arithmetic {n u v A a b : ℤ}
    (hn : 2 ≤ n) (hv : 0 ≤ v) (hvu : v ≤ u) (ha : 0 ≤ a) :
    let delta := 2 * u - v
    let D := A - u
    let B := A + delta
    let P := (n - 1) * B + (n - 2) * D
    let theta := max (2 * u) (v + max ((a - A) - (b - B)) 0)
    2 * (P - (n - 1) * a) + n * max (a - b) 0 +
        2 * (n - 4) * (a - A) ≤
      2 * ((n + 1) * A - (n - 1) * v) + n * theta := by
  dsimp
  have htheta := max_shift_identity (u := u) (v := v)
    (p := (a - A) - (b - (A + (2 * u - v)))) hv hvu
  have hp : (a - A) - (b - (A + (2 * u - v))) - (2 * u - v) = a - b := by ring
  rw [hp] at htheta
  have hnon : 0 ≤ max (2 * u) (v + max ((a - A) - (b - (A + (2 * u - v)))) 0) - 2 * u := by omega
  rw [max_eq_left hnon] at htheta
  nlinarith

theorem weighted_tail_bound_zero_J {n j a b : ℤ}
    (hn : 2 ≤ n) (hj0 : 0 ≤ j) (hjn : j ≤ n - 1)
    (hpos : n - 2 ≤ 2 * j) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (j * a + (n - 1 - j) * b) ≥
      2 * (n - 1) * a - n * max (a - b) 0 := by
  by_cases hd : 0 ≤ a - b
  · rw [max_eq_left hd]
    nlinarith
  · rw [max_eq_right (le_of_not_ge hd)]
    nlinarith

end ProximityPrize.SubmissionLower.BoundaryTail

import Mathlib.Data.Nat.Basic

namespace HighCore82258

private theorem transfer_capacity {x y d : ℕ} (hxy : y ≤ x) :
    (x + d) * (y - d) ≤ x * y := by
  by_cases hdy : d ≤ y
  · calc
      (x + d) * (y - d) = x * (y - d) + d * (y - d) := Nat.add_mul ..
      _ ≤ x * (y - d) + d * x :=
        Nat.add_le_add_left (Nat.mul_le_mul_left d (Nat.le_trans (Nat.sub_le y d) hxy)) _
      _ = x * y := by rw [Nat.mul_comm d x, ← Nat.mul_add, Nat.sub_add_cancel hdy]
  · simp [Nat.sub_eq_zero_of_le (by omega : y ≤ d)]

/-- When the smaller degree lies on the longer side, the balanced degree test
    dominates the remaining rectangle at each power of the polynomial. -/
theorem oriented_rect_capacity_le {u w a b lo hi r : ℕ}
    (hsides : w ≤ u) (hdegrees : a ≤ b)
    (hlohi : lo ≤ hi) (hbalanced : hi ≤ lo + 1) (hsum : lo + hi ≤ a + b) :
    (u + 1 - r * a) * (w + 1 - r * b) ≤
      (u + 1 - r * lo) * (w + 1 - r * hi) := by
  by_cases ha : lo ≤ a
  · have hb : hi ≤ b := by omega
    exact Nat.mul_le_mul
      (Nat.sub_le_sub_left (Nat.mul_le_mul_left r ha) _)
      (Nat.sub_le_sub_left (Nat.mul_le_mul_left r hb) _)
  by_cases hshort : w + 1 ≤ r * b
  · simp [Nat.sub_eq_zero_of_le hshort]
  have hb : hi ≤ b := by omega
  have hhi_prod := Nat.mul_le_mul_left r hb
  have hlo_prod := Nat.mul_le_mul_left r hlohi
  have ha_prod := Nat.mul_le_mul_left r (show a ≤ lo by omega)
  have hx := Nat.mul_le_mul_left r (show hi + (lo - a) ≤ b by omega)
  rw [Nat.mul_add] at hx
  let x := u + 1 - r * lo
  let y := w + 1 - r * hi
  let d := r * (lo - a)
  have hl : u + 1 - r * a = x + d := by
    dsimp [x, d]
    rw [Nat.mul_sub_left_distrib]
    omega
  have hr : w + 1 - r * b ≤ y - d := by
    dsimp [y, d]
    omega
  have hyx : y ≤ x := by
    dsimp [x, y]
    omega
  rw [hl]
  exact Nat.le_trans (Nat.mul_le_mul_left _ hr) (transfer_capacity hyx)

#print axioms oriented_rect_capacity_le

end HighCore82258

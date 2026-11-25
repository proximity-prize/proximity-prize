import Mathlib.Data.Nat.Basic
import ProximityPrize.SubmissionLower.KoalaRectReceipts

set_option Elab.async false

-- merged module HighCore82258RectangleOrder
section Merged_HighCore82258RectangleOrder

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

end Merged_HighCore82258RectangleOrder

-- merged module KoalaRectAxes
section Merged_KoalaRectAxes

namespace KoalaRectAxes

open KoalaRect (area rectDebit rectGain rectSlots)
open K1_14 (Shape)

def swap (u : Fin 2 → ℕ) : Fin 2 → ℕ := ![u 1, u 0]

@[simp] theorem swap_zero (u : Fin 2 → ℕ) : swap u 0 = u 1 := rfl
@[simp] theorem swap_one (u : Fin 2 → ℕ) : swap u 1 = u 0 := rfl

theorem slots_swap (u d : Fin 2 → ℕ) (r : ℕ) :
    rectSlots (swap u) (swap d) r = rectSlots u d r := by
  simp only [rectSlots, swap_zero, swap_one]
  exact Nat.mul_comm _ _

theorem debit_swap (h nodes moment : ℕ) (u : Fin 2 → ℕ) :
    rectDebit h nodes moment (swap u) = rectDebit h nodes moment u := by
  simp only [rectDebit, area, swap_zero, swap_one]
  ring

theorem gain_swap (A h : ℕ) (s : Shape) (E : ℕ) (u d : Fin 2 → ℕ) :
    rectGain A h s E (swap u) (swap d) = rectGain A h s E u d := by
  simp only [rectGain, slots_swap]

theorem slots_reversed {u d actual : Fin 2 → ℕ} (r : ℕ)
    (hsides : u 1 ≤ u 0) (hdegree : actual 1 ≤ actual 0)
    (horder : d 0 ≤ d 1) (hbalanced : d 1 ≤ d 0 + 1)
    (hsum : d 0 + d 1 ≤ actual 0 + actual 1) :
    rectSlots (swap u) actual r ≤ rectSlots (swap u) (swap d) r := by
  have h := HighCore82258.oriented_rect_capacity_le (r := r) hsides hdegree horder hbalanced
    (by omega : d 0 + d 1 ≤ actual 1 + actual 0)
  simpa only [rectSlots, swap_zero, swap_one, Nat.mul_comm] using h


#print axioms slots_reversed

end KoalaRectAxes

end Merged_KoalaRectAxes


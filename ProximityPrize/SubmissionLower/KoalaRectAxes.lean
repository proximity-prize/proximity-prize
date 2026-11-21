import ProximityPrize.SubmissionLower.KoalaRectReceipts
import ProximityPrize.SubmissionLower.HighCore82258RectangleOrder

namespace KoalaRectAxes

open KoalaRect (area rectDebit rectGain rectSlots)
open K1_14 (Shape)
open KoalaRectReceipts (rectWitness)

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

theorem rect_bounds_swap {h E : ℕ} (hl : 2414 ≤ h) (hu : h ≤ 2535)
    (hel : 1 ≤ E) (heu : E ≤ 23) :
    let T := HighCore82258.terminal .h2367
    rectDebit h T.nodeRows T.poleMoment (swap (rectWitness E).U) <
      rectGain HighCore82258.agreement h T.shape E (swap (rectWitness E).U)
        (swap (rectWitness E).order) := by
  dsimp only
  rw [debit_swap, gain_swap]
  exact KoalaRectReceipts.rect_bounds hl hu hel heu

#print axioms slots_reversed
#print axioms rect_bounds_swap

end KoalaRectAxes

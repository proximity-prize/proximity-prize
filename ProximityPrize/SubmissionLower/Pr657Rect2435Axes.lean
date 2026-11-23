import ProximityPrize.SubmissionLower.KoalaRectCharge
import ProximityPrize.SubmissionLower.HighCore82258RectangleOrder

namespace Pr657Rect2435Axes

open KoalaRect (area rectDebit rectGain rectSlots)
open K1_14 (Shape)

def swap (u:Fin 2→ℕ):Fin 2→ℕ := ![u 1,u 0]

@[simp] theorem swap_zero (u:Fin 2→ℕ):swap u 0=u 1:=rfl
@[simp] theorem swap_one (u:Fin 2→ℕ):swap u 1=u 0:=rfl

theorem slots_swap (u d : Fin 2 → ℕ) (r : ℕ) :
    rectSlots (swap u) (swap d) r=rectSlots u d r:=by
  simp only [rectSlots,swap_zero,swap_one]
  exact Nat.mul_comm _ _

theorem debit_swap (h nodes moment : ℕ) (u : Fin 2 → ℕ) :
    rectDebit h nodes moment (swap u)=rectDebit h nodes moment u:=by
  simp only [rectDebit,area,swap_zero,swap_one]
  ring

theorem gain_swap (A h : ℕ) (s : Shape) (E : ℕ) (u d : Fin 2 → ℕ) :
    rectGain A h s E (swap u) (swap d)=rectGain A h s E u d:=by
  simp only [rectGain,slots_swap]

theorem slots_reversed {u d actual : Fin 2 → ℕ} (r : ℕ)
    (hsides:u 1≤u 0) (hdegree:actual 1≤actual 0)
    (horder:d 0≤d 1) (hbalanced:d 1≤d 0+1)
    (hsum:d 0+d 1≤actual 0+actual 1) :
    rectSlots (swap u) actual r≤rectSlots (swap u) (swap d) r:=by
  have h := HighCore82258.oriented_rect_capacity_le (r := r) hsides hdegree horder hbalanced
    (by omega:d 0+d 1≤actual 1+actual 0)
  simpa only [rectSlots,swap_zero,swap_one,Nat.mul_comm] using h

end Pr657Rect2435Axes

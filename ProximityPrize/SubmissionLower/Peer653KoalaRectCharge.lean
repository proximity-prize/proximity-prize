-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, KoalaRectCharge.lean.
import ProximityPrize.SubmissionLower.Peer653KoalaRectSource

namespace KoalaRect
open K1_14 (Shape shapeSum)

def rectSlots (U d : Fin 2 → ℕ) (r : ℕ) : ℕ :=
  (U 0 + 1 - r*d 0) * (U 1 + 1 - r*d 1)

def rectGain (A h : ℕ) (s : Shape) (E : ℕ) (U d : Fin 2 → ℕ) : ℕ :=
  shapeSum s fun q j =>
    let g := (q-j)/E
    let x := s.m*A+j - q*(131071-h)
    let c := rectSlots U d
    (∑ a ∈ Finset.range g, (c a - c (a+1)) * (x - 2*h*(j+a))) +
      c g * (x - 2*h*(j+g))

def rectDebit (h nodes moment : ℕ) (U : Fin 2 → ℕ) : ℕ :=
  area U * nodes + h*(U 0+U 1+2)*moment

theorem rectSlots_zero (U d : Fin 2 → ℕ) : rectSlots U d 0 = area U := by
  simp [rectSlots, area]

theorem rectSlots_antitone (U d : Fin 2 → ℕ) : Antitone (rectSlots U d) :=
  fun _ _ h => Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ h) _)
    (Nat.sub_le_sub_left (Nat.mul_le_mul_right _ h) _)

end KoalaRect

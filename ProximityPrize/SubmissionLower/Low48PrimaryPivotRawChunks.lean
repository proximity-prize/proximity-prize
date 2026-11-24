import ProximityPrize.SubmissionLower.Low48PrimaryPivotBaseline

set_option Elab.async false

set_option autoImplicit false

namespace Low48PrimaryPivot.RawReceipt
open K1_13_2_3

def rawChunk (w : Window) (start count : ℕ) : ℕ :=
  ((List.range' start count).map (rawAt w)).sum

theorem joinRaw {w : Window} {start a b x y : ℕ}
    (left : rawChunk w start a = x) (right : rawChunk w (start + a) b = y) :
    rawChunk w start (a + b) = x + y := by
  have happend : rawChunk w start (a + b) = rawChunk w start a + rawChunk w (start + a) b := by
    unfold rawChunk
    rw [← List.range'_append_1, List.map_append, List.sum_append]
  exact happend.trans (congrArg₂ (· + ·) left right)

theorem rawCompute_eq (w : Window) :
    rawCompute w = rawChunk w w.offsetLo (w.offsetHi + 1 - w.offsetLo) := rfl

end Low48PrimaryPivot.RawReceipt

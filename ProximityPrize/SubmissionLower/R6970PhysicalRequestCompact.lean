import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.R6966ProofTerminalBanks

set_option autoImplicit false

namespace Research6969.PhysicalWindow.Compact

open Lower6960.HelperSource (WidthGuard cutoffCount)

def widthCheck (b : Request) (A h : ℕ) : Bool :=
  decide (b.shape.B * (131071-h) < cutoffCount b.shape A h b.reserve)

theorem requestWidth {b : Request} {A h : ℕ}
    (ok : widthCheck b A h = true) : WidthGuard b.bank A h b.reserve := by
  unfold WidthGuard
  exact of_decide_eq_true ok

def insideCheck (s E : K1_14.Shape) : Bool :=
  decide (0<s.m ∧ s.B≤E.B ∧ s.J≤E.J ∧ s.U≤E.U)

theorem requestInside {s E : K1_14.Shape}
    (ok : insideCheck s E = true) : Research6966.TerminalBanks.inside s E := by
  unfold Research6966.TerminalBanks.inside
  exact of_decide_eq_true ok

end Research6969.PhysicalWindow.Compact

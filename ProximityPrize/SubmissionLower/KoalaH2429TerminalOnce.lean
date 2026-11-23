import ProximityPrize.SubmissionLower.Pr657Rect2435Arithmetic

set_option autoImplicit false
set_option Elab.async false

namespace KoalaH2429TerminalOnce

open K1_14 (Shape)
open KoalaRectArithmetic (RectArgs orderEnd scaledDebit)
open Pr657Rect2435Arithmetic (blockSurplus boundary runValue)
open Pr657RectStockTerminalArithmetic (Parts)
open P0_10_5 (Row scan)
open private Pr657Rect2435Arithmetic.run_sum from ProximityPrize.SubmissionLower.Pr657Rect2435Arithmetic
open private P0_10_5.scan_sum from ProximityPrize.SubmissionLower.PortHighBase
open Pr657Rect2435Arithmetic (run_sum)
open P0_10_5 (scan_sum)

def baseRow (s : Shape) (h E : ℕ) (v : RectArgs) (n i : ℕ) : Row :=
  ⟨true, runValue s h E v n i, 0⟩

/-- For a singleton height, certify its surplus without checking the adjacent height. -/
theorem positive {s : Shape} {N P h E n last count : ℕ} {v : RectArgs} {gain cost : ℤ}
    (parts : Parts (baseRow s h E v n) last 0 count gain 0)
    (hn : s.J + orderEnd s E v = n) (hc : count ≤ s.B + 1) (hJ : s.J < 2*h)
    (hb : boundary s h n count = n) (hl : 6 * scaledDebit v N P h = cost)
    (hpos : cost < gain) :
    0 < blockSurplus s N P h E v := by
  have hs := scan_sum (baseRow s h E v n) 0 count false
  rw [parts.scan_eq] at hs
  simp only [Bool.false_eq_true, ite_false, Nat.zero_add, baseRow] at hs
  rw [run_sum s h E v n count hc hJ hb] at hs
  unfold blockSurplus
  rw [hn]
  omega

end KoalaH2429TerminalOnce

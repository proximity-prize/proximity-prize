import Mathlib.Data.Nat.Basic
import ProximityPrize.SubmissionLower.FrontCore82258Model
import ProximityPrize.SubmissionLower.UpperBranch6
import ProximityPrize.SubmissionLower.KoalaRectCutoff
import ProximityPrize.SubmissionLower.R6960RescueGeometryBills
import ProximityPrize.SubmissionLower.HighCore82258PrefixProcess
import ProximityPrize.SubmissionLower.R6960TerminalReceipts

set_option Elab.async false

-- merged module HighCore82258RectangleOrder
section Merged_HighCore82258RectangleOrder

namespace HighCore82258
















































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












end KoalaRectAxes

end Merged_KoalaRectAxes

-- merged module R6960TerminalDegrees
section Merged_R6960TerminalDegrees
noncomputable section
set_option Elab.async false
namespace Lower6960.TerminalDegrees
open Polynomial Finset
open K1_14 (Equation L atMark jetAt)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open K1_14_3 (Surface Parent ProjectedProduct)
open KoalaRect (axisDegree rectGain rectDebit rectSlots)
open KoalaRectAxes (swap)
open RescueGeometry (Model Family SurfacePass OnSurface terminalShape word)
open TerminalReceipts (terminalBank bank_checked)





























































































end Lower6960.TerminalDegrees

end
end Merged_R6960TerminalDegrees

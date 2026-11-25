import ProximityPrize.SubmissionLower.FrontCore82258Model
import ProximityPrize.SubmissionLower.HighCore82258Terminal
import ProximityPrize.SubmissionLower.KoalaRectCutoff

set_option Elab.async false

-- merged module KoalaRectArithmetic
section Merged_KoalaRectArithmetic

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace KoalaRectArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open K1_14 (Shape)
open HighCore82258 (agreement)
open HighCore82258 (Bank)
open P1_7_6 (linearEnd Quad prefixProduct intervalProduct yStart)

structure RectArgs where
  U : Fin 2 → ℕ
  order : Fin 2 → ℕ









end KoalaRectArithmetic
end
section
namespace KoalaRectArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open K1_14 (Shape shapeSum slots)
open HighCore82258 (agreement)
open HighCore82258 (Bank)
open P1_7_6 (rise_of_convex)
end KoalaRectArithmetic
end
section
namespace KoalaRectArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open K1_14 (Shape shapeSum slots triangle)
open HighCore82258 (agreement)
open P1_7_6 (sum_range_guard diagonal)
end KoalaRectArithmetic
end
section
namespace KoalaRectArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open HighCore82258 (agreement)
open K1_14 (Shape)
export P1_7_6 (lt_linearEnd)
export HighCore82258TerminalArithmetic (width_sum twice_width_interval)
end KoalaRectArithmetic
end
section
namespace KoalaRectArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open HighCore82258 (agreement)
open K1_14 (Shape slots triangle)
open P1_7_6 (intervalProduct_eq)
open P1_7_6 (yStart_eq sum_clipped)
end KoalaRectArithmetic
end
section
namespace KoalaRectArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open K1_14 (Shape)
open HighCore82258 (agreement)
open P1_7_6 (intervalProduct_eq)
open P1_7_6_4 (Core corePrefix diagonalCore)
end KoalaRectArithmetic
end
section
namespace KoalaRectArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open Finset
open K1_14 (Shape)
open HighCore82258 (agreement)
open P0_10_5 (Row scan)
open P0_10_5 (scan_sum)
end KoalaRectArithmetic
end
section
namespace KoalaRectArithmetic
open P1_7_6 (Quad linearEnd intervalProduct yStart)
open KoalaRect (rectGain rectDebit rectSlots_antitone)
open K1_14 (Shape)
open P0_10_5 (Row scan joinRows)
open HighCore82258TerminalArithmetic (Parts)
end KoalaRectArithmetic
end

namespace KoalaRectArithmetic
open HighCore82258 (agreement Bank)
open KoalaRect (rectGain rectDebit)



end KoalaRectArithmetic

end Merged_KoalaRectArithmetic

-- merged module KoalaRectReceipts
section Merged_KoalaRectReceipts

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaRectReceipts
open KoalaRectArithmetic
open KoalaRect (rectDebit rectGain)
open HighCore82258 (terminal agreement)
open HighCore82258TerminalArithmetic (Parts)


def paidCap : ℕ → ℕ
  | 1 => 468
  | 2 => 464
  | 3 => 460
  | 4 => 454
  | 5 => 450
  | 6 => 444
  | 7 => 440
  | 8 => 434
  | 9 => 428
  | 10 => 422
  | 11 => 416
  | 12 => 410
  | 13 => 402
  | 14 => 394
  | 15 => 386
  | 16 => 378
  | 17 => 366
  | 18 => 332
  | 19 => 268
  | 20 => 199
  | 21 => 125
  | 22 => 47
  | _ => 0

local notation "last!" l "," r => Parts.final (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel))
local notation "more!" l "," r "," p => Parts.more (gain := l) (next := r)
  (P0_10_5.Row.eq_of_check (by decide +kernel)) p
local notation "block!" nn "," k "," l "," r "," p => certify
  (n := nn) (last := k) (cost := l) (costNext := r) p
  (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide) (by decide)





























end KoalaRectReceipts

end Merged_KoalaRectReceipts

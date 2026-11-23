import ProximityPrize.SubmissionLower.KoalaRectArithmetic

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

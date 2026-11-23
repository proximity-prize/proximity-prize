import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r6 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 6
    (rectWitness 6) (endpoints 6).1 (endpoints 6).2 :=
  certify_endpoints (n := 1596) (last := 9)
    (cost := 0xf9207ea179afc9a46c18fb80) (costNext := 0xf92085b6954f4e9bad7b2dc0)
    (Parts.more (gain := 0xe88d3064ec30cb489b7f3780) (next := 0xe8b1da70471c683331ce1ec0)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x10935d95d3e4d0d06e7dcf80) (next := 0x106f0e5ebaac5aba3fe20c00)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

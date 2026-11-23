import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r9 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 9
    (rectWitness 9) (endpoints 9).1 (endpoints 9).2 :=
  certify_endpoints (n := 1608) (last := 9)
    (cost := 0xff263993fb5849e57c18fb80) (costNext := 0xff2640a916f7cedcbd7b2dc0)
    (Parts.more (gain := 0xee690b86a0ea9999c1137a80) (next := 0xee8e9da7dabd80f2b02b85c0)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x10bd511ec7aceddd06656980) (next := 0x10981bd9fce03daf8c650000)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r23 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 23
    (rectWitness 23) (endpoints 23).1 (endpoints 23).2 :=
  certify_endpoints (n := 1702) (last := 13)
    (cost := 0x2cbbef7681230e2c92618fb80) (costNext := 0x2cbbefe7d2dd067c0677b2dc0)
    (Parts.more (gain := 0x29bec10a27553b90968676700) (next := 0x29c56c5e351f3c5beb06d7900)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x2fe60f5248956daff5ff9700) (next := 0x2f7c53b5a389348d2d8ba300)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

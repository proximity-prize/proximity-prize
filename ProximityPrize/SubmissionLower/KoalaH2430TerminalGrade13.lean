import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r13 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 13
    (rectWitness 13) (endpoints 13).1 (endpoints 13).2 :=
  certify_endpoints (n := 1632) (last := 10)
    (cost := 0x10b87c51b036572902218fb80) (costNext := 0x10b87cc301f04f787637b2dc0)
    (Parts.more (gain := 0xfa4799d0a18f1fa5e8f57e00) (next := 0xfa6f09ebd06aa7f9b7879300)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x114048517e103603e44c6700) (next := 0x1119393b27d07ce25929d200)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

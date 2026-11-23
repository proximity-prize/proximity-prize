import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r21 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 21
    (rectWitness 21) (endpoints 21).1 (endpoints 21).2 :=
  certify_endpoints (n := 1729) (last := 14)
    (cost := 0x2cbbef7681230e2c92618fb80) (costNext := 0x2cbbefe7d2dd067c0677b2dc0)
    (Parts.more (gain := 0x29961e456239b0ff11a36dc80) (next := 0x299cce9fa90239136e60bc840)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x325d1d2341f94c4b6d615980) (next := 0x31f30f19ca1a43fbfe282b00)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

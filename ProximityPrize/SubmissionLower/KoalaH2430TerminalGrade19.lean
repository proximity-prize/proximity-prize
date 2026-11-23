import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r19 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 19
    (rectWitness 19) (endpoints 19).1 (endpoints 19).2 :=
  certify_endpoints (n := 1763) (last := 15)
    (cost := 0x2cbbef7681230e2c92618fb80) (costNext := 0x2cbbefe7d2dd067c0677b2dc0)
    (Parts.more (gain := 0x298210716c877e5879cbf6bc0) (next := 0x2988c1ccfb232416e999739c0)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x339e0400b6b9b45afefa1a00) (next := 0x3333e5e677656759822baa40)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

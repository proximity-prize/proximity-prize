import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r18 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 18
    (rectWitness 18) (endpoints 18).1 (endpoints 18).2 :=
  certify_endpoints (n := 1782) (last := 16)
    (cost := 0x2cbbef7681230e2c92618fb80) (costNext := 0x2cbbefe7d2dd067c0677b2dc0)
    (Parts.more (gain := 0x2976cb837e859193759c37440) (next := 0x297d7d696d68b4ecbc696d1c0)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x3452502afb06fb0db01cdec0) (next := 0x33e8296c06211b646b443400)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

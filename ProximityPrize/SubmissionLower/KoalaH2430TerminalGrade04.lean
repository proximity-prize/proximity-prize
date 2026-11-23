import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r4 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 4
    (rectWitness 4) (endpoints 4).1 (endpoints 4).2 :=
  certify_endpoints (n := 1589) (last := 9)
    (cost := 0xf5706f24cda65b989018fb80) (costNext := 0xf5707639e945e08fd17b2dc0)
    (Parts.more (gain := 0xe4fc2a4511db92a253c26ca0) (next := 0xe52045f5ef46ca1682f9a8a0)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x10744ffbd4fc2c629b443ec0) (next := 0x10508de17cbd09a6bfb22fe0)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

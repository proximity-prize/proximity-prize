import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r20 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 20
    (rectWitness 20) (endpoints 20).1 (endpoints 20).2 :=
  certify_endpoints (n := 1745) (last := 15)
    (cost := 0x2cbbe4a476859236ad018fb80) (costNext := 0x2cbbe515c83f8a862117b2dc0)
    (Parts.more (gain := 0x298c61c4e4c154f25a16300e0) (next := 0x2993129d6679a84cc28f94aa0)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x32f8340187b9ce9269228f00) (next := 0x328e1e14f53129a9abb46700)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

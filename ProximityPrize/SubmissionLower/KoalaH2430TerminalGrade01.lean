import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r1 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 1
    (rectWitness 1) (endpoints 1).1 (endpoints 1).2 :=
  certify_endpoints (n := 1581) (last := 8)
    (cost := 0xf1eb4fc9affc56719618fb80) (costNext := 0xf1eb56decb9bdb68d77b2dc0)
    (Parts.more (gain := 0xe1786309bc26803f5af14a00) (next := 0xe19bf71c34b58c787adda680)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x1072f361415f65297c807b80) (next := 0x104fb7b60819281c6ac21f80)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

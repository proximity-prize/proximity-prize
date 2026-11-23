import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r17 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 17
    (rectWitness 17) (endpoints 17).1 (endpoints 17).2 :=
  certify_endpoints (n := 1689) (last := 13)
    (cost := 0x12dae0348c4dd2c5eac18fb80) (costNext := 0x12dae0a5de07cb155ed7b2dc0)
    (Parts.more (gain := 0x11a545e8f27fa927cffffd0a0) (next := 0x11a80f615bd20f5e6143aee60)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x1359a4b9b33cb11b05203320) (next := 0x132d79ae5da0d412debcb660)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r3 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 3
    (rectWitness 3) (endpoints 3).1 (endpoints 3).2 :=
  certify_endpoints (n := 1587) (last := 9)
    (cost := 0xf5caa289407337154218fb80) (costNext := 0xf5caa99e5c12bc0c837b2dc0)
    (Parts.more (gain := 0xe5304d9aa6c7f8add7e1ba00) (next := 0xe55476b4f91a6fd416b22e00)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x109a8809506cd528208c2780) (next := 0x1076b8a830304b294655cc80)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

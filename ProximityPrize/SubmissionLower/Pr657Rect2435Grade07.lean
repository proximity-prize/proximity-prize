import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r7 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 7
    (rectWitness 7) (endpoints 7).1 (endpoints 7).2 :=
  certify_endpoints (n := 1534) (last := 9)
    (cost:=0xcb41e965dbce16c11422bd00) (costNext:=0xcb41ef1ebc8d1ac7e4bc8000)
    (Parts.more (gain := 0xbc23a00bf4feb158b884c000) (next := 0xbc42fa66f902c8671fc4f800)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xf1e7aed944d5bcb2c56fc00) (next := 0xeff6aa4a64dda4cf715d800)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

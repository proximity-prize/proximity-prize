import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r11 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 11
    (rectWitness 11) (endpoints 11).1 (endpoints 11).2 :=
  certify_endpoints (n := 1552) (last := 10)
    (cost:=0xd290a6bcd0f2a945e222bd00) (costNext:=0xd290ac75b1b1ad4cb2bc8000)
    (Parts.more (gain := 0xc327ca3045a5d47064ca5880) (next := 0xc3484c4b336f068f4d1dcf80)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xf68ff72f4341c75017a6e80) (next := 0xf48c9dd2a8320a2fcbc1a80)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

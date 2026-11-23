import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r22 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 22
    (rectWitness 22) (endpoints 22).1 (endpoints 22).2 :=
  certify_endpoints (n := 1644) (last := 13)
    (cost:=0x2410ae4be86418bbf9422bd00) (costNext:=0x2410aea7767008fc664bc8000)
    (Parts.more (gain := 0x2147b4fc61525853e83fe2c60) (next := 0x214d5a65bcaefbe4592be1c40)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x2c941937c9716131b2442a00) (next := 0x2c3a8abfa07726a0d125b320)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

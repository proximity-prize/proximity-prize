import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r18 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 18
    (rectWitness 18) (endpoints 18).1 (endpoints 18).2 :=
  certify_endpoints (n := 1709) (last := 16)
    (cost:=0x2410b03d2326d4768ca22bd00) (costNext:=0x2410b098b132c4b6f9abc8000)
    (Parts.more (gain := 0x2121a0620a5d17b00eb07cc80) (next := 0x2127487b205850a2a317df480)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x2ef1129c300c37533bf5b4c0) (next := 0x2e9758b3bee8d5f683f35880)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

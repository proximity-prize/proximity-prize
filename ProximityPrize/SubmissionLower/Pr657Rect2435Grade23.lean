import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r23 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 23
    (rectWitness 23) (endpoints 23).1 (endpoints 23).2 :=
  certify_endpoints (n := 1632) (last := 13)
    (cost:=0x2410b03d2326d4768ca22bd00) (costNext:=0x2410b098b132c4b6f9abc8000)
    (Parts.more (gain := 0x215bccfcdd12bc7b7be272480) (next := 0x21616f92e122b6d653eff7900)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x2b5d9b7dcb3f046296185480) (next := 0x2b043b64701d09df6f3ca500)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

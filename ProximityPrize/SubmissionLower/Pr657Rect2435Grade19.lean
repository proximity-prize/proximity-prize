import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r19 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 19
    (rectWitness 19) (endpoints 19).1 (endpoints 19).2 :=
  certify_endpoints (n := 1690) (last := 15)
    (cost:=0x2410b03d2326d4768ca22bd00) (costNext:=0x2410b098b132c4b6f9abc8000)
    (Parts.more (gain := 0x212ab30670251d74295c2e200) (next := 0x21305aae6bdc624db8b5c3e40)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x2e5fe47ff2c3c3c53c614680) (next := 0x2e0631a753b288ab056f0f80)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

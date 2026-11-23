import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r13 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 13
    (rectWitness 13) (endpoints 13).1 (endpoints 13).2 :=
  certify_endpoints (n := 1565) (last := 10)
    (cost:=0xd82b69a5cc50a28cde22bd00) (costNext:=0xd82b6f5ead0fa693aebc8000)
    (Parts.more (gain := 0xc87776018d773a06c82626c0) (next := 0xc898db08039bcc5459639440)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xfb40a78ac0d2dd49505e640) (next := 0xf92f3d82d43429ad4b751c0)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

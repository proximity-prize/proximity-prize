import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r8 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 8
    (rectWitness 8) (endpoints 8).1 (endpoints 8).2 :=
  certify_endpoints (n := 1538) (last := 9)
    (cost:=0xccc775d3ea1144c33e22bd00) (costNext:=0xccc77b8ccad048ca0ebc8000)
    (Parts.more (gain := 0xbd9a7b23f1a25b363a891f00) (next := 0xbdba1341f158c0fb094ed400)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xf2d1e23adaedc47f7880180) (next := 0xf0dd0992aa9bce003dc2800)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

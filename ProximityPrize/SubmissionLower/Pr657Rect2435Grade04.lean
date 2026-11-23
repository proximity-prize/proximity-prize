import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r4 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 4
    (rectWitness 4) (endpoints 4).1 (endpoints 4).2 :=
  certify_endpoints (n := 1524) (last := 9)
    (cost:=0xc6957ca6534297adf222bd00) (costNext:=0xc695825f34019bb4c2bc8000)
    (Parts.more (gain := 0xb7a3c987efc2ec94f7e4c180) (next := 0xb7c2676aaf1c895d85ff3780)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xef1bb33ea70d63950f71980) (next := 0xed365ccc0692344278b9800)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

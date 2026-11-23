import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r3 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 3
    (rectWitness 3) (endpoints 3).1 (endpoints 3).2 :=
  certify_endpoints (n := 1521) (last := 9)
    (cost:=0xc5bbe3bbed8e49aaac22bd00) (costNext:=0xc5bbe974ce4d4db17cbc8000)
    (Parts.more (gain := 0xb6ce06a4dae3c63bff3f7500) (next := 0xb6ec81af1c2b68aa3a12cf00)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xeee05740a927bca82c2fe80) (next := 0xecfd29fafb3779fd9f3df00)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

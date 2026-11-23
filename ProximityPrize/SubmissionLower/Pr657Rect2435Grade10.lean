import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r10 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 10
    (rectWitness 10) (endpoints 10).1 (endpoints 10).2 :=
  certify_endpoints (n := 1547) (last := 10)
    (cost:=0xd072a145f204cc515922bd00) (costNext:=0xd072a6fed2c3d05829bc8000)
    (Parts.more (gain := 0xc11f7fca160926e57b464f20) (next := 0xc13fac6a406133c3d5339100)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xf533c44836dc8fd5aef7e60) (next := 0xf335b7280aa30270e8098a0)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

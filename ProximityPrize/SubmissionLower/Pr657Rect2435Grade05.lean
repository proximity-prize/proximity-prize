import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r5 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 5
    (rectWitness 5) (endpoints 5).1 (endpoints 5).2 :=
  certify_endpoints (n := 1527) (last := 9)
    (cost:=0xc8220f186a7baa384522bd00) (costNext:=0xc82214d14b3aae3f15bc8000)
    (Parts.more (gain := 0xb92271f3d48a2997d327ea40) (next := 0xb9414e185a16510435cf0e20)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xeffc117e095510db98ace40) (next := 0xee12df72f46773ee49e8700)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r2 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 2
    (rectWitness 2) (endpoints 2).1 (endpoints 2).2 :=
  certify_endpoints (n := 1519) (last := 9)
    (cost:=0xc51f291d9a5abd580822bd00) (costNext:=0xc51f2ed67b19c15ed8bc8000)
    (Parts.more (gain := 0xb625c0b43b7b2897df995500) (next := 0xb6442373a6b41a3cd7fd7d00)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xef97ce6768c094d21a1c300) (next := 0xedb62263412e6c21b496600)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

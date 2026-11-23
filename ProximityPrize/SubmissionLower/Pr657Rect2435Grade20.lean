import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r20 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 20
    (rectWitness 20) (endpoints 20).1 (endpoints 20).2 :=
  certify_endpoints (n := 1673) (last := 15)
    (cost:=0x2410a783b7f63d962d222bd00) (costNext:=0x2410a7df46022dd69a2bc8000)
    (Parts.more (gain := 0x213301bc6756af471a3206500) (next := 0x2138a8f92501119ad71835b20)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x2dda5cd1fdfff15905eac840) (next := 0x2d80b0a9fe79273909fd4320)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

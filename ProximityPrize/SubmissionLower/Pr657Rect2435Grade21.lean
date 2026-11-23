import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r21 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 21
    (rectWitness 21) (endpoints 21).1 (endpoints 21).2 :=
  certify_endpoints (n := 1658) (last := 14)
    (cost:=0x2410ac8eca95b27227422bd00) (costNext:=0x2410acea58a1a2b2944bc8000)
    (Parts.more (gain := 0x213afa2d62c83ddf48728d0a0) (next := 0x2140a0fb64df4760c6fc58cc0)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x2d5b4198cc2cefced0c61d40) (next := 0x2d019c5e71952895c49978e0)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r17 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 17
    (rectWitness 17) (endpoints 17).1 (endpoints 17).2 :=
  certify_endpoints (n := 1619) (last := 13)
    (cost:=0xf3371cf011ec1e02c922bd00) (costNext:=0xf33722a8f2ab220999bc8000)
    (Parts.more (gain := 0xe1a32ca1df1ff719e008b300) (next := 0xe1c8d8d32cc49968969ac3c0)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x1193f04e45bd5255070e3c20) (next := 0x116e9b96ef81c4c1202d8880)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

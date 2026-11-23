import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r14 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 14
    (rectWitness 14) (endpoints 14).1 (endpoints 14).2 :=
  certify_endpoints (n := 1573) (last := 11)
    (cost:=0xdb7f6248e42b48cc9a22bd00) (costNext:=0xdb7f6801c4ea4cd36abc8000)
    (Parts.more (gain := 0xcb9cb9a318df7d6dbae73840) (next := 0xcbbea580b5dbd28f80f0ba20)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xfe2afc13b7d85fc81f574c0) (next := 0xfc113662a7a1012c6466ae0)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

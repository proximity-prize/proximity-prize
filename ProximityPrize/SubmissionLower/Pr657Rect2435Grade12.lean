import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r12 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 12
    (rectWitness 12) (endpoints 12).1 (endpoints 12).2 :=
  certify_endpoints (n := 1558) (last := 10)
    (cost:=0xd577197b893700802a22bd00) (costNext:=0xd5771f3469f60486fabc8000)
    (Parts.more (gain := 0xc5e779480b4d0de86d924200) (next := 0xc6087075897c2c6b1187d080)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xf8fd5ec059104d13586f580) (next := 0xf6f2c3f2ae57bb9becf0d80)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

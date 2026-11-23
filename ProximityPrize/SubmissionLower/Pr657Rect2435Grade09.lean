import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r9 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 9
    (rectWitness 9) (endpoints 9).1 (endpoints 9).2 :=
  certify_endpoints (n := 1542) (last := 10)
    (cost:=0xce30e118ce29df107b22bd00) (costNext:=0xce30e6d1aee8e3174bbc8000)
    (Parts.more (gain := 0xbefb28c165c7d8b2f5b11900) (next := 0xbf1afa05b8218639a73ee200)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xf35d3da15bb95881259a6c0) (next := 0xf164da1d536aa8c3b39e080)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

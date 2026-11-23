import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r16 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 16
    (rectWitness 16) (endpoints 16).1 (endpoints 16).2 :=
  certify_endpoints (n := 1597) (last := 12)
    (cost:=0xe7ef4d0581a5ee133622bd00) (costNext:=0xe7ef52be6264f21a06bc8000)
    (Parts.more (gain := 0xd737bd740eecaebbadb68ec0) (next := 0xd75ba027bc154bf41c6f4720)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x10b7c01aa20036ee847407e0) (next := 0x1094311bc8525f0959bc6600)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

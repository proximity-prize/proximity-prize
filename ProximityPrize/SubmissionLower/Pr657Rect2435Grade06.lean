import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r6 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 6
    (rectWitness 6) (endpoints 6).1 (endpoints 6).2 :=
  certify_endpoints (n := 1530) (last := 9)
    (cost:=0xc8d51c8a597145ce8322bd00) (costNext:=0xc8d522433a3049d553bc8000)
    (Parts.more (gain := 0xb9da12e357f853878ebdf580) (next := 0xb9f90b91f2a91cea1cb74e80)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xefb1518871dac1b1ed20d40) (next := 0xedc65a74779a840dcae6180)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r15 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 15
    (rectWitness 15) (endpoints 15).1 (endpoints 15).2 :=
  certify_endpoints (n := 1584) (last := 11)
    (cost:=0xe119211a74aa6a92cd22bd00) (costNext:=0xe11926d355696e999dbc8000)
    (Parts.more (gain := 0xd0d5e0ba49432554806e26c0) (next := 0xd0f8af473c46e727d74ab080)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x10434cac2b6f15d5ad5015c0) (next := 0x1020cf841db2e3fcf503d100)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

import ProximityPrize.SubmissionLower.Pr657Rect2435ReceiptData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r1 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 1
    (rectWitness 1) (endpoints 1).1 (endpoints 1).2 :=
  certify_endpoints (n := 1516) (last := 9)
    (cost:=0xc36642b20534b758b722bd00) (costNext:=0xc366486ae5f3bb5f87bc8000)
    (Parts.more (gain := 0xb4861fef1a51019f95a5adc0) (next := 0xb4a43d1c827ea2f60c9dc840)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0xee0271990671f524a021b00) (next := 0xec25155614841d350300940)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end Pr657Rect2435Receipts

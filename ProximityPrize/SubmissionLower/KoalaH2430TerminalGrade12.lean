import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r12 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 12
    (rectWitness 12) (endpoints 12).1 (endpoints 12).2 :=
  certify_endpoints (n := 1625) (last := 10)
    (cost := 0x10881d374657ce62e3818fb80) (costNext := 0x10881da89811c6b25797b2dc0)
    (Parts.more (gain := 0xf75f9283769bf2aedd1e0100) (next := 0xf7868d78feeb4e090c29c160)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x112284415aa807da765b33e0) (next := 0x10fbe950b84bace7b517ca20)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r10 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 10
    (rectWitness 10) (endpoints 10).1 (endpoints 10).2 :=
  certify_endpoints (n := 1613) (last := 10)
    (cost := 0x101b40bf857bdfbde4818fb80) (costNext := 0x101b4130d735d80d5897b2dc0)
    (Parts.more (gain := 0xf0de7d4ac4d6535b029edac0) (next := 0xf1047205261fa4bb31466ba0)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x10d5b0d938bcb6cb245c3ee0) (next := 0x10b019d6e4516c51711242e0)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

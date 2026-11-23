import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r15 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 15
    (rectWitness 15) (endpoints 15).1 (endpoints 15).2 :=
  certify_endpoints (n := 1652) (last := 11)
    (cost := 0x116c7e12a169e42e4fe18fb80) (costNext := 0x116c7e83f323dc7dc3f7b2dc0)
    (Parts.more (gain := 0x104e933fc0a5e385af8f09200) (next := 0x1051256bffb661e45161a6a80)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x11debced81431298d99ffb80) (next := 0x11b5fef4c839a90ce9873280)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r2 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 2
    (rectWitness 2) (endpoints 2).1 (endpoints 2).2 :=
  certify_endpoints (n := 1584) (last := 9)
    (cost := 0xf3e3b26c5040a5d76618fb80) (costNext := 0xf3e3b9816be02acea77b2dc0)
    (Parts.more (gain := 0xe35ac92f681ab1f2e6247f80) (next := 0xe37ea9255a44d936b9854280)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x108903e48162dce6ea677c80) (next := 0x10657d017c1ecea8455b3b00)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

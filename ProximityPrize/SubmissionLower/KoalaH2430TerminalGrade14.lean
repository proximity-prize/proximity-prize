import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r14 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 14
    (rectWitness 14) (endpoints 14).1 (endpoints 14).2 :=
  certify_endpoints (n := 1641) (last := 11)
    (cost := 0x11056cfaea5c889085818fb80) (costNext := 0x11056d6c3c1680dff997b2dc0)
    (Parts.more (gain := 0xfed56832d7c7d06114855b60) (next := 0xfefd9246ce4306819c144360)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x118170f02978f3116da7dac0) (next := 0x1159a97c9f6a05540581a8a0)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

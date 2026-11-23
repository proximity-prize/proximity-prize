import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r16 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 16
    (rectWitness 16) (endpoints 16).1 (endpoints 16).2 :=
  certify_endpoints (n := 1666) (last := 12)
    (cost := 0x11fae21c1f8dcbd388418fb80) (costNext := 0x11fae28d7147c422fc57b2dc0)
    (Parts.more (gain := 0x10d47e257234d785a483de6c0) (next := 0x10d725c2be04787c153013d40)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x12667bd9e1d2cf260e65de80) (next := 0x123c69d2a5754d8285c281c0)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

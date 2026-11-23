import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r22 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 22
    (rectWitness 22) (endpoints 22).1 (endpoints 22).2 :=
  certify_endpoints (n := 1715) (last := 14)
    (cost := 0x2cbbed10e39a05dcfca18fb80) (costNext := 0x2cbbed823553fe2c70b7b2dc0)
    (Parts.more (gain := 0x29a6009a1153178bfa3a5edc0) (next := 0x29acaf443c536fe9e452cb4a0)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x316470db3f7399feec9d6d80) (next := 0x30fa7e6c3d2db77ee7c1f720)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

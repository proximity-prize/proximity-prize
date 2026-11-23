import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r5 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 5
    (rectWitness 5) (endpoints 5).1 (endpoints 5).2 :=
  certify_endpoints (n := 1593) (last := 9)
    (cost := 0xf86cb356f1e361646018fb80) (costNext := 0xf86cba6c0d82e65ba17b2dc0)
    (Parts.more (gain := 0xe7cd0caeb0a07a4d593b79e0) (next := 0xe7f19b6144bf121c1fedbde0)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x109fd4409b041135ac2fd300) (next := 0x107ba02922f0b94080eed8a0)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

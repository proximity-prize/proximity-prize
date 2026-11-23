import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r8 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 8
    (rectWitness 8) (endpoints 8).1 (endpoints 8).2 :=
  certify_endpoints (n := 1604) (last := 9)
    (cost := 0xfd998947e46e09b68618fb80) (costNext := 0xfd99905d000d8eadc77b2dc0)
    (Parts.more (gain := 0xecde3f106bdbc9c4ddb27e00) (next := 0xed039563adad576dfb8bed80)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x10bb77275270a89c7462b600) (next := 0x10967d2c4957340c64026800)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

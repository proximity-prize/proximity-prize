import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r7 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 7
    (rectWitness 7) (endpoints 7).1 (endpoints 7).2 :=
  certify_endpoints (n := 1600) (last := 9)
    (cost := 0xfbeb9aa4dc959042c218fb80) (costNext := 0xfbeba1b9f835153a037b2dc0)
    (Parts.more (gain := 0xeb38e79bbd58bf42106fc000) (next := 0xeb5dfcebffe4b1f5ebdc3c00)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x10b2f17548678d3a30a7e000) (next := 0x108e37eea526258cf2877000)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

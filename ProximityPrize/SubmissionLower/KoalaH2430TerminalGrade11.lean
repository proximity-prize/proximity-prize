import ProximityPrize.SubmissionLower.KoalaH2430TerminalData

set_option Elab.async false
set_option maxRecDepth 18000
set_option quotPrecheck false
set_option maxHeartbeats 12000000

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks certify_endpoints)
open Pr657RectStockTerminalArithmetic (Parts)

theorem r11 : EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 11
    (rectWitness 11) (endpoints 11).1 (endpoints 11).2 :=
  certify_endpoints (n := 1618) (last := 10)
    (cost := 0x10417b0b206208f52b618fb80) (costNext := 0x10417b7c721c01449f77b2dc0)
    (Parts.more (gain := 0xf33266c1ef29e042bbbea780) (next := 0xf358b7743dcd75bee4710880)
      (P0_10_5.Row.eq_of_check (by decide +kernel))
      (Parts.final (gain := 0x10e575fcd469740cbf59d580) (next := 0x10bf83d12029e950938d4c80)
        (P0_10_5.Row.eq_of_check (by decide +kernel))))
    (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide)

end KoalaH2430Terminal

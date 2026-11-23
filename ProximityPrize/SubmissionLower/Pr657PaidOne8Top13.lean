import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

set_option linter.defProp false

namespace Pr657PaidOne8Top13
open Compact54Packed (paidGroup checkedWindows)
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceTableBase (Covered)
open Compact50Cover (PaidBatch tilesOf checks)

private abbrev P:=PaidBatch .one8 13
private def batch0:List P:=paidGroup ["(2%?!I"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 39 10 = true :=
  checkedWindows tiles 134 39 [8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 13) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+13) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top13

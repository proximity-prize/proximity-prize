import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open Compact54Packed (paidGroup checkedWindows)
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceTableBase (Covered)
open Compact50Cover (PaidBatch tilesOf checks)

set_option linter.defProp false

namespace Pr657PaidOne8Top9

private abbrev P:=PaidBatch .one8 9
private def batch0:List P:=paidGroup ["0!G'vf"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 27 22 = true :=
  checkedWindows tiles 134 27 [8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+9) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top9

namespace Pr657PaidOne8Top10

private abbrev P:=PaidBatch .one8 10
private def batch0:List P:=paidGroup [".&>`U)"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 30 19 = true :=
  checkedWindows tiles 134 30 [8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+10) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top10

namespace Pr657PaidOne8Top11

private abbrev P:=PaidBatch .one8 11
private def batch0:List P:=paidGroup [",*63L)"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 33 16 = true :=
  checkedWindows tiles 134 33 [8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+11) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top11

namespace Pr657PaidOne8Top12

private abbrev P:=PaidBatch .one8 12
private def batch0:List P:=paidGroup ["*.-dC)"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 36 13 = true :=
  checkedWindows tiles 134 36 [8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+12) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top12

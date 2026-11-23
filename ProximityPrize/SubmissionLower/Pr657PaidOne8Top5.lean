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

namespace Pr657PaidOne8Top5

private abbrev P:=PaidBatch .one8 5
private def batch0:List P:=paidGroup ["7oif(b"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 15 34 = true :=
  checkedWindows tiles 134 15 [8, 8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+5) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top5

namespace Pr657PaidOne8Top6

private abbrev P:=PaidBatch .one8 6
private def batch0:List P:=paidGroup ["5sa@e%"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 18 31 = true :=
  checkedWindows tiles 134 18 [8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+6) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top6

namespace Pr657PaidOne8Top7

private abbrev P:=PaidBatch .one8 7
private def batch0:List P:=paidGroup ["3wWyCE"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 21 28 = true :=
  checkedWindows tiles 134 21 [8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+7) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top7

namespace Pr657PaidOne8Top8

private abbrev P:=PaidBatch .one8 8
private def batch0:List P:=paidGroup ["1{OT!f"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 24 25 = true :=
  checkedWindows tiles 134 24 [8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+8) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top8

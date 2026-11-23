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

namespace Pr657PaidOne7Top9

private abbrev P:=PaidBatch .one7 9
private def batch0:List P:=paidGroup ["/p.V55 <T;fE &(k/AI &(k?a% &(k@Qz n$3}U"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 27 23 = true :=
  checkedWindows tiles 134 27 [8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .one7).t+9) .one7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne7Top9

namespace Pr657PaidOne7Top10

private abbrev P:=PaidBatch .one7 10
private def batch0:List P:=paidGroup ["-t&1qU <T;fE -m#u(5 'yK)9A '<OZR5 %wfX+Q %wfabj %:k&,U"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 30 20 = true :=
  checkedWindows tiles 134 30 [8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .one7).t+10) .one7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne7Top10

namespace Pr657PaidOne7Top11

private abbrev P:=PaidBatch .one7 11
private def batch0:List P:=paidGroup ["&15sKU &15|%z #UGMxj %{zGkv %{8ro1 #A|4YU"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 33 17 = true :=
  checkedWindows tiles 134 33 [8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .one7).t+11) .one7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne7Top11

namespace Pr657PaidOne7Top12

private abbrev P:=PaidBatch .one7 12
private def batch0:List P:=paidGroup ["*,w$QQ <T;fE %wfaV^ %wfbHU"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 36 14 = true :=
  checkedWindows tiles 134 36 [8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .one7).t+12) .one7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne7Top12

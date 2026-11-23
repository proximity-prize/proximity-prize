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

namespace Pr657PaidOne8Top1

private abbrev P:=PaidBatch .one8 1
private def batch0:List P:=paidGroup ["&17yEv &19-]n &19ML5 &19fS9 &19o-^ &19o|^ $5F~<Y %~@$85", "0HW'j) %}[fPQ %}0nM- %|bnbE"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 3 46 = true :=
  checkedWindows tiles 134 3 [8, 8, 8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+1) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top1

namespace Pr657PaidOne8Top2

private abbrev P:=PaidBatch .one8 2
private def batch0:List P:=paidGroup ["=KqO)Y /iZTL~ /,`j.5 /iZd|- /,`j/^ /iZtM9 /,`j1)"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 6 43 = true :=
  checkedWindows tiles 134 6 [8, 8, 8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+2) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top2

namespace Pr657PaidOne8Top3

private abbrev P:=PaidBatch .one8 3
private def batch0:List P:=paidGroup [";WOB(I .LdX{z .Le-p^ .LdiM) .Le-r)"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 9 40 = true :=
  checkedWindows tiles 134 9 [8, 8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+3) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top3

namespace Pr657PaidOne8Top4

private abbrev P:=PaidBatch .one8 4
private def batch0:List P:=paidGroup ["9[]`EQ 9Svh&= -mR_{b -0W=()"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 12 37 = true :=
  checkedWindows tiles 134 12 [8, 8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .one8).t+4) .one8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne8Top4

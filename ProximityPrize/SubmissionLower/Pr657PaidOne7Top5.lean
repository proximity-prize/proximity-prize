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

namespace Pr657PaidOne7Top5

private abbrev P:=PaidBatch .one7 5
private def batch0:List P:=paidGroup [",WovSn ,VJ@In <T;fE ,WYcBv ,WpYVU %wf?'Q %wfOF- %wfW}E", "%wP.E^ %wP/7U"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 15 35 = true :=
  checkedWindows tiles 134 15 [8, 8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .one7).t+5) .one7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne7Top5

namespace Pr657PaidOne7Top6

private abbrev P:=PaidBatch .one7 6
private def batch0:List P:=paidGroup ["5[ah0d <T;fE &0Pt-5 &0Q'Kn &0Q7kI &0Q@Db $4_NbU"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 18 32 = true :=
  checkedWindows tiles 134 18 [8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .one7).t+6) .one7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne7Top6

namespace Pr657PaidOne7Top7

private abbrev P:=PaidBatch .one7 7
private def batch0:List P:=paidGroup ["3h)mfM <T;fE &)#Y'= &)#jEv &)#r}1 &)#{VI kC/v"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 21 29 = true :=
  checkedWindows tiles 134 21 [8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .one7).t+7) .one7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne7Top7

namespace Pr657PaidOne7Top8

private abbrev P:=PaidBatch .one7 8
private def batch0:List P:=paidGroup ["1k~HDn <T;fE &)#b1% &)#jh= &)#sAU $j,a)U"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 24 26 = true :=
  checkedWindows tiles 134 24 [8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .one7).t+8) .one7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne7Top8

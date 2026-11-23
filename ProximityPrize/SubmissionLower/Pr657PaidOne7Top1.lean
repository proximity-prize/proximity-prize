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

namespace Pr657PaidOne7Top1

private abbrev P:=PaidBatch .one7 1
private def batch0:List P:=paidGroup ["&.AfUf &14WR% &152VM &15Z.5 0N0$j% <T;fE 0H=Mvj &$*3o-", "(XrT!M )8nK~) (Xrvhr %}Wbpn %wfG&- %wfO]E %wfX6^ %wfamv", "$ZoFmU"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 3 47 = true :=
  checkedWindows tiles 134 3 [8, 8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .one7).t+1) .one7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne7Top1

namespace Pr657PaidOne7Top2

private abbrev P:=PaidBatch .one7 2
private def batch0:List P:=paidGroup ["&13nB= &14wqr &15J0z &15c7~ /2#;eE <T;fE ,#q7~) &)ePuU", "$jn>]U (Xr;b9 (Xr[~) %wf.N^ %wf>n9 %wfGGQ %wOzmj %wP&G%"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 6 44 = true :=
  checkedWindows tiles 134 6 [8, 8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .one7).t+2) .one7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne7Top2

namespace Pr657PaidOne7Top3

private abbrev P:=PaidBatch .one7 3
private def batch0:List P:=paidGroup [".Swl(z .R=2YI <T;fE &)N1Q^ &)NQ@z &)Nb`U .LJ[g1 'ya[?5", "'yae:r %wfX+Q %wfabj %:k&,U"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 9 41 = true :=
  checkedWindows tiles 134 9 [8, 8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .one7).t+3) .one7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne7Top3

namespace Pr657PaidOne7Top4

private abbrev P:=PaidBatch .one7 4
private def batch0:List P:=paidGroup ["-tfylY -60AmI <T;fE -mNKlf -0SA.1 'ya:<Y '<et=n '<e}.A", "'<f0d5 %wf>c- %wfG<E %wfOs^ %wfXLv %wfb'1 #>x,4U"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 12 38 = true :=
  checkedWindows tiles 134 12 [8, 8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .one7).t+4) .one7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne7Top4

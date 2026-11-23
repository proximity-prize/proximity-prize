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

namespace Pr657PaidOne6Top1

private abbrev P:=PaidBatch .one6 1
private def batch0:List P:=paidGroup ["%Cq-)v %Ct(+~ &12uSv &13gnI &142E1 0N,wG; <iFG^ &mu?-b","'Fik`% )9$';` &)yd?1 $k%Q'1 )rdWDY )rd`-j &^`Zq` )8lpT)","%wdtw1 %wNH[Y %w8brf %w8s4A %w9'[- %w905E"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 3 48 = true :=
  checkedWindows tiles 135 3 [8, 8, 8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .one6).t+1) .one6 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne6Top1

namespace Pr657PaidOne6Top2

private abbrev P:=PaidBatch .one6 2
private def batch0:List P:=paidGroup ["&11|!^ &13O6z &14!S% &14:Z) /o2z{= <iFG^ &)d(k1 &)d1DI", "#Mua:1 (XpQ)| (XpRHG (XqLwb %wdsAM %wdt3E %wd|j^ %we(Cv"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 6 45 = true :=
  checkedWindows tiles 135 6 [8, 8, 8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .one6).t+2) .one6 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne6Top2

namespace Pr657PaidOne6Top3

private abbrev P:=PaidBatch .one6 3
private def batch0:List P:=paidGroup ["&12uSv &13gnI &142E1 .R;h*^ <i'J7 &)d(=^ &)d0tv &(=}Cv", "(Xp:6? 'yu^%n %wztp1 %wdscr %wdtTj %we'tE"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 9 42 = true :=
  checkedWindows tiles 135 9 [8, 8, 8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .one6).t+3) .one6 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne6Top3

namespace Pr657PaidOne6Top4

private abbrev P:=PaidBatch .one6 4
private def batch0:List P:=paidGroup ["-tzm-` -s>hv+ <iFG^ &)Lg91 &)M1mn &)MB/I &)MRN% &(SJ@-", "$-/b#) %wNk}^ #{0qxQ"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 12 39 = true :=
  checkedWindows tiles 135 12 [8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .one6).t+4) .one6 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne6Top4

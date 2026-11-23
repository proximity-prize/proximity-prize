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

namespace Pr657PaidOne6Top9

private abbrev P:=PaidBatch .one6 9
private def batch0:List P:=paidGroup ["&14:Z) &14Jyl &14[;O #UF.1? <iFG[ &]h.vd %{y(/^ $^r.{Q", "#A960h #|+%`O %wNYx9 %wNcQQ %w99%t"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 27 24 = true :=
  checkedWindows tiles 135 27 [8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .one6).t+9) .one6 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne6Top9

namespace Pr657PaidOne6Top10

private abbrev P:=PaidBatch .one6 10
private def batch0:List P:=paidGroup [".S5XrG <iN/| &(itU^ &'olGf &$*1%; #~`zX[ #@TWel #?ZNfO","%wNk[9 %w99</"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 30 21 = true :=
  checkedWindows tiles 135 30 [8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .one6).t+10) .one6 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne6Top10

namespace Pr657PaidOne6Top11

private abbrev P:=PaidBatch .one6 11
private def batch0:List P:=paidGroup [",W,Z>? <iFG[ &(itx% &%{J<h $*A.k` %<GQ%Q #}P6w# j#EO"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 33 18 = true :=
  checkedWindows tiles 135 33 [8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .one6).t+11) .one6 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne6Top11

namespace Pr657PaidOne6Top12

private abbrev P:=PaidBatch .one6 12
private def batch0:List P:=paidGroup ["*[9AH| <iFG[ &(SIpj &$U9<; #~`zM[ #@TWYl #{rONO"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 36 15 = true :=
  checkedWindows tiles 135 36 [8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .one6).t+12) .one6 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne6Top12

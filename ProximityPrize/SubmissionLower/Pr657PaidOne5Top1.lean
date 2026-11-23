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

namespace Pr657PaidOne5Top1

private abbrev P:=PaidBatch .one5 1
private def batch0:List P:=paidGroup ["9H]]1 .^T7A bcLfz &10sM; &12NIt &138|# 1.)O!9 <heW|", "&1155- &,$Tw9 )9$m{n &'XOjW %FM6#O )5&SoQ %~OaHv %~$i[j", "%}Uy@f %}*yT~ %{L=XY %z<-<~ $]K4F7 %xtF/p %:RFY# $ZA<qO"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 3 49 = true :=
  checkedWindows tiles 135 3 [8, 8, 8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+1) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top1

namespace Pr657PaidOne5Top2

private abbrev P:=PaidBatch .one5 2
private def batch0:List P:=paidGroup ["&10sB+ &12N>h &13)C3 &13Pwx /o24F; 9N)~C &(=%}h &%e.SS", "$*UxGS (XpRSS %~:6A^ %}UaDv %|[y<d $^Zwdd #Ad]M+ #@SvvG", "%wz-2| %wdEW5 %wdN1K #>4L'O"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 6 46 = true :=
  checkedWindows tiles 135 6 [8, 8, 8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+2) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top2

namespace Pr657PaidOne5Top3

private abbrev P:=PaidBatch .one5 3
private def batch0:List P:=paidGroup ["&11t[d &12n^W &1395? /26]o[ 9N)~C &)Lab+ &&_>l3 &$>zS#","(XpA{b 'yttB` #BH:jd #?D2fS #?D2fp aX:Y# %yBFH' aBeHO","#|kwSC %wd4i) %wd=BA %wdEyW %:<xw7 %vjES3 %vjFE+"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 9 43 = true :=
  checkedWindows tiles 135 9 [8, 8, 8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+3) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top3

namespace Pr657PaidOne5Top4

private abbrev P:=PaidBatch .one5 4
private def batch0:List P:=paidGroup ["&12N3W &13)8' &13Pll -s?B6` 9N)~C &'XG>S &$jza; $eG`&3", "'y_0dz 'y_I0; %{x>*| #@(n<d `t]%x $]5Ufp #@SvH[ `t]&?", "#{[3f/ %x2hXh %x2`f? #|?o1? %wd<rn %wdEL' %wdN&? iAUp", "%w8N:W $Z+gTC %vjNNp"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 12 40 = true :=
  checkedWindows tiles 135 12 [8, 8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+4) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top4

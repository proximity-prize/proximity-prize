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

namespace Pr657PaidOne4Top5

private abbrev P:=PaidBatch .one4 5
private def batch0:List P:=paidGroup ["&127?| &12g]+ &13*KO -6-g/' 8SFw; &$jB~? &!`[_S #H:G_S", "'y^gCW #~3ac/ #@=r#C %|qtkh %>|05l #bx|[ #6pe` #6xX7", "$!-j*d #Ad-RC `t-6[ $1$6l ~=St #LEkx hp6G an=ed", "#6xMO R=%S `H$qx #LEa+ hh8+ <gq[ R<w[ '4`_"] (by decide +kernel) ++ paidGroup ["%wcd$h %wctCC '4`c ho}[ '4`g #{E.C[ <gfd '4`k", "%w!IPC _8=y# '4`o $Yrb'C _!h[t ',V. <gfk"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 15 38 = true :=
  checkedWindows tiles 135 15 [8, 8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+5) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top5

namespace Pr657PaidOne4Top6

private abbrev P:=PaidBatch .one4 6
private def batch0:List P:=paidGroup [",Wm&^G ,VG^$+ 8(>T3 &)6CCK &)6Sc' &&H1m/ &#.[ll %}l:S[","#B26D; #@iz[G $!-j5W #AMWL3 #xN%S #LEkW hhBW <`+[","hp6/ hhBh a,`<W $1$+d R=%; ~=Hl R51t #LE`p","<gqC %yAtBC hp+G <gqK hh7| #@(>B[ '4`N '4`R","<gfO '4TS '4`V $[:{1C `H$ft #LEU# ~=>' ~E1S","'4`Z '4`_ <gfZ <gf_ <gfc <_h/ <gZ[ <gfg","<gfk"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 18 35 = true :=
  checkedWindows tiles 135 18 [8, 8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+6) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top6

namespace Pr657PaidOne4Top7

private abbrev P:=PaidBatch .one4 7
private def batch0:List P:=paidGroup ["&12_iW &13!X# &132wd &.ZC5x $2<I0p #~I/#W #A!OK7 aB5oG", "`H%@O %}*Agt %|EtRO hhBS <`+W $_>{AC #AyWe` R=%'", "#LE`W ~=H[ R51` <gq/ `t-+O #xMw[ <_}h <gq7", "#@=qSG hh7l ',lk '4`: R<w; '4`> #6pNp '4`B"] (by decide +kernel) ++ paidGroup ["'4`F R5&x <gfC '4`J '4`N `H$fl #LETx <gfK", "'4`R <_s# '4`V hh-# <gfR R<lO <gfV $ZV?fK", "_yy8h <gfZ <gf_ %:<@[[ <_h+ <gZW <gfc <_Pt", "<_]# <gfg #zw%sO ',V. R<lc"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 21 32 = true :=
  checkedWindows tiles 135 21 [8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+7) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top7

namespace Pr657PaidOne4Top8

private abbrev P:=PaidBatch .one4 8
private def batch0:List P:=paidGroup ["&12oZd &13*bl &0#T+; &-525K 7Y62+ #~3ay' #@=r9; %|qt`[","$^/7jC #AMWL/ $1$6K #LEkK ~=SO <`+S %?4c;h $!oGRS","',wV `t-+? #xMwK <gq# <_}W '4`& hh7[ ',l[","',l` '4`* '4`. ',lc '4`2 #6pNd ',lg '4`6","R5&h ',lk '4`: <gf7 '4`> `H$f[ #bxfl '4`B","#|kGBC <_rp <gf? '4`F a,`1d '4`J hh,t ',as","<gfF ',aw <gfJ ',a{ <gfN <gZG <gfR #6p8t","R4y# <gfV ~=3# <gZO <gfZ <gf_ #{E.8O ',V&"] ++ paidGroup ["R<lZ %:&kat ',V* R<l_ _!hPh ',V. R<lc"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 24 29 = true :=
  checkedWindows tiles 135 24 [8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+8) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top8

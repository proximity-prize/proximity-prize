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

namespace Pr657PaidOne4Top9

private abbrev P:=PaidBatch .one4 9
private def batch0:List P:=paidGroup ["&13!Lp &132lW &.ZC*l $nSIv` #@=r.7 `t-cG #~u7:S #A8%Q/", "%|[Aq# ~=SO <`+O $1$+G #LE`G ~=HK ',wR $`#XjC", "#BsiAd ',wV '4_{ ',lR '4`! ',lV '4`& R5&W", "',lZ '4`* ',l_ '4`. aB5BO $FV1[ ~==[ ',lc"] (by decide +kernel) ++ paidGroup ["'4`2 R5&d ',lg '4`6 ',lk '4`: #@iykK #LETd", "<gf7 '4`> <_rl '4`B hh,l <gf> ',ao <gfB", "',as <gfF ',aw <gfJ R4xx ',a{ <gfN ~=2x", "<gZG <gfR `2NIh #6p8t <gfV <_h# R<lR R<lV"] (by decide +kernel)
private def batch1:List P:=paidGroup ["',V& R<lZ <_]# ',V* R<l_ $Yrb'C #={Fmh ',V.", "R<lc"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 27 26 = true :=
  checkedWindows tiles 135 27 [8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+9) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top9

namespace Pr657PaidOne4Top10

private abbrev P:=PaidBatch .one4 10
private def batch0:List P:=paidGroup ["&13*V[ &0N]B7 &,|T0x t)j+| #CAz'/ #AMWy3 b&qPC hhMO", "%{b95[ $#=OuW #Ad%_` ~=HK <_}K ',wR ',wV $],BK", "#xMwK #6pNK ',lN '4_{ ',lR '4`! ',lV '4`&", "R5&W ',lZ '4`* ',l_ '4`. ',lc '4`2 ~==`"] (by decide +kernel) ++ paidGroup ["<_r` ',lg '4`6 ',lk '4`: #?C`wK <_rh <gf6", "#LETh <gf: ',ak <gf> hh,p ',ao <gfB #xMlp", "',as <gfF ',aw <gfJ #|Tr1O ',a{ <gfN `H$Zh", "<_gx <gZG <gfR ~=2| <gfV ',U{ R<lR ',V!"] (by decide +kernel)
private def batch1:List P:=paidGroup ["R<lV %w7|K+ ',V& R<lZ ',V* R<l_ %9n8Ot R4b{", "R<lc"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 30 23 = true :=
  checkedWindows tiles 135 30 [8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+10) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top10

namespace Pr657PaidOne4Top11

private abbrev P:=PaidBatch .one4 11
private def batch0:List P:=paidGroup ["&132aG &/)KAh %LkJ_S #}9PJ+ aB6(C $]a/^G #@iz// _dFH/","_8>&7 _8>&? #LEkG ~=SK R5<O $`9'*t $!C?;W ',wR","',wV ',lN '4_{ ',lR '4`! R5&S ',lV '4`&","#bxfS #6pNW ',lZ '4`* ',l_ '4`. #A!N|C aB5BO","$FV1[ <_r[ ',lc '4`2 ',lg '4`6 <_rd ',lk","'4`: <_rh <gf6 hh,h <gf: ',ak <gf> hg~d","R4mp ',ao <gfB ',as <gfF R4xt ',aw <gfJ","',a{ <gfN <gZG <gfR `2NIh #6p8t <_g| <gfV"] ++ paidGroup ["R<lR $ZV7gt hh!# ',V! R<lV #>IO'[ ',V& R<lZ","',V* R<l_ ',V. R<lc"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 33 20 = true :=
  checkedWindows tiles 135 33 [8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+11) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top11

namespace Pr657PaidOne4Top12

private abbrev P:=PaidBatch .one4 12
private def batch0:List P:=paidGroup ["+x0];7 7.-m# &#p9~` %}Ud~? #Ewzm; #~3XzW #@SG43 ~=H7","R5&C <_rK #LEvK <`+K ',wN ',wR ',wV `2N`?","#6pNK ',lN '4_{ ',lR '4`! $_)H;W #AMOMp ',lV","'4`& b<E|K `t-+K R5&W ',lZ '4`* ',l_ '4`.","',lc '4`2 #bxf` ~==` <_r` ',lg '4`6 ',lk","'4`: <_rh <gf6 <gf: ',ak <gf> hh,p ',ao","<gfB `2NTd ',as <gfF ',aw <gfJ #6pCx ',a{","<gfN <_gx <gZG <gfR <gfV <_h# R<lR #{ZaIO"] ++ paidGroup ["_dF'h hgst R<lV ',V& R<lZ <_]# ',V* R<l_","%9n8Dh ',V. R<lc"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 36 17 = true :=
  checkedWindows tiles 135 36 [8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+12) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top12

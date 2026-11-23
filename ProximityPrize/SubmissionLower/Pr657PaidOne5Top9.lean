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

namespace Pr657PaidOne5Top9

private abbrev P:=PaidBatch .one5 9
private def batch0:List P:=paidGroup ["&13Pwx &13j!# &/kXN+ $3c4Z# &]h6_' #CBCG| #Ad]6G b<ukW", "`t[w[ #x}fh %>%V%S _du~l i9mx `2~D' #7B33 #?.]T|", "#|kw1x _zK>G #>v*O? %wMx}K %wN$Vd %:<xTp 'd!k #={v]7", "_#B>p"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 27 25 = true :=
  checkedWindows tiles 135 27 [8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+9) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top9

namespace Pr657PaidOne5Top10

private abbrev P:=PaidBatch .one5 10
private def batch0:List P:=paidGroup ["&13Y$d &13jCK &.EGM[ 98Sm? #~`;^? #@SvjO %|FF6p $_)wqd", "#Az21G $G(gd #cJ>d ~lsd Rd[l '[9o #@(n&h _8mgx", "_NBy' `2~D+ #cR=h `t[m7 _zK>K #{qfU+ %:RMq| %w8Nh+", "_#B>p"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 30 22 = true :=
  checkedWindows tiles 135 30 [8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+10) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top10

namespace Pr657PaidOne5Top11

private abbrev P:=PaidBatch .one5 11
private def batch0:List P:=paidGroup ["-7(I6/ 98Sm? &'Byr| &!vX4' $_*#kO $[},-x $ZmE5/ #>`T2'","_dv,? b<ukW _zK2G _NBmS _8m[[ #}$D-K #}$D-t #AN*%K","Rd[l _du~l i9m| _zK3# #?.]T| #7B37 #|kw1| #cJJC","%wz,nW `2~97 #7Ixp %:i#ld"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 33 19 = true :=
  checkedWindows tiles 135 33 [8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+11) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top11

namespace Pr657PaidOne5Top12

private abbrev P:=PaidBatch .one5 12
private def batch0:List P:=paidGroup ["+;5W&S 98Sm? &%#OD| %~PG3W i)eP[ #~und? #@jKpO ~lsd", "Rd[l #>`T2` i9m| %=+EHp #}f*`[ #Lu9# #>v*Ct #?p:}|", "#7B37 `HSU? #7Ixp #{E^>7 %:'EN| _#B>p"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 36 16 = true :=
  checkedWindows tiles 135 36 [8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+12) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top12

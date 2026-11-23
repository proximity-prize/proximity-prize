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

namespace Pr657PaidOne5Top5

private abbrev P:=PaidBatch .one5 5
private def batch0:List P:=paidGroup ["-7i413 -6Ck`# 9N)~C &)L?ul &)LW|h &)LaV# &&36># &#Di`h", "k3]1p $]5^p? b<uvh $[;M+[ `HSa/ %<rp7p #}{]qd #?D2r3", "#cJUC #|UD77 _dv-O"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 15 37 = true :=
  checkedWindows tiles 135 15 [8, 8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+5) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top5

namespace Pr657PaidOne5Top6

private abbrev P:=PaidBatch .one5 6
private def batch0:List P:=paidGroup [",Wmm@S +wLP'' 9N)~C &)6rnS &)7-uO &'XG3K &$)?!' %BeO&x", "#A8T*S #?p;A` $!.;`p #AN)wK `2~Cl #7B2| #@(n1| `_)g/", "#x}gC %x2W/+ $[%ww| #>v*ZO %w8Vfd #>J!-C"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 18 34 = true :=
  checkedWindows tiles 135 18 [8, 8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+6) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top6

namespace Pr657PaidOne5Top7

private abbrev P:=PaidBatch .one5 7
private def batch0:List P:=paidGroup ["&138|# &13XkK &13j-/ &/U&H3 #TK3r3 '{~st7 &#/-=p #~`3_t","#A!~vO $#(L<p `2~C` #7B2l `2~Cx #7B3' #?p:}t $[gUBh","`_)g; $1Z`p #>v*D7 %w8=@? %w8EwW %w8NPp %:'EN| _8uOp"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 21 31 = true :=
  checkedWindows tiles 135 21 [8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+7) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top7

namespace Pr657PaidOne5Top8

private abbrev P:=PaidBatch .one5 8
private def batch0:List P:=paidGroup ["&13Hn/ &13au7 &0{7=S &./rGd #~IfWC #@SvuW %|rF-d %{bhkt", "$#(L<p #B2eBG _du~[ i9mh #?p:r[ `HSIl #Lu8x ~l~|", "#LuD; a-1~7 $1RmC #|?nx' ~tgp %:RMq| %w!xp?"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 24 28 = true :=
  checkedWindows tiles 135 24 [8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+8) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top8

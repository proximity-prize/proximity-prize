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

namespace Pr657PaidTwo7wideTop1

private abbrev P:=PaidBatch .two7wide 1
private def batch0:List P:=paidGroup ["&13m}r &15xGY &16Z4E &16s;I &16{rn &.HQ7^ $o&6Y^ %}C7M9", "#B5oB= #@mUYI #?sL{~ `b;e5 $4m^j %|_j8r %|3r5M %{OF~%", "lKU9 lSHf #|2-- #P)s1 #$~[5 $!1E3Y #Agf[9 *u}k", "*u}o *n!: @K&k `62[v #P)]) *n!> @K&o *mt6"] (by decide +kernel) ++ paidGroup ["U~,k *mt: U~,o @Bz6 U~,s @Bz: U~,w Uv#6", "U~,{ `b:]r #f[K~ #$~#~ Uuj% Uv#: U~-! lK)6", "U~-& lK): U~-* #$~/6 U~-. #$~/: U~-2 #:S56", "U~-6 #$~$6 lS32 #$~$: lS36 %w&6=5 $Z.y<r #>7fkY"] (by decide +kernel)
private def batch1:List P:=paidGroup ["%vmO=)"]
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 130 3 47 = true :=
  checkedWindows tiles 130 3 [8, 8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 130) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7wide).t+1) .two7wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7wideTop1

namespace Pr657PaidTwo7wideTop2

private abbrev P:=PaidBatch .two7wide 2
private def batch0:List P:=paidGroup ["&158}5 &16:gI &16c>1 &16s]r &/-/>5 &,T7r) s3<bb &lR`?n", "&lSB7^ dIwx9 #AQ409 #@W+Qn a0D*% #%)eY #~xx+z #@mU8-", "lKU) U~7Q #f[xv #:Saz lKI~ %{{GDM *u}Z @K&V", "$^^y!= *n!* @K&Z $`m>r #|1sr #P)[v @C(& @K&_"] (by decide +kernel) ++ paidGroup ["@C(* @K&c Uv.& @K&g Uv.* @K&k lK4& @K&o", "Uv#& U~,k `b:]b #f[Kn Uv#* U~,o lK)& U~,s", "lK)* U~,w #$~/& U~,{ #$~/* U~-! #?1fM) `62/b", "#$~/. U~-& #:S5* U~-* #:S5. U~-. UuGn #P);*"] (by decide +kernel)
private def batch1:List P:=paidGroup ["U~-2 #P);. U~-6 %wPqJb %wQ$j= %wQ-CU #{_;wb #>c]})", "#:S*. lS32 _QSMb Uu<n #P)0* lS36 $Z.xxM #>7^ar", "_<*CM @K2Y"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 130 6 44 = true :=
  checkedWindows tiles 130 6 [8, 8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 130) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7wide).t+2) .two7wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7wideTop2

namespace Pr657PaidTwo7wideTop3

private abbrev P:=PaidBatch .two7wide 3
private def batch0:List P:=paidGroup ["&15x<I &16R@v &16c`Y &0<k!M &,jbn5 %KHrs1 &e%l|^ &d+|1v", "#@W+Q^ aEw:r $J;)~ #~cE;v #@mUY- lKTv @C=z @K1I", "#|2,j #P)rn #$~Zr @K&B @K&F *m~w @K&J $#+UmI", "#B5nr~ *m~{ @K&N $`m>f #|1sf #P)[j @C'w @K&R"] (by decide +kernel) ++ paidGroup ["%yqWmr @C'{ @K&V Uv-w @K&Z Uv-{ @K&_ aEn@-", "%.uJf $J:!f lK3w @K&c lK3{ @K&g lK4! @K&k", "#$~9{ @K&o lK({ U~,k #$~.w U~,o #$~.{ U~,s", "#fSB1 #$~/! U~,w #:S4{ U~,{ #:S5! U~-! #:S5&"] (by decide +kernel)
private def batch1:List P:=paidGroup ["U~-& %xK.9M %;O`0z _;~GU #P);! U~-* #P);& U~-.", "lJMf #P);* U~-2 _}[YI _QSMY #f[A& U~-6 %wPyTI", "%wQ%.b #P)0& lS32 #P)0* lS36 $Z.xV) #>7^?M _<!9f", "@Jn5 @JyA @K'J %vmWi5 _&T=Y"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 130 9 41 = true :=
  checkedWindows tiles 130 9 [8, 8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 130) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7wide).t+3) .two7wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7wideTop3

namespace Pr657PaidTwo7wideTop4

private abbrev P:=PaidBatch .two7wide 4
private def batch0:List P:=paidGroup ["&16:[9 &16c3% &16sQf &.HP[v &+.{[b #OlN/9 $)I<vv #}i4ur", "#@AU@Q `63Af #P2*9 lKTj @C=n #~7<`j bUTO) $4e=b", "#P)rb #$~Zf *u}: *n,o *u}> `b39) $4e2^ *n,s", "*u}B @C2o *u}F *m~o @K&B %|_jO- @C'k @K&F"] (by decide +kernel) ++ paidGroup ["@C'o @K&J Uv-k @K&N %{{?:f Uv-o @K&R Uv-s", "@K&V $_X,E) #f[V^ #$~.^ lK3o @K&Z lK3s @K&_", "#$~9o @K&c #$~9s @K&g #$~9w @K&k #AQ+5M bUSu)", "a0;$) $`lz^ #:S?s @K&o #f[@^ #$}u^ #$~.s U~,k"] (by decide +kernel)
private def batch1:List P:=paidGroup ["#$~.w U~,o #:S4s U~,s #:S4w U~,w #:S4{ U~,{", "#P):w U~-! #P):{ U~-& #P);! U~-* #f[@{ U~-.", "#:RYU #:Reb #f[A! U~-2 #f[A& U~-6 #f[5{ lS32", "#f[6! lS36 #{3<E5 _<!#M _<!9f @Jn5 U~-B #>!3YY"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 130 12 38 = true :=
  checkedWindows tiles 130 12 [8, 8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 130) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7wide).t+4) .two7wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7wideTop4

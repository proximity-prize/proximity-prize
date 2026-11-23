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

namespace Pr657PaidTwo7wideTop5

private abbrev P:=PaidBatch .two7wide 5
private def batch0:List P:=paidGroup ["&16R5f &16cTM &0R@(E &,T/P~ &):YPj #}R`(v #@,#PU #|2Mb", "#P*6f #:[v1 #C[+5v #AQ3vv aqw=% `wnSQ #|2B^ *u}2", "*n,g *u}6 *n,k *u}: @C2g *u}> @C2k *u}B", "#$~DY Uv-^ Uv8g *u}F @C'g @K&B @C'k @K&F"] (by decide +kernel) ++ paidGroup ["%|IG05 #f[bY #$~9Y Uv-g @K&J Uv-k @K&N $#+UbA", "#BKCxz lK3g @K&R %{er3M $`e@1 $J:!Y #f[VY lK3k", "@K&V lK3o @K&Z #$~9k @K&_ #$~9o @K&c #$~9s", "@K&g #:S?o @K&k $`lz^ #:S?s @K&o #$~.s U~,k"] (by decide +kernel)
private def batch1:List P:=paidGroup ["#:S4o U~,o `wmWQ #:S4s U~,s #:S4w U~,w #P):s", "U~,{ @B6Y #P):w U~-! #P):{ U~-& #f[@w U~-*", "#f[@{ U~-. #f[A! U~-2 #f[A& U~-6 *laF lJBb", "#f[5{ lS32 _QKCz _QSBU #f[6! lS36 #{3<E5 _<!#M"] (by decide +kernel) ++ paidGroup ["@BoY @Bzf @Jn5 U~-B #>!3YY"]
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 130 15 35 = true :=
  checkedWindows tiles 130 15 [8, 8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 130) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7wide).t+5) .two7wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7wideTop5

namespace Pr657PaidTwo7wideTop6

private abbrev P:=PaidBatch .two7wide 6
private def batch0:List P:=paidGroup ["&16Z?Q &16sFY &.2sWE &*vH?M $.Aq@~ #~7=/f bUT|% a[L5M", "`b;dU #f]Rb lKTY @C=^ *u}& *u}* *n,_ *u}.", "*n,c *u}2 $^tV<Y #A;^Nr #$~OU Uv8Y @C2_ *u}6", "@C2c *u}: @C2g *u}> `wf>~ $J:8U Uv8c *u}B"] (by decide +kernel) ++ paidGroup ["#P)[U lK3U Uv8g *u}F Uv-_ @K&B Uv-c @K&F", "Uv-g @K&J %|3r@Y lK3c @K&N lK3g @K&R lK3k", "@K&V %>Shb) #~c<nI #$~9g @K&Z #|1]Y #$~#U #$~9k", "@K&_ #$~9o @K&c #:S?k @K&g %DB^9 $J2$5 #|1QY"] (by decide +kernel)
private def batch1:List P:=paidGroup ["#:S?o @K&k $`lz^ #:S?s @K&o #:S4k U~,k a[C;-", "#:S4o U~,o #:S4s U~,s #:S4w U~,w #P):s U~,{", "#P):w U~-! #P):{ U~-& #f[@w U~-* #f[@{ U~-.", "#f[A! U~-2 #f[A& U~-6 #>c]fn _h)HI #f[5{ lS32"] (by decide +kernel) ++ paidGroup ["#f[6! lS36 $Z.xV) _;~uA _<!.Y @Bzf lS3: #zzovY"]
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 130 18 32 = true :=
  checkedWindows tiles 130 18 [8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 130) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7wide).t+6) .two7wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7wideTop6

namespace Pr657PaidTwo7wideTop7

private abbrev P:=PaidBatch .two7wide 7
private def batch0:List P:=paidGroup ["&16cI= &0~@V~ *Wk$c5 3u;;^ %CL6h~ %@^j!Y #E$E^% #A;^{r", "b*TLI `wnjM #f]GY *u}! *u}& #$~ZU @C2U *n,Z", "*u}* *n,_ *u}. @C2Z *u}2 #C0!ez c:2x% a[Cr~", "@C2_ *u}6 @C2c *u}: #:SUU Uv-U Uv8_ *u}>"] (by decide +kernel) ++ paidGroup ["$J:8U #f[mU Uv8c *u}B Uv8g *u}F Uv-_ @K&B", "Uv-c @K&F Uv-g @K&J lK3c @K&N %{{G9A lK3g", "@K&R lK3k @K&V $_X,[A #BKCy% #$~9g @K&Z #|1]Y", "#$~#U #$~9k @K&_ #$~9o @K&c #:S?k @K&g #:S?o"] (by decide +kernel)
private def batch1:List P:=paidGroup ["@K&k #:S?s @K&o #:S4k U~,k #:S4o U~,o $4dWb", "#:R{^ #:S4s U~,s #:S4w U~,w #P):s U~,{ #P):w", "U~-! `62$U #P):{ U~-& #P);! U~-* #f[@{ U~-.", "#f[A! U~-2 #f[A& U~-6 #P)0& lS32 Uu&U Uu1b"] (by decide +kernel) ++ paidGroup ["#f[6! lS36 #{3<E5 _<!#M @BoY *mi_ lS3: %vmX-Y", "#zzh&- *u~V"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 130 21 29 = true :=
  checkedWindows tiles 130 21 [8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 130) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7wide).t+7) .two7wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7wideTop7

namespace Pr657PaidTwo7wideTop8

private abbrev P:=PaidBatch .two7wide 8
private def batch0:List P:=paidGroup ["&16s;I &/-'4I &*`k:z $jC>uj #@AUKA `wo#Q #Cq^]v #AQ4/r", "b@*^I lK`U @CHY #f]1U #$~fU *u|{ *u}! *n,V", "*u}& *n,Z *u}* *n,_ *u}. @C2Z *u}2 @C2_", "*u}6 @C2c *u}: #:SUU Uv-U Uv8_ *u}> $v:h1"] (by decide +kernel) ++ paidGroup ["$J:8U #f[mU Uv8c *u}B $#m4NQ #BKD1~ Uv8g *u}F", "Uv-_ @K&B Uv-c @K&F Uv-g @K&J lK3c @K&N", "lK3g @K&R %{ez2) lK3k @K&V #$~9g @K&Z #$~9k", "@K&_ %DBi= $vB9b #|1]^ #$~9o @K&c #:S?k @K&g"] (by decide +kernel)
private def batch1:List P:=paidGroup ["#:S?o @K&k @BLY #:S?s @K&o #$~.s U~,k #:S4o", "U~,o #:S4s U~,s #:S4w U~,w #:S4{ U~,{ #P):w", "U~-! #P):{ U~-& `b:;U #f[*b #P);! U~-* #P);&", "U~-. #f[A! U~-2 #f[A& U~-6 @B+f #P)0& lS32"] (by decide +kernel) ++ paidGroup ["#P)0* lS36 %w&.(A #{3<E5 _<!#M @BoY *mi_ lS3:", "#zzh&- *u~V"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 130 24 26 = true :=
  checkedWindows tiles 130 24 [8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 130) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7wide).t+8) .two7wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7wideTop8

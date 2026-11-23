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

namespace Pr657PaidTwo6widerTop5

private abbrev P:=PaidBatch .two6wider 5
private def batch0:List P:=paidGroup ["&16bcI &-z?2v &*`y`A &(+,{U &%~=tU /wA6I #|Xn=Q #?Gdw5", "#A}Zt1 #@WB.= #?G[VM #:st5 #%@n= V8VA _}|t) +0?J", "@cEF @cEJ V8KF _}|Qv #%@A% V8*) @c$1 lkQB", "lkQF $!G:*Q #Ah(A- #%@WB #:s^> #:s^B #|HfI #P@NM"] (by decide +kernel) ++ paidGroup ["#:s0v ljvz @b_~ #PHd> #PHdB #f{j> #f{jB #|Pp>", "#|PpB $JPgE #fs>E #%7sE $5&v> $JX|: $JX|> $`i1kQ", "#C08}j +'9J $JX|B $a/%> +'.F $a/%B +'.J $a/%F", "+'.N $a/%J $a&VE #|H.E #:jcE @Y4J $a/%N +'#J"] (by decide +kernel)
private def batch1:List P:=paidGroup ["$vb+J +'#N $vb+N ar7n= $vX]I @Y)J $vb+R @Y)N", "$vb+V @Y)R $vb+Z %zl!V^ V//N $vb+_ @X{N %/71Z", "@X{R %/71_ V/$N %/71c V/$R %/71g @XpR %Dj7c", "V.vN %Dj7g V.vR %Dj7k V.vV %Dj7o V.vZ %Dj7s"] (by decide +kernel) ++ paidGroup ["#frMQ laqM V.kR %Z?=o V.kV %Z?=s `6H19 #:i}E", "V.kZ %Z?=w V.k_ %Z?={ V.`V %prCw #{I'qr #>MHw9", "V.`Z %prC{ #>7t@v _<@#Q @ao^ $va~6 +8)g #>!I[%", "_&kU= #f{`c +8)k"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 123 15 36 = true :=
  checkedWindows tiles 123 15 [8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wider).t+5) .two6wider a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6widerTop5

namespace Pr657PaidTwo6widerTop6

private abbrev P:=PaidBatch .two6wider 6
private def batch0:List P:=paidGroup ["&16rTU &-#><r &)fq$z &&xFFj $g*#Ff #?Gdl- `6RTA #AQRs=", "#@Am>M aF8~) V8VA +0?B #%@c5 V8K9 +0?F +0?J", "@cEF V8KB #~y9o% #@mt{5 V8KF _}|Qv #%@A% V8*)", "#%@W: #%@W> #%@WB #:s^> #:s^B $4{wM #P@NM #:s0v"] (by decide +kernel) ++ paidGroup ["ljvz @b_~ #PHd> #PHdB #f{j> #f{jB #|Pp> #|PpB", "$_-BqM #A}Z11 $5&v> $JPgI #fs>I #%7sI @b=v $5&vB", "$5&vF $JX|B $a/%> $a/%B `x'J= #|H9I +'.J $a/%F", "+'.N $a/%J +'.R $a/%N +'#J $vb+J +'#N $vb+N"] (by decide +kernel)
private def batch1:List P:=paidGroup ["+'#R $vb+R @Y)N $vb+V @Y)R $vb+Z @Y)V $vb+_", "%=Yn?v #~cZyj #P?^M lb5M @X{N %/71Z @X{R %/71_", "@X{V %/71c `bPuE #frdQ @X{Z %/71g ar7WE @XpR", "%Dj7c @XpV %Dj7g @XpZ %Dj7k V.vV %Dj7o V.vZ"] (by decide +kernel) ++ paidGroup ["%Dj7s @XeZ %Z?=o @Xe_ %Z?=s #:j+Q laqU V.kZ", "%Z?=w V.k_ %Z?={ @XY_ %prCw @XYc %prC{ #>7t@v", "_<@#Q @ao^ @azj $a.x> +8)g #>!Ig1 _&kaI #PHYk", "+8)k"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 123 18 33 = true :=
  checkedWindows tiles 123 18 [8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wider).t+6) .two6wider a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6widerTop6

namespace Pr657PaidTwo6widerTop7

private abbrev P:=PaidBatch .two6wider 7
private def batch0:List P:=paidGroup ["&0'6f- &+Z-<E &(@W<- &&6pzI kxe%v #|oCCI #?^9}- #%@yA", "V8bE #BwlP9 #A&JE= a[czM _Qt]- V8K9 +0?F `L(!z", "_hIc) +0?J @cEF @c/5 V8KB V8KF V8*) @c$1", "lkQB lkQF #%@WB #%@6% @bk% #:s^> #:s^B #PHd>"] (by decide +kernel) ++ paidGroup ["$#AJdf #B60X9 #:s0z ljv~ #PHdB #PHdF $JP}Q #fsTQ", "#%8,Q #f{jB #f{jF #|PpB #|PpF $5&vB @b=z $5&vF", "$5&vJ $JX|F $a&mQ #|HDQ #%7hM $a/%B $a/%F $a/%J", "+'.R $a/%N $vb+J +'#N $vb+N %=pKZQ #Bb8CE +'#R"] (by decide +kernel)
private def batch1:List P:=paidGroup ["$vb+R +'#V $vb+V +'#Z $vb+Z %Db!^ $4{4U #P?iU", "@Y)V $vb+_ +&uV %/71Z +&uZ %/71_ @X{V %/71c", "@X{Z %/71g a0Y:Q +&jZ %Dj7c +&j_ %Dj7g @XpZ", "%Dj7k @Xp_ %Dj7o @Xpc %Dj7s @XeZ %Z?=o @Xe_"] (by decide +kernel) ++ paidGroup ["%Z?=s @Xec %Z?=w @Xeg %Z?={ +&Sg %prCw $ZD[HQ", "#>MHw9 V.TQ V.`^ @XYc %prC{ #>7tL% _<@.^ @azj", "$a.x> +8)g #>!Ig1 _&kaI #PHYk +8)k"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 123 21 30 = true :=
  checkedWindows tiles 123 21 [8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wider).t+7) .two6wider a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6widerTop7

namespace Pr657PaidTwo6widerTop8

private abbrev P:=PaidBatch .two6wider 8
private def batch0:List P:=paidGroup ["&.t`_% &*JNLz &'FN^f %Em,Q^ #|CC+% `L(f= #A}[-A #@WBDM", "aF8s% _}}!- #%@n9 lkhA @cPE +0?F +0?J @cEF", "lkF1 @c/5 V8KB V8KF lkQB lkQF $!]u:1 #A;}5=", "lk0) @bv- #%@WB $5&u~ #f{_% #%@6% #%@WF #:s^B"] (by decide +kernel) ++ paidGroup ["#:s^F #PHdB #PHdF #f{jB $JP}U #fsTU #PH6~ #f{jF", "#f{jJ #|PpF #|PpJ $5&vF $5&vJ $5&vN $JX|J $vX~Y", "#|HDU #:jyU @b2~ $JX|N $_XK+f #BKcHI $JX|R $a/%N", "@b'~ $a/%R $a/%V $vb+R aF/bQ $JPP^ +'#V $vb+V"] (by decide +kernel)
private def batch1:List P:=paidGroup ["+'#Z $vb+Z +'#_ $vb+_ +&uV %/71Z +&uZ %/71_", "+&u_ %/71c +&uc %/71g +&jZ %Dj7c +&j_ %Dj7g", "+&jc %Dj7k +&jg %Dj7o #frdf lb*b @Xpc %Dj7s", "+&_c %Z?=o +&_g %Z?=s +&_k %Z?=w _}s6Q #%7%^"] (by decide +kernel) ++ paidGroup ["@Xeg %Z?={ #{_Z<- #>MI0M +&Sg %prCw +&Sk %prC{", "#>7tW1 @ao^ @azj $a.x> +8)g %vmwO% #>!Ig1 _&kaI", "#PHYk +8)k"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 123 24 27 = true :=
  checkedWindows tiles 123 24 [8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wider).t+8) .two6wider a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6widerTop8

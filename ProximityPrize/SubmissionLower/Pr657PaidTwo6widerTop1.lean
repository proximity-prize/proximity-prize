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

namespace Pr657PaidTwo6widerTop1

private abbrev P:=PaidBatch .two6wider 1
private def batch0:List P:=paidGroup ["%Q81Uf &16#$j &0R':M &-8agv &*vN|Q &)%=nv &']-=~ #@,B,9", "#?GdwQ #|Qlf #}'uz= #?^1]Y #%@cM lk]U V8V^ #~M)MQ", "#A&Iv1 +0?g #%@A5 lk;= V85E @cEc V8K_ _hI5~", "#%@61 lkQZ #%@WV `K|TA #fsTQ #:k=U #:s^R #PHdN"] (by decide +kernel) ++ paidGroup ["V7Y~ @bT) #PHdR $$&(`I #Bb0ZU #f{jN #|PpJ $5&vF", "$JX|B lbVE @Y?I $JX|F $a/%B #|H.= #P?tA #%7]E", "+'.J $a/%F +'.N $a/%J a[b]- `K{z1 @Y4J $a/%N", "+'#J $vb+J %{ew]% +'#N $vb+N @Y)J $vb+R %{9wq="] (by decide +kernel)
private def batch1:List P:=paidGroup ["%=Yn4^ @Y)N $vb+V V//J $vb+Z V//N $vb+_ #:jA=", "V.v= V/$F %/71Z V/$J %/71_ V/$N %/71c lb*J", "%/71g V.vJ %Dj7c #P?<= laq= V.vN %Dj7g `x&e1", "$4zeA la|J %Dj7k la|N %Dj7o la|R %Dj7s laqJ"] (by decide +kernel) ++ paidGroup ["%Z?=o laqN %Z?=s laqR %Z?=w #{3Qkr #%6wN %Z?={", "lafN %prCw $ZDZx~ #{I'qr _QjO- lafR %prC{ #{3RF^", "_<8$v _<@#Q @ao^ $va~6 +8)g #z{)&1 _&kaI #PHYk", "+8)k"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 123 3 48 = true :=
  checkedWindows tiles 123 3 [8, 8, 8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wider).t+1) .two6wider a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6widerTop1

namespace Pr657PaidTwo6widerTop2

private abbrev P:=PaidBatch .two6wider 2
private def batch0:List P:=paidGroup ["&15@eU &16Q|M &.^zOf &+p`B9 &):hv1 &'],yU #L<]L- #@Am3Q", "#?slx1 #?21fI V8bY #}iS/% #@,9^= #%@cE V8KI @cEQ", "+0?Z @cEV #%@A- lk;5 V85= V8KR V8KV #f{Rz", "#:s;~ #%@6) lkQR #%@WN $!1d`E #AQQv~ #:s^J #PHdF"] (by decide +kernel) ++ paidGroup ["#fsIE #:k2I lbxM #PHdJ #f{jF #|PpB `x'U1 $4{UA", "#P@-A #|PpF @b=v $5&vB $5&vF +'9J $JX|B $a/%>", "$`'K8r #CEkx^ +'.F $a/%B +'.J $a/%F @Y4F $a/%J", "@Y4J $a/%N #:jW= V//= +'#J $vb+J @Y)F $vb+N"] (by decide +kernel)
private def batch1:List P:=paidGroup ["%{OLTj $vXQ= $4{)= #P?^= @Y)J $vb+R V//F $vb+V", "V//J $vb+Z %zl!@E ar7W1 $vXF= V//N $vb+_ V/$F", "%/71Z V/$J %/71_ V/$N %/71c lb*J %/71g V.vJ", "%Dj7c V.vN %Dj7g la|J %Dj7k la|N %Dj7o la|R"] (by decide +kernel) ++ paidGroup ["%Dj7s laqJ %Z?=o laqN %Z?=s laqR %Z?=w #%6a9", "laZA #%6wN %Z?={ #{_R'9 #>c{q~ lafN %prCw _<7I5", "lafR %prC{ #>7t5j _<80% @adQ @ao^ $va~6 +8)g", "%vmwCv #z{)&1 _&kaI #PHYk +8)k"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 123 6 45 = true :=
  checkedWindows tiles 123 6 [8, 8, 8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wider).t+2) .two6wider a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6widerTop2

namespace Pr657PaidTwo6widerTop3

private abbrev P:=PaidBatch .two6wider 3
private def batch0:List P:=paidGroup ["&16#$j &0hYKQ &-#.Ur &*JFYI &(+-)f &&LFDj &dA`sI #@Au=)", "#?^:+A $5'}U #}=K.1 #?sdnM #%@c= lk]E V8VM +0?V", "#:sR) #%@L1 V855 @cER #C09AY #AQR0% #@,9G1 V8KN", "lkQJ #f{Rv #:s;z #%@6% #%@WF #%@WJ #|HfI #P@NM"] (by decide +kernel) ++ paidGroup ["#:s^F #PHdB #PHdF #f{jB #|Pp> $$gd6Q #C08}Y #|PpB", "#|HD= #P@-A #%7sE $5&v> $JX|: $JX|> +'9J $JX|B", "$a/%> +'.F $a/%B $a&V= #|H.= #:jc= +'.J $a/%F", "@Y4F $a/%J @Y4J $a/%N @Y)B $vb+J @Y)F $vb+N"] (by decide +kernel)
private def batch1:List P:=paidGroup ["@Y)J $vb+R V//F $vb+V %>(vVj `bPu1 #frd= V//J", "$vb+Z V//N $vb+_ V/$F %/71Z V/$J %/71_ V/$N", "%/71c lb*J %/71g V.vJ %Dj7c V.vN %Dj7g #P?<A", "laqA la|J %Dj7k a0Xv9 $4zeE la|N %Dj7o la|R"] (by decide +kernel) ++ paidGroup ["%Dj7s V.kR %Z?=o laqN %Z?=s laqR %Z?=w laqV", "%Z?={ %wQC9r %:UmH~ lafN %prCw #>MHTr _QjO- lafR", "%prC{ #>7t5j _<80% @adQ @ao^ $va~6 +8)g #>!I[%", "_&kU= #f{`c +8)k"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 123 9 42 = true :=
  checkedWindows tiles 123 9 [8, 8, 8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wider).t+3) .two6wider a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6widerTop3

namespace Pr657PaidTwo6widerTop4

private abbrev P:=PaidBatch .two6wider 4
private def batch0:List P:=paidGroup ["&16J+z &/X&DI &+pWNj &):hj~ &&xFQz $+(Tov #}'v>A #?slx%", "`6R>9 _hJ2I @cEE +0?J #~7[Ez #@WAu5 +0?N V8@9", "V8KB #:sR% #%@L- V851 V8KF `K|vE _}|Qv V8KJ", "lkQF #%@WB #%@WF #:s^B ljvz @b_~ #PHd> $^_:Y="] (by decide +kernel) ++ paidGroup ["#Ah(+% #PHdB lbxI ljkv #f{j> #f{jB #|HOA #P@8E", "#%7~I #|Pp> #|PpB @b=r $5&v> `x'U5 #|HDA $5&vB", "$JX|> +'9J $JX|B $a/%> +'.F $a/%B +'.J $a/%F", "@Y4F $a/%J @Y4J $a/%N $`'K-v #~y1-U +'#J $vb+J"] (by decide +kernel)
private def batch1:List P:=paidGroup ["#:jWA V//A @Y)F $vb+N @Y)J $vb+R c${P= a0Y:5", "$4{)A #P?^A @Y)N $vb+V %{$TF9 V//J $vb+Z V//N", "$vb+_ @X{N %/71Z V/$J %/71_ V/$N %/71c V/$R", "%/71g V.vJ %Dj7c V.vN %Dj7g V.vR %Dj7k #frMI"] (by decide +kernel) ++ paidGroup ["laqE la|N %Dj7o la|R %Dj7s V.kR %Z?=o V.kV", "%Z?=s laqR %Z?=w #>yQ%~ _}r}9 laqV %Z?={ V.`V", "%prCw V.`Z %prC{ #{3RQj _<80% @adQ @ao^ $va~6", "+8)g #>!I[% _&kU= #f{`c +8)k"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 123 12 39 = true :=
  checkedWindows tiles 123 12 [8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wider).t+4) .two6wider a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6widerTop4

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

namespace Pr657PaidTwo6widerTop9

private abbrev P:=PaidBatch .two6wider 9
private def batch0:List P:=paidGroup ["&-8yLQ &)%5e- &&LF#A #JtCAr #A;}xM #@Au=% `x0r5 #:t-A", "lksE +0?F +0?J $!1m99 #@mu4E lkQ9 @c:= @cEF", "@cEJ #f{u- #:s^1 lkF5 V8KF V8KJ lkQF lkQJ", "`6QWz #:sG) #%@WF #%@WJ #:s^F #:s^J #PHdF #PHdJ"] (by decide +kernel) ++ paidGroup ["#%?}% V7f) #f{jF $a'1^ #|Hf^ #PH7% #f{jJ #f{jN", "$#mR{z #BKc_I #|PpJ #|PpN $5&vJ $5&vN ar8=U $a&x^", "#|HO^ $5&vR $JX|N $JX|R $a/%N $a/%R $a/%V $vb+R", "$vb+V $vb+Z +'#_ $vb+_ %/71Z %/71_ +&u_ %/71c"] (by decide +kernel)
private def batch1:List P:=paidGroup ["#P?if V//b +&uc %/71g %Dj7c %Dj7g `bQ#^ #froj", "+&jc %Dj7k +&jg %Dj7o +&jk %Dj7s %Z?=o +&_g", "%Z?=s +&_k %Z?=w #>yQGE _}sA^ +&_o %Z?={ %prCw", "V.kj +&Sk %prC{ #>7tW1 _<@9j @b(v $JXrF +8)g"] (by decide +kernel) ++ paidGroup ["#>!Ir= #f{`c +8)k"]
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 123 27 24 = true :=
  checkedWindows tiles 123 27 [8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wider).t+9) .two6wider a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6widerTop9

namespace Pr657PaidTwo6widerTop10

private abbrev P:=PaidBatch .two6wider 10
private def batch0:List P:=paidGroup ["&+Z-R^ &(+-)f &%<`KU #}=Sd~ a[lS= $a0BI #~7[sA b@APY", "a[ky) `6R(- #:st9 V8K= @cEB @cEF @cEJ V8KF", "V8KJ #%@L5 @c$5 lkQF lkQJ #%@WF #%@WJ #%@WN", "#E$Zo1 #Bb9)M blI;U lk%- @bk1 #:s^J #:s^N #PHdJ"] (by decide +kernel) ++ paidGroup ["`bQqU $5&k- #PHB- ljw- #PHdN #f{jJ #f{jN #f{jR", "#|PpN #|PpR #|PpV $5&vR #:k'b #%?g- $5&vV $5&vZ", "$JX|V $JX|Z $JX|_ $a/%Z #P@!f lbVf @b(- $a/%_", "$a/%c $vb+_ $vb+c %Db-r $JPPn #P?tj %/71_ %/71c"] (by decide +kernel)
private def batch1:List P:=paidGroup ["%/71g @ao1 %/71k %/71o %Dj7k %Dj7o +&jk %Dj7s", "%Z?=o %Z?=s `6HR^ #:jAj %Z?=w +&_o %Z?={ %prCw", "%prC{ #>7|J^ _&k3r $JXrF +8)g %9r;`U #>!Ir= _&klU", "#:sSs +8)k"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 123 30 21 = true :=
  checkedWindows tiles 123 30 [8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wider).t+10) .two6wider a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6widerTop10

namespace Pr657PaidTwo6widerTop11

private abbrev P:=PaidBatch .two6wider 11
private def batch0:List P:=paidGroup ["&*JNd5 &&xFQz $*YLLn #}iSrM #@,B,) `bZa9 #f|OE #:t8I", "+0?J +0?N lkQ= @c:A @cEJ @cEN #|Q)5 #PHo9", "lkF9 V8KJ V8KN #D*R3U #Ah(cQ b*l)^ lkQJ `x0/)", "#f{j1 lkQN #%@WJ #%@WN #%@WR #:s^N #:s^R #PHdN"] (by decide +kernel) ++ paidGroup ["#PHdR #f{jN #%?}1 @bT1 #f{jR #f{jV #|PpR #|PpV", "#PH,1 lja1 #|PpZ $5&vV $5&vZ $vY,n #|HOj #:k'j", "$5&v_ $JX|Z $JX|_ $JX|c $a/%_ $a/%c $vb+_ $vb+c", "$vb+g @az5 $vb+k %/.yv $JPPv #P?tr $vb+o %/71k"] (by decide +kernel)
private def batch1:List P:=paidGroup ["%/71o @ao9 %/71s %/71w %Dj7s %Dj7w @ad= %Dj7{", "%Dj8! %Z?={ %Z?>! @aXA %Z?>& #>7|Uj $a.x> +8)g", "%9rCS% #>!I}I #PHYk +8)k"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 123 33 18 = true :=
  checkedWindows tiles 123 33 [8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wider).t+11) .two6wider a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6widerTop11

namespace Pr657PaidTwo6widerTop12

private abbrev P:=PaidBatch .two6wider 12
private def batch0:List P:=paidGroup ["&):ptj &%hhcQ 0/tGM #}S!%^ #?sm<9 #f|9A #:t!E lkhI", "+0?N #Bwl[U #A&JPY a[kn- `L(.1 #PHz= +0?R @cEN", "@cER V8KN V8KR lkQN lkQR #%@A9 @bv9 #%@WN", "#%@WR #:s^N #:s^R #:s^V #%@+5 V7q9 #PHdR #PHdV"] (by decide +kernel) ++ paidGroup ["$JQ+n #|PY5 #:s15 #PHdZ #f{jV #f{jZ #|PpV #|PpZ", "#|Pp_ $5&vZ $5&v_ %//=v $4{ar #f{29 $5&vc $JX|_", "$JX|c @b39 $JX|g $JX|k $a/%g $a/%k $a/%o $vb+k", "$vb+o @az= $vb+s $vb+w %/71s %/71w %Dj7s %Dj7w"] (by decide +kernel)
private def batch1:List P:=paidGroup ["%Dj7{ %Dj8! %Dj8& %Dj8* %Dj8. _<@9j @b(v @b4%", "$5&lN +8)g #>!I}I #PHYk +8)k"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 123 36 15 = true :=
  checkedWindows tiles 123 36 [8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 123) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wider).t+12) .two6wider a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6widerTop12

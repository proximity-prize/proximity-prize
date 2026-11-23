import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54LastOrder

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open Compact54Packed (checkedWindows)
open Compact54LastOrder (paidGroupLast)
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceTableBase (Covered)
open Compact50Cover (PaidBatch tilesOf checks)

set_option linter.defProp false

namespace Pr657PaidTwo7lastTop9

private abbrev P:=PaidBatch .two7last 9
private def batch0:List P:=paidGroupLast ["&#`*7~ %}E[}- fUa2~ ).y]) B-Dw #&hy* #<>-2 #<>-6", "#<>-: #<>-> #<>-B #<>-F #<>-J #<>-N #<>-R #<>-V", "#<>-Z #<>-_ #<>-c #<>-g #<>-k #<>-o #<>-s #<>-w", "#<>-{ #<>.! #<>.& #<>.* #<>.. #<>.2 #}>sE5 aGX#M"] (by decide +kernel) ++ paidGroupLast ["`MO9v #<>.6 #<>.: #<>.> #<>.B #<>.F #Qq4B #hF:>", "n5;z B-$~ #hF:B #hF:F #}y@B #}y@F #C]i{v #ARzG9", "as`kE `MFwE #QhfQ #&h6v W_|z $6NFB $6NFF $6NFJ", "$L$LF $L$LJ $bVRF $bVRJ #&`-M B$bM ,N[R $bVRN"] (by decide +kernel)
private def batch1:List P:=paidGroupLast [",N[V $bVRR B$bR $bVRV ,NPR $x,XR ,NPV $x,XV", "B$VR $x,XZ #&_tM B$KM B$VV $x,X_ B$VZ $x,Xc", "WV]V $x,Xg $x$!U #}pEQ #<4zQ WV]Z $x,Xk WV]_", "$x,Xo n,cZ $x,Xs n,c_ $x,Xw n,cc $x,X{ n,cg"] (by decide +kernel) ++ paidGroupLast ["$x,Y! n,W_ %0__{ n,Wc %0_`! n,Wg %0_`& %[VLA", "$x#ib #h<{Y #&_^c $x,N& ,`VV #&_^g $x,N* ,`VZ", "#&_^k $x,N. ,`V_ #&_^o $x,N2 ,`Vc #<4dk $x,N6", ",`Vg #<4do $x,N: ,`Vk #<4ds $x,N> ,`Vo #<4dw"] (by decide +kernel)
private def batch2:List P:=paidGroupLast ["$x,NB ,`Vs #Qgjs $x,NF ,`Vw #<4Xs %0_TB ,`V{", "#<4Xw %0_TF ,`W! #<4X{ %0_TJ ,`W& #<4Y! %0_TN", ",`W* #Qg_{ $x,CN B5^& #Qg`! $x,CR B5^* #Qg`&", "$x,CV B5^. #h<f! $x,CZ B5^2 #h<f& $x,C_ B5^6"] (by decide +kernel) ++ paidGroupLast ["#h<f* $x,Cc B5^: #h<f. $x,Cg B5^> #QgT. %0_Ic", "B5^B #QgT2 %0_Ig B5^F #QgT6 %0_Ik B5^J #QgT:", "%0_Io B5^N #QgT> %0_Is B5^R #QgTB $x,8s WhdN", "#QgTF $x,8w WhdR #QgTJ $x,8{ WhdV #QgTN $x,9!"] (by decide +kernel)
private def batch3:List P:=paidGroupLast ["WhdZ #QgTR $x,9& Whd_ #<4CR %0_?! Whdc #<4CV", "%0_?& Whdg #<4CZ %0_?* Whdk #<4C_ %0_?. Whdo", "#<4Cc %0_?2 Whds #<4Cg %0_?6 Whdw #<4Ck %0_?:", "Whd{ #<4Co $x,.: n=jw #<4Cs $x,.> n=j{ #<4Cw"] (by decide +kernel) ++ paidGroupLast ["$x,.B n=k! #&_2w %0_4> n=k& #&_2{ %0_4B n=k*", "#&_3! %0_4F n=k. #&_3& %0_4J n=k2 #&_3* %0_4N", "n=k6 #&_3. %0_4R n=k: #&_32 %0_4V n=k> #&_36", "%0_4Z n=kB #&_3: $x,#Z #&pq> #>9>NM B#~Y B+r)"] (by decide +kernel)
private def batch4:List P:=paidGroupLast ["B+}5 $bUzg #&pqB $Yx/Zr #>#rD9 n5JN #&pqF"]
private def batches:List P:=batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 127 27 23 = true :=
  checkedWindows tiles 127 27 [8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 127) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7last).t+9) .two7last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7lastTop9

namespace Pr657PaidTwo7lastTop10

private abbrev P:=PaidBatch .two7last 10
private def batch0:List P:=paidGroupLast ["&!e~YY $azIrE f@.-) ).yh5 ,W?! n5s2 #&i': #&i'>", "#&i'B #&i'F #&i'J #&i'N #&i'R #&i'V #&i'Z #&i'_", "#&i'c #&i'g #&i'k #&i'o #&i's #&i'w #&i'{ #&i(!", "#&i(& #&i(* #&i(. #&i(2 #&i(6 #&i(: #&i(> #&i(B"] (by decide +kernel) ++ paidGroupLast ["#&i(F #?_XiM `7z(~ #&i(J #&i(N n5R- B-;1 #<>.J", "#<>.N #Qq4J #By6QE #@o?5E a2%XQ #Qq4N #&hM) B-%)", "#hF:J #hF:N #hEk% #&hB% #}y@J #}y@N #}y@R $6NFN", "$6NFR $L$LN $L$LR #&`8Y B$mY $L$LV $bVRR ,N[Z"] (by decide +kernel)
private def batch1:List P:=paidGroupLast ["$bVRV $bN2^ #h=UY #&`-Y $x,XR $x,XV ,NPZ $x,XZ", ",NP_ $x,X_ ,NPc $x,Xc B$V_ $x,Xg B$Vc $x,Xk", "B$Vg $x,Xo WV]c $x,Xs %0V3f $6EVb #<4z^ WV]g", "$x,Xw WV]k $x,X{ WV]o $x,Y! WVQg %0__{ WVQk"] (by decide +kernel) ++ paidGroupLast ["%0_`! WVQo %0_`& n,Wk $x,N& ,`VV n,Wo $x,N*", ",`VZ n,Ws $x,N. ,`V_ n,Ww $x,N2 ,`Vc #&_^s", "$x,N6 ,`Vg #&_^w $x,N: ,`Vk #&_^{ $x,N> ,`Vo", "#&__! $x,NB ,`Vs #<4d{ $x,NF ,`Vw #&_R{ %0_TB"] (by decide +kernel)
private def batch2:List P:=paidGroupLast [",`V{ #&_S! %0_TF ,`W! #&_S& %0_TJ ,`W& #&_S*", "%0_TN ,`W* #&_S. $x,CN B5^& #&_S2 $x,CR B5^*", "#&_S6 $x,CV B5^. #&_S: $x,CZ B5^2 #&_S> $x,C_", "B5^6 #&_SB $x,Cc B5^: #&_SF $x,Cg B5^> n,BF"] (by decide +kernel) ++ paidGroupLast ["%0_Ic B5^B n,BJ %0_Ig B5^F n,BN %0_Ik B5^J", "n,BR %0_Io B5^N n,BV %0_Is B5^R n,BZ $x,8s", "WhdN n,B_ $x,8w WhdR n,Bc $x,8{ WhdV n,Bg", "$x,9! WhdZ n,Bk $x,9& Whd_ WV1k %0_?! Whdc"] (by decide +kernel)
private def batch3:List P:=paidGroupLast ["WV1o %0_?& Whdg WV1s %0_?* Whdk WV1w %0_?.", "Whdo WV1{ %0_?2 Whds WV2! %0_?6 Whdw WV2&", "%0_?: Whd{ WV2* $x,.: n=jw WV2. $x,.> n=j{", "WV22 $x,.B n=k! B#~2 %0_4> n=k& B#~6 %0_4B"] (by decide +kernel) ++ paidGroupLast ["n=k* B#~: %0_4F n=k. B#~> %0_4J n=k2 B#~B", "%0_4N n=k6 B#~F %0_4R n=k: B#~J %0_4V n=k>", "B#~N %0_4Z n=kB B#~R $x,#Z #&pq> _=`Hf B+}5", "$bUzg #&pqB $Yx/Zr #>#rD9 n5JN #&pqF"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1 ++ batch2 ++ batch3
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 127 30 20 = true :=
  checkedWindows tiles 127 30 [8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 127) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7last).t+10) .two7last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7lastTop10

namespace Pr657PaidTwo7lastTop11

private abbrev P:=PaidBatch .two7last 11
private def batch0:List P:=paidGroupLast ["%~ku|5 $$i8Z^ )DNy9 ,W?! n5s2 #&i': #&i'> #&i'B", "#&i'F #&i'J #&i'N #&i'R #&i'V #&i'Z #&i'_ #&i'c", "#&i'g #&i'k #&i'o #&i's #&i'w #&i'{ #&i(! #&i(&", "#&i(* #&i(. #&i(2 #&i(6 #&i(: #&i(> #&i(B #&i(F"] (by decide +kernel) ++ paidGroupLast ["`d%K) #hF:5 #<>#9 #&i(J #&i(N #B7X?Q #@C74U `yWQ)", "#&i(R #<>.N #<>.R #<>.V #Qq4R #Qq4V B-%1 #hF:R", "#hF:V #}y@R n51- B,w1 #}y@V #}y@Z $6F1f #Qhff", "#&h7- $6NFV $6NFZ $L$LV $L$LZ $L$L_ $bVRZ $bVR_"] (by decide +kernel)
private def batch1:List P:=paidGroupLast ["$x,XZ $bN2j #h=Uf #&`-f $x,X_ $x,Xc ,NPg $x,Xg", ",NPk $x,Xk ,NPo $x,Xo B$Vk $x,Xs B$Vo $x,Xw", "B$Vs $x,X{ WV]o $x,Y! B$Ko %0__{ B$Ks %0_`!", "B$Kw %0_`& WVQs $x,N& ,`VV WVQw $x,N* ,`VZ"] (by decide +kernel) ++ paidGroupLast ["WVQ{ $x,N. ,`V_ WVR! $x,N2 ,`Vc WVR& $x,N6", ",`Vg WVR* $x,N: ,`Vk WVR. $x,N> ,`Vo WVR2", "$x,NB ,`Vs WVR6 $x,NF ,`Vw B$A6 %0_TB ,`V{", "B$A: %0_TF ,`W! B$A> %0_TJ ,`W& B$AB %0_TN"] (by decide +kernel)
private def batch2:List P:=paidGroupLast [",`W* B$AF $x,CN B5^& B$AJ $x,CR B5^* B$AN", "$x,CV B5^. B$AR $x,CZ B5^2 B$AV $x,C_ B5^6", "B$AZ $x,Cc B5^: B$A_ $x,Cg B5^> ,N0_ %0_Ic", "B5^B ,N0c %0_Ig B5^F ,N0g %0_Ik B5^J ,N0k"] (by decide +kernel) ++ paidGroupLast ["%0_Io B5^N ,N0o %0_Is B5^R ,N0s $x,8s WhdN", ",N0w $x,8w WhdR ,N0{ $x,8{ WhdV ,N1! $x,9!", "WhdZ ,N1& $x,9& Whd_ %0_?! Whdc %0_?& Whdg", "%0_?* Whdk %0_?. Whdo %0_?2 Whds %0_?6 Whdw"] (by decide +kernel)
private def batch3:List P:=paidGroupLast ["%0_?: Whd{ $x,.: n=jw $x,.> n=j{ $x,.B n=k!", "$x,.F n=k& $x,.J n=k* $x,.N n=k. $x,.R n=k2", "$x,.V n=k6 $x,.Z n=k: $x,._ n=k> $x,.c n=kB", "$bUzc #&pq> B,+A $L#to #&pqB $Yx/f~ #>#rOE W`DV"] (by decide +kernel) ++ paidGroupLast ["#&pqF"]
private def batches:List P:=batch0 ++ batch1 ++ batch2 ++ batch3
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 127 33 17 = true :=
  checkedWindows tiles 127 33 [8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 127) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7last).t+11) .two7last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7lastTop11

namespace Pr657PaidTwo7lastTop12

private abbrev P:=PaidBatch .two7last 12
private def batch0:List P:=paidGroupLast ["%AYdeM #E;jT5 )DO'E W`m: n5~B n5~F n5~J n5~N", "n5~R n5~V n5~Z n5~_ n5~c n5~g n5~k n5~o", "n5~s n5~w n5~{ n6!! n6!& n6!* n6!. n6!2", "n6!6 n6!: n6!> n6!B n6!F n6!J n6!N n6!R"] (by decide +kernel) ++ paidGroupLast ["n6!V #@o?V^ aG`t1 `7z45 #&ho= W`WA n6!Z #&i(V", "#&i(Z #<>.V #<>.Z #Qq4V n5G9 B-0= #Qq4Z #Qq4_", "#hF:Z #hF:_ #}y@Z n515 B,w9 #}y@_ #}y@c $6F1n", "#Qhfn #&h75 $6NF_ $6NFc $L$L_ $L$Lc $L$Lg $bVRc"] (by decide +kernel)
private def batch1:List P:=paidGroupLast ["$bVRg $x,Xc $x,Xg $x,Xk ,NPo $x,Xo ,NPs $x,Xs", ",NPw $x,Xw ,NP{ $x,X{ ,NQ! $x,Y! %0__{ %0_`!", "%0_`& $x,N& ,`VV $x,N* ,`VZ $x,N. ,`V_ $x,N2", ",`Vc $x,N6 ,`Vg $x,N: ,`Vk $x,N> ,`Vo $x,NB"] (by decide +kernel) ++ paidGroupLast [",`Vs $x,NF ,`Vw $x,NJ ,`V{ $x,NN ,`W! $x,NR", ",`W& $x,NV ,`W* $bV=V B5^& $bV=Z B5^* $bV=_", "B5^. $bV=c B5^2 $bV=g B5^6 $bV=k B5^: $bV=o", "B5^> $bV=s B5^B $bV=w B5^F $bV={ B5^J $bV>!"] (by decide +kernel)
private def batch2:List P:=paidGroupLast ["B5^N $bV>& B5^R $L$-& WhdN $L$-* WhdR $L$-.", "WhdV $L$-2 WhdZ $L$-6 Whd_ $L$-: Whdc $L$->", "Whdg $L$-B Whdk $L$-F Whdo $L$-J Whds $L$-N", "Whdw $L$-R Whd{ $6MyR n=jw $6MyV n=j{ $6MyZ"] (by decide +kernel) ++ paidGroupLast ["n=k! $6My_ n=k& $6Myc n=k* $6Myg n=k. $6Myk", "n=k2 $6Myo n=k6 $6Mys n=k: $6Myw n=k> $6My{", "n=kB #}xh{ #&pq> #}xi! #&pqB #z|PU- _(63E W`DV", "#&pqF"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1 ++ batch2
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 127 36 14 = true :=
  checkedWindows tiles 127 36 [8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 127) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7last).t+12) .two7last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7lastTop12

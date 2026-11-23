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

namespace Pr657PaidTwo7lastTop1

private abbrev P:=PaidBatch .two7last 1
private def batch0:List P:=paidGroupLast ["$5C7Q5 $l!X&b &%'p(~ &#3nH) %~ke]Q %~*:H) $$~klb f*X2A", "W`m: n5~B n5~F n5~J n5~N n5~R n5~V n5~Z", "n5~_ n5~c n5~g n5~k n5~o n5~s n5~w n5~{", "n6!! n6!& n6!* n6!. n6!2 n6!6 n6!: n6!>"] (by decide +kernel) ++ paidGroupLast ["n6!B n6!F n6!J #?3Ovn `7qq) `!>v= n6!N #|Z/,n", "#?Hz~1 n6!R n5;n _=iK~ B-;- n6!V #<>.J #}y@6", "#A~j5b #@XX51 a^$tj ,Ng2 ,VY_ #}y@: n,bf WV[n", "B$Uv B$b% ,N[* $bVR& ,N[. $bVR* #<4cQ n,KU"] (by decide +kernel)
private def batch1:List P:=paidGroupLast ["WVE^ WVh! $bVR. `!5ov #&V_% n,m{ $bVR2 #FaPX1", "#CF{+= d5qXr #&_sw $bVR6 #<4ys $bVR: #Qh!o $bVR>", "#Qh!s $bVRB WN%v Ax|~ ,Ew& #h=(o $bVRF #}p.k", "$bVRJ ,El! #}p.o $bVRN $64~A #h,gE #<,7j n#}n"] (by decide +kernel) ++ paidGroupLast ["Axfr Axq{ #}p.s $bVRR Axr! #}p.w $bVRV WMw{", "#h<zw $x,XR WMx! #h<z{ $x,XV n#}{ #h<{! $x,XZ", "n#~! #h<{& $x,X_ $KgyE #QV?A #&V&{ #h<{* $x,Xc", "#&V'! #h<{. $x,Xg #<,,{ #h<{2 $x,Xk #<,-! #h<{6"] (by decide +kernel)
private def batch2:List P:=paidGroupLast ["$x,Xo ,=@B #&Uy! #}p$2 $x,Xs #<+~{ #}p$6 $x,Xw", "#<,!! #}p$: $x,X{ ,=5B #<,!& #}p$> $x,Y! ,=5F", "#<,!* #h<p> %0__{ ,=5J #<,!. #h<pB %0_`! #}_@M", "#&MdI ,=5N #<,!2 #h<pF %0_`& #IeP_j j=q|= 'Oh!I"] (by decide +kernel) ++ paidGroupLast ["&*N#= $wozU Ap;J #<,!6 #h<pJ $x,N& ,`VV Ap;N", "#<,!: #h<pN $x,N* ,`VZ Ap;R #<,!> #h<pR $x,N.", ",`V_ Ap;V #&Un> #}ovN $x,N2 ,`Vc Ap0N #<+t:", "#}ovR $x,N6 ,`Vg Ap0R #<+t> #}ovV $x,N: ,`Vk"] (by decide +kernel)
private def batch3:List P:=paidGroupLast ["Ap0V #<+tB #}ovZ $x,N> ,`Vo Ap0Z #<+tF #}ov_", "$x,NB ,`Vs WE6V #<+tJ #}ovc $x,NF ,`Vw WE6Z", "#<+tN #h<ec %0_TB ,`V{ WE6_ #<+tR #h<eg %0_TF", ",`W! WE6c #<+tV #h<ek %0_TJ ,`W& WE6g #<+tZ"] (by decide +kernel) ++ paidGroupLast ["#h<eo %0_TN ,`W* WE+_ #Q^zV #h<es $x,CN B5^&", "c&,{Q &*Mj^ WE+c #<+iV #}oko $x,CR B5^* WE+g", "#<+iZ #}oks $x,CV B5^. WE+k #<+i_ #}okw $x,CZ", "B5^2 WE+o #<+ic #}ok{ $x,C_ B5^6 mx1k #<+ig"] (by decide +kernel)
private def batch4:List P:=paidGroupLast ["#}ol! $x,Cc B5^: mx1o #<+ik #}ol& $x,Cg B5^>", "mx1s #<+io #h<Z& %0_Ic B5^B WD}s #Q^ok #h<Z*", "%0_Ig B5^F WD}w #Q^oo #h<Z. %0_Ik B5^J WD}{", "#<+^o #}oa* %0_Io B5^N Aoar WD~! #<+^s #}oa."] (by decide +kernel) ++ paidGroupLast ["%0_Is B5^R $#nXef WD~& #<+^w #}oa2 $x,8s WhdN", "mx'! #<+^{ #}oa6 $x,8w WhdR mx'& #<+_! #}oa:", "$x,8{ WhdV WDs& #Q^d{ #}oa> $x,9! WhdZ WDs*", "#Q^e! #}oaB $x,9& Whd_ WDs. #Q^e& #h<OB %0_?!"] (by decide +kernel)
private def batch5:List P:=paidGroupLast ["Whdc WDs2 #<+S& #}oU> %0_?& Whdg &@+MU $Kg,A", "AoV) WDs6 #<+S* #}oUB %0_?* Whdk WDs: #<+S.", "#}oUF %0_?. Whdo WDh2 #Q^Y* #}oUJ %0_?2 Whds", "WDh6 #Q^Y. #}oUN %0_?6 Whdw WDh: #Q^Y2 #}oUR"] (by decide +kernel) ++ paidGroupLast ["%0_?: Whd{ WDh> #Q^Y6 #}oUV $x,.: n=jw WDhB", "#Q^Y: #}oUZ $x,.> n=j{ WDhF #<+H: $6D[V $x,.B", "n=k! AoVF #Q^N6 #}oJV %0_4> n=k& AoVJ #Q^N:", "#}oJZ %0_4B n=k* AoVN #Q^N> #}oJ_ %0_4F n=k."] (by decide +kernel)
private def batch6:List P:=paidGroupLast ["WD]J #Q^NB #}oJc %0_4J n=k2 WD]N #Q^NF #}oJg", "%0_4N n=k6 AoKN #h3TB #}oJk %0_4R n=k: AoKR", "#Q^CB $6DPg %0_4V n=k> AoKV #Q^CF $6DPk %0_4Z", "n=kB AoKZ #Q^CJ $6DPo $x,#Z #&pq> %:,'5z $Z0P9z"] (by decide +kernel) ++ paidGroupLast ["#>96#A _=_bz B#Q) n,!: %0_)V #&pqB %voA~~ #z|P>r", "_(5z- _(63E W`DV #&pqF"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4 ++ batch5 ++ batch6
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 127 3 47 = true :=
  checkedWindows tiles 127 3 [8, 8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 127) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7last).t+1) .two7last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7lastTop1

namespace Pr657PaidTwo7lastTop2

private abbrev P:=PaidBatch .two7last 2
private def batch0:List P:=paidGroupLast ["$nW@fz &%iEi^ &#_v_~ %~U2@A %}ES~M #DmY(A er%g~ B-Dw", "#&hy* #<>-2 #<>-6 #<>-: #<>-> #<>-B #<>-F #<>-J", "#<>-N #<>-R #<>-V #<>-Z #<>-_ #<>-c #<>-g #<>-k", "#<>-o #<>-s #<>-w #<>-{ #<>.! #<>.& #<>.* #<>.."] (by decide +kernel) ++ paidGroupLast ["#?u.Ab #?3P/z `7r*5 #<>.2 #<>.6 #<>.: #})7Cf #?_P'%", "n5;f W`5n #<>.> #hF:2 #hF:6 n,xr WVrz WV~)", "B$x1 ,VYV #}y@2 $L$L& ,Ng2 $L$L* #CG&4r #ARio9", "bA`?n #&_h^ n,bf WV[n B$b! $bVR& WVg{ $bVR*"] (by decide +kernel)
private def batch1:List P:=paidGroupLast ["#Q`$) #<4cQ #&_]Y WVh! $bVR. n,m{ $bVR2 `7hur", "#Q_v% #&_sw $bVR6 #<4ys $bVR: #<4yw $bVR> $%btGj", "#DA.pY #Qh!s $bVRB #h=(o $bVRF #}p.k $bVRJ #&V<z", "WN%~ #}p.o $bVRN ,El& #}p.s $bVRR ,El* #}p.w"] (by decide +kernel) ++ paidGroupLast ["$bVRV Axr& #h<zw $x,XR Axr* #h<z{ $x,XV #&V&v", "WMlz WMx& #h<{! $x,XZ $wpIU $64~U #Q_=v WMx*", "#h<{& $x,X_ WMx. #h<{* $x,Xc n#~* #h<{. $x,Xg", "n#~. #h<{2 $x,Xk #&V'* #h<{6 $x,Xo n#s* #}p$2"] (by decide +kernel)
private def batch2:List P:=paidGroupLast ["$x,Xs n#s. #}p$6 $x,Xw #&Uy* #}p$: $x,X{ &@,2j", "%0EDb #}_VY #&Uy. #}p$> $x,Y! #&Uy2 #h<p> %0__{", "#<,!. #h<pB %0_`! #<,!2 #h<pF %0_`& #<,!6 #h<pJ", "$x,N& ,`VV ,=5V #<,!: #h<pN $x,N* ,`VZ ,=5Z"] (by decide +kernel) ++ paidGroupLast ["#<,!> #h<pR $x,N. ,`V_ ,=5_ #&Un> #}ovN $x,N2", ",`Vc #<+t: #}ovR $x,N6 ,`Vg ,=*Z #<+t> #}ovV", "$x,N: ,`Vk ,=*_ #<+tB #}ovZ $x,N> ,`Vo (Ixgv", "&UVEb %Ex?z ,=*c #<+tF #}ov_ $x,NB ,`Vs ,=*g"] (by decide +kernel)
private def batch3:List P:=paidGroupLast ["#<+tJ #}ovc $x,NF ,`Vw ,=*k #<+tN #h<ec %0_TB", ",`V{ $'@jr- #E;>~M Ap0g #<+tR #h<eg %0_TF ,`W!", "Ap0k #<+tV #h<ek %0_TJ ,`W& Ap0o #<+tZ #h<eo", "%0_TN ,`W* c}=nj ,<|o #Q^zV #h<es $x,CN B5^&"] (by decide +kernel) ++ paidGroupLast [",<|s #<+iV #}oko $x,CR B5^* Ap%o #<+iZ #}oks", "$x,CV B5^. Ap%s #<+i_ #}okw $x,CZ B5^2 Ap%w", "#<+ic #}ok{ $x,C_ B5^6 Ap%{ #<+ig #}ol! $x,Cc", "B5^: Ap&! #<+ik #}ol& $x,Cg B5^> Ap&& #<+io"] (by decide +kernel)
private def batch4:List P:=paidGroupLast ["#h<Z& %0_Ic B5^B ,<r& #Q^ok #h<Z* %0_Ig B5^F", "Aox! #Q^oo #h<Z. %0_Ik B5^J Aox& #<+^o #}oa*", "%0_Io B5^N Aox* #<+^s #}oa. %0_Is B5^R Aox.", "#<+^w #}oa2 $x,8s WhdN Aox2 #<+^{ #}oa6 $x,8w"] (by decide +kernel) ++ paidGroupLast ["WhdR WD~. #<+_! #}oa: $x,8{ WhdV Aom. #Q^d{", "#}oa> $x,9! WhdZ Aom2 #Q^e! #}oaB $x,9& Whd_", "Aom6 #Q^e& #h<OB %0_?! Whdc Aom: #<+S& #}oU>", "%0_?& Whdg Aom> #<+S* #}oUB %0_?* Whdk AomB"] (by decide +kernel)
private def batch5:List P:=paidGroupLast ["#<+S. #}oUF %0_?. Whdo ,<[B #Q^Y* #}oUJ %0_?2", "Whds %[M%b $Kg7Y AobA ,<[F #Q^Y. #}oUN %0_?6", "Whdw ,<[J #Q^Y2 #}oUR %0_?: Whd{ AobF #Q^Y6", "#}oUV $x,.: n=jw AobJ #Q^Y: #}oUZ $x,.> n=j{"] (by decide +kernel) ++ paidGroupLast ["AobN #<+H: $6D[V $x,.B n=k! ,<PN #Q^N6 #}oJV", "%0_4> n=k& ,<PR #Q^N: #}oJZ %0_4B n=k* `y<mI", "#}^[U ,<PV #Q^N> #}oJ_ %0_4F n=k. ,<PZ #Q^NB", "#}oJc %0_4J n=k2 ,<P_ #Q^NF #}oJg %0_4N n=k6"] (by decide +kernel)
private def batch6:List P:=paidGroupLast ["#h3TB #}oJk %0_4R n=k: ,<EZ #Q^CB $6DPg %0_4V", "n=k> ,<E_ #Q^CF $6DPk %0_4Z n=kB ,<Ec #Q^CJ", "$6DPo $x,#Z #&pq> %:,'cM #>95u5 _=_Vn B#Ez B#Q)", "n,!: %0_)V #&pqB %9scVr #z|P3f #>#r9- #&hPF #&pqF"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4 ++ batch5 ++ batch6
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 127 6 44 = true :=
  checkedWindows tiles 127 6 [8, 8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 127) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7last).t+2) .two7last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7lastTop2

namespace Pr657PaidTwo7lastTop3

private abbrev P:=PaidBatch .two7last 3
private def batch0:List P:=paidGroupLast ["$nWpUM &%S#If &!{C5^ %}q[s~ $aNA8~ e[GWA (vF?r W`Jo", "#<>!! #Qq3* #Qq3. #Qq32 #Qq36 #Qq3: #Qq3> #Qq3B", "#Qq3F #Qq3J #Qq3N #Qq3R #Qq3V #Qq3Z #Qq3_ #Qq3c", "#Qq3g #Qq3k #Qq3o #Qq3s #Qq3w #Qq3{ #Qq4! #Qq4&"] (by decide +kernel) ++ paidGroupLast ["#Qq4* #|pbS~ #?_X0b `MFvv `!>k) #<=RY #Qq4. #Qq42", "W`*b B-$j #Qq46 #hF:2 #}y@. B$m% ,Ng* $6NF*", "#~NH9= c&=~~ asW?% ,Ng. $L$L& WVgv WVs! $L$L*", "#<4yb n,bf WV[n B$b! $bVR& `7i:- #Qh!^ B$b&"] (by decide +kernel)
private def batch1:List P:=paidGroupLast ["$bVR* WVh! $bVR. n,m{ $bVR2 #&_sw $bVR6 #&_s{", "$bVR: #<4yw $bVR> #GZj?) #D+a^1 dKNi^ n$M1 WV/Y", "#<4y{ $bVRB #Qh!w $bVRF #Qh!{ $bVRJ #h=(w $bVRN", "#&VH- Ax}- #}p.s $bVRR #}p.w $bVRV ,El. #h<zw"] (by decide +kernel) ++ paidGroupLast ["$x,XR `y>7U $Kp1- ,El2 #h<z{ $x,XV ,El6 #h<{!", "$x,XZ #&V2) Axg) Axr2 #h<{& $x,X_ Axr6 #h<{*", "$x,Xc WMx2 #h<{. $x,Xg WMx6 #h<{2 $x,Xk WMx:", "#h<{6 $x,Xo WMm2 #}p$2 $x,Xs WMm6 #}p$6 $x,Xw"] (by decide +kernel)
private def batch2:List P:=paidGroupLast ["#}gU1 #&Uy- WMm: #}p$: $x,X{ WMm> #}p$> $x,Y!", "n#s: #h<p> %0__{ n#s> #h<pB %0_`! n#sB #h<pF", "%0_`& #&Uy> #h<pJ $x,N& ,`VV #&UyB #h<pN $x,N*", ",`VZ #&UyF #h<pR $x,N. ,`V_ #}_Vv mxin n#hF"] (by decide +kernel) ++ paidGroupLast ["#}ovN $x,N2 ,`Vc #&UnB #}ovR $x,N6 ,`Vg #&UnF", "#}ovV $x,N: ,`Vk 'fE2A &*V!1 $b=#% #&UnJ #}ovZ", "$x,N> ,`Vo Ax/9 #&UnN #}ov_ $x,NB ,`Vs #&UnR", "#}ovc $x,NF ,`Vw #<+tN #h<ec %0_TB ,`V{ #<+tR"] (by decide +kernel)
private def batch3:List P:=paidGroupLast ["#h<eg %0_TF ,`W! $$~H,M gONYA #<+tV #h<ek %0_TJ", ",`W& ,=*w #<+tZ #h<eo %0_TN ,`W* #Q^zV #h<es", "$x,CN B5^& #<+iV #}oko $x,CR B5^* #<+iZ #}oks", "$x,CV B5^. #<+i_ #}okw $x,CZ B5^2 #<+ic #}ok{"] (by decide +kernel) ++ paidGroupLast ["$x,C_ B5^6 ,<}& #<+ig #}ol! $x,Cc B5^: ,<}*", "#<+ik #}ol& $x,Cg B5^> ,<}. #<+io #h<Z& %0_Ic", "B5^B (J#Or &*UiU #Q^ok #h<Z* %0_Ig B5^F #Q^oo", "#h<Z. %0_Ik B5^J #<+^o #}oa* %0_Io B5^N ,<r2"] (by decide +kernel)
private def batch4:List P:=paidGroupLast ["#<+^s #}oa. %0_Is B5^R ,<r6 #<+^w #}oa2 $x,8s", "WhdN ,<r: #<+^{ #}oa6 $x,8w WhdR ,<r> #<+_!", "#}oa: $x,8{ WhdV #Q^d{ #}oa> $x,9! WhdZ #Q^e!", "#}oaB $x,9& Whd_ #Q^e& #h<OB %0_?! Whdc ,<gB"] (by decide +kernel) ++ paidGroupLast ["#<+S& #}oU> %0_?& Whdg ,<gF #<+S* #}oUB %0_?*", "Whdk ,<gJ #<+S. #}oUF %0_?. Whdo #Q^Y* #}oUJ", "%0_?2 Whds #Q^Y. #}oUN %0_?6 Whdw #Q^Y2 #}oUR", "%0_?: Whd{ #Q^Y6 #}oUV $x,.: n=jw #Q^Y: #}oUZ"] (by decide +kernel)
private def batch5:List P:=paidGroupLast ["$x,.> n=j{ ,<[V #<+H: $6D[V $x,.B n=k! #Q^N6", "#}oJV %0_4> n=k& #Q^N: #}oJZ %0_4B n=k* #?tqD)", "`y=&b #Q^N> #}oJ_ %0_4F n=k. #Q^NB #}oJc %0_4J", "n=k2 #Q^NF #}oJg %0_4N n=k6 #Q^NJ #}oJk %0_4R"] (by decide +kernel) ++ paidGroupLast ["n=k: #<+=J $6DPg %0_4V n=k> #<+=N $6DPk %0_4Z", "n=kB WDhn #<+=R $6DPo $x,#Z #&pq> %:,/Uz #>96#A", "_=_bz B#Q) B#]5 WUyB %0_)V #&pqB %9scb~ #z|P>r", "_(5z- #&hPF #&pqF"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4 ++ batch5
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 127 9 41 = true :=
  checkedWindows tiles 127 9 [8, 8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 127) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7last).t+3) .two7last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7lastTop3

namespace Pr657PaidTwo7lastTop4

private abbrev P:=PaidBatch .two7last 4
private def batch0:List P:=paidGroupLast ["&'sE=Q &$.!09 %~U2KM %@I}In f*Oo9 (vF4f (`q.n W`Jo", "#<>!! #Qq3* #Qq3. #Qq32 #Qq36 #Qq3: #Qq3> #Qq3B", "#Qq3F #Qq3J #Qq3N #Qq3R #Qq3V #Qq3Z #Qq3_ #Qq3c", "#Qq3g #Qq3k #Qq3o #Qq3s #Qq3w #Qq3{ #Qq4! #Qq4&"] (by decide +kernel) ++ paidGroupLast ["#{vY/j `7q|) #Qq4* #Qq4. #Qq42 #AiGC% #@C.Z1 #?I%|f", "#hF:. W_|Y $6NF! #QhNz #&`7~ $6NF& WV~) ,Ng*", "$6NF* ,Ng. $L$L& ,Ng2 $L$L* ,N[* $bVR& #Qh-j", "#&_sn WV[r B$b& $bVR* B$b* $bVR. $!HQ#) #A=6tY"] (by decide +kernel)
private def batch1:List P:=paidGroupLast ["WVh& $bVR2 n,n! $bVR6 #}hF= #Qgtb #&_]f n,n&", "$bVR: #&_t! $bVR> #&_t& $bVRB #<4z! $bVRF #<4z&", "$bVRJ #Qh#! $bVRN $bEX= #h4|9 #<,e= #Qh#& $bVRR", "#h=)! $bVRV #Qgu! $x,XR #h<z{ $x,XV #h<{! $x,XZ"] (by decide +kernel) ++ paidGroupLast ["#KCH=U #FK.9f f*6)f #h<{& $x,X_ ,El> #h<{* $x,Xc", "%[U|E $bEBA #h4f= ,ElB #h<{. $x,Xg Axr> #h<{2", "$x,Xk AxrB #h<{6 $x,Xo ,EaB #}p$2 $x,Xs ,EaF", "#}p$6 $x,Xw bAW+z %[UqM AxgB #}p$: $x,X{ AxgF"] (by decide +kernel)
private def batch2:List P:=paidGroupLast ["#}p$> $x,Y! AxgJ #h<p> %0__{ WMmF #h<pB %0_`!", "WMmJ #h<pF %0_`& WMmN #h<pJ $x,N& ,`VV WMmR", "#h<pN $x,N* ,`VZ n#sN #h<pR $x,N. ,`V_ WMbN", "#}ovN $x,N2 ,`Vc WMbR #}ovR $x,N6 ,`Vg WMbV"] (by decide +kernel) ++ paidGroupLast ["#}ovV $x,N: ,`Vk n#hR #}ovZ $x,N> ,`Vo n#hV", "#}ov_ $x,NB ,`Vs n#hZ #}ovc $x,NF ,`Vw n#h_", "#h<ec %0_TB ,`V{ $64i9 #<+tU n#hc #h<eg %0_TF", ",`W! #&Un_ #h<ek %0_TJ ,`W& #&Unc #h<eo %0_TN"] (by decide +kernel)
private def batch3:List P:=paidGroupLast [",`W* #&Ung #h<es $x,CN B5^& n#]g #}oko $x,CR", "B5^* n#]k #}oks $x,CV B5^. #&Ucg #}okw $x,CZ", "B5^2 #&Uck #}ok{ $x,C_ B5^6 #&Uco #}ol! $x,Cc", "B5^: %ExKY #h,;I #&Ucs #}ol& $x,Cg B5^> Ax$b"] (by decide +kernel) ++ paidGroupLast ["#&Ucw #h<Z& %0_Ic B5^B #&Uc{ #h<Z* %0_Ig B5^F", "#<+iw #h<Z. %0_Ik B5^J #&UWw #}oa* %0_Io B5^N", "#&UW{ #}oa. %0_Is B5^R c&5(f %r#cn #&UX! #}oa2", "$x,8s WhdN #&UX& #}oa6 $x,8w WhdR #<+_! #}oa:"] (by decide +kernel)
private def batch4:List P:=paidGroupLast ["$x,8{ WhdV #<+_& #}oa> $x,9! WhdZ #<+_* #}oaB", "$x,9& Whd_ #<+_. #h<OB %0_?! Whdc #&UM. #}oU>", "%0_?& Whdg #&UM2 #}oUB %0_?* Whdk #&UM6 #}oUF", "%0_?. Whdo #<+S2 #}oUJ %0_?2 Whds #<+S6 #}oUN"] (by decide +kernel) ++ paidGroupLast ["%0_?6 Whdw #<+S: #}oUR %0_?: Whd{ #<+S> #}oUV", "$x,.: n=jw #<+SB #}oUZ $x,.> n=j{ #&UBB $6D[V", "$x,.B n=k! #&UBF #}oJV %0_4> n=k& #&UBJ #}oJZ", "%0_4B n=k* Awa9 #&UBN #}oJ_ %0_4F n=k. #h+lz"] (by decide +kernel)
private def batch5:List P:=paidGroupLast ["#h3`I #&UBR #}oJc %0_4J n=k2 #<+HN #}oJg %0_4N", "n=k6 #<+HR #}oJk %0_4R n=k: #>zhfn #&U7R $6DPg", "%0_4V n=k> #&U7V $6DPk %0_4Z n=kB #&U7Z $6DPo", "$x,#Z #&pq> $Z0PE) #>9=sn _=_n) B#]5 WUyB %0_)V"] (by decide +kernel) ++ paidGroupLast ["#&pqB %9scb~ #z|P>r _(5z- #&hPF #&pqF"]
private def batches:List P:=batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4 ++ batch5
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 127 12 38 = true :=
  checkedWindows tiles 127 12 [8, 8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 127) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7last).t+4) .two7last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7lastTop4

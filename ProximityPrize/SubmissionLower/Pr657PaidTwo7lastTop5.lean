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

namespace Pr657PaidTwo7lastTop5

private abbrev P:=PaidBatch .two7last 5
private def batch0:List P:=paidGroupLast ["&'GLjU &#IKcv %}q]!- $$i8.% e[GWA (`q.n W`Jo #<>!!", "#Qq3* #Qq3. #Qq32 #Qq36 #Qq3: #Qq3> #Qq3B #Qq3F", "#Qq3J #Qq3N #Qq3R #Qq3V #Qq3Z #Qq3_ #Qq3c #Qq3g", "#Qq3k #Qq3o #Qq3s #Qq3w #Qq3{ #Qq4! #Qq4& #Qq4*"] (by decide +kernel) ++ paidGroupLast ["#A=?B9 #@-aRj `yO;~ #Qq4. `!>k- _S>F^ #Qq42 B-$j", "#hF:. #hF:2 B,kY $6NF& $6NF* WV~- ,Ng. $L$L&", ",Ng2 $L$L* $bVR& #~zPg^ #A'im5 WVg~ B$b& $bVR*", "#}pOv #<5'v n,mz B$b* $bVR. B$b. $bVR2 WVh*"] (by decide +kernel)
private def batch1:List P:=paidGroupLast ["$bVR6 WVh. $bVR: n,n* $bVR> $KpiM #}p9r #<4nr", "n,n. $bVRB #&_t* $bVRF #&_t. $bVRJ #&_t2 $bVRN", "#<4z. $bVRR #<4z2 $bVRV #<4o* $x,XR #<4o. $x,XV", "#HT{2f #DVj.f db%)1 $wxjQ #}h0M #<,eM #<4o2 $x,XZ"] (by decide +kernel) ++ paidGroupLast ["#Qgu. $x,X_ #Qgu2 $x,Xc #h<{. $x,Xg asVpI $wx_U", "#h<{2 $x,Xk #h<{6 $x,Xo #}p$2 $x,Xs #}p$6 $x,Xw", "#}p$: $x,X{ ,EaN #}p$> $x,Y! ,EaR #h<p> %0__{", ",EaV #h<pB %0_`! ,EaZ #h<pF %0_`& AxgV #h<pJ"] (by decide +kernel)
private def batch2:List P:=paidGroupLast ["$x,N& ,`VV AxgZ #h<pN $x,N* ,`VZ Axg_ #h<pR", "$x,N. ,`V_ ,EU_ #}ovN $x,N2 ,`Vc #}gab n#sY", "Ax[Z #}ovR $x,N6 ,`Vg Ax[_ #}ovV $x,N: ,`Vk", "Ax[c #}ovZ $x,N> ,`Vo Ax[g #}ov_ $x,NB ,`Vs"] (by decide +kernel) ++ paidGroupLast ["WMbc #}ovc $x,NF ,`Vw WMbg #h<ec %0_TB ,`V{", "WMbk #h<eg %0_TF ,`W! WMbo #h<ek %0_TJ ,`W&", "$bD~v #<,!j WMbs #h<eo %0_TN ,`W* n#ho #h<es", "$x,CN B5^& WMVo #}oko $x,CR B5^* WMVs #}oks"] (by decide +kernel)
private def batch3:List P:=paidGroupLast ["$x,CV B5^. (J#r% &U_On %0M9% WMVw #}okw $x,CZ", "B5^2 WMV{ #}ok{ $x,C_ B5^6 n#]w #}ol! $x,Cc", "B5^: n#]{ #}ol& $x,Cg B5^> n#^! #h<Z& %0_Ic", "B5^B n#^& #h<Z* %0_Ig B5^F n#^* #h<Z. %0_Ik"] (by decide +kernel) ++ paidGroupLast ["B5^J WML* #}oa* %0_Io B5^N n#R& #}oa. %0_Is", "B5^R n#R* #}oa2 $x,8s WhdN n#R. #}oa6 $x,8w", "WhdR n#R2 #}oa: $x,8{ WhdV n#R6 #}oa> $x,9!", "WhdZ n#R: #}oaB $x,9& Whd_ #&UX6 #h<OB %0_?!"] (by decide +kernel)
private def batch4:List P:=paidGroupLast ["Whdc n#G6 #}oU> %0_?& Whdg n#G: #}oUB %0_?*", "Whdk c&5)) &*Uu5 n#G> #}oUF %0_?. Whdo n#GB", "#}oUJ %0_?2 Whds n#GF #}oUN %0_?6 Whdw #&UMB", "#}oUR %0_?: Whd{ #&UMF #}oUV $x,.: n=jw #&UMJ"] (by decide +kernel) ++ paidGroupLast ["#}oUZ $x,.> n=j{ n#<J $6D[V $x,.B n=k! n#<N", "#}oJV %0_4> n=k& n#<R #}oJZ %0_4B n=k* n#<V", "#}oJ_ %0_4F n=k. n#<Z #}oJc %0_4J n=k2 AwlM", "n#<_ #}oJg %0_4N n=k6 n#<c #}oJk %0_4R n=k:"] (by decide +kernel)
private def batch5:List P:=paidGroupLast ["n#1Z $6DPg %0_4V n=k> n#1_ $6DPk %0_4Z n=kB", "n#1c $6DPo $x,#Z #&pq> $Z0PP5 #>9=~z _=_y5 B#hA", "B#sJ %0_)V #&pqB %9scn- #>#r!r _(5z- #&hPF #&pqF"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4 ++ batch5
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 127 15 35 = true :=
  checkedWindows tiles 127 15 [8, 8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 127) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7last).t+5) .two7last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7lastTop5

namespace Pr657PaidTwo7lastTop6

private abbrev P:=PaidBatch .two7last 6
private def batch0:List P:=paidGroupLast ["&&d!(U &!ev9U %}/~mI #DW&t= (vF?r W`Jo #<>!! #Qq3*", "#Qq3. #Qq32 #Qq36 #Qq3: #Qq3> #Qq3B #Qq3F #Qq3J", "#Qq3N #Qq3R #Qq3V #Qq3Z #Qq3_ #Qq3c #Qq3g #Qq3k", "#Qq3o #Qq3s #Qq3w #Qq3{ #Qq4! #A=GKv #?u.d% `MG;5"] (by decide +kernel) ++ paidGroupLast ["#Qq4& #Qq4* #Qq4. #&hLf W`5j #Qq42 #Qq46 #hF:2", "#}y@. n-=9 W_|b #}y@2 $6NF. #~e&`9 bmi=Q a^-Bv", "#h=a- #&`8- WV~1 $6NF2 $L$L. $bVR* ,N[2 $bVR.", ",N[6 $bVR2 B$b2 $bVR6 #<5(% n,n) B$b6 $bVR:"] (by decide +kernel)
private def batch1:List P:=paidGroupLast ["B$b: $bVR> WVh6 $bVRB WVh: $bVRF n,n6 $bVRJ", "n,n: $bVRN #<4o% WVF% #&_t6 $bVRR #&_t: $bVRV", "#Faam% #CG.?1 cgyJ^ n,c: $x,XR #&_i6 $x,XV #&_i:", "$x,XZ a1y^U #}h;^ #Qgj% n,A% #&_i> $x,X_ #<4o:"] (by decide +kernel) ++ paidGroupLast ["$x,Xc #<4o> $x,Xg #<4oB $x,Xk #Qgu> $x,Xo #QguB", "$x,Xs #QguF $x,Xw #h<{B $x,X{ #h<{F $x,Y! #h<p>", "%0__{ #Q_`f WN&b #h<pB %0_`! #h<pF %0_`& #h<pJ", "$x,N& ,`VV ,Eac #h<pN $x,N* ,`VZ ,Eag #h<pR"] (by decide +kernel)
private def batch2:List P:=paidGroupLast ["$x,N. ,`V_ #}ovN $x,N2 ,`Vc #}ovR $x,N6 ,`Vg", ",EUg #}ovV $x,N: ,`Vk #h4Zr WMmj ,EUk #}ovZ", "$x,N> ,`Vo ,EUo #}ov_ $x,NB ,`Vs ,EUs #}ovc", "$x,NF ,`Vw ':E%9 %[Ur) $Kp&~ Ax[o #h<ec %0_TB"] (by decide +kernel) ++ paidGroupLast [",`V{ Ax[s #h<eg %0_TF ,`W! Ax[w #h<ek %0_TJ", ",`W& Ax[{ #h<eo %0_TN ,`W* Ax]! #h<es $x,CN", "B5^& AxPw #}oko $x,CR B5^* AxP{ #}oks $x,CV", "B5^. AxQ! #}okw $x,CZ B5^2 AxQ& #}ok{ $x,C_"] (by decide +kernel)
private def batch3:List P:=paidGroupLast ["B5^6 AxQ* #}ol! $x,Cc B5^: AxQ. #}ol& $x,Cg", "B5^> WMW* #h<Z& %0_Ic B5^B WMW. #h<Z* %0_Ig", "B5^F WMW2 #h<Z. %0_Ik B5^J bAVsv %[U[I AxF2", "#}oa* %0_Io B5^N AxF6 #}oa. %0_Is B5^R WML2"] (by decide +kernel) ++ paidGroupLast ["#}oa2 $x,8s WhdN WML6 #}oa6 $x,8w WhdR WML:", "#}oa: $x,8{ WhdV WML> #}oa> $x,9! WhdZ WMLB", "#}oaB $x,9& Whd_ WMLF #h<OB %0_?! Whdc Ax;F", "#}oU> %0_?& Whdg WMAB #}oUB %0_?* Whdk WMAF"] (by decide +kernel)
private def batch4:List P:=paidGroupLast ["#}oUF %0_?. Whdo WMAJ #}oUJ %0_?2 Whds WMAN", "#}oUN %0_?6 Whdw WMAR #}oUR %0_?: Whd{ WMAV", "#}oUV $x,.: n=jw $wwob #}g5^ WMAZ #}oUZ $x,.>", "n=j{ WM6R $6D[V $x,.B n=k! WM6V #}oJV %0_4>"] (by decide +kernel) ++ paidGroupLast ["n=k& WM6Z #}oJZ %0_4B n=k* WM6_ #}oJ_ %0_4F", "n=k. WM6c #}oJc %0_4J n=k2 WM6g #}oJg %0_4N", "n=k6 WM6k #}oJk %0_4R n=k: Ax%k $6DPg %0_4V", "n=k> WM+g $6DPk %0_4Z n=kB WM+k $6DPo $x,#Z"] (by decide +kernel)
private def batch5:List P:=paidGroupLast ["#&pq> $Z0P[A #>9>-) _=`'A B#sM ,MmR %0_)V #&pqB", "$Yx'Q- #>#r!r _(5z- #&hPF #&pqF"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4 ++ batch5
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 127 18 32 = true :=
  checkedWindows tiles 127 18 [8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 127) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7last).t+6) .two7last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7lastTop6

namespace Pr657PaidTwo7lastTop7

private abbrev P:=PaidBatch .two7last 7
private def batch0:List P:=paidGroupLast ["&%ivJ1 &!$Bm5 $azI[) eqziE ).yPv (`q9~ B-Dw #&hy*", "#<>-2 #<>-6 #<>-: #<>-> #<>-B #<>-F #<>-J #<>-N", "#<>-R #<>-V #<>-Z #<>-_ #<>-c #<>-g #<>-k #<>-o", "#<>-s #<>-w #<>-{ #<>.! #<>.& #<>.* #<>.. #<>.2"] (by decide +kernel) ++ paidGroupLast ["#<>.6 #<>.: #?I&A- `!>v= #<>.> #&hLn W`5r #Qq4:", "#hF:6 #~#HMI bAi%) a2%B- #hF:: #}y@6 n-=A B,kf", "#}y@: $6NF6 #<5I9 n-2= $L$L2 $L$L6 $bVR2 $bVR6", ",N[> $bVR: ,N[B $bVR> #&`!5 B$V5 B$b> $bVRB"] (by decide +kernel)
private def batch1:List P:=paidGroupLast ["B$bB $bVRF WVh> $bVRJ #EQ%}I #BcWr^ bmi'f WVhB", "$bVRN a2$h) $6EV5 WVhF $bVRR #&_i1 B$@1 n,nB", "$bVRV WV]B $x,XR n,c> $x,XV n,cB $x,XZ n,cF", "$x,X_ #&_iB $x,Xc #&_iF $x,Xg #&_iJ $x,Xk #&_iN"] (by decide +kernel) ++ paidGroupLast ["$x,Xo #<4X5 WV05 #<4oJ $x,Xs #<4oN $x,Xw #<4oR", "$x,X{ #QguN $x,Y! #<4dN %0__{ #<4dR %0_`! #Q_kv", "n,+9 #QgjN %0_`& #QgjR $x,N& ,`VV #QgjV $x,N*", ",`VZ #QgjZ $x,N. ,`V_ &*_M1 $bEN% #h4q~ #h<pV"] (by decide +kernel)
private def batch2:List P:=paidGroupLast ["$x,N2 ,`Vc #h<pZ $x,N6 ,`Vg #h<p_ $x,N: ,`Vk", "B#ZA #h<pc $x,N> ,`Vo #h<pg $x,NB ,`Vs #}ovc", "$x,NF ,`Vw #h<ec %0_TB ,`V{ #h<eg %0_TF ,`W!", ",EV! #h<ek %0_TJ ,`W& ,EV& #h<eo %0_TN ,`W*"] (by decide +kernel) ++ paidGroupLast [",EV* #h<es $x,CN B5^& #}oko $x,CR B5^* 'Ox6U", "&*_7I $Kp'9 ,EK& #}oks $x,CV B5^. ,EK* #}okw", "$x,CZ B5^2 ,EK. #}ok{ $x,C_ B5^6 ,EK2 #}ol!", "$x,Cc B5^: ,EK6 #}ol& $x,Cg B5^> ,EK: #h<Z&"] (by decide +kernel)
private def batch3:List P:=paidGroupLast ["%0_Ic B5^B AxQ6 #h<Z* %0_Ig B5^F AxQ: #h<Z.", "%0_Ik B5^J ,E@: #}oa* %0_Io B5^N ,E@> #}oa.", "%0_Is B5^R ,E@B #}oa2 $x,8s WhdN AxF> #}oa6", "$x,8w WhdR AxFB #}oa: $x,8{ WhdV AxFF #}oa>"] (by decide +kernel) ++ paidGroupLast ["$x,9! WhdZ AxFJ #}oaB $x,9& Whd_ AxFN #h<OB", "%0_?! Whdc ,E5N #}oU> %0_?& Whdg ,E5R #}oUB", "%0_?* Whdk Ax;N #}oUF %0_?. Whdo Ax;R #}oUJ", "%0_?2 Whds Ax;V #}oUN %0_?6 Whdw Ax;Z #}oUR"] (by decide +kernel)
private def batch4:List P:=paidGroupLast ["%0_?: Whd{ Ax;_ #}oUV $x,.: n=jw Ax;c #}oUZ", "$x,.> n=j{ Ax0Z $6D[V $x,.B n=k! Ax0_ #}oJV", "%0_4> n=k& Ax0c #}oJZ %0_4B n=k* Ax0g #}oJ_", "%0_4F n=k. Ax0k #}oJc %0_4J n=k2 Ax0o #}oJg"] (by decide +kernel) ++ paidGroupLast ["%0_4N n=k6 Ax0s #}oJk %0_4R n=k: ,D|s $6DPg", "%0_4V n=k> ,D|w $6DPk %0_4Z n=kB ,D|{ $6DPo", "$x,#Z #&pq> $Z0PrY #>9>CA B#sM B#~Y %0_)V #&pqB", "%9sklf #>#r9- #&hPF #&pqF"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 127 21 29 = true :=
  checkedWindows tiles 127 21 [8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 127) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7last).t+7) .two7last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7lastTop7

namespace Pr657PaidTwo7lastTop8

private abbrev P:=PaidBatch .two7last 8
private def batch0:List P:=paidGroupLast ["&$omlj %~*2IM $$i8DA )Z$s~ (vFK% B-Dw #&hy* #<>-2", "#<>-6 #<>-: #<>-> #<>-B #<>-F #<>-J #<>-N #<>-R", "#<>-V #<>-Z #<>-_ #<>-c #<>-g #<>-k #<>-o #<>-s", "#<>-w #<>-{ #<>.! #<>.& #<>.* #<>.. #<>.2 #<>.6"] (by decide +kernel) ++ paidGroupLast ["#<>.: #~#PW% #?u.d5 `MG;E _iqcr #<>.> #<>.B #Qq4>", "#Qq4B W`*r #}y@6 #}y@: #}y@> #&h6n B,kn $6NF:", "$6NF> #}prA #QhZE n-2E $L$L: $L$L> $L$LB $bVR>", "#DVzAr #AiGNf bAhl9 ,N[F $bVRB `MFU5 #QhDA ,N[J"] (by decide +kernel)
private def batch1:List P:=paidGroupLast ["$bVRF ,N[N $bVRJ B$bJ $bVRN B$bN $bVRR WVhJ", "$bVRV B$VJ $x,XR B$VN $x,XV #<4zA WVQA WV]J", "$x,XZ WV]N $x,X_ WV]R $x,Xc n,cN $x,Xg n,cR", "$x,Xk n,cV $x,Xo #&_iR $x,Xs #<4dE WV;E #&_iV"] (by decide +kernel) ++ paidGroupLast ["$x,Xw #&_iZ $x,X{ %F$;- $bMWM #h<{I #&_i_ $x,Y!", "#&_^V %0__{ #&_^Z %0_`! #&_^_ %0_`& #<4dZ $x,N&", ",`VV #<4d_ $x,N* ,`VZ #<4dc $x,N. ,`V_ #<4dg", "$x,N2 ,`Vc #Qgjc $x,N6 ,`Vg #Qgjg $x,N: ,`Vk"] (by decide +kernel)
private def batch2:List P:=paidGroupLast ["#Qgjk $x,N> ,`Vo #Qgjo $x,NB ,`Vs &@4_I $wx`=", "#h4r5 #h<pk $x,NF ,`Vw #Qg_k %0_TB ,`V{ #Qg_o", "%0_TF ,`W! B#ZU #Qg_s %0_TJ ,`W& #Qg_w %0_TN", ",`W* #h<es $x,CN B5^& #h<ew $x,CR B5^* #h<e{"] (by decide +kernel) ++ paidGroupLast ["$x,CV B5^. #}okw $x,CZ B5^2 #}ok{ $x,C_ B5^6", "#}ol! $x,Cc B5^: #}ol& $x,Cg B5^> #h<Z& %0_Ic", "B5^B ,EK> #h<Z* %0_Ig B5^F ,EKB #h<Z. %0_Ik", "B5^J #}oa* %0_Io B5^N #}oa. %0_Is B5^R #}oa2"] (by decide +kernel)
private def batch3:List P:=paidGroupLast ["$x,8s WhdN #}oa6 $x,8w WhdR ,E@J #}oa: $x,8{", "WhdV ,E@N #}oa> $x,9! WhdZ ,E@R #}oaB $x,9&", "Whd_ ,E@V #h<OB %0_?! Whdc #}oU> %0_?& Whdg", "#}oUB %0_?* Whdk #}oUF %0_?. Whdo #}oUJ %0_?2"] (by decide +kernel) ++ paidGroupLast ["Whds #}oUN %0_?6 Whdw #}oUR %0_?: Whd{ #}oUV", "$x,.: n=jw #}oUZ $x,.> n=j{ #}oU_ $x,.B n=k!", "#h<D_ %0_4> n=k& #h<Dc %0_4B n=k* #h<Dg %0_4F", "n=k. #h<Dk %0_4J n=k2 #h<Do %0_4N n=k6 #h<Ds"] (by decide +kernel)
private def batch4:List P:=paidGroupLast ["%0_4R n=k: #h<Dw %0_4V n=k> #h<D{ %0_4Z n=kB", "#h<E! $x,#Z #&pq> #{4zT5 _=`2M B#~Y B+r) $x,#_", "#&pqB $Yx/Of #>#r9- #&hPF #&pqF"] (by decide +kernel)
private def batches:List P:=batch0 ++ batch1 ++ batch2 ++ batch3 ++ batch4
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 127 24 26 = true :=
  checkedWindows tiles 127 24 [8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 127) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7last).t+8) .two7last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7lastTop8

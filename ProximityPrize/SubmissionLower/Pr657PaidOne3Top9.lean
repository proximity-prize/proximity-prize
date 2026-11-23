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

namespace Pr657PaidOne3Top9

private abbrev P:=PaidBatch .one3 9
private def batch0:List P:=paidGroup ["&11~T` &12aAO &.Yq]d %LTF.S #}e25S amtpl $!Buwt #A7S''","%|qM?? `sc[` #x'Jl #K|3p }syt <8Pt <wZ~,d%:>CCuY@ $`8]P?","#CAJ!' <wZ~,d%:>CCuYD <wZ~,d%:>CCuYH ;W+pIrAzLrB&x$","<wZ~,d%:>CCuYL ;W+pIrAzLrB&x( <wZ~,d%:>CCuYP $r7ch",":rh1pnVHi2Uz!H ;l.(|Y20F~jF.( <wZ~,d%:>CCuYT ;,>8rZb}/u`4T$","<&ZgSrXF*oV-ye =!%p(F<Ub7qdz( `^0)[ #bPuh","#6H^l Qk5l :Hk05jStLvm@GT ;Br?tGnST:e+Pi <>+H,.![k`BrhD","=:Mo:_%Au5s:^L :_ICi[H]i3d)dy ;YHFv4z*x}nC&D","<UX)aFHrNP/YV$ =RvnLvk.+3tnAq :u(W?M=F(-UNKL ;p|Mx!(_@Bs:#,","<n(h8_p+2@yADa =lAm`1Rw>nr#MD :2/f6j8y-Byt0u ;-dks?2/CGL7hq","<*RTyl45e(|QTe =(UHmx9@s1f)3@ >'jlrI;cQlsV1i :FumF3whSt.,;u",";CC!I1&u_bB~(8 <A)[{X?j+l(j*@ =@&*E3`VV_MLI, >@5l'b$Neju,s0","a,0B3 $r7Ll :[^tUZXVzhCb|i ;Y!5}!x^{[5Eli <W]c}EK@P1-a'(","=WRhzL)m:O:47i >X^k9yj:xhv`VT 9tN}6!!`Tq:V?m"] ++ paidGroup [":qF{f%:FD;Tx*i ;o^IRqmG9v,/,0 <o3k!2Vttt6xXa =p#IQeP%{@&y&H",">r)jL4R'.fx6:y :+C_)QQI<~?{J} ;)0%uKy5klg05i <(<^)cb0U3!uHT","=(gr#|cK<9;oUH >*P+)}w;_0p`r( ?-Qi_L:pBCuHFL #6H<h &bYk",":?8?z%$3%.EBV0 ;=v-'sZ%4`|fv] <=xq]TUvqLv^ey","=?=y%io!`|E*+$ >A}i_9@QA~]G`e ?Ezhqe#[UAv|*q &bYo :S,~mTRyjxFF,L",";R_47=;q[40|$] <SW(3FJ`0Fi&LL =Ur#'UzV(AI~'i",">YMJ6Qgh%oI/ND ?_Eh&|iGi?xQl8 &bYs :g~`a(%cR(Kk7] ;hG;Fdza%(FTeP","<j6;g8?HKa_liq =mH*)C)-L'S8YD >q{+kk0}f`5t=$","?wng97Q3|=z(O] <7`o :{sASWTL:5Q2Bm ;}0BV.[OKXWjpP =!rO=*41g{UU)8",">&|1+04apj]P.} ?,JjC&W6IP![+a @39fKO9}2;{[4$","<7`s ;2h#G+'6#!R5v, <4vIfU=>rLnCSD =8Pcpy(x&8L>E] >=R8,z@88/bG+e","?CxJx>~L-@lBw@ @Kbe^h!iEvxn?T <7`w",";F[b:ZU|h/WZ$< <I_Pu||.;~!X_D =N/wFjzaB2>d-0 >T)?.gKl[rk_^@","?[H,OWGbn1X*e} A*.#I<I%93qmk4 Qjfs ;ZPC..(fO<^!/L","<_GX(F]zbr82B8 =dl-z[oI^L5LIT >k]F0SWC$7pUZ( ?suk'pnxQ!DoS]","@}Ud&:P@lr|!La _MHl` Qjfw ;oE$~^WO8)_%bi"] ++ paidGroup ["<t0`7n>j,EIGM8 =zJAPMd2yg,5fy ?%3M2@cwGzyn/a @.EK],814p1VB<","A8~c8R9-!p}U1( Qjf{ <&9cr1*8}6dImy =+vgG7}XRvZ]X8",">3)U'?Wy8$!|&@ ?;gT4-oMm?~e,H @Es-4D_Fv?vzX( AQIbJj~v5o!+rL Qjg!","<:.DeaY!eCiny, =@_nV__Gyjq6<, >HeiZ1LbSzrCjq","?R=[5w{%4&*|_$ @^Bki^(]Y0cbFe AX&w`19(weYX?8"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 27 27 = true :=
  checkedWindows tiles 136 27 [8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+9) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top9

namespace Pr657PaidOne3Top10

private abbrev P:=PaidBatch .one3 10
private def batch0:List P:=paidGroup ["&12PD3 &08Wd+ &-J5n; #R@C:7 $^.o9| #BsB7' #AM16S aWAHd","_yRCl $#~dfx #B]lb' h@hp <8Pt %|EM'# >+`FmB]CkRo2{D",">+`FmB]CkRo2{H","}scl <8:l <`5,}CXP)<)@7@ >+`FmB]CkRo2{L <`5,}CXP)<)@7D",">+`FmB]CkRo2{P `2'z` #6Hil",";:Gx^sjK,)*%Gy <`5,}CXP)<)@7H >+`FmB]CkRo2{T ;:Gx^sjK,)*%G}","<`5,}CXP)<)@7L >+`FmB]CkRo2{X ;:Gx^sjK,)*%H$ <`5,}CXP)<)@7P",">+`FmB]CkRo2{] :PzzGUzCq/!~-] ;KouV&F(Dnl:S$ <`5,}CXP)<)@7T",">+`FmB]CkRo2{a :gY0{Go-/HvgJ$ ;cE|WpQ[iSuR(] <`Fu!x834F$sG8",">+`FmB]CkRo2{e :}8DQ9csJcmOgH ;yz&Y]^30vzI%D <wtUW3_Hu6nZ5u",">+`FmB]CkRo2{i `^/{[ #bPjh }sAh","<7vh :9U5*hW,M?Acm4 ;5tX(+W[f}d9&m <3P-[IigT]&aV} =2D7/L(_X'ZB$T",">2M>!uIURIa{]4 :N><:28xt3W<P( ;KRlZzLE%wU^k@","<J'4^6u=z!+WSe =IqudeNu;uG)p4 >Jv=502AfGcQ@X 9g<x'coRSKso!T",":d'CIXwh=diQ[( ;b2#1lA.A4LG*e <aZ;`$#r@e4p)@ =bAV;}v-|f3n^q"] ++ paidGroup [">dA<GGx-yEe($} 9{1Xx6A<;Xy6-e :xmJY#XVdX!+>y ;wn6e^5t]NC0G,","<x1Ban/Hf*9g&( =yo7q9?C`U}ULP >|j;Y``w/CfZfD :2&:kfq&#f~Z8u",";0UQiJ:F.,3@Iy <0LJ;O*]yH5U.] =1eIcZ:},mB~Wa >4>vHQfYCFj=;0","?85:lxHcB~cmqu &bYk :Ewy_9BliS!^l4 ;E>Xxqy5T]DUTy","<F+^o@|F7c,>K$ =H;PeGFSQ2GuTH >KlV}k/p'7V%)m ?P^:!31NU|eCU< &bYo",":YlZQirUPa(%wD ;Z'a+;Z${PZ/8m <[grE2q/R}#'hH","=_oWg4R*uuQ0*$ >d<8U&V(h(BiuL ?j)94Jw:izfw9a &bYs :na<E<D?8n-J%T",";omh:c;qE$lDCm <rF(y$euo9vn'm =vE_h~^_<ZZG[]",">{iw->}>Jv/Pd, @%Q8Fc`&|xhL{( #K{Bl Qjfh <7`o ;%T{8lt(~Z.MWq","<'UoJ,z`kv${'a =+%<NsY_.3i5l@",">/yfjkj5a}`>XD ?69WbWFT.fy8Qi @=z7X{Gp2vj#_L `1|O3 #6H&` <7`s",";9I],?Eofh3rd$ <<>vYS[O5I632a","=@aP%eNGIM_|+e >FOmlWuj(ciV-} ?Mg99pmjoVe}@H @VE6l60[FSg5j} <7`w",";M>=|ouXMu99o4 <Q'}i{=>[=KisT =V?dXVC0ehUeH,",">^&tnE$@M(nM*e ?f6wo,7#S'MCV4 A4zB7ArN6$[Y2D Qjfs ;b2|pBGB6b:=DP","<fn'yD|.%n]~~T =l{x/H7w$%LMeP >tY{p2/tqkwe]@"] ++ paidGroup ["?}dXFD^96u:+Dq A+953f_3mOjFx, Qjfw ;v'^crw+{o?bOa <{V/+l]zLAo7,T",">%Z.c:,`?|>sL$ ?.1%q|;K90|[Y( @849{^'Nwf&p3P","ACb4E~F}#Mkz[P Qjf{ <,y?VEHrc|E)Zq =3?6;6>is6'mmH >;9B9+~H[95[iH","?De,siG!]t(t.a @OaxRvMeZUpW!0 A]-3X9/i6KmP?u","%9mf3x #zvRml Qjg! <@m~Iux[KiF-10 =H(=J]}X<g9%xH >PuUlzs1wS,E(m","?[;3uURV$Y2.a< @h1Y+1t{>F]>mm","AcaIWJs}R@2@q]"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 30 24 = true :=
  checkedWindows tiles 136 30 [8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+10) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top10

namespace Pr657PaidOne3Top11

private abbrev P:=PaidBatch .one3 11
private def batch0:List P:=paidGroup ["&12Pf[ &/(yt` &+lFtG #~32e# #@iS/` $^.n=h #@iJb' #x'Ul","#K|>p h@sp a,8m` $0Y[l &c?s %>f3J3 $!-BOx &c?w","?#$8TJa0j_)|@P =Ni`'2k*>4]~<e ?#$8TJa0j_)|@T =Ni`'2k*>4]~<i","?#$8TJa0j_)|@X <!UKTdzZYh^?xX =Ni`'2k*>4]~<m ?#$8TJa0j_)|@]","bQIL/ <!UKTdzZYh^?x] =Ni`'2k*>4]~<q ?#$8TJa0j_)|@a","<!UKTdzZYh^?xa =Ni`'2k*>4]~<u ?#$8TJa0j_)|@e `^0)[","#bPuh }sLh <8$h :Vz1-(D1E$xI1m <!UKTdzZYh^?xe =Ni`'2k*>4]~<y","?#$8TJa0j_)|@i :mXD`w8wa>o2N4","<!UKTdzZYh^?xi =Ni`'2k*>4]~<} ?#$8TJa0j_)|@m `sc/[",":*/Fm1P#mSB!]0 ;&7X6i-`}8aW5e <#[`>q|lt_[(p< =Ni`'2k*>4]~=$","?#$8TJa0j_)|@q :>uM|X1p7'S7h0 ;;sljZ!I;RW@R, <:2g@_+C<$`|m$","=Ni`'2k*>4]~=( ?#$8TJa0j_)|@u :S^U/!p_^WeLs0 ;QR#@Kt2VmN)oP","<PfnBK6w`gj7A] =Q:DWcn([4q:'D ?#$8TJa0j_)|@y 9l#d:vawyhCiPm",":iF]>IQN'K{&V$ ;h16t=hxs*Dp.u <h<uD8BN(,o.>D =ih&/|7>?%]~s$"] ++ paidGroup ["?#$8TJa0j_)|@} :!uE.I3aauI0[} :~/dMq3=M}/;b$ ;}mJJ/]b2$77sH","<~p|F%N%KoxEp} >$7de7^T!sIfaa ?'z(lL)FRXy;KL :6j&~ycJI%NTh0",";5uk^:r,tqDrDu <6K^}~QJM>-~2m =8G&GoYXq4}<me >;eE<P'jdC2,wL","?@E'~do2fVzo/q Qjqh &bYk :J^erL541oOX=L",";J^rmbRy>DV*Ou <L*rSpF3iX$gO4 =N{-I[f07x)TB@ >S5&qiN#G3{qf,","?Xn'3|V{yT|Dq8 &bYo :_RFe|dzv|T}H] ;`Fy},4he8la3i","<bg)*b:z'rxOlX =fQ4KHqd[^2lty >kbeI$u9+$hXSi ?r9&F7?h02yV|i &bYs",":sG(XO6d_,ZDSm ;u0$/RsW.i}v>i <xE<^S/cCljuS,","=}(;M5};$#7cqa ?&2E~=>NkrT@BH @-b%XO(SC0{-a0 #K{Bl Qjfh <7`o",";*;gL!fMFv[H*, <,v+>zTFT^6O!]","=1$P4E$K`)a^pP >6[BO#+oGf@{F< ?=`'UUeeNcA(1( @F-$kgn?V.|aDT","#?-Za' <7`s ;>0H?R87/&am5< <A_2ND65|1Ge-]","=F`dh6v4{CWG/u >M2IPm7Em+ErC$ ?U/f-o.{2S-l|e @_U#~!V+j,~7(y <7`w",";R%*3%g}t3g4@L <VG9^ku%EbXz8] =]>x>(j{9^N0L<",">dfPRYBz3nO,u] ?m]Fc*U3sCwSkD @w~#3:>t}+!jj@ _c{}` Qjfs",";fvi&U9g[}h7si <l0@n5UqlUoRyP =r{.qw_dUW@U3m"] ++ paidGroup [">{<WTFNPX3T#rD @(-(:B|IV4d;Y$ AUz7/tmTKR&jdm $Z@:8S #>H|~x Qjfw",";zkIw(iPD-m[~y =#vG}]7a6*#i'P",">+YBGiSLqr7>P4 ?4p_V3Z'|v^;F} @?Yfo[E`:%P#Ga AKq~WjmLFc~ZAX Qjf{","<1`+jX;:,:s$-, =8_O0&vO[{9AhD >A8U{ZH60/.'mX","?KFfW}f[C[gRyX @W*GFtluzs<h6@ Ae<}k%U8Yb#1%} Qjg! <ESj^+k#r't'`H","=MGV?MW?&NJVsD >VtjQL<|L(}LT, ?bzmYjr2h~lIv@","@oW(|06.^d)O$} Akl^Gd;^|pLp'("]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 33 21 = true :=
  checkedWindows tiles 136 33 [8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+11) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top11

namespace Pr657PaidOne3Top12

private abbrev P:=PaidBatch .one3 12
private def batch0:List P:=paidGroup ["&12i@+ &-`ht3 $1WD#+ #~3+5[ #CAJN' #AM)C+ &|/Yh b&I``","`sc}d #x'lp }snl QkVp &c?s &c?w $#<~?K #BsAh+","&c?{ >)7|)yIiJz6HLu &c@! >)7|)yIiJz6HLy ?a/#iX`bWd<;PX }sWh Qk@l","<RiUtD*6,m9:>$",">)7|)yIiJz6HL} ?a/#iX`bWd<;P] #K{XO h@%` <7`h &bNk $0Y:h","<RiUtD*6,m9:>(",">)7|)yIiJz6HM$ ?a/#iX`bWd<;Pa <RiUtD*6,m9:>, >)7|)yIiJz6HM(","?a/#iX`bWd<;Pe ;$em0t^&W}MR1] <RiUtD*6,m9:>0 >)7|)yIiJz6HM,","?a/#iX`bWd<;Pi ;$em0t^&W}MR1a <RiUtD*6,m9:>4 >)7|)yIiJz6HM0","?a/#iX`bWd<;Pm :0'G(|(Iz[feu0 ;*EAxE?NK0SXPa <RiUtD*6,m9:>8",">)7|)yIiJz6HM4 ?a/#iX`bWd<;Pq :DiV?0{{?Zn`v( ;@$UN747h*E~84","<RiUtD*6,m9:>< >)7|)yIiJz6HM8 ?a/#iX`bWd<;Pu :YMfUBrNbYvZv}",";U`j%)(~&D<gTX <ULYU_)?)&:1pu >)7|)yIiJz6HM< ?a/#iX`bWd<;Py",":&BI|Jk*@;2:Aq :o2ulTi#'X~Uwu ;l>}WwzgA_3Oq} <m#aWK4sMH?(m]"] ++ paidGroup [">)7|)yIiJz6HM@ ?a/#iX`bWd<;P} `sc$` #x&pl ::CBPP=[Ux.eHP",";&u(%g_SJ8%0By <${4.ioO]y*91D =&VhY8@Ir.H@B8",">)V}Y(8:j:Vw&i ?a/#iX`bWd<;Q$ :ND;%Un0lW+2O0 ;;Y7;yU'm7-+Cq","<:YGbZd8yry^uu ==-o[%K~9PM7>} >A'_1@_PM+C^rH ?a/#iX`bWd<;Q(","&bYk :cE3V[@c%7']Um ;P>FR.KX265&Di <P8[8LX!8/pG5< =Sav]oWT^6VNqX",">XT?fY(g0y0Ea( ?oAogN6o5>Ti-L &bYo",":wF,+aq7:t$*]L ;f#Ui@B,T5<~Ea <ftol>LhSIg0Qa =k7}_[d,$y`gF4",">q$~=rN|qiz-Ne @-&y$l,,vLctSy &bYs ;.G$]gCiPR}Td,",";zef!R8]wq@Wne <|S&B0APod]vo( >$l'aHo`I>e^By ?+Q_s-v5TYfr=D","@Gi%?+~GX{vCS< &bYw ;BGz1lt=g2z!ji <2Iu8e/1<pHRo]","=529v!6:.^O>UX >;B.c5{6n$nuuT ?C!@JF?K8JRY,$ @cM.YHsc=-'Nzi <7`s",";VHrcrFo|ovLqH <G/'Nw%b_oPMpT =JnMKq+#IxF'r}",">Qv5e#)k5Fslr< ?ZO!!_fay;?@wa @~27tfh}}[9{z, <7`w ;kIk7wwD5Nrwx(","<[q6f+y6$nXHqL =aLb!b|if5<n2D >iL<fm5AY,}'Fu","?r|`Vx/w],,(f@ A;tA2&^;ajH*CX <7`{ <!Jci}IvK.oD~e <qUE|=ogGL]#<P","=w+uUSqR$O3VNi ?##ChY@u~O${C] @-LA/3V0?yumS}"] ++ paidGroup ["AVXJLCRVD;Z_+< &b-V QjZl Qjfw <6K[>%zJakkp(D =):U5Of:jKd{=H",">/h,,Ef;@I%|6< ?9VJjFLLE5.5v8","@Dz!dK}F#jbTB] B-_U+>2c,6Azd0 _7k]' _7sZ` Qjf{ <JLSp+L|wJh=/$","==|eKb[l/Jlv>@ >EF?`7Z$[cyeRa","?P-Ql3X#ix7MJq @]Ia;eF[dZN<1< B1M0+z]$[lB]oP Qjg! <_MLD0}Q0*dh5a","=RatbtR?QItq?8 >[%S6)Njw}pMp( ?gaXm}dW1=<DGX","@twAp}mrH+6`G( B*edGk7mNbDE3y"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 36 18 = true :=
  checkedWindows tiles 136 36 [8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+12) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top12

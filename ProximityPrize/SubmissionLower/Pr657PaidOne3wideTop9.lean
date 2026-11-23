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

namespace Pr657PaidOne3wideTop9

private abbrev P:=PaidBatch .one3wide 9
private def batch0:List P:=paidGroup ["&12)=# &0N-Rd &-J5Kp %KZ=.d #A!(|; #@'}@p $!B}`# #A7Zl3","#x/=| #6Pr| hH[# $0YEK #x/'t #L&mx &k(& &k(*",";W+pIrAzLrB.`, &k(. %|[!s[ $_T)bG #B1kn' ;W+pIrAzLrB.`0","<wZ~,d%:>CC}AX ;W+pIrAzLrB.`4","<wZ~,d%:>CC}A] ::sPh7&`?.Nn;8 ;W+pIrAzLrB.`8 <wZ~,d%:>CC}Aa","::sPh7&`?.Nn;< ;W+pIrAzLrB.`< <wZ~,d%:>CC}Ae `GYuC","#K{dO 98V*KT0,|qC!2m ::sPh7&`?.Nn;@ ;W+pIrAzLrB.`@","<wZ~,d%:>CC}Ai 9N5>!F$s;.9hO4 :D^#m7?=}*Gs8H ;W+pIrAzLrB.`D","<wZ~,d%:>CC}Am Qr{# 9dqQU7v[VH0PlX :[4*o$JrCmQ-k$ ;W+pIrAzLrB.`H","<wZ~,d%:>CC}Aq }{5# 9zOf,)kDsB!vS,",":rh1pnVHi2V$gi ;l.(|Y20F~jMsH <wZ~,d%:>CC}Au :3.y_x`.1[v_pP",";,>8rZb}/u`<<D <&ZgSrXF*oV5b( =!%p(F<Ub7qlbH ams^K","`GYjK 9OuOeQ7Mt*<VFP :Hk05jStLvmH/u ;Br?tGnST:e39,","<>+H,.![k`BzOe =:Mo:_%Au5sBEm 9e^Vtxv=<{R0*D :_ICi[H]i3d1L<"] ++ paidGroup [";YHFv4z*x}nJke <UX)aFHrNP/b>D =RvnLvk.+3tv*4 #6HG[ }{*'","9zF_'BW,dNdE5D :u(W?M=F(-UV3m ;p|Mx!(_@BsAhL","<n(h8_p+2@yI-$ =lAm`1Rw>nr+5e <?_+ :2/f6j8y-By{v8 ;-dks?2/CGL?P4","<*RTyl45e(|Y=( =(UHmx9@s1f0xa >'jlrI;cQls^w,",":FumF3whSt.4$8 ;CC!I1&u_bC(mX <A)[{X?j+l(qoa =@&*E3`VV_MT1L",">@5l'b$Neju4ZP 9`Z>BNOvm'9ZQq :[^tUZXVzhCje, ;Y!5}!x^{[5MT,","<W]c}EK@P1-hlH =WRhzL)m:O:;}, >X^k9yj:xhvh>u 9tN}6!!`Tq:_(0",":qF{f%:FD;U!p, ;o^IRqmG9v,6qP <o3k!2Vttt7#A$ =p#IQeP%{@'#ki",">r)jL4R'.fx>#< #bPS` }s+` <?S/ :+C_)QQI<~@&3@ ;)0%uKy5klg7{,","<(<^)cb0U3!}0u =(gr#|cK<9;w=i",">*P+)}w;_0phYH ?-Qi_L:pBCuP.m hGk/ :?8?z%$3%.EJ>P ;=v-'sZ%4`|n^}","<=xq]TUvqLvfM< =?=y%io!`|E1pD >A}i_9@QA~]OH(","?Ezhqe#[UAw&p4 &jB2 :S,~mTRyjxFMqm ;R_47=;q[41&i} <SW(3FJ`0Fi.4m","=Ur#'UzV(AJ(m, >YMJ6Qgh%oI76e ?_Eh&|iGi?xYSX","#?C8YC &jB6 :g~`a(%cR(Kr|} ;hG;Fdza%(F]Lq <j6;g8?HKa_tQ4","=mH*)C)-L'S@Ae >q{+kk0}f`5|%D ?wng97Q3|=z07}"] ++ paidGroup ["<?H3 &jB: :{sASWTL:5Q:+0 ;}0BV.[OKXWrWq =!rO=*41g{U]nX",">&|1+04apj]Wt@ ?,JjC&W6IP!cq$ @39fKO9}2;{cyD","$ZlBf[ hG`3 &jB> ;2h#G+'6#!R=^L <4vIfU=>rLnK;e =8Pcpy(x&8LF-}",">=R8,z@88/bNq( ?CxJx>~L-@lJ_a","@Kbe^h!iEvxv'u _c{}[ <?H: ;F[b:ZU|h/Wbi] <I_Pu||.;~!aFe","=N/wFjzaB2>krP >T)?.gKl[rkgEa ?[H,OWGbn1X2M@","@e-dq!hTXtzKi< <?H> ;ZPC..(fO<^)tm <_GX(F]zbr8:*X =dl-z[oI^L5T1u",">k]F0SWC$7p^BH ?suk'pnxQ!Dw;} @}Ud&:P@lr|!La","<7Ih <?HB ;oE$~^WO8)_-J, <t0`7n>j,EIO5X =zJAPMd2yg,=N<","?%3M2@cwGzyuu$ @.EK],814p1_*] A8~c8R9-!p}U1(","QrN> <&9cr1*8}6dQU< =+vgG7}XRvZe@X >3)U'?Wy8$#&ka ?;gT4-oMm?~lqi","@Es-4D_Fv?w%@H AQIbJj~v5o!+rL"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 27 27 = true :=
  checkedWindows tiles 135 27 [8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+9) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop9

namespace Pr657PaidOne3wideTop10

private abbrev P:=PaidBatch .one3wide 10
private def batch0:List P:=paidGroup ["&12`qt &$SF3; &$=xi[ &+lFQ| #Q0e)C %{wV)| #~tu_' #@iRk;","`GcBt #L'2# #6Pgx $^DC-G #AM0[/ #x'4G #x/'t #6P[t","<@-| &k(& &k(* <@.& <@.* %?4;Jp $!XJPW `^0);","#bPuG ;:Gx^sjK,)*-0( <@.. ;:Gx^sjK,)*-0, <`5,}CXP)<)G|X &k(:","&jcx &jc|",";:Gx^sjK,)*-00 <`5,}CXP)<)G|] &k(> ;:Gx^sjK,)*-04 <`5,}CXP)<)G|a",">+`FmB]CkRo:cm 9v;omu34rYz+F0 ;:Gx^sjK,)*-08","<`5,}CXP)<)G|e >+`FmB]CkRo:cq }{4| <?i| 9v;omu34rYz+F4",";:Gx^sjK,)*-0< <`5,}CXP)<)G|i >+`FmB]CkRo:cu",":%`R=s3r8x9wo( ;:Gx^sjK,)*-0@ <`5,}CXP)<)G|m >+`FmB]CkRo:cy","9BTuI(tomRP0wm :;>fqe(ZT50a.L ;:Gx^sjK,)*-0D <`5,}CXP)<)G|q",">+`FmB]CkRo:c} $0Y$W #K{XW #6P;# 9W=|XOU_6FfgZa :PzzGUzCq/#(r}",";KouV&F(DnlB;D <`5,}CXP)<)G|u"] ++ paidGroup [">+`FmB]CkRo:d$ 9m'&hw7M]ww|fa :gY0{Go-/Hvo2D ;cE|WpQ[iSuYm}","<`Fu!x834F${/X >+`FmB]CkRo:d( <?_' :$m-x@v=&l0UIT",":}8DQ9csJcmWNi ;yz&Y]^30vzPje <wtUW3_Hu6nb{8 >+`FmB]CkRo:d,","#@=ILC `^/pO :9U5*hW,M?AkTT ;5tX(+W[f}d@l0","<3P-[IigT]&i?@ =2D7/L(_X'ZIiu >2M>!uIURIb&DT 9RH943?ik_rs4X",":N><:28xt3WD8H ;KRlZzLE%wUfRa <J'4^6u=z!+`<( =IqudeNu;uG1WT",">Jv=502AfGcY(y 9g<x'coRSKsvgu :d'CIXwh=diYCH ;b2#1lA.A4LNp(","<aZ;`$#r@e4wna =bAV;}v-|f3vF4 >dA<GGx-yEe/j@ <?S+","9{1Xx6A<;Xy=s( :xmJY#XVdX!3'< ;wn6e^5t]NC8/L <x1Ban/Hf*9nkH","=yo7q9?C`U}^4q >|j;Y``w/CfcMe }z|/ :2&:kfq&#f~b~8",";0UQiJ:F.,3H2< <0LJ;O*]yH5]s} =1eIcZ:},mC)@$ >4>vHQfYCFjE#P","?85:lxHcB~cuY8 &jB. :Ewy_9BliS!fST ;E>Xxqy5T]D^=<","<F+^o@|F7c,F3D =H;PeGFSQ2G}<i >KlV}k/p'7V,o0 ?P^:!31NU|eK=] &jB2",":YlZQirUPa(-_e ;Z'a+;Z${PZ6~0 <[grE2q/R}#/Oi","=_oWg4R*uuQ7oD >d<8U&V(h(Bq]m ?j)94Jw:izg!!$ Qjfd &jB6",":na<E<D?8n-Qju ;omh:c;qE$lL,0 <rF(y$euo9vum0"] ++ paidGroup ["=vE_h~^_<ZZOC} >{iw->}>Jv/XKL @%Q8Fc`&|xhTcH #6H&[ #6H1h <?H3","&jB: ;%T{8lt(~Z.U@4","<'UoJ,z`kv%%m$ =+%<NsY_.3i=Sa >/yfjkj5a}`F@e ?69WbWFT.fy@:,","@=z7X{Gp2vj+Fm &jB> ;9I],?Eofh3zKD <<>vYS[O5I6:x$","=@aP%eNGIM`&q( >FOmlWuj(ci^s@ ?Mg99pmjoVf((i @VE6l60[FSg=R@","#{Z9,+ QrN3 <?H: ;M>=|ouXMu9AVT","<Q'}i{=>[=KqZu =V?dXVC0ehUm0L >^&tnE$@M(nTp( ?f6wo,7#S'MK>T","@on5~MvGYQhq6e #>I'}O <?H> ;b2|pBGB6b:E,q","<fn'yD|.%n^)fu =l{x/H7w$%LULq >tY{p2/tqkwmDa ?}dXFD^96u:3-4","A+953f_3mOjFx, <?HB ;v'^crw+{o?j8$ <{V/+l]zLAo>qu",">%Z.c:,`?|>{4D ?.1%q|;K90|dAH @849{^'Nwf&wxq ACb4E~F}#Mkz[P","%viLCC QrN> <,y?VEHrc|E1C4 =3?6;6>is6'uTi",">;9B9+~H[95dPi ?De,siG!]t({t$ @OaxRvMeZUp_gP A]-3X9/i6KmP?u"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 30 24 = true :=
  checkedWindows tiles 135 30 [8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+10) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop10

namespace Pr657PaidOne3wideTop11

private abbrev P:=PaidBatch .one3wide 11
private def batch0:List P:=paidGroup ["&12h{` &-v=cl &*r=tW #B1lj7 #@R}p? %U{o| $!-BZW #A7Za/","_d'ad _7|>l &jcd &jnp #6Prx }{Ux &k(! &k(&","<@.! $0Y:G #K{oG #L&bt hH9t <@.& <@.* Qs4&","$_jT#' #B]l?h Qs4* :VFZ%&2f``/GV( <!UKTdzZYh^G`m <@.6",":VFZ%&2f``/GV, <!UKTdzZYh^G`q","<@.: :VFZ%&2f``/GV0 <!UKTdzZYh^G`u =Ni`'2k*>4^)%, &k(F `sc/G","#x&{S }{4|","<?i| :VFZ%&2f``/GV4 <!UKTdzZYh^G`y =Ni`'2k*>4^)%0 ?#$8TJa0j_*'(}",":VFZ%&2f``/GV8 <!UKTdzZYh^G`} =Ni`'2k*>4^)%4","?#$8TJa0j_*')$ 9Gu1=vNUV:bbri :VFZ%&2f``/GV< <!UKTdzZYh^Ga$","=Ni`'2k*>4^)%8 ?#$8TJa0j_*')( #6P;# 9]^8M@0D}.x;U]",":Vz1-(D1E$xPw0 <!UKTdzZYh^Ga( =Ni`'2k*>4^)%< ?#$8TJa0j_*'),","bQQ)O _yQ<; _yQ<O 9rF?]go4F`,Pa]"] ++ paidGroup [":mXD`w8wa>o:6T <!UKTdzZYh^Ga, =Ni`'2k*>4^)%@ ?#$8TJa0j_*')0 <?_'",":*/Fm1P#mSB*DP ;&7X6i-`}8a_{( <#[`>q|lt_[0W]","=Ni`'2k*>4^)%D ?#$8TJa0j_*')4 :>uM|X1p7'S?OP ;;sljZ!I;RWH:L","<:2g@_+C<$a'TD =Ni`'2k*>4^)%H ?#$8TJa0j_*')8 9W/%GF213{Bmcq",":S^U/!p_^WeTZP ;QR#@Kt2VmN1Vq <PfnBK6w`gj?)} =Q:DWcn([4qAle","?#$8TJa0j_*')< 9l#d:vawyhCq90 :iF]>IQN'K{.>D ;h16t=hxs*Dwt8","<h<uD8BN(,o6&e =ih&/|7>?%^)ZD ?#$8TJa0j_*')@ #6H<` }z|+ <?S+",":!uE.I3aauI8D@ :~/dMq3=M}/CID",";}mJJ/]b2$7?Zi <~p|F%N%KoxMX@ >$7de7^T!sInI$ ?'z(lL)FRXyC3m",":6j&~ycJI%N]OP ;5uk^:r,tqDz-8 <6K^}~QJM>.(x0 =8G&GoYXq4}DU(",">;eE<P'jdC24_m ?@E'~do2fVzvu4 &jB. :J^erL541oOa%m ;J^rmbRy>DV288","<L*rSpF3iX$o7T =N{-I[f07x)]*a >S5&qiN#G3{yML","?Xn'3|V{yT|LXX &jB2 :_RFe|dzv|U(0} ;`Fy},4he8lhy, <bg)*b:z'rxWSy","=fQ4KHqd[^2t]< >kbeI$u9+$ha<, ?r9&F7?h02y_e,","&jB6 :sG(XO6d_,ZL<0 ;u0$/RsW.i}~', <xE<^S/cClj};L =}(;M5};$#7kY$","?&2E~=>NkrTH*i @-b%XO(SC0{5HP #6H&["] ++ paidGroup ["#6H1h <?H3 &jB: ;*;gL!fMFv[OoL <,v+>zTFT^6Vg} =1$P4E$K`)afWq",">6[BO#+oGfA&.] ?=`'UUeeNcA/vH","@F-$kgn?V.|i,u hG`3 &jB> ;>0H?R87/&atz] <A_2ND65|1Glr}","=F`dh6v4{CWNu8 >M2IPm7Em+Ez+D ?U/f-o.{2S-te(","@_U#~!V+j,~>n< <?H: ;R%*3%g}t3g<(m <VG9^ku%EbY$}} =]>x>(j{9^N84]",">dfPRYBz3nO4]} ?m]Fc*U3sCw[Re @w~#3:>t}+!rQa","#{Dd1C <?H> ;fvi&U9g[}h?[, <l0@n5UqlUoZaq =r{.qw_dUW@]y0",">{<WTFNPX3T+Ye @(-(:B|IV4dCAD AUz7/tmTKR&jdm","%:&CN[ <?HB ;zkIw(iPD-mdg< =#vG}]7a6*#plq >+YBGiSLqr7F8T","?4p_V3Z'|v^C/@ @?Yfo[E`:%P+0$ AKq~WjmLFc~ZAX","QrN> <1`+jX;:,:s+rL =8_O0&vO[{9IOe >A8U{ZH60/./Ty ?KFfW}f[C[gZay","@W*GFtluzs<o{a Ae<}k%U8Yb#1%}"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 33 21 = true :=
  checkedWindows tiles 135 33 [8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+11) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop11

namespace Pr657PaidOne3wideTop12

private abbrev P:=PaidBatch .one3wide 12
private def batch0:List P:=paidGroup ["&0#-/7 &,:Nix $02*up $!-Je' #A!(q7 a,9&C `^8_t hHOx","<@8| #L&mt }{Ux &k(! &k(& $#R[8[ #B]t>3 <@.!","$0Y:G #K{oG #L&bt <@.& <@.* Qs4& Qs4* ;$em0t^&W}MYve","Qs4. amsiC `GYuC ;$em0t^&W}MYvi Qs42 ;$em0t^&W}MYvm","<RiUtD*6,m9B&@ <@.>","}{4| <?i| ;$em0t^&W}MYvq <RiUtD*6,m9B&D <@.B <?j# ;$em0t^&W}MYvu","<RiUtD*6,m9B&H",">)7|)yIiJz6P5D &k(N ;$em0t^&W}MYvy <RiUtD*6,m9B&L >)7|)yIiJz6P5H","?a/#iX`bWd<C9( #6P;# 9c^(XW;E4~Z;3T",";$em0t^&W}MYv} <RiUtD*6,m9B&P >)7|)yIiJz6P5L ?a/#iX`bWd<C9,","9xB7oj1vV}c64L ;$em0t^&W}MYw$ <RiUtD*6,m9B&T >)7|)yIiJz6P5P","?a/#iX`bWd<C90 #x&p[ #6HG[ <?_' :0'G(|(Iz[fm]P ;*EAxE?NK0Sa9$","<RiUtD*6,m9B&X >)7|)yIiJz6P5T"] ++ paidGroup ["?a/#iX`bWd<C94 :DiV?0{{?Znh^H ;@$UN747h*F(}T <RiUtD*6,m9B&]",">)7|)yIiJz6P5X ?a/#iX`bWd<C98 9oAQJE:U*[5u#T :YMfUBrNbYvc_@",";U`j%)(~&D<o<y <ULYU_)?)&:9X8 >)7|)yIiJz6P5] ?a/#iX`bWd<C9<",":&BI|Jk*@;2B*4 :o2ulTi#'X~^`8 ;l>}WwzgA_3WY@ <m#aWK4sMH?0T}",">)7|)yIiJz6P5a ?a/#iX`bWd<C9@ <?S+ ::CBPP=[Ux.m0q ;&u(%g_SJ8%8+<","<${4.ioO]y*@ve =&VhY8@Ir.HH*X >)V}Y(8:j:V~l,","?a/#iX`bWd<C9D :ND;%Un0lW+:7P ;;Y7;yU'm7-3,4 <:YGbZd8yryf^8","==-o[%K~9PM?'@ >A'_1@_PM+CfYi ?a/#iX`bWd<C9H _yQ<W","hGk/ &jB. :cE3V[@c%7'e>0 ;P>FR.KX265.-, <P8[8LX!8/pNz]","=Sav]oWT^6VVXy >XT?fY(g0y0MHH ?oAogN6o5>Tprm","&jB2 :wF,+aq7:t$2Dm ;f#Ui@B,T5=).$ <ftol>LhSIg8:$ =k7}_[d,$y`o.T",">q$~=rN|qiz57( @-&y$l,,vLc|<< #?C8eO","&jB6 ;.G$]gCiPR}]KL ;zef!R8]wq@`V( <|S&B0APod]~VH >$l'aHo`I>ef+<","?+Q_s-v5TYfz%e @Gi%?+~GX{vK;] Qjfh","<?H3 &jB: ;BGz1lt=g2z*R, <2Iu8e/1<pHZV} =529v!6:.^OF=y",">;B.c5{6n$n}]u ?C!@JF?K8JRaqD @cM.YHsc=-'Vc,"] ++ paidGroup ["&jB> ;VHrcrFo|ovTXi <G/'Nw%b_oPUWu =JnMKq+#IxF/Z@ >Qv5e#)k5FstY]","?ZO!!_fay;?H`$ @~27tfh}}[:&bL h?a[","h?lh <?H: ;kIk7wwD5Ns!`H <[q6f+y6$nXPXm =aLb!b|if5<uwe",">iL<fm5AY,}//8 ?r|`Vx/w],,0Ma A;tA2&^;ajH2+y","$Z@BB7 QrN7 <?H> <!Jci}IvK.oLg( <qUE|=ogGL]+$q =w+uUSqR$O3_7,","?##ChY@u~O%&+} @-LA/3V0?yuu<@","AVXJLCRVD;Z_+< <?HB <6K[>%zJakkwme =):U5Of:jKe&%i >/h,,Ef;@I&&{]","?9VJjFLLE5.=^X @Dz!dK}F#jb]*} B-_U+>2c,6Azd0","<?HF <JLSp+L|wJhDtD ==|eKb[l/Jl~&a >EF?`7Z$[cym;$ ?P-Ql3X#ix7U34","@]Ia;eF[dZNCv] B1M0+z]$[lB]oP"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 36 18 = true :=
  checkedWindows tiles 135 36 [8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+12) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop12

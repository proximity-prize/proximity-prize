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

namespace Pr657PaidOne3wideTop5

private abbrev P:=PaidBatch .one3wide 5
private def batch0:List P:=paidGroup ["&10|2h &12(b? &0yco| -s(t,+ 7Xt?p &#op;h %~ON#W $&A:tW","'y^GF3 #~39}3 #@R}NK `skZ' `20=3 %|qM)# $`N2J| <@./","<@.7 <@9; #~tm([ #AM0P; :r0?RHCVb7iZ4q `2'zW #bXt/ #6P]3","hHE7 ;-X>ea,Bu5k0v8 :R)cKM#(paTdA< ;F$=wxr/+3ldY] :jVD#fI>SQAK/y",";_L=-3Yx>1n:>$ aAkQS `2'oW",";%'%W~pT7B.2{X ;wu<?KBdQlkLIT <@#? ;<Sd0:9jx2wwj8 <3@;Qd+Oejm#-y",";T$DeRa#[#d_Wu <Ki:d{q;xhnUo@ #L&W7","<?u; 8JDAi3eF':tjPL ;lQ&<l*9?PL%na <e49w6Y(.fp,Re 8[vod1g|]96vXq","9L2i9e(X(nk}%T :=KUdK%/2Rz*]q Qr{;","7~Q[4v4]9d(:~X 8nK?_/jU56[qz( 9_GvSDFm8Up?R< :PEV@u[Tw+0+me","#bPjl #L&L7 &jdB 9!}mY-m.k4{~%L","9q^&n$f$Hzp>J0 :d?V{B5{^`C,}X <?j? &jdF 94R=T+oeC3>--q",":&s4*b'8XazM2e :w9WWlmDE7V.0L &jdJ"] ++ paidGroup ["9F'kO)r=y1^968 :9+ADAELj(zL*X ;-3X59Fk,lj/@@ <?jF 9WY;J'ttQ/}E>]",":K@N^~daym~lW@ ;@-Xoc~3qC}0P4 <?_?","<?jJ 9j.iE%wM*.?QG$ :^U[x_%v-4~kO4 ;S'YL0WYWx8}xu #?-c_S #bPSh","#K{Mp <?jN","9{a9@#z&`,_^OH :pkj5>D-<z&-|y ;f~Z)Z2#?OL!+i QrpJ :05g:~|]8*~jWm",";&#wN{cAMA&,tm ;yxZd'iI''`#;] #|)AY7","<?S? hH$R ;89'i[$U^)*LDT </r[@QBok[s$KP %wcD'C %wcTE| hGk? <?SC","hH$V ;JN5&;BjnM*K<H <Bl[z{z8R4)%[D hH$Z ;]dB?xa~~5.kj0","<Uf]WHS_9i<&l8 }{*V ;oyOYX#61Y.jb$","<i`^4s.'~@O'|, #>3Qw[ }{*Z <%1]t8AJAA3-1i <|Y^o?eMeuc).} %9mn2O","#L&6N <7Fk0u`_Qf3,)]","=2S_Kj>tLLv*>q"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 15 39 = true :=
  checkedWindows tiles 135 15 [8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+5) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop5

namespace Pr657PaidOne3wideTop6

private abbrev P:=PaidBatch .one3wide 6
private def batch0:List P:=paidGroup ["&/''sl &12)&h &12hpS ,VG6IO 7-kzh %~{N0p %}?p4/ &!I<jG","#AM1+? #@'uBK aAt6+ #~tm>W #AM0g7 `2/xx #L&y+ hHP/","<@93 %|Zwu# :XIvm*V=ZPH=g@ $`#*(| #CAIhh :qrv!B?)o.EOrq",":9xg5_SJL`DmUu ;-=u4Z's%,G&V8","$[bQW #x')W #x.z' #6PQ' hH:+ :QHGjwza0P1TDT ;EftFrm_8*HY:] <@#3",":iv)B3Cvq@{<34 ;_1sY-UJK(J/|$ ;$EgwKk/T1h#~q ;wYrlE>6_&Kc`H",":EbM9HqGk_J!pL ;;sHNe4E8!ShmP <3%q~^'!raHuky <?u3",":]8T;5||3$Nvm4 ;SC*&}ZZxp@O[0 <KMq3ull(_JKO@ :sl[=#+RVgX1Am",";kph[9$q[a-7Im <dvpF0TW;]L!3e Qr{3 :5K8WVd0f?Q4X<",";-Bc>m7)|,^(>T <&@I3QK*?Pv|8L <}AoXH=CNZMTu, a,85S $0Y$`",":K*L.HWw$YGzua ;Cvj@YB^Bog?q0 <=n*hjr@#~_BN8","=8jnka&/bXO+XP <?j7 :af`b:L`?t>d5( ;ZLqBFN4h4l6mu <U=i@&;UdoK*<u","=Q5m}xkxv6L=e$ #@=ILG #6P;3"] ++ paidGroup ["Qrp3 :wDt8,AH[n1+yX ;r#xD3Yi.wuNBP <mkIu>blG`7o+T =j^m33Se,4MqHH",":5]|<j]FXi)<Ne ;0$*k{61x+'r8} <+W!E}f?R]~fu,","=(;+LW,%+P$Uw4 >&)lEK<P?2OG,m :JF&L4>6!]>s2X ;E`>Am*x6D{ZUD","<B.)Gjqsx#&]qq =?hj$pR:l@n=eq >>QkWd%<R0Pzn4 hGk+","QrY7 9e5V7i'?A+wK3q :`/-[Z}%I0P+=X ;[>Qu^|aQ_rCri <Xb0IV}J>f/uFL","=W8JY+yPO1Z%SP >Vzjj{k(f.RPQX 9y*8+;V))8|p?$",":tu4l%^qp$fa~L ;qzfKOqInXdiY< <p87KD+~d+4lC4 =of,1DBg3!FjB0",">pEi}6RqyiOc^, :/{v{l(oo%}sr@ ;,^;{L?a9Tww,L <*Xz!Af3,sZQva","=)l>M17U*n>&um >*5jf]i|sp3Q0m ?+ni2N;^/gQ9AP <?S; &jMB",";AFC-s~O`I0Om@ <@80U3YyH0Q;6( =@BEN{C,O3BzrT",">AcK=v35V`}8|L ?D9hDg$IBeRm%u &jMF ;V/J==`?)zAex@ <UtD,%NbdJH$RL","=VvLPhN`svL5G0 >Y3,s1YK:Pi}k, ?]bgV~j5UcTBg<","_MHw` }zq7 QreF <lRW_tCK#D:I9} =nLSRTZ7;;Q,Cu >q`kJJ#a{AUeXi","?v-fj9Q~iaUvJa QreJ","=%1l5f84>_12VD >(#ZTAfk_~ZCvP ?,0L!cIw_2BLGH @1Ue|Q:j}>S+V4 }z|J",">>VbV.rB&dd[K, ?C^-V{q0B#/46( @I~e1j#V3<T_:X"] ++ paidGroup ["#>3QlO <7>[ <7Ih #6P0R ?[-l/7:F&OtWKq @cIdD$iBF:V4{} %9mn2O","#6P0V","?sZLdOa[g@a?:P @{rcV<Q.Y8Wh`D"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 18 36 = true :=
  checkedWindows tiles 135 18 [8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+6) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop6

namespace Pr657PaidOne3wideTop7

private abbrev P:=PaidBatch .one3wide 7
private def batch0:List P:=paidGroup ["+xZZ1[ +w6$yO 6_cW` &)6$hK &',=H` &#op0` %~$ERG $a_*u?","aWA=K a,@v| #~Hm&' #@R}C; <@9+ hHE# <@.' :;p=8N~sktG}.(",":T;<Jgg_~rIRoL #L&b| hH9| 9{#z[cStWWeSi( :md;^!OK4pK)Rq",":5P[3{{-;HQ;Ve ;)/:p:87GnL]78 $#'Rh[","#AcZch `2'oG #bXh| 9YBBYR2Z)?sx3} :L~<i7DB|9>#ED ;AW:%Q~#ZlN2x]","9pvI[?>1M%}2fX :eM{@OkX`**h4$",";Z#97jfloIKE'0 <?u' :*LP^,Ieqi)J;4 :|{[ui4oBwtO!a ;sK8J%NX%GLxhT",":A#W_vU<9..A7y ;7K=M$[(&ha6n@ <.t7]=7D8ENNKy","b;|#K `sc/K 9b9uF'}XK@UVz4 :WV_acap]q7XjT ;Nx|%=%=gXL{[}","<G?6oT}0KCP%0@ Qr{+ 9wv+yvrAgZL@9X",":o-fcOmG%6<Og< ;gH]YUKSK)5Ari <`h6$mey_AQWqe #bPj[ #L&L'",":0T?Ohg+%uC)U} ;(ame<x{HyEh;u ;~v>1nrj.w!)aH","<y357(Mer|Nj}8 <?j/ :F3S&YZqA29osD ;?7tg*'Qn>J_8] <9E|g*<!ogknO(","=4[4I@6Q(zP@a] hH$/ :[ogYKOY^,,7Yu"] ++ paidGroup [";Uk{ht3)5$Svk8 <Ps^>Bc8RWWU=e =M'3[W|=;xQtE$ 9xj_[iCKU8@,EX",":rM{0=DByF!}w< ;mB%ja>]YFXmg} <iC>s[,N6HD=,D =fO2npe)NvSJ)H",":0Rfl3%:|,Uc)L ;+-1d/9,7`vg6a <&v,lMJ3~,c(<X =#p}JtRdw91$x$","=~x2$+LrbtT}jm <?_3 :E;m{Yd*E]gx4L ;@iE9~-rRzmOS(","<=L3n:UhDol?o4 =;@_#/yzZ)zifa >:C16C5^vQR2v@ :Z$u.$DvlP}Pu@",";VGXmp!Zot_u:X <T#:p'b>j4q6ky =Rn?WHC3=wgPT@ >Rl0HZ{J,OSfYe","#x&ed #6H<d Qre3 9skI;IDhfdSF~i :oj|=K&f6%1g#@ ;m&mCatD.1U^V}","<kVAqqms0wzN@T =k=~/ajH~hS8B}",">l7/Zsd6?MU<>, %x]nY+ }z|3 :*`+.ytQMqXl,y ;'S&LreT[vG?d4","<%c#wRi-IKLFtD =%-Hs^yIU=!E=< >%k_dz3_bX?}1]","?'`.n.L!RKVp!P :>Sj!LF;5~_38, ;<<-]<FD&IXTo4 <;A7MD]sefC03i","=;aOuK'}z#+]ou >=;@<5YuEI,d}< ?@+.#F4kfIXEcu &jB6",":RHJr|v${k`6kH ;Q%4ld(3Lzjjz4 <P}K$6Q]$`5Tx< =R7Vw83TAE0Sl]",">Th~qN$.)9vKky ?XS-5^zVz'UWoH #?-cHC &jB:",":g=,fOGkcxeZvX ;fk;|-g!so#C^( <g[_W(FE?z,>7a =ik^y%?+f+9lA8",">m8`HgJCjg^p$e ?q|,GvcC0%W.Rm <?H7 &jB>"] ++ paidGroup [":{1kY!wTK(k#$i ;{SC.TGo=B4Xi( <}:s-w;.[7#'T( >#AezoJ`,nC&sq","?'f@~!qYMWJVpD @-G+Z1K/C#Xb74 _c{}[ hG`7","&jBB ;2&LLRI>3rl&W( <3<J=|)^d6J2Ky =5w)ai/tx0rL;X >9ul|[V6Q3GzpX","??6!U;:p1H7>_$ @Ep*mI3xU~Z7xX <?H>",";Ex.@%y'y!qJc8 <H%QMEhM-g[GVy =KU=7Z$^6Ji5W} >PKs~HbjuvQ5E4","?Vca-Sb(r9$&La @_;*!aydi|[k[} <?HB ;Ylm3UJna/vonH","<]kX]mI<SZq~:m =b4PkKvFQe_{uD >h!{#5nA=;V,Ay ?o3Abm+>U)mk;@","@wd)4ybO}YX}hP &b8g <?HF ;naN'(zWHywsCe","<rS`m7++{/&6Em =wpeA=k/n!Ue4i >~V%%!yua~`CtT @)a#:(QT8wYR)}","A3/(G4J<3WZSKu"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 21 33 = true :=
  checkedWindows tiles 135 21 [8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+7) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop7

namespace Pr657PaidOne3wideTop8

private abbrev P:=PaidBatch .one3wide 8
private def batch0:List P:=paidGroup ["&12(xW &12`}' &.pFL? &,:VhS rvd@S #}ze%+ #@=JSC $^.n'G","#A7ZU/ #6Ps# hH[' `2/xp #6Pg| ;HIR%sCm%nQn[i %|qLzt `^04?","#bQ#K ;HIR%sCm%nQn[m :3#@}&SF0>BWtq ;HIR%sCm%nQn[q",":3#@}&SF0>BWtu ;HIR%sCm%nQn[u $`8].t $!Bu?W","}{?x Qs(| 9QD.[FDO)UJ}%0 :E/Lrl$n(=2w<L ;HIR%sCm%nQn[y Qs)#","9hx5^3P&M;T7Vi :]].J'K&i-|_+,",";R?TPTud7>2L]q :!N<_}[Yr^Y.SP :u,m!?r<K{iEvi ;khScm^OJ<4#A8",":9%Cajh19CcF), ;/YMVX;R/lU-eH <'3Rv(F;^:5V%] 9Y1#GihiUkB,A0",":OXJcVse^fh=%q ;G*/.qbhq<=P{4 <?[R+@/'qu2i10 #bPjS #6HRW }{5#","Qr{' 9om6{Z]Qre4Q(a",":g/QeD!<%KqTWL ;_Vmd-+~T-*8iq <X'Q=Wtq's4>rT :(KJQLQ;1!+:E(",":}cXg1-pI1zm-( ;w'N;ER77zs}WP <qOPOp]]:q5rUy #@iQo?","a,85K $0Y$W :>*_(>F$L<!#bL ;79`h{9FnT!d)m <1T/p^yLxk`eF0","=,xOc+EHMo7H:@ 9ZoiUG)|WeXRa< :Sfr[0:jhUui~q"] ++ paidGroup [";MmgjhD{5:+{[H <I$nGwBc[[LL4m =ECNuC.4am8{{e 9pWpenhl!8jhl<",":jE)2!/S'Oh1fD ;eCnlTPQY]0rX0 <aQN}2iy?L94#L =^lN*Zs}uJ61*8","<?_+ :(@wu8IZH-#AO0 ;#$<eq$<Bj^x%i ;{wunA](~B:--i <y!0TK32#=%xo,","=w7M<s[j+H7dk] hGv+ :=*!'`+Io^4VZ0",";8`P;bv%_'TaB0 <5M|p.h]Ee?$*P =3No,dYGd-o`]i >2`LO.DU>F9:O$","9V]f`pxD|P2KOX :Qp)7)j98QJ0>$ ;N>doSjkzAKI_T <L%&qxt3jJH;],","=J|Oa}#^F{[GKH >K+KbF-AQD:n3H #6P0/ 9kQGSCJ.d^7pZi",":gX0FPK(`%[EI$ ;dzxEE_T9;=oF( <cX-sf!h10QS1e =cL198It*lH/:(",">dSJt^s-eB<Ctm <?S/ :!F)FsyuLJ8t1( :|A7Ux,u(vq|,u ;zY.y7S=TU4WcL","<z/4uR.>URVJ.L =zyonPq,k]4t(e >||J)vZvx}9V#@",":6:h:FK_4W>;<8 ;4*>fAkdOJ&47u <38BO)H&pp+A!q =3c;w?9rz8`ba(",">5IPEj:BNL~ZtD ?8GI<1Cc.{;,de &jB2 :J/I-v{GyeC`GH",";HpEuiLRv>;jxi <HtV%x<m/izfgD =J9By,EIAZeX]m >Lw1{%aX2zg!-0","?PpHNI,NAy<`H, #K{7[ #6H1d Qjfd","&jB6 :_$*~IM1arI'RX ;^XM(3.B?oM#&i <_RjXj1UK&qO&i =amIzvP}f@nq2H",">eFpR>*nskRfxm ?j;Gaar:Tw>6,P <?H3"] ++ paidGroup ["&jB: :ruiqy|xI_J+(u ;sAT7Ym1gB_81i <u1~/[&>g@h8C0 =xCP|c]T-csh/0",">|tQ*VQ'V[?MgL @%dFsyZ&hu?imu &jB>",";)jJeLNb1lOO4( <+*[G$M~06tnr] =-n4cLx(%Z^~`T >1wW~Oi+QH}!ai","?7D2_ox=:L,5U, @>/F)4Bo|R<{yH #{Z9,+ #>_Z1O","hG`7 <?H: ;=_,W|~JvyTt?8 <?pcVK/mVh)&}] =CLH9>lnATPFG(",">HM`#<t_vl$v^P ?Nqq7+AR{<uzCi @VWE;L+[2P>Q]m","<?H> ;QRkKOP4_fUwrT <TXjfrn[}[>]aP =Y+[m0aV]oG/dL >`$g%*#6=Q.13,","?gAQlChi_-bb2H @p#DMdqGEN@(A4 <?HB",";fGL?#!{Fs[>}e <jAqv<OKG/OrlP =ogpC!U?y,=v#q >vWn&t.jb77Hee","?~o3C]2!A{NH~( A+KC`|Y3XLA[%X &b8g <?HF",";z<.2RQe/#ad+u =!*y(d1:n#fKOD >(F&vqJ)7F4_@8 ?0.u(a:A)Y<?bL","@9>qxuX8%l;0le ACtBs7A|lJC1f}"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 24 30 = true :=
  checkedWindows tiles 135 24 [8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+8) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop8

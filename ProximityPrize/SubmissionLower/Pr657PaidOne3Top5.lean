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

namespace Pr657PaidOne3Top5

private abbrev P:=PaidBatch .one3 5
private def batch0:List P:=paidGroup ["&11^-S &11}y| &12P9' -s>9mK 8iRPd &%!NL` &!uh-t $'%ncG","'y^(Hp %}*#:' #}z]'+ #@R}Nh a,9&x `GZg' %?`D'3 h@i+","<8Q/ #~_:!| #@Ru// <3@;Qd+OejlxEX }sd# QkL' <Ki:d{q;xhnN)}",";lQ&<l*9?PK{)@","<e49w6Y(.fp$kD $0Y:x #bQ#| }sW| <&~dr'PO#A8bt} <}]9,NAqAdqWNi",";Dy5(+E)`'X-)X <>NEI?wed2%Ic]","=9(8>g*]UAnjZ< `^0)l ;[O<)uP^&jbD[4 <U|&~X@{G!o1Q<","=QP7P~pHi?p@>a :xge{&=$@i$~e, ;s&C+b]4K/g;Wy <nKeUqh4*pZv?y","=jy6d9X4|=qt#( #x&{x ;1EyPu1j]btFK] <,YJ-NhhorpS-T","=(yF.-1IkaG^.X >&D5vQ@~2;sIdL :L)W)&/,vw[1>] ;G%0'g&Rx|k/i$","<C0Q/;t?77uJ*< =@I'cEW`NQ4Dz8 >>m5+j)jE9t}Gq 8'YY<6be-BFI<X","8vmn@!_-y{pwk@ <YdX1)!sZz~b[u =Wvf:^~v2A~,hu >W84>$oUXtr2SD","87lFY5!bEHqxi, 9*`qzIA[tY|_B$ 9{a9@#z&`,_Uh( :pkj5>D-<z&&7X",">pa3P<WAlrsf7i 7UZJmc<'1E2{Ri 8G~3w3?_^O?J7] 9;RuVq%-nY/gNX"] ++ paidGroup [":05g:~|]8*~bpL ;&#wN{cAMA&%/L ;yxZd'iI''_xS< `GYS` #K{Bl","7f04oC3&d=N&ji 8X2~71][vUjyd0 9LEy4:e[i8;N&<",":Ah75}!5n)@nxq ;89'i[$U^)*D]4 </r[@QBok[ryd0 }s+t 7&6?8}:=Exi3g0","7ub{q$*&9rekKu 8iDkT/zY1]8K2a 9^8|nbH-c7KV2q",":S<e0{$lF'`{$8 ;JN5&;BjnM*CT( <Bl[z{z8R4(zt$ %wcD'G %wcL^`","75-8}Jds2iA@'H 8(7era~%lk#scu 8yVWr.:VIccz_4","9o,#K,+[]sW=gT :eo5+y'D|&#*,] ;]dB?xa~~5.d$m <Uf]WHS_9i;|&u","7D$2dv1J|XwLDa 87jNtAu%BB:ZE$ 9,iE2,WSbj1L-e :!|'(Rl-VrhEt,",":wCc&w){T$B65$ ;oyOYX#61Y.bya <i`^4s.'~@O'|, 6`lW^pn>#y+o70","7Rx,KC[#iIOXby 8G?8v!l$u:Uc]$ 9<{2O*uPzp[{Y8 :3o*bzN[QPt-Jm",";+v2~u,T-!bB=H <%1]t8AJAA3%IH <|Y^o?eMeuc).} #>3Imx _7sOS","6o(u,6k##KQ2'4 7bo&2o(XU:(f#4 8Vr!w`c$JomJ>0","9M/|m)5N5w*M(i :Db.?D2-KP'5WD ;=J`ys/-b~$NEm <7Fk0u`_Qf3$A<","=2S_Kj>tLLv*>q 6-<9H{dPH?]&6T 6}B4VYge#Zs1>D 7qe|w<R1B*^r@L","8gFiy@Y#}h+RU0 9^Aj-'RKM}T|T< :UT1ykr[F/2z/( ;N}0tq1d:|CZN4","<I[xJT~sbM7Co$ =EM`)6v=4%,+Ne"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 15 39 = true :=
  checkedWindows tiles 136 15 [8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+5) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top5

namespace Pr657PaidOne3Top6

private abbrev P:=PaidBatch .one3 6
private def batch0:List P:=paidGroup ["+z9AC/ .Ob(al &(<,mS &%M`2; %D,p7/ &(%d:` &(&F'C &%MVBO","#}#S_` aAlM| $]J2rt #@iRT` `GZDp #K|3| h@i# <8Q'",";wYrlE>6_&KZx( <3%q~^'!raHn&X ;SC*&}ZZxp@Gsm <KMq3ull(_JCg}",";kph[9$q[a-/bL <dvpF0TW;]KwKD }sWx <8/x",";-Bc>m7)|,]}V4 <&@I3QK*?PvtP, <}AoXH=CNZMM/i #}#Jox aAc_7 `^0)d",";Cvj@YB^Bog8+m <=n*hjr@#~_:fu","=8jnka&/bXO#q0 h@0d <7kl &bYp &bYs }sLt :af`b:L`?t>[Le",";ZLqBFN4h4l/(T","<U=i@&;UdoK!TT =Q5m}xkxv6L5|a :wDt8,AH[n1$48 ;r#xD3Yi.wuFZ0","<mkIu>blG`7gC4 =j^m33Se,4Mia( ;0$*k{61x+'jP] <+W!E}f?R]~_/i","=(;+LW,%+P$N1q >&)lEK<P?2O?DL :JF&L4>6!]>kJ8 ;E`>Am*x6D{Rn$","<B.)Gjqsx#&U,P =?hj$pR:l@n5}P >>QkWd%<R0Ps(q %;w^+/","#@=AMx :`/-[Z}%I0P#U8 ;[>Qu^|aQ_r<-H <Xb0IV}J>f/m_,","=W8JY+yPO1Yzl0 >Vzjj{k(f.RHj8 9y*8+;V))8|hVa :tu4l%^qp$fY9,"] ++ paidGroup [";qzfKOqInXdaqy <p87KD+~d+4dZq =of,1DBg3!FbYm >pEi}6RqyiOZui",":/{v{l(oo%}l,} ;,^;{L?a9TwoD, <*Xz!Af3,sZJ1@ =)l>M17U*n=|0L",">*5jf]i|sp3IHL ?+ni2N;^/gQ1Y0 #6H<p Qjqp :CpWo>WXV3&380",";AFC-s~O`I0H'} <@80U3YyH0Q3Me =@BEN{C,O3Bs-4",">AcK=v35V`}17, ?D9hDg$IBeRe=T 7b`1{yj8`FJVPe :We9bo*B>@+WC@",";V/J==`?)zA^2} <UtD,%NbdJGyk, =VvLPhN`svL-_m >Y3,s1YK:Piv%i","?]bgV~j5UcT:~y `1|O3 7qpn?)xefh~B,X :lXxUAY,'-,Zv]",";kuQLeA.PMRs=} <lRW_tCK#D:AQ] =nLSRTZ7;;Q$[T >q`kJJ#a{AU]qH","?v-fj9Q~iaUnc@ _MHwd 7.C9FO;%0#Z+^q 8$$L`7*4mjOj/X",";#MYHr+rl:2#$m <#^X]/!zwAiK~q =%1l5f84>_1*o$ >(#ZTAfk_~Z<10","?,0L!cIw_2BD`( @1Ue|Q:j}>S#nq &bNw 835,#D8at/&ThL ;7B;<DZ[SG7G/}","<8F`lUaj@rzb,q =:n!iW,zYy'q.H >>VbV.rB&ddSci","?C^-V{q0B#/,Me @I~e1j#V3<T_:X &bN{ 8BEhCQG0{0T|kL ;K6z/u-E<48Jc<","<M/g{}BXgg3:me =PL6?H~cv5{YJm >U-iWx}vK)iJ`P","?[-l/7:F&OtOdP @cIdD$iBF:V4{} <7>` <7Il <7Tw 8QVFd_U^$R+hF@",";`+[#G]/$A=onL <buo.G$H1:DOxe"] ++ paidGroup ["=g+Is:sL5/n!2@ >lapYf,Lolrc5, ?sZLdOa[g@a7R0 @{rcV<Q.Y8Wh`D","%9mn2S <7T{ 8ah&'le-+SZ2I@ ;s}<sx.uiNC6y]","<w^v=nc7W.Z)[X =|g^I,h5PIdhNe ?&7w[R8$71wY1q @.+.;i*rJ1L|@m","A%l;-CM^%N1%:4"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 18 36 = true :=
  checkedWindows tiles 136 18 [8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+6) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top6

namespace Pr657PaidOne3Top7

private abbrev P:=PaidBatch .one3 7
private def batch0:List P:=paidGroup ["+xp}r| +wK80/ 7oAiS &(gB2| &(;yYW &$iy0S %~{NR; $bX3u3","#@'uBd `^0wt #~_:N| #}#SHS QkVt &c4x &c4{ <8P|","#K|(t }snx ;Z#97jfloIK=>m ;sK8J%NX%GLq#4 a,8Vd $0YEp #K{zp","<.t7]=7D8ENFdX","aAk]` ;Nx|%=%=gXLst] <G?6oT}0KCOzG} $^D;/? #AM(^' ;gH]YUKSK)5:-H","<`h6$mey_AQP,D ;(ame<x{HyE`ST",";~v>1nrj.v~~y( <y357(Mer|Nc7u ;?7tg*'Qn>JVP< <9E|g*<!ogkfge","=4[4I@6Q(zP8y< :[ogYKOY^,,/rT ;Uk{ht3)5$So%u <Ps^>Bc8RWWMUD","=M'3[W|=;xQl]a :rM{0=DByF!v1y ;mB%ja>]YFXf!] <iC>s[,N6HD5D$","=fO2npe)NvSBA( `^(+3 :0Rfl3%:|,UZA, ;+-1d/9,7`v_N@","<&v,lMJ3~,b}T8 =#p}JtRdw90z2a =~x2$+LrbtTv%L :E;m{Yd*E]gpL,",";@iE9~-rRzmGke <=L3n:UhDol8)q =;@_#/yzZ)za~@ >:C16C5^vQR+0}",":Z$u.$DvlP}I/} ;VGXmp!Zot_mR8 <T#:p'b>j4q/&X =Rn?WHC3=wgHl}",">Rl0HZ{J,OS^rD <7kl 9skI;IDhfdS?9H :oj|=K&f6%1_:}"] ++ paidGroup [";m&mCatD.1UUo] <kVAqqms0wzFX4 =k=~/ajH~hS0Z] >l7/Zsd6?MU4Ui",":*`+.ytQMqXdDX ;'S&LreT[vG7{q <%c#wRi-IKL?/$ =%-Hs^yIU=!=Ty",">%k_dz3_bX?uI< ?'`.n.L!RKVh:0 #6H<l Qjql &bYo :>Sj!LF;5~_+Oi",";<<-]<FD&IXM)q <;A7MD]sefC(KH","=;aOuK'}z#+U*T >=;@<5YuEI,]7y ?@+.#F4kfIX={T &bYs :RHJr|v${k`/&(",";Q%4ld(3Lzjc4q <P}K$6Q]$`5M2y =R7Vw83TAE0L'<",">Th~qN$.)9vD&X ?XS-5^zVz'UP*( &bYw :g=,fOGkcxeS18 ;fk;|-g!so#;ue","<g[_W(FE?z,6O@ =ik^y%?+f+9dXu >m8`HgJCjg^h<D","?q|,GvcC0%W&kL _MHw` <7`s :{1kY!wTK(jx<H ;{SC.TGo=B4Q#e","<}:s-w;.[7!|le >#AezoJ`,nB|.P ?'f@~!qYMWJO+$","@-G+Z1K/C#XYNq <7`w ;2&LLRI>3rk{oe <3<J=|)^d6J*dX =5w)ai/tx0rDS8",">9ul|[V6Q3Gs+8 ??6!U;:p1H76va @Ep*mI3xU~Z038","%wM!xl <7`{ ;Ex.@%y'y!qBzu <H%QMEhM-g[?oX =KU=7Z$^6Ji-p]",">PKs~HbjuvQ-]q ?Vca-Sb(r9#{e@ @_;*!aydi|[k[}","#{D['` #>H}-' _MHl` QjZl Qjfw ;Ylm3UJna/vh)( <]kX]mI<SZqvRL","=b4PkKvFQe_t0$"] ++ paidGroup [">h!{#5nA=;V$YX ?o3Abm+>U)mcR} @wd)4ybO}YX}hP %v~n|S Qjf{",";naN'(zWHywk[D <rS`m7++{/&.^L =wpeA=k/n!U]LH",">~V%%!yua~`</4 @)a#:(QT8wYJA] A3/(G4J<3WZSKu Qjg! <%U/wXLA1)}2gT","=*<g|^ixD#;eA@ >0Nxu/_v,yH%3y ?8-,&m(L)Ce3+y","@A0ao@xjyhF20< A9z;LZOoE{5*},"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 21 33 = true :=
  checkedWindows tiles 136 21 [8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+7) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top7

namespace Pr657PaidOne3Top8

private abbrev P:=PaidBatch .one3 8
private def batch0:List P:=paidGroup ["&11~37 &12POC &0N5h[ &-4`hC t)BQG #~He`# #A!)*` %})xFW","&:Pxl #6I-t h@sx $^DC8h #@~}]' %?Inh' $#R[Cx #x'?l","#K|(p }snt ;R?TPTud7>2DuP ;khScm^OJ<3xXu a,8V` $0YEl",";/YMVX;R/lU%}( <'3Rv(F;^:5N=<",";G*/.qbhq<=I5q <?[R+@/'qu2aHm ;_Vmd-+~T-*1$P <X'Q=Wtq's47-4",":}cXg1-pI1zeDe ;w'N;ER77zsup0 <qOPOp]]:q5jnX ;79`h{9FnT![AL","<1T/p^yLxk`]^m =,xOc+EHMo7@Q} :Sfr[0:jhUub9P ;MmgjhD{5:+st(","<I$nGwBc[[LDLL =ECNuC.4am8t6D :jE)2!/S'Oh)~$ ;eCnlTPQY]0jpm","<aQN}2iy?L9,;, =^lN*Zs}uJ6)Au :(@wu8IZH-#9gm ;#$<eq$<Bj^p=H",";{wunA](~B:%EH <y!0TK32#=%q)i =w7M<s[j+H7]&< :=*!'`+Io^4Nrm",";8`P;bv%_'TXYm <5M|p.h]Ee>yB0 =3No,dYGd-oWuH >2`LO.DU>F92ga",":Qp)7)j98QJ(Ua ;N>doSjkzAKAw4 <L%&qxt3jJH3ti =J|Oa}#^F{[?d(",">K+KbF-AQD:fK( `^/p[ #x&pl #6HGl 9kQGSCJ.d^7hsH :gX0FPK(`%[=aa",";dzxEE_T9;=g^e <cX-sf!h10QKID"] ++ paidGroup ["=cL198It*lH'Qe >dSJt^s-eB<</L :!F)FsyuLJ8lHe :|A7Ux,u(vqtDT",";zY.y7S=TU4O{, <z/4uR.>URVBF, =zyonPq,k]4l@D >||J)vZvx}9N:}","a,073 :6:h:FK_4W>3Su ;4*>fAkdOJ&,OT <38BO)H&pp+9:P","=3c;w?9rz8`Yxe >5IPEj:BNL~S/$ ?8GI<1Cc.{;$|D &bYo",":J/I-v{GyeCW`( ;HpEuiLRv>;c3H <HtV%x<m/iz_!$ =J9By,EIAZePuL",">Lw1{%aX2zfwDm ?PpHNI,NAy<W`i &bYs :_$*~IM1arH|k8",";^XM(3.B?oLx>H <_RjXj1UK&qG>H =amIzvP}f@niJ( >eFpR>*nskR_3L","?j;Gaar:Tw>.D0 &bYw :ruiqy|xI_J#@T ;sAT7Ym1gB_0IH","<u1~/[&>g@h0Zm =xCP|c]T-cs`Fm >|tQ*VQ'V[?F!, @%dFsyZ&hu?b(T <7`s",";)jJeLNb1lOGKe <+*[G$M~06tg-< =-n4cLx(%Z^vx4",">1wW~Oi+QH|wyH ?7D2_ox=:L,-mi @>/F)4Bo|R<t4( <7`w ;=_,W|~JvyTlVu","<?pcVK/mVh(|8< =CLH9>lnATP>_e >HM`#<t_vl$nv0","?Nqq7+AR{<ur[H @yHb:?~983dF]] h?a` h?ll <7`{ ;QRkKOP4_fUp-4","<TXjfrn[}[>Ty0 =Y+[m0aV]oG'|,",">`$g%*#6=Q.)Ji ?gAQlChi_-bYJ( @p#DMdqGEN@(A4 Qjfw ;fGL?#!{Fs[78D","<jAqv<OKG/Ok'0 =ogpC!U?y,=n;P >vWn&t.jb77@}D"] ++ paidGroup ["?~o3C]2!A{NA8e A+KC`|Y3XLA[%X Qjf{ ;z<.2RQe/#a[CT =!*y(d1:n#fCh$",">(F&vqJ)7F4VWu ?0.u(a:A)Y<7z, @9>qxuX8%l;)'D","ACtBs7A|lJC1f} Qjg! <10m&&$Mtmb_vq =6q#8-p*7SwXs$ >>%:Lc>oS@&|?H","?Fb|*MEuM?EONe @PlRP1!Mf]'ms$ AJX2]EJOz&0[;8"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 24 30 = true :=
  checkedWindows tiles 136 24 [8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+8) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top8

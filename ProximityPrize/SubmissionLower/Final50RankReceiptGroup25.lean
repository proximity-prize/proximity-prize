/-
Nine-factor witness construction adapted from public Proximity Prize peer
submission 657, commit e07f14a81dfe2cf1bda985e67040ad4d31fe81ab.
-/
import ProximityPrize.SubmissionLower.Final50RankReceiptFast
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Final50RankReceipt
open K1_13_1_1 (bandCount)
open Final50RankReceipt renaming witnessFinal50Fast → w



private def r25_0 : List (Chunk 25) := [
  w 25 56 0 190403 190903 25 2520 [],
  w 25 55 0 200340 200902 30 2975 ["?VtewS*D'OEgD)VAzQTd0vA&`r1*1J-fA25IWg"],
  w 25 54 0 210277 210902 36 3530 [".sq+#!Oo`Ve-^pfmN{t:ZVdnyV;T&4{y.fUXg4Oxc+Zy?Q$:1Al2S0IKw"],
  w 25 53 0 220214 220901 42 4081 ["f5Jym!lKg8>Yd3t)GdmAym9;ShBYbcPW<?zJ!}h<<kalTPG,CCTNLqBD6mKw<=7g","Llr_XOk7WHh-ID!"]]

private def r25_1 : List (Chunk 25) := [
  w 25 52 0 230151 230901 48 4618 [">E(9(x0CB^DAYHjG;'2VN`82sX7z]F.q>k%gTJ0Po|O>yBdRwJ=A[~z91AIt/e!B","#-T8$|V8T8[V6ba|P>aC&mXIT1WB|f~~ohOn"],
  w 25 51 0 240088 240900 54 5151 ["bPem|hA<2XkB'/#tZv22f<:tgU`H*qd<OzoJ3f^sn:!yupF&ZS7KRuo+N=);}?gc","8HH)8urh;e`:QXY3WQj]!::s/X>*I^qUl7m&#@({u%%Ci>$'*m=7+2h"],
  w 25 50 0 250025 250900 60 5669 ["hUgMsSkr9~M0h)UK%.)Xs.d.UHFBccUCuYlL]2<rZ~j}MLP.@*(<8pfu_QM+.=+6","1v:e$N&~e<88C5.Wh|[7hovdYB!>k<<j/StfH|8sGNZ636u#lQ#[hXynr5eh$6l,","$("],
  w 25 49 0 260024 260899 65 6086 ["9'cDf&|IXf-eO-$F{|1AGi)P]%cLtM_5p4OThVJ3aI:a1or9nzi.FC0HV&Y)n|d6","9z~.&AOkR;)`Esxeu<.r3Gcf10Ed%M`hiW_tz[o,|>;(A@.o?|XkKD`;~bY(a!b#","0hYCT-RzSE2mR!W&r"]]

private def r25_2 : List (Chunk 25) := [
  w 25 48 0 270023 270899 70 6486 ["pRjdETd6r7JXC^8Ry9{QT0EFJ}mQ>X8.h1kv9+*8/G:m~6zA[,]x2o3/69gW{>e2","'W4Tm<,g>G*V@PhH=CLWh3)3GG!OJEl}5w|Zb8=g]T{OMw<7_Dd[fe.+,eu5@_ao","%0y6c0pU0_Y:`_R);Q:!]g3vDf7$%M]shuQ2"],
  w 25 47 0 280022 280898 74 6792 ["v{6.YeCWJf/ODaf=%Fb`#A*;>LGL,<>9:yX#&Lcg;?YEJU3id|omBdH+a8chPN!k","j'Jpv%kle}74^HKc)YY*!R'pxW?HkJm5TmC;{tBT2W(t4(_`{qFDLaMoF*s<U.xg","/_%J[!:2rS>X*!3kA^ipf_zN>qCSV*n3}P[mn/!Z6S"],
  w 25 46 0 290021 290898 78 7082 ["WuqE*|<<+TU/#..(Ru$)Gpbgan~)Dz%FGfl5!S,WOwDc3](=s3$p|=0p>I2%]e2J","^`Djd{%|,6sCE8/U]fg9$m!=l.:aK8Kh3&v3!gSR<p(ose#e=:fV$D.L?$ubDD8g","5yFq{}A31pLv{)vZzM@R2.;t6[F|B[,u]!hN:lc(&BV*`}1sxU)q35lK"],
  w 25 45 0 300020 300897 81 7285 ["'Cqdb?Ril=ca9snSk3jSy}-eHZ)l]d9ecZJ,}uVByq:(Ki]/qx)'0=&jlP2A~6QF","Lyj@'):dCF%C;6Z(R`ONEx-i58oxw~!;N-f4g^9|do&)LtmdZOuCm%vi)Hct>9,3","GQ7K#$%|$R=C>]W'&C7x9h1_HO>;OhrXG)JP^%VTub_{YapN7xKgI/>TZNu;U~r,",".'lthZ$"]]

private def r25_3 : List (Chunk 25) := [
  w 25 44 0 310019 310897 84 7470 ["5dQA,|Oq&BNo<wj~x,;LDj&)!E4>fLhpKOgAqQzAw5Zm(Bvt~5`nO%~k`Sr^H%N*",".:ngu_&Y[_t.i!Lw/^3WEa^!N,,|)^nRKn2}K]N0,v+wflaLpW%^-0s*ahgxLUdX","[4'y;apl}[,YH)u%?:{}ctY9zgbtO:9.AkeXv5G7Um*g$//m$|Lui;&nc^:rQYM_","=R}!OIT=DVb8"],
  w 25 43 0 320018 320896 86 7575 ["*.':ZHl3PX45Q!p#t=OSPR(CJJY*%7jC'0=w2b<187y$^[wAvNg8d~/e2Jx,VTwZ","Jy=0`F>4u>,-L<(a)yw:C^N,s[H&2etYstyD0|rw*3Z{F!n5agoZpR0ckNGO5{6U","(Ioy(.2%s]'L(QSwqerE/}(]X3G>F[S9l9;g=zZ/yO<#DnQQ0J,o9Er_L#EcH*jK","YC`0s#Z3Te-QGJOISGwN"],
  w 25 42 0 330017 330896 88 7663 ["B3]6?T_SQ1p[$Nb;aCaCg]AMoF?FY&2E-qAumv.:[)^'/0:aJQD6g4g2eN-YO7Z{","AuaYL!Qi``QrR'9DqeN#P@xd/{nJ_LnJqrzdzZ=W^}@016ElOEkg5&W`[8G([G6,","xFCcR4Uh+A'Nbo2v>Y[lp4gTSlAys)bT#n,{9*DS@*x8!BX:gR`L_-U>2Pz4niE;","#;E1)t)#8TC'}*?I`vg_Va]P1q6~Y!Gd<"],
  w 25 41 0 340016 340833 89 7676 ["ELYbQj1`T$3Fsi8@,|;v'kGHW,Lnhw>xj,_>^oeg?B=tMad}jJ}75!!lQR{6)&|.","F;u^#t|]322dw(n}zY3[SU&Jnlr$_gEA6_[nYFAy~G)2^i0M%SD3)OPi!yY?<pe%","xHE.W9b@Q/{X#9R{'DO_@i2TVkeo&a0NyscxMm2w?a&=2Yu0%CR~Nm/)PPCd8&S~","#VNU{0F[s5.BT%-KV=1*;8f1EG(=5T2{"]]

private def r25_4 : List (Chunk 25) := [
  w 25 40 0 350015 350832 90 7671 ["&xb#Dk6E6!,Joa'f[qaQSI90)qhMSgL8;9>U{:/i}-^C!(+6b%2/wTxHB8L.@vY6","+l/F,7(F$L[axSm?J1b#+:@n!RY<$KMcgdAy&w#^$W~w+awt`QLCWKO&MP((ejL)","n[7lE-q01f+99M~sc7A9sfw[7rCw4h:{N8huJQ|d:D-b~/JNvLK9O}XXx+q|8hyz","#!|oF7h-7]s*i%Dny4h99H^337;7mJqqOU9"],
  w 25 39 0 360014 360832 91 7672 ["N<3BD~[/2PVLPL?-C1QgN8c<lDg,~k?Y:k:D6rVS/{Rj^zOFv}l]yrwhE2*AN$aB","~2^-pacT.pfLa,=;2k)R<h]&|jAl~Pbpte@?,J|O{p'-/r}uCs&9J5-$PGa5dfz^","4zp$!UrKT]K92<`ZSoHVI*sOFV9La[mWP9<SL@:Piq>*}GRMZBA%n;jqU=~cCCi4","#+{5MA2C~Tq}j*oW<parGJ#El3cjv%YFb#G?_RK`MF<M"],
  w 25 38 0 370013 370769 91 7580 ["MhMsm,~d&(-c|97iB/E$13tCNZWR-^6r4}a(O;y*(|=<HBDZhSCG;?_Rv^k/<gSN","if!S?'j%1Lg6et@|qh;r%QtgVBt7k=X*z0.63+#m.*ewp9X1H2XGwI_488dIG9vb","/$9J[WBS0(7mfL}k*B.EB9;eZoB#RxhhNyGOAu5(0*7:yxrhipZ8BtP=<Ow11<~e","'N7:oqfBv@.:2_YK.],%Tct1cRrZ3a!LFvIrFB&R"],
  w 25 37 0 380012 380768 91 7494 ["~lIs,8O4?|qPX,l,nG?o7SS85[MsVWz/5Uy?6j>k)O}&!FR0rt+-`lKkS@NRxF<R","'3x?Ke,6PRH|uz`V,@|yZ`I^.bW2-'/Xv4Q>|X3v|dj7(7<Pjc(i{^5!,Lat2[pH","KkRa0=#bRO#cB%F`paw7FJ{K,XL0Q:00KYFH^#L[iXzel{fSY&|7vXD~+Z{94BfX","0RPX26we!';oEm^Gv;P%`%QOFT~],{5@[HeQZO5!*"]]

private def r25_5 : List (Chunk 25) := [
  w 25 36 0 390011 390768 91 7390 ["R!uY;xe7sMg][~b&]L{>/7J^v9e/D%EaL5iE3*!4LJ]<I|:HX5dC+PMEtbC5~e!J","!33JnM(qIlP#KlU;&-3Le74|{5ETyE]J`U:82<J=*y!GgrL0O,'QYj-1JjsY+De]","@w23OzM-&GJw?|$dY/h`Si<)t%NX}>$kD0T4tlUmao|jZAfi+=C,NNz]/c~}|!QL","#BsM2=>8~1`30SX8Q#{#-Xr{'P4kQ3R&*$3)I{p3$9.36!bu^"],
  w 25 35 0 400010 400705 90 7225 ["-X#^IJ^P}7<n}FHvHD<2<0-~>e|.Aae0hp@J]7l?p#ZE0C8<-J]J<(2}9+N,'P$R","$j+1@[Sjh%0ell/+tYu8a+n!8Nz.[N5Hjv.pSM:X<~3&#d*YV,qWdSHSxelXEzPA","kh$nx4lO+}I%u(rsvg,yQux(knb3^weO#7o9gNM<`JpVtE6iF7A4=bNon64qv`Z1","%L|?>:90ts7,&A}]M%Hbsi#/']2`X:H<Vny<Xdz~!KbUm8Z"],
  w 25 34 0 410009 410704 89 7037 ["aZg,/l,DeUH'1C*By}k5z_oz%Zp2)S{X9rtd($g*bUle<q<VZy{-jL3US>x5t0:k","6FTs^[0L7qVt)StD2-Y`mXKK*c!d=UFfm8EWz%od5PSd#2Nyh/9`C$|JgI]v=6pS","ybru`OFHWe;PWla4dAr7_.afFb$%XQG/~eh:4jW;YhQM8-.z*!^(q#!/27~,HQuR","&v@c0*mD7>?uT^ecR+GH|g-4N&Sa_IMdj7o`hiB!4)>2"],
  w 25 33 0 420008 420704 88 6864 ["m>[[KJ]]s&~hC{{4WN!>B]aFaKxh79hUKlkN_8S[&'em6S}|0#:7ME;j![rJEg*J","]y>ewsl!|/-a_ba5Vq5$%+(=>U|g_;m6Fl8n=+`AbuO(l<lv@[?Fy+.N>hNTRKNQ","a{GO_tkh4QU7x/%|va`[BsUTC*sLiM!*WfWY_Nu?eG1W24TZEwN06c:zy5YLqr(f",")d`.LKu:Bb:JgzG+P/vqRJcK3`5gAyc%n*>7yVondXZ{l1Z$1Z<"]]

private def r25_6 : List (Chunk 25) := [
  w 25 32 0 430007 430641 86 6601 [">@{-j9/#O~BL!zP50:a-4}yvvG?+CSPiU9<ZLH(eF'Ob#=H{7765r-BJz&3)fqic","!|Fll}?z/8/hqA}:#.Jh@>0b4b'9(K/eWw/&Z]YzI2{jV,?DX~<t$E`S`~.bGBz;","!X1lY+'>1,B<LCOO#)vN>AQMRkUW?I17!T2#XdvnevIDe45oeb}R87*]4!;9UaL{","5~PXx:nDG]mgS`]?b>dG)Uaq=D7'aA(CLFEyU;IdT*Pz(s"],
  w 25 31 0 440006 440640 84 6351 ["2vzUv1r{0fs-Zzg'Yyu83TRHP3Q$x+:nL)l%nXWN#Y,~$T#A<(ht[g.p`LZ/[?]B","9n9+m1^7%]XvR],Mlnh6v,]pA!j-iKA:^yL{fyt%7fOFBT]AfL?c2<Ns}]t`#YW)","TY`Nx{J`qDX2bR76e88tkPjca0a,+oeuy)C~6wP/;37o&g*lq{JWpq3.rrF',>$3","1+NEFk-^Ji<gH-e<B4>nKWU0ymF$TL#idp1S5dK"],
  w 25 30 0 450005 450640 82 6080 ["f<Wj`K*bt#PO:AD*x?d$1&%zFyowzaU^^L+Vf*53Pv6?-b*dsPwZAYbcC+G{,PIF","z-`Q]vK00[k$$`=lY[aSA5hZLubxtSVF#'@&d-/pqr)vpv~/qMBi3Y1-e8)aCsSb","fo|cj6F[8C]j&`9}d[}--`rvWr.bL>_U(Ten7VxTd9c2O>MM0<KxVv9.M'/u^4dL","2`+`ht2KDr?r*ZMBgOaFC]XNBzE0!lE?mNi`z[I]r&"],
  w 25 29 0 460004 460577 79 5763 ["Y*1bPXD=(`VdV,NMwT^ucCH83[%'wej7#%+ml0>[G=:2dF55_~o,kzRk)oJ;}ZUV","Eb92V1{2_13<M`v+l93VlhnmV6Jnts)G'1qz[}@1u<){8.`JbFV,Q%1Cl*q37CSw","uX}I(H.!wS-Y{u'#K3pkK(7`(VuZyS=@/KW~/dEI6_+.IN.Sd4Yt/Q?7&Kq?lePH","Rkfx5I[lU6i@$?'dDP4iF|SDz5k(,3I%3y"]]

private def r25_7 : List (Chunk 25) := [
  w 25 28 0 470003 470576 76 5419 ["PjU7M>}_GBr?|s1SNMbV=~xU_?MxuASlOaUJbr`5GC7?e7J^DwcO_HHN-N`koTaB",")7<Ljq^`RZnZ>n>#u(:3Wj:gozQ!=!6:I$HPKES{]W7mePvK*y*o?.ecY(EpAej8","f{GuqWAbmpH3JhgQD-&J.]nnHwkrRV?bNfI%aG48-rD,$?-A~p+gD=*We6&X0>$S","#_@fg7&ZS/>=H[B2s9t+O}6}T$"],
  w 25 27 0 480002 480576 73 5098 ["d:!.I,>Rap{*v<gi'oyaU`,oi&rJyY@'h5!{T2q4'&E8MO)B>FjsvMMTE8>2IawZ","Qb/)UUn2oW29+K;D~e/U`3GycT8|7hh-n9Ri2qz_wsFOVrU|h3ERybLz3.{?Q2ss","8+F!8'I$!TZ&^5(!T*:dQIlcG,gRTuS>$^]b%x0RuBcA$`>Ep%+jKmu4NBl&vJ,q","%C$'KNMaGZj-Q{._(c[A/3zRZt"],
  w 25 26 0 490001 490513 69 4691 ["V,$B&Xr)Jpcw!S~a%L,R!cvSe^=B^=NaE2|*<kY.ARF2`X/'>o*oPP=}9<M{_bE&","$NyR0ieX1Usc`HKspe+eM$/[-cq.BSXF]<Y-kb|P,N0+N<]vm[<M-|L9=?mEA90Z","X5D~4mIXz@C^LS|g9-[h@yYZh=)j+*iC|Y^R<KqO)svgQdqF0/'ew!P%TA:<4=VW","~B-~6N9ZJs;gtV%>6"],
  w 25 25 0 500000 500512 65 4305 ["_DqXVXN2RhnC,?(gaW:=,1H1|DHCrvWS}bjl&{Y:hP@q3^mG|ZUyeU-y(l?/tYWo","SGKG2?r:74_mLOMZI%aAEaf-W&xdIDs-o9@Sh|Q!%&w,VW>2F-(E`C9X;umg+WCr","6{<+DjSRr+^taPoy9nR9CjBHuJh=x:*IgD39Ak<Tu}+VJ{wXb+vSk>6Ui}@bhdiB","&Y`-S}"]]

private def r25_8 : List (Chunk 25) := [
  w 25 24 0 510000 510512 61 3894 ["{f=$4!Kq{0,uZ3}DnOLpTfz-.NgHoPS$W,-KZW[7bqx@ge-DN[Urb{H*G5q~{bgS","[7l8yJl6GNg6U`*x9hFbdh2(u=ZX6+p0W+A@)/UHnluv`NEo|#l>A<}XDj>[_E^+","]yW?gSL[>Uma&Gyu2q+D-Z6Y0oo;UgxG`&7--?eyTq+%00N('J9d{KW0G$^w5?='","O}:s"],
  w 25 23 0 520000 520449 56 3453 ["pn3wliy(7s3H}VX;1PgcF$<r~x|j(>etsI^w8>n-*+%jj_{4xurqQgD=e5cUb7&3","b_.bOyHVW382;Z_Q<W:mJwN#;ZL+?i_T5%eWlYXu4[UoW+CF7@Y..ii$R-I3cF%`","2z4]Tv%0SL7bY?wEV&b7bQE7`c<i>J8A^N*hKvo6r_:CJVvF|oqVtvjTc"],
  w 25 22 0 530000 530448 52 3083 ["z9%}kI^4@:IaMfi2J%<x|*oi:,3Ws^J=rJ;(koNYMK`a]2-)(LZ2FAPii!mvs3#G","k8%JP]Pr<z/%vEuO(T-|3xyi$xoL[L3cqmub<RL2v^0QCaV6T6r!d,b'8No0h`<>","qZF/z|GU3J@]hFSs#Y8R+1uRufU:ffw^>b:Y^,`+jS)[v"],
  w 25 21 0 540000 540448 48 2740 ["Az6F|rJUFu_.B-{VDcKO:dyAL[Ns}{d-*L`1!Zp/},2LS+7_[m1$eX{)+e$z>*&C","vRgg'7b2v'u/7Amde4=OSKP5~02bl/u_%BZ}<tWw?jHrg|QbVaqlm,/&<V[GO*.#","#;S(=M*qhJ;^SzgDiyql3im*7xA98'vFA~TB<@e@!0"]]

private def r25_9 : List (Chunk 25) := [
  w 25 20 0 550000 550385 44 2413 ["%NC`eB7z8W+.u)iFJ+'b:GT-OHsuZN&E/GsZbE|cS,F.-JSrmIEXYgZo$^+T^#-p","_hU7Gv7N6s92GOf.lc_/1/HLf]ycOXx#@3lNJ5g[mOLd=~kuTX?M(]<`Wp'[ddUA","+%_oJnc}5_|>$R[H$X]y*0%mqiWU&u0m"],
  w 25 19 0 560000 560384 40 2107 ["~Oog%q9DMr4o'j#_udH^6gD.dG@,}P/V.PYnYAO:1*v>qK42YvI5{()Z^6H]JEv/","`gf('bc6@cRxX_dmb`;;Gv2a0tZArfqN0x5Qz/.B3/A=J_#3vC{YI,4gU~w/ZrRM","Ky7'9/e&0[Hg2&R{OF5}"],
  w 25 18 0 570000 570384 37 1866 ["f*bk,3!q%kqLE.9/N+DS?cLO-X~SQfvw;g>O&1Pm@/GYo(W1N/d8+9OePismAxQ?","70PCfv2Q6:gZKQd=ZEs)s)/c~qXw*3u%p$/w[YOU,iuilShN0>X#%B;{!X=S&;/i","(4.0%0%*rm8v4:yvU"],
  w 25 17 0 580000 580321 33 1598 ["ohYvp/U9HT=|c<#{;MOT12.QX<In_;4X9xGomE,^iv+:).s4s`Y]&<3n;xDHpDWG","H,B8'c/$Zjl4=O+Z<_TBL:~lMR9@G+8fcW_&cCEtT`r}_5'8G^E&2-j=H7nj~v},","/r@t)@"]]

private def r25_10 : List (Chunk 25) := [
  w 25 16 0 590000 590320 30 1386 ["#GoKAUHQ*T2b#HPAJ&,EsvyApD}&1ldqKxxA2{V>dfea$;x:LM.Rx9rWbeP4<D$[","1UlPXJI7bmAY1,L10kko,E++MWdS/GuiA^[MU+t323H}Ltic@`%Pj{hq(R4}"],
  w 25 15 0 600000 600320 27 1195 ["#%1^1JgI]sy+f.gIwjs.#gtRowc<8*~,!u_izG]|Q&.[ApV<D,ua`~r_/@a>~/px",",~Dy45HAgHU,c.t(?+^#xGD=J`3Lw-vG@x];)nZ{zZeYa=A=e})VH"],
  w 25 14 0 610000 610257 24 1013 ["}KxZ-'E'+5Bm`sPnb!8vW/G^*k'>7K(Z%Wx{x2`bW>nGw9'l&>#ktcmdm=~m@b8[","0kMp0wFLidT54c@7/yN2%xgm^r1e}5B~pb+?^ZcU${Bce"],
  w 25 13 0 620000 620256 21 846 ["4m{7d970?:vvj-/c&G{)RWI3GK<EmV<sjR4N[J%`0';y<%YsM#0_GwT:M?BLuZ;7","$/<ck.YZ=[9Jix}]+6xl^%5|6iKkuhYO2"]]

private def r25_11 : List (Chunk 25) := [
  w 25 12 0 630000 630256 19 729 ["S}YSW@+}P+*kdm},l4b>F,wVR=9-f!4UyfKtJ>E*zE0pRJg>jc9A+7gF+qlK7D#x","G=AFU[apW3tAwWjTPDmT$^{]_$4"],
  w 25 11 0 640000 640193 16 586 ["1gxL57IJWJk}r=,:`x0pVgJlySFSU{+O(}@(+p9om'^>2.z{2R?-%exZu0n{p3Tl","'qsJSFg;G)/cffj9P"],
  w 25 10 0 650000 650192 14 486 ["iT|BH%n[Tl1K=vhdlDTt<~W;ZD9I~,?}5:3GH9vt(Tm0ijc5D9ffd,S3Q?CvP[.L","V[8pM,j"],
  w 25 9 0 660000 660192 12 398 ["#GM,>@n~#c/XBrSsjODw~nM.px!Ho{9=<-f+xdY@DXzmO[(-u7t^|]wWQR=z-^Yy"]]

private def r25_12 : List (Chunk 25) := [
  w 25 8 0 670000 670129 10 314 ["&O1;V}7ZYT^O`WxTpYyLv.0:O]wRhVyzw:w-B6Escn_dug5Z0$Ffv8T"],
  w 25 7 0 680000 680128 8 238 ["0P/?Dmz[*j1[;/m@*<ASRvy/2:Pf36gb[HGhJX]0L]/b"],
  w 25 6 0 690000 690128 7 198 ["<+7.RM_N[yUJenKa{q<yu+2;G^d=R30kMZO-+gn"],
  w 25 5 0 700000 700065 5 134 ["=T8=n,^XWd)v:5|V_g[mIh:74C;~*"]]

private def r25_13 : List (Chunk 25) := [
  w 25 4 0 710000 710064 4 101 ["#m`^!T2'%:UPnJMT_A/noJN"],
  w 25 3 0 720000 720064 3 73 ["#:@p4q{TRZsAz]*!&"],
  w 25 2 0 730000 730001 2 46 ["$?-~/SnSDh{"],
  w 25 1 0 740000 740000 1 22 ["I!pT_"]]

private def r25_14 : List (Chunk 25) := [
  w 25 0 0 750000 750000 1 21 ["#_=0n"]]
private def chunks25:List (Chunk 25):=r25_0 ++ r25_1 ++ r25_2 ++ r25_3 ++ r25_4 ++ r25_5 ++ r25_6 ++ r25_7 ++ r25_8 ++ r25_9 ++ r25_10 ++ r25_11 ++ r25_12 ++ r25_13 ++ r25_14
def rows25:=rowsFrom chunks25

theorem good25 : ∀ r ∈ rows25,good 25 r=true:=rowsFrom_good chunks25

theorem sorted25 : rows25.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks25 0 (by decide +kernel)).1

theorem mass25 (i : Fin 57) :
    bandCount 25 (i.val:ℤ) 56 14≤(rows25.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks25).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 25 (j:ℤ) 56 14≤mass j chunks25))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total25 : (rows25.map (price 25)).sum = 224840 :=
  (total_eq chunks25).trans (by decide +kernel)



private def r26_0 : List (Chunk 26) := [
  w 26 56 0 220278 220903 36 3617 [],
  w 26 55 0 230215 230902 42 4143 ["-#xq6d+EA0lgL*CL=cg',`PqOR{AgE;qy2/)eB4z}#EW=fD8XqeWY.8:"],
  w 26 54 0 240152 240902 49 4772 ["u(GQ;+_QjUL(82NT{F]2[0lPS%_pHBP{HME$~%JHA?K5W}}2',8Jg*|_Y63q:)ak","$+en{9!^(Si:6|39rUO"],
  w 26 53 0 250089 250901 55 5298 ["%)l<<feYW2FNZGri#9Sa'6Br8oSThSOy[TG<~%[6x>sxS5gukD'XeZMnRX}HM=q*","#(9v1t9)],a^&_6D)F>VY)4ZP!M5x`)?}Kn]azRt*ijubvz^4o"]]

private def r26_1 : List (Chunk 26) := [
  w 26 52 0 260026 260901 62 5912 ["-{q6HFJK2plLo()pF?;LmVfpYg<Lh5^qg4TU)>N]0=sC9H9+~lBhhA,w!XQpA:%N","eO+IkX4,0s_EUFsK:,'#c^2t]>dF}@wnQM?Dt:o7}@mUFB.GOW.4=z(A/.Cn=>WI","#g&1a%F_D"],
  w 26 51 0 270025 270900 67 6319 ["0=JAb/*P#rj#I40g8/,/vwCVen-IM/3^%@JndtL6|omd%Y5WQefrAcW3^P|.Y%h&","L+bXo:>?0W)84+Ee?`Y{J|=]yzuXp]a5:m>]AJh]&:pCCT1OffyErBjhd|~Yyl.%","_m^)]/;_s_{B1x0l2V-)'Da6<#w`v{j@Mb@_"],
  w 26 50 0 280024 280900 73 6814 ["4}2U-?)'M9ysK3WH/'gi`mE*'[S&DfY0RY|5?Awu4W.t(3|(6e9<50;@%f2D0x{:","avz_aeY4-E)sgH];)y2P<v/?c2Y&-KfDn?Y(*4VdovVoCpI*tzIQ^7!~OB:9/U|#","$#F.xi;*~'!hz7AA1J(m9DGpoPrbC3sZu=[ojo#~~`r&uY"],
  w 26 49 0 290023 290899 77 7107 ["$V?P4chn:52tkMl39T!MIZ(,/!0rO?IV[!'~lk*A-}d>&Z4-lqN9~FQorFM8?Q_k","p`FX<.:uU~+c4f#<ik5sA54x{8{-rMZQc/:$NxFj>&UVvV@R21)#Rx~cX9di><Bw","'!A=TZ}DN9%dU10B6UHn(j)e&:Ysk_4(D,VL^p:=S2{r->cj(yO8bGf_?vr3x?"]]

private def r26_2 : List (Chunk 26) := [
  w 26 48 0 300022 300899 82 7489 ["YR<TPs^L|HI7}H4lT9,*XB_=jAt'=HxUjBSR0$g`?k,'-}=sfM_@nT.EN2$#O^vg","Xj7P=xDoy^ykfWW>L&G@@qP8>2weWj.>rDIfIfDrXV5YQI7gJECh[+|>Ag8b/Ks9","9F?TSF-_Sd2};~k]1&J=|a[.:L0aB39<=A^)WeMD?g3vijDFHoyKOhnX!)}Q)%0V","EKb!mNGPb=OJj4d"],
  w 26 47 0 310021 310898 85 7675 ["O#G5VGNXwf|wB8U=-?~Lq{^joQ8Ybw+35O&H0)FYAqxzI&F%z/Am~YHf'7|c~yv6","2Os04g@-|*ed!;a^.2f1VpjsypCL4X7-1f$1QvACw_89yK1@pJA0}3'qv:M0eOYH","UL&h7Lf?&e@3v;&.fhO[r_Ecv1x8.^z&!4*5t[~)_#e=x!@Tw+|9PoKE_])rD]|Q","XK.m6A)8-zH_pfzNi.)O>#"],
  w 26 46 0 320020 320898 89 7950 [";XPMH@UO(LSN(nBg-kDjMsVW*,Nit7KCd7'o-_RAK]93Mw|$o2z3AWHPGR][ydec",",To/).@79C'd+^IU`G#h/Z7t/05K|,*nuCl$6NbVA/8x,>yoI?c3Lt_;Z-9|Xi6_",">e}9_|MZ<Tt_`1I3edSh(0]>D}8/0wU`j0YHI%!+Ih/fChXs/FP{z4t7SlET#{+]","C#|HJ~,<mHmK2=x%1q<Q*GJ6;dLO|`]<J"],
  w 26 45 0 330019 330897 91 8037 ["v<$rmDvWhII,Tb?}rl2=S-@n.1Yoykf@$/cr)6Z|KBINMi*x9B9oB&uC^LP_4bvg","F$gkoM^miy6bG$N^*OOElUz$>!6F5Pl3vn2Z<zCE9g|4I|lEA]0DF`wMK7ne$0??","^O/I~S{g7K$-!26lu5w?qO9H>F=,2FxX|{^,|5GKn%UT>3ABs~Q(u2{yM`>$+wa8","$+j>yhiAao!-)JH&@'#}cI.=}[Q)Tr>1qQ%-si{cJ$Rv0q~<'H"]]

private def r26_3 : List (Chunk 26) := [
  w 26 44 0 340018 340897 94 8210 ["yTH@Y4**n{5<L1`:BOqmNi.$m}=1O.}VbQ.Oz{Q8AG5iM]>Y<'9mq{-BNj8KTe2J","9dd_}Ggl-6GgJASe/C46(k<h(gWCV6Q1=:39;'D54'aV<W&#8t[MWbs]m@wC-yL[","~3[(X$o&vE~1&-F/{p^)uib%!j)CdX?b)adua'&)2Cm[D'Y0^T?|BctbMZhr.`E?","@/kjV2)T=4IAVhhV+D@Lr+mvm(Iw}pj8(@qn05*MP~09Eh[yrR;|"],
  w 26 43 0 350017 350896 95 8203 ["X+E'fA]bVdv0v}tpK<<tMy+>H8VpS-gaYBEF&BDv+ftO7h<<guMuBx/%wNxP]4So","d=?`R2f41w=y5Zl]cJ3R9J>Ng$%}H3Oy;XWWDxk~hnh9%[-}>Z!wT_|D-%D7vy&L","*DT5F:j-+$?=d54}Ckh0s{7.2/X_!kSLK(T?~EMLD8kQA(+*~fpI7^^%$Us-cJtr","0Bxm%NUW[[E!Y/{G-[ia5[PcGqE^^5>HZ#wIHrD^/8W:ec3,G6DLxMvh0FJ3"],
  w 26 42 0 360016 360896 97 8282 ["Otk%9WFf`iFZ~>,>ABg9OVbaVnb~@L]p]=A9`M@<ph$4VL/wB5(8^4H$T<]yO|;_","Y`J!9emNNw:Q.Wb*Kbrc%c/t+prv)8~hjg?``>IkN1T,oHZ`_*6CGSO8dyYA!}=v","'ZA!#K@u<k63YJ3E+-EVb=?%>:d<BDoJN[8T~c*Uf<3}{LH2LX!T,fvD-/=]c:h/","_c7AZ;(nf-@LtLKeK.6+*~na@`_+9$q>;9ME6jlhJupQ(E34aR`'n7FI6mk>/!.1","6gV*13<>"],
  w 26 41 0 370015 370833 97 8186 ["bR:<HJ=|YVZHYA4'0{|KQB|*&3_Q!Oj?ts8PZofao=*t>n9hC<=_}Sj,`6TNR,'>","zo0Voo6d)67Xx{r&l}$HS!GBN|f7>K^-jH.ZLaUv2vtSIC~;MxpnQ}2AVjDlC+8T","h=86i]R4S1NmrkmOQRON.Pd1c!;,hjW':S:Zwez5~AET294@<YMN9h<Jo!lVz9Se","T}USl}3B*p<z3xmlm*?ZWxs)?_C9oo1Qc~vEBfsuP?=Eqg70X2ZB{fuj_p/>e;$!","&b$9Exk"]]

private def r26_4 : List (Chunk 26) := [
  w 26 40 0 380014 380832 98 8176 ["9]ErP)X0)!Uy|HM3~7?hJ/`OP3p+YsqB8ZX9Oy{'nB+$PbFSqEji?C#zMZ8`hgw{","}Y(`Mn!e;YNWalX]{/WYQ`76Y]he~AVyx!9dYs4K,zY6x&J{?KGp3jc!z53A9Q{^","jK.d9Lhb-DTK:'<S2<^.K2#500P0K.|sfMY#o^*8'xRe*dwTF2%Ac>l/}7ZQjp6&","N')g'5!l_W170<c/n/hoDbF?.-$yf;mv];_*~ELz*1HlTH&;r!K)mT97G!(/Pa~s","9A@O$Fv^/Uym"],
  w 26 39 0 390013 390832 98 8071 [">.]lD87117bR7eIGu:}f8QX5&<8lq'dsJVHM8|{?~y;+TixNZ~j(mXG~$nmyY`16","EPf64,cguUuYbH~<XUxU@|vX{ZA4_!F9dU7Vg@cAXIVeM;UB[L}d1R/D?!d8%`It","pa0|A=.GMs:dVX4$21Rx/bRFegDvO6P[9({CDj1aMe7yBW9crZ5)&r?!5mWdWl}C","nDCEeo)2.kI6U']Lvi.H#KEQ0S3&YqoR9rjFvFGx&,4}690%QSKZo5Y]/rv|Ttat","%48XD43&$spss%6Te}_SX"],
  w 26 38 0 400012 400769 98 7975 ["mtIp%)}^(MfMSth[sV]G*PXURv4RLPg19it25x]:/Ni)]+`o}w2t/L/=!4K|V.7_","U6mss1B^sT-D[a0*90M[:_t$#?xTjtGe+bm?TPjP171L%W9B=5^<jY`rI-<`/;9t","bg*+(pN~1F-@Gi$MUx*I.{tl2]0x]`SM$k#p.ji'A1${qL.$ElO8j23nc.PXDUS+","43.e_bzMG1m#6fKsVap_CH!V:8K|ykNXJJky-t7!GhGp`T#S,nntg#,W%wQ>`A`?","'cf`g'r~C(ZJ{..`"],
  w 26 37 0 410011 410768 97 7789 ["I1IeJGNAJv&~0+nZmlm'W*#rMF*3qBrtpDQ^,50b9:pHIpa;~v&/EW_?^!1q5$L2","/!6ZhgEEbtx0H_,(wi>iSwbNz.)et+_xeP0R0JTbIA<9TmoH-gu&msKy`?Qlv?=O","6=jJ<HiZY|nC6m|&d`V0*9DQ&xU'yNrQ5QC/976[@DN8<|$OI$?N&@<wk'F,o|US","m(Lh(L'8|,Cq>5Y;1mO)$wkF%Dq7yMaG~sA2e&km>i%55&J{4F[XnrKmBOr!q{[[","'9j@N3?lb`o]^u|0?>"]]

private def r26_5 : List (Chunk 26) := [
  w 26 36 0 420010 420768 97 7684 ["qB?8x(Pgf5AQoT5H'ikaPR4e_~_6/j<O<CNAzM8=>)a@;x~cIgK2VJ5ulbW8}Vus","cr=G!<Zvs>67dQXjuYx8S=kb]VBNKq4CTml<IHMQ,M=ajkJ.#;M5lpjCz'Wiu/v$","|IM)a_]cb)6,'[w6P*zhWSOH)A@]})}T.WstXhMs'HQ'C7gSl%7h;CmKKx`D,l_Y","1Ei5zP0tLl=ad,|N@p%vOrn)CWLuKt#+Dn&'}&}_@u;D4PIdU)Ja+<dcwL`W8^vR","O,~/94[s|v<5]>h=i@Joq$<vw"],
  w 26 35 0 430009 430705 95 7418 ["+).H)N{B0uzR!jA,BkBbp8AP=i_>3&s`:a@n?heHsNi&>GJenNc<Ukw;CeanmbFJ","b(4y@sLN`3{IXJ!EDGaMgPS_sfnVjnkb*T~{0}Jp?hUSz-O'>JP>@eZ-a|',Z?UU","w||E=CO`:c-W^:-K1@,xt4Q}`EW}}jL18yjqx@smNUyf9S&3S.z}t+LtztgZSSyK","`SoNe!3IJ_Z`I/5yCee*he+W-bkgOsS$U0YwgW8WDV'y.ajSY4,0`/Gg^l2.fTP0","8/QNsRxeScO&NkOR3<"],
  w 26 34 0 440008 440704 94 7237 ["4xJ.EK5Y?T*z+zVp4Rs6JRTo)>d98a8X'kRj0dy9r+it,vVI9=X'@GQxMcZ?pBx_","{Z[f2,wip;.O,PyBoFi*B^Z!(GyN5aj34X`*`:VI.LDsLHKfc6.9+>5xSMCLe1S^","U-OUxst^hEmbMBs[ozQK:+f,qRAm<nQ|$2D9YfF(?~L]`rr!w)zU,|)5II41U(4|","nNK11mCH@9It3onkrA&IX!agh%D&s(JO`Tb8m+20UeIqjGP3|m2,*;gBGK9*m._#",")A2(=tM;cHt{~zbBqa8"],
  w 26 33 0 450007 450704 92 6965 ["vI8hd2.q^#R*q^#[pCH+}9g|;5eQV5|zSH7%/>(>P2:</,nEn#e{quGVEq8:o*c*","X11Ztt[b:I-3{sbL($x<pDq::C~ZKL]F6@7G6p*@.h235T1NO{B7@*KYRvx<jz}>","]}b(KfnWmpH/!NBYay@bTN&+L~(pCQ]vcSH#S^xG^q0vEW_Zu1$QTnJrp,4`b%S1","weIW_]Mey|,JP#-c(gXlyps6Kk8byxm!+C}%-Yj:(0ZG|;0bmC?F>'X0SP{y)kpT","#JSi!:+Xu1HvQ3E?,{PUILQfBd"]]

private def r26_6 : List (Chunk 26) := [
  w 26 32 0 460006 460641 90 6707 ["5fgmu.HZqg]}PI?~ml@QV=of?evB'TkM3!@m^a?*uOd2pi6K>gFqy8sdEQPGYjpN",",QsP)@jq_!'fGqya-LA&U/C{/2{E1jBRvWC^;tnEy1n@8Y+0EA>gdVQV8t)<+:@>","QzRbJ]}I*0}D:.4a+u)i$_[/A6mq8ax4Kp:}]`RE/-@kV$4Vf)1R,GGgulZ)c+A7","/c>ON4pj]3P:><m+SMv)>@d-*K3`lj-2L=q??M}z_-W]ek>nM--75_2uL.3c(wd,","g1mI{SQj1U:+?"],
  w 26 31 0 470005 470640 87 6367 ["lWV=%4#=g`=L+w!n4&3)Wl=1CzIElk}A.pKz|kt|c}Z@RYsqu4T]p<Z_lUdS$4Q&","fr&`l)m=lIi*_5fo1ece4i|BhfwB;vq7%m0QPe`.8o<qMc%VO@7ubG!GShbiN&sX","rxFEIa6SWC1NS*8*ePtU,u|ALgVs7E=yT4Iz[0FmJoOTqwxr<am{^qfcop!c'a?x","Un]%j9&`b`a0X7]^sLj'@-)rou9M3l<`wNdWj[Yd.=/X83nG+6i~n<H&*:w^Q'('","}DGk;SI,|D}wv,"],
  w 26 30 0 480004 480640 85 6103 ["%-z8uJ7htV50.z?q/pxx9jsvY8uMa}'V#BC]lHD'm1J-Qh0D!Z,;3xx!<W4:+HDR","@FEYGWUb7kqd)9{,=_9#:8u@E7s~s${XvEI6*XI^ODl#h6AYk[UN6wekuz^*H8FS","-P+Gb,rHO>UtN1iV;^qH]jM[CC;JlAs!Po&1;yq+d!+,+{5y0;nsnh0BfzWMqYUh","Dj+]QNg.oftga:.-z-MQh<3s$(_jKY+,/i>Q#@CZWiG3(v3bK`d50Fj+AoHu(Vq_",".rd&AS:8ZbX?v$>"],
  w 26 29 0 490003 490577 81 5693 ["z)i>^<zu~V&^ivPLBB>w~&s3@;`~R%Z`Bcd3lyC=7_u&_#cA:bhD)|kI{1f10<to","5N!=25r{bO)NxLf%0$y$Gj=wdHuh'qyn8j2m$!o)&XU93n@.V0Dj;l6sNbPND-+[","X8?fhovJ-6]Q/*,f_{^O2'$@xE6KvvT]MC+'4wxW__k]3,-(@])[z<2$wX}-?bJ^","Y.&VG45WmqegYtN?Zo80X||dHUe%wr2E~!]D~(5R#AXBuDec8).;W>t1<K/r8+R:","$"]]

private def r26_7 : List (Chunk 26) := [
  w 26 28 0 500002 500576 78 5365 ["4#XR`uSbVi$ua3I3/&$Z|nVg7-pX%[pL@~mSkj4O.BJn,T5k1_CQ]AE#'g>`DKOo","SWU=5XDP0Rg|K8h:J8oJDV[k%^yniYO^F-mFAb`*LO[Y?/)<|397,4a>mNdD3g14","]LF;rTKkkog+O&y.{Q>>tCCo9QB>H!pFgwQgYDUePR1nW2BY6UqZIdKeu/+.]NY(","'<SQJn-,H<C!xy^1g&_=itcW&}:k(c#xuB#HF%vGf#f!$Do.81I^98H)umYE+"],
  w 26 27 0 510001 510576 74 4953 ["j+6/X];hi>2#St~^;JUPb~$~eMD4uY,(=Ve^6IcfwSW+w$2'*YRJf.&OG|XL6%qs","M],$0jn/tDU+-v{X@ah`O)yN/):s/YHN6ytCqE`>2:?;jEku811r@2d)J3M5F==W","PhB`)tFGYC7j&oR1Yi;I{a9o,@w,C8oHJGnRS#'E}^4ndaDhM~@Y2~n<#k|R=15P","1wmBb<|~eWi[(5dLhx}_h3T||aHuZxEKM*yoFPNP%zSn*jm,@iRo,%cuE#"],
  w 26 26 0 520000 520513 70 4559 ["cWDR;XvmjwSmG)%Ak{{I^|zi@LvQ6zQ3{ai!|)Z^0=`'2^I&#lmV+Bid$$<CgAXR","rHz*='x}iOp`/eDD+sT^N@hH#4rX`g`,y4HPvk@E+GX!AUh_88Piy['oMxc9{p(G","c^?LPyoQGt9AVAX9y@eXYzg1%:BAJDYsd=-8>4AQwy#;s`66/V7x4B@0FS`_iaOn","xs}}T+^-U'*;USgzAkKQ(?~|1D~ZdF4Oh/ZP)dc^V-"],
  w 26 25 0 530000 530512 65 4091 ["PB|2!1aOaDY%AQE2*~+41f+CNqobMC5asu{NBti!`h2=sJILyt*ZG!)R0Qyn:s4;","b:_m:q^<%[5I`E=1z~)od2CHh{pN[G([,<3w-?Ep~rNtmRY4lY^(|Aff_GOA;aZL","c+YO]o0l@G-R]ZwoLnG=N5Pj019yAANe2ZR[g}6K=4z2qlsPWNi]uoUP,;Lv;uKL","};k|u|AOYU!<L7t7Cvfkmf}bI8ELK!JD.6)A"]]

private def r26_8 : List (Chunk 26) := [
  w 26 24 0 540000 540512 61 3695 ["|C!xQEq+0vT5>=DXUsHyJ7j/wqikwmG0R#)R0o1u8l[xYolbQH}=Gy);)OC}*-<+","Mc:rjP0+eQKg==]|#NIfw8lDv6@dt!aK4aAg8wj)YH!Vl%ay1{NPn+-Nb2U=*V`[","+t>?vyxtR(YW'im7_yE0,?vmb#6$]5'AnY5j|-dNT@tm.ALr)l}'vH|m)R5Ud:gi","Kmn;zieB={4:+sLU2*}0)>DJwp3c)P9"],
  w 26 23 0 550000 550449 56 3271 ["fTWc:rn0Rg>!&d}!C|v>'l6r={ypmlax[Z'O^f{]?_.|R[7m0ampqhTU!;h;SBs3","RtSynL~;4Y~M`JBJoU)):UKprgG]q%?INBK?thIVv}_~t1KG4%p_%t5ra1`nt!dn","_IW75@'yuW'FD%;QR8|v{VHk]pj)2!S|:g@3:Afw'IpJA#u]n?]EO(v.T,!(`MO!","*PGIl3B+$XO,ZU"],
  w 26 22 0 560000 560448 52 2921 ["~_S!XVnZxwl0hF:Z5=S2k-L[&)6B'3.T~TB~H2%M$5Jurqng2bI^*L-5%GjNU,37","*_*nm5rs3uh#skkdI.;*GuLi|1:/6kGbTMiwEIfeCg|y'CDm'KH/$p9!_`RhWukt","IIW-lZ<XS<`1v2zMPJc&}RAH)vlph[Vk-)[|F>4Z'1HUnSXR*RY}%rDswFSLU*f]","jRu&EV}p"],
  w 26 21 0 570000 570448 48 2593 ["@P'Lk4qkf_M=#z/JcMNAZganiC~a'G<:;%+;Agw0Mho^YoB,,Yf(:Ehh7sznU{/G",")K0pocK,@U2oPd6>QPu&}t|XtXej]tx[?aNcQm@rdkO9#^2_nu']xVtokzAJ>U<H","{H[bzof]M=2FpVg<;)j[9bbc0]'P{N)3=[Wjm&@q00x<gUtBF>-wJ5V:HW}`<|Wx","&"]]

private def r26_9 : List (Chunk 26) := [
  w 26 20 0 580000 580385 44 2279 ["tjyupw.}p`*n1<x9]AA%@T;+?4plO(y=eM=K:3'E|L{I?]fHLXm*%A3df7$'Ac,[","jf'Opm0%#E[;TJO6tpy?[_rC%_VX}{a`&LfiT7i{.[wsrJ8owu~I;r_uG9Y/E0ET","WuZ=n6lc(v_cta4BpXxfe?e'x!WWP6FF)*wv2P%*<Al2%tSE#c"],
  w 26 19 0 590000 590384 40 1992 [">?z|4?u=d*hWg>.-]){wo}#>1a/R.i!mHsEm9y4T#~#[{*Jz${>jweuaA1D]]dy;","7r!;A5fRZ(0la+0@<zHf4M&9OvLqB6ck5rv@}JRd9JAr}_KAV={7tb0BGnST@G3R","]U<=(we[;#y|I=xu.2bML3c@Ou'M|Y=lwUBG9b(_B'"],
  w 26 18 0 600000 600384 37 1762 ["OV&~kb`G}56azEpH<Y=CYE_BUVHR&p{UBp+6zs3o#ZQ]/|8B1;O8C%,tD$7J1LQp","{GzP$i=s^QaL(>&&*%J&:4J%,zuvdgV[U$n+H$.P#/k)+80+jV6@&Irs'&Vvk!d5","#,iQN`#,[zNZg7(9Q/U^6@X&z#VnYn-g4X;Ma"],
  w 26 17 0 610000 610321 33 1506 ["9uBB7&yXx=popI3L6{C9p!X,W-yHvj!+'w}uLI8_wlFDh=n6ZGVVr@n5ZTI<<mU?","?(tEkMXEERZW85LPMeS,YeFL}ikV|D.1O:&=vND$V:w163vGixy7bq^@K2(g:iu(","#DoV&Fp,C%Z*2wE>DJ^V"]]

private def r26_10 : List (Chunk 26) := [
  w 26 16 0 620000 620320 30 1309 ["m8^l)/~Z%pT^H%hd[dV$)oeBXntJ0l~@?}sk~>e]PIory>k*nX.s]GyU<dm,QMnO","eguk%!i!UNk@T<4G/e,Ps#Uw;Yw}*HdIgID-(7j_U8!YY%/gO)W1L#W4RG:^R,>K","CAw5BB)5zRA;5"],
  w 26 15 0 630000 630320 27 1127 ["HCA?3&cgm<MYs<'cMt/%B>GLi%Ng[:[0#b4!pie)g#2/JN!Oxa.t_nOenx=^Wss3",";Uf])dB')Z9jPYGS;t9QM*R}&Q1N7NBRrlnVui0PF8,_l%G$8zoa007R_!^-uBfQ","*LM]w"],
  w 26 14 0 640000 640257 24 954 ["2}2hp8^id0lmr{.,.]n_KW7vpVzqQLx)E'RrDuuTy]SX$w@)4K}</XOO9mo`9jG7","$9[?/el9C<g6qr$|YQJQZ}ODaxHQ2|nT+yJRg@?6gOFKk2Eeya#fW["],
  w 26 13 0 650000 650256 21 799 ["0A#fB@]Mv*#Q1o@<D(HqBLDDlE;lf[3w^-Z2>4Z^Xx35x$eAF/B8ig<4)CQz=GF3","5[*+Vw,m9H<OfsATUUqq+_2=I>A(0f`pQ<C.1/S(KM#M5h"]]

private def r26_11 : List (Chunk 26) := [
  w 26 12 0 660000 660256 19 688 ["d69?FgDoaW#A+m2{+T^!jTd!fisiLY0m<Ov^jdv_0eQv)M/v|N-n.>Q#{r]pFGp7","1oXtNfQia5j:f1qj#_!]q|5J-+.&h{x1:UB<5"],
  w 26 11 0 670000 670193 16 552 ["Vi`K[R><!'AlQc;jH-}lwNcQGyJ*Hd$gU2oXe%Ll<+$o/4JL][D#~SfO#Sav4[<D",",[.Z^n.0RM+4k}!s9vYjJVf"],
  w 26 10 0 680000 680192 14 460 ["Lh#-v8qu_u87DzY8s+I%!Z3wO!WF-?[/EQ/awL3k?#fnQ8&29A[|MR^'o^[?Qj>m","$tQFs5F,vS5C[g&"],
  w 26 9 0 690000 690192 12 376 ["1Y7O;Vc1s/dBC!:bt6ta&a_uWwO_U61yp;?r2BO}$0$rx.;~tM8DFKOrLt0HC)U)","$Tb'f?"]]

private def r26_12 : List (Chunk 26) := [
  w 26 8 0 700000 700129 10 296 [".O`@R3Cy27.]4=y/[oGQ.+.EN~|h&^)]>rk&h48kqORCcnv!zuoq7$F^"],
  w 26 7 0 710000 710128 8 226 ["+KFZ(G'7ipq;_zJw4hyp)%kVBE-|}]lz(K2EJz|T2H(>_~#3B"],
  w 26 6 0 720000 720128 7 188 ["kYTQUE41{Zowl#Tz>o4/+U#;kWem@u_6D>B_2{u5"],
  w 26 5 0 730000 730065 5 127 ["=T5d#s!e}HiYO-sS*9O){S&2S-;[c"]]

private def r26_13 : List (Chunk 26) := [
  w 26 4 0 740000 740064 4 97 ["'%j$EHieH9(3q!@9D~RoRdYS"],
  w 26 3 0 750000 750064 3 70 ["#:=ad.bIc]hQIGF8>"],
  w 26 2 0 760000 760001 2 44 ["$?-j-5l(2)!"],
  w 26 1 0 770000 770000 1 21 ["I!ld:"]]

private def r26_14 : List (Chunk 26) := [
  w 26 0 0 780000 780000 1 20 ["#_9?I"]]
private def chunks26:List (Chunk 26):=r26_0 ++ r26_1 ++ r26_2 ++ r26_3 ++ r26_4 ++ r26_5 ++ r26_6 ++ r26_7 ++ r26_8 ++ r26_9 ++ r26_10 ++ r26_11 ++ r26_12 ++ r26_13 ++ r26_14
def rows26:=rowsFrom chunks26

theorem good26 : ∀ r ∈ rows26,good 26 r=true:=rowsFrom_good chunks26

theorem sorted26 : rows26.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks26 0 (by decide +kernel)).1

theorem mass26 (i : Fin 57) :
    bandCount 26 (i.val:ℤ) 56 14≤(rows26.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks26).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 26 (j:ℤ) 56 14≤mass j chunks26))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total26 : (rows26.map (price 26)).sum = 240540 :=
  (total_eq chunks26).trans (by decide +kernel)



private def r27_0 : List (Chunk 27) := [
  w 27 56 0 250153 250903 49 4907 [],
  w 27 55 0 260090 260902 56 5497 ["|1p8]ri:.TVBj%O>FGZW[;Q.)Dp'm.7x^8d_neSV'q?T)7atR)dkm1RYcnEDZlDZ","8-36%NP7_}tz6"],
  w 27 54 0 270027 270902 63 6091 ["PeW5$ILO7!%/YRO{l#VALdC5(cBuEX1jwMM.;ShG4-u8E`,4]UqvVQl3)Jt+?38k","7@&'&LgjQ<M{^<}WG(z!U(_8*js&wJ#qr46%2fgo]PZL@!;"],
  w 27 53 0 280026 280901 69 6589 ["zZd^H[{<R0ghP^IM{N'nteLbB6y-b*R/pY<`g/oVpWlvCsifl<1|Z:>g?h8zJ^P*","0kAKAUh=N,S}r9Z8^ncuL-ZVe%RuZz3v|gDor[G8}*':5{Ggn-Kw#@m[ZZ'FdgK!","#^sM0~=MP&!r=xzxYFi6F=)"]]

private def r27_1 : List (Chunk 27) := [
  w 27 52 0 290025 290901 75 7072 ["kAB`K4R^Q&YmWui,<f%;3Vetj>t5r8!hbClIlf]h>K8*,K}m*3h!ra)h%|TB,ZM6","#XO<pr00U8HB,ub;w^(wme6{>UZ%Ij*~wr3s=9ki@&t-Htwdfy^UgVAid|O0=2bp","Z(OW/Kx|73oiB5&3h)JB,lgkymg6r20l&FT@6VQ_?&n9W[zHNna"],
  w 27 51 0 300024 300900 80 7458 ["w(d8XN:48`:9rJ')yg)?|0xX5BT{UnFSw/ghoO0v&s'/l({2~s12IQ<J6WG(%[~&","Oc?RY.McmV$oaMK*?(5%#Q!k#JTH$Zx}jq2>;di#GZ?v*Q>4/~:?v,$q#<W7Xgw4",":BMAodKyT<9TH(1W<LxKr!f|[{L5FWycgfv[!d.qP4XK-.xJ#iuj&8AaY@xpHhMD","/t;RZ~Sq.&[E+d3}L;_D"],
  w 27 50 0 310023 310900 85 7826 ["uv]sb0~wR99Q`!(k%xn#FX|EPSBQA<(>`CZB^3VX|/JkVQ[*4,5SEli%gCZ*kE<!","HMs!.LnOe<sd^4Lf9E~?`&V]ZK3HXFb7QXqss/Ehb6k9.Jq}o&#SbS@*@wYD.-fv","2y]F0`qlIa9XfkT+5=0t(Z1X60^95s>Q86'CsMfV?5R,bLU_ki;)./l#~>XA7*?h","'<gifXMthqR5#{/~?i||wZdt-o)&h"],
  w 27 49 0 320022 320899 89 8103 ["LF]vhmwH::TI3n|IlSvn4?J2'x_5:l,phed2U!u%fT4'[7n2_Xqsqll[dr8=c?)V","aV>x66=_3M2c|h<n/I;<JB*}Y.yrI3Ju9qX$x6|qGQ<RLd(A_ypawZ-WW(0SwLd;","^vXtPNlW1|p@tZ/P(pSTB`%|8i[#!IhvqiN(fFsaE3CQHx_tGk]3lZa_)z&jtSBd","#+e7_x4}:Hnf8G2Ey%<S78xA?We3M-_o(A![_^(Q1GiRXd1?"]]

private def r27_2 : List (Chunk 27) := [
  w 27 48 0 330021 330899 93 8362 ["?!e?Tg_[{%eM>~)(*7NP~nV*QtBr0<p!d#JSZq?_Ww12Jaei`o2G?_S/[]91pjz6","Pl&S[iz?>^,2DbYN'h{fMEg-WS8AHsGtE3G*k]-//oqTgs6?$&XV#8y*>J9WG]Pp","h/L}b3}6fnm%BQC7Y40EvymPlW*0!,.7.vmP)+S;~B4.c^}h1Mo:r4ep5fccfG$f","BDZxi(e&zzH%+7^GH-7Oh5B3opsbs>jMMR]Eg:g/NyO(QI|'*.DYhD>6n/}s[7~"],
  w 27 47 0 340020 340898 96 8536 ["ntUt[>xNg#1;4<f&9w5OJc$:g,LXg$K)AgozE1Q2XF|R~dI85E?o/$,.q29mIXh>","GJy?;B5fL,0p:.iZ)~?B3(hkBR|&dkH[z0TDhkrh6%`$g-ao4eyZRHsKdk/GD3Y?","XQ?S9^_VM4U6k0So}=~K^SeBhI~BpDRLlxmxyILc;C$W_e2AcnnDB}L~S07e<ork","5ZQnH^'pC1IOk@XM^+5TMDUIRvFkj4wo7uY]IdPHP9n51?XbkgN~Vi3p@RTelRlf","&2~@48aal"],
  w 27 46 0 350019 350898 99 8692 ["*I2k1p&F(z7uOl$X'wwJL=}M:cEnv'/>*4Ta)I9i~@c;UQ]Me23n4<s=%F7A<G/.","p'm)N0&8|>pC<z,,kJCGW!c_(3>,iGkpR{cN&'ivKL=K9BxDuX[.}gT%c84W.O`J","5E}-1M`&>1=a_baLi'QzYPBy=Lxu|DN8gN.b7m6BOBwgq+DKe$rCQQ|`Ts7VL$F@","b'lAOP*niCK4<:FFGs@07h+m*:c&cQ'M-yg/%n]`uLyl4w0Xo,UK0QGuz>D&~.'k","NkPkq(znlScHSm"],
  w 27 45 0 360018 360896 100 8689 ["9wsa37K}vgtumwXVnvs+4<=ker=o_bBM7[y)CYFS&?evFBSi6c3N{jQ@BLcVLG{:","=gzz*V]UwGJD|ov?{>A*W(gt;5C`Anb'(p8=L-{}n3_UTiy+ys8aUIyd=u1.3nVm","*ohI)'*BA=Jv-2ad]TUH2e!e^#Q%etEd{UpmUT)v8z54'y1egN|!>[6dtW@~Bt2d","#MMP~mb2?*:{ADtyFo0Go@C(v{_#3BuQfa-;bFXoN>xhIQ>}b>E@{g1TW$dOdY^(","#M#U;1]8`ZdwT6!Q~JMLPpu{6C"]]

private def r27_3 : List (Chunk 27) := [
  w 27 45 100 360897 360897 1 79 ["&gu"],
  w 27 44 0 370017 370833 100 8596 [";`9fg`|ujpdE^&mXAVXsN{lV5E~:g[KE#cZb0H]9hpB0Xw=`p?qqnW:/Y<w|&:n6","idG>^#(ZSLbPf18G'HNPufT{G?Ga}JU.A4az/R$Kc~/!K31F5AFtWP:s1yL*-F/n","-]Xz/UK%u*^%p~-Rj5fN-Xlvk)M(GLhDL[f+;3V*wX9-&y]/|5_tIV^~WU>_}<e-","0}q%VmS@'P:HDL`P]Sq0d+>G|GJ/C2^:esn6J6KpGU)s4'?XgsIRYkBIl!}.#XB1","$Y@Bx0LK}z$,pN.d^n'w<I"],
  w 27 44 100 370834 370897 3 232 ["]^Mg)6JjW)"],
  w 27 43 0 380016 380771 100 8511 ["Z/y^.f2Lv:(m;h./45`(j^yP1bb)K_iZo<j=0l_Y1&MQ3W}!cD'}XZx?BzAqx:ZJ","i]Q6M)DjOY[HfyuH(1k!Py[6Ry_~nr%24YQJ-M#?Z_tkFb|i'TAfK7I#H/7f<LF=",")%@kR9*.x>%po'!/SRRi#kw%LKhCrvS5n3cgUwG6#-VlYUt)8!]'!xnX#iBNw)cP","5)1EPHldjHeEy]sp16!V6BQQEq&B@}Fu{Hm}$-=R$SXsydPnwqx1@{KN%Ny+%J}[","&TV?kTK)M|h,?-`|>$C2@:"]]

private def r27_4 : List (Chunk 27) := [
  w 27 43 100 380832 380896 4 302 ["$TyVwQ^FD)*AQ7Q.'Z"],
  w 27 42 0 390015 390769 100 8410 ["6|?Q|3d{kHbL%)r.=*DS>.^eD3TR`(1S3>%l%H60L9<@n|<.o&|f`U)_!%TRsK]B","'P1rySeFdf?>fq;QYh66XTQAjJE<O#*==~5oYy%&g>u0Oa</4Va|sTpfDzF@|>kc","P||_%,v?T(6o,=0z1o'yKXG%svhrT?=m{Xb~IWWB~[*p.cBaPJ]~2%srB[m<4LAx","|NfQw79HeU11^s.::CZZH}qnR#v^ix2w4Lqx(D5snrpo2)'g02k[YD>]S6h,uSzU",")41~D/^~7/Rm%X[=?!@|Aq*"],
  w 27 42 100 390770 390896 5 370 ["&Kgh0L#)DIB-!U78^q%1Y2"],
  w 27 41 0 400014 400708 100 8320 ["[e=DgI]6K0`GgJ}b]Px[]:@F0ldG;]>SteDjd=/!z03KI[wruZQS5t1ed.b6O<(!","6R)BqX(H}u[yy]0iPW9E`q.;.b)9:s9XRLT`H*VJ%{T-'~^[PuHlMuicN4{I/9eC","}(c4)la[Wp]0d]Klb+~<O.m`uYAB2uBnq@B%)4Fkj,3*?Gb4y$pAht6,0$+bc75n","g'EV3LEfD/n53[v3]pUQL;}JHm4pu|<%zx&q[)MzZY;k?Y;UCXYZSvrM@$zf(Py-","Tu00b24cGX![dXkdT~R;[)ql"]]

private def r27_5 : List (Chunk 27) := [
  w 27 41 100 400768 400833 5 362 ["%Jx=v|/p3z+qta^!d0Y_C[Zv=c6"],
  w 27 40 0 410013 410706 100 8209 ["tb)UdM*Rgawz^:T^@0)b)m=[/%PiO8i*UW^vW26${jkTZ0qa;cIEJB2?HdaQ-6]R","m<<r3d(qZuYru~!.4ECW,1_8)ws%zPDK[:S8Td']k0:~RrdEIzsSz[735SGI<OxM","fd'I>iPPtVA.p)%k#0RFMsJ%ys%Nnkn-VT#9<z%3EeGUsSgR5aERNAe1zBA]vo`/","W2uqle;%hCn;&+Lo|:lVdh2kC5Q)oZ}3@.m@)QbVC-^.%&tzNU!`+a;34P:f./Vm","E70OyYD/|Nf`tqbt%8b>*^8B"],
  w 27 40 100 410707 410832 5 355 ["#2o%!t3S<_}Z$2]~2s|qSHR]eN"],
  w 27 39 0 420012 420705 100 8107 ["[:VNL([Cmoi_0iEY+&Lp_]SyC(s4fh8y`C^w~|-T>63#s$FEp#q1>$p3RpkHO`y2","9*dO/1RTcwZ6^hc:*.:D~}l)Fu'Md-aUz?P=@-9>Og@W>~73sKv%E;|}>jC&3A]p","jH$-PDTf$CU-bqyDIj4f*Ibj[yU:rdm1@:49P.d.~TNdasf069&JuLcF6|aEZnJc","Rvw}c6}n]~Fc5B%iQr*K^ml`Gs@ktN9xPXkx+2J]THsD:V5[~M#R3Y(kr=_WsHZ<","#9Koh89QP5||}R%5REWr(Q>*CGRD*E'R"]]

private def r27_6 : List (Chunk 27) := [
  w 27 39 100 420706 420832 5 349 ["E+RrZ49;%XWHBh9SyTcoh?6h"],
  w 27 38 0 430011 430704 100 7984 ["Z4Aw:5;=e;eL[Xy$T:Q$Vy>bOaP<jvM`b`69z6=D_zXRo/MC*43/[;mM_.bR@nDB","xb-XX*`}=Cd4hTo#jf:VO<+`n+4C${oi.j]T$Li'.xSn#xkd7T}Jc_J!h8Z^`Y:Y","Wmnw-E%C9omt4TxigVV}Cg9ZLUA[F'k}AHBfj!!(JdsqT66}}yHLfLv[QR=Boe2D","~l_m-TI{9~f}he5O_Gtao1vs}B.5S_n=a4,?zm^`Bw~-S>tP6Hm`7~${oTINAddw","n6c*=p(PDC__A>-2w6Lp?Ts8Z=Mh8ef!Wg(6"],
  w 27 38 100 430705 430769 4 274 ["7q*,Dy=)^_VC449/dURw"],
  w 27 37 0 440010 440704 100 7872 ["T9+D$bClvCgih*^]).xZ15HR*yrynTc>d0m7?c`YwJF%C{*k_G.]tgDvS_CYP?(2",":C:{YD&cfI%pJg+iqM$*;`BFJ|=+:|Z:-,b}>pGXwo4ps1q1'S?{zP*Ef7l<*dxk","R;?,y:+T-c)liIVgR1jv5SE`j(EiyjI)'&~Bm;W>'EGNZeuY_2j%aEi1NiCOW:4>","sRgZkj20I<Vd]_=a+denBC=(:%f~5g2`;9e:g7N5P`B%e`z.CGd'0y$f=MIn0db0","S$,THXVw7Yaewo!wWFU2Sb}[!(&g#3m*!$pqGt$OY"]]

private def r27_7 : List (Chunk 27) := [
  w 27 37 100 440705 440768 3 202 ["-+}j70WTM>[):lQ2"],
  w 27 36 0 450009 450704 100 7731 ["4YSx%RK2'_m%FbRA5I#JMEteBw'x!D~|HNHEal/B@jA0H1)}7pfG*G1^>S8^:Lms","*'R?X$v+Tg_k.L)KmFHMPHJhzFx!B6Q-=<<w%l5*4I&!&XBLt|kK5@=~TlD8p.%-","YTH78DY-$qW7hvphPQ5wz'd.K3URSa[i%-Ra;NNQ7acnqZThf'>tnB&_$f'*Va'w","I]mG5D1`Q1qP+p=^%_&i1x5-D>*{#55@[(Qc`WTJ'(d!7odzQ`ZjE(O$|Is;MTU(","-Ms.=zvln2_:J&a'sS]K(Pg(RH}G@~r1<)!#ZPL+u]y~|"],
  w 27 36 100 450705 450768 2 133 ["%Zi'&7Mpm!G"],
  w 27 35 0 460008 460705 100 7608 ["f^nxYh6c5zNj.,j`au)`fhI2X}Bp,?sUBZ5Jr|VXSYvPM|B+PWlOO^+nU)xmWja2","<4:dXS386@I)*`6>9~TY2KwRG|,q:WHv7,<e!YUCsNymiD@_F_L>>HJ=T4{]&fz^","t7vep(V:]$,P8:{xKT$s-WYB*m(&}%$5[nhC#Qer[wZ(2EG@$,E@=_xkY=Li!<KM",";evji)S8~l1%Ryow6#}_H&YjHvJ<1})BT-3q&K?Pb>'m+/,/i7WOW-'@$[V617D%","C.%(9[*=41iItS`t.X8e.u;HT+=zXPW<iC@LJC+zcK}1{1D&b;TIJf%-/"]]

private def r27_8 : List (Chunk 27) := [
  w 27 34 0 470007 470704 98 7326 ["`993IfO?DMo3~;@Z$aaZ`K`EH2,^0V^woKXVQ>6)_@U:(P.Kpp=(/5145Z2o!P7>","rXf`%`Ke4S*[OG|+i6mUP`DQ_imPLa.S4CVm[t%#YRZ:AtR)Y/Y>`I]o`^Taw1/!","z<O<sQ,<XYc:kkH0o2ZHm>Xh_^SxR^2]!.=/#|(nl!fbJ.9wn='@g^4ZKgD]BKr4","kw}cib'y`#;h.:gWi>z>PhnBDQv}A?4lgE,%@s0$P;/FqC=T-YE0@AD$FXv>c%x@","OD:V}Spv]#$upHO/Vij0IhlP9E]YFbBZTrn~p%$8,Kw+.(i`ST1~<4~."],
  w 27 33 0 480006 480704 96 7061 ["xyXcj<TlwOPX1`AdT+pTDXEifTfkkX`L!OPaVxQYw3>qB`tn.O{ur-.I~2KTm9rV","07Q,}Z,-B,p`.zJ%V#tPaF$|jH1=tdrsm>g%#w[Wp&sV{!bvt565}D&Jx5x@39{p","}{ADaz#z!n<@}}V4|nxAl;iM%o'rw_W+NYPfYYaNJQ4~6p6Wy&x[-+.+P%-nB+>/","r6./@6+zqqNI{g0fi&T#uGP0yX.){BBIH|1T02:x'y1]7ug<)SCBKb7Gn&/V%3/]","6z9rrR3{QVIA_rb$L/XS?3Mh%[gu![/~-C[.pZ?*WL|P`Fz+dpE6F"],
  w 27 32 0 490005 490641 93 6711 ["C!Jg9r,3$nf[bQh8(ICoN|1KSEzj!m'BJXzp{}S#_GZHT<u]TBZ;qci92;5'ls4s","kn'k.Be9Z0=<H!s^cWRQBLvpxEJu2Z>p6ZVtm7/$:WTqP`X[Cey>o4hy>%~1u?V:","*+f@~0mdl@L@rn9wKQX(&<rrWZtgOQ(]rcDImArOr/CiEqAa.J<F059-G$M>hHS_","MqDCbh./[Ao=ItVlX@Ky4'Dmuq?AN<z%Luh$]q%lx^-fNUwgC}V0&OLg]Q2<RuS*","&IxEdf,k(8J=utt3yrJ+SMWDbHNa%4PT-tY[gP/2jGn'9eCFL5l2+"],
  w 27 31 0 500004 500640 90 6381 ["fHOz+n]NCer}V&:byAUIuA~UGcIHQZ{FjB$Q/i6.&%X>SFAfPAhqa+z,4,,]'F+o","B)_KI&Zoe}{0cvAxOpq/]>ddkd?C01X'#v^:f3tfA|YD[_LhFy5M(2njw3TA%|Ln","D/3'ql]+;GMj7'choQ4}p[/sc;<sSIVRMyV1GRdg$P+T15WLr:8]@7@i*uspqt8n","zAJ'{Rr+$4Hn7c6^GJW6u(#!<T-K:flx`Gzu|do;!rA:-}O@S=teHW5E%+g}*e4j",";+0K7)fAMhgP-Pct+'hkyt)GEm}fexN$Cjjjdq&`8[]sy5R8!["]]

private def r27_9 : List (Chunk 27) := [
  w 27 30 0 510003 510640 87 6022 ["7CNVIw{lIJDlvP>`cXEx+[8U76t,dX+tYPw~Th$9k)nTi.hC+A'3D3`8Bik!dn*Z","Xoa?4s-qe97omI<;M]z]Z(u{e[>`|8AQmH8RI[P<J6vdQgR*$veiQLy1$A6EC9t1","$bnySEjSifTP=xH+:{AUr<LCVK~<)$[QF$6N~32{;ah]M&2g>VmQ|<UiB?[+&Zh$","M<wHLenUX`_t]mjUGqHFUzAM$%]Mp*V!3x]#~{y/,D`K!0U&:x%WcF@ijDw;aaK+","#&aMpIqb7@F7v#-ltGMOL~[bL$]z:ndxq7&C<KYi!"],
  w 27 29 0 520002 520577 83 5631 ["P,~5Q01LZRjYtcB2!RiB7R6v)@Q'0]Yrl%k&U]F<s<[v(s{cv{QlD9imgl~LX[oJ","$qpo{Y!!OFYaDQ4}pr<)zXT*=J*{C`'3$@',JHrV8?T[g23l+fWOTvR}tX$QkUfn","(Pr{~Zf'$stI%8`ib]mR_nil5>w=-_pNNOd-IFhestkq0#]otU]&UwZv1/g9G^cI","X]:/G@fp|(D3[O^<hOjT>n^<kG@!0az~z{2tySX]`5?O([X)VtZkm<-Ns{dQ[S/T","c;dTV4dIn1]{>Pgq;QW+^BilFwSzI[LGn~4qB$"],
  w 27 28 0 530001 530576 79 5211 ["8ap/EMhRY<<cSy6;Vajog6DF$Bpb[YjScJ+SjE~7J6c|bXGx<Tn:'EB(l}@^S3jV","5BT`p~B:lS4y-6j=]>`LReZtwvC;l|nfnSXN4>U>?T*$)sSOc$F(4>(qsa%(!7'*","fn^[>i|f?>Sc>I=j<kT,IuZ[c03_C)gIj/R_hWB$T&<@CwRj=-1vY>L9=aIOCC$Q","V[uOyY=Qg)-Kjdo887E3EgLJ<q}lJ,`UT4s=9(I#O,23m[cdD-Lbw~L[>36a7&^[","$,8H6W?^YO/cz`5.bgrKMd.9mYaqq*k'"],
  w 27 27 0 540000 540576 75 4814 [".I4b2Ml49s2V%IXu<7c4(/D+9@{XuWm;Ismu;&=q5eL3|WQae>,&(e|#/E.Prd6*","<reuN|<RA)NG!f2]WD3CvoT}sO7yf]N<=`xVr+jt@i)o%;Gn4DZ}DR3psMcX5TfF","U2fF8VN9TaM;uk_}hi{vm)-B^xA}QUeuID)t)B+-K'^m]x;5};7^CP+Et4)<1Xwe","D<(t|y?5opfSc~<Khc>,q*Fv.RyFZkIOqkqX#6a;V!/5-Y|PYsK*z}L-T%)?{sco","#xeL&ANTLyL>:Uko%"]]

private def r27_10 : List (Chunk 27) := [
  w 27 26 0 550000 550513 70 4337 ["wu<K=59,n@<zq'X^*Ul,fq`_|f`NZ/(uzcRwZ@`Y9xlU-l^~n)1}7wYkRd&/g[8;","w(/au;+xw}~28z0Q.1+-52nYC?g=w0Vj!:2+(7XI}/Cg~Z%Ovwd!u|S#V1R-GkxU","%D-([w~kMhq.c.ic]WoN,='{mW)P.gI`a}i;H=:T7<6<W>B5ayTwo@lzMmtn2Co;","Sb@Xh[OPCg!'}Fu(,wKp/'QohjAaaxw4))}#Eg`E8K~zO953?;h=#h{@u!sL99VM","#ScEd#GW47q)"],
  w 27 25 0 560000 560512 65 3887 ["bO7ULU1n#62a7B!kp)V:K~B^]/$%f,5$rO2OGZC~[nj]Je`T&/:'N+M,0odRUrN3","4ngxLL`N(xB;o'K(<vdX9?UP!1Pg&5&hXA!>SweJSL:42f5xt$vEDi2<y5Y2!0Bo","|*Jm41<V;h7x&sFSWf@Lq#DJ?&w8w#&s6=2zf!Re8EI4,gm-}x&?p]@I(%8;&4s]","NWp>D+gVKA<b<^<Q0Z1:z|Tua;BWGQNO><;K:3w-K>kK$B[(o'H77Xxi}2!3d#V&","$"],
  w 27 24 0 570000 570512 61 3506 ["SJ+X@Hq~X}g!]qqBmO4;f;{ZBqo#%#3<na)!s4boT?TL]J6ncF^35Fz'Jql0OSs#","yW!r1NiuWi=?w?ql~K4&1Id7^b&;7W#Wb{tZ_syRH3_ASzDC*r+(Y+&xot^s`jCb","n6K;zh}c_Trg&2Yh;[~4=_!kKP_O:*5CZj%NCeW'D_+3stRp_3$OU'@sVlxS2`|T","$d/^*5SU<h5o)vF`Sg!;wBD4`~A/6:_/,GQs4-Ike[bn%Bd3^Y"],
  w 27 23 0 580000 580449 56 3105 ["ff~PG*Aj%IMJZ>c=a!+`N_Z.-;bMEt.KT(W3>pJrLA6:BW-FYPSyeS,_^Oxq|oXK","[^a?aOLrr}^;FrKDwHh6*d|.KyWP`yPW;j`b!x0AP|IE5??mi<'2!b~5bF~Sk9,%","aNiQSNk]_Pv*Kw}c5&[&*TZhD+NAnXNib.@&7|dfs_pBm~<b+'>j7jH0kt8@(Dk8","7S#EETjd@qyosJ:)$6f`oUAb/77Kc/I)6'+[g@e6/U"]]

private def r27_11 : List (Chunk 27) := [
  w 27 22 0 590000 590448 52 2769 ["db>8]K(.w/ok55NPwZ?_aD6Oc?)S=a%41VEnYmOn}*Hd3q9[?ZPx~^i.6D,/1OoS","5ou!SsF2}!>?T)N&mh|L>lf7;^*:]0P2,:/`-JsPi3zp-y?:~j,;QUR4huOgvA'v","s.3(Sr$8bJ=BE|F,>eK#=<<z>JDY|jzw$uhy:,+T.%3NZq$IIj4){FQ]%awL+LT2","*GCCiM$P[#BAAQkgY/sgITkz}RQQ7T(LM"],
  w 27 21 0 600000 600448 48 2455 ["5[uEYpYU{<Km1z2%d~rJJt-n'PaFpSyGo]->9z@wK.i[f]!TI9ZE&kJra;2l{u~`","1rY/MdwY3W(nc_Aeb^NN/,NDG>Ez)JXJfU]GiK1ll=(>?^N@TmRPudmTHxx.U>a-","T0:R=aRAm%wQwZ/Zz7,W;0)-nW@7M53gzE`ZB$V[YUZ&4(JuAv?]`@G4uws7LdC4","%n:|;<VQ>uJ22t^]/"],
  w 27 20 0 610000 610385 44 2160 ["pgpS/@Iz%=!->Q')rjHgx>v!fy=,a}K7hTF6ptVMWbF@O11xbDRJBZ8x8QG9==E/","z{5Fie62=rIseq1B%`#?[0}+;XQdB4i;SE7x'[cBJiL4711jZyKH,&~c|Ilm#H48",")lTb$S3?d8]]r^Q-s.3>ZRPwbA/y=,=1hBA_qaTu]ez/,4R-vx~.4,Eq{QInQo*X","$;H./LWz*H"],
  w 27 19 0 620000 620384 40 1885 ["qld-^V^y4%DiQ3dVyhDy.t<<;:{5z7ub{T-_FM+VD5%p^o+?OAd%s`2F4MxLqy(+","Hvlt0K;uEcY(}-S:#Omd3+jAAR;*hr0QA#jfubY><Inek@eq&62<60=rD]mQ3:?!",",UQ#~?m>TAO[qW4oyq[3%F1&*2ARFoHA1,XkZ&/ta)DHvpY5#~,,{p^p2&2p%|"]]

private def r27_12 : List (Chunk 27) := [
  w 27 18 0 630000 630384 37 1666 ["wM*2k9S33:q79/v@j{-l'(ztT.J[lpxQ'Z*&2;&>O0X/)!15`GFj~<tqdOO?]<U?","c<q0*~;pL8k[~Z$B>7e(;0@qDdpUxnv/'sQ1uljVB|f]1I1Ym}M+s4[r~&gUk?6J","%`g]'8pm**k*Q0fRk<mB`Yc/fS[#cJhqgR&DZ_#8l*;Q4-~oJ"],
  w 27 17 0 640000 640321 33 1426 ["H5^o2),)8^clTK1[OSLbfR,Xp>OF30#L9V!uQO2z+b}%&ZVvzn)5S{MiAp~My8O'","'ySC#5@p{XBKf&1`R]?,rRfx-F6PHR1|6!62SzL0>h+Krlmu~@:o5NPO^<$k6[v*","*65M/S@0d)(s.0lk:tI~X@L{WNw<?zoGMPRDMS"],
  w 27 16 0 650000 650320 30 1238 ["T*#w<+@3{#9q||u[6EAe`@-Vvy@aZp+ei_57dK6O7#l|]9FgP[(O>$T>%YDeDIx7","G^Q_i=,W7i;lEwwRwd&ME~y>Gj[IXQNesZ'I_FJSgd;+Q/0_jwf42B3/veA{;+)J","+6}bX}NRVOEF<v_P`[*FWt7Ffz0M"],
  w 27 15 0 660000 660320 27 1065 ["x<;tM5oI)54]B%=A.2@Ro}IqO!b,/u#%AZ46wm}0vGv>F>$['>By:1Fqsc`SXq{3","U2]9):7GBb*z(ZW]@PBBBY!hC@@2x{-~d=Xi(.jk;Nw(Yq`FZi+*5v]'PS*c{/Q=","#<hF9o*eN'V/0g"]]

private def r27_13 : List (Chunk 27) := [
  w 27 14 0 670000 670257 24 904 ["P[y1?phqgS!UF]z71<Rp<2|Bc<ZMMc1wm3uu*dUGxmtlgKh;!BwGZ5Ot,>*(9K[h","fr>Q6;Uu#RC9wji<-K^Hwy*czRMw2<E{V7ppe~K)MU4L.p{`(;P~}m*9J!%'=x-v","6^["],
  w 27 13 0 680000 680256 21 756 ["{g)=Y3>jjkYK8xZFB2Rl`w~NZP.eeuiTc2eJ~;$q{29Ks<jwC%=b2R94m+<5-(?'","*@S`9fGuOVL9=&QC^ugKMz*j-R;kyI.H^0T&|bW$J&ybo{f8xFI5P},k"],
  w 27 12 0 690000 690256 19 651 ["q~5c'}JPs+GYjom[=dTv#e7yO''GfXQ`XfO+K'`..ndww{>c,.B31FGqNqtf|<km",",>pL0WuBko>~>?i^dv~8H{7SWjC+!,bT5]~TF)K.;f"],
  w 27 11 0 700000 700193 16 524 [",kma<Swv#ndSg$$mJC%IGf2M.y?j!N8,)M{'$4xmY%bS+O}Vw>]3GNic3Hk6)G<E","#[-1PB12<.Y+sUf.0thx(2HEf-6^}w1I"]]

private def r27_14 : List (Chunk 27) := [
  w 27 10 0 710000 710192 14 436 ["QSq;4Zov_lfY5kty/{nz_$TPuY1#XLj6C^c~eYcq,cV!&:>-kChbx}9%]Yd>dV}U","#t$0jv8_%FO!$ZR*,pnc"],
  w 27 9 0 720000 720192 12 356 ["8tCW|c*5Z0l7qH/j}${d~!c^$e9[|~6wj<vthF{lQf,2W!diDGPEE_`$n~qWz]L6",")*mUi(]"],
  w 27 8 0 730000 730129 10 282 ["*/2nDY,ob2J@jOVm(8siXqZ^/yxQJ=yz#aS'H$q<dPD@5#X}K.ppXd41aylDf"],
  w 27 7 0 740000 740128 8 215 ["<=1:C9m<RS@DMU;`<-[<5UGX[vVKfRi`s=]sHjhhdXb,'1K;_N"]]

private def r27_15 : List (Chunk 27) := [
  w 27 6 0 750000 750128 7 179 ["kWH69sw%g!mc:+/vHHS>H_O:sG=w)HDu[KU}=5TE"],
  w 27 5 0 760000 760065 5 122 ["o^^ZKE]6ti]x-iPy_vi'4*5o{gkird"],
  w 27 4 0 770000 770064 4 93 ["'%iRW?winGl'H*%?m*E4&ebd"],
  w 27 3 0 780000 780064 3 67 ["#::R5HH>s_]av2cNV"]]

private def r27_16 : List (Chunk 27) := [
  w 27 2 0 790000 790001 2 42 ["$?-U*tiX|F&"],
  w 27 1 0 800000 800000 1 20 ["I!hrs"],
  w 27 0 0 810000 810000 1 19 ["#_5N%"]]
private def chunks27:List (Chunk 27):=r27_0 ++ r27_1 ++ r27_2 ++ r27_3 ++ r27_4 ++ r27_5 ++ r27_6 ++ r27_7 ++ r27_8 ++ r27_9 ++ r27_10 ++ r27_11 ++ r27_12 ++ r27_13 ++ r27_14 ++ r27_15 ++ r27_16
def rows27:=rowsFrom chunks27

theorem good27 : ∀ r ∈ rows27,good 27 r=true:=rowsFrom_good chunks27

theorem sorted27 : rows27.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks27 0 (by decide +kernel)).1

theorem mass27 (i : Fin 57) :
    bandCount 27 (i.val:ℤ) 56 14≤(rows27.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks27).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 27 (j:ℤ) 56 14≤mass j chunks27))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total27 : (rows27.map (price 27)).sum = 255150 :=
  (total_eq chunks27).trans (by decide +kernel)



private def r28_0 : List (Chunk 28) := [
  w 28 56 0 280028 280903 64 6388 [],
  w 28 55 0 290027 290902 70 6831 ["cvXavc't~,#2~6cRi+Wr?Tk5lH]*d(}Kd[)kyiS}6*5S:fViEyhTExZfMH/NDmvo","%fm?vBPw!MU#@*>LA$WCh^Ne+oJV`IE_695ke"],
  w 28 54 0 300026 300902 77 7386 ["`9Oer=WMc-(@YUG1I<=[IfQ'Te@qg'rf8o;<U<aa3(ld{`E:Dfb<C*_-o'G^cg`>","8ks5`Ssml0?E|PPtr+[##d;NGbZjhCuj;T2JdIczcsd91^9B6T1eg1EuC`gG|luo","(S$D1${M]{YpZ"],
  w 28 53 0 310025 310901 82 7751 ["P}o?,`,Xn_9&mb@m|L0VfR<BgPeiK|-u;3eP'CPc:]$UU?#}Rm4z'!S-=qw(Grjw","`tXPyrsP1B).f#m8rg87%`]^nU/t/azNg?X.'*#E]0x|6K>+Wi?D%0Rm93]v@@XT","t^mYvHW4n7A*DO,+3RQqRJgAIv?=>TRXOYF?B_b$%&k':&i1Y5BqgPJow/O~"]]

private def r28_1 : List (Chunk 28) := [
  w 28 52 0 320024 320901 88 8209 ["vnM[s6w0-H[?sEK2<E[syZk|[n)iEeH(ekN[-3S5ln3mRqY2=hCa?@mRWL6T>5t_","yg>iVUViDtHN[1tCo,,q$QSOI-NmCP=mN^L&W7YhQ|Q~OM&iT?k)z]XLVGD!qtB=","aYrA.j>$PvXv{x+si}~^[rg?CeW[I~O2`%+>6]1Nuy4dS%+kM*EzTG1?1Ae[N>2+","X_ooqigb{&J$x%n[<S/d;=CmBJ-1=:V"],
  w 28 51 0 330023 330900 92 8469 ["fD!x.-e|Ztnd'qh_QXV&'m`O:?dv'.k]HE@oq!#ZAa2rx%Ls92QxN/Qv*Rzaa20!",",78?/n~=QSc@(0:`r=zSBh>sN-j4Xy.~]!A5*uR[HJ1s9Cx6|F;|.EM&E`L8;5}z","UPg&,5TF;1cJvoO[#Ma2+8D@ZV3wsiqX~lmBsy,NrcJab;{|Kjfgt>S'rMQ;zDic","#b^Nj#u/M^SrAX.#|t+1%iD*LDhpkad2ue)c.Dwy)(7A!{2jajQ#(aV';)SCfd@K"],
  w 28 50 0 340022 340900 97 8817 ["ciTjkJ]rhR-REnFlvLA{u3U,U+6I@/$5+)yAEZ=|?zKm^/x$t&I3|KWZktZi_2[.","'Sr`j:*;9=khI|z[vy.P|a[T1Bc5TK}{(bXUx6D~qzywt:yX{.9';B_&r9]R,06I","d`s!]lX6;bb421|T+?'E-8^Y;Ob2vHAi=e^(,+.MJT#m$cVekX+?rQ@/I@O^Q~94","RhB2W(CQ[hJS)IxrthgeyBRMb'F*8?5'd]b+AX_;u=7VU:,XiQ`_PAr3KP$^x}(3","i*5iA2@2cQ_J7!Sqm.1"],
  w 28 49 0 350021 350899 100 8974 ["6xfBW61|q*[A9({>N.Jn)CX=I2)Gp-~%LQ;'w~VeYR'MD[A=Y^(#WU0C]#A|uc-6","8I{+(0T02XnyXC/!hG~->.E9C;GAR*D-O{X.hV@!ez;yHW.X{/uFH/O5?!Lv0zT$",":|Lg'Ni<dvxo2@uF-Q,||hZkwd]Oz|bj&J8r9(Zvcw4D6zLu$1D#kPn##ZYo=[:&","ik<IO~`sd(n;@4Vaz*N3xYbf$RG-J^sJK<PE]~cmntK6kC)zOzYP=*e!&@KMs>_P","7hGMX~g%RkEGT(6H:K2$t~NGHH^0Z(,.e_V"]]

private def r28_2 : List (Chunk 28) := [
  w 28 48 0 360020 360836 100 8891 ["NTM_~8AoxfG9/M&bZfJbg`@7h.P'ee>jY^XVcv)=}%ln&+e+pO8LxmvK~lvh]*G_","x5VqS}-f)A&4}eB{HZ4d#VZZj?1(NslC_>@|Tf8406^>'>cFVFDYrM2UKNxy0T85","Qyt.A8En$XE@sbB/zd,v:P'!<8c?QG~=d(m~t~`A#X]?w;$bQt|b)`HF@r[mK2Pz","#Cnve'@}(WQ,d#l?f1%sV=zzrA|[1Rr%N2/JX)FjKkhj'y(2oI'8y$:!POKfYULH",":k9evYb_!zW]Z!-GP*NdETJ5S7$^CQe'M%@"],
  w 28 48 100 360896 360899 4 326 ["%FuT0B!p$Nu"],
  w 28 47 0 370019 370833 100 8795 ["w$WfkC|Nh^TqN,yy3`Zf-j-&i(y?l[WCS7y[d>H<vAfE8:+i@8'd~S>+0?**:Gng","[`x`lV{NN4-ix5K4frU6j{3=E&K/%x?&Z,?+C3aGXN!m'P}kF4)</T49lMn*5*;G","O!.Giz<rc3zk/mptKJfGn/~<?5i)4[q4FTCIejjCz>6Z%-XG2t5YY9mYG^Xo>#&s","ut.XX[D*.0n-~|4wypp;DV_(3n'Qb7U6rsYQC-7`X9oR8J<r4Z!6ntff$#%0uQKs",",4-Iy;);:a(Z9fVB_gN+s,m'{B]2NL=>@8&X)5)0X@<G3"],
  w 28 47 100 370834 370898 6 480 ["''*<pfK*jt/{_+Rwx]*f"]]

private def r28_3 : List (Chunk 28) := [
  w 28 46 0 380018 380771 100 8712 ["So9DLxli&2t{0t[m$t.9y$G8RD(X2u]8=,85IWP)HdNjI6(@-o%OXsv7Bv5C2czg","o3wk&+<i'WI4z%DlkJq.4DY]K8_rHgi&fQ@ZiI%x`^it#1hO3SvlrS1#'ldy(:.y","%=;$%]t'n^HhLN72M`@.'F'm}qKZ%W@>_a]t8r+}0FE9|-*;}1:CR@8#a{E}(}{V",")c^RW#W-Ul]mkcOl6+H(g5#6O1wB.*H%7%:Sr6_3UBP=PVG8A[0.HFivX;73A;>P","$}.7(k*7A[|iX_Y',jjbs@7*KfQ"],
  w 28 46 100 380772 380898 9 705 ["*9`Yhs);d}z@T1)od.}+_E/c:>s+)PZj@o"],
  w 28 45 0 390017 390768 100 8616 ["`e1WfwX5+AW?h9FEcgBf40>f#HHjB@gT&NG@1vYuDZ(qIHd>U%6iOyVW=Vp.cMK>","cquYoFr%O6KN-qgCf8xhH%s1d(pWDL(j)W$SnKJXr:`u'i]u,a$L&UhJ(95ZB_yt","b'C5/,TYD_Qn<+hDJN~?d{7_4~33No~v,!RmN}D:Al1A8z|h6d5B!,O34bqHk4kn","#fHxzP})[D+qC<fRJFMX)2eh$CR&JI6'>?`IBK3FakpoCBP+,a)|>@ka8Hj1'GLr","#@)-Gu0wD8R<%m&[*aK@Iff0Rr{r'sCuj/QXf"],
  w 28 45 100 390769 390897 10 766 ["Jq*2;Q_[t.rA~VsmSEXX0&[t>ZiX;b:W*y!I%7BAJ"]]

private def r28_4 : List (Chunk 28) := [
  w 28 44 0 400016 400707 100 8528 ["Qa=Wvw]ecIN:RR<5y_{7P'C{st|@cl@!eUK!(5xR|*9S`J7~U*)/70Cy0Kc5?yX!","Mb{Zz##*we9IL-zZVIwYS{$)sl>TN^9,d?Uu(9HAW7BBAW>j(g0:}#J@>no.,_P4","iVN.m5@A--5j@[]!5S~:5/45lX{3r;=c|2fd|Gu*j_5Z03Qsf5lFOGYVcaU$gS_r","AAk|wpTM?-e)G8FHloZkD[GuI?-$QlXcb@g$j/~]AbINY/L%}^=1DpBF+F(AkyA!","~s>aXodZ5$);yH#o'lWGg2j,S;NcV-"],
  w 28 44 100 400708 400897 12 903 ["LL&}'1D(llP6N@)5aI]c0-Zxp|Dbv>FPNMQBmZH$PkG-b}S)Ty^"],
  w 28 43 0 410015 410705 100 8425 ["P^I=M]FB50,?>)Yf.YJ3'bL.s(J_ExU@M2hB&A$%;:3?c&Sg|u<g&,?b]1T~C1eB",";OW!$AS_6Co(IDOvmhmhs^e1bY-91rzJY*%Oz5fKv`]c.8j2j!w9fb/K#HF}jCti","TQ+E(P<IBU}-cCUX#;?40-XI>6hIvD$bh9Sr8slk{s$/5?Lxa(V<@h{-SWzIV:/3","H^,/:J,`#b0mXonOyv%rpeW9~MoLe41:+!f>5Jtet5^7<Ro+#d)i~A(M|3JMP3Ll","$%B'q~!#z-~C-wzUgQn0l-DdK,0~hKsN"],
  w 28 43 100 410706 410896 12 882 ["./:OLZr&3,bZ6H^Wq@vqytt^44fqZs5x(<ZQO;+$.li-c9HP7i+R"]]

private def r28_5 : List (Chunk 28) := [
  w 28 42 0 420014 420645 100 8327 ["'qnslhJ*iN|#%Y}%>AG>_e#n}E8hwK$k{yq*69VPP<{KXo2uJ:%~{4zt6ghg[}Qg","-Q:jKUAJ0`W9@f[hHZ7{&`M=T`z#cs1]%Z{{w4a0)>F$cA4fuJm[HnrF%qq30jvt","'.a.K|,Gg!'9CjmyHr$4;S-1Njy$*d!t#Tg$!*Kc}R0QN0M1}u-(8X&al_U/>H<z","3>zlP3Wa^j@Y1tx{MjFB}5`*6?iHF}.z^T^J!)5zhW8:Yw18S2zzg8%U%F5m(n6;","dbS6QAj/)|,.LM=Qup,cGyT."],
  w 28 42 100 420646 420896 13 942 ["_Lyg3dNJd]_lOx^l,t_JT%sz~!R65?d)HD}m2Y9.#Qwd{'J|}C(LcMV%B^SY"],
  w 28 41 0 430013 430643 100 8215 ["3+?*,9M9{>=#[j3]BqvgNEBA)Z5Q^^eA`|vHA?Ml@BD~Rnf$'K|d9bt71maa)P%w","CEip7'!EJqYNj_,s}?)2;cd4z2C6L*u,l1E0cs{:cu7jI,``vlf>tk(9aSh8!th8","S<h+VZ%JS7[=F{I:R;66gM3`CR{S3R3J$:NPko}L9OhYN/Ctb,w0v?jnJ:@XsEeH","Iyf9a.AR|,8<RHxwId2kGCOdbP2Y8Z%b]*OJA`Q`l`W`vu=/7qYYwnY!udW[lpx:","'#I|p>=NlK@_E_<K'@x&HO^Qcs-r/`[C;CPR~w"],
  w 28 41 100 430644 430833 12 849 [":?Q:'b!'/}d4FsDXM4&NpL%zQfj*I+]%wz~pscWEQ;hvQEf%nlsIJkpu-Q"]]

private def r28_6 : List (Chunk 28) := [
  w 28 40 0 440012 440641 100 8113 ["KCu=^;DA90E!b!rMIso2MZ9`AVksb`.[B94CmwQja`MOC}H<1MvG9jOuN}=,7ErV","*Z4TTv4j1o*-9aJBrb<:$jSSXpr^b&.1Nv+1Bnu+5r+?z^N9if^*@piL|#`i;<A4","#k0f_+?`U$#.P[,4'Now9?V4#Njg0?!&Z=9]L1G3Jp=I`U4g[SQ<.tbu-Z=W0D*6","^NwTmQA_t7J`'jgW$DU4*I,[DJ7L3i{2ue5|n2eL]gKN-67eDvgtsuL6h`(R%>2.","%-{J9:vmhj;[IN34-wBP&X:a_`%"],
  w 28 40 100 440642 440832 12 830 ["#t9YBPVYX#s>&u!@?&P/[3TUWhnV@u7)T=l`W8yjO~vz]_`u*EXTVdPe)$ESc"],
  w 28 39 0 450011 450640 100 7984 ["(gxtP*o*i8()Fkxbv8B#)W/DH(r]E:$vv_:`M;OUw*~si4Z34:ZOv?Z}zag=LbFJ","<dAj4p*4ddfBm}>q}.e00.`12E}>p=uFA.~(yMnB132v2HIqL|n`cknc>Qf=RG-Z","mddNQ2F{a?H9O4JRy=&s;j718BQfI#-BE9#Y]hiqY).DAgQNJ^N>8]S5o+%~!?^T","-hi.;!6@n3CKGCi^*t5Qmi[C$j6xy+}>*-&{xnE$8eQz'rN^E#+$UuU~1,`=JV$(","#@*%d^MMX5mGGM*_]Sn2g2F/dQKd+5*,E[~~&"],
  w 28 39 100 450641 450832 11 749 [")?LIB5#)+o<C:LHz#Rb%w<mhebO}?&.0^q.o#:^raz3A1P*5$m@MBp}5(E|"]]

private def r28_7 : List (Chunk 28) := [
  w 28 38 0 460010 460581 100 7866 ["t#PK[g~]goXBDp&iWU/@*IaG#eGmc3xhh*dmMz&v$8{'d/eLE'<BE&X5,.]|}K?.",">i+M![u~>=aQcld/9w0XuOwxa$!_TB0l}D=uu,wg1rF](})MK2sp[fq:E~#2^{7`","s!}U(XQ3eE~zyI$8!0M9&|Mby5WhYM:/QdX[N4+pH[Z9Wr.x:0aCixF=Mit8hhaX",":av<<pThH=(38}sD~Hwy'Zg6'x`iQT.*@,cKG[~g.SC)%uRL+LNu'YN^5(aFK!!i","#t4uX_F.Pg#Z3EK@lY[:XU.L9gsA|%Rb5:UZ+ode_b"],
  w 28 38 100 460640 460769 10 669 ["#V6?0:6]od9?yr|W-=5-Tf(QAEP`Nbyrl%^ftf5M9<BH?-Pg}**P-Y"],
  w 28 37 0 470009 470581 100 7724 ["G&)-?`{p#.$|UNRoLL5e#fN5OkRM|`dL]4;IHP4#eP';s#Y?UuGe)o(XBV!eWVJJ","=?'&3N3p>wYFbjC0iCeeM@u#$*V^N:,nQ1xzJ:IFy',qhEh$/boK.xg9V7N,9ii3","yPyE@~:^?m?;g-}OVn+>k}3>Ef4r+h[:*j0|4!s&-vQZY4KlXKeZeRm+eNmQu.pS","`d(9i%MS:Fuw3oehpm_nMi@aUf(p[sU|S(=l%/TFO/lf3D(}+NfXCA'A3_{#0(j<","%IsXk8v|[W|~*kl.Ag'YLlg$jo~_ej3hzcI|6J@@&T&tzfDl"],
  w 28 37 100 470640 470768 8 525 ["'&{T>6Sc;IuSjIUb;1JKVfh;=h7=W>X$6c65LPUp'YY"]]

private def r28_8 : List (Chunk 28) := [
  w 28 36 0 480008 480580 100 7594 ["W#EF[5xG&v3)r43y5h$!^3!}M{,QhT&h5L[`'c[N00a+_)<r7Fs#hf)<pVn(c=v&","Z:Q?J6hgis_43OO%_mz0bdsKL7,[[ejFs&bh1l(Se7/de9f={/F&vqCUt8L((#`e","nj.HOUHRug9z@l=#Ho:wg(p,/70z$HM8Q1LPg;U64[IGrrC2Ol4S[=(hg{Wrx=m0",";m[H~{v.3,/Hlt%D/$?0_D<=,GB$B,7=.;VFuoG~Z'C!oCn5g&6w<_M5pK_#pe?4","HwRN;2Ol3!mi)JUcby',`5(NqCZ=P7xfjbc{#TOtE@vv@x88Z,H1]1xE"],
  w 28 36 100 480640 480768 7 452 ["6#JOh<]Un1-kBOx{'w_`F$C|ts^'&mJ6uKI"],
  w 28 35 0 490007 490640 100 7437 ["rpP^xH~ld'PW1>CA$DN{fI5R'!_Tl#jSWvCz<-M?g;kS#ZjKVDW=6C7rSs|7~Q(R","`NX8?(uqYwOS*pG@[eE`=GP}9xkD`_lV'|#7^*g}iZ9ZdWuHk+0Z`D[<T4D!WOr4","&~MI-26Qaj<DtSXe^7)|]r8qJZg1ULleKJ=/LpUR'<[YBy;HM.L<Gz'!nBE%:6:4","z+o3_bh5.Qf+}^2<Wf9G(pU-<lr4A7)R}K{kX|xk6L)slPyrpBd45FaTZk6:E4'U","qgH[E`@Bv~zj*)<T`f}PJ!-`3}25(>It?FpwR.oA&6GT1{V]})[ma/Yxm^,U0Xkg","#BK03K"],
  w 28 35 100 490641 490705 4 254 ["#pc8|F>LF.r!)X-6[<K%uvt"]]

private def r28_9 : List (Chunk 28) := [
  w 28 34 0 500006 500641 100 7289 ["d<#SbJ`]'YoF4N*m2ES`Q*G&ea(vdn?!0'EE$Rk*IP:'TJ9cp%#AsC;-w[xU3!e2","ro<Os#aBH&l,t9:W5>$qS(<uc_+q9g<9Pv%W|%,+U_Cf8<1A7}e~6+3(C%WpN+7k","}63HztvnBT}d-CaK8Oc2O*Pl9}]bs5$YH8XX<sx=BLh{Igrr<vUi$m{TCO$#Lckk","pR19EN?/kpz[@nM'/Y#')/=)dUv*!R][lo86ZQmJoLy!f6qcAw@5]s/HsmUXx*V6","=k0_.GJVen~la:4Ug&trY(9+K1n$bK]d*saK~ezpk%9x~Hr~&SK`>N_$iWyG$N&/","+1m.{I4="],
  w 28 34 100 500642 500704 2 125 ["i`RAB:d*5"],
  w 28 33 0 510005 510704 99 7059 ["bi4-p_;Y1T{P&M`o;',/,B0=vVS=fr]UT;yI%>Wj%@q@/,d[H#ChSOLqhJVP4e$R","S;^9+C#D)T%,+hs(;D~U=}-<-yV!0f)KxywJN4mn$l4lX-jeKin]mpW5CP.Dz!CJ",")`8}1ReeO&X)6OXU>:Yh[Q+4K#~F^TKuc;a_]s$URo1<b1=PEGxD$t:l{E|C<>r~","Tib/u&`'<R&[C/@eiGY/oADU.A:L>xe(Nq2!j&dB`wS<iHiyzzfUt^>Z/)zNx^-w","K_#ZaU}`TDIF3H(_!(68[{$ifazXtEVN[E%d7k)Mva^yp_0d.e+:%>tX(8w_&%lg","+(ZsxWjVg,|[gt+|[*bj"],
  w 28 32 0 520004 520641 96 6716 ["&L;!<,Y&9Iy=4*~Eo]jP*IQ+pR;zB(J4zr!{l+afroU+q#UI+<Dp4V7fae%/Rpuc","R*`9o?[{?63fl<LTeX=2^ZwQz=|?J0,=Yu^u9]b^t[^Kgp%)Krm@&H3.h.a5uC7X","m6`n]L}wg=,zc|AD}L]rE7$G;l8rq8/)&Rtm>^3!B.Lvj<|~>Ec9NEX$Ioq8Z~gk","G7bG;UWL%-^+Rnch,Lp=9s#*&#q'rZ%pC6'Fu^;^KP<,1|s,W*>Sc'BvYx|1JsO,","Kn!<SMz{s}l#ZZmzX,9jAD*gMlo@2}koANy{pJCa={m'A=A+dF0{'qiOjK6biD`.","aNv^2bEpfAaJ-]}R0K"]]

private def r28_10 : List (Chunk 28) := [
  w 28 31 0 530003 530640 92 6294 ["lKBl6&1Q$p.vO5Ig;vTX(.k^:5H$:PBE@u-IZ=clfJIA7W%ZQ.]kD[ue22g47)a2","'%<_/NgLS]DR>|r(6i.gZH9.!,vS>}R?^11##m)#|;?O#CM'oKJV!How*0&9j$~8","jH<fnW^y#Ol,Tifj}eZa5S:n&3z~C=3@RGSr4h}@/<;du:57C4rG!%$@:0*wvc>_","X]kMlopaSv2QcFVv8@JGmVSPJc=EJ!5f]dsW0pd'8ADo$L,Z;YI)?'v}:QGklq4.","@w+A>/*2`1ZNQ//FIQ%%b2._`G^0<B&7)u:k:ZA&=u,$WI%Jfu}zdp6B3lWy`oUT","*i(u`lLa"],
  w 28 30 0 540002 540640 89 5951 ["%?FjNF2:iq10n2Y]krf/O[TRdZZXi:o6:F7>h3Z-~E';Y;~og7,1/rvJ:1VHAD-V","fn-C&!M>)e7@@vp`Je.|ZCgJBxs5mtka6!InzYp-vrF1I0=%o2PHeTff+JP'z5o,",".`<U0iL,emOIWxV1/;,u2E>:4~A?wNUI_!^H/TY2sZa*9:z5eXmMzEdIYM+k3y!W","ker6Hn7yM;d4,=Am^nxe[kw1G{0C,n*eMQ1U&n*y9DZ,a'Y5'^v(s=KSsR}Kw4`T","{/wm@HBmp`3fdsO,>fS_(^b9.Yy/LZB7?.fp;Yct&mx0-0r(8Qe3/T,'o^+,CYQ2","#sCll;"],
  w 28 29 0 550001 550577 84 5471 ["*!lJ_#oMV=VY6q0TJ7@9FWbz=V5<]}`5z!`*U5D)P[?yr,~t7}pJV@5#LY(LYjbV","7@Vyu8ISK?eT)0mvB!#4fB&LwToGOI(<w-arLd,Ide>0(|!>8'Ulq<a:@oJ*cgy3","`@vIB|M(b.]sYlA=h}utXt[*oVH%h5wYT,sg&?(#{j6ng~4Z4wb:j__@w&Ba^*N8","e+(gzfuqQ'&cz5:vnPC9KZmxDlp1m5k&p1L`U6zW7;Ne/)O79K`~~Zl?;s8KQA?s","T;=E%!WE.Az<ZOJBxh2g>zuG8&'ptOy5g?<:-8v>PB%=u1X,,G{_JdP/bDuqcj,F","005"],
  w 28 28 0 560000 560576 80 5064 ["LZC1'@>)iAdb()*PF7<JQKBHsud^Zzxe;>X-ANt(q~4;)<y6CPAzfE|#C:_#`tV*","&)7CAop{;&x7U1m!eMhipo?Y10A-;B]C9ewCHwWDT;,XC63{!9n!eRbE[B@`%|)?","#:9RRsrZL&DUey6$uadnt^4W'eLtP^#~+_)x1@W{yAo@}(bS7+{vV:D<fi~{[m+5","@B:{i?x69-(^iY)Ye5i4%H[djH!P.8@h5IAk8UTY*p'X]32coE{-YkFr.g:{y`[:","F3^IyJJcGp:ZKrns!@;|.2F$flmm{8P}y9$iPV!I$M?QJnl^A"]]

private def r28_11 : List (Chunk 28) := [
  w 28 27 0 570000 570576 75 4587 [")/.wnwWDK%tKIZ>5n!ZodeAcm7>dSrKO9:]8`l$^3V!P<JRX}1q%@s3N~12yH)gS","*~mM]^q$'-o0KW8B2B3p)8Y^cAP*CDC'2c@J.u,$C.yQ=Pz*cV78$47{2eqEbooE","<;;!TDm3s!b{]xp+8u6Ayv3{fKMXKCl.CQ1}7Cpl5NI=0Z9,4_+_$8mIBa+DzJ;C",">5HBN~EO1e:aqI=Uh%TM.}Mzx6Fy-*>yBevol~p&t`dg9bD,zqMBmMYfH@PF}0g4","/gKS29vwF#>E/F_H/.OwQk8&`277q}+cDs&|G.AK2X?EL?"],
  w 28 26 0 580000 580513 70 4127 ["ea/*H&beGlLdB1z+Z04:vbf,bJh>047wj$n!CR6RH)oFt;os!r]LYR']yCwh6Z1O","#Zz>)jZs+LM*NX2Xvf:IyL.Xn#!hE_ZmL4Jz8&tn?{W5I=Y9+QzJOC<oIons`'0T",",9#*(:ZY2vF2:iEJ0`O^R=+KfBKhARBL,C^i]@l79#(Zu!}U:9M@v]Bk;$yBi&KM","vXj@MrQ![|1VV0NVZl_n@w}pGRx/@IlNf$'q~2+X,kO`dcPk_vr1dA0>ys@{{Olp","PAUL;,g?F^{E/vgCL?jO;B/].ep<Jw!Y-g{Fl"],
  w 28 25 0 590000 590512 65 3694 ["Nqod}!B6b9@L/G>@WL}-QH7>nUv=#,cN@7[mQUtT9s//fsUSr6{2h2/T=a4U0A0;","IDF=Pf|^J{t}q)mrV?9zxhlaCR=j*2*B5]KXQ?R]k'#_1jeRak=nbZ#gABAt|d1>","Wx}S/;dhw&o|l-D-N5U-._;5L]m<A;Zz[L6s61RStxC%pvzqBcD:kfd#{Nm;K6/Q","'vOs&ooS$V|L2kAsn?VE#!Yr1Fd`*Ac)#zfLi{`2}fh%u`u{WD[N.kKyX(cT7Wu`","'?k[pgX*kF7U59FAZC"],
  w 28 24 0 600000 600512 61 3335 ["~NCI|J]<zulYU']<RO/&~44H:H2fPEI[8hsYa=P>dxsm-MQS|otvd[z-w8VCf*o#","'a0{uqP7vxZz8|V2VZZB:fl>{5<}J|HOf84JlCaM]72K'QJT+#Z-j#lQE:i~YT0w","K^75`VzjQ:u(&~C%~5`Xi*B2%u%x7]WFSz:CnFga1u5$KjXkDM>,l(y$l)d^s*W(",")Nvm}R^u}},kA[^.iTTB^[5v}Z^)8vp9f38=7uSjS5*s~O2K~MWd)vDh2o2Wh{FL","u/1^%CB)T~Y"]]

private def r28_12 : List (Chunk 28) := [
  w 28 23 0 610000 610449 56 2949 ["[1&hNS2eM!CIZF>8VN},'.Hz$+I|G6A@.0U@)8o>>gPm.<lUE{PB,[<*+x#.j{h'","q4j#u$iCa{&~<e7r]Y#KIRr{fF]}q?.fQrwA=-Dh3^)?3y/uc*7Z&d%D-%Bq/=$Q","Ml9Af%S2ZK3iP%3HLJxNS'OXFNpx.L)zk4(GjK?dzYRz7TZ4oh==n!v.KyE2Z,}s","@(Q|hf`,:wB,^&<o?8HGfxk>;%<X>aWt%o9$mI6&LET&_T^5.:]U.9>Pqd/O}@Po"],
  w 28 22 0 620000 620448 52 2627 ["M_4v83L7ba}_aes(U.AaqN$nYm*5d+sT;'b=]RTuQ&>pPrS7C)[rN?JaYk-Jh4*t","o:%dP#BVBAoz7tT,%5`gU@P%~9clZ,mzRML[I`,UuciRZCu`MD3Ll-^C(h%iQXgG","Jq)G&kb.-mEN/jZXJVA!T`<>2?u?w{M(xLm'6VG!|YW~fkMI03}igi+.~65(+4e]","ovm/d<iZxdKJQ#,<gl9WEW~|+o*DRySrkLmg{dXRd$=XMw"],
  w 28 21 0 630000 630448 48 2332 ["~Z0}n-u6eLBM%`Q0jt0>m`;$Rs'{#+A(c'1IZV;vc-@~+|4KM:/S1Joa^'Kiz)k#","s#vhhL`F(~*K:U{0WmXLFlOeQ9s_mGitiVcPLesO~bX@}~}ZWpStdk{LC<ew0tCB","zB8D!gZzgLYwP*)|)&33q}hvFtjcVL=:Y#[*OXItRb8Y0r[m38_3G`X`8y$6tGiP","'C{2?ogGzM>jTuI+|[=(l8Ya:_dD8$cv;TghD>6"],
  w 28 20 0 640000 640385 44 2049 ["!lw6V2h_Do;%8^NH-izI=fV|)?Lf|=-tycl*nN/Ah6!}!{n3|8)(ff}@n[-p*C=p","u]f9Svg$dHqE2<GE#qh~7s-pUU9WMK9RooO?W~%n>[fPyOTm<hciR8]j*(AkGzhT",",`/$j+Jp!*,q7m>-%VQ|}GZKP[0Z<Iu7YvBls_5Sn{0^u']wb#E9D{v>JE0:cSl1","#h;g,Ze(,goalls!N(B3;Y&?tG"]]

private def r28_13 : List (Chunk 28) := [
  w 28 19 0 650000 650384 40 1786 ["dq1Z(iO-^B0[h}%s$hRLW_2-]D:u.0m73KO5J.iH(YbnKq#q2Z#}m,b^`V2zawN#","R*2s:+]vds3m$0Qh]A5]HRR`t8#/13hr7Cu1,oVmq{kS#fj|Fr4X/gBd~i(%,^wG","+{$3wmnFXKZS./Zy!9x.;^l[]_OJfG,*KqPf`$nU<4j3-KZN[rE|u}L=8({Q?%Tj",".M}Z}Dl!j"],
  w 28 18 0 660000 660384 37 1582 ["lOVHq>jo'~9pr|F-r@d|)B^qX}+qbI~0Z|.t:plOhrxQ~v8H)TDV)vDI/'fW$k-?","VW,D!~~XJS7Zm6RM:O-dOmHhLn7{Arbid@miaOcUVj8-=-:W~ti;E/[)C4(}1hw9","pbZ|/$x<#1QlL#:,smNd?SWFs%]F,cA:NLT2HijTy?ezDqYNnv[UIFRsxxN'vsHQ","$"],
  w 28 17 0 670000 670321 33 1352 ["HQ*-uDtlSoqr[n@.i({GI.eM%suq{gY:swlp;7uF%9%pw#ZJ_ZIEFm&z&_j,Iq9O","G<_%`UO&8=z@nrWN+IVMtv&5X:-.6,t>?{O(dp1dI_]Y/gEL{K~V,%]EC[ha~hfl","=$p:l1J?Rsd}CB7{6z%ps3TBLT/NX$T0KAM4NO?#H!dTPPl71."],
  w 28 16 0 680000 680320 30 1173 ["I5e4+0oq1.CcK=m<H@CJs&.0rG`0jw@}D'tOsY'b$ih4.8Yo#=iK_9hTZ9YMwy}|","Hptv21<.e|5@B~a3Fvf`sV@$,V?d5FxLYdpk=/e8z51bVEl(dJA^f!51XsdY_x$~","2fL7U,F*tJ3j^={x^OOd-!rp2w9Aftr];8"]]

private def r28_14 : List (Chunk 28) := [
  w 28 15 0 690000 690320 27 1012 ["1?4Oq2Q8?}F_E(qc$5.'',=gnpW;U2qBuN|GkatT>@{fD$Z.38m/Qv|K$XS][W.S","X!h`q=cUsym>%4upC;Ez[m}#v[hXJ@t)?vb2T4z/dwCH7i((|3oy`{IgZ)Ey8}@I","&:]7vNIoR.7-d@<3`^V}1-Hq|o"],
  w 28 14 0 700000 700257 24 858 ["#`#K0y*HLkG7W(g);OtL^)W(/'$`Fqo449uq@#:SZfUm2b+2#7>3xX)B7dcRZPCx","*-HNtEM'~{;MC2YdaI51tGOvCkJLrP~Jr&8t~0]D5SaEA]4-w~|q8pi{oNk3LF]X","GK)lN/$;F"],
  w 28 13 0 710000 710256 21 717 ["7C3&i#7/(WW$c,tBOmIXFA]#e2yxnH;ne|q4Un|j`n(c`tH9hJ(el4!3PbiCh(fz","#zQ<*/-*}o`R<j(5P^>Y|9vI$Vlo%$-nzwxWqLKgKC|;erw!2E_c&e&/J(a3"],
  w 28 12 0 720000 720256 19 620 ["Q7;jAH0*:,[L($-?5_fC7J{[B@_,JuEPk*b#)-fx+lD[xp.&joXF`Or0?#3^1cBn","4l,9zIX#9X6#}]$YmcHGv6_O]s_O|?C^GKL,W;3aM/WdBQp|"]]

private def r28_15 : List (Chunk 28) := [
  w 28 11 0 730000 730193 16 498 ["z&X~J!-.FZHF']&B3k!-|N+_yZo?<kuL5^`383B3)YX@FRx_Pw7jguWqZ=ZYAGF.",".TkXIL>`T?+|Qd?ia>5dt+J~d|iTJ=ZL+a"],
  w 28 10 0 740000 740192 14 414 ["FNNA|g4jcLS__g@O~`V#],<U>MvcJRb?&,.2}BUR4jw)S&.sY`*0qMlMS{[u,%Lf","a2R!jmzC_fC/$-y@qX"],
  w 28 9 0 750000 750192 12 340 ["?*Wldw#P><;.OW{Frz[+/vd$Ly<ycP!l*dtr!i3LU1<]gNt5w*gR?7R(`QdOxJl2","Y3Tg^YVFH"],
  w 28 8 0 760000 760129 10 269 ["$x;2NS9pZ]2oV-CT{OG`}!vIZ_d!OQWtwb/=~yj'SwIr(Fy-2_^$f!!X{Z7!"]]

private def r28_16 : List (Chunk 28) := [
  w 28 7 0 770000 770128 8 205 ["+KDfn!2U4a:_EM)dm/4Ge$m^K7}4%$sg]TsO;/`z;?b;g|its"],
  w 28 6 0 780000 780128 7 172 ["<3`dtiFqX^3|ofJ]t8K@uoHIye|o6`Gw'HoDzFF"],
  w 28 5 0 790000 790065 5 117 ["=TR<p&o(Y|6~M!/2z&`-r<n4cYid+"],
  w 28 4 0 800000 800064 4 89 ["#m`+[6Q#VOjWC99H1}mIcP`"]]

private def r28_17 : List (Chunk 28) := [
  w 28 3 0 810000 810064 3 64 ["Kyns/N2j1<f?7e_"],
  w 28 2 0 820000 820001 2 40 ["oYG9/_y7:"],
  w 28 1 0 830000 830000 1 19 ["I!e$N"],
  w 28 0 0 840000 840000 1 18 ["XuL"]]
private def chunks28:List (Chunk 28):=r28_0 ++ r28_1 ++ r28_2 ++ r28_3 ++ r28_4 ++ r28_5 ++ r28_6 ++ r28_7 ++ r28_8 ++ r28_9 ++ r28_10 ++ r28_11 ++ r28_12 ++ r28_13 ++ r28_14 ++ r28_15 ++ r28_16 ++ r28_17
def rows28:=rowsFrom chunks28

theorem good28 : ∀ r ∈ rows28,good 28 r=true:=rowsFrom_good chunks28

theorem sorted28 : rows28.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks28 0 (by decide +kernel)).1

theorem mass28 (i : Fin 57) :
    bandCount 28 (i.val:ℤ) 56 14≤(rows28.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks28).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 28 (j:ℤ) 56 14≤mass j chunks28))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total28 : (rows28.map (price 28)).sum = 268398 :=
  (total_eq chunks28).trans (by decide +kernel)



private def r29_0 : List (Chunk 29) := [
  w 29 56 0 310027 310903 78 7752 [],
  w 29 55 0 320026 320902 84 8148 ["lRS<ONGi}J$msRI}OG'#Cuk6q3ORFb!K8:H^YCF)X)]'Y5Luf&RoxzM$I3SC4{mR","])CvRsK3D1*$:ar|+6Er@'yb[|gRTjSE]VLgzFu$fdfvh36HviVTb(uTKbqv"],
  w 29 54 0 330025 330902 90 8561 [":G/d=4SCw,(sYH.&;3!u9g!u]{0@D1UP0TmnV$fP[T;ydw[%&)EE<G:'1K;KcRF:","c^n3aFWp?{-)|!F?(!?eY@+ET.B1SHwTh4ChU^M%[xK|Z,{cxe$Vl;arKAM3dyJj","9#:GB+/kg?EK:om%$3-`7U]W&+;Td*tG&UU}5a+,Aa"],
  w 29 53 0 340024 340901 95 8894 ["r5P%+f/_'@(d?c%?kM+%(>HGG99Qd~wsiW)v&LZpRw3kVp2mzi5>EC^M!J%;Vz|>","ntj7:o<{U:Z~(2(>43PhOu`6.g9{07NKsFVR,JjAL5)qojEFu!+hdCS^j]$.G#5g","_L_<wH;I2R!I#XB}HA.a%/1#%?.=!=*5V9>E;2x;AgG?DJ<-WK97z]^?<-S%kZKJ","1j?bdh*BcN=>^lm#c,,n&s{e9hi`6*6!y"]]

private def r29_1 : List (Chunk 29) := [
  w 29 52 0 350023 350901 100 9224 ["p4ouHqPDpWOaFzjb:-07yS6oiW;=oEsz0ud!:gceJi|{s}=fH@b?wgXYSg~<%XeR","j]RFC:'d]-'_g$hD#4qukwzso;/mkF%s~*?%nXfNxRoz$J9YBd3.=3Y}YMF-R5[9","2`pGnN2AE8@7<)pdS{x[hE,C`iO*1=@7xg/c4dSWB_{b8JPnd]9#X*kM8nad0v=2","~v*j}Sn72aJjwa^ecqlw6,n-]+CCLKH)$KLLwCa]9Zhc6G13X/*v<zy}-%@qH{;W","(_l~/+$a>Jy"],
  w 29 51 0 360022 360896 100 9122 ["[4]&YK&2.'<V*H5MGgU,w6V#fXOf!=!Jq=BmptEf%WV7hNap~}__JKv=r;Pq,RkJ","'K$7bsFv^RIlPwYpyUg2^CU6hH%!R;pJGU5qaZ]8HZpQ!]%6Y`h:7B,Cg|yE=6Rs","=k(-ZM#N=PQ9y6nYJ1/z{#u|,4sle5qcbx0O_i/5tRw]I7d2]t,6hj})]J.c{e]-","bO+VubEe}z{7M>ctA~%BH|RAd24#bS7mT>u403W6MgFlV-B$SVEIA+*W)cK5kgmg","##A@<?%'F~s$6K15kimM2YSJES*t`LRjg-fD"],
  w 29 51 100 360897 360900 4 340 ["2u2,*cBgK"],
  w 29 50 0 370021 370834 100 9023 ["DMKN-?8LFD0z@<#+E_J0J[8(&`U0O-Ht]tS^;ry3|+opEX69|Ksa~1HRv+k3;,FZ","*SMgH@E$5o[OV;$l6U_.s{=,$UVxR#niMx',.S>+Ud.'T_z3rhqORA'O<V<y{Md!","d#wj=~A'2UR}}SR.$;39zi^uN5Y%6po1r26OcS}h`W_mU!f*y*,t-Fr81``j0B)^","BU'U^4dD,,T55Q><}GaO5#dd/]hJ<.L~=#x(WE$ui6cQ`6!Sd'mCjAwq}]L#ZoL{","6,9$3<2z6,n5g37,'OOk:S&zZ;1*4RqyFqzx%mUN4IdXagLDW8*"]]

private def r29_2 : List (Chunk 29) := [
  w 29 50 100 370835 370900 8 666 ["R8Pc}2{Pa&Ug13Y5l/{z*m"],
  w 29 49 0 380020 380773 100 8930 ["Tj[E#$m9d2)f$>AEVc~s~8&q-(Z27l.*n~f3pVo6V#'(K<zvr.<#i)8b.mRt)nd_","`>5k[udYb%}`RjhOKx$>dm-+AC|<:C/jHMf@0'#PixoJa7d$v!_]TvN%[{XB>njY","!BIAOMEk_vmK6tvh0W7_2K94>-)?PG+G;>45;_,z?&KHhU:hHdYOh=8.AGurL_'$","{u-cxO||N;H3h#$1V{,XecYoo#m~vLjCBxmx3-,|v)j0=bz/~(Y`l**3*7CaZCKZ","45YQL0C2RM,a=DUT!|kmD/h=8r~Y+Bo7.7q/'i}`D0DUP"],
  w 29 49 100 380774 380899 11 898 ["'E)x[b0J;[b5{mgX>tE-<yTHFBR{p7qU6wt:v"],
  w 29 48 0 390019 390769 100 8836 ["k?9KadJ`?t]'@m=&l3V.~q3{vFi4Lugi*#7L{3e#opyNKpg!B+:--}p6lI7+cl'N","a4p[<a)uhE%DN?E'_TiP]W0UILk_O.vKv@&p=?n<mntUFeDV2U)1QAInq@l?ZPQ#","+9[j{#>QhHc|q.djIUsH58MVHOM!F,m`%xppv~RD2:>>|<u@%<k[CSD3MBt=M<Ee","`S108v{ODc{1ywPwpSF;.Wf)w4uu]X;r7,8vTebg{]S.e7)f.c3$&Yu9rM?kLaHM",".0eC^4qIuZl!&jb]9(,&*:@#eSNih~ti8TD:[O)iACN/Qs*,j;"]]

private def r29_3 : List (Chunk 29) := [
  w 29 48 100 390770 390899 14 1119 ["$T%yUEpkWyXbI}$$OUC]%U0'oFgn(Uk;'d{93tv^8|I7[QS?n9"],
  w 29 47 0 400018 400709 100 8742 ["**+]7?o9_*w^J85HS@Rn{^D</%uqyUlo,;faJD.F+9xMS@5(#g9]@ika1s2K,b5g","[X;0+`Dw@(rrNCqTi^4[)heG]-|!-{L}j;CarS@I7NQ,{GxK`e>)-1]EVnq:8~^t","2w~'BC4@/-'jvo^tPh&$fXRgO]JUa&?XdKyZCFaDNI@W!`]4me`mv=2#KNR?lWN-","Mv*Ok;:'B<)l-Q?h@R'jKWom5n+~cX:~w=D@l>!,<aq)ZD>*M~b6Wt]F]OYHtU&r",",UFfw;gY-'Gf,`[voQe'F&4,Imrw6+<+C~r;Q/dz1A+|~"],
  w 29 47 100 400710 400898 16 1257 ["tM:_V0?4pN;`DbDl58<Dt=l#R8C8jhV#%Fo||;>RID=7-/+vfQ7grEqz+Gm{<N"],
  w 29 46 0 410017 410705 100 8645 ["n#`4kw)Ah+:!G|NEzw;o`OD8a2hzj).v6U|O{wr!:EBuIFhtVSM^^AcHc,mb4*1F","P%T.*vs;OC?q}G!)~0pD<CzLa1Y3'L^KPFN!)^;koV7XwSK:ktOoZt}_%a|8,hou","S[J9DnKRX6@nGrp0r.3IC^<b_C(jE=8=Q]Od(.4Yx`9eA7vDA+n[4nvc*5m1BL$,","2<KMlX%#eJnX[veFAthg3TbzC^6:v]tYq2%R'aO&*VWKW%;$BGkp;wb'@Z@Z]DGR","$GEKzHA,U*$Q7rjArTnt6s@3z%idlcX8o}B|@Lpn!t:"]]

private def r29_4 : List (Chunk 29) := [
  w 29 46 100 410706 410898 18 1384 ["4h|:F'N;0/IPvE@1vyRP~H{mA@nU0BC|nI?P4lWh(y]{}j#W!?'{wf;{pKOx;2AJ","2]@;.V~ei!=9"],
  w 29 45 0 420016 420646 100 8545 ["OSIN;ev,]JT:PRq[UcJPEn(R,%`*,R,l~Y&L:2)L'`au3p-Y~K8H(>w_vndx%856","^,a,6BNd~cLa3*O,'a^QIEbF5/EvIsge[&4a?%[jDw2/c':ylS1[,oVyu('&<}.2","L1(wi^,K4I+!P'689Y4iz+kI~gMGEGriqMcif_|'I$$Oy^c&/QiwQMVCWmi*TQBS","hlK:]<:v.|D-#1fm2Bw6Drj`MoE3s7Lo4d;syY|94(+#(?:3/l7]p^VU,L]N>9oy","'p5>g2^Dd=h?aeUt&sB<TZ{RRPw$YDH{K~<m_SD"],
  w 29 45 100 420647 420897 19 1439 ["40SnmP8<k9e%_A#7mFK7>PfNybs~Kz4@uJI$ZC#@D[!aR..1^5KG)|w/%cc1->kF","u<T)+PfZX}Gcv^qJgq@"],
  w 29 44 0 430015 430643 100 8445 ["YF5t8&)15fnU,[Y>onw,;'?whlq^y&!Nm=Rg^K3!T(!wgE*Tp4}E'M{f{Iy^B*QF","L>oZiN#:1ju^CU%;=v?b:w17@F<5F`YV'7$J7npER}9x?x87Mt?B.@ZM2/:$ph'[","M[@Ow2Qw$KDQ@?+U*C^eVfBt%,-cPXW+0}&5@[ovy5JO`+hcB><8a^e=O!I3GZ60","43Km?~3=HC=Y]:lx]9+Fxx,lmcq;L%i4H`46MVau8n^am8AzUG>[KGPV!G.~a0)^",">]w_?c/)9ZAlyE|/q2>Km]$31j%oQb{W^E`R]:1$"]]

private def r29_5 : List (Chunk 29) := [
  w 29 44 100 430644 430897 20 1477 ["$q<rz?FnjHNn|au&p+O#k{>$@](2Li1}-,!G0GG*jb['K@^U/U[zA0q/q#:hJZ[@","'uHZLX.S3OIV(hcd(UQ)}i3"],
  w 29 43 0 440014 440640 100 8342 ["[Ol(a'K5(JM}D.K!Q{l)k;fvei-uI),+iC7B;7F_<^d}{_<7F?@e-9sei1}&bKxN","cfh3%:&jM#tX0fFz{iG8n6sm=d}94T.l7STo7<kM<.BeM7dd=kH:?>)U6UR8D:}$","&'9E1g]_JKN^DQ1-*UjX#I+-.d58H5V|$&p.gTAX8Sve%dmY*M7n1T~4~#+_[cF*","~6PF?@!Q9@SrvyUKB>kP>w*uha}~Iz9z]@59vW(-LxY~LZIfQ|'pU*|T[o1o[JF}","2tLSU_40Mz)1<xklk;>z3E0WO;9Ar+Rm8?8Hbix~"],
  w 29 43 100 440641 440896 20 1452 ["c#hYlkJmIp+}7|#3;]t7MORx&$uhi^h5/DE@Q{&*N>GITr7,]-{~b_QLitDy{Q72","F@lV!]8#RH9%8ayy[(JjU]J&<2Y"],
  w 29 42 0 450013 450582 100 8222 ["]DxT5!e7PJ5z;AhdqrX-h(k7K);/.z_I-/O=!,11.hdXhbuAH(OD1}#BH5Y&<0N{","]vBG|,3zFZN>LDK4_Ge<]|QuwY=34M?n+mIg`x;Zb/$wHrCHyart~T,ocHO>I|DD","O=+W}Q+IVwXWuJ#2OKevY^y+oVI~`ILoOp]Gn!ZL6#KYHt/5zmNa:*v0?bW6}l)l","Rt>3px)ln=8Q&zR+%vU7}yO3A[WP[1'9pM2'(-FQS/&-bB-*@@qA{xR</a+VK,KD","$+YO+wtVVHtV:i{N=(^<(r&zPN4VGoM$,vpYES"]]

private def r29_6 : List (Chunk 29) := [
  w 29 42 100 450583 450896 20 1426 ["3tK-(qGbYef}&r}%r*4zEiE*|4}Gu'A-iA0[&DwrATH.W_qdK,u5+{mjGf=Xc1|:","Dc[7(g8h:+{P[W!nN-s>7%gUfb2'YW"],
  w 29 41 0 460012 460580 100 8120 ["mIL37:8@dU]9witJ&v[1^<e'!I(w3es;cpuU70.U=3d<;?PTV5<ImxF@vCg%Q>Rk","tGe1K!:R?|{k*:m1%Gja;Cb3HnjO<cHm?yuF%/m(v')BBqe6bNK)qli*%g|a-oqb","-mz/j<PIcw_/ym_!,*4]uKPT7Z=fKC{.AfV[arqdn0_%OGFc#A2lAEU7-9k&&H/C","t//^f6UFe[fGD[>%CQ+Mp4FQ4[<r$<oZzzUXNlFY:}z[GRa{4:q[HIy/!R`sj>/_","#R]d^2%&|K<U6G..Ik(SKnSuj]_.pcIoCPIyW~Y_E0"],
  w 29 41 100 460581 460833 19 1320 [":_b-8[YUZ^)|>IwMe^l)j{,>'P*.Vh^r*O(W[<MNSq4?PMLbT-BA`'![=,;dHO;Y","'#NQ'K.,cp,Q3sybdKrz|%Q0zE8"],
  w 29 40 0 470011 470578 100 7994 [":;P}{T%C1#-6<w0`_e2A>(]5D=Ia9li'zy6#h&VJ(oGWJ#xxFETMVV(kFiqAp``.","jPn+<7{%Xb'TJx()4XoR$8f}S3|rEkVRw#Df$8d:<D9/Aw/Y`^IJPMR(*Z<EwJw_","gC!fL(FI[L,O|;5*!`y*hZ2Z_7a8Z#q|p1T;TW$jZmv[l0.2CZv`Z?.,Frd8E~t_","iK,.k97}!xz[<$(V`$|'&zH>VU@'r;77M!aOc^vg)wK~g*kwF$I56Sj@Ln[Y=|>*","#6/$j/<(=1M$c^jLWrY*D,N+{c^w)WC32^499e,Jnu"]]

private def r29_7 : List (Chunk 29) := [
  w 29 40 100 470579 470832 18 1223 ["m=~u3bX>LV^kT?-vGW~D8XTaoDp.{`^^_U~qy2bD~/V6}RZA1PxGD+_4aF38^,]x","#`Zo;<D}c0I~_&%:b<#Gp[7_/sSC"],
  w 29 39 0 480010 480577 100 7874 ["(V6UNay+IhKY6j'~`5CVEJ[Fi7J*|xt51#Si(4ySuc+T.D3#->ChPkoIS^7~&==F","mwH`Qz#)i%S@~~U.g&nQ~Tx<3aiby/]3@|`g@pp{Je8j+T>b}NgYL9C<42jmG:47","|I]nYND<no0VQsXkm'BMeM|rPhB[BH9!*#/lQWt@tRuA_|n8u([(uX.,^otQFx?*","{(1xjLKsI<w2Mez%Enn}({bv8ut??C8?2X|UrY;e#Ik+cD9%nqLYJ5D+nlM&j/pH","+K,SGu{31TvS~5;,ATo;VITyDU#Egz1y4Th3BwY>xV-B"],
  w 29 39 100 480578 480832 17 1133 ["]EuH@?uy,L|U(;-K4/^Q&HoaaI5ktF.<u2*H@3,.>xGMj&v~eAUvw%/oPfm'{Q%+","iK~]~_84vX5JWQvZ&t9HiY/"],
  w 29 38 0 490009 490576 100 7727 ["DifSsAVJ`{|fQhRl_9x~vf3)=[z6GPF6nCk'g+xs,5=Skt~[^0M+6@}LY&be?=L!","Rhx]aL[K5mjk9Jv(#B{U|g1-P9#j)3l6Rj{r8egEW{`Sqwil&5A.M+3mDM@xwiH`","=?#qw;7U7EXu0wVQ<ONypb4:lsDfb{C|Z_DNK0KB.8`J+w^}Kg*a_e+^lF>QSK{c","TD`lEgD)k5Cv:.+)1u5QKS()lbqaVjj`vi.e.Ceg|=JFAvr(Smeo(1bb16//hB1X","#V:V5z7~Wo/m'-I|$=EZaEE8-Y!DA/ma%mZ,lcvWJ|1vdem@"]]

private def r29_8 : List (Chunk 29) := [
  w 29 38 100 490577 490769 15 980 ["}'{,ADB'BgBe58<m5nv^=^'vDJO?MsK1n~ch+jp=`0i1aa>T9]MC1cd'R(D<I+V.","9W%#jdiAr*J1;^e"],
  w 29 37 0 500008 500576 100 7594 ["Y#nRHWnIW6Q#EX[kYr^6388|^tij{tGJ$~%qNrwbGoR~X6H?_}t4dJ(_:$dPIP1&","*%^al)rB+ih#<keAZ;X|:<@aG{3h=!s$0z:jjIQLBDcu,p_7wDkrfPJS{z`Ex&5E","M9>8(2,F>!(]3<els9x.})o/)Eb;K#TG&?5hUWJM*xtC=jUsXruk)%dOz=rpy^!O","8,73y`MZy8p5DC{B-T:$iL??l$eFn>Nf(1WSy_1uIdu$>@M9c3GdKT,+Pjw&h6TV","yJ!eg@@[5<JWZn&;R?}9D(.2%whF5%fqN%B6uk(!MsgPB6`c:F~)%^%it"],
  w 29 37 100 500577 500768 13 833 ["x2ZC<qT(+(=8#KYNQdx(kSPj~bORYat`mh@l<_9E^zm(>)D6Ft-`/7lvGdJZpK!a","3m4sc:>1"],
  w 29 36 0 510007 510576 100 7433 ["p3m7)vgkBnDT1Cdqv@@lr(':OB}j.y`u&3u{Q+X)-!wxlDjG>xo3`'g#[~CjsvG.","a+7S7kcS^8ybUQ)Q1soWM:rlIoD'(g=OX~$zoxY1`rd[?2YNTeQ1t2C{VL!Jw/r0","!9Q?ll|3J.cc(oeTDu=_X,n1mC0C]SHLD*x%5Yw%0Xx:@AX/]*t*c;&Bjs%(9f]t","2jC3ul(~meio~UcQmK4$}o#wSam*Q(UH;XuRuJC`7:@p|[='*eXW(t;j/,pSZ#xG",")''C/G8fF]o)6m&As,OFt^NBf{Z+}O7%PWuuqk^&xF)L*(Rgb=G+mg*oIe1E:eqY","$"]]

private def r29_9 : List (Chunk 29) := [
  w 29 36 100 510577 510768 11 693 [")!d#!HBG-P~Zp@iKga!]=?[u3J_0u)$zq66ab2npw{v#Wdb{,AXPr:zvi2G"],
  w 29 35 0 520006 520577 100 7280 [":gC[0uRD%j?RS),~,+61.J16;Pw0v{vr,(f&7eO;e{4D/T=hkvcX)82D},$CkM{Z","S*C?n#o3R1|^|nnf2y0~gE2bdjz@n:weGLe(>y?7GTrS|+D)3h1s8u+Eg.^rZV/z","]@:x~^WMPVF({3wtF$O4HJL*50F.1yT[wFRS3u:#,Z^R`=N-z*?50}<ZQm:,Jv_*","kE!UWzo0F1(x5.XA|`Ymyk8.IO0sjAGtx?>p^SGhml=~{2wW`dP_Z(&FR(yAk3^P","BgD?mc--5WUggs1I)q%OwD_4dT`@DWdfCnGJ'j*r$ejq|'bv1Bz|qAs:.kxbWZY+","REkBXD#xC"],
  w 29 35 100 520578 520705 8 495 ["0i:~9q7XLQbi0n%)&FS:m[cYeC=895@kE7!w~e8L-Iqp"],
  w 29 34 0 530005 530578 100 7103 ["YG0M}Q1,5.z',>ZI?Tv5Wh?I&@|zD+#6~*%T8{PvMV+f%G?Gc,AaE_M&k/M{z[Xs","1|nZ.!RYN{EC@uND7gBj9Zu.M)1R+0Ewp[R2=.=3|`1L.nY(g#))|kN[S9z:A8i<","jS~uiR[HwyN|IjxQz$?`JK*bfR]K({)<z)EBr~yz7@P&>Ps{a]7Xdt+qp[c[M~W3","Wfw17]@-f!mn_nK(~qmDc9f48.Svj*mNiu|g&)Xf6$XC?M]}QttmB*#b6M[U<L%.","_$zcE[%k*Dp;#*M$FoDf*=1)]h'{[66)^H&28Fo=s+d`(XmsURIY*ImQDJo9+j,.","8Jz:w?'Q_0tXs[`g4``ONn6%!"]]

private def r29_10 : List (Chunk 29) := [
  w 29 34 100 530579 530704 5 305 ["+0p)Y1jvmkVB0nWLoj{7fBf#ed8."],
  w 29 33 0 540004 540640 100 6939 ["X^.u3mv9pKAz(FH#FR:k1gSQ*:&DX:p=hz6<w>FwM;~&JrwO-;%lVhU!;J|z`=>*","/a1J)dR.IoEeYr1*4fh^=1QMo-Ae'Jd~w)aVUZ,MZ96/#Bz[:^+&]tX@fmoLm@dw","jwAo*Ki)_^*}&@9>3TC@AqhwOt:w@;'!KuSQ%AC/pxao(7jyW44/vA:%Z>}]P=Ke",";14krPf|wzaq/dj'Okl]`>+:7J%3F)ZgCkq|`s(Rb1n0gv9p?Y%ZSAL+&ht7V%#Z","^a.V<Oc')k(NutO,ByV~86.Nka8VwBE5TZp4:9F:IsE5l5H%^(eY4M%Sf8;d`V0N","liS^5a3V3:WR7<aC`q:'yxN2+lILC!eTpBOTC"],
  w 29 33 100 540641 540704 2 121 ["#=X0z7@G&g"],
  w 29 32 0 550003 550641 98 6625 ["^$##M%)Vetsoon}K*Ey9g;1uc7*-oa*I??F5h+}w,$IAjIk$2a+$dbZ3PS:_+,vw","JH}Nq:T.yL:6&LEp<skR@h~tK;g03T|+0UCtKd1*b2faB(`M,tX,&;;E2qQFDeYm","awBLnS$mwP<DHM'z+q#.!UyH';3}sU{fq3trO!VmyH+{0J;_>z?cyTAIZ|I?@hSI","z/$-<&8$w,|mgcZ<#tVpbQ7LKe6;->6#[]=7`HSVP'[p$TKWCm`*W%E`<q*J+B}e","%p6xfu`QA<xuP<*;/C[3udadqY9t1378yxs$`'^OMQ,trsH%!xsZxKtfGez*]E'P",")m}G?|q}2V+V<3k97*&*ij1[@}.sdRs^G?M.@5w"]]

private def r29_11 : List (Chunk 29) := [
  w 29 31 0 560002 560640 94 6219 ["mxj_`>BFA;WD&/(Ik4IpD$DjDDjYVV5lsa0kD;sR|bby|=?>j)QZ;#!5y&UnwWk{","hu@qp8At{_5]qgzIKvV9F(++XZ>33MV%P{.Aj/QiC!Ub%IZNA1nT:j3LKmx#'w9v","46(9#K))N&m[)R!s'53Ly8EFZtx`b/U6>s/*e5:]onFp,mT19Jng99/QK}/6xT:n","RnsLhwa4BvbAVJoJ)AVu$F@ZOOqz0k^6JFwE^e6P<P/!:7;I1|A$!Xo(0x@}Ln3'","Ee#u.s>SwF^`iyZ<%JczJ*</tpDPKFG97G=G0A<r/aMT{Q|n*VBX_IEB#:X7p3-j","LzCxI#Obtt?;eGM7.0fN&P73BW<K~zU.ti9})F"],
  w 29 30 0 570001 570640 90 5786 ["Q5zr9z]XHVkLr?g0%^%vouz,K3|5W~-N0v?@R$brIX]+//ch'5c_';(9qakr6Q}c","~-(2&]RCW#zFMCB3Td0*jY8YvjIj7/u/Y<wLv3VTmwK6HGPaGtFNxDXoFkQjSo.R","i^!6sq~vpH({TvywB1{uFg%7[n!>md?dChn&qDZhdvrp[Ul8J0R%5}fClQr)Nu_p","17!gyUj?vBg<9<Fu]t{`BWj'X5JZxJ7^x;`~v{sy,FJaVq|=QH!;7Ce,iU_P$cn(","=C[nbTX`Z+c@F@t/]B$%}*`$S)f_(5tQiSTno2:!5QV7I:oE,mFBrK1}xBJS,c7t","%`Y^y{P]jf4s'=V;MJOuV$).N(idYhE0"],
  w 29 29 0 580000 580577 85 5320 ["i2Of/9hNX0@1X.);MB@[ZH9X/e&#O049#DKsl>`%?i)[)5FFtaANs`B+DwI7Kiic","iM;@AO.0CQ3oTE'P[86wX^|8b`#^TV{kXO04dfqw=O><#nv*^'<FkV?Y!>@#b~#Y","rpo`5Dx<<{.gntX&k=5@*7e2(K(z*hh#9-{k5!,m50'/hf-.C5uDntlHDUJY|Pc;","G#x*h8|x,=Og~VLNIZ1^Z_k_`cd?_y#o4Q/D]Q{=ZsJ-RV>@F(-.!)4w8'B8N_=.","Jf,93mVqlpqFE.RU_}tiEVuz~pYB*U]0}TVxkFsoN//fdJ37U2ggQ-S-{P*0=-ko","A8'U4M{taO35H^[<3|"],
  w 29 28 0 590000 590576 80 4832 ["]vQbvH%@S]/O/@%zbky'avU=l**]w>>8G0uPI={pus#lgX9;rzwMJ4xHC]XWG;O7","UL>q+}_~7;Ph'2[9H$bP]Er]F/2)bY)OX#O^L-Upi]|iS~ne9YD1CE31FL!KF,3m","3VSl4R_Zu+[V[yko8/5HxA`l.ks+Rhr|s8n!jYf+:1Z1ZgKT+Y]Sm%h~S$bY<&UV","Ru7LY19p,V{.V)OPuS%N!H.'$?ahG9oO_n-9YPB=9R#PImurYvziUN>fc;JzV)](","xc,5)Np9&rn5+Xz3RGoDIs7Oi#M3z|4bYWYR7fEJSL=j%?:M@8uLn4+FwW!1SQd,","7L`S?auhP~o::ptGD"]]

private def r29_12 : List (Chunk 29) := [
  w 29 27 0 600000 600576 75 4372 ["$sNvMj)H;2q^ON>ky5<'Z^iNDU&PbpT[{a$oi2KD1i3L}~ZW.?HET0lkr^|fQ!7h","#6`[OU<9i*&;ze+OSnSm%i>9%7>(,y9{u;oRPPR|qVH=8`ASv%dg/_w&<?5tz;U?","JKt57$F{nVo{f+a2IRQ^!A=|}xOH<IX^B1A]_&IJ<J-SF|/p5wrX0X*_S%@Oxk&z","S*pf,ZRor~)f_*O?uCSe]?:^F]0UJxv^3MYWv[Fuki8.O)9/3=)TQGkj5dD3ppJ)","C61T&?ATreihJ5O4>.fshOsP/``K*vfOm0k:A=QUiK4saqz(mf{k82_RJe`AJpG{","#<LVNiZ"],
  w 29 26 0 610000 610513 70 3929 ["vz'x7Ifm[#'IIE>]/8m.+QCV;Xtlw$PA5@$=yfEV}sdZdz7Kq*T>3gOEpVZOBc}[","}Nkwj$E0+S9h+u|H9$bg`ai~$Ary~ju`RqZTUnK}c9&~_.fUS=HmY^LYpfu<q|w2",">|z?jq]$HF^v+e-rT)*c*yJmwwkPV=lxTDYFrbwQ.pmB0b+Hh%HqE:IYm#Xt{{/i","hgqqq<-R0x2OsQQr&f/l-pOk!}I~%rSI%@r45D4kTsK>!5cG>N(~gQ=/:=J&WZ^+","EW&L+t!XtXL2N$Pltf2D?s(bk0]<CHS_KIca^j^^E*4clBw7lp2.r"],
  w 29 25 0 620000 620512 65 3519 ["AudA~2NE+1,:tdfS0Zvo]@b<kgfRQKqne>$;Rp1|iWL?)WFrf<B7oseTsZPvB=lG","2Wx91,K?ywk&/S(roLd96sm341'[@4w!?xWWS|+WL=?;Q]/+NVCm]=}4R]{0%u_'","]1Ghv]{+o@T(E^XLpeTyYFcTjF-uN<S9ISt1w4]YyR_5tpag~lv~*QIP+L#1atwZ","Ei!`d+0lc399G34~5bHGV8%O$:KUao3QsDk`Yz`JqJ)Sij/m$N75-.%!+RH={MQ*","#.EhTHS_XJI]U=+XLLB$3UjJsmx-Q&-5K|1:U4%zw>ZZ)[oVK"],
  w 29 24 0 630000 630512 61 3174 ["0a$_Ws+61L%#$F)yr0q[i5k'yN16IDz&s!>`bKD2/@8`^Yjhx|1cFbr>}tc#p@Vd","KE/)qjq4uvsMgU3_1%ok*HWE%Pk},?iIhmopv]HV.TA}r/Eaz9pb(oiF@xd2N121","*`Nui:8$nAD]k=CGerFdY_DLdFGXY?$1MwJBz1|?owa%D.OO-4SkbixmY/:NDUWG","WDYDqR%Q+-_7S{b(.F5y{wX:>d;?l4F-L[L3e6lc*bK+V'n^xL[$qRKrs};f4YRk","$sw(3[>Zqgu:HWBxN)dcp7i`4+&7}^Ib_|;"]]

private def r29_13 : List (Chunk 29) := [
  w 29 23 0 640000 640449 56 2803 ["z(6K.HB)[mr,31P;F,M*u&_|4LfBGezmUF2-oiex)hYgE!=7G^l%~ZpFAlg~p6Yp",")DOeuz[k-h(nGN3Oj,gGiC95~J8@2>-n;2JM'Cc97:`6#>/>,,{7IMVH6S~W{$Rz","`?c$TGGmbJ=^)G?tPv+wwiGh954Zl[;y@lZd203YN/?cw'K[yHYPR/+c.q61C+g;","AeINT.C*p}T-.,,jR-WC}@+b'i+>c2M>=yqbk}uszp.1,A!kTR!3}G'*?#wsi`P+","$}<u~U88@M_'t0"],
  w 29 22 0 650000 650448 52 2500 ["f=L^fnms{_D&oY(:Rek/}}l,E_q^cBF2^D*ux!l5`DQq_ayVw{Y|F-{?jN<=3^q;","6?!5H-$'X0*gF~?@hd+[d8bjpCPM>Pj%Wz)fGjc)J-T%/P72Y($*[K#s69*Fb,q/","1^U;h5W0`n`d8JhGW;*S}o)8iMwFGbRDlWrKMaK^3gyG^?A.J]_`|~=3[kaS?=V0",":U-E-co)N*fD*^8^:V:y<sXCEa)_~U)ps^RCQ5N7}Za@2E:4aW;<p*T|om;gU|>q",";03Fxfz_"],
  w 29 21 0 660000 660448 48 2217 ["*5>-&p)uNLC6'p=ws!@_`Wew_z}(!38.*sT5+qt%8jxX'-[*qG;:7Xa(5XaMl'Y`","8+J*!$&kZ(Zh~<apZ=qt)+?TPW}t-RMtlkLMZ,?bi/Pn)Eo!J?E%Tt#w/w!P*dqu","V9?(A9I(EGc~g2/U2=gEUW8+$FTX`RkVUKIN|4jkn+wPHg~)}WP&lK)!bM~sx*/9","%ReI}05&?CzT9N:)~6U+c{qB0_3:C.]KeAwj7pUX<'^9FDo+L]2oD2#"],
  w 29 20 0 670000 670385 44 1946 [")g!6,x>-:fW2pH`9U4XmZBm`/uBl$',grbQUny@_2?5h0v[JSVcjJ='N@Kd]Q^_3","WRHDv<2i`o{tO_pT`6ntKzs57W8mO,j_o~d-E1}T2Ws#=eG+!hnm:N.'T{_@BBw*","&@Ks`bNGMa}`~6#qcAk}oZ{m:5/F@`97nesZJTRXzN2BeQZ-In^W^:pJ=_pSzjzb","'gb;<)&U8gR9>8p>s#<Aqvn8SW]Y^F:h..l%~u"]]

private def r29_14 : List (Chunk 29) := [
  w 29 19 0 680000 680384 40 1699 ["mk;O~kvPu4JW-xU'u}AdLC.{$%8lfot9|$rzyL(ut+A&>'AEXRy}BOjk?$a>PR1O","<+!T<-%f4SC#XfZbn8|Z5+1v[ddG,UxceIaAG@f!Him-N5{0?gmNk7cLuj{mV%)t","h(Z(;zshn<&FPPV3($gd-J(jk`9*V<-7j8qYN'.<u@17u856|_T7|v{d.]?qD4?)","mGi'~B$!ChtK8ir4i9+0{DYZPET"],
  w 29 18 0 690000 690384 37 1504 ["X_k3Rbu#ChsN<~`[w|k7w?@yn:T1B.X=wiyl9f~e*[)>/CaK)sWdzJGRrU=wn`Rd","yLrB=W-i^LpfylTAr/Y]~$]x#d}2=B3:h^dB9y,;T}u{*r%D&}kt/K3CX:i4B{em","6.WE?Ht[;V(tn9|-xe@a$~v8>`#B~@*$hk,q?ViQnFU7iGu*b!=F$O^:cKq56d!=","*/|flH@AJ:-43"],
  w 29 17 0 700000 700321 33 1284 [",|hLFHM$U*F+2u$|~i2_+z`3&4B#_{Urt)MTQ_ETkcgE7/77Z,Ffo_JMhI0a=E,+","B{;C!|tQg6`=+'5UGjV$IxvN-O!Y]m81;L_]xuc7R;q8,&2tlFFwg2NRfk>7I2d/","#M|lDlZewD`T`2-b]'Z(TF#g?i2{[D%A2jwF')k/cIiRm6/!18svkebrrX"],
  w 29 16 0 710000 710320 30 1117 ["jQ1[=9jyto+fe<,}[F:Vd*SL5Sn'u4JzCO!O#CH`{vm<?Zt[A.9oBn^aYRV;kWcd","Jsm8/gNG**$sFoAdJHk_SiXX8(2d.g5ga;uULA<.Imo<>b{x6?&>2+/X%Nmc(1aE","&])uIE/jM+45$0s-YL`bJ&j!ltMX.UPDL)o|P<)Tt;S^e8_F("]]

private def r29_15 : List (Chunk 29) := [
  w 29 15 0 720000 720320 27 963 ["$`T-ZQ4QPprpzq#10Aai8(u:yD_9]>]LQ^RU^JLDe!fYBabAh~,Nu9}hv-y{U=#i","^Jh{;1WvHf_|i@4@?H-#'4x?yX(HCBTfhEd6Doo*hk0dCqX^D.jZJQI^Hw{n#nM[","(qP/Ndmn&aKBDqMgA3;~aN)Tl?uWxQyD"],
  w 29 14 0 730000 730257 24 816 [">.i%.aGju-OoG*x!fxw_SW5j8Xd9n993.5'gMTSu<|`cgmF>vW%Pr~WUF(M0];J=","U+M#2Pm_Io$+gA2|<R#%g:M.Q[R?u(iLW(})u5{!clZ1Fl5Ys.)c5AR89:mpG,:r",":@5pK(9#jj;C`E"],
  w 29 13 0 740000 740256 21 684 ["LW!LS5`HV{nk14o?eG~5Z&<F+8M.;^gUvtN^>43e+6KjKEFTj{Ug7d.U~J]AK;e&","[Ti>:q}sof,c7;Cpad$b|53X^Qg{5}{>-a^F6n%6K%Vu+bSDXjk&}0;^x^:D%Vqe","+pw"],
  w 29 12 0 750000 750256 19 591 ["|^B>O}vVtzL_JR?_NgVGgH9^vJC@;#1Barw[bB903>C(XP%f(z!cNO~0d9I_YazI","#HPw(/'S=7s/i`xd94&;H&Rdc%{&+4WWRTTP;g9z6/$pu10-U87"]]

private def r29_16 : List (Chunk 29) := [
  w 29 11 0 760000 760193 16 474 ["`2T0Kkjl9T<;9wEy!4fQgDAg,hv_^9!_RH9-Z,k'!h?9MZ:TP:,kYgR)z/XrHKs_",".Q=HVYA?s^(b}WdC_!+l}vlk$j&e>^r@0~"],
  w 29 10 0 770000 770192 14 396 ["vRgLAi/s#]|ri@qeiS,gHT-_u6&ag4D/bz,Iw['*fU2*DvJEfJu8|MP*vAS,SvJ^","JRF}c/Kp^7#?6&eRtb/p;9,"],
  w 29 9 0 780000 780192 12 325 ["2u<Ma>=>BJJv+:lT;nb@M.ao*/eVg0(}8Ju1bX0$/]2+9!RuEDD2(5Ua2E7smJn:","T!P$:)8h_"],
  w 29 8 0 790000 790129 10 257 ["*-$;!HP34H[;p=1X$>F]?ZZkP55S!pHPW5&MN^CCFgv/M%P[.i`E|sd~qmlUJ"]]

private def r29_17 : List (Chunk 29) := [
  w 29 7 0 800000 800128 8 197 ["+KPww&ch|-J7|m+ZvZj$cRTxBl5qFSk}0%QJY~(z^TIA<DauO"],
  w 29 6 0 810000 810128 7 165 ["eXwu$wY3Lm8~?C`SY0|K6i~_[hHnAO8IQ7_W'Ql:"],
  w 29 5 0 820000 820065 5 112 ["=LvIs]yLj_puUV'=1RM$+065@J(E3"],
  w 29 4 0 830000 830064 4 85 ["#mbIuC]h.dc1`j=xrpzMl|["]]

private def r29_18 : List (Chunk 29) := [
  w 29 3 0 840000 840064 3 61 ["HY<ujlgL/.E`i]."],
  w 29 2 0 850000 850001 2 38 ["$>QFOIT#o^s"],
  w 29 1 0 860000 860000 1 18 ["0#tz"],
  w 29 0 0 870000 870000 1 17 ["#SJIb"]]
private def chunks29:List (Chunk 29):=r29_0 ++ r29_1 ++ r29_2 ++ r29_3 ++ r29_4 ++ r29_5 ++ r29_6 ++ r29_7 ++ r29_8 ++ r29_9 ++ r29_10 ++ r29_11 ++ r29_12 ++ r29_13 ++ r29_14 ++ r29_15 ++ r29_16 ++ r29_17 ++ r29_18
def rows29:=rowsFrom chunks29

theorem good29 : ∀ r ∈ rows29,good 29 r=true:=rowsFrom_good chunks29

theorem sorted29 : rows29.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks29 0 (by decide +kernel)).1

theorem mass29 (i : Fin 57) :
    bandCount 29 (i.val:ℤ) 56 14≤(rows29.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks29).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 29 (j:ℤ) 56 14≤mass j chunks29))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total29 : (rows29.map (price 29)).sum = 280101 :=
  (total_eq chunks29).trans (by decide +kernel)


end Final50RankReceipt

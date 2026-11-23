/-
Nine-factor witness construction adapted from public Proximity Prize peer
submission 657, commit e07f14a81dfe2cf1bda985e67040ad4d31fe81ab.
-/
import ProximityPrize.SubmissionLower.Final50RankPayloads
import ProximityPrize.SubmissionLower.Final50RankReceiptFast
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Final50RankReceipt
open K1_13_1_1 (bandCount)
open Final50RankReceipt renaming witnessFinal50Fast → w



private def r50_0 : List (Chunk 50) := [
  w 50 56 0 940006 940261 100 9115 [],
  w 50 56 100 940262 940582 100 8616 [],
  w 50 56 200 940583 940903 62 4926 [],
  w 50 55 0 950005 950260 100 8785 ["n>N,~n~F!1&6toQb1]1L2)wL$zSAkc!K<#DGnBHxWJx]iV/A'.YbYIU<=R+=P3D!",";JlD%K<+,(+R:2'bsS)/0KwXCu~%==n*5KbySt*s[V~ZO7ULM$vO6cC*k<{qM0Q`","(B`z{mxIf05wBvSVZRsfn$JduY%7ppS}jL36)"]]

private def r50_1 : List (Chunk 50) := [
  w 50 55 100 950261 950584 100 8252 ["n8dABiHGjiDhZ3YU^t9uuqeXB:BFq`=i,|+[B3yx(o5CH{?}n6J,,Y3M6t4+%DIx","|!Xc7k]*d.5*j50}gc!-2OcP1<p$|Z0;}>d3{B7OrWIkk{`f]V/1v>,m40/^sm<p","#Nx)'z?L4|^,y!>07=KeA`'TuuW+q?P4qdnsenzP("],
  w 50 55 200 950585 950902 57 4326 ["nZfzhDKhC8E+?h8D!Nn]4vY&'h}/bSgPfFCgW~CGW-@j#B2cU[YJN]4p/X/~MGL3","-M27_oT+8v+n*n%H^m3hj5iL?8X)NWKC"],
  w 50 54 0 960004 960259 100 8472 ["U(?u94{D?n1@!h%MH7An8_EL*@L/Bap6&dnE^RtUWgY/~m9y;6WC6__RO,<dj=W.","bq0Nx4|?~&$$~JhH:/nr,%:EaI+jGJ%R]?L5>fIdQ3IG?dItErIf6Bxls,7IQbW9","&V(zX4fD}XDaNb?,2dX7a55}oQ[V|~OtgE:Cj5g{a|N.O*c"],
  w 50 54 100 960260 960585 100 7890 ["]~}H|$!/+1V7`j0}0[x<t?cMzbN;e<s?_]3:-<n&4|;nik%/NvST'Kr*Z(<Goc*|","8c0y]fwTuE.%e;<9P3X6wFKR6o&P.(ykrJ,3gKR9)a*ug$(,iO?y(=31TE-M-v)B","$|g_)e2iaw7rlM)l1Qq>s;])i*.Tg<-a~%tr@=Kg>KOb6(f'MH}g"]]

private def r50_2 : List (Chunk 50) := [
  w 50 54 200 960586 960902 53 3853 ["_lq_JL>alNl/&O{rSUcCz;9J<:YB[(SanUp.v.lE}VeUOq<ewA=uxmS2j/.l86Dd","-#XgDE#xL>CBBN8,<V-cci~{T%ljalYRcWhT@D/<]PtVz"],
  w 50 53 0 970003 970259 100 8157 ["jZ^kpcKhV'-zC'2z~JSz!8}~{uOs^Y+X]_Q_YjZeE/Bs?9ZH[BS/R8R^m</gT[#>","[2h~+tlnzZ@H$7mxmA|D7V9_Pnr}vvI#7?-{=RdLr2&PN0c{[wvdM10w??^(p)%'","/k4P%-m,zRTey69l&^#{Ha1L9];Rx1PAwvHH:d.X:6X`RL<n30?y6SFD#;)0!B<U"],
  w 50 53 100 970260 970588 100 7521 ["AE$39}*1`pRFK1t.@Fts:2(a.Tej0cvc3(0q2b1+M{[kD-=Skq_?IsaR?8&,QT97","t*J<$@/dTs*~X[-1h3iI(Ox6rdIXPO|v3I(EEKQ#,]8GWku^@.z6.Ka8r&'dp1YM","mg+%ZW(Vk8%,w,'6{w!XGe>vSy`HrQOAOYKa{>}Ncu93mea^A!>%;!r2,>b>Z?=j","$B1z.C<MV/"],
  w 50 53 200 970589 970901 47 3283 ["S[8:kFUoRC9)ByTF6sBe?8u&+I7R15bi*k-b+3[=f9UjvaUU9siQrOYqM>MAks,;","$|HQJ4*7=FDKW[Vb>[|'7='(NloTn#f&}om/IPm,)h{o!P&:Lxz"]]

private def r50_3 : List (Chunk 50) := [
  w 50 52 0 980002 980259 100 7856 [":FI?>K83ACNxX$3nflmCVB!&Dw&XdF;L!`:{u!11)ak._c&lNAtyLCic{zs%#aHc","23]iP3OVS6kA.OOC.};Hm]E,k(ffzVmu:<kDFbyQTdc1V3LPIX;{fAT?Vux@M{@w","7%YSy,~{t1b*Muf2Qt(aFp#Y54Xg(}>}nq%B'U>JyfR$pMBdaw(k^vnmIR%6E15$","/c#Na1Hk2nHSg@+d"],
  w 50 52 100 980260 980641 100 7178 ["R;w9dgDTU5V&MX1emzfO(|$'@@$cB/<_c%8f$<@v7<alx!o=&kOlZ6LNQW4_c]gK","I,|},C})'J(HAIZI+yH6EJ0UTr%;SSeJlkuN#=okZL=4MAlTR>*'O:p&EdEj98{y","x$)RKb~w|IA{JpI:2i(>B)D6{.;4A%7gX9nHT<Z&AVV#@[:8:UKYg!Wp4GwMRYY?","O%(%@eq&?&]VfBhE/kuJds5{@Zy6"],
  w 50 52 200 980642 980901 42 2815 ["vgZpM]OER?Kkn,i5b0w@f:aX.0)E63tp4&i+rpi^6o7.CYuUxEL0'yhF&+sE2gVl",".~)8v9#G3[q!cT87ex?FsK[s+NP-Fx`2s7v#:%nX2J4vc*jC.)i_(]OT"],
  w 50 51 0 990001 990260 100 7541 ["yrq+YX6S6+q}|JT9,m{81Cwvv/BPk)UJgWXQ!:c^MeFab<YYvBU`Hr>X&l2~-F|.","(imV1JsiFgAl<6rKz'yB}D(p$w8T~Aj*.k7E[BSKvMZ`l0oWXShR?qh_Qbeo'3*T","u`QmY<0*Eh]1%NhyuC9HUiQO.S%J|)u9x9aJt5u}_I}Qt-`x)$KPFg#r%E;C`OJm",".wR{-2sXK0xJCLHvK4`o3CmK/23!FXU]"]]

private def r50_4 : List (Chunk 50) := [
  w 50 51 100 990261 990645 100 6835 ["}nVp>i$^|j#TE_TLxhAyS)z:8p77J)%0N_t2LcQ_lKM]po<Dt&:X9&@lI~<r_[IG","+pvYEbMZM[)^1}QUpXWEDv&~X*:1IB-C+#YQlG-(Kif%&WW]*!Bam9C7G<Ymn@]I","*N<gVcb9iH7A+wRxn`YIh8oRLR`P+sgN#Ymz_%f8LZy7n+j&sZyIVGj9/1wNLnMj","-GiU7LVP)>4L[)ad:#m2tU|/T2E%#?{#ds?oM*sPRQ*B5x%IPo)J}R"],
  w 50 51 200 990646 990900 35 2259 ["A@BND%@}vdbf^$?X}&>^z-Z#FS$4J*o&!VO8cXf11*x(@xlk>Wmw7VyW>?pMk'39","Qr<]ifUQZtzHUmyA_$D%G]f_3><m-uDj3;x@Zc.rYH>C['1[fqS"],
  w 50 50 0 1000000 1000261 100 7235 ["$1,[grb?C?$8q(XQEbp}#K1;<**Yan:|ssr|2V(SZ6=*3Jz@r6:s{:Bp.^I3:Uz6","1&~9Ba4]yuF0r#:zuqvNX8GUDs8$jJ/9VW#$3h|Tu}xw%K;[Hb}%aCZC^x(~DG,3","p?.Y*E^ZZPDH28,!2]n?SokqBU;oow8<|LPS`)bIK+ICNFU)Dk'K{F8i/K)q2b5O","&7>H,{.{eBexakT6TT)C;V|vxK[?rmB&u*2X$;iqADo%gSS"],
  w 50 50 100 1000262 1000649 100 6514 payload16]

private def r50_5 : List (Chunk 50) := [
  w 50 50 200 1000650 1000900 29 1810 payload13,
  w 50 49 0 1010000 1010263 100 6899 ["`_D]/:{pGI'0Tvhi|&AByP:dMUv&#my6g%DP?+=U6V3:c%1%R0IiXjuS(eD0<8u[","^TkXZaOOd<H+kK^%fmTh']&pp;}z:&Jke*Q:.%H23W5#_fh9U.W6/KUI@6txj?]i","zOu{e('6VB%>#s0z*bjT'g&-y%t<wMlo=B/J7aB<z8)ktSpK#,C^CJd&l7ph(A[!","%i=7l$#Iyy8<*2SjDi`ujs.#>$l4*1-^]f^lVyiY$EB|4lSMJua,wqVV2ZD#$Q$"],
  w 50 49 100 1010264 1010708 100 6221 payload8,
  w 50 49 200 1010709 1010899 21 1265 payload20]

private def r50_6 : List (Chunk 50) := [
  w 50 48 0 1020000 1020265 100 6570 ["Jn$(`4z{/WwLhey;7Tq4CFBh3%]L=f:SHCLkD@4$3D`d<Ok-i`IG}|N6LRDRPAdh","2.0g#:$X*M;wUWwkw56S69uH?uE-ZeVWykJ0u'RY[-#!?H;@<dU8&FCO6uTs,<YK","V/.+[mnAKC(T=A{L#zn,[;q|H=;&c@'kW>#TW[7:^o0Y7}WHJp&5#`yc2?,}m[)-","!d,|CS1:#>/}^55csn0aXs5vTQo$t*&aBavnq}OkHd!sZt<Bk>`<?DYc2>u+3-&h","(}3t~P^2Rs!La$je"],
  w 50 48 100 1020266 1020769 100 5953 payload18,
  w 50 48 200 1020770 1020899 14 822 payload11,
  w 50 47 0 1030000 1030267 100 6252 ["O<o<#Iim3RkuI}G+'w!i4OO:'tQgH;A=%1*rAcLt[f)6GDIDj^tD(Yb7DhG#O2s3","(35WMVZ@5P5'7~-r/@=Jp)/(XhHHW1oZ,:cgV7T[v$N]1fbVRHDT/'fNw|MBa;b/","5xH#E;l_D(hod[D6)E&h;+R`$&}NSV!'?p%7G-KqZEeF)>R]1qN=^xbtFH_QFu|m","D`jy%4v3qCU,e-&RxXZ<MJ?yT[/uzI]ti+q8fqZvR0rnr0Wbn(S05Q-eS94?N5wt","(fYh^*GwlkFa!ZYbP8?8-KJ/nmj$CMJhFU)g)y"]]

private def r50_7 : List (Chunk 50) := [
  w 50 47 100 1030268 1030833 100 5711 payload26,
  w 50 47 200 1030834 1030898 6 348 ["''*<pfK*jt/{_+Rwy>&v"],
  w 50 46 0 1040000 1040269 100 5947 ["9yJPHBcHV4U@?Kw')N6P:9${Gi[E3odKH}&y_#,>X|Yj0OY!ZY$*%G?`Mt(RcUAa","6}B}e-mz}*b1~aIi{5,$2oa)>d~8[TuV*S&_Sv'q2QEkz{P0:@XAX,*h<uToJ?La","c41BU?Ldnm&Rw56GYg]MJU.@(AX&S>n)-cKRPdgj$J;Z6tmm{%&.vCu)iXbhtmFS","$.{`ebEtMP_IfaFhw-rx(;4_MD,<itrO5eHjSZ.*(|wwp?A.uj^Eux&+o3!g!sxW","'49@`POLiq.#G0JKhe4XOV^oV$iT%?{!~j?'Ipt,Hdxz^fdQiTrn`%8t9sx)"],
  w 50 46 100 1040270 1040898 99 5453 payload27]

private def r50_8 : List (Chunk 50) := [
  w 50 45 0 1050000 1050271 100 5658 ["uP)G^kqxhU4p?%~]^UPm{MEUth.G[F`9|Pp-lE{Vff;5,?o8w1`AezWXd,nY2j5q","F@hWOleVLNraA5O~ZgUSf4,|5WaG0^H%+lBya&rf&|;OEJ90^ntl{IwH`^eN'b)6","B^x{8e(,-4h4r1DuiymgOy{&5%]7Y-i{Zw*><[Ur7X7o]{heQoq!c(k1Aq12[Wj+","fZx6cX~SW>8e@@;&q$:YK1s%26=(r<gY*om%`[6vGW59R$6:2!q29^5`d)tq;a|o","/GBu5!7N1gs3Cqu_AufY_/i1UUGi;tz|LG1r/OV+lrT=ND#YTW4&t&yl%QoJM&Ki","$oQeW:yE'FDINxe8fBh:Gc'"],
  w 50 45 100 1050272 1050897 91 4835 payload9,
  w 50 44 0 1060000 1060320 100 5393 [":jL&7Afk)(i{{bP<j2q.8uLo!?KgJl9Y2AR^)k[<1~OAdnwf_q'<G=bR'gRtr,Xm","Yz`kz&zqmg_v$eu%Y7!=337|?b5W1g!xf92W6>Yg`eMIt{#VjFq;efQzXx-8BYGD","0c1f%+-S:SQRr3:2I_g~U,pkqb4%YcV[sCl?gX-.-Dk]GMUj+JH2I&Z4bq8C)WIH","iFaw$?T;}:gZ#?NE`RrvOSg|`*9fu0aDj:.fLG!X/3k1]_Me_'gx'kSd3sSEA;P#","o&??]b?N6<5_7{,X`de@r9zmId1x#UTO*9pHs#_ZTXEBdba`CkP~@zokx-:mRE1%","2Q!_b7&D{@m0e)0X#Ojua[/-kP|)}Oa@CO>nn?msPi{WsOZb>x"],
  w 50 44 100 1060321 1060897 84 4305 payload7]

private def r50_9 : List (Chunk 50) := [
  w 50 43 0 1070000 1070323 100 5149 ["HNbaw9uJ1l8J5<OrVZga=OC.coJ;jBd7kLrlWq{iTacDwE~`w&~3(aV}$ct,&k!4","UJIquskI|D03~ZvJ(CKChPIZ&{mYgcDg)--:ZFa#BQ?@9Mo3e#DU]l~d(z<a[,Sx","*S?JIf8d11+}dnH=4{y.Cp3HaY(Pm5dTc8DL`}`0Huzm2d3MyQITl{^.f&lYsZ[=","N5JTl:TNO__8inJMyN9z5z!`$)~SvJoC<fV4tlYE[f>jsFjBM_;Ywr3W`sEer'Q_","iZczR9CVVqX=yI/T%n<aE7S8,[Uiwo'=W/`;f6t,r8b=o6vN>HhA-Xl%/VLG#p}}","JV!^2%&p#IZ:^d~kCi'j-[$^)kaGU?7Mq'2M7a5N*eeho6Z/A#:ubIV[hJgP&@aG","$G&p>5:rwf@VR0xJO"],
  w 50 43 100 1070324 1070896 76 3753 payload2,
  w 50 42 0 1080000 1080325 100 4914 ["_D?Mg%AnGev2>*kpgR7vZTnoezT_sW7bmB4ifzqZt;SsXImJPt7l7,7J3*c^YKV4","r8n#53.TKAuMhao_)8#N>7|e$7qldQK}pv`MS5A&!H/8h$Ls5+'Jqi1et|.#_9@E","[Qr(*O_~:tS_mk!GFv:[c(TYnITBy|'et*a.ed1F#gd_jF=9g(E;r]bq~{YOYeQ+","<tjgf[3|t1W7F7-?41;_UNPH|A?9?'[TB5'4w<sN_HhMDy9X_qmbcaehJdoIy]#~","_sp5WfrO?N=eGV-3C#$F'hzM-G`<fMj<B{2e7>qek$^Vhd@{!RGc<6.E_ALW[}'`","|uqdxG2?.hwIlTSSeS6ZLb83B$Vf.Ga3e]co}bJ)|<]t#g4dzcX$V(S,s40z#a~4","$?A-]g,Y.bo5^YP~l}^/l:A9S},8hYIDFA//`#b"],
  w 50 42 100 1080326 1080896 69 3291 payload10]

private def r50_10 : List (Chunk 50) := [
  w 50 41 0 1090000 1090328 100 4687 ["-zOzwTEx/@pT*&Z<,;!4E&h48gC%,tEMq/ph,0Z:T:;r9gS$ayN[qC)G+XcaGd_T","+YZ'Hdt:s60+e^FT<Ii51$x2V-@C*#t@`V{ntv=?_Lf7'HTlnR`SIOg6?G_0^YO5","qa!QedC2X=!*Ajp7_D2Uv8Ev8[g;>NVOoT68ypaIl_]iM8_6A94]tNS-g*[P]=uZ","7;IU.%zf9pWTTpz.K2?Y3hJZ)1hI)u91z2r~wd[Rt3Qe!HuiHUY@D>J6:<hPY3)8","2+}hgBwVn<w?/]ek)cn[M]s^}/e2^RRvR_a}98J{3XdOW4L$D]/(C}w<-bC$JT5>","Y}XQrMi+k-'u)@UjZ@mol01U&8g`?#P-4`d2%y2j_z#ywP$AejGg(cJ[F*UR5<.0","i(Wo@DeZFA4Ddb}^mL14A-2/@F71EUXz$Zu|G.4p%Fs9k9,3rlcehC}$'3-%:&^O","#x_"],
  w 50 41 100 1090329 1090833 61 2815 payload6,
  w 50 40 0 1100000 1100330 100 4467 ["Tj-P7B{K]FaQ`GlgTL8x~V(/Fz,|v*Qcdu3o|,8[e0Ju&LhA}F0@{.i~5^b33t$,","Wn%9Jj+=pfK{Y^6CC8-QDrbK5[MSD$J`NN*5EV{C6hr#H5]ZJKQ7.|};IYyk>Jl'","P`12g+V%iLkp&t4+WQ&JFk*DMX||Y:lIT8mnQb&4~8yI!@Kmn:INJIw~+AS@K;9o","Mxr@:YG_j>o9oi(S$^)wqfcw.s/rnDR|j8b}R:o<~l7DcW]xHvb:wp'EHg%S']f?","J?J0~:Vq.incEOQesOe>&9*jH:1h5kjo8}RD{F+~cu'8p`BAe#=M5[9'v1DR*D>!","WWdIpS,fMgQ-6D34=BjE{c!2:.^FvE.|DmV_U}xjIaA0yR6G+z1'yy!_,}M&t~6-",",I[_9DZ|Rv3i,uZwh/Z4KNQ9CRZZ5NVf#UQR4Xk#4n@ep}vzaPrBF1IwyDb2X=pP","0[&.#dAeH}/L<1"],
  w 50 40 100 1100331 1100832 54 2419 payload19]

private def r50_11 : List (Chunk 50) := [
  w 50 39 0 1110000 1110384 100 4263 ["TDF?W2+x,q3]+jiUG'(zbeIHBdujqpU_f8|t@+nV;F70$0g-d<2#YScXhKicdJ0m","z@^&H0tbs<m?EuWqe)}QU=CE3E(_Y}-H3F2?ZV|xr-:Plq}16F]],H_eNz*E&B.[","->,jf$pT@$T0aNCQgpZ/D[Mq!MyWI}x>6<ICq:aJ|G9nO`C}u-as40r6PY,i)(;2","&4KSWc,|p7[&%iTXnlcxwB&3`s4Xv3dK:SK+KE>,G6(}42Xr0b7&j0.4sTrunW`a","*vq2%U8fa`>lV+0zbj{d*PV=nU|FB)VU~eRX)7'Q`F;=6`h%heqA57>80IE$an1j","a[Eyo()46YcVy+k-GM8Qc?$>Zn?F?/rq[VU6uh4?zfmQRi7Ly6AeF,5i%zsQ}&^a","(6*P8G/pUu+p{4<Zf$*7{r[KkomOc^(hl-Y(W@]&hS&L9HF~lkU|S`6xo[+^zt'H","#^lSWHgd~foR7.V/6>JM50=4"],
  w 50 39 100 1110385 1110832 47 2046 payload28,
  w 50 38 0 1120000 1120387 100 4066 ["Hq$6Ab$nt&bVV)TTeisU<(+ngK);Bj?!pc8;5:rIT*8+5bJH^Ls[QQnP!.1/1yVe","S8Q1@[(ydTz@8P,;,#T`At{|'&BG-*K*s6(oS{!yt9abAb5IPKKPWL$dKvUkB{V>","$IYQw{`=AQB:syu4Z9I#Z}1>h7OBwc7bo#<Y={Bb:qNk6|$-m6&y%R@dj5$~)0Js","rsO&Kl.z8N+1Ccz{3%,!J{&)T]|9bW1}Z4/.AzV53BZ)J'('V2ZCvCo)YKT|1/2V","b]E>[Kp!uJd9Yp)c$F`zB5K_]uzZiQ5Za]Tg0P`TB?~h3CA+1@(%o6:`{5YT[5{$","lZK0jJjR_('+a&'?~i?T*1Gf%]3{BtCH#v&F[n6%@xd$+8O>rP/gKl;;n>Copw`f","#@zj;1FxN8~U(c/?kPffO3nem32@4(B.J->av1q*gFz1`4rXR<UNEg%N$Wj3S1,H",",%H]Dn{Pcd&-g(lCfoXbE?l%[}vZ&}jrr!KkW&6"],
  w 50 38 100 1120388 1120769 40 1695 payload17]

private def r50_12 : List (Chunk 50) := [
  w 50 37 0 1130000 1130390 100 3880 [":}jrO{mS=m'e0@~W3q$YAnDR?&OH='X+~fNPTK:w>;>&-I'Y;|jCao<zk-K}B56T","x4s<wYlsABYhy1@`%nfehkc$yZy|(F=wP3sI%AQHz3a$@<(uj&v2rn/4qk/HkSOB","DQsF%aG1TuOYu+qd,[Ln~A^?eI#%')/K0JJv_D`%)}=#/bDwAtUWsZLrsI+}Xhq|","^fh:7993fV&yS!de?W2Dn/`zyiydUF2ej$F+5X?7->T#gyRtF3;YjwUmbn*B?LNv","Gr<d1JWc;s69+2_H@^^AJ%-MBTaKVli!=m@Q&BS;nU6{[njuQ%0sv?Av?s1zY6o$","<a)dZ>OHOX9Hge6A,5a(,N|6wK{'M9,Wg{*M$LwoRH_QxZkK-S8g^MV:kyq`@W~%","6/P1RSg2z'/J(?L5/.XAt6J|?G@IB15*hE-Pw^a<jM4wfG<TdUo8wr'=W/EO(>i;","#W'yM4dQXT]9UXCvojJW<4;=v[&r^]^F^>=l|I*PxS"],
  w 50 37 100 1130391 1130768 33 1367 payload22,
  w 50 36 0 1140000 1140393 100 3708 ["SyBgO}&ez5Wwan/];z0X*>'5_dr,;JZ/H[&Rh*:Bskj9Ok3PpnLfS]Uq3=as#O!$","uJNfj&sxE$qS8~R},zIQ=ecZZ$X:8']_Y~!Y+2&ml94.^eHo%?7K.GiQldRniv:[","|[2W.xtg147#b=*[mqrPACe%F!;Ax!0OerbjM?D$+::sY'g})i=96w*qkp#sz|@k","I_V?[86im-_j>_$|l9m{><1B{CR>&sM{cq1bweoNzbDV8Rf7b;@S9j}7<@0QacHb","9.h.%o/iZ/3CnC>bpj4owqPg[sTG@74._WI2vSGz/cJinxkpcQ$e4J'CxCB']/)/","+A;S]FN&mR{#Ecmq8;)Qs<o_vpe=Atz,*}eo['%gmZ@fuF$eNP)70$rvWN~Mw}&S",":a|c72(TE8mj}U6v;TBzM.g@z|xVJi:lv|mxRX0CHXkZsN,#WsYm'sl2Hm'(J6eD","%h}7t|2LQd2>:M`TQ$MPp0#d{bU<V{)Rlx<GD|]jr^gi]U%i"],
  w 50 36 100 1140448 1140768 27 1095 payload1]

private def r50_13 : List (Chunk 50) := [
  w 50 35 0 1150000 1150451 100 3553 ["v8cp*Z!h!#P_Y$S0<~PMQ>r^K4I/F%b?PI3T2?azj~.Cs3UWn+e~7hb;rQ(D%'CB","e`R''3`PgKL13NtdN?JW[~6}Z-$4X~~Wa5-H]s+b^J4x?]]!(,VyvL)sf4MwWF5W","uTG9^/|3yW<!F'LfxfW3Vrt*)`LqfQtlL,bx7j2(*ah4pqOsCA}h[o.AG$->#,^~","Nhv:7%$QFG_KWiM/+iezN`k(Hc;Q*dwGpyfnz3.z!w<E>EF7DL?TVZ;]fcm^(kuE","NqA|_7N`o^7>8HqK'uR<qk>r'.`w=a'AYU^[i}%~w9P.%LDa<WlhF7)>$o4ra@jx",";('9-=2K[9OZm%2iSZlGU/5rWl%S.^C#2ru.u!F7u$PE%pC@U0+1poKR9Tkt.1?Q","XBX[-7-?40,qr~k=RshFr@@2Ga;oom?!|{y*&&S/DVNfiJU%iM{6_1PY}Z9Gh/?h","#I,dpANOV~%7KvBJTq*v#<CJLs1[X5zcxJ)p21Iqy3Y8{nO1BYQI"],
  w 50 35 100 1150452 1150705 20 793 payload3,
  w 50 34 0 1160000 1160454 100 3409 ["8isyP<WT~Y>@;0(w^/,#*`e76Zx^<lWd4*?7IkCaI?*}-+j[OvL6V,eWt_zKMiJ/","<E]zGY8axq&qSGa$hT0i7lI0x$J8XIz[EIE4.L9P+>d+=ei&<?9;=wUpSPG*(l|8","=|66t3X8r{mSZ1rN{]dQ>T,/s%*F&obyV1onrx6MN?[~|U}LB(jU8Hu;v`H{iztn","KXzByQ/A]?|4gO_mHVsw}#FBrrYjW&j#S7*oEl3Q8V!f,j.9(Wk,;'bT)n*O.0Ex","[2Qx|pl+xZ.nc^jRY:.}`i)w&_1jSjsl)%J!-p'0@0V(bO|'{=KWAq+s3StMNmyB",".sjC0CLMv8TRHV`B?voJbN+t<1qmK<j*A=.C/ywZq'KfZ${8|r1ntbTBWK'TCRyp",">H1^UUYD$rk(nhMW'L~$$wy[&JoQ;f}F;qgL3OXBLd9;Q$NmfF?`F]ro%ZqDW8+a","%oxMSW/SGWg0.[_U;D`4PGienopNeBh<nPTX9Q%LZui2&Y=-Psg"],
  w 50 34 100 1160512 1160704 14 545 payload14]

private def r50_14 : List (Chunk 50) := [
  w 50 33 0 1170000 1170515 100 3284 ["5=*O=@Mx3RIW5BFbmUr2|(aC{#7Wo-*HHcjWy,<O?YOB|t,cNt|{I]5/(#jj8Q2~","H>>Ugxn7?;rb^$EDZ*gRxW*-?7>L$?u-m4[NO+U[eBj2.v7RX(SJ$d9RNSj'7<0j","JdxovofGPBP92lD|{|x,46xhn:ByT>ti8gS;?V$W<-9vIx0E{+N8/00)Z@X5yi(J","BBc+Rfq{lKYOCE9]=myuAU@@W6Mg>y'5%^s3Z24/~|FoR<#Z9Apgj,S35?4o'a3R","ZM;:`$rSt8*o1Co)`_r5J|(>,ABUVP,9e3zhC%q7d6cJ~+Phx@IO*3+N^]0IXN5`","5(3}zI7$JDssjztvf|}'M+l9Or*fQK$67$$@Z_DM8Zkmz|mjt*$GcF=G-{]1!Xb^","&0`pAs=K_f2cPZ~!.:9:M/*mZWbX6h;*JDaS]T2yPVJ9gP=t>?,:|R~E)3`Exx#V","3|P!2:=vop=jFHc--;n*bWNhm9-?.><iKYgEyN@BsUHd0"],
  w 50 33 100 1170516 1170704 8 307 payload4,
  w 50 32 0 1180000 1180578 100 3170 ["u]5[x1a_./k5sJ5!#s34l_:3m)3bLA>#2I!j_z&$Lrod5j|+9GjVrX>vy>u#u1#c","]|[W?)fpm#^+I/wHq(?g0)99mRz]2=<ls0sKo=T9Qor(bnn{LT-FlrlVjN1)fNQi","go<@Y3@h(i,Jei5d8X!a(b=SHrTD8bmroFQw-dHSH(Cwa`38eG(abkye5aV<}E?%","+&$VgmXG3*1egW-v?@/so'#H(%A{t2x6$(z[7G>,[g0LPWNX3*a~&&LE!/BsK4S{","GE)x/vMu-xdEW&0;}=BJ'p!jL3.5gr/V+Z-|,}=+L:gYrs71TuY,GseE?@||JA>Z","K|)=k2W=RalvsZ,o+?roBFbe,g8+!|WCx;KVx6?B:tX|OL4^X$Hly5DpTI6uA^zP",":1LMZtjq]|d%>xhIi5@N-jpYAjVMq;fZg5]]P*Gbmo@l)7#@?Ml|}hnmBC(qHfLk","*k'!zN+)C@P_HkZ=zKB=>F*wz4?^.DZRwT(e}ei;BhUVZf"],
  w 50 32 100 1180640 1180641 2 76 ["#i2GG<Je"]]

private def r50_15 : List (Chunk 50) := [
  w 50 31 0 1190000 1190640 96 2930 ["N}|!Dgf'lZ@AS*>#|1+9hruq|r@@/Ng)3<VYXb})p2,=.y?hGQ,ii1V^Rqv01ODg","Jvl9`xA?3+oI?7AKU%C0plt'XuNtQdfJT9c2vAZf8L[1HLqr1&x<It@K]7NKJ%dj","4^MpJ7t;Vv_9J5j_!jfMj/Q8Y3mQ43UEEM7r2mq}[|B}_q^K84aNK3_?+p|qfUUF","n@D9B]e.CyX2@kw~<v+~DY@y4j-PO!`e:)]!kC7<)5oR:45}wT2u7uW_x5iG(_y0","_JwvOV7_yR^sW5PiTT6*@j,yZ'J=X<^)O_9%3uUBf(@<;dT-jHX=P_!U,!B=dL|Y","z,(V>SFV>h&,CPm=]k1d6ZQOm2cG7'k;7s=X:WE$M1Lw!Y:r9kxq^)lx+j*8P/`t","g0XJzJGM:bA.=,2R4EI^bOC50EeVm#yi]G6?D0]b7+}jd&At>K#^,tA]MQCNRu`d","-~H)|3,Lmys}aosJ'TF(I?_RhhQ?"],
  w 50 30 0 1200000 1200640 91 2666 ["~qBkz^$WEY8:)/:(Ex1C_P@$TasKhf'kdCqWf=i{fY*:'~j22dBZ*GEbqM@5JlrI","#;:c77MB0r2P<er,9/imG@-NUezHcJ8&?/19LmL/kE,zS/5c0bjM3[QY)R3%~>&+",":r}V:;dhf-AzXm6X[bO&X;Y./9Vcu9BH#mjk?>kWQ}lmacH9)#rR%a'_hH^/lB1U","S6`?<MxvP3:=w[q.S-6sC*OUQ=?,^wrG=s-AD,P_iyYK2-$xBC[F;$'oVT`{1>0K","@E/TbeK&M>v%c^jGZYyJ1I|&z57X8_GUw^kK[KTRvFB!5bEu[d!F{_5Ka/J^+87j","]C0#l*M{I]X%9Wy(U*Xqcr}TQUp{RRN9[f?`WF[72!i;qqsi=E+3=2ttPj<foG7?","V~YH[S&@G0{Uup6biT|/s<[Yaub;SNK:OXV{'@%C^oOiv_>J!~,uUTY<Au6?45S&","$(TZP"],
  w 50 29 0 1210000 1210577 85 2387 ["Ndu#}%*Ka8T}jOp8Y!mEzm8/O_Fd6Q=5&>$c0pdRsG6DA%CqNF.X(344+H/R~Hg-","&xb1.nKu._6`Uk-'kb-nUL779v>YH_(H]7zO|OTimaKUqngWOvT>bZ,JhLgh*={$","yTOJ?eJ{va:_c+f0L[5NvbX6FIgZ:OXvf}0`m>U5%e/Rg1:T&Wn&*_]-g?'vl03G","GJX_5augY/?VO4~t7Ztg/iG|l`i.*N@G=Rt|eF2~5{N4lR-7b_l0nC#J^-Toq,UO","nKF<uCPBd$VuB$gdpaJQ;B{d0UiseO[0~6sIW|@f<bjdy}O}Snl~5-eyIkH)^$|o","rM'6vgp.q-Ijk%6k:E,@0O0H~&01tWGdeX]t?n]]<_q+Y?:hp]^5aXOHs01MTul`","#{LZ_gay+E.UzFDRyR3XWtU/q$n]28Ew%ba==qbO13"],
  w 50 28 0 1220000 1220576 80 2155 ["nqY8Lz]sk-+NndZHodetz)o2m<o`kL~]:d54h#JJ$VlAi%u*2n,Kp-%{}T#gHdu4","IZK,~?@UM?^<K7d=?Q>Hs{5&8=J'Em41hf$.hPX=@pFli<>q{YSni}+q&xYESO3f","(hD92_Wcj8%}_{Ht|rIKt)!.huTnXFy*~WR7k+@edCru53r$/KR&^0Vq}NWLB1@!","yK-rFfg6skq(!:Fu~'=B77P*by4?6XL+z;3|r*RSXfIG?2b)=-57_%U4R^T.y4p6","_EY92%&riyAgB,DP,[2!;-<7$F+,oSO',1r,yT>V^hWiA(QDc9hFH2wmV/I@eqYi","w%^a'VHXxI5I1NnIsoB(G^6+<4OS8J[2N-m.+=1BF>sJ1MtMI3iRSJZ@#PMH%8HI","H{s-ZT*h~VTv[4wh.KQj"]]

private def r50_16 : List (Chunk 50) := [
  w 50 27 0 1230000 1230576 75 1940 ["yDC8xd)}!f@qt9(lKC}%JS-_;a<)DP?~mfcuJqUKcbI]+Yj5eN0Pf)yf>~w;x|EA","OjG;(e}UBgSc&%hPQKfy3O~=x+73ArkW0#joYX<QnPvFMaXyQMHKT|-`bgn.3[j1","s?RhGHW?P|oBf!Z!6.G|sAM7BPN$yTWAnE/ygRqM'2Yw}z/IyUhoukaSx'X+-^m@","z?^CV]iH--u_@0qR7ZzXzBh<+xx@5-pQ@7'a~,mj>@iOb~]}S(fxM2Va0e>R={b1","Yi7{@}A'JU:Hx<<io%m9D3VjbM5Y~nn+.keF7Cf9'sNqk]1@'-%DU4TiYUQI><XA","$QuQ{dC8wc7(C{8c`nP5DU''gdub;~sA`H4A<4Ua#[{DfYX.B>IA?R?CAvA[7T.("],
  w 50 26 0 1240000 1240513 70 1730 ["UX,br3L*_mYNW@qvI%QFr;BJ>sY4H;>aCe<p?rZTZ!8I9'MFg=~=^:nGK@mQc$~Q","|rDB7A2oLmo&J-H?tDhqp<?`do6]BXw]yzY.,+2Di/QO8q[CX-4O`w2H8kNC+lO`",":lq/h#Ajh|VN2<#V{WVm`mYV{So2Bj2z1?LGp:?Z%T|bC06CNnyo=d2z;7^$^M'q","DR;K3NuY1upBY76BHzU*uSG>tVBr#47i(Z<?Hb)9Cs?B(r;Al3=#ZM%cO-NTXvzY","90b;%9r^AXaqm&bBlOsA>0qug@>}qBrOm7Z!g];c=|r:W`F<D.4}B2}b.%h_3H.K",")jWn,L7?|e/i'92Dx~k9.EHPRl%}pmLKiDp^YJ^PLww"],
  w 50 25 0 1250000 1250512 65 1535 ["wjMR#S|-)XfL%SXU%2u.ufPPTWnte/J>[1aA6W5'}9,J+Iis-e3t@_l?!qM}z5#Y","ymT@-=,'|?!M;SxY?P<~Om-1'OEYboR(f`GZHY|/HUn5/${O,~_%CQ8n`/@}XVq.","^'x9HV/2*z7BGw##R,>Z,8JzdEx)DKSabXf*lU=O(QCPn^p!?RbpstN*uZx&>GSe","eR8@Lu_['~+~G#w8-kd6;j$z_3lY}vllL~wsazfaNBt`&Q&3|T3h)th^jHXdYhng","UTs>pUL+'gb>8.GY9C;$U-:|C~*w9nMqET/du$'s8nV!,Wsr8$>DwDRV~9Ve@`!~","#1Qq,Dc!Z.'j0j2^tK!O{z,"],
  w 50 24 0 1260000 1260512 61 1374 ["o{?#zlu$:VapOxlgz0z4D;NO0X@D_lA_QapLr>5pih;5^(hb{KQ@1*{fBdK_oAI1","=TD<7lGZJ<$Ubg=4tfn=O:./GKSxt<hk(mNyQgOVCV58E_@{mXN7k~qZxl6Pq3aW","M=6+Ug22C%,[NV2zG7prGsT/-0ZUl.N-rHV@LxYnQvn{06[~#@)lfo<4Y(>AyZmt","o!9k66+{y+.]Y^iHDPP>t:}^FP'0lZrk9M..5@jhd'd;8cF*ED9'zTypRV[0~&#L","&#],pr52M~P(L>#!%>X#gbevm.8UVi>zi!c>bfqY|nvtA?HdJ[gL9^*)#`'0.QIG","#<Um`"]]

private def r50_17 : List (Chunk 50) := [
  w 50 23 0 1270000 1270449 56 1198 ["k,,u:F)=_G;68fPHQXq+N`:JRwnU]qtz;}<mwY@{BE;G!{dEAZmT/|0{>E[oe%Ir","ww+I%v4ccjY!q<{MR/JfAU%?t%9KsmVp8xsjm%6*04LnAzUP%ie2z#My9!}y~x1K","bpI0@#%vcsr]w:H-ZjD2uqy8-QqvcSG)1m}BJlfq$i|zk$JZ:`eJ]PZ20`aV'8Y6","Dp&b&9<r'b@R(`JpG6x}CD&0m-1c~=u|*b!#H)RIs`Uw@mr'JxikA+mWR?[/mMT;","={ZR%7j!<2L%y*pu+YgmtOP010TGEC}1g.oZTZc`20IKgq{q]7"],
  w 50 22 0 1280000 1280448 52 1054 ["HPj|{F+EgHB_(w)P}T~U0MHxUXsJ3cWQ{2T;A28vx,!G~XKBi9)RM7G9dQjfSm)A","nb_320/ht}iJ+d^IAzT0h;T^oH*xAK*38ZLa3-?#ZK!-/k-5%8IzXd.h]Vsl#y)8","2c@W9RVv9(Jmfxgx^V2cQ3a;L=9-kx;-=.FE<IzP9MX@MH,-HZek<]ah=QaVB!k`","iil$KPH[[x`~A8[mZZ=MEFbaC|NAnfyGo&#rn)dyWGaM$@K'<?c_#W;5?7DsG{{i","'p|vuF4K<rGrfvEllESytfvXv0P='fO"],
  w 50 21 0 1290000 1290448 48 922 ["4Em7<65VN@lVkb<D-H3y2UH#1oBD~DO8KeB1k[Xs!v?kKe&4cnJ:J$Wo__^#Rn3Y","c/J&Q_@h?r2-p-*q[HWJ$W&O@3*~DgNxVtCY0GNbX$jXe!XPo|a|IGh%~oUjrVKW","AFDaI]Y`caGu,F-.>dZIMsEiFe]#P3nAw_IQ;/wBW.UvWy~'Xt|8r>V[q:QGu,g3","gPko4*7[^<~{[04@Frq]JnB6Pb?j0yk;l{_kN9=t]O+I9@%r!f;rPUmiQ3lqWaP;","&u<F5k*T.l+HE^"],
  w 50 20 0 1300000 1300385 44 794 ["8T,SVXO]9jnrz$<(3*Y-bv6R<gGS'Z0CisTW.S$Brg%6)<rM:N.O#Ag%&4s3DL51","F5$dJT,MqkB7gX1^JEpn4AINOpQ9s&{2R{Q>u|]RW{hzjqWw-~8MN3eozRJWzEu$","U?=,39nU4ms71?xcL.Qc|?]-lu;e^^q%;8lIf+2#0|_ER:.vZgJD00XOLkS/Vht}","#*RnD8G}=s`j5m'Kzw}}[Q*??Cl^(o<Rv|Z('_G'G8yQ.<K@#EXsZ-R]?J"]]

private def r50_18 : List (Chunk 50) := [
  w 50 19 0 1310000 1310384 40 678 ["&A;.)-{9y@vK|-^f0q^WPD?+#S`K2`/@QTFI$7coe@_MG^=O'Za*]5jTr]VFg<<-","wWUrhPGi^H#!b9{e<Io}HmF(&oy0qdy%f2tElM[X<{Puh`i7_{]Fc]EFxF.c5{!G",";lr6{pb%'GJ>p~0pDQaxpNF';i&:(5>,x,YvA'j)+n1oUF(Jt7~1>VDy-UPD;.rn","@7.'RWdo1*gQ>^Mq9|kRZa*>Eb'j|(H1ggk?i"],
  w 50 18 0 1320000 1320384 37 587 ["L&:WHGfv7kJ')w#}*.xdK%1L!8:ua.ZeGk+eseP?{>!715a50I$!=%.}S`@`s878","{{'>#g0X]<|zDzAW]>j@s=amB$]!EHE;_m|$0A$Ap?Ua5EJ%EN:w~&Z,ChxMA#{V","}l;i}*qc[7xDDevS`)XO+>nKAw52w,-sS8%NT/tu=l4hcd-.-~}8Bs7iCQdM+]YM","#imaJS),EDAYKEmE}U"],
  w 50 17 0 1330000 1330321 33 486 ["L:TGGK@W{R]vi'#MAU|;MKjv.];M5~D!FVF.^?3c0+ZO`BHPsl<5fCKlG@Kh[>1B","VsU6r:ke:Nr9R8&/ag/#(LKF[bC2TDE<kVnH`,KG!qTc6NG,Gqg%(8*Z1L0fS72;","cy`X<.TH2L)ihw[L=~p%b2T3)6kF=wH3Gm<kmHlzO'<g4b^,c8n@].~;)gLNR<H"],
  w 50 16 0 1340000 1340320 30 408 ["tTM{pD|e}9@Q(Nx5[o`WAb=*$a,7t=%|S-,mJr+wx:S,Q^b+BNCM-ys'MjpiT'i-","Fp'xW,x9kn-:R|2~4A'pmv(fdZqn('R0hRj*bJZ7#*dOa:(V1:PT]Vt-|Dim_BS&","I(?8CaeY(mQY3)Pr@7*wKkW~-3OJ[U#=51lf_W{%tOJ"]]

private def r50_19 : List (Chunk 50) := [
  w 50 15 0 1350000 1350320 27 339 ["=ES}@9,h<1=}d%m?iC00g,A;Jt;qe6CU1SD;d8)S`q+)VceP)`RvBCCd5&n:-Hfr","&ES@ygwg'lq1~PKyLa`ETByyvIm!c8Q~,r#Kh]6Prn@q=4yRdviQ=qCFF~jFmEwN","(q6E=4]=P@`Tw@qs7X=,-ZI?C"],
  w 50 14 0 1360000 1360257 24 273 ["<2rziC[d&?$y._u^ZyaQ^OGoO_q':f@-u03.MJAT^Y:zOF6y~fV3[nSFktOsH;5A","},p|tG%v=f2y^G'~6F5C=OM.=zMmVq#=cDiH32]z4E9w@Jv!%,:84'F5o6oi[jaT","0-?HNA9|"],
  w 50 13 0 1370000 1370256 21 216 ["-<@_W>9[+A.=;>@t[<IRRDOD@iv2uy^.B[$)a|?Q*ZT#`N@Q@)|,kc5g&}Pyw]<.","'SSKimn6CsW6$Z2^weX9ckv;-x<y#LJt9J8AK@:ESS}a>$`Uf81LTG=BO"],
  w 50 12 0 1380000 1380256 19 175 ["2%!H]eiYr<h!ttM3jNa}yOEcLO1YS6#)?7q+Y!W2ah~I>h4Yc4>bidnp#vu:5uMQ","$)=WESxtu(,Z9!!yA~rM|3~d|7-1d4r[IMQv8b{"]]

private def r50_20 : List (Chunk 50) := [
  w 50 11 0 1390000 1390193 16 129 ["+@sZWDMa?GcR'2P]/_[k}zcC~LK]Xm}X>Y(0,agv~+SaAiF|iJ}m8c3,?(52C$Nw","@~Nis1OIO.exfkg'*E9}hRa,"],
  w 50 10 0 1400000 1400192 14 97 ["<YX.#NP^~.n9m$BN^g0*r.J@TN%8;%Sv>5W<WaxfB&yy%`rl&>Qit+jx'PRPg+RV","1prwWD:SS]9BXl"],
  w 50 9 0 1410000 1410192 12 71 ["/DR#X5yN2+TuHrCbrQaD)VU5B%5Gi9jk#Dx:rpW~/$wCD#)$!DNZIFP%,]xM<[5B","A~#"],
  w 50 8 0 1420000 1420129 10 47 [";q3Q}(IEzCuWuFd?s,<zm`VGS%VEo9jsh{P3wo:%3qAHzPLfH;otC:"]]

private def r50_21 : List (Chunk 50) := [
  w 50 7 0 1430000 1430128 8 29 ["#2t.'6r*kyvNQkeMCYlnDg7ZCL(bnx-b`&1wu{r@?>(5r/K"],
  w 50 6 0 1440000 1440128 7 18 ["%[!2DOE?*qT,UXWF*AG?:6E$BLuU5al!GX:TKI"],
  w 50 5 0 1450000 1450065 5 7 ["U^(!OsBO`pRWIPp4:Dur}<x}N*`(8h|"],
  w 50 4 0 1460000 1460064 4 1 ["&sFy~@v[FOq:/%8$xzMS:mlJ"]]

private def r50_22 : List (Chunk 50) := [
  w 50 3 0 1470000 1470064 3 0 ["$?|gCX7|Hk!d3XE0':"],
  w 50 2 0 1480000 1480001 2 0 [".v!BT}z!_U"],
  w 50 1 0 1490000 1490000 1 0 ["<8'vhk"],
  w 50 0 0 1500000 1500000 1 0 ["*S`("]]
private def chunks50:List (Chunk 50):=r50_0 ++ r50_1 ++ r50_2 ++ r50_3 ++ r50_4 ++ r50_5 ++ r50_6 ++ r50_7 ++ r50_8 ++ r50_9 ++ r50_10 ++ r50_11 ++ r50_12 ++ r50_13 ++ r50_14 ++ r50_15 ++ r50_16 ++ r50_17 ++ r50_18 ++ r50_19 ++ r50_20 ++ r50_21 ++ r50_22
def rows50:=rowsFrom chunks50

theorem good50 : ∀ r ∈ rows50,good 50 r=true:=rowsFrom_good chunks50

theorem sorted50 : rows50.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks50 0 (by decide +kernel)).1

theorem mass50 (i : Fin 57) :
    bandCount 50 (i.val:ℤ) 56 14≤(rows50.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks50).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 50 (j:ℤ) 56 14≤mass j chunks50))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total50 : (rows50.map (price 50)).sum = 297869 :=
  (total_eq chunks50).trans (by decide +kernel)



private def r51_0 : List (Chunk 51) := [
  w 51 56 0 970005 970258 100 13208 [],
  w 51 56 100 970259 970579 100 11747 [],
  w 51 56 200 970580 970903 65 6313 [],
  w 51 55 0 980004 980257 100 12218 ["8mm#3@z|:1L{PfTa>|et~Q`ZpIiK7@>MyUR-eCXgj(?u,6z_wMJm@f$|z4esD(p_","FpficUnPCbiY%Tqez2'0'wu?n_#lM94&ta>P+nqaq:Bdt1fjl)n}EI%sv!aA~>j9","(B`zw,K||`]3-B4%}Km]wMd#J_63t$DiWes'!"]]

private def r51_1 : List (Chunk 51) := [
  w 51 55 100 980258 980581 100 10682 [".IuxHt?{4WoZqcqrUJ($v|X#P{/)XbR/P1r2@F9fkop]vN4U9$;`;K](i>lm+;fx","R'm64xR6y5D!%hjia6$J|/MT$W]lb$`XTvCKj2<S0#o0fhY9%+#Kv_8n&->rgX%s","#Nx)'z?L4|]{~rbP?w|~2`2VX;wsx7)|u=%%2ztIy"],
  w 51 55 200 980582 980902 60 5169 ["yCnoaxb@L]sF+'(MML%hNA1hq6VhK+~i`Cq7YCZ_|{9ADtC;7$;]O:,u)KoH2>:|","0z7=[H%_#u6'>C7pB,?M$WytM9KqbN5jw{2wj"],
  w 51 54 0 990003 990257 100 11243 ["M,nY@Z6D<=Fa]Y=icvx)@@3&|%e8s67l5{G_^jh[x~>o!s&'6qY]0#8f?3Tj8ox_","#3%QjJ[SGL='7ew;4W3_jJA-<S7pmj^L9B*EKNEs$4n.]~,ML>H|aGk)@o0R74&e",".cv@c4>m^3fI}jP])Tij~|Dc-_Vd(Qrwp){T7Q0C7wl<HpYb"],
  w 51 54 100 990258 990583 100 9566 ["`lAo'fzk!<FzKbq~*[Uyi5^Hjv.3cnatiI'TET70Iyzg`4Vp.`{L[BjZ`1<+K{Vl","=QSbg3Rxn:30n]lp$<F{-nL~q;BZ.#m&e^BBy^8Tw1imbcepRziP,.b:4{-JHO;P","$|g_)e2iaw7rlM)$dR_^F(X~Mm0>Ia'jsLD((czYM&$BcU+^~a:x"]]

private def r51_2 : List (Chunk 51) := [
  w 51 54 200 990584 990902 55 4209 ["55'GsQ!A&^E1<8(qC-n1Y)A0'#7dhd`CxsLGQp$<G#&X>~-e.T&=QHefTKcnZf0#","^AY<&HzD~WtuY&-Nw=X7*e*;vBh)j*q0HK%9ZvA}Jh#_MdY<"],
  w 51 53 0 1000002 1000257 100 10304 ["9XK<0gVv.Q`&M*Tb2:?sf!sw--SZDRrf_0,0V85nxWISs#7MpQZv&KIkaNOy{g|o","=Odtg%yFIymsmQWuFKdzDgM4)[FNs)3LH+6],u,(9T78~1lGAAmQ{TDi/(73/EaY","/k4O}keI}_*q67HlM(hga#n]qoK9NYWiHycvBk,lHGt,V90rjs]p]c.Fw<;,*Qc("],
  w 51 53 100 1000258 1000586 100 8485 ["xLX}mWxCfyGxSj`lMjWRY2]T8_M}+9E_tBb|-C/1i>0qoI&L;`1dy#!Spw$]}R6+","1m.+IN6.F_guKb}}bg`GdKE0NWskxz#Wi!>BgGBV4wR<903t+7sG(_PreIe/68e:","L,74m(Z)Us#+n%@Nl?OZWgKxf:$WzdiIl@#Og2oTBC/jAxc%wkqz+B/K@kvA!iqZ","3dk|,r"],
  w 51 53 200 1000587 1000901 49 3438 [".bZ(2y0(2)A/6`?[G9_0I=KzrHX93}_(MtkfD6/T|W|[Isa(,TA|-OYPA<.(;6j9","%gul7|tN{T9(t,5~fiv3p5=v?9%cJ8EHH<8NSP&<dXd3efk>RzT@h|3EQ&"]]

private def r51_3 : List (Chunk 51) := [
  w 51 52 0 1010001 1010258 100 9362 ["os?TXkUe5{ct/bg~'{X:ePJ.kr*@ngLde,^TIZ@DD3M1>Qt|1Bv!nh_vN+kDmL.:","s1|,&GlS8{h9?%e$[feoa?XoriYL[!%pyW2pH4SG~Bi92'0^612ryjw*6EMsq`i:","&=&{`%vA95PqxMUk*-V2ze>[/3SP*z]mf8nu^he(ao}nh^TK*n(^j:Q9RcuW:^d)","/c#Na.ukPwena}Gu"],
  w 51 52 100 1010259 1010640 100 7572 ["[X)d')2Bffc%n_SP^Ajv>m/3c+(zlScQuwf6W#-5?TpWxqdylOe52_|QfEwAk>M'","0B7#c:}ch'0b@6R,%mJA3_6`p7>5XUdi^LGTt4neYFt<~|&39&sSLv@unkd*ox,}","-%u.+TR5B5XKRPd1LULHvB2g!'PQejHcdxZh4v=mWe@N2MwA{V1|>4)*7&#Ys*mX","O$WDKh0Eb-`:e9onUZ{[nitYc5P|"],
  w 51 52 200 1010641 1010901 43 2845 ["9OB^D,@n^a>{1Y$8&'B+KG;$SJB#T7mKq!^`I2XI_yM:.?z{h@C*=6eEIlE2iQ=7","%/1OCt6A9wIgQZqH~`r<Nqyc91,]hm,|~X1U{)3(a'v!z0nBSS!wl9e0'>"],
  w 51 51 0 1020000 1020259 100 8551 ["prxntzW1e.'qZnV&v6,qI6a&|}Q(>4[?9!3{C&[8))HT#wHlE6$.1Uf7K8*@b9{Z","/uYbF@$dI`8eVxs`thfvb6LG`0Bzt&tT<gU2?PYI,8c^SChu;cIY]%^`Ub0VvIe|","pqfs<XfmEvEi>~;D6j#z0eF?kr[y^fFWf)Ej!>E(@VZ0Z3GG}Z.Jz5:gJWXbRc/6","&^-p`Qh5FEVi#T?wBr5Y2ty703jqj6Q"]]

private def r51_4 : List (Chunk 51) := [
  w 51 51 100 1020260 1020644 100 6902 payload15,
  w 51 51 200 1020645 1020900 36 2288 payload24,
  w 51 50 0 1030000 1030261 100 7771 ["cORc|3M7z-Y?0^cy0goEC,-nOD/~_uvWlaMGF6HU~qbR=ftT>OeOq>AB{&7pDr|G","Gr#ovZ`;84ztFT$qFYVnFWzPw!9zUfe2m;,LO-vc%a^(,PNp8Qd|/@!&z(2#[Ec+","p?.Y*E^ZZPDH28,!2]n?SokqBU;oow8<|LPS`)bIK+ICNFU)Dk'K{F8i/K)q2b5O","&7>H,{.{eBexakT6TT)C;V|vxK[?rmB&u*2X$;iqADo%gSS"],
  w 51 50 100 1030262 1030649 100 6434 payload16]

private def r51_5 : List (Chunk 51) := [
  w 51 50 200 1030650 1030900 29 1781 payload13,
  w 51 49 0 1040000 1040263 100 7115 ["^6MOpiJxLWRHn/xplBuMWXPx*(!S,#<WP;23F{1JzD{^b^FGMgBW^Mb<X8;uI#ul","#4Z^dCBFw1Tm*;yp{oxN7Vt)Ps!|6u`cc:GMi:`Uoy4%[t!^pA`V`h5u_l}Q&=&7","db(G1id>q|U?gB)(HqiL<M!sXlPW3xtNDy@`2UNy/f}w&LmikLsFO*7!c3z6NN08","Ne]6j1XXjfszB?kO1D2v}o$zfgJ*U3=)wswz:r@HfzQvO$n:-`9L}wC{N_;@"],
  w 51 49 100 1040264 1040708 100 6121 payload8,
  w 51 49 200 1040709 1040899 21 1244 payload20]

private def r51_6 : List (Chunk 51) := [
  w 51 48 0 1050000 1050265 100 6622 ["~XvCv%pj_?20F[Wo*a#Kmu<h0f)1kh>=`P`!x&6p*Qy[MYZq&X$SGiSgdS4-xhNT","zu-DivDPv4I3~LT_-iMHe>cVYaa!sbeg'{+04vPNZ|b&;gBM5:EkM>VY<=z3?(&'","lCYC?RP-5V<99'LVB@qLKF55S-H$q&qEPc^lmGnQxsMF?47/A,<R'89,i>p#A>pw","K,=SUF,LW=(3>yEmk'_p:k+#bN]kl6qlMnAq$0BnAMYh}Qc-hTf#ei2/V(M17=+j","uyKA0K,+~Tf?l"],
  w 51 48 100 1050266 1050769 100 5853 payload18,
  w 51 48 200 1050770 1050899 14 808 payload11,
  w 51 47 0 1060000 1060267 100 6229 ["MSNAg=6K3ns`o<^J*lD6MIoA|<MJ9c['-b'Dm3S*@c[9d{/,GkQDf)MMj$|C;-E1","41vkdtLjablPe1UN.?`;o->~K1hu*|}^6!f@&17/n!Pv_9NC1x:X%:7K5<mpQfRW","ib._YI%?T'%/.V8`c3<#mJh-&81<o^1,bZh#1BVIzr)reP-SqVWYSPmc2G5qTzDD","ke=AUmIKP+#|#&zw>?q|nXmMf$Na76Zt^8DG|TY)1=aB41cn}BZ=j9{;E!>'B[-x","s$'<Q{Ssb+.ioO+l8@a}^a|wo_Qe:r*Q8&_"]]

private def r51_7 : List (Chunk 51) := [
  w 51 47 100 1060268 1060833 100 5611 payload26,
  w 51 47 200 1060834 1060898 6 342 ["''*<pfK*jt/{_+Rwy>&v"],
  w 51 46 0 1070000 1070269 100 5873 ["$yeA5I!>hvr_P;+u]pGU:d/2Q~Rl$X_7U^?/UIlQ3lvZ4sv?J4nAM[r4=j?drP:v","GV&6jnQB/NWfyv=7r}k=QXB_RYj;>G<#BPAI'X.Vn]3elJFFSV4K[8m5W4Ir=r`&","B)oB8spwK_XF12JF5(3=>5f8#BKT*tu#x]OM=:if&xu'S<#PVn}bpM{[5w_hs(XN","4@mVXOPCy=23*z>opxo,*,$C5(~PQ^i$Z^CP?aSL|BhaPuYFx*0kzlZt@d(cyoig","840aye.+^-j;ww|YO1Bltr5LtohGUMv9^d1aRidPWSqX>Yb|^Rwdbh-f"],
  w 51 46 100 1070270 1070898 99 5354 payload27]

private def r51_8 : List (Chunk 51) := [
  w 51 45 0 1080000 1080271 100 5550 ["8>+Qh'pvu{7){c>'I~A~w-(BNA]!!E[JUHV%bX0D+_eCVce=ZF{2{(0|W2jH>C*E","E[%p;orcYZ',pz$NL,7i2!z##!W][68$sPGdGts;py23h8=]DG0M-d$h@o(&Jt_E",",kuL('ZiPeO#N],-fI{S_cn+'lsfWCJVk7sg/2w1`GHrI96{@[6yxpwm-]uTV+tI","sT|W/![c7u!W:uV:Lr_Bc.%Kr|tHeaufCT8[52h_mC(jhZ2Eza:jl2CM4c$D'wK+","9Fq;>p-1u}eCrKnmG]bn:gC?yQ09Ei7hhaJ!`&z#:0|WsQvHQw90Q*EhJw[vt:f2",".*I#<;*%}N><:-).*bL"],
  w 51 45 100 1080272 1080897 91 4744 payload9,
  w 51 44 0 1090000 1090320 100 5267 ["'eBom?b0I+~j2mSgLS*[8wz'e%U,y<Z9C@D?U1(D]0Yx[o'[VYdXHOUQ`{H8&s5b","_|jB6auWAecARZbnt,|!Zx-aHEH(>AZw1F$)V9nOme@i}T1F&RY'zA4IWdae)DTU","!-QE+hf%q@7|.~!|S7Zs7q%ZSu,Z;-g2.<g|'o?3V{=uqNrI~!.$U`JvIj%MUtVc","MA+8x_hxJE_4'}c?AmPL~*8VK2|>WM(*q}sWiU$`QK%~S/9!W2%yCKS#NYQt.%Pk","HxojS0So7Vma&wVkWx:n)jrD0LUlla|tcBvopC(k:g6!{9Qg[5oB=C>r>W[1yfhC","$.2X^Lz#]t{Xj4Fe?9e[nk4Y~+5ChZRGx?H(#d;rR}c6ZPir"],
  w 51 44 100 1090321 1090897 84 4221 payload7]

private def r51_9 : List (Chunk 51) := [
  w 51 43 0 1100000 1100323 100 5015 ["8^iYf-40RUHE49g%3<fKsi72grC:J+OTN>+DwJ_!=YJ-~jwd@N1iat#!i(Lg!gs5","~FO}_FfRY`fR>OGwriJ,WNxYH&V-w:XyH2J5&nK0AIYi}-9>nkUzgZ=Y}jwGlXhP","d_,m,<}h5}6-uy%YWZx1xsOiTT1L>m$AvuA5MZ(_va{~83L:F9EpfnApMUe&|Ij!","n4^_nE6<TmkoGIP_D&/V_amc6L,:Ax-Ywt,_|<A*[y8d&H$~K<]4*c4xsXN>Tt=7","+mf:|{xKUVSzPO|5_>&Fx!+dwT6nh{4Cm[WE$ej?}l=Z~H9,{qgBz(o.Jwt/}^]$","D~-~}#S%C%=ITL:H{02-z%e|]qE5c%!mTXUV+Ym4_Y26=BYHHYmDTiI/2$YtoOx@",">TP~}BgmRiP!#x"],
  w 51 43 100 1100324 1100896 76 3677 payload2,
  w 51 42 0 1110000 1110325 100 4781 ["r@5K=0p;&FueNnbyAZj}>2~?P1YM$SEX&L|!b]-Vv{z|ZL9u?H4a)B%h'n=?+K/9","ZM?hBh%s#8n5#$=pNA7oN:LqMRQv(TM'`^T;|U|JHVLxG@3pq:`p4h;c.P=k1Xpl",",@+217wmm}1shrcQa`'bj?~S6Bw9S)Un+HZ)ujc)sO55$7^M>&n!a}i@CkIxf|?B","5?HdZ(VGa+^`5RL2(|x7cKiU6},;Pcf2c^)fTDJOCTDi)S'}nzA=5_47+gxgbck/","<DFn.%U]J_.*4=`,$e=8c^4iX-dq'et!J~Q}3y6:-r10tu'8c}7U^CWX59?jQ~I(","CVFE?D+e#*Y(swJbl+qIq_%02XZ3Q,%SSw<?8pe2'wrYxFxq*${ZO{}h7'v:WI:m","+u{Q4)RbQRn)b5X&^`C2jZGoII(15c0&XVa"],
  w 51 42 100 1110326 1110896 69 3222 payload10]

private def r51_10 : List (Chunk 51) := [
  w 51 41 0 1120000 1120328 100 4556 ["/8i8`a5aUo7>vK{]*X`BcE[gQYN2ji#LY@!rZz-7VdbCSVN$Y|?&7)mCZ4dyY*3Y","<li]5k>jr&kf8cuFw^$&4z>{fI=at)z>n<=2T|,HM(vJSb'DvK]LO,uh^6GO8VJ-","YlD5W(7t_b5/xKJld[L-7lDk@p`v5/nS4,?AV*(2MYSc+A~Q[&iy328=AKC:^cO>","MC}p>te9SK>5I+{lPgjX28L9!ve?}xxdj_a%r5UNG9x!UV>e,G^H5,05kEw[rGS)","dI{eJt!nsjUyjaA~8PHO|roGLQ8kXK({)Xe@HjCuMXT$$bDjLUKaJe,#]YvN+l_2","KW6@u*C`PC/bc2e!r~`PYr]Y2A0$_R:J[lcX+&.b*MS<#Y}#r.vlq#;>Ns>%^0jL","._-zb'3fk]_7KFxeVSeTCf?2X`jQRfu,FQX7_1o8)DkcYBtUB}P{W@6?]/"],
  w 51 41 100 1120329 1120833 61 2754 payload6,
  w 51 40 0 1130000 1130330 100 4338 ["l&TT}Wo>0W4rJ[`XNU}.+mC6kp=oqQZF_QCfaJn[X,'b!t-l0C,gsXh_G{w,~mi-","bUkV|xuc(/ul)/%<qea'[/!9jqm)O*Xl/k_Ty69~xVKGfBmH/!-PGTIew4C)nfw2","#9@OI6M|4EqG`,0{)yV]C3sm}ryg;_[:4C-pr<wc'6]gcr;Dj4C;=fXXkbX6hba7","WVw]W9dyK4=k<c[6=nuKCv!^Wy.,c#b-a-mV:EA4i[8`aF=vIVfG]t#O]`w${J,^","L@sNMRM-pj0HI|8QoNFfEeoL#`iGzCD:^]E)tmnXfVPHda1yu@&NLUPjy''[bh>h","x37yYbM=!IMwR*+KYMT:3^;aX.bhdBfvdAV~V&^=8#U0my*92%jgr=:Rgt%B,LPS","r[95RCoWkE+U;1r}B*jDl#ep88{ym,]S,~tWSv%c=p/j4P+K.[.3=v+|E[Nfcv&p","aIEgAh`HPh"],
  w 51 40 100 1130331 1130832 54 2365 payload19]

private def r51_11 : List (Chunk 51) := [
  w 51 39 0 1140000 1140384 100 4138 ["67+eyHwej$>5PXkGgdSTG*W[mH&&d.=@G~ZD'Og#l4}}!'V}hkY&ygAZ7!s)*b;I","'Tkbuf(Gg,3r'|Xbg('WEaRMwZK^-=jjg5!jk[)2|<U`'-@zGu&H@8VjK<ew`g<5","YKG!'ppUbI3R9Z,H;X6mJNpWBa79VYI#T]qV!.9R(R.[#QAg#W[pgyWftA+v/|E'","}0FMlWr2-WZI5oX(]]U<sTz/Vagizz50'<+n;*'}%]./7,.s2lA!ro(^X2=Cz[Zz",")dW.-ZtHJ)|&afn,sJ2UVAo]4{F&bVQhiB<6aCZOk&@(,4m/3L(&-.1=!r^`6K#>","?P-sbnbTPD*B<IM+(U-{E'qw.(Q`9mHwtJJ%fG56By>8s?CnNfv='.p2rGZV--}[","mpu^0x7948$1J((K~]uVPfL>Ce_=@GeS;zO!3,,S8cT{9HSe-Ltu_gpdL^M>:oa&",")&3A!leF1l'l}XCM~AXk"],
  w 51 39 100 1140385 1140832 47 1999 payload28,
  w 51 38 0 1150000 1150387 100 3944 ["(n9)b#+0I!1AgDzEv#S's}P^0{l'Otw@9R~+#i3tY.BivWo,:zW4TpN8wt8[p<H-","%P_c2?c!yghlco6,7N{e'$eS:=,Jx'[B[=5CF'+E_qv,vFPKNE}:!4T{I*6d9$@^","JxOD'[#U!S=4|r5cPIRyTd1&GkHKJB]LKr/gsz9$+dTBnD~GAA,<;tDrO;]+_uwB","iT6Br(fA3$q@}N*M<4on0S`Fr2#>Z]AnPHBo#,mm/~I?A/Z[!caa?Uq;2m.6'L?v","NwW4E]=BW:rtBCC@?VFzQ#PY]:#pG#|,B.{HcGLvf^Kqimu~G_n{{^K5_$~!&iQ^","]^2{&Z^|r-7KREdOLHCUlBRKr(|o[@T*g-0m9@a/sqtV3ljcP~[*1Lf(<p/`4::W","]s0Q-5l~Z:r$0r6H)mD4'!o{tY^?Q1Dw`&HIj%!p|p#*mgU@#r3,}fjq<01QO)|]","Lr%8TS$EcSD8j(L]3f9BnU%}t^JXWZ&xF.C"],
  w 51 38 100 1150388 1150769 40 1655 payload17]

private def r51_12 : List (Chunk 51) := [
  w 51 37 0 1160000 1160390 100 3762 ["xs.Mz?r)yARdV^5Nt|:=U_Mu<8S>i65;L+TyAQ38BVX$H[ygSx^LGY1-U+dl=V1Q","$-*&Ml?#bYl2wA6>wkyXEnoVY@w0KWcg)]]*u&yDoR2WA;7j@+6/JQ5}UM`**2Va","P@~&%0I=d21x;aAd.M|<~[OFiFGDKBqlyjlzIk,[29[_RXgBSPb7-ynLWqo,c<^2","1yAkLE{X1BFN'%V6z$v[@23RW<o}Y1K8K9q'@8Ra0h/dUyrI$Kfv&-UDs.4u<ouN","+jbVt7I'`xS_[e_p+#/mU'RFn4{M!fSRZc#iK9#_lxX$=EF;3.@b.4E`yHE|WkDN","r_yks0=;DQ4FN_qU}CF:ct>1Fs;nJrTCo-)DrK:rOMx#1_@a?Cf6n_wWek?{+[{h","n^W%aM_{qQZ{D7qo=|0&!CVf:9O/:=;q(iu;-l0kHbIO'0~Rn,66GxsZ^|!n:yDq","$r&D/RQW8<u}*q*7:<0Avb=o}2o&M54lz9>K3SC8/C6uQpBW"],
  w 51 37 100 1160391 1160768 33 1334 payload22,
  w 51 36 0 1170000 1170393 100 3593 ["D[8gv0B1u#RN7Zb:!U$}?shvOjWrzlv*NCI`n|93^(/nwUK68A3X^G:Pil-mDxEI","k'de_KE[NVVByA3HP)E79:~+mdc7?DSe[Rej@[?fqQm6}_UUz~gH%dU|7Wa#U}$V","ko`Q0JZI2nz]umjLdNARZ<y7P+#E+BnTfSoe._w/EyM9[53I?9F~Sc@g0;MHb_zP","x'[=@`^xj;qG[:F>gBZ^69/+t`lkmRz&m`]hmo9PS$X-Ki*ioHDS`izy~m<;UpST","K@_U'~sNyOcmu#@[79`^R?52qPF3f9l}uzSY$J*?QHY@%D:-j#LX]zv=4;HrGhMn","4[dd[(hW0LAFD+QMI}&3w}Yu7BOHpfd`d++~-<1<JTCRrGd/f[m]3Dv-kos6ArO`",",QGl|/,YR#T+nHGg{mbk,*0OUc<M%FML[d5ZJ.R[s&AjVM058QQ*YJS]~gR7/50i","(nD4#rN#g~8g/sBuT#cj(f/#rK3E?E!<]M#@baCTw_'g*mdK:)j^Ea"],
  w 51 36 100 1170448 1170768 27 1068 payload1]

private def r51_13 : List (Chunk 51) := [
  w 51 35 0 1180000 1180451 100 3441 ["jkQ.P*['s4z%DV5Y=Jd/lbM*R%)nc16Gp+_:21KRwlIy%/&~D^2yM@-po6iRAj6N",",}/$&eTH2dMYls-_,|S+a!Mb!*L|MA?i/FCI`D}AOad5E]sN8;6ka[{YD!9XxFb[","{Cgt]</ypi48cITv6$x]]=TY+rio#7SJRY(^hcm1jKd%2zj4f3]8}ih1]Jp40WZz","Np@#L/0#!qescRiL?`S.g!z}<z'C>m<!rA>n5?):?t7*`wQ?Y|nFtfjwu=CX&xjz",":kXu}<Sv=}4F0q%gt*EZQZTGL-MekT'?TrTC;Z!*P-T_emDWf@dJR)KYn~^kCwgP","ADpZzvtVX6Jd#ubr-,yl[jMu|H_:f2'A)DZ4@@j'7Y7tTm,SIb)+*Y,bST:p81?7",",,q[5#|j=gMY#M6{2Mr]4H%Hej$T'_]^|(LjjJDc}L!_0@95q1u)XFL*a(ZKKK+.","@c|/,qHiKx}jjvE,:C]IKJmA+Rn?&AERrF2~nvo7Z2S:f/grH3bO+Bz"],
  w 51 35 100 1180452 1180705 20 773 payload3,
  w 51 34 0 1190000 1190454 100 3300 ["AX11qaDSYWmb.SS_@mVb>``a1&P]0~PhU,.S!<:?e1:r<w2&FKefGPRIhuh|+A+B","x&D2t6?+qL<8}1m2g'~3j%&YgV)7/va/_|QDEZFn<{0|aVdh%r!PS/^;9Su4<knh","Oh1u;!9bpjn+wv%4$S>BqK@VwjTQIHh8f_yzsN>IhlTE$-r@4N,ow*`w+?{KQr9<","Q;:'@cf;,LV!@A@~XN'lAE[mW;a5G1UkYnGnrg(9ZTr$G9'=Y)%@;`jY[0t[Z7>j","y2Q>@5VP'bW`;X9/Q6UD|G>>nhkSFVG|9bew:{x)n39ey3!rhP`f}#{U3m>D5M$2","G*B`~*]sre(p9;sal3DBq{-czquCEs?;6;5rE;A|A6J<Y!-q~P4_&zH8*=x9Z;fD","?XXy?Z_PZEM1!BK3^ppoX|vUEX-vim'2Y=WQf-SK{dE4uwNu.UD7)V'Z>We#F^(?",")I2'`d.mj#8S;__2MU;I-G,-JS:Y:;.vwH[xD5&khl(|0=E<[c=2w"],
  w 51 34 100 1190512 1190704 14 531 payload14]

private def r51_14 : List (Chunk 51) := [
  w 51 33 0 1200000 1200515 100 3176 ["ZvX~8R]1Sc%W~1c2#f)bIB%]gRQqDVZnsrC)6T<k0[WMECk{X]W'>@%q9N.@*kN_","[XTJAAtD)KFLZZ`_sPi6VBl~=Yp8NG}-tSm%AI,CC-6f,m+i4<,idFO^IHHghypP","%w*>(*vq,uWr}1kw@mNcKLB+yR8N+B*~4h`5IIbk^XVlRhV#sYme!LnBEe3M-`WB",">!^~goLmoO;[ZW7lc[%OA'i9KD_,D1:w]SP_Lq-oj]t</J1Fu3<pAr(a?sXZ_`2z","DeZ.L)2>Pc)!xx(T=q-#C4v#{2{Lqb+.=fqIMT.}lU3/0uT_bA0Mse*Z6>@OxL{T","eXTRe/R*L&WUzs[,WLzZEO?kEOG=ZJhbE2n'O$fW$.WNNACBMHO6/?+E!Mrc`Ow2","!Coj/AII!p`rX8^LYw,'a7['Pk3J%P^IUH'|Js/zPYwAOKE!_9;SohN&t/gXq7{4","-dQg_E9E_t!D.Mu{A$WtDV4SN=i1l3;]_(>Z=CR!V<u!lgq#_*"],
  w 51 33 100 1200516 1200704 8 299 payload4,
  w 51 32 0 1210000 1210578 100 3066 [":K.lQlVaBa<+,T}Q8RR74FalnGLa;~$=c{UCh_/CCrQ<vRQ</h&8zy!{qs~2@x7b","F<0:[0Pl?^E+7oV_~#GNoD&&Km`Yg|%n.0!EDJoxkB<|'l=gNPXTTA5B*[:<3;.T","&3%%[ZsO==!HS;UfglgzRAF#,NPx9TSu';Jme1(yre=>44Q>V}=[eafJ-W3QO!pp","N7b.|JJ+_Nm|)eP>.!s27tNz_q3be}Se6$$P{q'5FIa*qJ]<O3ew'$?p-mIgc'Fb","^)(T+X.R6%+s:npB&[#YM?6$A8f,1B&L3O(ZnVh=3VK|^R{ot;=Y9tZ!$8y<p:b?","RjIU8=1.W|>4(qbjn'!aV(Iq<d^#PUwtF*__JH8AIR9g1zj{44$)L~:KNc1h_M:p","1Es+FTy^t1n,^,}_4>O`Rf@L2.o`gAa'&'9hhNCsH#)lKqr?z/e{?Hg$<^n~*i9h","Bvmu2c%x);AAi7WhAG9Q`GxH>]RNUlO33C~}!UN&4@fd'XGNzn"],
  w 51 32 100 1210640 1210641 2 74 ["#i2GG<Je"]]

private def r51_15 : List (Chunk 51) := [
  w 51 31 0 1220000 1220640 96 2831 ["XRTEEhAE7p}|u32[<t5`9}ce(u8R[s2C:jqWm'>V6m;4~'ViK-Mn%*zp1cJEn-<v","]W{2syMc.bpkHZyJ-r'}<6PpP6}#uo^k^{]G^OBi|-?LHD1(y32},V|Df(6n|b[2","Nj(~2{y,H$.<]9},[)'dD/!_I-)w]'(.j>O3'x;jnUpIC']hP;7S{lxrNxT:u7~{","o7%l,:Hb-*)8l<<XX:u5-OjqutC;)l3WfoVJ$qd#l_.~4,wn5Hh4g(AI+TC[LKq>","+{7BhZK2H#jO*T.}EmM((A-~q,6C(0Gg]KT6n]K0#kD!i1k=e+N`%VfKE]+id;K/",":FJyQ:+&#~+Irz}S31Etk4bDbQGOhWj[n*B(BYKxwXV,gesf=,G<UI;)+%'mZfAQ","S^~2z!8E1y-E#5`ySK7PnTNsXM}zTQ&k;.^_ncr)k[_R#QR$L3.&WVM?Bei[&^g(","'l|vamdxy2_'[CTW-T~Su0cHul]uw,"],
  w 51 30 0 1230000 1230640 91 2573 ["1`@}%G|fO2^UJ<}#SUr0'$KYuE_O)}/YK;P3zs_T#U?S~p^pClXAqjubQV20hZlA","N,GQNxYdXVIdQ2k%7k_5T5@8pR[`R8*UvM~M@&o'ZTlw7'u@k:cz`pw?.rm{%1mH","=(,awN_w)F(z1.fgPFdevM]qXXX=V6dV_Fm(SSy7)c>)^lD{-fB#j8nY[GHo<NET","6@%oWG8Z|.W:gSZ]<(KU$(7unV`o#y*sj'p`4x78=C'a{.0Xpnw@F)ur8ZY8rMQf","W^c*wNG($d'3N<fdY<O_!{gn'KKY.w;A~SfjYAAvU5R!#75OH+mj>Si5q]A<bo.r","%^V[Z?;gjMvsce[-vbkIHT~v_MO-<%$iMq{+Y*%W(h&F,aITF5JnoK>,p`zwg$@)","vmed`*n#unb%8I@%}_b(Zi`+72`KppRW;q0mP@[dBO$r2f#jP'bx_eGzuOEinte?","-v`$"],
  w 51 29 0 1240000 1240577 85 2302 ["(9}3#mUl*N}axF/3tf1@TR'4~!$8Ya+m(/X}}]{+1fow08>X'U17+v<:)w'S1STv","h&u)l4=Q{gg'HS:G!Yj+m-wA9{(pD9L>qe*uiG^/b-Y}y/CR2jC^Cba1-}dJc,&a","_3k.o_9/!,LA&WEeANZGto,=u>&8_19pGZU|$TM36YhwU-<RAA(Q:b}D,{0#hO1%","gF',S$eS+y*M$mX9/UFytVhTJzvF,^x04daUIzM,D(2(A`y,#`f?/TiB]'EA`f*6","G))-hZ}T3$m+Y#w;#%qjf{OLu/Pkl%Zx,tCoU[nzRp6LWHoAz}I#_Rjx%`T(:};B","KeW^Qh*@YCOo)x~>sUyT'A&b:QQTtn&{,rJ@{@$JiOtn%2VUH^[$#yQD,dk<%o7a","_h8?=@fo}6hp`f^Y(V5a:)_vqnx81jevU6C)s<eyO4.v"],
  w 51 28 0 1250000 1250576 80 2075 ["T)HLv>2x{ffO/TpS.`0IyMO6L>Qec'^4YO8/,IW]in~x_Gx<5`H_H`s::H01JQdq","JVr0]6Kzt?y1J!Imz-InWceBawRjmq*PBwZ|i;rx43,LL4hhw::(o&HPKoCo{;|u","E8(rpS<My#c=v)TXC^3[w]Y==([j9U:wurPQK[)$XT:ZUU3~/@2CK`LeRAsPs1pV","j.0~U|WR~AY9mDyq%pa|C:5,WfS*kTexWgBdA`&&m#~5M:kU@T}(t:y;[(bS`)%z","R~vhnwbT>79#dw'.tNN0PIg,Q3y9YCzRu,Q+5w*&L#bU@'>otW[:#Evp[n6!Mb$B","XJn%|mGQ?grpQLILb1lA{PxDQI>I.Sdc`ZLhpQP:hS2C'r;Fz!!|6-gE#!pFH)#V","4qobC+L@&>viT}uG<$BQ?d"]]

private def r51_16 : List (Chunk 51) := [
  w 51 27 0 1260000 1260576 75 1865 ["$*t|9HV+navi)6Sb+}#DxV)8fPZfw~o|kX^cKo$.?qmYohB]#am`.YxnVhS*l;?j","%+}4M0_&`Cs9zn=Ojq9-ek45K,atnu<.d&uoODqZu<'[PfwB]LZZ!dgHw'=(@qb{","~Pq};_!RHO3:}j'/ZF(/1A41!<|,~6#iLg.4p?R=c)]1'*+,TP0ZCPqINk)p5@FU","l<WL<U'_NQX[>^H*yMmElI#.Ifd>oQD'>w8f{M9+7A'}j}Uw=c@.}JKB35zmMz_<","I&zpAxB7i7'bd/1)>17#Ni=,hsqI~=:FU0tVxLx!9OzI0R`>6N/P6m5(H8'd70CE",",)X)qpJ~akw;Mo}mb<!pP668}rXh-~OD`_lC.m8c(QpPyHBSG7dC<+;KE[DNy2R<"],
  w 51 26 0 1270000 1270513 70 1660 ["9jstp8cZATDCV|(CNRJ-B#htE~s4*z!zi@JP|w>.MDOl:UPZR06]:m$8>7]+q-[z","6B-r|H?X-P$x#)<qO0fzqrQj3l{?W%K^-V#&Dfqm#DzX*$,9?J+*FG^'Y2QwPD*!","BHF,nGRwlXAqh8U??@f^mI3aSP/.32L)R6KupX=C0DZ|3r;kN2:%WBEwjewpTOD1","!FI1%mCXiGK`YbS]j6tTBXO$3+dg51k3/kW,e|:'t|+W3kGRf!c;nN^5p}n~Agji","$U!BV/q?OPxcsn#cj||JuWeEt;%l[dn{vhg-y.M2r[k;@a>Wy-=dXzi}*_,M$]14","#BKC'nAd5YPF2w$q(z{V$00c*NcblRzE:8'PC^(B)Li_"],
  w 51 25 0 1280000 1280512 65 1470 ["pbF0oO%=U<T3hfd'){,)hA:0sjA{C~4_GWhI=mNa_dW,8*{-Lz>fgbDHs`iLn]f1","Mg,Y^~k+tp/d3mfbZ80/`E%#pYaTwf&f$o`pJJL}93s?8~=H'l<z1vg?j$Zy;(3)","R_ax#A|eJ;%y(J}Tv8HEWL$d(w*)6v*^sSdNR3G$Odk{VJ|L}h/G(rVn!i??6i%[","x]'WZe`0:OjOq9N'Rz2>(Jhfw&KF~ezKCg}61fxw[*6H:-i&OETJ:|JGyq^aEVP#","]te)5ErR:J1o'S+Fmp?9]jn8AOj7'zr{XtSIMPQM'cu!$^M5mPW*f*]/8mu2W`98","<s{RXa!0%#Jkbl0|C9-O7j"],
  w 51 24 0 1290000 1290512 61 1313 ["B5nlo~.j=8=OtFe8#vP/oz1=k@Yf4oC{FOfGh0/yg}~2c!J{Ua[]Tgt/!O<xvZTn","E{P*=0aq'g6k0_}Oc?fUDDo7=W1},qCx.Kc'$~+GvWYyRU~&nJW?;W7og5Ua66tJ","Yn'+|CiNEN;=mj]-oe4PFC)SneEDQLYc&(B>?R';*gg0MW3'BsCQ(2-ud,v$4dLn","jPzB19fW<m[3Zr*R8G|yBEcK(OixYo2ws>1ZmDjNa4.$]qp<ous}&,EaPk~CHl(r","s^PuPOt]dj-YM*SYFh#i?8~2S2J/0S):r-;Kc~k11e`HGrOVmrxBXbVL(?KC5X_)","[D]g/i"]]

private def r51_17 : List (Chunk 51) := [
  w 51 23 0 1300000 1300449 56 1142 ["]s42aYi#!EFr2R<>Lg.;OZW!C*f+`qzvMc[9dKW#7>[@k#}qu]A<z8O3gD$mZ;wf","xx1*g$--_J+uE``3YWBspo?q^<<Im9_}]pB=wd4o(Tf]B/<|&D'cHIYhh1L?%HvT","Uv!-jwpLs'q{|}nk'|3pBl*n'fI'fVL)@s-_^6I3ewfZ(=jko$*;e(S&~!ZtC^^{","zKW]~w,e$([)H+6ZOiTFMc*KAQ[k5.QIJB&6NbJ5)uBpZm^3tB(:b;l,_0&+*(@P","$Q.:JSh:n`.G!vKOo@R7+M}%IKw>QE%IPf;VQ`sUO_7Q7]pcU"],
  w 51 22 0 1310000 1310448 52 1002 [".}xPREW7+UOH7APYc94h#6G](kj]K*m|!F2^]g$RoTE&oJzp75a1CX(M0mml8A_%","bB/6gFvV`RH~%~*'U*~3:UaX_~;8J&j}Q2=^LXgLR5hXQUd>g}#g>nR{0Qd>y!#,","b$kZ,@bOu*Yd[8i=8CMY=4twzxt2(4%ge,IR1G#:j#2!O,:%AB$6U0-WhZ?P8p-i","OkD'b)JE3VKW~;V)F3?&;VoZ@?d6.Dl`UqBpp!~L2Td!JA3U$a|*p]:z[@Kldu#^","O;P{TonC}9wa;:})WZXtml}W}`1?SkCbZ"],
  w 51 21 0 1320000 1320448 48 874 ["N~56?zq6Le'mn6VM3HC82K$D+Nhs>p]{0`}%8{J2{Z#T!;Tx~9TnQ=+-MCT<#mE1","s;+fjo@qmJRBt2IlszoD5m:G8P,m$8p9!TIv8(DF5R2:^I*#g=@1oy}tt!9I^<[8",">s)yO.v8|;W&-@G$I$L._HK2'T28WgpN?EAdgPL]g:>OJrr1r3nDzIVL/tfb>hpQ","NS]o:*miyh_<79n`=t_C=Rz:n09_S0]o5V<=$4B;rV@^I+^--irBs*qb.l{55]f(","JKv%5j4sx[}j"],
  w 51 20 0 1330000 1330385 44 750 ["XK6ia7~ZSM]cc3T&jnbt(A2@M$1n3hY{Ag0m{KM8U~$Yd6yo!ctz(KA[H~tBVN>U","NVK1Nmx;n_>B6!2+zoaR{8S)<38Y8oJ>Z91pA.GOftM(eh'-&!<iPy.K6`599n@+","V!;,C$UG}zd{|__QSUGsF1U}MJI!`2Z7Y/`}5piOaZX=61%k|d%?{n?bF`N#zhK<","*LFk=7Cg)0$.]&%}Y&?d!ZJhlMlalFjriud(GtIme0OPrN|$`1|(yFgF:.-:"]]

private def r51_18 : List (Chunk 51) := [
  w 51 19 0 1340000 1340384 40 638 ["J6l~,([{,A8P?H5.pd.TP@~7W0uBr,jfxIqZapsiJPbt*`J6xLJLT4,x0^g6g[9Q","Pl=<[QV%nBcK%{%>Dn@Q?/-+6ANhWk'U1qA5&cL5!j3kHTZ?HK|.D$njB`80(+[h","4(FYk6IHLkE#TZjVixe#&|_QL/VN_Ff>kwAy$ZI@8.w4(/2G39ND#~J}lVVqMum:",",rM/Nj&|2x)D97DK'g4seCmr4Vq:I4,pS/68"],
  w 51 18 0 1350000 1350384 37 550 ["3_5Wb@U,Vc^}D{*E5[_Yg89Vo]Ffzas6a?Qvb1/w$WN}H<@@Q[GzkG8}5.bZ!c!%","W/ZlNKrQbv-(iF9D5$IweyHr(]A.SWTu!^.hlE5et.12}O0SE9UiESTWIo^Yu0He","c*6Q),MkkA5AZ;g!|%AV1zNp7X}OC^3D;9mK%mWjp=ew@^eg+pZUQ'G~*QZH3}3A","H-r!(#P(1<rdw<P'R|;Zg"],
  w 51 17 0 1360000 1360321 33 453 [";KFoSNw(.o2l6]?kms|LS(|W~AU1(A53@a#C%+0}5&OXKOO[E:nsp*f9R)A.a%!v","x@(NC87jy7cuvshMz;p1f8qCVWB}MAG:vbs-(hAZ0iWZ|K0U(;2WqKhs6~}ZSt*?","9A/PnQ]Cpk[HCh6^iJ3[E^.<:0_QT<$6]/i!<gVKPD{`tL~aj{bC&#j*sQ*~n%"],
  w 51 16 0 1370000 1370320 30 378 ["H5$0yxtIEz3+5sZ9>$@&,pZ;g1gGQ56tC1%UmvRkq}YgEnuTsBx7O{>.`G#PUH.5","O67E|{@!GkEE^Yp+7a2cBJr~j{55gEQ2sqfa#VV9<v46uy,fU9WI0b^[)<kh5'O[","+/hArR$NnQk#Rx:@c~ySA!;1D59vbDGHp[,/:vzUA@5/>&l"]]

private def r51_19 : List (Chunk 51) := [
  w 51 15 0 1380000 1380320 27 312 [";$*En|KNY3]f7AK9ys9wEW4&w0c&GYFuz:xLIG[Ik]k;2|cW59.U=M7#O]<tY2_T","T2]-Uk6WT@`xx}}!S2r-=|^OH1y$>MU_]`mYAZosxE9}QZ=.!~r?{O'cmSsVI|ZU","W%g{8l``./M%LF/.D~cblFfwt|J"],
  w 51 14 0 1390000 1390257 24 249 ["1wv.Q{j/(`^Nsyf2FR@^#g#=AI/st~y)i7wip@FUZ(VpPL_pl)Mmqc0Mm-dN^9|{",";)(+~_n,N`bS7wP&CuqR)WJ$Sd*R7oB@}u@^XL@,!?N{W9R<w'&avH0F%fL=1VV%",";Z(lId0P8%MR9."],
  w 51 13 0 1400000 1400256 21 195 ["Xh|v8AH5[^~x]B=1,|~nM-3N4K)Ish_TawT8NgJ/Z$C|(?q]Zey4b,gLT72`/PWz","1GpZ7&3>a:6)f:@@fh<|{<rh:>r`qg$I5qTx&#1`r+#Nlp({PG49J:r<}n"],
  w 51 12 0 1410000 1410256 19 156 ["(lG82jn;KH>%IrYk+v^R'`Z$.yY;U-aI!Gwn}R7P!NQ!/Kbq3r])QqhYoVdqJ-ZU","%itT}>vav!k$k-N9964@R`yvY}7;wB}+C`sX=]!LOK5]p"]]

private def r51_20 : List (Chunk 51) := [
  w 51 11 0 1420000 1420193 16 113 ["tSSNjqMVam+k4EC>,z2}diLhS/S7Eb!IkT~LA[2+9je$#n_ibqMO>B|Xz15E,it)",")9kai(/b&od99~5N@w$ki}(QJ3sh"],
  w 51 10 0 1430000 1430192 14 83 ["h(uk%G2ViS*S*~RwLq$pJ!{3nWlS6=#R_3ezt</70!m*|fQj3:^B=5gyIb(a'ZH>","%dHOn=xi=;O?'(TJ}{"],
  w 51 9 0 1440000 1440192 12 59 ["#NXiIY6:gLgYB&k7|<bP:KJ4**6Ofejtx!jU:^3V9!}8_BgCChk2W%vtwAtik9MA"],
  w 51 8 0 1450000 1450129 10 37 ["+<_w]t]Z/.U[kEd0DKtc__%,V,<7s>[P8~SHE@S<'sp(6@2$$f|T_"]]

private def r51_21 : List (Chunk 51) := [
  w 51 7 0 1460000 1460128 8 21 ["'6A?qvGLpa&-FIM2Xaw2lB&mDdTI$eJG~`cv`Hxw%Ec"],
  w 51 6 0 1470000 1470128 7 11 ["%IPJA{7SMO=5CSuC[}D18m;pV3CuY9l~oDd/aN"],
  w 51 5 0 1480000 1480065 5 2 ["$FMQ-A*=,L>3f@*>IAZo'W}S]S^c"],
  w 51 4 0 1490000 1490064 4 0 ["&sL<E*^Q7_-#%wt?z>tk>nAS"]]

private def r51_22 : List (Chunk 51) := [
  w 51 3 0 1500000 1500064 3 0 ["J!<k^jADfN?jau<-"],
  w 51 2 0 1510000 1510001 2 0 ["#)XWdBdP5n+O*"],
  w 51 1 0 1520000 1520000 1 0 ["+I`=b"],
  w 51 0 0 1530000 1530000 1 0 ["1{)MA"]]
private def chunks51:List (Chunk 51):=r51_0 ++ r51_1 ++ r51_2 ++ r51_3 ++ r51_4 ++ r51_5 ++ r51_6 ++ r51_7 ++ r51_8 ++ r51_9 ++ r51_10 ++ r51_11 ++ r51_12 ++ r51_13 ++ r51_14 ++ r51_15 ++ r51_16 ++ r51_17 ++ r51_18 ++ r51_19 ++ r51_20 ++ r51_21 ++ r51_22
def rows51:=rowsFrom chunks51

theorem good51 : ∀ r ∈ rows51,good 51 r=true:=rowsFrom_good chunks51

theorem sorted51 : rows51.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks51 0 (by decide +kernel)).1

theorem mass51 (i : Fin 57) :
    bandCount 51 (i.val:ℤ) 56 14≤(rows51.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks51).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 51 (j:ℤ) 56 14≤mass j chunks51))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total51 : (rows51.map (price 51)).sum = 321017 :=
  (total_eq chunks51).trans (by decide +kernel)



private def r52_0 : List (Chunk 52) := [
  w 52 56 0 1000004 1000215 100 8951 [],
  w 52 56 100 1000256 1000576 100 8482 [],
  w 52 56 200 1000577 1000903 68 5309 [],
  w 52 55 0 1010003 1010215 100 8614 ["|'1?2,^FT&WAobOg5Z~/%<d@y^5J^7hPtS,S2}0b*h9HmehofC17Va;ZSDZmrP}s","P2AVpbCJ:6MG}_vAhNE]ushah#Pn|B(e<6NVl@g%'x{]57[WP&7mBDRi,[ViLC=0","2wLIe12jQTFc}l8mPwMX,=II;[]pkjIEF]a*4V"]]

private def r52_1 : List (Chunk 52) := [
  w 52 55 100 1010256 1010579 100 8122 ["`vq/!~v=B1FDlr9-5G_o(+l3',+-bDi0uQC1fiB/=}I8O)j-})Dt]xb+'C9U%HYx","FV8fCO2rth]v+kFVC$hk_!+|+6Y&4@oT%Q]X=/wfM5Cw*1p6b'P$W6i8LkQ#EARS","#Nx)'z?KEvVkk|jt~qjn1.H_W0QuXG1EWm#r#FV1s"],
  w 52 55 200 1010580 1010902 62 4602 ["x]'8faOt`;>Zyg.0Eq=y=QzIIbb8vcRwAW%XW^y^#SovB&Q:_8![QpURnqHx{<`O","sQPv{N)=pi'*vd[|dQ0S5}sM]`{797x$:CG.CTvb"],
  w 52 54 0 1020002 1020214 100 8291 ["4.oMORSgSwx38CzcytX9rb9me^{Q0U;O<m83xVnw+L?Vjw~l)yKN55i(li(~ROw*","=DqxQo?ZG/%uqWy!!7lei1{q-tua=EuQyEFt`lAwmm8)?EEm#K@*=tN}{~P#j^yU",")14Wj/]:sFl.Nr-.nCU^o_|]CNx-1.'`z<d=0Hh{h~,`M~o0"],
  w 52 54 100 1020256 1020581 100 7754 ["~a-*eP%Z@g-u^Yi#uW]I4#W6cLOx&J.tuDjUOFWcmic&MeboG3?r~ND@6_uQP)>[","Os#h1Ww<UwyNO6)BJnx|@Q_pR-nSj.[q+N;U'&9-mJ>PB;{v8)>07~AY_2ckM}bG","$|g_)e2iaw7n`{_2.Ak1tpshzyU<f^HErD/u&?KViRM@T=EE-f=U"]]

private def r52_2 : List (Chunk 52) := [
  w 52 54 200 1020582 1020902 57 4037 ["Nc2SCP{-bp`#d*[$PrJN|Lg%mxOC('OJ=vp5^F)^x!c7.}OAYJ6>MmWIX{7rb@|?","%M^K+JDiLyWqn}H_G}||i1Qoh-f;8vj;sC)JqTrS6gh*'<OOQ2!n"],
  w 52 53 0 1030001 1030256 100 7964 ["LvmH7HT{}'8Y>Qh>n#-)YD#'a,i^fyE+Z%28|3l$/ERV!3r8gLcx:4.U_t!guk[.","s$IMe2LKeSk>@&gp!Tb'[ZXwec7k0iw!!iMq4G3mi+-DbE;!e4$uIV~d53kEnFf7","/k3KM2TQ~SiXh6f[,[W_!/{,!w~ie(WV&ILa'WxIznC+-GC2?||=,gLh5WNNT06h"],
  w 52 53 100 1030257 1030585 100 7372 ["?)cNe:bf%xD9K?|1v:&dN`Z2Vd|i:-p/'rjb$!k>:h?E>6VGaxxF:3)4M8D[a)/?","BH$d178Kpo;H!~(.=z@wb,[cCi.+T+wUH?$5$#+$)#?,*LF`-&U)u'~[Yn<OzxnC","+Vh}RL$G*<0Lr^Bm!4#Z3}]e<Tl&b#iV@%UK_|eXP4''*H~|9d@X~o$4Z|6PHt8-","(CRws"],
  w 52 53 200 1030586 1030901 50 3390 ["V<tl,`Jf*[J@.gTJ0>[77{[X4=((^F1@$`X(Y7_H~+:dj5<$QDzfI=Oovu%:G5e,","$R67soL9@Q;VL:}<QA0N)|x|J,nt5mtv+#9G*&_[hnOcPp4SUe.Q{SZ_X~Q+;"]]

private def r52_3 : List (Chunk 52) := [
  w 52 52 0 1040000 1040257 100 7646 [".s0%y3gf3`%A:[Ub%J,h;0eVqRS#X<D}&Ah>7iAq3=6j7mr<quHBQA7(H]|l,M}!","]~]f@3F&KwlA@'HgUB|cR'gpM8295l>H8X4Y70or>qrP5HET|=bv8)1Vysl9zI#3","<A#p<gb4q!,nu)h=X=[cr_sJ.bpzj/J*nxY<ZO-:7+2E59hnrC6,'z?(Rr*Ii.a4","&wn;u_SZ~?W=V;)"],
  w 52 52 100 1040258 1040588 100 6998 payload25,
  w 52 52 200 1040640 1040901 44 2870 payload29,
  w 52 51 0 1050000 1050259 100 7308 ["jnNh@v*C>@s9zi,kR~Fra>YwQ;*=6F97ff>GtV7@'hX.+!{K'(0$8.dX]}0xK$<|","h&~Ote8<q.nGRycR4vD[&XoLFU`fU$6n5TOP'8Q0=Kl|QLI/T2-(mt>6XO3TdEo:",">bwC#Sm=8Hj_<d&&m,A;.]M}aK~rhzXGWmHXSzlKBLZ;xh(9Pd[TMLpC@Aoh{zy=","#`Oyq1eUS#</_x^[[mL}:hc&ew#EOe"]]

private def r52_4 : List (Chunk 52) := [
  w 52 51 100 1050260 1050644 100 6646 payload15,
  w 52 51 200 1050645 1050900 36 2252 payload24,
  w 52 50 0 1060000 1060261 100 6972 ["t_1Q{nYq(@%]Q9[']T<a_s.~bRNr}m&nOjF<A(4Y?J;9O0MA;7=%cDvy,59TK5cC",";h-eCIsN+rlL,ZP4HOI2A2QP|:<w`)Bk9pGOdlc&'V*'ymg<T?r5Cn&mo;4.&7ON","u~lFcui7'|ZN8KkqB@4J3qC`;q^rUp|Krw&P*J@vJZ?=n#)M])$i?V$t$L|On*Fs","4(C@pl5S%}MAc&CLm(FR=X[))D<DPo-)g#@Nw$+i(/]"],
  w 52 50 100 1060262 1060649 100 6314 payload16]

private def r52_5 : List (Chunk 52) := [
  w 52 50 200 1060650 1060900 29 1752 payload13,
  w 52 49 0 1070000 1070263 100 6636 ["%Q7Y;sP[7]Qb&n`(W1=(Hd-JX5s+-Mc[@5'-LVNL{-j$f%v~3'Iq3,_dLB)k]7R$","n)=1K2;u([nD&P`]r>=5JjwlI7j,rhWn=3.BicF*:feipvSHWxNHwXD+0*md=40h","LH^X)$v}ZGwf8JS1VfMd=pFpi7@A0Xh*=OWg/+~A4kLZ#4,V0l&`likg].6@(pwV","$(|[TzEpiO|gG]EYcf9!fR0`{fY6eDSh-^]PTa+Xsk7aOM'aFA;S4;A$e"],
  w 52 49 100 1070264 1070708 100 6021 payload8,
  w 52 49 200 1070709 1070899 21 1223 payload20]

private def r52_6 : List (Chunk 52) := [
  w 52 48 0 1080000 1080265 100 6307 ["@fb|X:Y1R-MMb'HR|SP|$bTN|=@lyMtFr's6/h2l'rhlP!O^/zq2=CJxG6b'aFtX","JRpdE`SMJ(Ken[_?r(qbSd-d!BSY!5fSpR{Mdbe2ruIw,5nqDn^omF5Y5v$?wk^6","5!~0t^!E9PQMG@!XQvZsa4A3^']GL{ozZf(%H?Vn0T6_Q4uZQuv73|T;5h7cQrvV","=];P<R7GTT-o+]|D'Q9P!d-!V|.d{&Rhxg_d>oDB3lRjGO0Epc%OJz*G?<oUq@q,","#E;9idR~O"],
  w 52 48 100 1080266 1080769 100 5753 payload18,
  w 52 48 200 1080770 1080899 14 794 payload11,
  w 52 47 0 1090000 1090267 100 5989 ["4qS:@T^QEB+>~t,Xbf,+.*)XkD}za[pquGzs3q+hu^+R|ab&lg.szBn/}?dUS_.e","h'C+szPRx1:FY)G`tY-AB~&cgC#)LbUN;*f6Hn>0xkNZ(hSK>b(S3e|hv3;2Otym","#Y60V<)g/V@RzGkTR``)G#AYK%9pWdlg'2a/}t~lHHRXDV-21Q{'&UH[?fIb^F:S","Y,(rpqmBns{o,g*3-#]rNQU-S1lX`H-$#~`3rmr8G24d(tJ-jm7.k-cz|a`}JAZ(","N.!:CZFR6Jfx4FC#pBrtT6*30&rK$"]]

private def r52_7 : List (Chunk 52) := [
  w 52 47 100 1090268 1090833 100 5511 payload26,
  w 52 47 200 1090834 1090898 6 336 ["''*<pfK*jt/{_+Rwy>&v"],
  w 52 46 0 1100000 1100269 100 5684 ["n-o!_D.,N7bU4:{vn{zAg`uG7#5N)u8)D,7m3eeJPj_:2uy:)R5d#9)9n)N1O*VD","!!6q;OoG%h24fSRrf1P*;I;8v)sEomSaz(%lEAX9kDFT,0FZs{5J#0E+'F`wdUU<","Y_E}3q+IejEWmVZ&[7>41Y0uX5c<CyVst?hS6T7F^n-c^(q7)xN>}dZri0BOX=64","/ITprU!5f]f*DkIdUw0c8+oZD2|xOaa3&^?D0D-538'tO1(2L)Tk&uHd{Sg24'^u",".84d:_9PXK<1#2*tWyCN&~h^bAwX-Jl76j?'9Tv_ZQ:3=s.vjs"],
  w 52 46 100 1100270 1100898 99 5255 payload27]

private def r52_8 : List (Chunk 52) := [
  w 52 45 0 1110000 1110271 100 5395 ["Tqi:{jp}VyUKD&WnNdlG~;[X'Luk@SQ7{a%+A|*/')~&qXS:}!FDtI?uh'AGWLb0","]hp@PjG~te,0FoC*XXoUGqv;s}B^[@(RO;)S*AMu.3z=[SBE-tFX(^P&JE0ta(4(","Cu&/;PETx:aLIaZdb=R?(%!/)ilsB-`bKQHvI%?!X(8HP$Mlmd2uMY]CQs`aPcGO","O>8mB)Z%BIvDUgZ1y!QZ2qMK,kTUSE6N8zuCN8'Vh:f/%ctFs|~N:kZm'S/t/E7u","$G$t8kDyNsl?9KM@]XQ?u09}}]?G/U[!eRfQ6Q-k0u7'#u~+&0Hz7P2+yrz{aR~]","(`Mk*ayaj[LKT"],
  w 52 45 100 1110272 1110897 91 4653 payload9,
  w 52 44 0 1120000 1120320 100 5130 ["y1s'.8zw$J~L8{M9}Z.K-O)dd%-F/4s:k`%Wbu'i)Yqii!b|wZ@q7>Uj7}80`S-q","IEpFXyz}zWILNA-)#wOO(rm4cSM07;<^>8iM=a<;l[u/DS0N?JGX7Kd<.!?%I7g%","0;h,BvTdzOl5Yswj7gj?q*0nDHg~gZ,N[f[A$Sc2^L'[^hXpCUsW+fxp@17Am8G3","=%`{sb6Hw^M~v%AvP~;Bs$T?`y[mS-2.!#<{d@L|${M<Ex<9i?D_-,ZISA%y|gW+","]?r(~Y{)*^#zdjba$/af-XO^R%F=sr{1gFp'>!,9ih'jOtc0>=h}YM_=%fl</ZoT","#23Dm@KVKOjNQ+^@ItEk,'}W/7#`TTvq?Ura:IaVcI"],
  w 52 44 100 1120321 1120897 84 4137 payload7]

private def r52_9 : List (Chunk 52) := [
  w 52 43 0 1130000 1130323 100 4888 ["+)Y{!Lr%0CLxX4$(uWL,MZA8%c^=7g(@Yg[7Jp3zn'>C:ie#7!<8%|nc3~Nl!x_T","I%cH#lyjEkUNONsb/I4CeGdaVUK&O2;owP*/y`tr-Wftw._XHEN.*yD)aA4p]CPU","HrKBs)dcc'9=b1N-'6U0]S.T#h9Kzd'S_MUtK((aEUL#25`e3-d@2&P-bnD8^e2A","x~3!wM)~<]biF~}>zj(1~TGd#(t=88gtx}<@`_h`rPen,8qh<P)PtU>!4%&d:0mE","bQif`0Ylt?mnVm14Bqm8'Jz#&j)p;&6sW4&t9j,vqeIht&FHm({n0Ru88aUG9%WC","kH`a|U$_1b]E,Iwh_r`=9^0p>?-H(`WFSjPl$Z@O2SLU|$MvV0mo[QJ:1~mYkZ,<","MmOZm|Je6"],
  w 52 43 100 1130324 1130896 76 3601 payload2,
  w 52 42 0 1140000 1140325 100 4656 ["LEz&uY@mfj:QVo3~e?SKP}|mH5p:6L2O2^M+YF[Dn=u$v(t%|/f~G!8KX?2.Qqe]","tBSLT1^UyIG>ExA&fzPeg`D}|fle-ku-hZ~Qp&yg%sQlX.B?w9sQy;;#%)FCGs:<","P}IDrYUOj{-Rk=rzaA=*F=JMV!a+'ng;!E?C&R$[hk.SwuthYQ$o5?b*Vzd,d{|9","=?:9ksKVOFh($(2'O0&4TI%v|BxHcRzuf@jv;7;k=}u:dTqW.lvr#=|K(zC]ZI>)","l'EYv~J2H3]3**zTr9XL296{|F6Up#b<?0|*e@Yb&YGO3Cx]DL~s>I5f])<+IE7^","Y~e3UeI9w8g}NYD4(#R&|[Sros?u.rN#PsN-ZfH)/-JFunbl$il+Jlt*i-z:=7-m","L;p:OI7PL(;glUXJrS//U1K/*v?5yv*"],
  w 52 42 100 1140326 1140896 69 3153 payload10]

private def r52_10 : List (Chunk 52) := [
  w 52 41 0 1150000 1150328 100 4433 ["4cGkr?IEaI&5@N6([k-?+h3BOq|8-P_sut.A)46v%>WPgbxMP7,5>VrY7u_T6BT<","eC%L*l$6|_~]f^Yl_XGtM2MJZn]<ZRCTx((Y@n<E~pFec#PS.n#Qy'^c[0O{VCov","'Kp2S8.V-rBmE)&LPQ3BqOd[jqvVp?JR*-z0q^_n=)doXMz2qPuF4WdI/NC&*0j~","ap?1FzU)Ju)p4:5:@?JgB!d=RN^4HrEL.%aph[On'I+58b=M}$DI!29yI8FM_J4Y","JP;0u0U|vx8X7'_bpJQK(CNe91*`pMOt@k6D/DWQ*-`#2y}D[Gg#Y(T1ql|_u^$$","$+IL'8@rrD%gvmCK]#W)oLeDfu&{iw'Tv9}J18TJoIZSnPa9QdL_vX<!pSQ]1XAh","(|~-L-c,Ix9kPm8|m*]'?s)AhsHV29Bly3-K4/<ji0$*$v^-|}NB"],
  w 52 41 100 1150329 1150833 61 2693 payload6,
  w 52 40 0 1160000 1160330 100 4217 [")r%kD+d%DS$3~XrB]tJ$pG2(eMMim&X=>c`#Afn@ZpKk17^7Mwn%w@Q?L-JIQ#K(","LOHJU,M+I|~;p3D87[JKV)dU;'PG)+ph:Jd)$u7lHho7jfc{O9S2)C7'bp$^g#ti",":j1xX)H0q]3<`.<>A%_@xt_P%fNIwq2LsvhB61o>8,IJ!mk63#6}$wPkh(T`ulLT","G%xLlDl4szE(7yZ<F`#om4fq=!t%69[iV@wE+;|AGWnR:h:^1>r$L(hG-b4g:*+I","+(g<ngILfN48JMSWT)ERq&ze7P/vV$g1WiuHF!.=rQqlS:XuS+E5Tgd+ztal@3+:","LB{oQ%~r$3Ki|/c}C$&.;y1G91pK5m{:@fgi:2JbQw}MdlD5O8$`QwH:*#iLff-;","'s(:ckg^/]nh(_{u#mKp#y`ahl)-M1UUHk;-S8D9ol}IOovzsYhYyzbjJ3@znYCb","&K"],
  w 52 40 100 1160331 1160832 54 2311 payload19]

private def r52_11 : List (Chunk 52) := [
  w 52 39 0 1170000 1170384 100 4018 ["O&2r~e.KL9/f>RFhKUkt]~FW>S6ZvLa'Y/,,jKasSK[zBu7*8@+/AsKExD~YT5(]","lEV~*5K8-m`i9zYdG&:g]HK:PyaT{~SXCfM;%:x_kx$3ynH*|'U*VNx<:[&)'>l5","_W4*.$G{V1C7ZeW*uGUrwus7~-{L!R]fLg_^G;gsg.W>~7)w#EL]~bi4M0maZuKb","@6<Dsq^}s+k#{FVTL1>!J[*LHs%IEX3!^-qe@HQ`uNFDk9h6oHT4lPU_:td|lsBT","wi@QQc^0K}<W@Dm}qmp,j:Ha!hI!zJaAz46op6T@]%|n:t6|Ce27miOObn0s*B}n","5]x<g5v]8CipObVUbsithP/>FlV2>.p+C_FnW$Pl&rk;wI_d5HT(Vlwc]Q-TaM4F",",-gN;@Y:Jr5a;%.#m8vfdy]g?bXaT^P].jSD{w56,.ryQGWA<Jc30+/UPAk@CTXc","$/.)6k]e"],
  w 52 39 100 1170385 1170832 47 1952 payload28,
  w 52 38 0 1180000 1180387 100 3827 ["|qRdIYuV@'Fcnzn7g:&_|JsAVcHzq,7!fzJUoS;z=JDhQ7+]m*{ZX$hEQDPCv_yL","*Sbfw1ql!U[C?GG#:~#k`^$GgR!C#S60`W6jC@n]:otlJ2JlTIJp;[!`YYo%%Vr_","dqmFA}DO7INV~m.HKSpV}{YZEJwvRT5EOZ+DwLLhL7#=[ROcJjV*Tno}Zg~/~V`_","yojl8H:dt9f.I,G)V8z^afwPB+6mmh3s0v;aL,2!x'S@_!'S'2[LP,Glp0,pXw83","L1jU:bn(/(a0J13`83EUnL}nt#E8s.Q@YXTH^^?=>@-Gm&MvTTj+!p>x%V1,;HLF","jG`6dn_r^-}d5f;&x-;dX(zkH=PQ{7nbmVbr/SDMU01g|[)0Q*<2|X{cuB8#a@Yq","5H;Vep]V(olBFSn2[5rLR'}gWg`<N/:J=z!wG:pr#q|L3/}mYFzb9NfwU.*X,:Eq","@br?!P%zo>T|N"],
  w 52 38 100 1180388 1180769 40 1615 payload17]

private def r52_12 : List (Chunk 52) := [
  w 52 37 0 1190000 1190390 100 3648 [",L-eCI'ny~`Xo)KT%$NMA-+{E9y;$B?D[VjS1Ki@o(*0EAhiZ-?(gG/>g.p>(fbZ","J5j9_t-%sq=b;c;M^:B1It,>C_jqc!C05p$%]tl)Y<v^6u<2J1DT!;;9|`|xy-,&","yf$@VfyF~EFdS:>>F?L)q/P:6M4~[{xi!7P5OHmJ?/kytz)>)KVKJ1]F58L&8wjk","bzsMb(X(f4hA_tD}z}|OiXB1J&dBs-lWQ`UA-geoH{q2i&.yGdb=dF>Q`KknbB.]","S4Rc+x?FA@_[(-8B@UVVzott%q4v{v62OIRKyW#sDmDoH*j:O!.>+j&ze$L8U#mz","r1pzspOA?.5oL%zv[2{1KPo+U.}23x}>@1T/h/Q;e&1E?BZ}sY-HQ3Y:XM5AspQH","/^Bv-lR^wd=2v8/#>ZZ3D08A1]`u(Shoy:PsQ?{7}{qLnEu#+`LZr+b[^9{){eR2","%/)r[iQAY&;.M<`9=4zkA"],
  w 52 37 100 1190391 1190768 33 1301 payload22,
  w 52 36 0 1200000 1200393 100 3482 ["VBbl_>Gy&DzCdfbRTC]`D5jX@bnf`n9w<)(,E9**wDMv^Q@d/vn7l+~}'^.SK)h1","!Q#jeI']EVeX'G26`B8TLa0M3XLl+s5:v]v}KuZ~}UMGvC])+p29aQ=(so:s:sNz","x[X|sd@eIvLq3A{$nyO]pqq{qpD]J`lA/YK%-DeUa1bX++;&zdki~p11:WML:X0U","3X7SBaddMWGRz<5VWdxv3RQ#dP[[;qDbZxj1y.#+4+{>nev'7o`&{yN/m}7P<ua;","mx}*zz5;/9gb:0x$+Ud2H,W%Z{I|rG}9wH[$IC,ExN8]mhdsE:#O]mr%9Kp9Di('","u+dUy}?>k~<'5hoL7Y!(ch<[_j6)G_|i+K!!0hYrD_w8'<,Z/Y1Ce^CR$KF=&D6!","!-Iqda1Rz2eq34%r_m0/cS=U9'a[8.ybkig<v'J`N:*B3pXZ,zISXE-[yf6/p{ak",")OMN6A9]nc)JUHC1M<l6.p(Uo]k"],
  w 52 36 100 1200448 1200768 27 1041 payload1]

private def r52_13 : List (Chunk 52) := [
  w 52 35 0 1210000 1210451 100 3332 ["P^*8Ze%F!#YH}<LCc+svELEW:N,@+&AV(gV8|S5FNJB;$!76-~VeNi]MLnkM6W(6","<xKK,Qlf$N@J!y8(!EY,f_-ecF%0(2vcJ04N)B<+#DC[Ls6{%~TH(=}ORxB9/R?H","llCa%EZ/FEraU`h-:t3{U?1X{k?[x.Aw$qMzM1};UA)8X*UUAIf:iHC%)eC&l}#W","~]:P<#ny'7@>U|z0PP0zP?WgpEIXUQtub(f%Dlsa1-]x[GGR[Pc#4/)bPJ'izFz=","MiueK:3n2PY7ls+Xq]*=)K8&NO=tt0.a5u6G739El<2sy2}'MxBAVcUV,Qw?t@2U","z7!?lcB*6srV(,#[nv.jG3Ue-y_uCZpN9Z7*yLgqh79p=`H<E$3t]e)T|TywS>kX","ZM:%pDQk$2LpymF_|!9va3VBwuXS*6yZo~`AP#I+?IBa3Bq$i@gy;qO~mH[%]w+N","'rxZR)aGHq=(^(kW_jgvJD]!}[eAi"],
  w 52 35 100 1210452 1210705 20 753 payload3,
  w 52 34 0 1220000 1220454 100 3192 ["5E.aE4m~$SblR?N<6$V[O`3qhYp}}*C60kQ2i)(Vs}71^>k)y0wQd`+b4J65&!Nn","-<^;Rs<L(%5UArMa-V8~j{*Z<6%[j<oBUW=8k&`O|z2+)J8'<>f6+:>J[Xkfn<~M","tZ{x!`F$W~j^!O]`(`[sktk0)_%n6Zu@2COEn4'RYCZS`ocfjZ>_4^8@X5ZKi_HI","DvCy5hbz_R~1_YY'6[E):VIhZ6_l3fH(Rb2pHqd#)-ABRi=ugZHD!=C>vl6`kZ32","_rOdY$&9>2xcTM-i$dG.q-iZwI[$qg-dX)26p/,DGt6$FiqU3Tu83A5}=k:^!IXD","jrIXXOaK.v2Pp=%KV|L=:B1'0Fv:x'A5-A/MRoeAcWLi5v47g(j-^RsGjqwK5U:Z",".=^OHC]|,/Rp8y~SK'f:qi)!}$NA:.ankqpEOW)k_m_Y#~BG-!adi^DDlEd_fQRB","1lAT,<=nP#%dnGQ!P_H@c>K/CHXm"],
  w 52 34 100 1220512 1220704 14 517 payload14]

private def r52_14 : List (Chunk 52) := [
  w 52 33 0 1230000 1230515 100 3072 ["U%q=F+Q_c:uu{V@GL>2^`5'4teQknV4U8LM)5e-BKd=X7W|&]Y87G#{<5HcW6UEz","ht8(o'xDui_a6YEr>+&qlS?ABA`mWi-MkX_%j_p0d&{]$0cEJ>*cVValU77g.fq;","Q`tK!<*[4.GloUGy(p77NUG>cCNCg}k1.rY51~?ovXXpmkL;>m*Zjl:oaEm~&FMo","9B)71z>-7/~2i$qrD`4SL>~[cy|.R:8G)|%N]z:Y#vO1a+4<o9pU(}`:0>IQJx$w",",j!A&w(%2C.%da^,U)xQ1vGQ+)-gm{u&h8bXfj8%Iwa[@Mxq!Dc-^TrB{_m/{+=l","h)BCmk{CWXYT],hI^#T;DG@o%b@<@(pRMO,kYrKjYc,nQ(+Aa,`4cMV3{$u-Ob;v","<hnL0uBN~XX'._=)tYm51dlwo50o8MfBI0$$|N7dCsPWuZ_1_;i6M({CRb<v1Bf<","3@Yj=Zd7a;;~O.W<xhrLQ/dn+K"],
  w 52 33 100 1230516 1230704 8 291 payload4,
  w 52 32 0 1240000 1240578 100 2963 ["G+j8!z$b[.bRCE8b(Eh.~()FJO`Bd,ZH#(JrH)hhoS&bn~l@CwN1?zC6?GBG'-Uz","!?}22~%NNU>0n6&,1S]6Dyj'ht.,LYVQm!*t]cZ^~B(_%2O!RfOr{FnJ`)1:>b)g","Gj_8%<f`%1JvN?{^^y,2}rVYVS;mwnW=P<aBq]X.l^%HZdjdzOvYr!l#l-xHksKM","SrV''x,4iJQcrh[+l2FUIFr[{@Y!=O$Fy4@jBEWAv:83$m%_GJY4|U~*hbh7rw6E","YO;o|3Wv?`iN47A[XwS~rZ8([IbDI?w8Z}pcEmK93d65_nOx0{Mbtn>.cbZ((v}:","%`K/5^]g`Y[LPq^kjzxDw*LNW<C6%xPbG@^A3bgH0?DUqp6v[&MswO[dfR2CG}{=","u6aCNNq7}Zz.BU7<fe2J[>*g&ReQ5r<lhU6J;31o0yC't]GE;RA%QGn`PV3Zf-QX","3P=3[eCpPP){E}o?l21x{'W~r"],
  w 52 32 100 1240640 1240641 2 72 ["#i2GG<Je"]]

private def r52_15 : List (Chunk 52) := [
  w 52 31 0 1250000 1250640 96 2733 [";]]AI1F;p=.^Xuk-EGG_:<VX^KBq4tjS.fox0}{wcZvPTB3P_xl})ahTdw2M7H/r","1q):Lk=kKfmwCnWL[yzY|i&PO1'qR+?a?%W|}0nQ/H097`qPxZdlM}]6`%S*=F69",">b0Fc])o,saKW?R}:sh]O`5&coA:GhQ,G3(oaGyc|$6;Vf}?{;2AmPK):b=T>_VU","Lz'c5hhY?QjI:~rVS-d1%S`b0q>`4z:tajE0jddZo!xsWUQbUkn?'d7Q3Bt[L6b1","_p&)fOm'@h[5(!R_:<iP2Oj#%]>8:]qx9mPsAg=|%%6zGg+Uk7{`[1e3?##z'JD+","H^0,pB.73F&UC)[d}+fyF.,I(W}FI-+osd0qLNM3DD%.w7wMvt*m|$MDgZ@@ft!:","}0@--(3aT}kaX8}{;5(qWp19*?W,UJ^n(H.tAAwc6^9{kCaPb$jk%,e-M@L'&{{$","3gxC"],
  w 52 30 0 1260000 1260640 91 2482 ["M)/2byQH|>DV^oJf8^7d|ebrerFnyv7Cr)e<4xFXC+&S-/DH]C}0gQE?2r3L19^Y","a&%VnDw,`@:6c!N0+nG]0B4c>zhOdsxz!&kp($WJh^R(d99OWz&+X,bOl/UZq)fg","JM~Di,UXpD,*Z=a$C2mmdpO1Y!^6'v(%~f+z(Kzi<[Ms8@Pnkpjg='NvnEhF*+97","nf0Jqw&i}K=a-iPKO~Y#!5o*Q[p8ZCwueT4(B'gM>I^e?[oQ28GkYJK!'{R9msCj","<HfTLitl!(*@lx,sw00C&sB?_,u`gL=>#;eu+LfHd'W<A[^i]#7Y6u&9{veX~%vJ","|{#]|=JCGFcRs%QS'<<Y4cXx)j_9nx;wC{)=Ag!Vq/_I/rQ&+$X>9:Dw!Qs=*$-6","9fJsEO^*Xy+/3FnjRK=:!AlkXxp-.S=*%ihz^*@>,0s2=@n"],
  w 52 29 0 1270000 1270577 85 2217 ["k,'IRUMz:j.g3Hoi#p~gEeZer<!_cf3F%&cw0KZv:&0C:ux)`n7}bE?;Z&%5AA~Y","(,Rmjz!?^Q5:I^%PZK-/9kZO2,D/GQ$TntZHW)c8:4Ze/7tAenz%4qY|hSsNp<1=","mAz9z*!>pD[<i(dh+#2Qu%f||5nY>V_>-s!]ym2;(FMX/0ZbwC[pN*Z8Qvo(HkCA","O[8<U(~*S@g.zGc<_'a1u9NJ,qBkfeR;`yQ_pc6zcwQLl6(W(n7zeJHsYv-_sAM$","pDfr;>nj?_#cere8b5!0?Z-,)[,,P*'{xpkh(Ot(5:yw5z7rVe$5dV'z3=C:Q<5^","k=H4rSM_{,3L:WgSe$O65F7]CO|m[c)N$X+T@m`YlV~Qerz1+HRrwV,r+NKRp;l$","':;+)XH3Pn<'Tp2c,!xzWqub"],
  w 52 28 0 1280000 1280576 80 1995 ["&5'ni(7dfd32NV2f',CVt}]1kF1D)%#g:fF2&^R'M~cCX}.Cw<ycbaZ,!uW%g<wm","<oD/aXY-]ol9dM{*a0fGFZL*{mQ8c7~pU#&Ok-x_cZ|,4frGJiB^2IWFaXIq8yiD","I2Ipb=Y>^Ee!orASV9vDB@ZO&Xia49m_/*Ge0hZV8A&j]GONw1gsB`EF7d^Sg,h!","_U%+Tc00ukT]o['${3Zo0I'8cL2g#E,#Y1Oor,kBg$ghG)6;1[AGw^;8}=j#,D{8","NV3vW8R}6w.GH{d}A#^65|^nhhQgynBMqbt.nBC/=#Bi2>]_;&SBB87,5d*GpO8~","k1ndAc>gMTDIp1t@f?L%U4#cDd>^[J*@nId8!dqu@$FA[O[*FApn*KX;cNvT0X{^","kg1"]]

private def r52_16 : List (Chunk 52) := [
  w 52 27 0 1290000 1290576 75 1790 ["BXq(2FyBH5Smt+Y9eo.Z&/^+0F2leQ[ZWT>2d|!zBiJMOLVK~Y'3KOmG}yezZ[Ar","`m:Zcf!wz`xA{=Y2*vf<A.,FP$RLz{/6__)5JnpCG)4e>er{@~Gga%3zsm)[JlkC","@:fb22iE%x[Y1X:~Cz~P#9M2-,kWkc@tqq~Zh0$THCSc{R`ta#t66p!gkf?Ew@GI",";4b}iL%v`bssBkp[Q6,h/(9eUZ=fn=>LGuqq7!hmN/7:[;//<R,64O.S$c]]X)9I","Uz2cHF/P@}/-qS/}`jx8'2'Q6QC#E-8o}@qQP~]I6'x=*{%tELRiX90^SKttksSg","&cuu>Rn<|)~ksSW,sxz~{dq~qr*iu$DEBJg<QNo2/Y)9o.}"],
  w 52 26 0 1300000 1300513 70 1590 ["e|5,<w{8EUnwoVe^JA}EY)/s==Yj/50eCi+2OME?(]|pV$%:&Au+?MP%'W=g]WZ5","3'AxgHMXi2O12_e@]CE6g&gY&Tf!C;CKqM%4w9lc[)5#R+,Py'D{J4~Sb-0t1kYU","QE{vc-VL5VVw/B&*NE4mfnFIDK/'c&y@?;MD+gqcq^-!d+584cQPmY.ljZ#z**;x","M0*o`V9kRD^0~Jul4AvE/]K[7e!@Ih^[s[v;igfUUi1+I4zIix]5NYj.0#dXrYM1","EX%#d,AtSgfvs|OvJ>2-{TcgV~om$4G-T%v'si:nt-Zz[0%dGZ+|qM{Y-){:;8s!","$R?KqH'z9Od^8W:JMCK)KbE=r$C"],
  w 52 25 0 1310000 1310512 65 1405 ["nD#sDtayUQK{d*@W?h3$?sEFKI-!p0k(HM<~fr-x.GcyP{BhBU3!W~pzTz$tcp|Y","0UiPw@U%-]%)g8NW9Zr{@;V3*yVdRZ8H5x4J71~RDtd<4#GU6tW&Lt1CYg`oL4Z(","(PnGagYF/B76#}m@Pze%r{.p+TJ<.Y=o#cpl_i6qH/>[bg@[#F#I}tD]tQ<Nt<_b",",k1C,A8T<W<67mLUSykF|FvIrwD),gf%8[isbKga>X-6XeSFN3QT56sJ=1cG?i;?","[;A%z1D6t+:62V>SFCs0b&mOU0(,8CO}*W`)(@N_(szfQ%h87;j68uB'eSUSeB@M","#'.9!{Lb"],
  w 52 24 0 1320000 1320512 61 1252 ["8u)q</uIUdVP0;N~z'_K[lF2}A0}:;S#_k0<~0a-f/h#sMoa?}+:!:8os_QzK]ov","WD'D7rSj7E*sg0lvz<^V~~rDPvJQrZYcaoe)lAP-)qfKHjB~^?oi#]81fBb`#C[u","d.Kpz%B5F0X9&R!B{G_P(]{N!&BmRQ-!i:K5|=yR`AOn>=l[.9[9[ds2eoA7zZ|U","WZAIlm0QuTS0%2Yu:{m4n|]DSWR2X>py]x,p4v,~|H^kgeLU#4$!C9qgVD,oe,Cu","#1,('_O-f`b!N@v*dxU3^aq9-7p3<~vPXv5'.XBie4n?MseQh#=$%+"]]

private def r52_17 : List (Chunk 52) := [
  w 52 23 0 1330000 1330449 56 1086 ["w]V+B6BNkuD=4],@39:VjC'ea9,|,Q`k{i`KxgzW^5iq*k)bB6RL[HoHwtJnQx^b","HPfB|u!jqJcP3%#XsfaaroO5-:P0Ni1F[46k3`nC-D86]Iz8,=etO.I?j_/uB{N>","%q8VzrrYrOZ#F,]Yl)mMqZ0$joU1lR0~[,;ARD.CW'Vi[0jrbA-oWY.{cSv(0>b&",")08S<_$,a!Be,[q|/3q:$@62P6w^2pTFsrQWhmw[FR$w!5#JM!<AqX|O_n4bXEiW","(?$#fRiyR9^{^;dg[|jP.kRE%!a8@8ACz?O"],
  w 52 22 0 1340000 1340448 52 950 ["9kpL0$(~i:u)]IF<9<eTcz;|*Up!+<^u>x#temw2B8nH&Pt&OV@Xed*$t?;~$M25","%7R:gyTSmsge9GTyLMm48|pUs'tp~._o`3_PC(x+uwd>z#Z#&a_;Ianq.iVD7v!5","{>xD[V*DJu3dEsbZ4Rw>xEB/y,Ud*o%;=l~$n.)J06ED]C.KPGT@y<L^fGF!NF11","0CB(x6>P.2G1BH$GrM]L1K35We<cb%;A#jXrYFb/$3%u,z{wT@Q{qA7_t_F,T_?7","%a*FCtb*VHjoi'}g."],
  w 52 21 0 1350000 1350448 48 826 ["Y3<Q~zy>v;t2TZ+Ku*(>L=*aP5f4F86d%Q3$bk([4G<`'0+rpnX)mhW?w#|_2be~","g{moEfJm?CkGKwi?iD'=NqG4GP<9<@!udpcj6,W6DqzsQ`AU##_]%O2Yni:$IlOk","Os{(xlETaNA7K+nB7(nNn']WP?21!^eOc2br=9A8]#}$[S+8sVt^$/}YuAeJBHAX","&HkGeOv;:Q|Ttc7VjS__Ul#E_Q5C{+LqdEK^^Ksb<Q|+`=.v'6[RB.gsK_#Y+Q+"],
  w 52 20 0 1360000 1360385 44 706 ["`Z{}UY%vk6[^lZ._yj`h]8>4=3UMZ`%Ytm&Q_hM}0ow./W?VrV.pcM<'lE_w<z'j","5mB1XUh<|U(3p~Y[H^T,L&CHXN:bKNPZt4#gBze{#DKujXB5Qlz)VDO2t_9z<dx:","{^Mq6l!#?Q'Xxb}szh{HA``<;My'8hBwciuC_Fk6Ao^Yy:66hn(2l>n<$x&]T#5d","%z;C-O@!@t1vdUe^8yVT@<'Y-^Z4s?zBEwQ+>p+QpT*"]]

private def r52_18 : List (Chunk 52) := [
  w 52 19 0 1370000 1370384 40 598 ["1Fucw8P.^}x%HWpB{-5svH5&Z*F_{3RP_x78B'1]sEWYYa}~:]5@=6KRyctR>&K)","Sx$V6>gd#%g{~1ZT_o)6QVV!CF<A}5o8aJ#u=g/:j;}h5vWw%/I.n&D$^R|N6#x^","cpA>EEp=FCVyw{(fyMT!KQY_.[NsM]]Y-(8^ss/Svk!cl;D|^qR8y[!biqQXE'__","%={jr5Ld?$3:(4*9Bo,FBi<("],
  w 52 18 0 1380000 1380384 37 513 ["^_q6/QPMm|3bvV'(Q}U4<|Lsr3rfJM[X1p8ISiKn'jz1;>}hD'-+0#%G)fi]Z:UQ","3>vp:rCaj%|h9Rc#.&oq.4HYd,%3`9pRIfKlUy*m!,Pr)yvcGE+w9y1Nl*z+^s~'","MHD!7:E.Er[t^6BG(FAq~T@'Bg`;@L-e!y6oLsOj.qcwoN,&&y,mL$4qDkDwO{$+","SQH#c"],
  w 52 17 0 1390000 1390321 33 420 ["^~)`9d5bYDgmL^xg<Dk$Q[r)Z8)S(xDNa3yH~UJ{A+K]NQ;Nw=[bV}R9p/U`,ed)","K%hzk1r*SY}+H|0OPTrpBJWZ48?M%Wbmno@=F7kse8(C{5MDR;y{K|W9%dx_4:)q","5h'*Sl,,azSa~pfX?&ncE,o=r$yj#l-kSdF!G`D:[-[DV-X(a'?"],
  w 52 16 0 1400000 1400320 30 348 ["DY+ttm!UQD^gCP,QR0x!,<JQKidDFJp4Iu5pN,:n+W,[_/}yRS}094F%W9Tz,tin","WV?>_inV3ZJF4NF665jg1S?FbeHVpjpJtc1Yw6V-x$[Ky=>,b07g.dg]x_UHjS(^","~~}t9OU^+nXPq^x4g^hY7'B8]qIoc?B$6"]]

private def r52_19 : List (Chunk 52) := [
  w 52 15 0 1410000 1410320 27 285 ["{XnLF-k8D4K=][WxtrK2#Y:-mhf;c.4,.`?DC5]{%IsI(zoOyMcaQ,wun>PuFp0M","N^74[L#k;.XR]Hx*$klNCOz=y54pHE1Q:Cv:|:Id=4=N3#AT|+Kpm7yW2CJ$_W;]","%jTo5K=p|4*Vt_C,GA)"],
  w 52 14 0 1420000 1420257 24 225 ["/1x{J3n|I?1;L)j+q#).iUCR->nBc0S_^Ge/sPTNWzLn{0`hZyT9~K>/_K6pI~I1","T*r3O-TnLg6>F#dOAS-C(u0<BC!cYg)1w9ZiinxVYpC)D?#Xppgl~Pl{UeD{G:G#",")k"],
  w 52 13 0 1430000 1430256 21 174 ["pPV:4$;c1QEYvb&b;5rUe/>sert_!;g}T}=`*!RtT)KG;Dh[q]sDKK)TRAVB,s<M","%&~nYw>vMvh1H[0|G3O42!znsxx2{kcA39(r*@+fmW0Nr2[-:(("],
  w 52 12 0 1440000 1440256 19 137 ["_ielh:6i2.GqE0ZH`{JAqt[>XAl1TMJN_Ie-N~2^v5GT~>*fBknnA)-wgJVLD<KH","ggq-@t2O>(bAzDnr^ER>fvz5{h;WGA~`_^'6@"]]

private def r52_20 : List (Chunk 52) := [
  w 52 11 0 1450000 1450193 16 97 ["ryckPJhbIhvvnFHFsj9LlH,s}wTc-Tzse*x'Q6jbk>bgVHZ>NL&_;(MaZ^I@(uZg","@~Nis1OJVg-Wld'C/Zpn1FkO"],
  w 52 10 0 1460000 1460192 14 69 ["5RS(k5a=LFvyzjPK?96w/1/EI91$]@)8}gu&~+H<gzcH?1}^-~~vIFEAXH3H4GL=","f`/n*/v.#d"],
  w 52 9 0 1470000 1470192 12 47 ["3^!97gFg)wT@>QLp)LKLDxSu}flK=]1=SqDW9xJHdr503p7!&QC9w-s:M9%<^"],
  w 52 8 0 1480000 1480129 10 27 ["%OP^sK(SwRIVZ4O,R9zmH:4crx4'=zP3;~2fSZd5#P6*11vi%pKY"]]

private def r52_21 : List (Chunk 52) := [
  w 52 7 0 1490000 1490128 8 13 ["/p/7n*.aPE[7xiEVs6;Y=`nI&c_M994b|e+]x<yRp?lZ"],
  w 52 6 0 1500000 1500128 7 4 ["#l!&R<X>KM}k()u{y}{eoE>4ez:1hi=+b(M"],
  w 52 5 0 1510000 1510065 5 0 ["?H4u^lwsO-7'H:>?FCyge;bL_"],
  w 52 4 0 1520000 1520064 4 0 ["6mVVZW9kYc+^LW%X*W{6"]]

private def r52_22 : List (Chunk 52) := [
  w 52 3 0 1530000 1530064 3 0 ["KW=([lBt5Ecvf+3:"],
  w 52 2 0 1540000 1540001 2 0 [".rPD:V`/Ar"],
  w 52 1 0 1550000 1550000 1 0 ["<0VLU2"],
  w 52 0 0 1560000 1560000 1 0 ["'qZe"]]
private def chunks52:List (Chunk 52):=r52_0 ++ r52_1 ++ r52_2 ++ r52_3 ++ r52_4 ++ r52_5 ++ r52_6 ++ r52_7 ++ r52_8 ++ r52_9 ++ r52_10 ++ r52_11 ++ r52_12 ++ r52_13 ++ r52_14 ++ r52_15 ++ r52_16 ++ r52_17 ++ r52_18 ++ r52_19 ++ r52_20 ++ r52_21 ++ r52_22
def rows52:=rowsFrom chunks52

theorem good52 : ∀ r ∈ rows52,good 52 r=true:=rowsFrom_good chunks52

theorem sorted52 : rows52.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks52 0 (by decide +kernel)).1

theorem mass52 (i : Fin 57) :
    bandCount 52 (i.val:ℤ) 56 14≤(rows52.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks52).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 52 (j:ℤ) 56 14≤mass j chunks52))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total52 : (rows52.map (price 52)).sum = 287487 :=
  (total_eq chunks52).trans (by decide +kernel)



private def r53_0 : List (Chunk 53) := [
  w 53 56 0 1030003 1030213 100 13606 [],
  w 53 56 100 1030214 1030527 100 12025 [],
  w 53 56 200 1030528 1030903 70 7033 [],
  w 53 55 0 1040002 1040213 100 12595 ["u.F-G<$%ns*GeZIWT26iho_]7F.Evh=a{Um;*'4L7U}H_^*rj}4T?t{-2S_%3$**","!&OE*%_kt7LEEfueOG<&`;;b>rC+::T9rHF}%ePz}q16Er02n+f<#Z[:;tM2zs]u","3awFj.OeT|Xh]xh?{NH7}7$$32[W-Sr@&>%~;A"]]

private def r53_1 : List (Chunk 53) := [
  w 53 55 100 1040214 1040577 100 10924 ["d1GWr@n~OZqJJW8zD0h;RB)XJ]%1jAlh{S+h9'Y]Fe$sSqxiq}}IBOjC1-)Xy7SO","ZIkuQ,)>%@dxdk6#cXf>.O>~`cE0<Q>EP7-3_e,h>|KCUKw<7h$kClXmK~kCmpoy","#Nx)#T}l;jQXN+WQ!3+L+FMk,%x+0H=TCI6([Zudu"],
  w 53 55 200 1040578 1040902 64 5719 ["-?r}Q^%keS,W'ltT6y:L^2lR;9=a+6OSFM:vg9|D;8lK.QpW%Up>ty*vu,vuC}<#","&dbZ7]x0@<IKj}WyJ?Cfx#)^X7F]cLY.K,OU>HyDfg>X"],
  w 53 54 0 1050001 1050213 100 11530 ["N>_FgPn^tTa)qmq40>sZSx$mv)q.uN:UXv`kzZ]vaj95)8RUR+pZmC0g2Ax=#H,s","rbiMbd`_|3h*ytoLy7[b2h+D;p3x>8k1*q$ePOpt!Dgi?-SnqD1@9B2?<.%BGA[+",")OH&:.C6_Kh(p9.b2DeOuUhOf;bfs#yg{9{;$8}]rsubKQA="],
  w 53 54 100 1050214 1050580 100 9853 ["EP]@.5!nDIQt&Wo5Vz-uB%!PpyIH&zh:kq:m(T&$Z=!4egr$s2o|&P1PmS29dXwm","JMdL$<>kB{19x401-2<WL-ePVe85HjfE0}l6q{GNyv(t<!ljF90Ko{|l?D8[o~'z","*;f%3N0_b%[@;hc:8mDOTj*ARAWr{4F{i6V+Hh)H]UQRo1%,Ti)E1"]]

private def r53_2 : List (Chunk 53) := [
  w 53 54 200 1050581 1050902 58 4564 ["!c,t|?k?6q@#%tMr6G?-UH_v~/g(u=O3@@p@-8?{ASm[$KEP)B+v:7GMJ8hxxJ:|","pAY@},pw^vLufJoRp`8y4#NoTp/X(!uj{sGdJ_<QlqKzCdkh0.D:E"],
  w 53 53 0 1060000 1060214 100 10498 ["<DpQ.zo{=ErX/o#9I0ciDIdL`yKZr/1y;68y2*Y+2TU(]M%AV%J8W(Kl@&S*mkUV","6HK,6y:3m:U}NKBpk4E4h?XIi{v+wJ/95~[r4[QGC_s3/:53M_LLc~?K:!1wLwe&","/RotZe>nhZ:3CyAXm%>Xi=Rff7M6Y8.QgkVZZbFQm,NzrN{Y[bo^^.+cp>jIG(-v"],
  w 53 53 100 1060256 1060584 100 8770 payload12,
  w 53 53 200 1060585 1060901 51 3566 payload5]

private def r53_3 : List (Chunk 53) := [
  w 53 52 0 1070000 1070257 100 9484 [".s0&$pWozJGO&#+]y0g4nQ|!~n0]ueGntN7yVJd/]rTY;-6]x-2@8|)i#|,(UH$[","]~]f@3F&KwlA@'HgUB|cR'gpM8295l>H8X4Y70or>qrP5HET|=bv8)1Vysl9zI#3","<A#p<gb4q!,nu)h=X=[cr_sJ.bpzj/J*nxY<ZO-:7+2E59hnrC6,'z?(Rr*Ii.a4","&wn;u_SZ~?W=V;)"],
  w 53 52 100 1070258 1070588 100 7650 payload25,
  w 53 52 200 1070640 1070901 44 2856 payload29,
  w 53 51 0 1080000 1080259 100 8504 ["B0ZI44mc:@Fzl<N=;gjPC'M@yl!`HxhL,m_nU,l0+HqQs)UC<'}hvz7;3c/@0{}]","KY!Bt2IZtR4}B2/vUnl*-sdcqNi?DA;7qjdWerPv(V~5FNCxym*`N.SAcuoZ[%DJ","Cu369CZdQ18U[YY!#etACMBQIj?M)+@%g./m8Mo,W`}'q?Dt>Ved8KOWa<e($/;q","Y1(j6$Bu=j5<5;g/X(nV$&@K=?8n"]]

private def r53_4 : List (Chunk 53) := [
  w 53 51 100 1080260 1080644 100 6831 payload15,
  w 53 51 200 1080645 1080900 36 2216 payload24,
  w 53 50 0 1090000 1090261 100 7652 ["FbwYI}!(q_LS!<2M%Ptv|r]cqrv$.}#ABlDNew&3!L~Dh*IkPal0NZ$J0r6{+7(~","!+9G;<Eu,+=8)z3IYOL4F'Ks?n4kx&cK|6(9SO5=@59$u]P}`<dBj^X<1F%>):71","jN4ZV!?gCJ{:Z/nF8GOBP(H6eWqW.jnL5C$u,mvOYr;~$mF?~rmFx^P#%8K?<RTL","(OGq^W[@UgKKW4n;J~I!+w?.Yp!qRKf7M-}#iK!]8@"],
  w 53 50 100 1090262 1090649 100 6274 payload16]

private def r53_5 : List (Chunk 53) := [
  w 53 50 200 1090650 1090900 29 1723 payload13,
  w 53 49 0 1100000 1100263 100 6920 ["e3lt1K`[TvoH1k$$LZlkRYvkv]94h!cQ3Z(Mm=t|,of:!}GMog#c?jBn'G!{&f>v","_[qI<%Gf)V-zUlw*Kc.S*T4!5fR%7{lPQi-5lW^Jl-6:Dx,D[$yIeOK{s!bBR%_D","=3c]yd[w*+l!WnRYj%MBZECS?y76G]0:!ZB$ukkq-vZ%gF54S,fWzXcJszx6O-0q",":`-GY)pG0YvA*f:@R`9cQ9TCOMqh-bkg#$r;eniC,z(g[k&>;Q,{2t"],
  w 53 49 100 1100264 1100708 100 5925 payload8,
  w 53 49 200 1100709 1100899 21 1202 payload20]

private def r53_6 : List (Chunk 53) := [
  w 53 48 0 1110000 1110265 100 6351 ["|f$&@)ElZ&7[2Y&??XFCE3f&l-ms$rPG+&6qXPaugy#B_kBC/_T@%xkZob.`E>9r","[W<Zl^GYCCVinYD0cPJb`'LsF`#zpwh*gm0J>6wULy&Ejj5o*{luz5{>[Q&EAnE(","$a37W3[>>7u17}y#Ub^/oP:UwF5{5Y^Eb-WpVXxc'O^:P#ZaIw(T5rty{u~A4L.U","8ril*;iOK%R7t2!RIB*VhGKnk{;Zt:P|JRUl6'M;Oa'dWO(J2)!y;Q[H^nRL-+=l","2J9NjW"],
  w 53 48 100 1110266 1110769 100 5653 payload18,
  w 53 48 200 1110770 1110899 14 780 payload11,
  w 53 47 0 1120000 1120267 100 5933 [";LR[/Lr.,jLE|+:nHxNf2dACr<X&0)WnC')#`)!Kb2~oqYJ?)f[7>S4bk.S|}`Fv","<B-*}3E!IX0j)dD0Gn%TuF#*ZU>7YPSI(K*],57e^&JrD88ZTt*q&'/A`u}qn3I[","!EvBq.pPG0td[q/}VA&u2)}fy>Z6,{Z3rS/{sRp9_xo&_qe&lX)pb3K`[R7oMU7F","cVfm7@%$=)0^y>c3<-DPf#'3;}j#IyH1+#GGU3'xEAl`?]i*GCzrTpGtMOXPN1ES","'cB<PV6}&l;-IXYV!yEE>0ib-uk"]]

private def r53_7 : List (Chunk 53) := [
  w 53 47 100 1120268 1120833 100 5411 payload26,
  w 53 47 200 1120834 1120898 6 330 ["''*<pfK*jt/{_+Rwy>&v"],
  w 53 46 0 1130000 1130269 100 5594 [")k3Gqq[F&f|tO!Y[^{bI1Z/|=7_5g9tZK0B9jIj18}/Qw0U$[:)BC(h|6J,6*0dz","mT_je_s05&{^6[>u,D^?oL)XrsQId|RlXlDo6p<HU;W1ODH#3)Z]P]D`$lMV+Di#","15mRETtaheYim<s:uZp4GJ}+l@,nKZ?i?QD6FOTg=Yc/T!H[Ty7JW!@>no0IKd!M","}56Q*(Xz@f@!U$GLnV,&fpZ6KSrcif>4e,YI<?X;gQL~Crn-O8oiwQu5C)%D3*UV","#WKCKN1R6DFLap=^zN{+N`S.6U:^]h>'+2%T_4r6='x%WVw&"],
  w 53 46 100 1130270 1130898 99 5156 payload27]

private def r53_8 : List (Chunk 53) := [
  w 53 45 0 1140000 1140271 100 5287 ["N/yVAgzZ6Yq<%?DJOFmB#o=sUh=(OpGqc4jv{XhE<zamsDS5r:Hx1=g[*~cKi0w%","T=xH:=/*]kl{Ie7Ht*?HpG;JWEVlF()^sq*StyvNi@d?C61>z.$a+z9v2>x_U`@T","JS_%9.&>$=`L<p`XH~Oxg$iIYZ&1aXYKFY_7P{:@rD7}k5=nUt,__{T7}l^5^m.!","TM#qP|0Z/PAV?ZD-}KGaL[T8BQk-=fJ&=j_fTPPR>RIqH70QRc)W`Z35}1qUwg2h","'.zXY<[&e?v#Se0#,4N}nI7j0DCy]o()z-1@HCp+r-Ke]^Qcw>vN[moI6~>>cAnv","r768zf5Ukm"],
  w 53 45 100 1140272 1140897 91 4562 payload9,
  w 53 44 0 1150000 1150320 100 5013 ["e{Eu(T}#gk,a%ZkmR:NyKySL2b|DS6.,8O##J]Ls}foAVL''t:9lx2uf!{7#L8V%","[y~[t>M%+0{1r@B;>e<f*$ss(PVi2Dc8Y_}?u3GHxD^-Su2l'Q``gxA+`porZrG5","b]l,Dnh(_R2u1X%846ka~/dmXE4tb.,v9Kx1i;/0+5>R)r|GS@Qxbx^z7-[^@Wv/","@+;n<p}^w3k0jbz{~Yj;-{~+`tafmddH=hU_ux:9!E:-E'KZ2tvKF5W;@{N:8aHi","9a|}jjX+KKJ)u)-lA<iFq<rC|.MD`SHeN(9T6+YEj&#55!]+OXWwu7{secWwE._,","/|NGWx^:GDzF:y_Pt<=9q:55|1@R'KY</;e@0,%"],
  w 53 44 100 1150321 1150897 84 4053 payload7]

private def r53_9 : List (Chunk 53) := [
  w 53 43 0 1160000 1160323 100 4770 ["R@8K[M8$PSuG?wlOw.Yy4dNOL4#W;:V%?);:*4vQSyB);5:Jf-y`CQ_Ns]pt/`CI","8k|#Ww$.OjlQ92AyObi/kOIIH=Q7yI7`%4rmm!{Cf8q<!ggdCgr?K9VW.I%&Q##4","Yq_2=[Rj&Uitb.]h%|UzEK0k(MhKO:@V=vT0@d(OR=02S=EnCq$iw0F,o)-;8Q@|","ZhdoT^+fUOP|%fwm/;k|vDA&x24<ABIl]3{Pp/S/ST.N.Zs*2;@y(kJ!!(N6DzgV","45zYYy`>aO%RKS10*%2nU&oRQn$T9L'oP5,l[zYgZ!|~w&bF*3~[l!vc'-$Bq(pM","&XjFSymFt~tm1OJ6FS3-{qxz:vN{w-$!P3ti!D!,{,9RC&ac_62ni_wZ0J8xgx$w","1gL:f3ic"],
  w 53 43 100 1160324 1160896 76 3525 payload2,
  w 53 42 0 1170000 1170325 100 4539 ["w[QnJ-9bV`NsG2+dqmll0GP`w=U[R5]%&aL`j&gwH.@*ee$^]nF/<t|79-N8K@*5","@/I!RBG8pYOkAiGqeEw]N,=mEVDIIW>zE?Oj;HbsEFSj[d%.(`Ct`vUzIZD-4+Vx","Rc?[;L}G3twqu67QHc*D1zl,7GDg?.0;|NcJfyJ9yt.}hbVkPW#*4i3qfijip1)S","5s9Kjl[_yI?#nMrp^MSZ.H8_AZT^K6?*X1Vg{rPL@=>BJPUA,MH'c@_CWVmR$D_-","m?-~r$s=D^edMQML{dqw9j{p|M[WEsr`U/Bb^4*-EXpGvlm!X%i)/&LpRg>O?:5q","NjsFeb/mNR{a1:_/erkHoSL87P>rg@OmhSvTBx(|s3_1{##@,Im?/K|lc{K`THS;","13voCVvw9gE-kJ+P>WY%IzN|Qi3b71"],
  w 53 42 100 1170326 1170896 69 3084 payload10]

private def r53_10 : List (Chunk 53) := [
  w 53 41 0 1180000 1180328 100 4318 [">+%/eNJ<Z=IeQ|Xer^{:fN@;`sg$H-(hL2BM*tok6sRnPC</D&Om]nk.NL1N81kf","A2.P*3~=%e]59g'rk6RbEHVokdD-!'*(3ji~(!pN6!P)`bL.L=^6v4]v87(O20|I","5,Eus0U3Z_!v*9dO!+[:45K>r$CM?RFhr+u:eNx`g_FK6Z!E]iAkqc4-=(I2u(_d","5fa{nhF<6Gj=%xjE()R$aQD&i8[KIuiUS=Qr}p<d`D@b,82wz)KkqcUE|AJs.NC5","x3$wGco{BeNTsgP0aNeFs|#MSnWB,Rr_Jyde@_wkP%Or%mx.WON_8+TZ|e83rR6w","|z{?=%cY<>jP/w9WQFpas#%,TNYBGIiIg3M&jye=@+*ItO0K&.0G;$Z1AZV{:Gz.","uw$Bf7<7TsugNi5nBsKQ~G0?V~P&17^7FFSa^tw0(B$cAbW~D"],
  w 53 41 100 1180329 1180833 61 2632 payload6,
  w 53 40 0 1190000 1190330 100 4103 ["7p*tWa-,;Y'&Cs:Ruj:w{4P=9hLNBD)MC.k,.i#:z7I]VHW$K9S]sS1N_PMW#IDM","sk==/bW$F_{P=(}1LW67))0B~fs4]`}:|`94nX:q6Cyr@i14CSup4x-ht+tk3o/A",";$6;4TZPz;[8olAg!RI/Sb=#eZj7]L.7`9KJ~k9Ej9}%GXU5Sha`d-r<#>|ZUeJ)","?B.:4QW0PKrtyt92qcMageO!?s{}Um}}R.4qg$R9s*MD-]=4J2na.FW8rlkTk1*g",".dvMmC>_dejkDyCgJadffJ~?Ft(qR@}jq7tt]C!]g#:({]O9.6]j2&2~?hgw[Q;F","bfRl-`=*UB-.<SG1;St!%k+oKA>0g?[?!gk5&Y/]{UkkM*k_0JQjtFx._%;VL7x:","4}dy'}Y^0@cT00Mlv8p{aFPy>S@NNU<oxbEfRNNUm3SThi>X+a{bR#-q_GNo>i"],
  w 53 40 100 1190331 1190832 54 2257 payload19]

private def r53_11 : List (Chunk 53) := [
  w 53 39 0 1200000 1200384 100 3905 ["hz3~Nq3FDnz^{KG:bc(@64VBBnQeCrxMm^Jb?-kt&TVsT3*ul?HZW/p$0`l4OTxI","]J0rgOIXA;}]Luus^mkZYix_876=5f^h<jk?C9kirZOfCTg_Jma7G=MG)!eWUX:e","G(;4CXT,?eMBTd</g;EIB=1#NHVX,4,GOfMek#6wVV:vRB!$kbQbB<Po%)c|PDpz","yLd[#,'E9'~dBA=/71*0R_T;M2Bl0[W`*ZInB:mM88jI!HkF1O~+G-bs6/4ckwUE","!xY<BrdY_ftV>Xw#7$73W^4ar3@3@aCcf.-.!FG&5fYulO/X*lq7-;1WL_::1`s0","}qagK<ibs(]xLa=zB2@H?K$-~0Ir?A`gJ-neyYQ&>mQ9J-CZ+kA>'I]=ei!P,/K$","/.;e|Tfa?VsH&Nu@n!G`@Fs_6Z*%&r%&e(|O=aBL'uKVaFr7XKp+~gP=k.9O;b8z","+/hb"],
  w 53 39 100 1200385 1200832 47 1905 payload28,
  w 53 38 0 1210000 1210387 100 3715 ["w{C~3z0g<-8wmjvzA%[+xQ6~P<]/NH5,9dRy(zz-x'BJ?]!zHG*>?ZgmTlb-ge.=","[_%b]vex^epE;j3(14W}R>a}Pj:FPX7o7DM>S|xE~_fs5;*cChbX$M5~vuy+-vm)","eg7.C38H:t#95&8@A(=|bYcug.$D~dP+Eqn%[Z)j?Xk2<ulA=r*-p^AW4XX?gMmk","CFz|&hrsha:A>v'24R{gsENS'0Gn%tN~7[+lw9hjsoV=ko3:}ya%Foz,dB%]R#&F","K.;l0,>aw/?dLUmL<?SDAUUEQF=mN0H~hy+SgQ>PLsZn|j1}RdY[22,S5'Xax]!t","tOkMV!_9>[38S>_,JWXCaE8[H{Q9vC/XQC}mcE&m4RVRk6d(tG&H0ec?!?XdG|{[",";zMyn#$$C*4|Z4t0)GmcOM/^x$'~$@8#XfS{#W^875Bbj6SX43%6#1[iGVsS)z't","-$nyZ8==9,:("],
  w 53 38 100 1210388 1210769 40 1575 payload17]

private def r53_12 : List (Chunk 53) := [
  w 53 37 0 1220000 1220390 100 3538 ["%.2'RC|SUr~[0$?&^J18Tq0;Az1ePGm;3:[&xe5f3.pp6iHoJdLuV72jT~D5-A<&","n}*~]4U}QT`ENrYix=J[>5oLwy^Fk#/fWzoeYCY^*rsM'0JhE0Z@kgSI=A_FyQ^Z","Ua/WS's|w8.UBD)yMy3$R]SJhobmHK*BHfCU]2Tsq[Y(@N=M1:l!z1h7<fp'hy]G","i1H($DN@EY*;>Od9*.HeBBtTvRu'3QF.>)4h^p>SLXMy!%45Bpw(9wb&Jc<8>Uvu","(H<Acn_y@G{.wjkPjXdW@hTYe~d,l<0{^*j]6cJqGTUpVcC%k*dDmK]>k6OAB~CO","GS(~/f(w-uX?])k;1v~~Yr)OQ(BagkF;P3*=N!oYa#&rw3ouy@YU/..kPjt@s3VU","ij.QyA`Yo_,o2,8cD|&AxHe8]eQ+)X4&Wk.%_aLX0_(M7]>o6*S{vbSgkp&dHy,2","G@rdE]:eMUy[Qu9YbQ"],
  w 53 37 100 1220391 1220768 33 1268 payload22,
  w 53 36 0 1230000 1230393 100 3374 [">g3qK2dkl%ty@Pz1e4zcxjA#V6mXQh|TB-EqYbW8*qi6Rd18v'MZkz7'#uhlEndr","i5iMW<tr.&28-Y,kX3'>dzWZS*(00)/-..$'[24dSa/=:i#=/xTvESCY>?C_2.>d","d&WkL%Hn4Tt*]D^c|?SR^Y'Jv?XpklUMhct!o(SUd#7!z~1K<VC]@QxrqQ8l9=A;","}6E}`i;Bm5)BxTTB^}H$0[-Wm}F{Z2i=-S&]I.3=^tdAIL:I(vW@iXp95.=6j+PL","I<8|`t(b1`}Gih)ip'Xfl)[=f[ulrDG/'Ex:xpYB<9+O*.G#/,>uzIc66a$o*,GZ","v>H;De_J~sfny:d#KAPqvm[fAy^:,=D.$kPT8%14^ZaG,9'q'+*WjGpe4GyMp_~D","V03}YA|gYjRCW^DcAe7y-FG4.V'<qew+:6XMvAj@'Km^dWxaQ/F~=CY^x-H*!bjm","|&4K)C6'jXX~!B2Vw=D{}eT6"],
  w 53 36 100 1230448 1230768 27 1014 payload1]

private def r53_13 : List (Chunk 53) := [
  w 53 35 0 1240000 1240451 100 3225 ["dnx4v_eeY1zBY~Roz/y+q,%bdi1S3bH.PVB[pQ{aAqr9jz$0>Wn{t0c`93@hUVFM","CqZc:sIW$y17.Y/i&*(CUIwEdk%'VN<(TPaSXfOY*H]2.hS=[]v1YIey:9wcneN{","D1ef?hjb6q?~nbA_7-^2goF+=I7fdVI79XDTFF#?XP)4'KGVHh!4+62?#X[`$$c2","}.2kG)=LUBAN]<RCFKYNu?UU@X1nC9u)PeSFpVN}*E}9g*I>#y-@NGFd5N'I4mxC","l<2un?W3x`c`Tuc]l^)BehBMm'YpnA;-BkjX{#)Ywq|5n8Y87O~q^^O#;@^0=}*a","eJux)'<u+#Fs~sRv5ATbNrw#7/K3T1Y/cLcsXzY.^0A*}uSGL+j1Et#p3hr76+~W",".Dub>&{H'n6tU$#^_eRp&tbZ7ngXu;$09(b_%{lxtPx&=G-bdUo)yI~M)Le-y$G(","2@H7;lC_.+r@NDt|?-^g2BCHg2ZZFO"],
  w 53 35 100 1240452 1240705 20 733 payload3,
  w 53 34 0 1250000 1250454 100 3088 ["H}v25X~;j3/H>ZKg^H8K&}>k/V_`Y<J[;g&=rHc%?b^El9}i4?UpQJn>4T$#6auf","zvagGeS$$|_l#a0K+s@Rs-x|Z-n/)N)!,TqC),w|+6boYXc=?oFh*T:vjjQpS;e:","Z>)6&eKHCbT5q=?>!`c*{iLNz><<V_(/d'/N@5~B`ET-*=F^s-`$cxKBwG[Bz6';","*Zj5|ljXtj6^0<d%6x#IFBupN%FVdJ[owa0rqcB[<O}A!(k0,5#mFhxl(cyM>,q`","|Wz+L2Frh?sA_=q_{4!VsM!x59$]h@q&:'pS-jHlr1C/_DmQ07N4T+wO4]uYhy/8","h4c:Ia^#2lnC4f7J9{Sud?RqKooK^S^Gn58nsP|N.kjgm;DPxRW^K`.c/d9GV]je","gW#;6Pmc&6[hJw]Y-HJ;<aNWV9+UW$bM7aVYDEYL*x~qvsro{)%bOUxs>6l`jB%/","$%cE,*,Lt$bxgIP1&??M~*tGr["],
  w 53 34 100 1250512 1250704 14 503 payload14]

private def r53_14 : List (Chunk 53) := [
  w 53 33 0 1260000 1260515 100 2969 ["j]?sUj957`:8Zs{AjfoH}|^nMt6B#>=@W}2pH1ui-k7oN>'kV>VutO23Ng7}q9_=","-atW(fvh9y-g4i;^NrBz+)A;Y=K<*<`!F`3Hin9;ieQ^r;ok~B4n8fZ_lG[msw9V","*>e=)]YV,?x1aQ7$x&)0=LqJtmM*CN9rd)kC2(Y+,P{g]>-|_Ju#G!rcqBn}i+LV","]bTaLQ(iK9n^WZYY86eXOGyc=+kP+E{IEa1T:OT8bt$o<x!+v[t4o+Z=k8q$,D6W","OwcY#BI2B[u%X{44{~UEB[q<f-7pYHC/-50ZgROV^{hjh-!BPubO<wj&|VRX+0gF","qzI,Kq7^bF)Hj%'~iiB-AgqneNu7i^NL2xpefZigl]Tak3RAgZ98$hi%Z7x(_bFz","L0}CfFU8?wH@#2X<s.!ALbWd64Av[t)R+$)C{`y~(zOb->[UGA^mzD'=Ai.sFyTf","#U:HEv)=LZ2B=H/G~lN084pIK"],
  w 53 33 100 1260516 1260704 8 283 payload4,
  w 53 32 0 1270000 1270578 100 2861 ["N(nr17!vE.&q?0XN4Ym16T5Dh0)&QDG}Su!34?lgIN,D*)+qP)55(/5ZmGDc<xHE","us;HbxhpsS%1E@@z%zN,R8;)j#!PF3Y|90jr7gX0+8kyO_:'U_feW'(;(.U!3_xl","qJw'Pnaw9krDG'&#o_,0kL0q3L}}SCsCcHhO+#8NNpl'K*(*P)t`:EFX9HJ@>yoY",".Lu#:N;TbZ-x5yG;K=+.qq5vO)^h(s9Y7TWbp*u@|n'T9cPw+C/lgE~j3Hy>L}'*","us?L8=FMoHJ[&U@vFf.O{v'Q_BwpYoN'_8dI*zZ>lI>&w4sN<g,w|Ko%21v#Qe~V","PwC<=vvb1FvC[d_z3}}Af$,[/?X>!}D`q@_olHy+SWA]{d>6v:,|7-GIIt&*BOg(","|U1XD-5UO_7k*.m?axT,0@$3#.2[l{ncJEm,(=<{%fX:MGYAnE)hsqKwD^&G2jsu","&DVlGIXLD[Q~*~d)K=%}O#FO{"],
  w 53 32 100 1270640 1270641 2 70 ["#i2GG<Je"]]

private def r53_15 : List (Chunk 53) := [
  w 53 31 0 1280000 1280640 96 2637 ["9Nsu4$bIG3:q-!i/A4kOU;9'b}:sxf7yuj%Ukj4UKH-h,*TQc6&>J0(Hm.?rmIg^","f_spp;v'I%FdGgd!&B6S9[reT;q5FtVtyaq>eY)L^A0DGpKn4P3F!,$-(.#Yy/(G","1p('P&Nw9{M3yoe~YK;kVk^68`:gnn2>uiU?|X'{:9M8N3>DK`(6Kmqkq##'6|1!","&/az`ai}9*&J|}]v7;3SYHF'4V6~[J&]u'H!p`H!+UA_Wb;xq#3u2?kwk4(1x!;d","X/o?-?3OAa{nET5'Mar}OpT;jxEG!Kzs'<t+7#1v-cf_:+hV3rfOAqmv[L_$/D?N","KZT^eZQD>}yZvW`Q`ViB^>-S9FWdeOud;+;9IqpP59n$Ip)$TRKb]%8yfuRP0Ex{","tt%*fb/$$-qY=Oa,;70g~U!$Noi,;n,7X'[I[0vE,D{xrLyP5jv(h5}d2!C#.Q)g","*X6kkp"],
  w 53 30 0 1290000 1290640 91 2391 ["x%kxBic#s]P)~g|Sk-M/qB]>6o,,8{Sq#XpH:bMp?#R06R/B}~M(38Gpj<+_qy,E","@C*L8d0I`.XXD`iJB*tN~yrs^Om%[?m*N|%-6rml<:j'YDdeMqrsd^S0)w}3i$%T","0_=`]3/Za[EHZ+O+BTiMH%$K!_O<m7'zzimXH{4qFcF^1sGtqv{Kg]2!RI,sbO#R","[z)'D.J<yk0%r!)^m+2[Xfj6Q-,h]=q}eoL^MgJ3l8sj,iNE3iJF:dHtK:V7P)k]",">QDk6+X,z1)I;ZDLa9=V|E&6W6_zz-^6|H1CDSb>ZFFs(_{Xq|am.pb$IS&7Cz'Q","$d'Md[%?(#%jJV:-@J;g^|B,@4ogFts9pJtK)hVz>$9'9}PKz?prlHF)1Dp|4MU6","-N]fiwB(yhp=)4bKgO$WcbEt6/d`Um,`|~mDG}mp9RH+[W!H`"],
  w 53 29 0 1300000 1300577 85 2132 ["I/Qp/2QzUz9^gg-0XID6M++toaXMA85|W9>H+`v{E~mPAlH3gd*v_h*,bD~LRj?b","ty'sRRY-6;kJXroFz9~^37&P{'Jbo]*;78)jV)18*Z+.8iOl*iV2T)1ztjgcmO)Q","Ked6wp9IKc0KBiQ/''T?tUe|fxGKk,aW9/W7$yc]E'SUz8a9AWgp3kz>wl=FpV<W","O[()K]~*:1bw]]RE:TRKF9fgg+;`Y+x2MlpwD!5a]yq-5R.uZ<,jjdHf*_^lvqlJ","#*OvOp?168*!taN619VTO~WyRU/?jxC5VAG;CG#5#=}c@7e`6G?,{U>j)t/t:`-)",":p.L6MkH$_fp{TK.~>VNc.q7s5/w!`CDLnMqE#)<uokIxRkWuH#)&br[9Oc<!`U=","#j$eg)^'z/b^N/R!9n(q(x+C`]p"],
  w 53 28 0 1310000 1310576 80 1915 ["-=uLT~U:bFdM-VffW%xh1Ke-qZxy)u%[)4g?<IBdv!~'rB_XRsO1r^,H[X/%xp)(","a|hJ:t$BC^;*e5^Bl3ZsS{4}vAR'j~gVNV;5>2V+O+TD-SyQvmXN$0f`.EGs_dy0","(vNcU5]p#Td=Q-%da)}AsghI/X_=7$xGdYoF8p[N[[278Zg5%.q{wpw[6kU<jq2B","!$T><'[pMQ]on&!xZ*Q_TeF`KP?%DjOm&P1NZ'BG4W:NcC_/u7](-h%l+,FES,3Z","&z@:]l2:kL*SbLGO8=/$?pr6GjMD@dN-v%,ac2v{b*`+TgqqmO>(rH|bBO[4Q^{4",">,b>nny.cb9H{l<'=rvWoTwT@yr^<6j%W}.z|$.@4_Q~zjKJTL-m(w0'jpu<Mia*","*l]jb"]]

private def r53_16 : List (Chunk 53) := [
  w 53 27 0 1320000 1320576 75 1715 ["`$drXh/zqmn==bXvF2Jl;CygL$|.{V$7F<oEGK|A;Oo_gtHTuF;:}_s%{XcU&.Tn","Ddltv9.oAT`<b$3b*ENGY%xT6@yPg)upNQ+S5U#;_`D5b=O9!WNCH(Tm*nLysGpM","phspP(eJ05~Ch58=8zes;5,WK}/Bhg~)0&=aLF;j`F0xvTKVVv/2O]vUhx'MhSPN","mmnEQQX9>J(wZBGgJnBfv+P@c}#<1&R;c5E2e,i1!jn8#t^T9=VP}j5sd-9Yn@)f",",;D.F?5OYp5]p@@cTlDsC#RiYwd3(XrVlR!y*1AbF`P|ygn#wp'_G^KlW;xi^uf3","#Wf_ICeyfYARbaXl@cWQh@<3/O$7ThrYe7PD^qxkOrI|Ae5t]-"],
  w 53 26 0 1330000 1330513 70 1520 ["/|lU:t'0TmfdVrB6F'.Px$EMQL2__Reif6HzQ2S6aq56xEH9P[>VLvMMuZK^8_s%","RT]i3n6dhyJ93~}L-l]L{:WD3!QonF'w#KA]~w/W]i*sxYTj8<F:0:CHeX*jD({L","oX`Eq!y/blZV]n(Itoyr*/F<EF[cOo`->Q%>;'=2th>'w,RKm,lZa6.xuerUcIj6","+:I/q;UZxwZw@~=K>G#h,KI}CQ]:pc_.2_FNTiTS#<4c=84jF=%~/uke.9I.|E*0","T0:PeD/C;NjomGc{(]3M4d8#0AXj3e9=Z4E)wUu8.lwkSYOn>eqYR|F|KqUpj-L.","5Toi/Gr;B3zxAB)`d`xU|7%9t;j5$"],
  w 53 25 0 1340000 1340512 65 1340 ["J|b%~`vZL&FuVI<K1,xu-8h+*]i7m@PwwrN|'L)r`k-;*V>A]9lV]D&m6FI<8]h9","vpQSZd'-{5$FjEh')(C%Pz-Z5{(r^#5VFFzO%A6yO81G*5[k'LvA(#|f}V2:]6x4","K-AHEVT>Xg0q,fAXZA)'|$u4;FDw9Se,|hzs?_*kV0]/NVmYNr|)WhUI<@nVkfH:","%8{U)izfp)p8gldbt|rQ(k^hQ)=5Z}.-r!u,:_GT4Fx7*Wm%q|4q!A>PHgrI<3jV","P#Qy5*{Hb+VZH7[kl!5KlS1'BV$!wrijS=maM?!_W&QIWibJqsdDoVrcY[`HQr-w","-h.B,c^2/"],
  w 53 24 0 1350000 1350512 61 1191 [")4TW3v2yM#0.*NNnhYeV:-6Oak~'_>QjdC::6??+S7ZXl4X/,el0<(u2fuD|C{X~","Xz5UWWZs!!l4M<Yy2YBaMHH?OU1+xBNDxdP:NmkPF50lF{^ENU*})R16-3=|f''>","f*^152[=mo!3=QHn#/]d{&mfe~#o[Ao}Am;:i%i[_o%^uw=`;B@7n3FBh!-cp3>B","xfN[Hfg>rYEy/XG5Pc*Cv7bfUqKi=i,^fsDGV[gEPgeN97U}6IwE)NuN-F'In<'g","#V7HPX;kZ>ak}>[C;kC%$:Tb@Z0jHzHni[wia-_k-=HbC35m$vN;85bry"]]

private def r53_17 : List (Chunk 53) := [
  w 53 23 0 1360000 1360449 56 1030 ["N,ZJP&Dd{b:RPGF$nFO|o2(-%(SJx69mJ:(ji<nd*N~sr3oLIqL]!!W;H!+(u~@-","c-dfZ&#h;tN4gLlcy$`:P5&<R[oZhk&Q8$S1HL11=(/$oI.UI7tMPTVkJ96!3ANe","`Yx5;tpdnxg8;q3cdBz[`iJNO>ugkDYxxkGNGy/p6|2;yVOr#H'??X9I6aK(N}{i","8MwV]JCqk'bOq'fP=+Z2G9Ps%]e<xNiH'o;B/$d}BBPZ%>9%N&WS`UUyW)9'L6;6","#+&B=gNA&F,IH>MIy)ZJ$6ZH*R,nt9tKv3-p"],
  w 53 22 0 1370000 1370448 52 898 ["usl:<|Nlz!?1uWm^hzPKH{/ts&9s#3*r<Dlke?^7|Yz{9Q`nBu'r_dB[mBQx3vKz","wg;m%sbWNqE&NHd+I4pjLTW@%~l]J/7~!I<*xrp-c]Cz|a^>Idkbrw2O003k.Q~N","^cHEkfD,WH'+8*:g9E=dn;hnw{Jfsz7~VUCYvJA!a6)x2|EFa_7]cn;Z4w'xoNGU","i{3NcvfVl@y&E|M'@u`U$tE]xIMWn>6.aDk+lBbC1#6A/b>fIL)=8[b;z-Tx+n$j","),K^*e~2(1XBi7a)dJp"],
  w 53 21 0 1380000 1380448 48 778 [">.n5dWkO&`n=wrdW]'KhSGm^b>Y.cEBuB}&uJ6Y!MU'Qh(R^`T7|WK/C}&y'FQ$~","f,G`F)*I+L2JDLNnk|l@b2Np({fIG0iT9p.&NTf:H'70D;(rA?ySQx@8zxahRw2C","g+=_F~53*/o>M^@pF#ni9<|dZYL,-/1dWlDgzI}?w?Mow?=d.S)PX;5FsLRj>s^j","#X3FU5D8#[O-+7^P;d<,:CI>[a{u]|^{_s=v8l}mOM,L<A?(q'|`y=WP0|.(rY"],
  w 53 20 0 1390000 1390385 44 662 ["0L.[f58jD=DrY%P5Ygi6oeYLq,%oXs|+/Swicd`)UK@6q*U71oeG$-m=4[EFmt#9",",tQEo!n'4*Rc0][YD-=7AqkO#5T`m1`UAPfW^5UdWt?BdBiX#,/=w`1s?W3*M(=z","`P#`r.%a,zVqL&t:4a$c-XS,u9LY>~Yc7;3_(B{ZW;r_%F;i:t4g!3NJ._uv1DpM",",}qV1}-Nxxs:yIxJrou6&:QWFGsFQQA(-z1'w8TO-jFy"]]

private def r53_18 : List (Chunk 53) := [
  w 53 19 0 1400000 1400384 40 558 ["Z1tf|3=fr8wPr8c:cFBZXEFD(2.A]LaY;yJH.]$7/Sgym&c%}+I5x9n2D'dmB*i~","C9bZ}^&WJZJ0eN:=Pz}XAmTv'*d2TNx=]dzFuf=rfJH@llU_S_!,S+}tY^->5G/U","gS2='te(5vPV*7vFwki;0SH`b=SGbHahxxw2iF9&rgwn!<@at*V_LgPC>`FpM}6e","#37pVv2kA~B)5MsXF7YNbR9"],
  w 53 18 0 1410000 1410384 37 476 ["eQ@;gomV_L7H68x#Fv*9Otj:BbKuEz=h&CHX%Ah+M8^!&[xqTu7`5X(pBToexV'Y","2K=#2pe`b'gdMP-/SKpGz9E*&Ube0v:?K47zB4ZG3NbxC'HT(YhiiO;ZU@Rz'kOM","miZ^1piMlW)2k]1/l.^mg%]v-(PNh6YaYx{j=~Czj!_&mfz;f])2y.L*lG1-sxpV","#OjxkfF"],
  w 53 17 0 1420000 1420321 33 387 ["3CHVPo!Jsnqt:!Frt8l-AfHzy+g7pJExlQR_T^2yQA}~.}|*j0UhDl=Ibik2o!n1","<F>`),-KC9W2V:(1:}%v?7e@iPm/LjefOW-FR=4T6V*;D;#:/OG=yG$B;C'F{89{",")+!F./@z5gokz]-BL(&4ns)=:*8UFWXTPZUh/SCseRg'7Yw-$2"],
  w 53 16 0 1430000 1430320 30 318 ["CJ}'^?mN;Ns+|HTw$_PyDXG{=R}:Q<R><BJ9x[o)$}M/=-8PDsq,c<,2;j7/k42E","'WUh+(;7#&FfIRk:9%[b77m+>nA&IvOj@UIC~t4v(e(xmP;X?5l]n$g(1ECv?:mY","$j~{u+DjcM@AaDqh*1$;`aXte~i8pH|`,3;"]]

private def r53_19 : List (Chunk 53) := [
  w 53 15 0 1440000 1440320 27 258 ["v|5WOS#|M2Kq>UI&T6p/bw3z1NT!.CJ/N<oa~rv0`,jqU5Y*B5ks]YE7G!psKSfA","}Df<>9R1#S<**qOZKc9<GPSVy6wRL4+i:1yx}voAQv*#9(,S/3B2D]_,W:faHi'R","#Buzi8$nL,m{!XhFlk"],
  w 53 14 0 1450000 1450257 24 201 [";B/iB[4vi2vNd;Mtp7RsTz;L1VGa+OuTPl9VffLh'U<#lUU1T{0z4RYO@xqD[Cyn","F_B`V/G}xoQ!6i81gbZ%2Yh@%pzj+I{<Kd{x)<,EE:&QNgJYYS!O)AC%;vEgh9fm","7`r"],
  w 53 13 0 1460000 1460256 21 153 ["m}GjdOW}uUDx$p[pFID.?@cP5p'<V/x]pA91P>@f3yJ>N/@>[J84M4[#-Ls-,q#j","%&~nYw>vMvh1H[0|G3O42!znsxx2{kcA39(r*@+fmW0Nr2[)|y`"],
  w 53 12 0 1470000 1470256 19 118 ["xVl~_,A7BCtQ*0$Z7De+qIY,9#~a6a`nBhoCVZ+_4ZPIyf}mUV,4vby2n9>IehqM","'k>gTuy~sC#RW=Av8j=X95W>2pn$(5ZZW(i.vu<*"]]

private def r53_20 : List (Chunk 53) := [
  w 53 11 0 1480000 1480193 16 81 ["ryckPJhbIl@Z.(#{~.n2+R~%Zx~izFJyB%dY%k/h0V/8&4K83>88p1|3R}3KTdJ5","@~Nis1OJVg-Wld'C/Zpn1FkO"],
  w 53 10 0 1490000 1490192 14 55 ["F`W7F}3cHP0l/G_XU}r!2k[@TKc`b$ez,_<<OxvE&Vv7jjX9C6XX_6$W.',3ZUK9","'bwk3x4J3xG;m"],
  w 53 9 0 1500000 1500192 12 35 [".*F,4fX*Vjr7{-0tVq:DQ/2QP%OE_A|^daO1D~%=dM9*S3GwsP}T/Uq]X8g>i]C(","&"],
  w 53 8 0 1510000 1510129 10 17 ["n=$WP3<%HP/.p5/lHy(;[y1is5J0!O1x!}tcl|U)>?Pl%NJ,a[oXdD_"]]

private def r53_21 : List (Chunk 53) := [
  w 53 7 0 1520000 1520128 8 5 ["&|S?G&C>5T29btBvW$[Gl-v${{ocHSrIqmf,;}}U,'z"],
  w 53 6 0 1530000 1530128 7 1 ["^=@DYU/+1:j8$qLPSNWE/rN8;dP4+Y5lz"],
  w 53 5 0 1540000 1540065 5 0 [",VSw.pb?~K;4^^([h7ph*j1Q"],
  w 53 4 0 1550000 1550064 4 0 ["7TNuvF!#IFo%Hyy/_XP>"]]

private def r53_22 : List (Chunk 53) := [
  w 53 3 0 1560000 1560064 3 0 ["'*/<Bt:&<5Kjjr"],
  w 53 2 0 1570000 1570001 2 0 [".r<PK/:a@~"],
  w 53 1 0 1580000 1580000 1 0 ["+F}9A"],
  w 53 0 0 1590000 1590000 1 0 ["*L]:f"]]
private def chunks53:List (Chunk 53):=r53_0 ++ r53_1 ++ r53_2 ++ r53_3 ++ r53_4 ++ r53_5 ++ r53_6 ++ r53_7 ++ r53_8 ++ r53_9 ++ r53_10 ++ r53_11 ++ r53_12 ++ r53_13 ++ r53_14 ++ r53_15 ++ r53_16 ++ r53_17 ++ r53_18 ++ r53_19 ++ r53_20 ++ r53_21 ++ r53_22
def rows53:=rowsFrom chunks53

theorem good53 : ∀ r ∈ rows53,good 53 r=true:=rowsFrom_good chunks53

theorem sorted53 : rows53.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks53 0 (by decide +kernel)).1

theorem mass53 (i : Fin 57) :
    bandCount 53 (i.val:ℤ) 56 14≤(rows53.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks53).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 53 (j:ℤ) 56 14≤mass j chunks53))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total53 : (rows53.map (price 53)).sum = 316169 :=
  (total_eq chunks53).trans (by decide +kernel)



private def r54_0 : List (Chunk 54) := [
  w 54 56 0 1060002 1060211 100 8851 [],
  w 54 56 100 1060212 1060525 100 8283 [],
  w 54 56 200 1060526 1060903 72 5478 [],
  w 54 55 0 1070001 1070212 100 8488 ["tjdzG8Uq<wgrSvI/LYM:<sztag'|Y6dF)B*fyG{q5XZ'+UbzsJ1ZRD{/x=Z-$ljV","=JihM,OULywNg:)%KThkHL[9F.GS!*/Pw0~Y0QXBS~g:iw+,l*N`5hhYrl]%f]p1","S5(q?yj73p>Cj}ZvD5XG1(O])m:5o,gfY}%*_%C"]]

private def r54_1 : List (Chunk 54) := [
  w 54 55 100 1070213 1070576 100 7900 ["M30<GhOV1LFCez+0%%UGT,&b<;>sm_k#uC4%1m]i%^%BxWhc[KgtfH}cUg>GchlO","UDA)'6-2oFC2Nc^Vrzyn.YrWqYNn_3>`dZHrY8O#PatowAR%#D%+n6`.lj'/,wk?","#Nw#7.h3^O&L6Nf(@OVw8wN%B!RWAzpT96U&MZ?8J"],
  w 54 55 200 1070577 1070902 65 4718 ["*wQ!T>Dt+AK72j<,*BW;K{e]0c(G>7bYr8R1S[P}%P~ed$wb@#)-{XER$vWZKj&;","#.yB%pff]}6@<,JRg3Sf&&J,8Q:AXf!=C)7]02emp:!_Fo"],
  w 54 54 0 1080000 1080212 100 8133 ["g|Ua/oj(5!M)VzbKTf`7K#=}:ye`D<xp9^nQs<3=*bmGh`mQJ'O^cFon]},X[,:*","IpS[6G?TphA'G&[sg!Y7r2B_c[r,qs*!m5w;_ce*EHUiXsm?HbQHG@`b<(QeH'_w","$b]4!l_O+lr`=`Vh]zg]K)sKDoh|/'p&z&d&7ibToLe2i+F"],
  w 54 54 100 1080213 1080579 100 7547 payload23]

private def r54_2 : List (Chunk 54) := [
  w 54 54 200 1080580 1080902 59 4070 payload21,
  w 54 53 0 1090000 1090214 100 7754 ["<DpQ.zo{=Es3!y%_<Cg?o79>i&eg'=`:j/Hi+P{?-m1)nGs9i_;sJUtwrHYaM+j`","6HK,6y:3m:U}NKBpk4E4h?XIi{v+wJ/95~[r4[QGC_s3/:53M_LLc~?K:!1wLwe&","/RotZe>nhZ:3CyAXm%>Xi=Rff7M6Y8.QgkVZZbFQm,NzrN{Y[bo^^.+cp>jIG(-v"],
  w 54 53 100 1090256 1090584 100 7190 payload12,
  w 54 53 200 1090585 1090901 51 3356 payload5]

private def r54_3 : List (Chunk 54) := [
  w 54 52 0 1100000 1100257 100 7416 [",MJ>&?j/Q;:F5nPbO1P_F+Ret8o9N-)G1z^h}S3-L?*u&Y>ow|9x(E,Y!4/j)IN4","YVo'=(SDQY?%BnO(fi5%Nh$(&pBGLpTk$8OBUMSu8h>AK&+NG!M#G+D4S5eGo1Yd","Q2_$+*2'LdGHEub0pMzTx-DmvI'bzYhQMHkKIh25r/@Z4G+|jn{-SZi3]Gaw|%^2","#if=~Q])T(?5|6"],
  w 54 52 100 1100258 1100588 100 6798 payload25,
  w 54 52 200 1100640 1100901 44 2782 payload29,
  w 54 51 0 1110000 1110259 100 7078 ["Bn'zH^3T=znZj/:QhFj:a$N7/Vto8JDSdCW6zqFX}D{@~aEN9bul>Zl,FXdxUPty","*pK2,24$rHGh.k*0-Oym]<qto.dEw~|e1;FI`~PF+*9flr=Psp8fMVP8<&Mp~0X:","G,.dBCe[b.rI7>Ko,G:E|R*t2Vx|Y)g;RfTfQ@e^Q~5DRq0C-m(&MUzw+rCybUa&",")-K3b=J7784T[(K)/EI2q(BXR,"]]

private def r54_4 : List (Chunk 54) := [
  w 54 51 100 1110260 1110644 100 6446 payload15,
  w 54 51 200 1110645 1110900 36 2180 payload24,
  w 54 50 0 1120000 1120261 100 6742 ["mg`^:@WXY/Ml%'p`{]D4`w@pmnrB}G[3*oX[>FRlT9S:Rr8Yi`5'>ec>%4zmZ'+(","&7}jwN:Vr9~XT@/yRB'fefWI;q*RjV8/aJ]!{S<W1Q>)8%.sK28.LWtg+W]dGy]T","'W@0HBB(Reio<:/&$4t:(R&@X}^$5r6nr|Q$j;.sPF2MX}D9@+j}yDgC>&y<?cCh","=e|$}8WaZ/<r63bL{;4)nN*:u[WNl9<bH4~M=,"],
  w 54 50 100 1120262 1120649 100 6114 payload16]

private def r54_5 : List (Chunk 54) := [
  w 54 50 200 1120650 1120900 29 1694 payload13,
  w 54 49 0 1130000 1130263 100 6406 ["JV@aE8I%P&;R@-Pk0;So&'VJ/^O4nA9Oyrk;eZ:+,uDz}=;)vgebGW5J~EnOf<b0","|TfHA7>)Ug^;|qP7~RZ*k&$pHHww-R<>T@j/'2^i2,2~tNhYlUaQe~z[l}wpe>v<","<'%aBK-?cCX]^vA)FyKPWpza<%uk4S.xH&yrq[@-%6Toyi5ew`54!SHgymtyKxr)","#/?7y;dWcULE!#lInRNi_1V-/cHaA{0=T_G-}kypc;h>W>T,q?["],
  w 54 49 100 1130264 1130708 100 5821 payload8,
  w 54 49 200 1130709 1130899 21 1181 payload20]

private def r54_6 : List (Chunk 54) := [
  w 54 48 0 1140000 1140265 100 6077 ["TGq+,oHD,%{vi6[v6?|hjCxtN:0jmZ=gJ|?U&r|){,0,VV6q^XDoU`m',<-}$f{e","&St@cEI}jh^A5?M&}OT8+hRluZ&+eQf%)mVRT:Lb*c=JdLf$`aWtA$O$w.!Ov#ys","H]?]};~EpQfnX{*+O~:-A-?Ww=2zb38A;+q~>DI)YoXH~]/>]}]1DM_DA@4ZT$FQ","E53%}hyv3Ej(DT=A_0AdFL}EP2x[NQ'iY~&c*3lb[B1%sV0P9`L;Leksv~Cp]cql","i3"],
  w 54 48 100 1140266 1140769 100 5553 payload18,
  w 54 48 200 1140770 1140899 14 766 payload11,
  w 54 47 0 1150000 1150267 100 5759 ["M*iv1Dt#ad?[?E~o'XbwAPac;#r9yg%=zY4{_X=SN+jKs[@EGf#cI_Q3~cNQ5S-q","p`jY,qR;8OR70$@]`YdM2iS9Okv3:`fBxA=6y4D52(K9B^T2-M0[RC(>';O+m)ZD","Yiq*za7_?.kOK_#p_!Nx6W>+KC%4mfDx0K[n#4):8tPiw.|8CO~R]$TvB=Rc9a|R","<<IW<xVYLa^wS`)$yUdSc[u{4RTV_yG:E8OH7?c8tHQ}L8*H`l#Bm{%9%uis~&^e",":@~d2r!G8,?o#G6t~Tau:]t"]]

private def r54_7 : List (Chunk 54) := [
  w 54 47 100 1150268 1150833 100 5311 payload26,
  w 54 47 200 1150834 1150898 6 324 ["''*<pfK*jt/{_+Rwy>&v"],
  w 54 46 0 1160000 1160269 100 5454 ["Bwqlga$':/|kCz5=GwDD`DRW[I3H_%!YRNb#w|lkR&+45q.9#/6I-K^f8CAjNToD","C]{-62Xz9PD7yab{+['W*l]VZ8|P09Ia7%n'3;:s-E{rEc09F*.eWH8<>e+,TBR*","nw=5cu!NL^%I~(stUB?7'|P1Gt4qH+5-nWW=$oh9sSh/9w=hG4;H?#6lRnm$%;@R","Fr-nw^v<Y<AlQ.$MSrRk&,as_~7=s~!=Lumm$$Ou@YpR$tdTLo)>ue`?9ZtfM)$s","(h(tconRt*k[7Z1zKw^C}%9!tp5m`~k0/pmqn0#;1Q9]"],
  w 54 46 100 1160270 1160898 99 5057 payload27]

private def r54_8 : List (Chunk 54) := [
  w 54 45 0 1170000 1170271 100 5165 ["Ss+E{'BczdR</xrFgoo8p!d?IDGy/LtP%v(,|;#u^N~$n!wX:OIb*sNQOm:gx%ra","yv)>7t&l<R*40S%_8^eHFXSeD'r3IT$E[AaXm|k?PZpR[J%^)I_Sv_(/v4Oi/|ff","o0cWy+.A1FeBtBn2jrvuz@wvY%.l(-^<LdDPuk:[d<OG%)^l@TXeBtOX>EO>j2+$","%4O1+8za;yN<0^aYB;h'^0**<B1M2[D~lyX%0QN<Z'8Y<Y{/4},i{X-sJxbtaI_}","f;~k%xO!hHS;H9,!fh&+S?Szvn]Q%,bVN6%:>4I]%)Qs9DAi/p@{NId&G}#=@Y(g","%a?6U.V"],
  w 54 45 100 1170272 1170897 91 4471 payload9,
  w 54 44 0 1180000 1180320 100 4900 ["wK.60p1=Qmn|]wX'k[67kcJ:EP8b;6+ALrv[L2m;gOdM[V`G}:P3Dp4-;MCsf&*T","KNs/&k;neiEcjGknAuvJU(47*L$Gl.!C6expLtYUOQ'9^2~`DJ&D,bN>WlT6v=R5","<Cg=.<r.WI5%:6,;M`|=`>Ctj$@)TuSO7+Dl.VqYid`68*@ll4L7q42#$ez`fg=c","_Ppy7$@>Cq{c1?T=``y@K7oP|1J<OJv&~KQ&gacB7!H=1J8q6&q;efn+F;a8dd-~","uPTwz{h7X<^l$IR,7OoSa$G-,%9(,Tomk7w1RekWxA,C^+g%hzKU=>=Kr_645Q&1","^`'.jiA[F=B+Y5[wtM!['TvIABFpNC20Mg5"],
  w 54 44 100 1180321 1180897 84 3969 payload7]

private def r54_9 : List (Chunk 54) := [
  w 54 43 0 1190000 1190323 100 4658 [":02RGGx!_%(^7#?u&VfoAr!wr[f3,'4b7/dOI8X(7GqD}eM#+40<a`oNT5Ypr.}]","*.,@p*Hkd,~p[W>X/kfxXW~|XWOKIadlsV<w<xD'uCH8fBAp{!UTHt$;JgMaLX<A","y~k%.NP5CHM/?:6gZi}a,G4#2v,a+Cp7<*0p*EMc8`8u:x%HuNkN>0p!I]la3}N.","B?va8]0ZHAVfLTxF_TP@_e5KK([7*,Roa4}Ns#+R+Z|!{'F)L@>B+yYC)xsdDW!k","8V_?D90yF$)g!&qQ_yp5G!UpFf*Dwr9,A4CKx1tPpeJMZasqD+Kn'SOg,L;Qo{d%","oxS/{Q|5&Md`%M7{%-%Wip)wde_qy~t/DJhbydBXQ^^:iUO`/hg@lbFq);}t`tCp","f6|J"],
  w 54 43 100 1190324 1190896 76 3449 payload2,
  w 54 42 0 1200000 1200325 100 4428 ["%)Q=P;-oN!qwGsJt{]+!,v(IOn6bDq!XcdGeHT*wHMe`D)!(=sQd+HZt^t=Dp`@]","Q6;5517(AG4bcUG|VTd6?/NDNI/1~Xf:$/:-Q:/&xUPd0ygDud@A3{1h]Z#`i7Kg","#t!(800SrfDz'P-^}#U{^-'c?mx4'6~e3MwS!zwHv&Rh;{*/S,:1(2m$^%v!i6}b","mta}h8JoH^DAK+89knP0G<ibkH_7_Bsr+PakWbBGhz*:rU:]_q==-KVJtHx<8wix","`=|O6d51R{1P=f1R@p%r_tT'OrA9Bg~}Ud(:c[!J&HNfZWR6<g.3Q$yokDa,1[s9",".?sHh,yb3%1z;,!O$^SuOK6JZrvzO;pJj;W?Dla{ktf0ia|b<kLSgs:O06j%(;h{","#{Sh.YD4.X:pHJ`HtSjTLb_?RjNU"],
  w 54 42 100 1200326 1200896 69 3015 payload10]

private def r54_10 : List (Chunk 54) := [
  w 54 41 0 1210000 1210328 100 4208 ["Y9zF)&}5U|?57Z:nv{HKl~RH2MK.$EA~8G(v9/L<>kmYg}`kb`2Nm&R|0J*3nhn0","bf:Ng>nLs0;E=&6/Y}^-gj`=ZAt'VrM4YBhN,D=MNYQ]Y3;8V-_]G?_%Ohau0*rm","a{m1jM2f;#`n(r0:|NY5/!l,S2ukG.&K{Bg8Dhu;%P7cq'|-]m>0=[$z#2w8d!gQ","iQAQ(&6[YH{?xvB:5k[@45XFa)~PQz^xfFG4]xo^v|Zuv',p{$T,c~S(|,T,DTNb","[oZIr5=ZGP9u.S/,p/oK,Dp~*LAMZ+S3-_d_~Fu:e>&.1M'CM@e_Z/bm9B8Cq=/#","G!c`x;Ri_,u5z$-XM`XxHGDs2f#_/)cYOvJjS0BYKK!F*WeShDTCx:m9'Q=Qj|;.","?l?Xt_o~-*z7fo}Oih0wmS<d9Bt7[6dq-^.+W/[U'0EM8tkX"],
  w 54 41 100 1210329 1210833 61 2571 payload6,
  w 54 40 0 1220000 1220330 100 3994 ["z-c:^aLVN-__Zx#HH(/TZ%Vpg?=~F@CR45_$A1KtRZUCe.8^cKWTu0gW8p{+y_;y","36j--~/.=~v2k5gSLTb(+MZ]F%Ngj7=7}xf|Y5%Ulp6z*NBs[O(Cp:H2AAKg}t*G","x#mK}EXdCGg([3H^vPFZCjQP=FoQE@RZzFyl:H>B}g=f{i;5c>Qsl5kSY,d@ro>*","Msypi8t?:3l[i,9V_+;kPgEJYGza?Es'g6;8Q]1=~B/S(ZmgaoQ}aljpw(!vkUtx","w|,j}te/Gh21}GWYNwX_)Vb'+Wm3&-nEs['-a*K:@D}&a$Rv,`+hBg,7&!p<Egq_","-z}z+VbWe}P<?JqY^GL1?mN2r}:7c~qWt&H#kOi[q:<uORFGo7nXL)S']@yO;yz6","?.H#3ldW;L1v06|bU:dYin~00GS`VR['K<~zExcZ>nju%I.n|jHQ=Jqn%"],
  w 54 40 100 1220331 1220832 54 2203 payload19]

private def r54_11 : List (Chunk 54) := [
  w 54 39 0 1230000 1230384 100 3797 ["E&pf4?F-v7>4^f'Re1V1:y^z=%*?&{wbdmF.._W&BGlicM#.`0)(r1-q_)$[0{&=","Ct9,r)nv9yt5g},J<z!Eh#-8~,~`K`gv]<V-MCzsH'eOMR5^FkyVzxPEfvwwW@tq","#bFhrO*`hkV5vg-:%QW1s_FwuF4z|`X05wU~_pA4GM1%qM`0~bBEahVztX6*zOID","ODyNhnQSqEDkyCkM)!MR~r=9whiR.5Id//H,4;H!S'sZl/@hXE^)+?=XjyS,Y%ps","5;O<BPPq8ui<mSiEDpu$Ev6U</Z)q%LRB6oB6|-sHALG1x^CA$<#|j.LBhyP/J![","n@LaNSCAv}O_fxiiLO:.9O.p8M~kfMmF~1|*2+,El(L@/(BALVSS4@_Frcm@uY]0","^z_x-u3j:'U@aI</ae-vnr3LYC'7@&:jg,}e?!2=Nfg[%X2;&Rt]1`~DW&r"],
  w 54 39 100 1230385 1230832 47 1858 payload28,
  w 54 38 0 1240000 1240387 100 3607 ["jfn4b#Z$k87N~;&'K0=s9_y6OXPil^?5Y>%|pnY#n4#B7KuwUhbkp4bLqzkVcz:-","M^.GvqxD?.asv%@RtE>!PUpH0u$iU0!>'^9T}7a.&l:D$Z;4H8(UyEjtLnZ7@_@E","xUABg+S)OZw+s0lnFD?#XVjLE*f4CCSEPDSzU%5%bv|/8zIJaGglXo6>mk.P8`|6","ut`22`8UG4USwm>pg}4obuYHHv)0hf(R-vJGi_?~^'Pbm<h1W!1Ld3r&zHZ/tisI","L2K.m34YzWzYkp9^)(vRP*L_bg&e!|1BLQ{`=.L(hs8O'&)L]q!Ut^Syy}Y$ggoy","i~<@716|b@|RZv!WGa(JG:#h{n#lIO^8+nvkz6ZX!yyvK~WoYQ07yyQWc5ZH`CJ^","Ir03M}a$BcMK+y0~_bA.sM5NF{w2p{[5oNMrm.K[ot$=~JcL9~M_?HRi}>O'q"],
  w 54 38 100 1240388 1240769 40 1535 payload17]

private def r54_12 : List (Chunk 54) := [
  w 54 37 0 1250000 1250390 100 3430 ["7aFL_JT$DHGgJ>_pC>~Js^!rK8wa%7TOnDoo_/C)r5/#UH!)'eQ}6#1YMxYj5@vI","xG%x^8Aq(W,4K&u%s&zkK:dH`{B$?%;u1A*yS6:e?rt|R0wLgb]fgi(Y>0db.v$F","KdtFjRnyiA,|*un'8!2$CuQ<9ew?*|iNUArXJ8{lP8yWMgkV@Dyc{vFb:Oay>oeZ","vlln|E>fsTFG(t%apA)'W{6@YcF`WfhE(A(!:?Q={HaV#w6mHJ0|4nP+(:g5t8QB",";(`CSrM4EMBo~$zd~*T]6z++UJry`P^6c:Su7cqs+:kk0gJ2<iEYG'2t7eQ4JiT,","dX!6Yog<(#hJnQk&(#3&OUZ}Kr&K:OLhv,H.wdTi?twMT2sHrRCxzhu:hbfJ@Q?Z","(:*F2j[}1ZrcZeEU~3q-LtsQ#0@/+$);NZHDkmp<(U5mLPX!)eaCtFT+4|BmQ{-E"],
  w 54 37 100 1250391 1250768 33 1235 payload22,
  w 54 36 0 1260000 1260393 100 3268 ["n*>#W%GY0(/CjS$'|=XX`|Vb^=p6[-;WM:j4A'{lR&W:ReUqfflGt&C9wpr0,WLU","s&u;`Q=V3t}P)I0S;-P!|mDPJV##~'2BG=t.^%+d}5)iF~xlJM0E0xYJ5O16'Pj+","`8UF~*:F#,#4UYbzVa[Ng(4UeJ=dYNZh%H5-v*dwH%EUX@[Yf)[V-+ev5b4Ipep;","|'Av*!-0Q387]5A;!_n'o,5U7c`{Al+uPVQnL5?Iy%'[XnHetUA]DIthhl+QX1Iy","fgxUVy[7!Z]nEYL0m(_)=dv.fq<)p]$zEi}T/GDNeBnD@u6J]iS/s)z?Xb.?cHPj","Ic^F?bFuR!esy/XGc!|8?qf>7xl;ybgnCVdZ!M8(5#KP-?cLeqP<c_*x-k#$})1&","*7e=W_fC6(D[1WgH0cn5]+4@?RADpF1iio[-,[ClYkl#ua^#25X|-M#QX__re4'b"],
  w 54 36 100 1260448 1260768 27 987 payload1]

private def r54_13 : List (Chunk 54) := [
  w 54 35 0 1270000 1270451 100 3121 ["uTIbAQ9*gf3uSa&3C@Ngx,.=jeDkIk{WPj~A#VB:$9`t=vJk_.TX2c,7K`cVlXy5","$CX0G3rezW5!gn~:W@+,G*7U+UCx1wGhLQ7K6)Jre]G<rRA)Rv3{BB:9eo0j,A_S","E0}x%ClJjD#=w1ew[4`v,Xr>LXtXb5z1,?fs+beSUYOiO?$U.BFX_niN5`8!s9hG",")C>eD=yc/)1>l1PFx8WIb<N&?]?{o3<RSS/5Xge#yHd~YD}fPA:]AW3j-J6[B-h3","/O<B!CeY^VH^nu]-5'xf1a66Ir?<KB'F5a1^~i:&@TjnR)DC>O,pLR}G>g5vKBma","Fki/7Gj1*T+%)xRDw>sAz%GV$'izx}qBkf@MLcf1{tN`{qd?FpRqe2^&{?aB,R]Q","n;:*C9QWFiJ|en!%NsrP[/~,n'*M@wASr+lCq-9CWtfMC!$A'>NZ]5f&BVcvj#e&","SyL0"],
  w 54 35 100 1270452 1270705 20 713 payload3,
  w 54 34 0 1280000 1280454 100 2985 ["[Z?V;Q#A7RIe%!o|fVp[)p.+y[ksWDUS7H)^@Q_!.FRf;,gN{Z1Hm{G}K^zy2O6=","sOCF^4Q2T(vtjhRs6*G:))<;|p(l$q:]I.e16e=79Gak)-XFD5Nat@c+'!`CQ9%'","i7>XK!g,j5w=e]GdqkbU%a<9zsKwe0R+lEx01DH1niz2p[F=Ni.X+x||E*@Pa6cK","uW6XbSfk24hGEeWHR3IYnI#rAt>-Vqkix:,h).~++6n[p?GWdS40}ol(%6758Wv6","`-qBk=(o1Yg:~+`D3xHyIEohV:-yJUf~apur5O;IgAtf8Lw'j-(.__u9Az~DE[]c","c'pbD58rOv=B%RE^z}oY84aQ79az/X,k9h8CUa;M>u8p6-+=_m`/qiR0r[_.SV}U",")E0?>S>+6FAM'8uzTKPxLT2+Mq8aJ5@8g,7k4/eK#CFJ=`x[J^rkzal^C4yA@R+[","'pc#"],
  w 54 34 100 1280512 1280704 14 489 payload14]

private def r54_14 : List (Chunk 54) := [
  w 54 33 0 1290000 1290515 100 2867 ["(*3U9{f#>!*Ls8^i-W&Y0sIXnwud&C5+PbH$4.+T|DO7PY&6Mh:s^,y+`I'gT,pr","8{2;Vs&dwgACG,W0KC0iq2]p!w9v^xL]Er0i[q00}H7I:dxw~0}#}<hFRn}mK]Ve","0{_zHoaxp8*c$27U3D`,DwjUM%@lJ%0E:-D(Q<?@k,YRA'|s[OQa}gn.QCWm_5.v","`AIm%}y`xtV(Fp4C)mX9SaAnz8X`7wmuVWyKJ2H4yMbY|eJ_~%Q9&EGYzfp&t3B^","f0/V>Er2w-NU3L]2O^,ql}2@{1+VWO%BSMq=&%zw|Q^Ld4*4rJ4}wFN2'_B[XJ)/","N_&7+l1vf+#]j2Gz^Ne_j&KlJ^T79<QW-w<N-;lo/eof]V3+wwAOUtXd?[6efYSX","Utez.>>Y1Y@f+US!Rh~tyKN8a+pfJA}QN?-W;bLp-|'xTkM_w>OhvB{&en1xnh,@","3p["],
  w 54 33 100 1290516 1290704 8 275 payload4,
  w 54 32 0 1300000 1300578 100 2761 ["gF!xo^jI?%Cs5H>+P.?W]KK<('#yvt(14J*SVLY(YuG2]Q$F&gj=/3^{k_BoF<g-","X!|7_Dz'1Yl65SAz7i(odI@O9T$i%~VW!+#E'Kz]?@-YH7us.EW25!ud$EJQ'4t/","Z$6z1tA(lDh~<5JZq##L_zg,+FAWFqlT:|+C)xL5k5S]A;AQm$a)qDc;ZwPyY[W6","B[)_BlLF~gngmIF`3gFoSN?+909N]eBPM+?qhF#6L{H]cY}gT2t$[y*Dks&d.I,s","b|ZDPW3HTscv(uu?h;D#gIx&5l$RWl3LzP=?0tbi4`F(~]jJm,12UO2L+Yj)6[7y","OJgDl>fdNVQ`6S3St%S{974EKKuTLFhL&?^]*ZZo%l*:orXBwmK?918Op>=tE80X","jd*|vn6F]0iqtGa;;ULgApT.H0Nn^njEX*B4l*g[uj__03_]>lyrX,kU@4mPSO,c","#QR$<"],
  w 54 32 100 1300640 1300641 2 68 ["#i2GG<Je"]]

private def r54_15 : List (Chunk 54) := [
  w 54 31 0 1310000 1310640 96 2541 ["sWbB1BxN'$QMGy}cfSW-4Y'uf<fz}T0>coy]3z0S-kG$1mTlHq'&*~u;;Oe'3M7A","Y7LndvUo'D%]Ta9dBXb|`S5KMC(`js=eR)(=zNa*rCUekp<9HtU!Cq3,TJ{-V|0s","t{:}sw5lOu$Q4@Y}!crR+X~dK5obnv4dyHqd+KV&v8QDHs}J:)_FWhgeAprjr(zX","TVE[%O0=e+wtqni9X@n1y5oVI7jp-N=}_E+DRP<?PdUwD0]tHaia7.XqJm+bOzbK","x0;/pm;%j`S1YHo2'+nd7h}IK[5p.,8M1h562?TSvePGcB>thSa6g6`>g%SG;<;`","=AG90o0J[7OH!sAs$+wG+%}82IT_YFK/2~'aiVv2{Z:MRM4QeU:>:rvx6}8)vI?e","$(Qp<nR^%~JjdLYz1g:CUjsxc(;Oe9<d1c#*h2G9Gk2HI|P/N}0"],
  w 54 30 0 1320000 1320640 91 2300 ["-gY}qM#qF^pv2@t*8@HUNl7'6{KGF_n+w|[O.`(H6t%p%,E4#.yOKL,(Is]VGIk-","GB59T-Ut`f@>RxR1KM`BP^eg`Z+tAfG_^_{b,q(.7|qW-|A]em0Z|@LsjUh-%0eW","_%]sO=STJ[m>WMwyrKo_!i*`M!t:)Xd-do=D9}%D7qh4#%-TIiTAiqcbsarYqGhk","v'JRM+dPiN=Q2_ySy=9e((-dD{j)c;nmEIG4K?Mn$sk.K*#RWOYJJ/luP;]%#r*~","s4dCLN/m8$&5V<PUyMBbd38_&l`{[YbJ^/|9wp_@*iy_Lq=JaV$T@zTMiM4@@gbB","Vnnb,0Dk^7F+Dj(B{KaotCO9Gq>49h#|.75viK*>v{mrm/hO^-&Dg+<AQt9eh#C:","#A;zU/B{Wk=QHB%oa_e~f=^?3T7BgXbl"],
  w 54 29 0 1330000 1330577 85 2047 ["jo[]yOh3K)>J*5>0bcQpb<Lr~fsCXOX(+mpPUK}wJe3.EJZl)(`f;<2{9w;}-$[b","~lQxUm2Oq?k_Yw*S<dG}Z@'|f+0n>+^'i_u{UAY>TqQsFpt<Z,m&h7IFNg*D6<O#","5,B7UqU+W21&'0d~}T,nvP:0V.)1%Sc,Wso:Ki?L$M,Ki7EzLe`vfX*,E9#?E@Yb","%|]t~B3}yQE`!t|%XIDVv=>pWIrD6?AU~BfUs3I>F}M:(:)doO'E/1%^MC%io%Z,","Os7U0N`m2d:p4.9@w5-gfuo2CH@96>X~!dEk=grh!KXAWO=ej]%vgv~'Xt0T'SEm","r4)ke.lR@5z5Y9[K4)r4v*FTyNP(WVRAwymt<3Ojf1fP*@79SazU8Onn(Pquc'y4","=AV+/')q"],
  w 54 28 0 1340000 1340576 80 1835 ["rq%M-6^U32r'(Z(O|.F|UKqD~=K#-jmiA^blB^quv?)UI5,[Jr|I7YhS.G9y3Lp0","e-#a3,n@<.ef=kMA%DQ}u2}+?O?18mRv}i#<~w5)iFDn7oWt9|F?93xart?!.Q8{","WpB%UcSiyH8P6`,HQS+|x&'VCq]%JTg:$~iDO[8Pm'RtTt1T[.Y(I>zhEc5&S}6b","jWfFn*_%QfsT_}TLrp::-m)A^w)1Q^@G9/),z=t@!ux]on.GR$FCcY2D@dl<RV1M","tc>z(s1opRAKI#U*(UWWgZU14#.3*v>nw1WM,I;ZMfTDL&pwHNqu_7Z%)6ya-2t.","2IHUEgRvCgo{<UEo-n$40^$quyam+3[MGiXXbH6X9)K?,NzxkB1B"]]

private def r54_16 : List (Chunk 54) := [
  w 54 27 0 1350000 1350576 75 1640 ["_6?0~1sXQAy|v.SW4?(Ov4:-g&Jgtj(_E>;,YPV/;CK3]Agu-#-B(Yu!Jt$!7g-1","rF0!e(3pVKl$yS/#sE4BN7!*uwV7_bz)tD8K+O37>eJ~j_Jj(f]pQRE3a+sJ&vC]","$Y!@bh7f2S+9p+5;`j9R/puA'^(M<X66ei(-w#f23pen/1E(1m59#a@sTC25TB+*","|6cZUAX$ILBADy;w,.P.+2Z/P98&~@tZ~Z]Oiq+E1;.jQ'[Qx>[(-<~1pocCnUEA","?{p:Fl{qn~y?I+5b_)-zz6+U4g9?_Qil+'EAPinC)fh)*n$0m{G}GhyHBE<%1HA}","$'9Xlvo@7*fI$2D9(`CAy$gCa$-uIFv`CG"],
  w 54 26 0 1360000 1360513 70 1450 ["]psbM!q-Kk<>Tq?rVw`2_*$'w]/d}nnd&reYtiP4]G3m6Ljb+?g.xM0KQX<{zP~Q","O&{~_K+LM%1G_g,m$Zsbrh`R_.<_V!/DQ;U#=]3X)_)zM_gTR$,`dbe=<L8Pf(!c","'OA@fr^|GG=@HA7*Yhw,u(5hzI9x@&:mD)8=},Uv6I.cZsP{<sXN=cVga]Zj-*^C","A(H42-G8yXV=>#>bh8x1l]Zq)XN(a!9oAa(SA;D/wDhkEj_vc$`Qm~^Y/+N!G]Mn","GyuKdc,48jL~TaE)!!IOR]jcg0wf&P*;|arO#@/#c<+cW{|K{A'.I`Clp[3ClW^0","i_7T<].(Rr-,Qi"],
  w 54 25 0 1370000 1370512 65 1275 ["f`Az|AFdq;j(DN$fYR~tp+omsvtYnF?_7f1ND=JcZjI}/AE,GY^-h/Q2hBU}1'GI","x=%L)M)wngwC`J;{xp66.#,-4|!kfX;MsF&*C:n:[yJ[6VWor[]}'~?&eL<<r)oz","+v0pzF0yl5Z*~_Eh;Y?[(|%bxAuM9JYXI^_5SI}-3@[8.e'~m]bW2Y|?<(A,621K","9&kDo3ukE22K5gp%9TAhu/{$ZX$lzW>@N/4+Ppi5EBa8|->ub,jW{#FlxeU>`(W'","'._!l'Fbx6BR%Z@$g,iOIPifNBp1xG(+e@l{49~d:I]vQT[LTW<mT5w,Z):j"],
  w 54 24 0 1380000 1380512 61 1130 ["|0IbCp85*=L.5<^<-pIHei$l:s7A,mM5_>X`.kO0c#o*8q2B!B`FS(0Q1'oLl[_E","xp`Q>hjMG-wOo5xSr,fS?E[j]xh9nPn|wK(3D<z0POMkZZta5BOroyNU&d~r.8K%","vd%M0J0s:}+yeg8-L/SU6OKA(%<Eev6]VR+eHB|J&OZ+RshRQHt;iN8x'/QYMW5u","@PBB+k/E5<+0n0Yb:v@qT=d%Wxv2fV6~]FFc-@TnkVwk;X`SM2L@R<Qyr[U(aTw^","1i<I>uU|QXB<@Ak]$QnztOH5EQ.L!]}xOjvyKMc/a<]"]]

private def r54_17 : List (Chunk 54) := [
  w 54 23 0 1390000 1390449 56 974 ["z3B$@$)sW~yuT;elTb}-3rh?c!+Sx$,rgDFdH(2P9t-|6ZRHgJ[ej^dJ9*}qLH0=","JIeSJR0C:C{L?Os}/WWX|O9pR{osZ]Hy[XC[Y3zRQ5a|S<B2h:Z(Mqc{C/,mm+7M","K?zFB3rozWK%MS3x=V>8/^e,()fk`'q1f<&7jn~HaH+7bxu<pCS)%n|]5YPnLI^x",":Zocbk9,}KnbVL`54,eU,c(^NqMOSaGT>3twf+vf$D;uz6%lKCEBfX9?V_:P8+cm","#@x(2^kQ8I0.pZOU:c`}P2'!"],
  w 54 22 0 1400000 1400448 52 846 ["OS'9]pH:EI~fad>g$!,qWJA2A}^c*2,g3'{>D,}~}D94`:UP(p%6;29:C(n0v&4-","u)(u'|ET3}FuLNxF>{V!$!hj1=w/m3*&(<1cqZ~^:*KNPR]-n:/femshd}=:KeGV","~NuL/vi!uul6)Be>KLw'k3kXwX!uSFzb4UC+:v4[4;yC03g!jJQ-z[9@jzyAIK[.","M2Pdt@#c#_1VM^6djE2weMdpTEEjdc0'W^)7/NAl}E!C&[%gTG429#XFG;&k+:|!","&M<a|"],
  w 54 21 0 1410000 1410448 48 730 ["!Vo3+eYA?;>q{vvO4cTh)u)6#<K#32>n0Fw+lqPQ#Z(@D&#`<Nmw>gs1l8Y70yTM","jvr&`8)?7tPU]U.on5,mW=&xjm3GFGw#)i`rMY^c1,s~LA(.;jePiV=Hkdj?(*gC","=P[{|=*`]WI-;nM;}dh!R-r~x$.{]HmLk`~1[(jKU6XVM;PCLfkQ?J&77GKzM]*h",")fC*LSjjLmz4Q-4m:MI.7#ZPU%H(}qYQ2`J0[t.J.zv1X%wfe>"],
  w 54 20 0 1420000 1420385 44 618 ["<$F?vdg>Qa|_F`db_~(+tG>:WO4)}5yt+O/l|SQd-oQ$jJJ:`w~*!^I1yeDTd8Er","2b;MD.ub4{7A@'%I,h!VB-wAf~Q=WoZcnbM2o5]Ux^^uC1SHcM'f$'D+b_6TxiSD","$&Z>8B^,4^xfC#0g-8N?)Qq$oqt>(Cj|J>DGhHD?|;iCPYcF+yJSfPA0&-X>G2N5","=[)F@Ky>o4US$b6_}(=nL34Q'w8x.E"]]

private def r54_18 : List (Chunk 54) := [
  w 54 19 0 1430000 1430384 40 518 [">`?^F?+o%|HOX2vQ%xCF~LTZ)p%vne[1L7=0PYwH[yJ%&e0sNU}vkJskumQxS(mn",")ZXBUXq;WWO/)2>~Hm#J3USw;uZP)0/1K%ZoN4R@2a]TF.#54?~A7D~U2zB@V(}}","L#iuc`RDqm@x*We-zTdpF3Ezi3AZ9ZKnSVk+~[:ARukDjTVimT$}M@<qbJbE;0iI","9,5,qCiz07G"],
  w 54 18 0 1440000 1440384 37 439 ["v&QyitlHaR2yXviUN(xkWb0SaJ^;xr[}5piLzA*].$PoKAq2hZPBlnJo~sVP2}3j","!.7RS}XO_cIhJsg.rknyv<mWJUI'wc3?yVkKc)<?}7R8'C$GN}TO3?Duqd'~G<Aj","1'Hn/.dro.I<B[daY@5G.hKm+P.k]Tz>J1>eh+#xLDVA5d1rLgx/j<jA{"],
  w 54 17 0 1450000 1450321 33 354 ["A-UKmdlnc-5LN])K5mld*gXjYx,#|AcS,N^)3Rz[$EI7$Jg[+jL[6Zl+~{Uvcp6%","#VmXeTG~u?yAW3P[E6dehat,'-^pbo)J:<2UATQ'}EMkBug`9z)me@d+E%D+g,S@","(!ZTnY#sz!zTm%3N.2ll'A^5'L1<+QFMfAO+9k~"],
  w 54 16 0 1460000 1460320 30 288 [")icJO:~[%66ST'`[^4V&,@>:`:97*3mxg8|E0Z`5912k/_5~%}gTc:ugKALT+U!5","_ppkH@>'F1d'[B:aQ#[MK!=z)(6s|[G>{*QmOo(bSR=QIYFx%:*4!S!!rM+[[^au","pqjPSj;gN;jCUS&(W6HPX:"]]

private def r54_19 : List (Chunk 54) := [
  w 54 15 0 1470000 1470320 27 231 ["^MpdR6F6k=q9s']mJ*IUr$/{*i!0)-:06e9[;,E{8bD;AaNh*t+&j#A7RLNK<b4=","[5!`(o1=|;y^h(})m0LMvk?x;i=G1q^:L:pB)P)aPKH(g'*!l7cAG6u;Zz2^&q*:","%4-2WGeu"],
  w 54 14 0 1480000 1480257 24 177 ["o{p|FO=T=_,p/)K}f&[]+_>/g8P,#pwbrTh10G1,41'E]8&sFncOPBWMd:7#nZZE","4A@|2w~d?S3Jb2,^hC4*C{5+sx=kX@q%S5R);@=[.)1!BF:]4<2LV]L4"],
  w 54 13 0 1490000 1490256 21 132 ["%|VuW<jdDMu|;SL5%C9r].3Mv,S.x8K.me;$Y#i@keiz;h|(L%{c0U36VG84Ou|I","6#9O'_5ef}Y?WuT^LM|D=z$^+#o0x(!hbnlY)K5_{s"],
  w 54 12 0 1500000 1500256 19 99 ["DB49kDVKo$eQ{$uENa8-ukZ?Vm7C+*dQ'P[MP5Gie>JYyR?5xR87;8WVKS;pnUGj","/[P6Ds=fD@n+``CaZ4jm(`[no_)U4r"]]

private def r54_20 : List (Chunk 54) := [
  w 54 11 0 1510000 1510193 16 65 ["J$m(}$Y%Ij4`vj:pGyxH*G}X@D3hE7=x2qDV)#;1g!H1o*21'JR:*Mew-D,mZB=r","(/-e%uHC^tEm+DP`S"],
  w 54 10 0 1520000 1520192 14 41 [".0;^3FLn#%Lev2Z62b~{$l'8vXEoufD#kXo%<UR#CT{_s.pj-d`d8H9qn>:SR0Cj","#-oiGY"],
  w 54 9 0 1530000 1530192 12 23 ["(A:RY9/4e*nX)(Y;T0DX_+ex$/wI.C`1LsT&iQU?iW9q0Q3%s&BpJ+hY`{[j"],
  w 54 8 0 1540000 1540129 10 7 ["KR*a5&]|oRF^hH~EPPgIveN=g]iC6ezZJ%o<dD!DzmhVgr;cU"]]

private def r54_21 : List (Chunk 54) := [
  w 54 7 0 1550000 1550128 8 1 ["77bymfU;9PTzNpwu2=1Vj}4={dk~Y~cg|vuV)dY"],
  w 54 6 0 1560000 1560128 7 0 ["7>Pr3o>V|i1W}#7Y_xR;Su!Td&V65cb@"],
  w 54 5 0 1570000 1570065 5 0 ["@kNA97QqH5}kwE4}1I$BM1?-!"],
  w 54 4 0 1580000 1580064 4 0 [")Dd4QP5CY/+/{E!JoFv"]]

private def r54_22 : List (Chunk 54) := [
  w 54 3 0 1590000 1590064 3 0 ["7k-'D>dRyPe+I"],
  w 54 2 0 1600000 1600001 2 0 ["#e5MvmQa"],
  w 54 1 0 1610000 1610000 1 0 ["+Fn!v"],
  w 54 0 0 1620000 1620000 1 0 ["%1VD"]]
private def chunks54:List (Chunk 54):=r54_0 ++ r54_1 ++ r54_2 ++ r54_3 ++ r54_4 ++ r54_5 ++ r54_6 ++ r54_7 ++ r54_8 ++ r54_9 ++ r54_10 ++ r54_11 ++ r54_12 ++ r54_13 ++ r54_14 ++ r54_15 ++ r54_16 ++ r54_17 ++ r54_18 ++ r54_19 ++ r54_20 ++ r54_21 ++ r54_22
def rows54:=rowsFrom chunks54

theorem good54 : ∀ r ∈ rows54,good 54 r=true:=rowsFrom_good chunks54

theorem sorted54 : rows54.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks54 0 (by decide +kernel)).1

theorem mass54 (i : Fin 57) :
    bandCount 54 (i.val:ℤ) 56 14≤(rows54.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks54).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 54 (j:ℤ) 56 14≤mass j chunks54))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total54 : (rows54.map (price 54)).sum = 276515 :=
  (total_eq chunks54).trans (by decide +kernel)


end Final50RankReceipt

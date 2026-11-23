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



private def r55_0 : List (Chunk 55) := [
  w 55 56 0 1090001 1090210 100 14025 [],
  w 55 56 100 1090211 1090524 100 12261 [],
  w 55 56 200 1090525 1090903 73 7461 [],
  w 55 55 0 1100000 1100211 100 12942 ["U71[_e@bhyeAECU;]EkQ);D'w]*2Xn+U$DA1_aH#|4jQ`38[oX-L6XH*h}dPWkUV","sl3k4f-&dydC#`f`iqv3$Oeq(0:-dIXOt_PH+^?3:@eewaJXG6eyt_Y&8Qh>8>f!","S5(q?yj73p>Cj}ZvD5XG1(O])m:5o,gfY|dLK%?"]]

private def r55_1 : List (Chunk 55) := [
  w 55 55 100 1100212 1100527 100 11076 payload0,
  w 55 55 200 1100576 1100902 66 6084 ["S<F1vgOE{'nSHp6[|7}a1)<b08XNTrzR'F;wc7k@03sz`#7c)}e>,ah6g[NdtU,S",";F$3;XMpg{FT/>H7#}M!L,gw'2/v@=T[&C'TUcA?~uHZUl}"],
  w 55 54 0 1110000 1110212 100 11781 ["x5kyO[h:t=t)B!U[2<Ea-[r3G?PjHyq|mL/5Fs-F3U''r~A~M=$-4OiN,hM}wzn`","ri)6jq7NByI%*t&`7`co?Psvp!05Lq<8QHQFw)v@U>&Jcqlr_fyrtA_*T.klvhQn",")O'y,6{?Q;SaV~@lk&0}]?vr.xXc&B8Gi7*~kVcpJis0^(/D"],
  w 55 54 100 1110213 1110579 100 10041 payload23]

private def r55_2 : List (Chunk 55) := [
  w 55 54 200 1110580 1110902 59 4776 payload21,
  w 55 53 0 1120000 1120214 100 10644 ["<DpQ.zo{=Es3!y%_<Cg?o79>i&eg'=`:j/Hi+P{?-m1)nGs9i_;sJUtwrHYcAjVe","6HK,6y:3m:U}NKBpk4E4h?XIi{v+wJ/95~[r4[QGC_s3/:53M_LLc~?K:!1wLwe&","/RotZe>nhZ:3CyAXm%>Xi=Rff7M6Y8.QgkVZZbFQm,NzrN{Y[bo^^.+cp>jIG(-v"],
  w 55 53 100 1120256 1120584 100 8970 payload12,
  w 55 53 200 1120585 1120901 51 3642 payload5]

private def r55_3 : List (Chunk 55) := [
  w 55 52 0 1130000 1130257 100 9630 ["{*(}`o=zE&&iW:D?dy`]Ko6a(k?iRb<}B&=31*+&dx^@Pfj[l^<@0hqgO^!kzVQa","4v6Ho_%kC{}?-:fDtNMwLyQm'&ZTL5d8Uhm52#8ors&j~lb<GQlN53^IYS>^l|3+","!2zwnPF!#{_t!r$G(i|+u}{uz=+efT1e`[<s_tq&Et[}'nZLFW-NYuQdMdTwI0gs","]N>go''Wx^DO"],
  w 55 52 100 1130258 1130588 100 7797 payload25,
  w 55 52 200 1130640 1130901 44 2832 payload29,
  w 55 51 0 1140000 1140259 100 8617 ["[[k|n}(uOEwgrA?4sGsjZ>%iQq3VGLUtG~&syXVZ;PqbD.nYsXQFyeAvj=RIz(*D","fXx@Z+GJ}0183__GIW!c9z(jMjx(8|NTxXCUv9dz,+#Rjl}>Vk29}DAm,t7fPdna","`7{Kyfbs!Yh>T%AkRw8#W2C*ya#j/Q+|6a)$H]c7)#I{upxX%;m'&NGC$w&)tL|!","$UTg1UTFDz%kn.Dt[~l#g>0X*"]]

private def r55_4 : List (Chunk 55) := [
  w 55 51 100 1140260 1140644 100 6831 payload15,
  w 55 51 200 1140645 1140900 36 2149 payload24,
  w 55 50 0 1150000 1150261 100 7662 ["1ENlv,2g.Iyjlaw%MoH6w@s[)p4]d%g/CK}jD|:[kI[@^-mN'`@[0ptM7Vv#mTF4","ssWuy6=GWOfUYSdLEGP$'^w_taMsbRe5L<h6p|?5ZNEb;YBh>vlFcqT~3<Jp0t44","aTs|um0P$AtOW<b=b9kvo5X^'8]K@}Q0`iIBda}|JI`s``K+J!h]xrwC3e/;9olJ","+{hD.>81>ljLpbqs-Y''b'j|K3n<0nxj`1KOg"],
  w 55 50 100 1150262 1150649 100 6151 payload16]

private def r55_5 : List (Chunk 55) := [
  w 55 50 200 1150650 1150900 29 1665 payload13,
  w 55 49 0 1160000 1160263 100 6846 ["2bKm;=%g_3}_wxW#!'.&|.{90IG3anzH]4;lG~P*_jM}38Ea4_<.Lvyb&`XWK5Ma","NTs&+Lq*_6%+m$+R8;cvG_Ez:z-,E}F%ctA2y[x&6vH0fQ|FQC[EG;QHaLF}ra^:","#ua3.Ak;],3nc4_.Yp{V<l|o(VNRJ?_k53}u|(betXAnijIY{flgdGV9}uz<V]3w","Gq(K(C],:8HKbuK[@CA.~p`PZ5^jr,tjF)X[(*5=H!M@_VQ$;"],
  w 55 49 100 1160264 1160708 100 5741 payload8,
  w 55 49 200 1160709 1160899 21 1160 payload20]

private def r55_6 : List (Chunk 55) := [
  w 55 48 0 1170000 1170265 100 6197 ["S(Zesuzp%]7T]qI%UM8;(EdE2Ae2mah+|<6Y2vb7z`qFc2#QgQ<f/.nFa5Pk>Hy}","g_VI<pi7U>_{t_.$S7#~CnE&Y>9#MgM$RT8Nh4'wA=Uqr?;HL^Sl~%{WUC,'xO^]","n9z)jPnLv?=6'Yb;vw*C+ns9VJBiji/EACLBcJED1`h5UEm)_Yc4$^o'tAE<my|}","6[5oUgU#&#y1M}%cKUm0:yHK+t<5:|>H!y8_[RyuT2=D0@E~LOt$9RHDn)3$+5_a",";"],
  w 55 48 100 1170266 1170769 100 5453 payload18,
  w 55 48 200 1170770 1170899 14 752 payload11,
  w 55 47 0 1180000 1180267 100 5715 ["4.ZA7:5eO1B+50sOy;!|*gnd_MO7=<r(y7HRP7j::|1#87kBNB8^TM!2{G:]-]um","=Z`#<~X*eV^N^BBL]L:@doLY)!^:/F2J#iwUMLM|wQLV4Kw^e1[43lJ]@5/MR)y,","{[HFbXPlvN|GTojt0|-a/Dd0GuI2{c7A7}!Wp:rmN^|`D,,GnY1*Kw+SwW=/3AQ(","0p!sB*8-dxjEvVB#*8NL82%UDV_Va&^liVw:z&kN^|]GCz''uuWTlYb:1M*2p}6B","*g]oZD/)]9op]!JVL{^|yN"]]

private def r55_7 : List (Chunk 55) := [
  w 55 47 100 1180268 1180833 100 5211 payload26,
  w 55 47 200 1180834 1180898 6 318 ["''*<pfK*jt/{_+Rwy>&v"],
  w 55 46 0 1190000 1190269 100 5358 ["k!@OVDg<ZQO;)?KG-<UtBWae@izFK4c@G4r>F[q;)DQMU,!iRQq'v'Tv;YM[rAOi","k!X9&$yLgfEBIP{_C+5(?/6dZ;{hS^gl4&b2vliu9&*ZD;iOD;vI(a?U.@K!FqM>","eHj};ihe=N(pHmHGbmQThE56v1&gX'(2y3+3djK{.u.-vo0NM[x]!oTh<I+~<Ylk","aa-336C$Z~gG=qh!tj+u6.}*6CHSAWSzl-+]PeqR,usJl?kO,z:Lsnf)_o&]->HL","$I4<NrBu9F6B(@8}Ch7@u`S{!_maj0=Coq;LcE6WYt`"],
  w 55 46 100 1190270 1190898 99 4958 payload27]

private def r55_8 : List (Chunk 55) := [
  w 55 45 0 1200000 1200271 100 5060 ["_5C+-NWa(*Q}`/]1Xu7r/{&V6]dU!i{e`,$S]V5&~Q9Bdc@Q^h2@(rD`~nFj/jL}","O[+f>orJSA*_K$A~sX.p'2$B8H,f:zR17I=42nnF&qV&r<EzUHYyJy-R5D5WnR/U","q]~S)t9GOcMEAyfqie)0A8i&]k{n%9i>OK6Z{f-Xq8$@b[1b2<km<eJkK)@!MG)6","C(uoYg#']?K/%^tnb#SPE*?P$||3'Kvs.rhxT!v3BUitI~O}ZO]9~[dK^*{=;%gs","czIRl@0vfoc0oc'IS.q!%I<IQG>Z{jU;e=EzHwtDCk}Eu$^jk^Y+bH|#mu^_pEIw","#?W[cD"],
  w 55 45 100 1200272 1200897 91 4380 payload9,
  w 55 44 0 1210000 1210320 100 4794 [":GS;zgWYmW-)2F}j2KvmooJGM:9m;ZP%Bs*XO)|H3saIAO-g(LP2Y-)ZnxAHODBe","Kq0b=bR|jjI`c{w#f@/}C:+H24qBO5*[[yQ&|^|cRbk|W'L&3gJ:VP{yC;)gCEb)","-8H!+h+_'{4G$Z.|yjhd09M9aKA$3*7%Gn/In0WOOwB6UoyD(FCz&|w0Ds%y.-GN","b-aot=a^iVHJP'PU.nB?X(3vUDwZ1:{#*}CYeF2k!)TLQ.f^{NWOE-&8a>q6xkN|","c^p+a0C@](VcZIb)6xB<(BBN{m&%|tHF7-WsUWK95D}8G{ly:B?~-8h+rfJ@9l.X","7J[v_<d~'qo6cG89?;Q_hUBqnzoO*hHrzX"],
  w 55 44 100 1210321 1210897 84 3885 payload7]

private def r55_9 : List (Chunk 55) := [
  w 55 43 0 1220000 1220323 100 4552 ["AC,pmuJyZ=?qVvg%U&Qc[[K@Qgra{)x8RY%O+.`>',VH747#)WZp!{^XlPl3]hs4","7X`qLd)A3PG#E)hM@{@K_z2Rr]IB/KVej,:SwwI>&~Gt>=)>bzbKR>A~E#cqz.I]","*{iC(s`~Boc.[|W:cv_!{K,O<=][$3g6V5J>@W?~u$FESbWUSw:e=Hs)TL~VBH*)","s:T~t>9jD^jeEgN2>}hujF4&,WVbb]}%2'+c/9!FNY5%7vFJ;a^iUkVb#o1&V8Nx","|Va&I>-4>1nOvDQgM!A5-<7iE!:,4=[78G*%F[wi}/U3Ha'Ax`.$*<IB9%hn=9As","^7uN|oDN~_T5<8mMo4D06i#o0]-#g[.uB,yR&<q,;AOs7p+t+%P[[(BpxUO;Mell",":0e"],
  w 55 43 100 1220324 1220896 76 3373 payload2,
  w 55 42 0 1230000 1230325 100 4322 ["mi+tb(V0>wn'C5C6Jzw-r+`M~nG*s;LGX0]!ZxesoA)*/IUE{QF-FA-zJ`.`&>ba","AKGMULnvhpGm;i]eoh46UrM_Pu*?1mYYl?Qt}E`rJWgneSxlK<q+Lot~v{[PY9lo","7xNwo~@{Y=5u~_w.mg<J7k~_}aLf~=hB{M_An,GAjN6?#u]|2CLP'H0`+VpX:dNw","_>B748!slL]dRa5.>a+t;=jIjlL^$%!?'IBX3L=)@nKC0b*C<oOEay&s_bi&j8ZA","4x;rY(!IzQjy(W*@#U@UcV(>&q=(wWL&>7L(V!6Ne/*)KTQ}^%r,.%{gWM9{K$g7","KDZfda5gRWUK`TdGTai;,{5-_Xy6+s{B/5r[|[(BbS3s48RPYm>w<P>plex*;Sbt","ct-vXFeu/h=n[g(kIKR?e!,ZAJ"],
  w 55 42 100 1230326 1230896 69 2946 payload10]

private def r55_10 : List (Chunk 55) := [
  w 55 41 0 1240000 1240328 100 4103 ["Y9zF)&}5U|?57Z:nv{HKl~RH2MK.$EA~8G(v9/L<>l0e`={:>W|@bc:O+r!':jIP","bf:Ng>nLs0;E=&6/Y}^-gj`=ZAt'VrM4YBhN,D=MNYQ]Y3;8V-_]G?_%Ohau0*rm","a{m1jM2f;#`n(r0:|NY5/!l,S2ukG.&K{Bg8Dhu;%P7cq'|-]m>0=[$z#2w8d!gQ","iQAQ(&6[YH{?xvB:5k[@45XFa)~PQz^xfFG4]xo^v|Zuv',p{$T,c~S(|,T,DTNb","[oZIr5=ZGP9u.S/,p/oK,Dp~*LAMZ+S3-_d_~Fu:e>&.1M'CM@e_Z/bm9B8Cq=/#","G!c`x;Ri_,u5z$-XM`XxHGDs2f#_/)cYOvJjS0BYKK!F*WeShDTCx:m9'Q=Qj|;.","?l?Xt_o~-*z7fo}Oih0wmS<d9Bt7[6dq-^.+W/[U'0EM8tkX"],
  w 55 41 100 1240329 1240833 61 2510 payload6,
  w 55 40 0 1250000 1250330 100 3890 ["Wt[F%+z.H}YyNk5&nZm)gP#<2JCRs<;mxl}&gZE08#-T$59a@-JuIo5D;/NLfZv)","*bbRUJ8b_NUdoM4Xn;BX<]$fkfW!:dq*BA838._$e&|V*=NbU|_hq<@@|8i83Y_i","]3ZdVLT1B,VDRDx?c_4,<!]i9n|H~j]GX{vdbcp#V+Z1e,A!J/&Oz|Ua!Vs%B_>r","iZ#jL?UB+)9^R(PmXr+)oD&KNj`)(Wb4d>o<?_8ADOiO,K3Sr>@DORJtt3;0cZ:F","ML%;J8Y8@bswsOIE)!@Ft{|D0j!^eP&8joGhG9h0o>1J}m%k4D#on7o6x39=j=6I","p>fUD2Dgq8]Fhoc~Os<Fdt/o9>gDWl`hxNyF`#Zc3w3B`:}copdAN!goVA$OL/]U",",M;0l{=s{5M*?T_}G,?@+]xz$=r_yJMPQv#HXY7j}q}R1Yh==zN$[=[("],
  w 55 40 100 1250331 1250832 54 2149 payload19]

private def r55_11 : List (Chunk 55) := [
  w 55 39 0 1260000 1260384 100 3693 ["2T5pj`lO|zIEZ>na^$U@#$fH2AZrr]Kxxi2]YG?D6Oi21Prwt50%JDZHt$PaSQC1","xYuOU(r1SyUGAU:c<C~tS[21JU<!if=b(Wx6;Le6S3~|]o[NMzswB4o`s6_&RO{U","#z:4~8O{!k%4#ln5Dc)vp#2'#Jt1P4Xas/g,KFAT{'.s|kJN.]g-pUjHr!VE/Hl^","jb-mky7b&r+0Od9fEl5p5ezHsqS<JNdegm(-;Y}m_~FAb:.P-eBMLDa3#9&-Q2>*","4}w4]9#+'^McT]%wn'@[;)KQ^z_ytEYQVL.Ysghvopg^uug,X6~K/wF7Qa9/17n2","I#?oPRCUEXel=H/:JYrM[OQPXrsLE;v#G|v4N;I2~$Y?s[-RD&YIJm=L!gnIZG]Y",")gB3naR(Rn#dF.hN-m1j[h/+V4};'A?ckUvn*^(b4{RnM(ZXK%JD-r?Ip"],
  w 55 39 100 1260385 1260832 47 1811 payload28,
  w 55 38 0 1270000 1270387 100 3503 [":Ov2wJS.}+:ih+(5R6$B#(lKsh`eBy<eyE!=}:u$=K!Yd;,0r+N~D5yep6vq*?Bn","^Ij%xa%FG>)`iMLtdv}MF=Di9uy'c3YJ/g..l;Qeml_C[|_FYCNk12Cb'y7mz,5R","!f/eN~[Fuf$CYsI>'27$KtSEZ6!S1jJE)Ek*L9C|A!]CTpMH<]@90V:u-A-CZ{2S","P?nRPU1C()G%?96ibYj#6}[y,RI$jZ'L#SV$hclx+BZ=^'X>x183,R|zaZ71x+AA","?[!=zk_(hmECmGLBtbFo8s2nlIb>1t55{J#[mOw_A`MN)-cfF2m%^rMa(8pG1jNz","iiVQaiAZt=Vyv-@ZulMI`(Z4`GmE=(e>8GQ.AL]|IMKWm|)+{b<%D9!Dy83-(;Ef","'/ZR=m%_*h{:YN=qn+|ts,98j|wCRt*wAHK0/Xh(z`?(J}iGJc9yoF2&?&J"],
  w 55 38 100 1270388 1270769 40 1495 payload17]

private def r55_12 : List (Chunk 55) := [
  w 55 37 0 1280000 1280390 100 3326 ["!lLVa^9!MfF]i8^,}:jUF-V{r%56+P^&0bKye4/s=YMsp&_<L8mQqE=d?k_^T#ev","6iBK/*EiM`O,&pD9?=&#n-L'<nv0G*E!V,6QW],HUg5@Q)}<!!m#[DinzV7eIdtL",".=PL!M/>b{H^hTm(:R_O/te)`3Eub)p|wl':/M1f/%L$#'-$0R:C%Z/RTeuUn6?S","SW^%?XwoD7OYA0:&K2Z=zco9Jjtz_HUHx!U11oD^e@@QbdAV^c>]XjOg}|%xS!W.","e--=2Aq5KI9P90&!w&*II-T!y;a'pMgA!U!8H]_tY#$[C/HrDBL^`RO'Y+n#.B,W","t3jh_#eKt}'};}]z4l}-DrlB<8j[eqV(h0g_cmIg}I.5n2xPj*6z&@gQQv_n3?cy","<fxR.S*<P5ad7/]gKm/bTm/HX_wCCR=z7]DJy.|zk|M=;DOMAo4BZlmk)g8W"],
  w 55 37 100 1280391 1280768 33 1202 payload22,
  w 55 36 0 1290000 1290393 100 3164 ["{xxA$wQh{b_1UOZY?22g48ot2;/&@*W5rCG_BLK[~.GR2$1hZ6lSme6,ultsuP!^","5~r*K:4gpN*Y1xrl?)-dV+0='>PAQ=XL01zo`>A1$.&FEFH1~N(Ey-]Q:hnOK9ga","e&Z<gO]=vUTT3Sa?eC_X}hGe=@:;nmpdpiTPY1)MbGQaEEVKw-1wQV`*@OU`/X0@","ueVK7F.@MNtYx]uwVJ`oG;J63-S?F_y.=)u0Lg=dAC5Js%@3b^S5Gpa}3CUJf+qF","0O{B@;LF1(bBE*1*%S>$cOXi_lqpE%ViiX]PA?t#cq?rF/`:GeZ<6aCv7OhZde!c","RhW1k*1sBaz+Zl$a[KVG&c2N'aoPGsf#*@%PKS=n_z~S>MJr#0j$n,GrL$vVWX>p","#'r,Al*QpKkt]n,,aGZZ@=fl745j?SArU'SQ;Ysx}bfUN%#<Kfp{^!?^*$>J%."],
  w 55 36 100 1290448 1290768 27 960 payload1]

private def r55_13 : List (Chunk 55) := [
  w 55 35 0 1300000 1300451 100 3019 ["QjP,A/5Z#f*s{STe$YRRPG:_krk-1u6b6K1%(H2EtDSR%_=$m|~Cw_!HXZ+C2Mbj","X.O,RTYMk.>/0W!4aevNda1pB7_A=#%#v>pin&wmgvc[(5w/pE#EsK,pzS7NhqmD","r&1nH}yG>lAC8?.8iN5E;C'/l}8Q3k/Zx@w0z{?*)#^{D8YA4q4XOr<o50@TI85x","y9ou%^QcRo,:~4uOg$8KVgaLx:.YKocS9d;V05ZJL!ccr?0HFE/Iu];ovJJx!KlK","?ad7p?$?N*WcF=*%0*d32_5b|f7Kf!1RmQ*,S^?$RS$KCMVU=,:5*=R^@^5HpPWZ","@FI~zDT#IC3Sf=!>;;c?3#CM#)%Ss-'/a;[~Yd2zk;Wu.aO>+t/k_|V)U=y=')xE","=Sfhlfx#L?+7YLVsN*_E@m.96t}AqK38v8C`J*u&yb;P:)b#2z&3GUJBD^oFYb"],
  w 55 35 100 1300452 1300705 20 693 payload3,
  w 55 34 0 1310000 1310454 100 2883 ["'QB`*M(5k0?7X,-Oe[a+FYZ%:n<ca}>=aOpD27~NC1N$G[XcEICv}wWy]4+~=s+A","mC)CJSz(7?Ykmhga7Yvmpyz|PGKKbZ4!!)T4P~q`*H75uR2~Qz^!%dO|8@GC8O3j","B{TW4C)z)}{p_]gPq7#NMI;(G6$cT(,AEn,hlPXaLJKV:HmJiV($X7*YbF*X{=v;","WQ@9*AP(yO7icdOY_6C6Fi1Dph=CV9zxnp)Tp`9OX1lB}}fHP$<KrT&?C{`U#N<9","|aY68.T-WX}Q(3Hude(W]{,InovGZc{,~POo77b&V2gT_NfV-[).~b`oH4s<tGN:","Jzl(j8%z(l$.6%hT0h[AECL4*=J;StDl.W6?6cFAg$$*LtJm$RI;Kv-*ZNrY%g^.","JmlVG6e@:OVkZ[<Rl^b;:&k~(9b!UO%1k|XF*IJtY&u.Q&-_dcyWLSDzbLTK#&!/","h"],
  w 55 34 100 1310512 1310704 14 475 payload14]

private def r55_14 : List (Chunk 55) := [
  w 55 33 0 1320000 1320515 100 2767 ["|?m`9$qhIP0UqK6m~*B^Rcb=}^oLC=Koq1j.~:`Z56G-Z<f0I}WEo%`;FW<SeEHf","8{2;Vs&dwgACG,W0KC0iq2]p!w9v^xL]Er0i[q016J#0Xdoha91GgP$V].P0B?8c","0{_zHoaxp8*c$27U3D`,DwjUM%@lJ%0E:-D(Q<?@k,YRA'|s[OQa}gn.QCWm_5.v","`AIm%}y`xtV(Fp4C)mX9SaAnz8X`7wmuVWyKJ2H4yMbY|eJ_~%Q9&EGYzfp&t3B^","f0/V>Er2w-NU3L]2O^,ql}2@{1+VWO%BSMq=&%zw|Q^Ld4*4rJ4}wFN2'_B[XJ)/","N_&7+l1vf+#]j2Gz^Ne_j&KlJ^T79<QW-w<N-;lo/eof]V3+wwAOUtXd?[6efYSX","Utez.>>Y1Y@f+US!Rh~tyKN8a+pfJA}QN?-W;bLp-|'xTkM_w>OhvB{&en1xnh,@","3p["],
  w 55 33 100 1320516 1320704 8 267 payload4,
  w 55 32 0 1330000 1330578 100 2661 ["@u*S4NPf7Ks[egVY(Q@cpzJGXSfcoGq){d^@l*>d<Zs^KKBG*i/cAL^u,xL_16[A","F1QiP).udcfQFWU1k33ADp=s*cN2bx/6#V8*z=82w4;KaCTwMp%Px4~xMi5hCk6-","gE^0i/G2i&1sUE'tV29HY9ph]?O<GckgAO[hDrAJUF]/JGN>sLlC]%2Kuc1'a#9W","`x@OcjDIz|1{yqD^)uG>Yd'Z$N)i5S_)O[3c(:5UMDe57fjwey*L(|L&`wn@0lu#","-Wm!+9$cq%<K4H?2&Gw=uykfJcJKBf%M6&h(X5*58a;5y6I*ti]szqr?`cC9Wzn#","v)u&g~jEh.<^VU&a*ZbB%b415<BjDF)>h0D+Opt6_dJ?CpKegz3*$^v|Jwq0-qSQ","M?U]W)TD,V?e0ToFJzItSNe0]Ql0G2H3GKY:dQy(FLTLM(T/!r+pGsZx9:{*Ypr5","::BF_"],
  w 55 32 100 1330640 1330641 2 66 ["#i2GG<Je"]]

private def r55_15 : List (Chunk 55) := [
  w 55 31 0 1340000 1340640 96 2445 ["sQOO+~Ci[tT-q2@I]cyaT!zT~Jz`,{]!z7hONK$)?su5k}N;J#ljecM}yPgpayWQ","N9y2L3gvLtIk[i)&JOPZKSv@2`$7Ty'Q=_T55GL#W)^:!V2{pzg`6LBNekg9g`]X","lW:lG3$L(dy{Yb>r={R`p@932:*Ve_d7/3ii-R._po9ogv&kG_t$aQ@Vt>@-c3ch",">w(fFbNTE/fogsOOE^/e8rW3XbIf^SK@;$2GI/7q0;3Abuf}MY}OO0OC'9<B'h=G","<teQF?4#beP+Gw(n#d<E9`|hbd9n[1)4.'l-9djAbGo`k#-FyDWawAbPO@3q}|7G","]')q{;kAzl4bCp/E('p#'G~QAw5#[m>[OU?Df;b?D1o.i+sK!bPqN$+1B)x})P=S","-05NUl,hn:W/qoS9S`X=]4^#nFz>N|8^7oyjE9/GNf~HT8>C!E%_FU"],
  w 55 30 0 1350000 1350640 91 2209 [":$e{FsSO:bq_EvS]p(7Fw}4iA;gthl)i0eW`.h|).iF^xQGZLwhWk7Lbtf,Dw.wM","OYB*e#$4fd:{PsDb5X`_,EYydhe/QeTTDYH|tW(1jxel6>3,V@a]tW/{/w<r/>Rn","J]7~skZj(&w|=]j+n;@J.3PbN0.3?Q@%K:h{1_Wzlc%.2T!iw:hR?b9,$xpd]V.X","Jz&IObF.9ck4uY&b!g-O'(%D)JCA2O2y0qM53-[&P&T1/F:K=x^$}FqB&L*R?hUy","z9CnEaFvoBfG*Z+%%Sb)@~yJomjH#b%(<IR0hPO7RA(QKZj(t&JhE6jZ9Q3;Az#e","330|iP&]=e;]&C+fE8xD/ns(WZv2.!AP-bLV9/K$YK#suF)y;wi%pZWN@.-Z!7k?","7JQ6u?fGBVk8`V`@uU^zcm?)&fdbxQ*l"],
  w 55 29 0 1360000 1360577 85 1962 ["t8~y9n|!:N<_u47Za1&Q,f6u9a!)L6oovIn&7bssy/]J)H6fJ.&Kz6$>>zrJEKWb","';xHPXSE,<uCE{$O6=05iT$vErgf;;Vl~K]huyQ6)rIVMQ.eK&vXD#:v70jcWG?I","wn.&[I8IM[kWf8I=5?zSbbVR|exSZXQ<i^NfHjM+vOIDsBX(2FB#.+4;F]g7(Y`=","yxyM'Fsnljk9`B1v7)AJR&0$yhjV]G@n?F'H1u*PUu)Tk9PxL)Z]'XAiI%p?Fe0L",">1dZwrebxxsz?T{G)Y!A%^VQiLto;65n^78~H(Z6-bL'VuG+.0*_-D31K=RiPu*R","|0pV[pM`>,s_-la/3}CYCrIyG93'(RO;p+yy%$3TVO:$lyB&$e3O_1L;m2dk:?nX","/7CEU#8Gn#"],
  w 55 28 0 1370000 1370576 80 1755 ["u-HQdw(i[6MQlU&c>F+3G96)9!;<fl~l{ZYnYO,[(oei1Utp2xWqtfBj`z5rnWj(","~`19vRG(2qHn@H/XB#E71maNQR<Yrq$I.cujyW;F|>6A3;NRa3:B.MYf3ac#GC>t","Km<M{u[B,Y_0DQ8l(0yU0nsITcDF5=Ne)oz~fn_UQq!fFLn5gi>MB/&:o`90iiF?","lDtZ8#iK56%8H~+nSgsk5S,#aN}l/;/w+*zZfFVs[bVxJ:]+G`=JyEEtCi}Kk<i?","og.Vjj#Kx[sn/)SZUt;EfAXVRkMu3{&mTp3~9?n<H~%|9D4ej4tOv$}/$V=5jgJt","-IHngra#~MtSHMgw{63R]3'}tc=bTF9}4;+}&,X?g'2g9=;1a@Das"]]

private def r55_16 : List (Chunk 55) := [
  w 55 27 0 1380000 1380576 75 1565 ["n'7!ssDy=](=S+E._{]9|<M^+.=6^eH6Xmq*pxW(SZ#.@GT'c}yS*Obon;o^uPuM","m<J-O)+O-:cQ&T:?}-3^b_#THd)iU-/D/zv/^q~c~U-{LQ*C1i7N:H-(HoW4XKBB","KV'A*%jasSZ/GYBLgF*DGT?F};-R[IQYZ3((Z=an+Q[(<a+(gvB!<pD!hinFhWWS","QY7oxOFHrC[L)!P[i2$+XtiB&%ortD3vxq1{?W],_D6J2}!@o|x'{bqhSA3t.y/F","5KJ8FrKd5~#,lYI(K8)=1O_v9s'0R>>dVy/N.?+hAk#7S&DW%DYeV1$`].RTa`Un","Bw+RqW;9`QekDp{#0`lT{MtqkD(@qHT`mO"],
  w 55 26 0 1390000 1390513 70 1380 ["e>x-m>Va/83=:Z)OM0W|fO+fLzQ;4=t._Px<03wR|.25-5(s4g^Vqv3V76.T2+UA","R[(wjs}zs*4l(o1P;(Wrf+NW!^OsltyMTwzV~*1PwYy)?vd>:o@L~mUV%6CnK[(H","4V3}!{4/H-6nhRN],oEf0j'7Ud1TsD&F|k(k;ARhO}-_dqva:HKKA`M0qyS^bY{)",",LNjM'[S+xDV|[pRDj|pn*#N(!gSu-jwq&$lm;uLX&-Qi)70f9r9p;s/M{ZqGr%0","I)sfh>3_9Fs#+<XZoKR'zpOPl7*SV$|jI:!NImHR+%m$om{Ui]Oo2fmYFVv>3,tC","#Niax1ukGb+@E?@ES"],
  w 55 25 0 1400000 1400512 65 1210 ["i?Lyfh>-?CE<a%d]T:|N!Twdn,i$KKO.rva$![|Qs&}XL7m.d[z+S52#V[x:Dsa^","ByNE-V2--)$foC#rIO&'cB_f,clV>-V@l3S(>7i.u..w|=5T;VLLcEBUe_]{5%^u","7[9ZeP@(u:F.2/z*zhb;U'-Sz#xJvyhp=}3L6~*Rwp,GU@huh9^wq}/y0T;gU{$`","W;Y_)7K^R)(fm3J8*COyEAl+pE5,lAA9@tOpGSMhQcr^|x_@Q{kU^W]u.n-%h4Rq","[2nwp2*IRTS}c4y8P1o[^gU=+dP|<VU{4@r3b9*iIx5`W9MWX|0Gex_8*2vh&"],
  w 55 24 0 1410000 1410512 61 1069 ["_'j}AzB:.Bg?9rY)J#pa@67C.wtyAG~;LG7^MW46uJYx1xEM%'Im)G~al.}vTt+Y","fithPB3Z<R#K37vG^Y=/Nt]9%L,11(W4lT/r,|^6$a=q}|LqUVKm#e^V+M*VOC8p",",Cla{:Y>Q(_`og*Sr'H+dxcDtAHTp1,d]~A~-v:2]Q?FOSv|B]wYg4UBY;M.h.3=","@ZxeJ1<D1~Lcl#9bFy_/}8X_uGZ2x1,zP19P*~'!c^5l~n'pY@g)Q(7Z;nCY{5;1","@QC8C@9fdr=3h!/<Wwh,^>zsoF<4Bu3'@#,_Ui/w%cz2*"]]

private def r55_17 : List (Chunk 55) := [
  w 55 23 0 1420000 1420449 56 918 ["n?8urGW>.!93s>4~Lk$w-lC_-,i+;euQ'g*A;Kn[&p9JRnW(L{GEf=f75Di+{~R5","$vVY&DOk7vEC-})aC??UUs/NQKD#q0j(#Kq#Y-6J5HzVVWXw&;h-[b=Ci;t!tYf]","354?Y+tE7=.YVU,ol*vqDEOh'Ak][#XfcRfkO5ueq[Yj,y>`KoS6`5X-G_/-DuHr",";tA9*V#vf;1'-H^A/rVtr/0Al^Uw]qRgv,8f`eU_G{PI1N_j3m/bhJ'/0N:%pb:z","7Dl(uFZ5umL7Onww=8jg$ks&"],
  w 55 22 0 1430000 1430448 52 794 ["sJ3uf~a+3Kfz5V=?N;k>VGK[~ju~S.mp)/1EP)O(@6%/+,v8Vbrv]V**i`g0hfNf","nzDbLT50M8hD[-b3s>Ut^'hlA8$fQ&VQ2_ph,:[iJ~du.bw^:a70ahveJYaq,Lo_","nJeW:foMFr5|z.mc]DP2c!VIqIihkrvF}Pm~/:<AjA_AU-H<Xd6VF-WuFc?'{1vw","bnS)/u!iUBt!E7'o;lE}C3i6q=rAok$:|-Sw|Ev=Wf|mi4zNBG#z)E1;dIw5,E`*","*_/F0W?"],
  w 55 21 0 1440000 1440448 48 682 ["+38z-:VtsqGf~T/Gv`X!w_/s/b:Yw=nT>`r5<_0fnc97m)?+<},fP'u[stY^KH{f","PWgm^p;)m2*}2u7C)?s|:cqwNv$P@XZ3B<hnWaE0[u)vCG(.NMV.;*ig^JG''Qtg","k,)MRdPe3<l{O-RQjJ!*D'v}kD9H0gzJ]jqdx2I6vWO-RJ'nIkZ7,{fbeQ=5X+R.","#AdhMF_NIK%163z:w9Tm-_;o*sX[5l`_4ua}T(,0}9<LdFafjRw"],
  w 55 20 0 1450000 1450385 44 574 ["uO$VMt,en13w85Y[~Qf-$P>,Lx<:PsrR=rk`-<'nb*?[3HcaN~&cS)qb4ghFXYc5","sk-nx+N2B{LsC'}4K+@dq6g>|MNTwDB)E(>w[#V6r(U@y|2*wo1mVKe!'!@Cx_[@","+ASd+4s|W)jf,[)aMc-)7.:z>1Dhw3=iG&%X;g|AZDz)nILD+zgxR=t4k)aG,{zz","WLp:y)k^;yS?ALUMjV$DH2z>`SQadBp#"]]

private def r55_18 : List (Chunk 55) := [
  w 55 19 0 1460000 1460384 40 478 ["W1@Gq);L!V[>u%zB;zCPL4ATan}!XhVBCFTfF;{Df65qbaiz@3d<^3|7N*~v<R9b","iv/X.udVFFD<:l)8qcPC&EtN(M_-QkS<r9v5-&])T1_]Y%!=lWOomAgtl7p)^#gg","CPJea1E*dcWf;/IR}taLB&A}yT@v'v,KtF4$Ov?)t6c*bt^3c]PgZoVd`r1pn<bY","'jTjdXJfkUB"],
  w 55 18 0 1470000 1470384 37 402 ["*WGK9Z=[}).{l*@r4UdFc#RnYLiC#['8]hFPD&Fo(KW4wO9PhWE_'V#i_(+'k,a=","D%v)*)^&v<[7g`Ym$^?niYRcr*cMaZ5>utZ$>;9I)u7Dvuc?1{Og3h,U#&aAh>J)","Kv*#*UE<-qW?@kXi3{'~AO:@4JEX,xiz-iYxg;+Clw3]qpB/,zky@DPRws"],
  w 55 17 0 1480000 1480321 33 321 ["BLmXIL`$*QN;acw-1#.DHKzgS*r6;@FAJrqR]Ko7OV->;KHOV<oRQq4?lEK-#bZU","HL9<m<kg;p$.AMTqV8eE-&wGj25~yr!$`vMvVzRA<X&-HyVfliHNOSd_ixv/bsSk","$0Xni<{CG#jdb}:|1skQn7I{kFdrn=*l5thFEr"],
  w 55 16 0 1490000 1490320 30 258 ["Zf>`|Tyc{;/r=jNFf_nJg8u.FYu,a@s.Tv8$}6U%9r;3$bP3(yi^LyqhUZwVt}Jf",">ZKP_@)!^d%^Wk`yoQwu*pi=`@+?EfoW-d%=QaZlmFU}40g[)$m+NB$G-ykBH)!G","$B^4|PPA]U5eWEFM@>*n/^!["]]

private def r55_19 : List (Chunk 55) := [
  w 55 15 0 1500000 1500320 27 204 ["pqsJrZ/):e7Pmcd;K-S$e(m1[QNv;gjHo_@W!Z5_@g*rp#C=TnPh<k*DSTV^`0Ab","+V2u24:Og~$.KY#(OxX(]v=IPL?V|T9zH|yTlAJ~tFn9gT@W3S?C3%?(V@RWHMIU","#/cF/Js"],
  w 55 14 0 1510000 1510257 24 153 ["16{hT&^{z<0_FgoLVsCarm@7uZ=rTdCE)rJ>am%z!RN%nT+nOw|E%q_WWtn6!)}^","U%421*Q3i2sS5kp];!DA<OK1O3C?~3p/oy?k8N>q|Yxg}.wSyspmLL`JH"],
  w 55 13 0 1520000 1520256 21 111 ["y:IDna;J/Ic_!L8)}5uEtm)9Rp>6R][ioXDMLwcDbx$;`_Xj>8oGt?~W1iZuQqh9",")3cPE*cX1m8hVIf(~Ka>.wL]ZIM2rJ|FT8xEYrOsp"],
  w 55 12 0 1530000 1530256 19 80 ["WXm3F3{EUW+J{'8g?3W,D&e<yUJ+>8<z?f]l@|ArYlh7xf:{V6zF}^ryA7]<U;>E","Gw!Zd%K1MSg}vXhe6F9m,UNv#=3$NNr"]]

private def r55_20 : List (Chunk 55) := [
  w 55 11 0 1540000 1540193 16 49 ["O)49g]7'G1f;F[HTZVK=nP/^ruk`!OeXY&ZmrI,|b|z#?&kT[1BnLLtL+B%8ZLd)","$5*R1j>0|)b2V8L^"],
  w 55 10 0 1550000 1550192 14 27 ["nfBcGM.et]u1L6J0L)szj<YgYAd}5L_}!UW/vCYl@Jl?Cg:|Zsa6IB0~-&Y<AU_%","%.xYw[G"],
  w 55 9 0 1560000 1560192 12 11 ["$;Z95qhIk[l1-1>O,p%m:MgZIWs_'t+&-*nNnt,1Fk!*k{dTVB`KJ|i'1^A"],
  w 55 8 0 1570000 1570129 10 2 ["#9So/+!w+{y`};2P<lH(I&{~;4~QkKa=l%UE!k2N2&f_O$9+(@="]]

private def r55_21 : List (Chunk 55) := [
  w 55 7 0 1580000 1580128 8 0 ["77bymfU;9PTzNpwu2=1Vj}4BS}([a.F[GbPg:u-"],
  w 55 6 0 1590000 1590128 7 0 ["#l!&W3Rjbx,;%1Fr]<v)DM!!pH&=v0N.^91"],
  w 55 5 0 1600000 1600065 5 0 ["-'wx}<Hhrr'?)?wiv3|{#kun"],
  w 55 4 0 1610000 1610064 4 0 [")Dd4QP5CY/+/{E!J`0M"]]

private def r55_22 : List (Chunk 55) := [
  w 55 3 0 1620000 1620064 3 0 [")o76Zu3l^{3H"],
  w 55 2 0 1630000 1630001 2 0 ["&k84+EV(~"],
  w 55 1 0 1640000 1640000 1 0 ["%PSi"],
  w 55 0 0 1650000 1650000 1 0 ["%!?y"]]
private def chunks55:List (Chunk 55):=r55_0 ++ r55_1 ++ r55_2 ++ r55_3 ++ r55_4 ++ r55_5 ++ r55_6 ++ r55_7 ++ r55_8 ++ r55_9 ++ r55_10 ++ r55_11 ++ r55_12 ++ r55_13 ++ r55_14 ++ r55_15 ++ r55_16 ++ r55_17 ++ r55_18 ++ r55_19 ++ r55_20 ++ r55_21 ++ r55_22
def rows55:=rowsFrom chunks55

theorem good55 : ∀ r ∈ rows55,good 55 r=true:=rowsFrom_good chunks55

theorem sorted55 : rows55.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks55 0 (by decide +kernel)).1

theorem mass55 (i : Fin 57) :
    bandCount 55 (i.val:ℤ) 56 14≤(rows55.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks55).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 55 (j:ℤ) 56 14≤mass j chunks55))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total55 : (rows55.map (price 55)).sum = 311354 :=
  (total_eq chunks55).trans (by decide +kernel)



private def r56_0 : List (Chunk 56) := [
  w 56 56 0 1120000 1120209 100 344940 [],
  w 56 56 100 1120210 1120523 100 308460 [],
  w 56 56 200 1120524 1120903 74 197880 [],
  w 56 55 0 1130000 1130211 100 321660 ["TvNJ{WGH[>Y@GDb@MWj!8XkMO]i2R}W}YTfVp`lN69!]9}{x,YtO=H!DgH;[`vPd","n`Nw,ih-O;rs^k=t1UMDz8#7-b.X(1^b6C0$p'6%dOa5[gzEWa;j6[1m_sqX)yKT","#Nx)'z?L4|^,y!>0A~4QEGy(|[e^E1lv:-h]0,39."]]

private def r56_1 : List (Chunk 56) := [
  w 56 55 100 1130212 1130527 100 284520 payload0,
  w 56 55 200 1130576 1130902 66 163260 ["S<F1vgOE{'nSHp6[|7}a1)<b08XNTrzR'F;wc7k@03sz`#7c)}e>,ah6g[NdtU,S",";F$3;XMpg{FT/>H7#}M!L,gw'2/v@=T[&C'TUcA?~uHZUl}"],
  w 56 54 0 1140000 1140212 100 298440 ["x5kyO[h:t=t)B!U[2<Ea-[r3G?PjHyq|mL/5Fs-F3U''r~A~M=$-4OiN,hM}wzp?","ri)6jq7NByI%*t&`7`co?Psvp!05Lq<8QHQFw)v@U>&Jcqlr_fyrtA_*T.klvhQn",")O'y,6{?Q;SaV~@lk&0}]?vr.xXc&B8Gi7*~kVcpJis0^(/D"],
  w 56 54 100 1140213 1140579 100 263820 payload23]

private def r56_2 : List (Chunk 56) := [
  w 56 54 200 1140580 1140902 59 132690 payload21,
  w 56 53 0 1150000 1150214 100 275700 ["N`7/N9AV*fAW9CF`bBMh,e5.bR2(fW_9K{n9~?<yCM'*=8kTG<o<TM@/[mSm^'cK","G*j?/fuh(Fh4acq,CchqjI<K-HJVrh0I:0DCf;E&+,_b?0o:/M!19|N?:ty>e<x(","&rCE)K)NMcjyg9pN.7>{a]icXB0*pBF-G_WGXs<'aV^;o!ApO1h7Iy<NrS01Y!i"],
  w 56 53 100 1150256 1150584 100 242400 payload12,
  w 56 53 200 1150585 1150901 51 104970 payload5]

private def r56_3 : List (Chunk 56) := [
  w 56 52 0 1160000 1160257 100 255420 ["LE|0!{AfT*;u5ZQVWm!{;?GKxU>rc0[8]A^&#qfY!9bpEFwfIL;ZudaN,80#eM!+","sVl%$Kwo,3{%d*C?{e_T<%xe'&bM?]=5.Hej7:Jc:gzc|-IHU2B~*cFR``^GY~:r","oTDpXw]C'hcx-rD/lc8[u[.V(mOaIl/e$FQu|CE1,4^R/aL}e}ipJM**Q|#~Z5nf","7#TWNWV?JpF"],
  w 56 52 100 1160258 1160588 100 218880 payload25,
  w 56 52 200 1160640 1160901 44 83760 payload29,
  w 56 51 0 1170000 1170259 100 235140 ["hyooSRrmBQy6F8i3apj,AN`o+RnSJFLZ#y{k3X,}j|`Fv/c}Hi^pGd`6*T'WAYh`","C@%x<mkE#k^dqG|C54S7mpYf->`k9mE%(ltB35q{EZn,ZAU$:^63AZw6'(k?D?ej",">~!cq?fK]yM%AnN@,9@;0y`y^;F`#.%~:sg>Fm9|5(oca.R.(N={I3H{22r)6)dh","w^wsALTK>G=Yh.SLG=aJC,~"]]

private def r56_4 : List (Chunk 56) := [
  w 56 51 100 1170260 1170644 100 197769 payload15,
  w 56 51 200 1170645 1170900 36 62791 payload24,
  w 56 50 0 1180000 1180261 100 214983 ["+G03SUIXt}e+[IHHn~yFfu'Aq#Dxh|OvI=ouy$PKw#XO%nsIcd<BV1FZXB3Vop.;","F9>{D,r1Y3kOpNFTp&+1+C_ArE+QF3)K&,tO!>#vmZ7cVxEc{0cZV!>74FFn&f0m","98N0em?R@w6)ebd_-E`ftsW%nq(c-}40(d?[:bqc?:XPa&vu@cbR$O7S!IIW^Esk","%WL2W=FdskQ8Wl:$w`MPYeiI@Zdrp4`#?1ZY"],
  w 56 50 100 1180262 1180649 100 178014 payload16]

private def r56_5 : List (Chunk 56) := [
  w 56 50 200 1180650 1180900 29 46978 payload13,
  w 56 49 0 1190000 1190263 100 194911 ["Hsgl{PLjk,.5^:j!CHoX^<<65n[<=wEwYVSbuJ{z!7pJ8B(Yz%o<^+`kp<,]I@_+","'x#$t|^{JN]zCdH.&FhZEee:HT_'I`m1o)PN:jE3[WQ6uw]x>y$#y%@fBX(ZHG9z","hCgR6R~wv{K%RiPzfjnKu%t5A^r7h0O0_KF^}3]M$Mc*U`D=1lW,bPPUp[+a~Nk`","/YCy]B5K'p'3r$?@`6YhC!Y1>o'`i-+:607(.9(y%Xl(cu-/"],
  w 56 49 100 1190264 1190708 100 161014 payload8,
  w 56 49 200 1190709 1190899 21 31466 payload20]

private def r56_6 : List (Chunk 56) := [
  w 56 48 0 1200000 1200265 100 175542 ["~MPyQ%4>b[Cr[#$>G5x|y]B{2zm^eHA25FFfjWQ?w)(H7mmhT6>OT!G`XrqtP,8S","5a&QXD)nTs97vbp`n_n,j^XG%*DX:|%%{XnU4{,m!-8pVj[{4.KR)v$r:~ioxPSL","gVwk}NEQ8Yn5p^Q?xO|0PFXW;e<!;J1/J#55S-_Q5M![y*G>'[e#Pf)-R,T*D(mE","+'|UbKXnoUhc$b8=4q32X!A'3^ZR7=_pj0dOQ_x/}%_N@{R=>U5CI[@A%tYim(3-"],
  w 56 48 100 1200266 1200769 100 146108 payload18,
  w 56 48 200 1200770 1200899 14 19830 payload11,
  w 56 47 0 1210000 1210267 100 157353 ["E<^0OeW:A)Yo6UK<'!n,Gic}L<&-yds*<xZV_U,cHveS{.=zmwyA.j?o9Aiu1.p/","YKTTa;Q<[hx&-f@>w?]>s%S%mHKwTCUmvE.TQ8m4aP3'7]E3NLL}~B:zw5N9Rce+","bXq.C>YRJy(+.'@M)Yb_9ixk<g8I{%-W`SWvWq)OxcwlvrnPrd}:,6mkIP50(2=.","t~WT[[R{KWt.e*M9!F$@BIX]j^r=QaTT842/%5k0TT=ulm#+!aqTs(@(ws>Hsm$7","%/1F0Pio'-JTu_S)BbNU!"]]

private def r56_7 : List (Chunk 56) := [
  w 56 47 100 1210268 1210833 100 133272 payload26,
  w 56 47 200 1210834 1210898 6 8270 ["''*<pfK*jt/{_+Rwy>&v"],
  w 56 46 0 1220000 1220269 100 140641 ["JRsZ{9.N`>y(5(yiy_,}Qx$%qLas<%>;~I8XD^1%b]dXJ*>%/pmb~8_xqltgrfBl","K|-dO_EU47n{u*K>}b^D15+(!W<WL80<0m&UL#Cc<avGXhnEFI]3%}*#~bCyZ4~K","ne~UgE.O2]h$L49rxHgL{a>LpzEXu/a4%5MQraKO:Nt:NRmm4qxPWva!~$>IRZ~x","SN)zFCP-s!B|:v?fx..ZgC,H-W?9vqvxQCLlup1Fp`HGS0q:ZLgff0`dl3T@H.bF","s5Pu8ihmRzmj;8]B9Jf1@g:JNqX2z({Ax]$GQ0WiF"],
  w 56 46 100 1220270 1220898 99 121760 payload27]

private def r56_8 : List (Chunk 56) := [
  w 56 45 0 1230000 1230271 100 125638 ["-DV{)XJL<Zmy8Qq5L}12N9ccu#`B2u5h9{)w<LZ.X}E`WJr2d~vlIUAFu_>S0(HS","0Tu@mP=[=PN7lMOGDKuc}y`nXdU(f=_4ge]a{MHgju8NWOgHl01>f!@zQQ5NH$cg","bU:)#o/Ee_}fAEwC!~S[4*BZlSspwLq|zrW[eME[B^g<d_7}KF%skc7!<%:3|=+#","<!ESu0;st*#{*~sLAQ)g+N7aBBb{,Jj-KfsH(>%4FI#B_ty(L[aFg~ra@jT_N=b0","K6Lw^6YF}M(!'@J:zQpxRtf>3(|Xp|G5ra]e+qa-~H#kfR1@+}l1O1YbZdf)(&mT","Mbol"],
  w 56 45 100 1230272 1230897 91 103294 payload9,
  w 56 44 0 1240000 1240320 100 112633 ["YlL8$.poiC}{l#WSs4q>aoNe:{r0>.)Cl)P%*)W2?STU3#9G;un^eA>Ha,%BqQ{K","0SS^v-EikQBqyrGcbs9j/k@6];z;<&ga%LEG%6e,a!8x0y]$1t-_M@D-p%@W*hOt","GjYO;w!FRu^!rIh&`(gv}|y'NK-}5MQQmSRV:D42B1'sWEsp%ZwyzA|mm1GEw.}B","A0']QhM!zYTLUxTqT!=)=t8B>XF}jx}vDu<ecX&DjsRdV_(#>ffi|[2vL^igCFWC","wAr!FS^kBVONm|;i+k51w,vP20`,)2O(Z/AMlQ<FE_0!m2QenUsZjUN,LB{wx[I6",")cw'[YYA<Su#bFE>PL7JQ~igW1h24{4;q"],
  w 56 44 100 1240321 1240897 84 87969 payload7]

private def r56_9 : List (Chunk 56) := [
  w 56 43 0 1250000 1250323 100 101392 ["8G/A5A7!A-YnH=]p]jS'^0{51;k3.Ujq(_X;b^ArRuA,5N~CI4SK}x0YwE%sxF{;",";Y45BP|Q4FM}x>He_.Uryp{oDmZy#O)h9~a[byWADQl+=j}7>~}KO,1y8jR&[-3G","QoS/k:%,j^7mlSWhKyW'hAk;@^i>9Cq9)F#7`xg%XWw7cR&0y)sXt?}0G5Vo%!/b","/9*no/GM&*.q{T6=DZHCgURy}YTsgtmE7:L)lCQ)@C;X;Y>S$|f)+T7iauXavW;@","u^P8=LsT$:Oy(J$AS%zmLmOCc+cjw14ThK,KcMB?$Pi~d45I=<MRt9+OiRRkR[7@","knw'5%S!u=3K&'-(]sVYFfow$xhi)m|S4*`Ie/%uc(7E1uY$,L'VboVXxPUV56$J","*a"],
  w 56 43 100 1250324 1250896 76 73235 payload2,
  w 56 42 0 1260000 1260325 100 91283 ["6HCnIHN&Cu:f6ZOis_e*`i,_vDJ%:h+/lt;E6A{>AwxwNZW$_C8jwXgb7C=eCJF+","4mTn;dxo0<SE/h]K7/5,r:EgsaqDZNOOq~%Hj/l3wZ;(&5Y?FL/{JjL!e*Z<H>NO","s6n<4}wVm{s6*:?)7qZ19)oT3YX(fUOvrGT3DIxa=7DW=aOQ(1yj@x?RF@h=t?!S","FR}b@Zrk3SFtMa'+h,>(I:v=+}O*.WwKlbi4ue^i+ni8&f*=JdcrU]U&[fm`,ABU","is,R+wMpjqtr%Z}zm%J!wct{QK~EYa#{HwuLIfUoC?Qo5xC|-#*Vro4a)FLr&MOT","=M[!:@k`e>{8lvxkE';I[v!(sDdgC+=_P&gzU$#nXs@Zf]>6>8x^:Sj:g5>CKkIH","9?0AM}nk^V6'Zb;JG2C2IRw>s"],
  w 56 42 100 1260326 1260896 69 61501 payload10]

private def r56_10 : List (Chunk 56) := [
  w 56 41 0 1270000 1270328 100 82208 ["Y9zF)&}5U|?57Z:nv{HKl~RH2MK.$EA~8G(v9/L<>l0e`={:>W|@bc?DJi606/>]","bf:Ng>nLs0;E=&6/Y}^-gj`=ZAt'VrM4YBhN,D=MNYQ]Y3;8V-_]G?_%Ohau0*rm","a{m1jM2f;#`n(r0:|NY5/!l,S2ukG.&K{Bg8Dhu;%P7cq'|-]m>0=[$z#2w8d!gQ","iQAQ(&6[YH{?xvB:5k[@45XFa)~PQz^xfFG4]xo^v|Zuv',p{$T,c~S(|,T,DTNb","[oZIr5=ZGP9u.S/,p/oK,Dp~*LAMZ+S3-_d_~Fu:e>&.1M'CM@e_Z/bm9B8Cq=/#","G!c`x;Ri_,u5z$-XM`XxHGDs2f#_/)cYOvJjS0BYKK!F*WeShDTCx:m9'Q=Qj|;.","?l?Xt_o~-*z7fo}Oih0wmS<d9Bt7[6dq-^.+W/[U'0EM8tkX"],
  w 56 41 100 1270329 1270833 61 50467 payload6,
  w 56 40 0 1280000 1280330 100 73807 ["Wt[F%+z.H}YyNk5&nZm)gP#<2JCRs<;mxl}&gZE08#-ULzD@~I'nj^AHt$KZ[mXu","*bbRUJ8b_NUdoM4Xn;BX<]$fkfW!:dq*BA838._$e&|V*=NbU|_hq<@@|8i83Y_i","]3ZdVLT1B,VDRDx?c_4,<!]i9n|H~j]GX{vdbcp#V+Z1e,A!J/&Oz|Ua!Vs%B_>r","iZ#jL?UB+)9^R(PmXr+)oD&KNj`)(Wb4d>o<?_8ADOiO,K3Sr>@DORJtt3;0cZ:F","ML%;J8Y8@bswsOIE)!@Ft{|D0j!^eP&8joGhG9h0o>1J}m%k4D#on7o6x39=j=6I","p>fUD2Dgq8]Fhoc~Os<Fdt/o9>gDWl`hxNyF`#Zc3w3B`:}copdAN!goVA$OL/]U",",M;0l{=s{5M*?T_}G,?@+]xz$=r_yJMPQv#HXY7j}q}R1Yh==zN$[=[("],
  w 56 40 100 1280331 1280832 54 41759 payload19]

private def r56_11 : List (Chunk 56) := [
  w 56 39 0 1290000 1290384 100 66433 ["EId78q}}r&jYn8DXBL53Rdh@x]{Oog>j:Y]O]Mq@K{(Yq#1_Djx;eLOGf7^[=3s,","6*~H1apuuipotsv)C`?w9Wx`<t,faO@0F]jY^F/x3Z)n11K^,9=p*@61*Xg`YR^t","n?fsK/Q/PLPl1Ioe|jM6w:=;`3NE(89]0<RZ[}Lm8jiX(Xg1K8lW4.Pf76{IJnVl","Mck6F{47l{V<Quip3nN)O,OsR?pq]p<9C4Kn5;f'J'`f.P&i='G:zjvZVl}x|o0s","J{:g]1R@RI5h{k!RZrI~b#i8&Ut./XicZ3gbXLx4dVG81wtS,e}6]nf}MAF'H.yq","`Fo:+et]Q#{g}@jgffyu!.RQv#vJaLq8t/s|!2n1F>n+xIfz/&<;,ASJeK_?*`mB","C'ho+N}*){p-t@aMa1hB)z*C7*n)MuKI}6S:ST8Xd/=(IH`F#vVdQ"],
  w 56 39 100 1290385 1290832 47 34056 payload28,
  w 56 38 0 1300000 1300387 100 59685 ["ad)ZA.)M+?B0'XQbKE-JF}26l4uq*((?9;+qgI3AsgXUil?!UjfMWV,bosJv_Z.m","CP|Ux1K?IAz3irt+T(l].L6G&Dz@]{?8T'#&7=S},Becg|Q.D.%NA^]#m{tp%}p~","?r2iSCO:uOr~oBs#g,MMv^|6Lf)KB7Cxuxg$[W@G2NL]8{(Sj0CjW?.#e'&;W%+.","zS#?A;,G.E@K_@p|<=Cm}N5%,1+gSC2Ko;6}r%K`JGoH+>{k[O@sn'ja;n<:Zkcz","w`J]OuY9hHSt`xq]%X*yblxxN0IqU2_mhG*W*x|h8PYEx'bS4V6LuV(Lj}<#GgCU","nlVz#c8=+w_>Y+)sN)_2iy,dC,I_?kkRTsHQOFh%}h`]1pXXgnxB6_#F6<u__;PS","$p375yN9#13i9HIpA?*]T@w~v:2s!(Vpn:%z7$,s->*<26heeY'Dk"],
  w 56 38 100 1300388 1300769 40 27245 payload17]

private def r56_12 : List (Chunk 56) := [
  w 56 37 0 1310000 1310390 100 53721 ["(=&oM(G>MCioc]myy=JH)]*.@ANBd{stAY4PH~jINS)yANNdo^)o(mC}.[Xoj,Te","k@deyZu~PLi+29wX'pXVX,oE162cYs1m~rTXT=Ej_@Mw{2Ln4~Mv;:yxw2c5f0(A","!X4Yt'*+SnuLqyR!%UFzJm)A`cdDt&<d1>2,RnagOZH#b^k:oS<i!Xu[/(/4__V.","rq/LS[BUl=.k)=wuoT3iHAb.%U_7pXyXr=rS*/teq1vFB3Y0Uf}MJ>U[3l=9FRDf","fKr>o6WM8dN5M36^X-S$Z<nys6(~^afG90Y[}?c<JKhrv>kDt$/oZl2j#&;;t>E<","A{#qt7,{j%dSRPM(ORKI)&I]Qsp.c!#-GPZ0iYqDhAm>J5|PQbhDjb4P/f$gRf4+","#v4nqfkubQ]o.iAeOb:8+Y~Jg,i&odm<PzLRm1@FB8PqZVtb#JfH"],
  w 56 37 100 1310391 1310768 33 21328 payload22,
  w 56 36 0 1320000 1320393 100 48542 ["a8Y:j!D;vFbKTF~C#RhEAv^'!?z)<|T}td7m%DGBH5!~fq{e[HDgRr!ZN8p,SJ7q","cE)_qyvs5k3-X%_rlo,1(-=QI'9_=%l9<eP>p/P4mTqPSCH};H:G6RKTk:gfg(@-","4_]j9:qp(}]Y@KeU35:,xhhXkzSx2E~[,pYw^iO0Ti%ET<A|eEpL-eonVbm'i9G0",">>YZ~>Pku^P)2rsv(~D|>,JLy>}tN@-9qc<KJgNA9FJh*oi%W$D-*1]7f63*v4`c","=:#'%X.S;]^fxx2[^^]WSR]^$g<N8rfj{:ew_wWK<TLD[C>'X.Fd?#_]f:Q&s4.[","2>}?}-K=3m%(rTqc<y]Kp_anev,cx;aS7pYLjIN]@Kd_?dQD?KFx'[Qr%Sc6qr;!","un#lIL#*v}l`az;o0h}{kHF>L]e$Ytby}Q:Y4^T?_bpwWfZ-/Z"],
  w 56 36 100 1320448 1320768 27 16614 payload1]

private def r56_13 : List (Chunk 56) := [
  w 56 35 0 1330000 1330451 100 44143 ["lBl%:KWH*?e=(tDa1pR}6OEH(}%&sx-h_LcCyBt!VI]sUT7=rD'5@#x;9gwPt}Xu","1Vuba%lbSvl@f)*JB{l&J,x4=4y'[,QtIPV~KvIo=9AO<$1kQ(>[fBJQ|aWgo_SX","5Xq{txO,6;MhM+*<A>y;^~^<xhZ_kR<!/8?K|1vrV7GcQ!T-kw!g*.YQ^@y!wYl5","gSNbnXs5g<&;4<C|u+.M];dkUz:9WCh/=`rlXm<??V.^GOE/2*5|YpC@-|cF@'W#","7fV/NmNPZZ6WB[]Z,;x]X$SK@Mo8W:]+m*Tj2^hV[EDWPM-g5#yA!Tz`b{BdOe-z",",ilv],`'`,p$A-Q0x=I}_zmQZh@ueqrXJMk/u<]:n'39M84h:_b8vrN{$yNe78W7","*DW$zSb%P{Lq'AIt,N/Dz.3=i07TTlS?>4ZcA,p-v^`0FRFU_F"],
  w 56 35 100 1330452 1330705 20 11675 payload3,
  w 56 34 0 1340000 1340454 100 40275 ["ITwcq0ThSE#Kl4y~3pf%dVhwXt#WT9NfopDy~mzf}3p2u]|>5'{Zbs1M!}shV{)8","k?Gn4urAZ]S^?uA))O/?IW~91~SH+3)8|^jkNDO|Q`q7MS`czzT%7GGjUd*6doXP","l0plii[}p,9i,I~LVY@#>L~JdJ;u:]W.?DPH_?wl5~dOFjSg2C^V,$,:.,7lWm4G","ru,ebs[DHhy4~L14{Gq7[!4h93GAIbP@boemC~KuCr_HbVA$U9#T0Yb8.LTfaki=","#>FH)IXv/'V?hy3&0DK8tz$XOcMDDlY&]e~XCpB4|yInK/w;AKpDP`HRJrzyU<B6","r/y|*o$%&m$<'q+C=>Ky0DQ4tE%]^JAPT*r8N@&v`'<z`B?rI4wyO2n/Lol#68.t","8T2>^84bFAjK3.D62TrcU-:{:l37|!0>}j;|HXl$gb,DFom-K"],
  w 56 34 100 1340512 1340704 14 7827 payload14]

private def r56_14 : List (Chunk 56) := [
  w 56 33 0 1350000 1350515 100 37103 ["U3Hh4)F5Lx6g3hMmy,PG:<97[JWf>ti-p,udnC4ceBI8O5;N?A||g-DZ{x|iKU!L","y#KE[<r8d,&APi>Lbb1&;+4CWNyq&@%]@rPVkqz%QK6[D+ebAT3N<j-cR)H.I'su","0{1fDf0~.IZ`-CI3[BlX-#XQwiMD0Z}nLJ1:;Y5`.F45!(CJXrjd6Em0AnB47nDi","7XSY|vr}F*CQ'hc9GroeBH@m6F;CRh3u)Zi1k{*Jx-vTAKe=0s~8Di9>6;$^#Gb&","bc;)KYy'Z$lCL1RX,OA)M/V*<X'k:miq!h'zeAu<F|a,$H8;fF-YqER]}qIPEX90","zOgdoeN5:GBDQ^[[w~LjH5:.lYT,jLJ&E`WHb/AQ>6mPe2.uARI(;#HWA0yQ}^/G","cN/YRz'ID=+~fzd`@Kv8d^?7L{z:q?]O}pP)]2_y]=>-P<mP2CBj"],
  w 56 33 100 1350516 1350704 8 4325 payload4,
  w 56 32 0 1360000 1360578 100 34345 ["cZ-9bL!<o9iz<Kb;{/F(ASdREC9zXL.Sr%v)11YIV,`-b@UJ^vd'pD{X`+k)[z:m","`_s<}+mdQYW+T5AA}@haNNe{|/cpqvj5WDr.f^S+m!=FC~hgBVY^2lOG+uS.]0pb","GzH(Bmx{!yyweUZHgy=MX>K-BqO)pjgR5Qu8u@>OEEmKi0ezF!gjTTdbY'5DE9/[","X`TB&MN]/u4ge^'f(*jn)0(73+TbPt^i^hl^r6MK8>'j4r-Q8q-YduH>oQ^[}g,P","5^nn7LEbgL(*%c1UO06oCfQ~M_G?'SekT@Y;NOTTS{YA5/5A.V<B,WC[/jf_WNGJ","Y0<&*VN#PENMTFI5R_Bzs31|m/noDMFc'.,0=kQ_sC*Jw}!omk@n<K;gvyC-gc})","LIjA5se/7noU>5zffq*s#t,Bm;.>Tjkgo;qtC*>:`d:&>Z(tcz[2NU?P"],
  w 56 32 100 1360640 1360641 2 1056 ["#i2GG<Je"]]

private def r56_15 : List (Chunk 56) := [
  w 56 31 0 1370000 1370640 96 30211 ["%N*~UiITU#AqDfP2u$>rZX#'KD}='}.V1BYWxb#O|qUP,I|mQ]&8J@-hOlp9sN(T","USf0$Z:H0GU/tZntT<kC.!@}y*tWDchv0jY.Vb_*Y=IGi8tQ_fQ'M3zZV>j05<~k",";0:JUuw+<E3kVO'#6zw8F-sds3nsq&h6qCtTVJ{T^t9zj&_h2!X)IU[''UECvy0-","iAG^53()ia;nYL,|9YSGb~Pg-i[:~W<%+EG7]{asQxSu]%*FNlHs+(r5?&srQz$G","zMcfWmB/'y?L*t2FJ=V;0EBzacwL2$jaf_y0.QJrT+RP0Y/dKa>n|{E7}#6)d|ZA","3=mlX,&UAR''lCGnH!{;gc(d3CCH@egcHzp)E@@1`l>a(+z*N^|*=|G}ZdaUC1v6","v<qSCRDHOQ|n(YVZlbdZ{j]3|`B:rgN8T;BB3"],
  w 56 30 0 1380000 1380640 91 25996 ["We86s3bOb`L/QJ%>h@{4%w0^,x:h',6I`ssTLTvg+=uy'%v7p8+;dMj^i=.XDzTT",".$|1,2k/G1JGNsd*HL@5$hqL'^@W}:~0p+w,?J{nW,-eIJ!p/mgd~w{`-tKUET;'",".ooi.%p8T-o%`$Yq~X{4(eG`e6Brdhau'arer,yMp~i[1Ntui!8vTC&w~x[;cQvT","cT>FGAlG8F;t-3Iiycuuk%v;Ofo]TPgr&#[XAL+)GPJDl(=2KMqlHy25TgLezW%P","Tg:8k=,{kBJ)55<lkG`q=.W*:*_F3aMVHwr`8`($-|?[O'LMrGi8!258Wxf=9@vd","_aE-s!},CVd^sgpp/ni5q]?SFS62Cl{~S~DZxzr#%joBbeO{|q}W.r<6suk*Em'{","#g+!b%YQ79@,0p~K"],
  w 56 29 0 1390000 1390577 85 21920 ["}s#sd9l%NjO'iEN?/$r8tdmN2gk*Z8i?{|nxu#oP;`to:T^5E!kQ*8KC!Hr!<||0","D>1N;>WT?TIr&KIjKN'e/~/bUsPV+}oX~bd/JCkU^|-.eZ]M5P2Z_-av&WcVl!,u","xkBsb?/DC8+$A*.7YJCJK]F}|;{Km`@[?o6Fy?ww7*m5qkc,*,]tku>'kfV+UFS;","ub@WwhU[S5W,k/2}pvBGG6^wrMEHg{w@Slf$XrW{whGv~x$mZNhJY$h44]s.9s3K","(GiYOTb.S[Tc0jBumR7b,$AmQLEWQIH6.80UoY+Sj}9C?>Ln~^x+QBz5jF7eCegW","#T%1D~k+y^ujq+X4a,wPN+bgRbI#gEg(G0yI]h'YX~1DT+-.1&hwAYz_/"],
  w 56 28 0 1400000 1400576 80 18605 ["Q]:#<l!43|@Hc%{0HH27SUG)H53.f4z'4fo/Wmxxy4]*q{*_^pJdx^bl~R^A>Bk[","<ZMT'M{!2DSdT'si+;dch]-~s&Vs'S=nI]F,tO2:3+zg(kMoMdCK^Mmm3=}jwz5B","~kJdgH7yh_9$+2h`*8#YTF}D6KFJK@exv1RaY&(<M3=:DX]u|P#c_orLC/aH=c#i","7??c,.hiu_1|AZ1Qeff^'%27G(K.,$-.rF03YYC_=DH{yi?J?T1''x^#JG-T9!GP","LMAf`'H@OB>52L:f<<h+O0yLXc1o{]|kh'Szm2y2MRC8)LU?M<Vx-'?C~NxS9j%J","xA+@nv37_wYZwV8]v<j&Ex?q3c3XCd/G(I+w"]]

private def r56_16 : List (Chunk 56) := [
  w 56 27 0 1410000 1410576 75 15755 ["R6U1u%Ce=sSh@+PpKlU7wu]`S<^D))xyw;vV$({hF,INAy_nv$7A0IQ>3^uPxzSX","nl(@y{!bXliB!_#x9`d;QK19#NnftcJ?DK9g(KsmvH[k;xwMLt_'(Z]R]C.2{1%/","k|?|>>vb[k()nm)cwR4n1-!N|+UiCAfah<QH*8&lv^>$OQg:aa5DoT>D>nSY|b%H","UNWRdVeM2Kg9EZ&ihCof-ehM{YTZjsVZKCQ2]#<@W:$A;@f$h^N>8?iqc_Q&:Z=b","GnSu|k>,}ErucMX%8j=;n=@Hn,#Z3ipr9If$#No2PxK{Vs_}EoakZD3f1?;:4LAx","?fVrP^xxaQ?9)D;+qC["],
  w 56 26 0 1420000 1420513 70 13090 ["7_d#ausB3dl&*lk4S_RaxjB?p2<cvV%`~-#,O76Hwb}mQRm5kp@?jYDCKrLI>U,]","s#S7EDa(|;X&Vg2HSR`e4~w&XxYUH'#,%/8&#EQhyURx:bpldy-0wey>(&+JT!3`","TDs?~*<sD4@-k_.=PxHj}^Mu$DMjrqQz1kYv`SDcX'^MPIxh]%W.6p(&kfgtpj8u","@ohhMyiWfr<_xw[Ix#Y<6yZI?yeoXB;wl/?DL>*a^'E!CvDXxOYJ,qvr*{'r=ScS","u4n4xPi&|+uH2p(v,>25WZ5j0q2_MNEZ~~[X2K_H<AAf)R5m({hRM{_[.5_eoN3d","7N"],
  w 56 25 0 1430000 1430512 65 10810 ["/mfs77!'(83r8MI3JDL?rt?6WytDXs/3VK~$r,U=+so0wYz#I~tcFs39GKLQF`-a","P$My7rSM!D^#wDsT7=xd7bV'l#*;_Z3$DW>XSk?Yfnnnf_u8d}p5/%rW^ev[$%@Q","?$~fm}ly730Cv)&[P5#qx]'2F]./Y2tvlr(Nv>k8fD*.6:a`R|$h$:|yrC[#2h=u","R41KmN8>}S'ejXJfY*ph,CXws;tvweIZW.j_7lNUqmq8_<FJnpB#^?)r9U;S<xF9","#Ug]q?_Ha]!BDJhV~S(tK29>m4c4qdsh;:qE~#E*8YW}7L=B"],
  w 56 24 0 1440000 1440512 61 8971 ["Cj*u/(oXN_hRvG<JF/!lBRKrE4UaKiZs0X8,l8WT3l%H,'/bMqL:S0J8[8rz63C8","'t2wT,kkq*G|H1,WY<zB8U,`^kaN]Edd[_^7blX|?`uG#]|&mlfYh>aC~gDy)tv$","L=QS%_v:Rl;B|=CV3aOlOc['AM,^h38u+Sp:@;+SK1s;?GGF%P,H5i|5jW%Pi~},","JhvQ.b{Pucd%!paH/FWRa>;L_ew{<}O3Y|1dby'k[F0Gp)fn-uEP1/fWs*y5YYYm","52<&x1z1I|jJ)vh)Y~i81U/lhwLngIT"]]

private def r56_17 : List (Chunk 56) := [
  w 56 23 0 1450000 1450449 56 7178 ["O&><%eg?!R>j113&I|K;P&B3Kg4$^02BMKgHF$L-L1$^L4.~!sR09Y5bf2k#8T#(","0*0=~Fwv/T5AnjiKuMl8m(*:3^MjD2_V&=yM6[RJab6$wGV(xdfI?<C#^V6<OxYS",";++{|c;D[:f&ofY15MoWQ5=xE8}[o:gW;a)+WF]~tA|<CJOt5yYYfkaa9U>b+DUE","B'Fx%,;X%Iej~3HZ277wnRx;a/W~7:a9'X?pC;j2fddb~0(ny&xlC^z@t,PwD+Ml","#[STKzwkx[|$"],
  w 56 22 0 1460000 1460448 52 5762 ["wZ(#v:F'K`?CBFWB4x_CkGQiwj*L^6i{CFsXXS!YJFo3l25aV[L~xh8zSxT<bBBe","06(VPX#u8Cz1A{&d_crOSv@mz5]o:?5)~B)]=B4xH+mi5DhAv<i%d5d.S5W3[(&n","7`r:j>:diFZY`^(#lp|ZL/ww-8UQUwJTA{V3mJgSj{2whD6p?Cie*HcAR2r_JqT9","1.86uU/a@Rz%Hh6ZE9K2XlK!@OMa-;Czd%#{r`>ve:B/-n-p<Q60G|'7ah"],
  w 56 21 0 1470000 1470448 48 4590 ["C8{!?+:`phy</T/5&6JQml[}*|_Px,nva?J]@vVx:--+V'R,SYQ}CxO3iR'{!9)0","]kbc+{leS[2>>9GV<s1MLhY$UYK2y@aD8;DKMX9eQeepNmq#7s1slgz=%g}Pwdkh","}<A$rD%ss/P(O#V[q5>s7g&%gq9r>^H`vg8<qzuv{#HSX(+M^^#qZP]{$>gPoo>j","<1~WCz:l$t0ts+1$}w<CmC]l|*6G*ZUo-qP;2A@"],
  w 56 20 0 1480000 1480385 44 3526 ["_+sA%j_x#ohef/Y9UZU'I_RJEkDwmk~.RL-UB)$p&vA_}n'[.suv6LcgxB?a=)z0","}E8'L+UPdHCajG<L(3V$/Ubzek~}Te25$5$|uo/S,-/$w':s7bn89naWYmQUXjIT","('N%,sUap*1yTw[O?:&c)/!s2Dn+87,M6$A84exE^OD+d@v<5uZ9P=./#Yv9(3Y6","$o13ms=/JHcl9'~-(!Bo$"]]

private def r56_18 : List (Chunk 56) := [
  w 56 19 0 1490000 1490384 40 2674 ["BL4`;zY});|!ooAU.|v%%FMj~WS#%)(-}]YN|7A,tr,<5Qcz8/?K-]TJH0heqm@<","A@!'j'rB]G-dgatKSN45&!KcC,%$Z`!m>I9b,OUxcJpfi,Pxy90fAwNPb7g!2E.&","FxCb8*.(dSMUJSQ@x9%'&taQ%D?1r!_VH<Ix_%4VTbO<Fdj;oq$yk->>sb9{d6B+","%"],
  w 56 18 0 1500000 1500384 37 2034 ["$TZGPrS$)A9G?r)p='p9XcZGL$5h>#kVQ@cAF`FLaN/W=9+[nmuL7b91jA|5Jbe}","UfF=kaKgkBQ.{F'PdF`xak~SWR+373fUr0IluIly|!J8d!Ks9ya;VFc(AiZ0*/XB","(1DmD(rqo!EJ-hM5IF-Zo!`+R8O{h|{,.L@NfA/{eI'OltH]"],
  w 56 17 0 1510000 1510321 33 1439 ["x^iV,10@?g)pQy`8$I3(%BkOU'<=%B=M/63zl*0}[0L)QCj&+QjFG:3>yhnZlGF$","XBw.fPz(Y;dUdEDox]]34}ebSq'jT&.#|GHWQr>;;1'!?}S`:eb2Th1%{n`F]TEt","%S@/A#W+~dSLAw#[#r1-tu_1aVEbq"],
  w 56 16 0 1520000 1520320 30 1012 ["E[lf^]_^Yn!cN:iWWQaUE{(v<8aJy8U>_zq](f}gFk)aR{;wf@kJ|_)A8]K[fhD]","~&_z/%%9PexTXl|tO^,ML`1[F%Eb5u7t{U'HkVN`')_@U%g[A$=8hKAc%$0H=dB#","#ES[Aq9JjD_bDa"]]

private def r56_19 : List (Chunk 56) := [
  w 56 15 0 1530000 1530320 27 696 ["2p*9wG'x(+=BQDH|q6+4vY^IQo'~4$sVTQe;^_lNHxodISs8n6SeVkYkw#,s(E90",")RY[0qzX>hthUShy'e<l]rU2[84/}YwN<]AI$n~=dKFD<5RN3+{iu=2]+-.FF3"],
  w 56 14 0 1540000 1540257 24 431 ["8supE/mC^8)EJ7wM<fKE4&J2/y(eg3N{~Re(|%7@FRMn9&gmdiUw,Nw@TgMM'Yu}","#>2Cd*sq(r9}eSNJAFl}HVoQ%DrlF-ywPZ_]Phyb>$mB%`wc"],
  w 56 13 0 1550000 1550256 21 253 ["3z)cTHbM$.!eN9;T2{QMu0@OO6PmBAlZ7?')&T4,v7Iq2x/+K!QG#K(G@TE?&HMP","#I.x=Sg'8.>~c%g*h33]*/<`1m|5+omr3X"],
  w 56 12 0 1560000 1560256 19 142 ["GV5D_r[U9]%n=C]gi(}ctM:PFM*L_{$V^AyCnyCKEyx<Ol-!OUZiqP^}a4s[gCF$","$cIBl5D@T6NucbY1iv~No-["]]

private def r56_20 : List (Chunk 56) := [
  w 56 11 0 1570000 1570193 16 59 ["%0'Br8J,'dat8RS#cH-b>n``]BOYkeXNYXR)fDk3wlHRo!6D>H6I~`SYj%Iew|9P","#6!)8%l=&G"],
  w 56 10 0 1580000 1580192 14 19 ["[:-bxe+F)j*qZipLTjx^^ejraI`rg~%0kq33Fy9'1K^2!9J-k].Ff+[!dbaP{!$"],
  w 56 9 0 1590000 1590192 12 5 ["%O_R`._F?z5&<Sw/Y3)'H%9;f$^Xz(3c$])+Z9u}~Qrzjiviir!35@"],
  w 56 8 0 1600000 1600129 10 0 ["be+D(~AsZML,=tq@o(N$t9_2Fbz-n}|R}0pR*TE/<l,}"]]

private def r56_21 : List (Chunk 56) := [
  w 56 7 0 1610000 1610128 8 0 ["}aAmg#fzn-/})|+,]Odg4EsLuP2Hz[f&yx8"],
  w 56 6 0 1620000 1620128 7 0 ["$h4KK;'`Dam^}8PThZ@XQOM{3L2t8,"],
  w 56 5 0 1630000 1630065 5 0 ["#ILl;INWXB<tyN{P$?Qmke"],
  w 56 4 0 1640000 1640064 4 0 ["z_>-hlyj$*p|8-:T"]]

private def r56_22 : List (Chunk 56) := [
  w 56 3 0 1650000 1650064 3 0 [")o76p).qNr$}"],
  w 56 2 0 1660000 1660001 2 0 ["#lW4bGr0"],
  w 56 1 0 1670000 1670000 1 0 ["%A=@"],
  w 56 0 0 1680000 1680000 1 0 ["/T["]]
private def chunks56:List (Chunk 56):=r56_0 ++ r56_1 ++ r56_2 ++ r56_3 ++ r56_4 ++ r56_5 ++ r56_6 ++ r56_7 ++ r56_8 ++ r56_9 ++ r56_10 ++ r56_11 ++ r56_12 ++ r56_13 ++ r56_14 ++ r56_15 ++ r56_16 ++ r56_17 ++ r56_18 ++ r56_19 ++ r56_20 ++ r56_21 ++ r56_22
def rows56:=rowsFrom chunks56

theorem good56 : ∀ r ∈ rows56,good 56 r=true:=rowsFrom_good chunks56

theorem sorted56 : rows56.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks56 0 (by decide +kernel)).1

theorem mass56 (i : Fin 57) :
    bandCount 56 (i.val:ℤ) 56 14≤(rows56.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks56).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 56 (j:ℤ) 56 14≤mass j chunks56))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total56 : (rows56.map (price 56)).sum = 7411379 :=
  (total_eq chunks56).trans (by decide +kernel)


end Final50RankReceipt

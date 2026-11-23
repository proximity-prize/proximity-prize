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



private def r35_0 : List (Chunk 35) := [
  w 35 56 0 490021 490590 100 9740 [],
  w 35 56 100 490641 490903 53 4997 [],
  w 35 55 0 500020 500585 100 9483 ["z89DH<|$zkKT@P3s1@:pnh@L^XC%SiF67ghuBFvaBiDwZ-OboL[)^WC^''ykrZ|.","v)<#xDhF!+f+H=bCH;W@Ojw-l9=pIWb2EN!w}16vj4.5>;t,n_W7'?I*>6)TZzD7","K^+_NKWZ<KT8zgu7P'dQ{(']g/Ay"],
  w 35 55 100 500586 500902 56 5092 ["iWEdS'fr+_'RDJkh,,=pQZOK&#hkZR|}]5pqU<.+FC;_M@)Qx4wgisNrMgP:y(B|","3%2NtFbOQh/<Nf,)+MGC!3fLl'f2t"]]

private def r35_1 : List (Chunk 35) := [
  w 35 54 0 510019 510579 100 9246 ["T;_n9[?X}X5X!BH3WHH{2Swd6[3(G`PR`5AOy=3@d@GzMN*^kavEBi;5Bd`/DqH!","(</YNXBQ_x]e%dK;1h[[)mmE)'tnaPNZ~B?~Q8Dmx>;o_TUqfYf+|YcC5[o07B[&","EAoxhf#RqD)jjuPU7?ZYq)!7s*^Ay6ewUfGKXA<wJIy'A62(Y"],
  w 35 54 100 510580 510902 59 5194 ["Q@JgI'qZ1Z)4OgET8cC>_^|d'rGN%|xj<SDT:}yX.ouF6e=jPuCjwgR?<hK]+K8#","4dfMp]+LVGX$|dBz^>vLXl',!-dDMSk$m$G~Nl$(B.$OoqRUQH^Hif="],
  w 35 53 0 520018 520525 100 9027 ["Z*_'8_8II~B0j}c2Y.]B>rG='e0LfYG~i=WMue5QiWib?gtI4C'zw&MS;$V'l@N:","P-<!6ei>up,9~>Efgjgp^P[IgNc;WT&@W7rqIw=[j2%0iqVzY0(?N_@~>HN-I/l}",".!RI;2cl*50,#{/)UtM7)YEM(NpY=DH8j6>VcqMFH=A0K-#PmAwAQU'3KI7XeEv|","aU3Q!ODRg.mJ;v;tNu`;|;AH"],
  w 35 53 100 520526 520901 61 5231 ["c}vK#Stejs^%zq@.[=~DzrYZe&1.tp:5R_.e}W+J?7UCqJ42/USZoQ5LMZsOW:G0","Rj0i3'[F[Qz}B+0ctdhFnAn0=4b?,QTPkj=gs:{KBU~~}BgcFDv)?#xIdsaKziT|",")&PxP`g7m&!Ft3wFO[x"]]

private def r35_2 : List (Chunk 35) := [
  w 35 52 0 530017 530520 100 8874 ["k3t%jn?.d0@Qk[r@IwD4Iv|1-a.bBUhKo>0wH/bY2zoxF2n#)-FB1*bqD^L78Y4B","!9ze5C9WD|j/Tw;2-Z-rN5u5!,+v?O3`-v|*epaOtD%2)`4&[p.?QITE?<Z:.chW","X+6sWMMEF{N!!wYMG0]0+C(@@C1%RdGi*o/=:Ix/0o5,;N`C'$]lLsSP9@xFe/$`","#8$033vC(v5;m-tcoc6Z+s]#[@#Qb]h'u&x;/>.ZRL6hvi<8;2CYlSnSU"],
  w 35 52 100 530521 530901 63 5225 ["|3kr0=&gag1%[<(l'&p?,'=28^S1P3a:#gVUl??T4L_a_t:CgDr25?#O9k|TWrk,","lt4o/TCv-MIH?-.MEy7@$;pQR}BMC}E@zn=Cx`Cl3}(Td0#Jqo-0M'<+k6#&5]sT","K]j;UC,>grV{>Ijw[cb!-/~l=PPM62E@%Fr%m&?apj#{rk0_"],
  w 35 51 0 540016 540515 100 8742 ["ZYOm;9NhQ|d-@}a4mLw46B^3'&YHSxj/#MG=/;x,0Ez0.aP_v=ZUT}~&i{0A822k","Z3/$zvTaLK7Uf45_IjOX;^Wgv:>(|m+<uJ?49x0{DAq},t_3pp+~c](0*LG%ui$c","$'sw/ePUQyeg9=Y=&JyktX.W-$k<VsO5p;PbvOCOqXRNkn]%l)?S?XS)D%xPyG:`","iBII>I+B7.l&e:YE]gb0m25^U8M!JYt++IQEZh29j~s2CY_,m*pq~XM:NsZ5B%|Q","G-AQT<mldKNZKK?i1402f8l4"],
  w 35 51 100 540516 540900 64 5154 ["Cbv'6uOpzZ)m93cT{o0V[(;k8RAQO#eUYA9$@XX*41VsV+TmO,8nFP0p0/v^y}+i","#$~<_gM39(-&>9%P9rR*~M./$lCN%T1sRDi:mn8*Py%jBUYpoZVTd%A]z%~]b(7~","!8u;m9qjy02.m'-Pj6N21w:?EwAt8bQ@Zq8&%OvO8|,@yeUgbOr~7S!~&?/R~QF8","&6Ki/~+A"]]

private def r35_3 : List (Chunk 35) := [
  w 35 50 0 550015 550462 100 8573 ["Bfu`fF1Q(?/x||5)`,:fl6b:=/O|ssb:&hk,OXtbwvoOh4N]v(U?H}:EwBXRj1}!","9tTgFHKxuSv`6F1l-QA{9SN3qo9O%T@BpY[Z=T@:M_2K&n(>%WeTX!RLG:!oE)~>","Eo@9)zA3OV'2BrQG}udeg@XM{/>x,{i[:O!w/O(F{QJ6A,mDX5Gx]fJnQ]XgW#GK","|b9@U|3n0%|yaN=^}]8-*i<iP_Dp4FbfkzR@VwN]~[rY2ODB([IYF44~s>5mSfIT","<gI*+i`lj5q;>q&g[6!9lD7`9DPhx1czDItT5.0k=|I[i(<==#"],
  w 35 50 100 550512 550900 65 5134 ["%,5T].lri8N6F#Ik?f^{#<<P@2v)HVJ,HTUtNy2#H$KoIn'JVJ9%d_#AuLv5zOi|","SXWTKRM|~O'K.DHeBwgozr1&}|q/c2a30v'HLkR|,sUz9L^Vv9Qp0QLu;0?t=`>t","L+2s.^x)O?^#{YO{bA!JvcOIzlF^TVnmwD(cqHgr1&e$=~^M@3Uzw+XnaK>i<2f.","%xLr''O$9PWG6Av_VRUQ&kHbj-"],
  w 35 49 0 560014 560458 100 8483 ["P-TO#W`zKJ@)m?%d,]0NjUfoOY.2Se^>yxFL^T:~nQsc.vSwo;[:y@B`]FSr~@lN","yb;*D3J?xuH.+O,pw/[>{A!}mlAB6q!/aj2$q$ctl%&@=f3e!;|o8V3.UNz^FTvL","<,L[2V(,jONRrbg3t4hPY`Y?45]L!s2}N<$H{G#v^s*pM,2e]3!XM/hnZ.!k{np3","3&ZDRwWfy-pjH6@:i<5kb>j%6.'6d=Q'l]sy;,`c,c>zI7@0?k@3tUMa/PHOAMm0","Z)3ti](/DlsvIag<Wn}mgyQ`4}:v`UU;pr39UW3JFx7hVz!{31qd&)rqt=x;<|z:","%}R)pTtE+h:s"],
  w 35 49 100 560459 560899 65 4979 ["YnG6eV$vFVT4NL37>4SC`,YX{W=CH&wJS.W|XfsT.=h'3b+0+1dk|:$bg*4T|C7I",".jCn7D~}=u^9-+GMdwBmQ%z+ld%1~e8kEm%0_kdZw+f)BKkYZ-E-QC47^b1Ge&O]","^J]HVnKPV*H-^I0K5Fb@`KtTJRyTLCPk@$[)<%)^01@7m-IzQk(=V~:cYh33/&]S","&eA~1b;+pgWX=jsWg+UDo&z,~AE'M`M1c$GfD]{M57'N"]]

private def r35_4 : List (Chunk 35) := [
  w 35 48 0 570013 570454 100 8369 ["U;e3njNak_}~v??uznZr)*PwU~~o|<FKqTJbK)L+tu6{Om+*1~c-uP<$8545$8Jk","cls/tsRz/~3s(jVd&S:CwWP(Fm):3Fsx<h'b~g|@a4^s@efBCH),fRk5`99GQESg","O1py5d]2Uf}x`VHR~(u=S2.Y;fx<;m7eGBTK3k:`CO1BA^By8OD{{v5Und];!#=@","GlSMx+7lG'[rfTU'0QerX=FQBGXdd2HP~5H(h]FIH)&rd+KS8YpA~HJuaBTs2]Nz","Z/Q9^>Kz7)TQE{^);tw<~ri?l:x7/5o>xVoC/~^E64qk3zrTg7$#:jUs}&@Z?N+V","#XklX2]Q%itc*!o1XYV<4/7RxX.Gb9;$"],
  w 35 48 100 570455 570899 65 4843 ["Oo)HA4!@6V+F+I:Ye`|+oSE(}T/L[o+z6IY#oUS=HsKr8Cg$Bu=&mpy.}]fDvSG!","f1{Nq[m|Y.;V^ue.Wv?XW>m:,54C/<}AO2EaZc3%?f*Hgn`hZG7oxGhX[2_^0-;(","70GPr9RNv2LsR!<SEAXxPV$k}zHR;ac^@`/|cDb`cu7KN!M2]RU&-dm[0U^!et7-","ev%CM*q;A)U)@Gq5WV@}cT@[T'w!&Ks/m'vUxGv@DE!BV8Ex-Cl6QL2t~9vJb"],
  w 35 47 0 580012 580451 100 8255 ["C+s(LT@y>5oz$ORB:}dNApBWx}ztSOShT^RCQ-}OE/x=dc!t8<rj~r6jc,KPrO#>","s{K~S.{w!PH5jXVsnWm>e4)>>4-&j+dPV4Mn`3m{8y?%eeaHOWe![91`>]elcO)B","pd9Ow?Uhf=3c.pp|W&m`lp7WTzqZ7Ne;|>m]M/v#+q(Q1h`hRR,zm%HNB?m<}x;1","6SM'h4#2~RZLuOEh980BGYJM/*O/Kw|nI)>0`eyVhK5GPj@9gyx|).nK]m+1h%D+","%1UJ:SgUq~sRzOQg6.<=N]d{7]-2AS_v~xW;Oaf@KagaaAL'cLm)_S/TO2TfGt&]","_Un_gTqXA;r31Y9&Z@!dgVYM,WyV9netkc?!"],
  w 35 47 100 580452 580898 64 4648 ["7YU0P.e#&_|/-)t%KF]W1{`3w,v}]+hKen/4#2PP<oW0}YOoES*_Z<yE{$o2Ub.5","%}&9!-Ct:y~OhDMJ!s8kVYzC3lZ*}eH3!QEDOR!4zc_4y#ebHa2G!b)Yc.LkmcN}","yRy=q;:Xha&NY8~W8^[-8NU1$+p6yz@knz@h#dg=+h)ZHa|4Od5/ptVRe+w1!s.>","PDNF3@8H9FHJWrAE:7h8!]pz@87AX,EG>(5,R2oT[*ie*&[wRX[Cwa-o<&[lP4.T","-^<.$j,`&F"]]

private def r35_5 : List (Chunk 35) := [
  w 35 46 0 590011 590448 100 8095 ["0^#?8>6}s{CO^IT7*$$}iYlf2$u&h`9^qqm?t@zx&b^o2WG1vIbP0X!H^k-k,@cJ","|'77tV%J=R$VPt7{HO-s-@'jX7!UM(<_[}K.x;mV5-AUw^:tJxpa-^u@(d_?jRhN","zia<q'M/CVypgFQwK%gUN#Ea,AC_;mb9^>(oftHGTp0MT8/@}iI)'s9T,.R)zCn<",":zN8L@'H;A*wlk}xH(d1o,fpdM}t]}6M`C1:Ie[a~p6>/i'|S**k.Pc=.T**Itw0","6^h'|6ZDeC1-dT{.*2?q(DY;=V/0UhRSQjXR,jt73N#fP;XKm@H~~E$J[0)O4[N1","$UAyF`%wRgXN-Z>7>P=mWrxz7Fw^'(&3/"],
  w 35 46 100 590449 590898 63 4488 ["IPXub|7{oyoBd6K~3f[O_8j!0+ZVj[+r#8R.)?DHaqTaM=.pN)[M)&C8Za{{@{M@","eCHHjL%)F`S(,R7$G>?`'aB8^~rA),H,><cKyW%Kn2-XBq[W8k)l%q5VzYm+&0zN","3Y<J'mbjb9)b!ys.0&;Uq3U1oF>P:|{Z;y+m*zD:)?M9|f]ejF;J'TJKQ:I#SJUf","wmM1,Hj5dK=Zs[P2`E9snU?F%8.:D56b$d0y#9+pGrZ0]>7d`9KZJR$vw`888g?)","C9zJ]9B|$`w"],
  w 35 45 0 600010 600396 100 7966 ["w[2G_L6i@rt<w%ijz~#MWHk<PW=7i.g=}.WWV4Wz4k_:k1Lp5e!-)&vqU)ac|tmB","je2-'x'U1>dH6BO4G6.KJZwFiC`n3'RzBvjptLAR:42QmA!cp.3AmR@=@4b/aV#S","Nkik.UsA'3W:W^Lssj+{wa9`25WL%X<TbTV[eT?*o<2z!WJn35K:$Z{Ata-xeCC}","Z4Y*MTX7,)tAXj<#:r9u2$C9Lr@G&?G}{QQ:`l{-ZEP}$e6W[$W`!,T:SACr3_Ht","|jp]s=z9sD>Kx;5b+-,Rvnp*T=Vk?'4z..Nh^#,?IF7u)B=!&M_`IbdwS<1m!(g(","j@Liwk}^bAciZRctZ7lMGBf<[adP0$Jb<L_Ki"],
  w 35 45 100 600397 600897 61 4242 ["#iF&)M$kc5`,:{zL4A~/;[(u4]GOEonCyl'zBe:/I[+[j4{MSr}%sc-)gC6qsRon","]i-2uHa-6MM2s0k@J54EyVhOZ7fc({AK:U^.=#JN9<DjXson:SP;P|Zt53#Mr>K5","cAD*T4J.RcR[|[p;1>|&8>#^m:Mh^X-fJxoPY;P.Lo~>Py,:`lD1zo2R_Z=2|}j5",")0'<qr[K6j'JS;TgcGTjD<aW0?HIKC2j,[2.!NCpI}RHy4j^~r|[yvQ!PI5~ow1$","h[4ySl8"]]

private def r35_6 : List (Chunk 35) := [
  w 35 44 0 610009 610394 100 7829 ["R2I[vX=h1{]*22lJ?~Ml2;_IW1PaX&1|}5hR2C0'j/(-lT6^S.$[W{#l@y<IG[8s","1eq8ks$coW};6J.N$^ee8@vkBoFy)6L/MFahp}RB@F!?<u^(x^fD$YV,DHeF.e,L","(W@uBZ4+A)sG3z*H;z02W^^:oHGaYl%OrSh/]/Kn*St9N`K:+F^|,!RKN$<,V'mM","@*w!2Wex@<Xr2;$]yfldK!~l:U9j,iPF[C^hdH=cksCi>'whqy[[%3/*)!}w?)'m",">?z(,P!&wXOg_*U{_T>2vs@sYg]WXB4F1k'q4r71rFODZ`]DD!Kim}oVcFF%H5O/","$/H{Is~{ViDsp(*qT3<evM<VOhl1LDi@Ingfo%@"],
  w 35 44 100 610395 610897 59 3990 ["G0u<G^o;E?+th5@erd.w6,PzwA;U^5z+vR~5r;%&B6#fp2Y'SoIk6g~(ZJ!R|92M","=i)kv-2tT&g&nG}82{oA?q1<,HgUJ4-Y^ez}s$wL.-rQ%zZ_l}l%$`k{aLV^FK@3",")Q[>6<Yre}qD}{63'ji@oR[EE=!tJL`0T-Ia5*!V^L##.c8j.UVCfkd2Zf/?-.0_","JY^'AeK_jIbdUsl>$EENE=;<mhl(K*zFe3JDh=d(MpMT^O(v=:Ufx#r#V4Oyx__A","$OLSHikScn-"],
  w 35 43 0 620008 620392 100 7696 ["7PvVC;d?El5IJA%.BSyTsRg'OK)d,lda%JnQ<y_:(N}l/~IcYYkO=>7^4Kb[)luc","G8AIkG$k[y4O=dXl1+OQ3^TZ9Itz@,J>ZPs-Dh]TVn5PEhy(;E@FzYpk{W@$bN$f","!'N/gF2ESN/.>-Pr_q3CXT.<E6O=BO>I8<a1buvg$6K_`^6Jdpsa&b,?=bcUWhO@","nB9Mkf5pE6`=vFh;!B?<Ey+O~Ic#jUt#jep0aiYuA.W;?]S9WA!]MlFlf%O7Tflr","xF*etru<,SBh{~blh]7~Pk+YA_h3d>w%LOp+$m;mT]>dXNTWJTG+dZfqUc<5ixQl","#~]'0!'ow.*j.C@y*E%Jlo~?h%u=vRLcx"],
  w 35 43 100 620393 620896 56 3684 ["(`P{qZ4<^9'%{B}|bQ76:4@qM5[08-)7<&tWeiYn9(2i8BE%|bq)IJq&m)91mFH?","9S-dVtedmTBD$*gyB7cTx,*Y$-BY#(2I;&QlpXZB}S]mG3skEK+UBVe*AlcR#rXR","J3pr)=)L4tO<9|6sx/iqTwRZ*7v{ts=n((Rw!$K`KLtVG'~sfr8zjFOBF]J!WL&?","2?*;~TIrb=K0NF[p6]<OE?+}(4a8D@6X/UD->#n^vo{i=P^a&/I!$RKal6(2wp%!","4+!75"]]

private def r35_7 : List (Chunk 35) := [
  w 35 42 0 630007 630391 100 7534 ["+oB%NRJd=;iP}Do3=+P&~YzUp)q9?#us(^A<9N[G6sfNN1C=`n4@cH,eQeSap@,s","{{/33V6%1WCT20/,Vg&_4N4c5)KGh`:%$=Z|d<?mw~Tuyo%&IIxbfV1((y+(`Yfs","rf=+-+%CnXRmae).F:F&,+`%Fv04v@Z(sO$h=mx/)GtrB>-k=VN_%{7fotOc$^=.","5R*)*^4_;6rn>~'P]7-oH@ABiBGdLx2%;CI[NWrn1:d+4>?|#2lWK${D@]NMj*d>",",!68+_[tYr6m$.uwLbj[Rx0,:3/}gb(i7dx?#D9PoM;^QRm2^H3&6lg`kDrkS8L^","%ZK>dl*[J7O_6-8/tte_l?F*{^Gj)&[_Xl6&x'{"],
  w 35 42 100 630392 630896 53 3394 ["e/xbx.mhD1s)g7H'n|#V_1baa?%yTN(R#vhmtajh.Iz@e;mVhIy:(^&9c:T{.RUk","A]JI4)vNf^Kl|cP[KnkQ-*ir.dcd}`+NSoN5,k(Ib3T=;I's^abpu7^B|qpFjUU)","Vv9!bgjcU9*hNk{4:^4*(B)pRl+#'4.qblW3~nOem@HAdPa9.)=o9VWNTB'ih?A*","dW9].S.`')s)D(pWHkP_}fe2TKgs)x'N<s`zKG}c^ffa#dD=5F.nLf=yo3#V$%@.","#"],
  w 35 41 0 640006 640390 100 7377 ["~Oc/.7ZY7&J'2(JsWf3yfadIwh!1)o$_k(N'Jg_`,b;~$d3WFiBS+_rA3a-fdy}2","F?RPHMY!?@B['uJ._&gk|+e5PgEcjOtcyQ$|('7R9`]&sAtLjW6Gq-QsjdQKyY*O","-7Xedz?cxKWFAf6,]=XxjFc,w-TBiG*}:Jh.eh<X4qf?m?1?T/7n1U1#N}Yz$7!=","w]ao5rF[W(Nrrlj1XP2^`U:.D48:Ka^h!D(1)`i+mEDV|sh,yBOPIP=*^rQ4Nr[a","?%x.r_/tg[!Xtf-]#bDp;zTv|e'5X;g|~N7Z)eL^=Ub]utg#7V<92]jm7}C1W-Qy","#3es[*HU,f+g+qL>5+T:7<dhA]Z'DC:v>lI!g8sJ$#*"],
  w 35 41 100 640391 640833 49 3053 [".[#6-<5>.;k6udJ[f6[Ut1{gZU'EfgfqF_VF1r`?&01u*l'Hsc+Iq{-[V%n?^/XF","x*8+GmjE|F9koZ?W7a>R]&==J71KPbd;XC)C,}n6b-2Nrn$Rj_|&%]nZ9g.Ts'^J","c,ESD!TaUz!qTmal<kO]MG@LuIZP.([z(VFE$[TzE1oI<8{ps#WOh=PH{0v}?THR","1Py5w&F:#;AA>5Tcg9^rHS@sfL'fs>(3AQJdx}N}lh,@g"]]

private def r35_8 : List (Chunk 35) := [
  w 35 40 0 650005 650390 100 7189 ["WT09rH/1oSM[dOvP(g72CWn62w]B!dywQd03g+}NzHH?|q%MIStj<;+97P%WM,1g","7GGlsy/%VoH~*u!fkKvw@w8}0^ckmW]()yWC,E[zRt3:9zpFxmBl5&pa6UO#)HSJ","hFWQD(I~l6j#'r!z=lBynR^A^l|(108g7c&:Oz82so_7&z_%ttU(9w/Kg|G?;-)K","-<pMZ_G5KzTG0s^4@xS>[!idVLjZ#u'J,EG#>Q;hr<|U)Ky}@Dgo<s|'(+Sn2#g(","{_?VzocyUc[r!W7xR5Gb4~.r|d~]%{~S`B6T/CWsJ6mEHFqrP;*EUy1t|edK$d|U","-t.BoHAO/op&CI%PY|8>El7RNd[zO3+cBAb./LI);N{vn%@i^K-"],
  w 35 40 100 650391 650832 45 2732 ["&9)ur}.SEYw}`7y;)%E[kG+~<Bu83:XV,H0q/{/<FW?;##IKF>DdI$22:w9z+hag","yboUjYoOci%!=Mlzm]K5lW^#(tKc8]l,d!!p`]5oX,jL@K`Fq0JwsJ4Q_EW%8?of","S*p7u>Vy!7W#V';0XGzP#n~N|}%f5jkf4-pW*'}gEy(KhMS]ru0lab<$tPOM!Ii|","#~&(GVny7W]A-GV>~8$fATZ9<O98U<5C*|'"],
  w 35 39 0 660004 660390 100 7005 ["J$2#zei~x<uD'e@fPLCu-.a%og1:n%=a~o]d9q$6Ctm-)zC8K0'XA!c69U>H}]+N","VV]NQA+bU~J[;^x#XyxIAh3wYWZAI*u:QsN_4}aR~ibx89e&ZW:/N47r3L}DcrPQ","q:RPNt`_yS7l0g(8U.0e*M4Ac4bbEXu):NE8.XH@W.#c<LIIk0Y%'S2Qf6#G1G_/","<]W>wsS`KjSp^[GqSMejhD{es#B%#Z6~g[RdAFPis]|,==jq$ppE&V:g4*fuy32I","A(2hzS1KnEVmYWd#8D4?+s8Fm$^:wdYf?Vok>/SzItws&`I]tI:B{_ksYE)Z!5Jv","#^55t3+U=+&WL9E{{eO22Vgz*c?7EV~4~#IqNrJd2U79ZN~RIg&s423"],
  w 35 39 100 660391 660832 41 2430 ["{XzFvJz^4bFrK+^y#umJy/RAp4z#iwOlecc*Ny'h@@W^jCPDWs+uNh3iDBDKbe`r","U_>0qV?;D,R+ouO}=5_*TQ8$$T@5jQ|?Y^ur<H4bZ1oDKYYvAtzGMu!{OoXEcW7~","_Qvg7k55Y#lmjjbk~Ix1&':LQyS}jn0aZz]DL?.ERIkci4!WNgSD.byOZ5py,O>,","E8sjIW@78ia?s@F^){w"]]

private def r35_9 : List (Chunk 35) := [
  w 35 38 0 670003 670391 100 6786 ["X{-,!;Uqgo<XWah]&M{`LVH;gvDJ_5c<}sp1{}IE:o(fYKFK:7W].?)w>Fd7Zi5w","saO^+9-+po{6DQy47DF9#)I?BM)9^9$<>^^W[#tXvW55Qm5mBFYU$CZa+J>pDl9l","G(DAr*n`?gw4XqbRhGyn6p*/02]XppO_hh:VxY,GW/j$Gcj5w]GTIdZftH'-}|`-","xsd`Y]B1~i=a--_+b[%,TW6mWrKdq8{mn?2lcc23SoJnevCw~QUAQY_<)I6_bU`j","<7#fm<f.,vRy;-dAQl|EzAwr4]PT0_/#H30l6+rPt%2`iNP49[8mT&JR8g*F!|1n","R&l}w2>M&~7xP|f0#s>q:{~}4'Rn^~fp@k5T':ue$RmCQSq*Y[@ctyYM9DIvFx[&","$+@QrRw"],
  w 35 38 100 670392 670769 36 2084 ["u}1D18Zv(kiZA)v@pIH2HC%ricuE6~SbFV'weHi#7%X%`xcm`):c2j|,Yt9WF<].","Lwc5k7Qe?PXH[HRW!CY_-S+Gn?UC.`W;q.3G[n9)M&n__I`Do{T5'<)p?#VNy~i.","-O}BZ,^8QbtH`:as:qtiyJ`M]LoP,%K%f['1,K`?Ao{@t-hi_-g{O8sVk$b`la"],
  w 35 37 0 680002 680392 100 6576 ["J'c0MxLCWS1,<OEXv`sa`FJ;0(DK@L#(iL@P>`}pzu2V1;{wSLwg?X9w5f.z(1W.","GAtA/umgrfY&YKX5NDsW,uruM'[MgUoID5`JK?O$4KM;){iIQ|&0GV!sqn%}gU=l",":,KjyrtYHwxN;{nq_Sjw)2QuWT=~x<;FV0pxn14DoffYq`14?Y:p$d)B`0^@W~ts","kb!UCS#:Z-:(kMZ*4Q%<Pmu8Yv_r[ZZX`$.Lo/;MZa/%m;>&$5fe>_{xyvm(w<V[","~ZrCvY<mR~;r8h%<aPqGRUdAzLnSMs:;-~e4kV;B~~HB7rBGAfUJe~FypY!}o|'+","&BMe_?9!IKb/=Gh_6X?2fiKzVPwNHW|mlo-`VqBlL>Z3(HG|wGqU36X#n]u7tVj8","KnC^WIwr/{wjV.:"],
  w 35 37 100 680393 680768 31 1759 ["=kWKiuw2KGoHX`k'qnQj:>VgS.z6]+9G3L^V>f6{SUkTd3qZ5.E=02s'SUx/,Azs","tg1#C-J3tEq5LR^6c8jj7oCYd&o6jD'qR)6M&:rib-lyX~ujSl.1s-S&v37`?/,5","%V(*GShKZe#6dPO0ylo00f043hKEaQ5$ADNju)(E"]]

private def r35_10 : List (Chunk 35) := [
  w 35 36 0 690001 690448 100 6336 ["+|e-X2&k8!tRs*7FaT[Idmv+Z3QX:LU~q~v..8OsWF[<_bW}FLKd)<TH6%0D8c!*","=-3q-3=OC**k?*vUF)vO7sDW)aY'L3%^XLrEpxP!K/K5kUfP}{q]2BXMb9N'Oy'&","A7CSe5!P|Ve2m)Ls3&*4uFSbX5&g&.ANo'8hTb?^R)))Mv+'HD3WGxs5[R1/c4B>",".e(.6599}]4HC1]feYyjlzwMAX4i04xG9TQ]}pn&_mZV85?u3&qX2B'}Z*ZV7CX_","dfR$/J)Gk-tkSew?#Lz];oK$3L?6,D*,JN5Q?w6YK'e,5/B^y|lZ2yldz)_~q]0K","zFWKvI461e^v2CnV#18Ez-A;b`cTq>mtZK0cYiW$nBpZnpi3?OOpEZxVm}Zg<)/9","e6>M}DUb8<7o*12<BBWqq[P=Y#]1MX2Q"],
  w 35 36 100 690449 690768 26 1446 [":#km4=:FlJ#-dBg`UorM5[&<//itJ],~,&uU,vykBq7/Cd>Nu:/MeGgsL;vH}SF'","^@_ueYLK&_C,Fz2tmAsTe{AqXQ*XrKsyC)#)'Zt^T^{3h]'f[3]8p`h-y3'V#d.Y","8[@bWs/I;d4BTL"],
  w 35 35 0 700000 700451 100 6105 ["0zR|`o&]}#TsL4u+TPO2K*,Y+r]rIZOM:Q`DG}w9'PcUgm>[dla`y_46/bj8@JoZ","TkbX^r,$O9l`O2t^)JHMPfzx7`RsW)o|$@a.'r?C=5U-Ck=LO.uPe!;w7s1;{XuA","X*p?Wa*OlXy3S8uL57VNmbZ~6p0^-HJh{@oFJ]YO,|(@CPU6!^mwC?JQ>~-T6:WR","h@4^K:Y}Gt<&>)Y{].=8F:;F&s~G0&w)%Pl0=b,<7#qSdK{I?_vZEVjw+&.gH<RB","?<xZ:z'Cw1o(vHE-n,:6VJlvb-6/>eQ[FobY`XPo/#zS@9vslx;0vDj^E8qX]Vt%","=Uf2nxGdM*x1uG0m#d+7R9jhs}c'&EM-p:8+i1^3b:ih]}35/t<Y=G`OaS(M4^h6",")4F&|#s!!|H$XXrom4tly'#&f7`wYMG)e+Qq1e6XQBLS3#^*-IHL"],
  w 35 35 100 700452 700705 20 1093 ["3g(+$BQKQ!92X9Cb}{pxxWNJ.S?q[9K*TeFF(MsHHT%a_'Yd?+dVO4480%kTa8`[","7}vG8=NzdaQb!mmAU~Gmkukcw[]^)?Lty&N]-&=Yg]}D"]]

private def r35_11 : List (Chunk 35) := [
  w 35 34 0 710000 710454 100 5844 ["#ca'Wx*<;F*Cp,#,@$=cf/KZ(Q$WVmGI)2&Pawzj<AM8`xWdWD.2*g^UJb2`Fbj?","XAT!PM}`)Wis8t('~48v^F`rJE1yc:(pN}TDe.91h#[*?oj`{V&V,j|0;{+wif;f","`-R:f8_Wq`p:lm(%Z5N[WcwD?3'zLZl>|jEe}U,.!!p^|Iu0$%D;i72#gjK3{I/c","iC~Pb3nr9SlLI1>q{Yunky@h/UwI0c3vA429/WloSON0GgHj[4~_2a$yFNV`ORgq","77]QR<xIi?xL[Q0.U1&NF2U@s[l<]ea|9+>(8rJoA@OAr'BLW8FAtULKpe}2Lect","<tTYMoL$RZ'BywPD3=v!.WXZM]^-n?AUTqHPfU.F&,asTdV5oG&Qr91KvH9EsuWp","8Jx?o9P<'(QN1@XGicGnKoIZ+NNl*nT}6Z]*|':6rESw#dB|X{(v4Fm*H0kOtTaX",":EgYg"],
  w 35 34 100 710512 710704 14 755 ["A(7Ims%@3e:#gkp7b@19g#<|Gctz~fmy)y7`)w{H~riY4=3'Dr}KZp`dKk-Mhh@N","eD`[cln?[u"],
  w 35 33 0 720000 720515 100 5605 ["3^]Fvn;XLxsa&k8Kz-sIWD}!^F}y@*v1!m+.M,ozN44/%wx,!`T7~0pr.kw(+2T|","|NCaTL)IW{p*/>.&r4#{q[.&OPI_0RAxC[hdkOy-U2?}u0Tw,jq1^G)bj^D'3Y?r","g)ZK&}7~XpLZ7{CRmN@$vm-w.jET0S|o*wGjfNY|Y]$?BBoI@6Pkws{CqO.Zk[Z2","SS-@^wPxSbvq!Z1=lD;)TvD@jr5=E$a$1Ul]O9`%K0wv^Sb'?B*M0AS_4,x{f*pD","#DFTs$j&#P5cjG|f_=eJaC,Yn=_a/8BOHAje]ILu+f1?(~#T-Oh0@99A_82*MOk'","1_Pd)2.[.IH~XTw2f}B1G/+.ds$'',v:q$NZ^t}/~k5EAFBX+IM8aF=77.X{6Af#","7RK#C0C{ZL.))DSxp'?@4mVzK*XXzo&s^<_IRLG7vb#$Fw/]9Vz..`>,&55f={_x",")c]z3Ajh>Nt#.EcsTHdY<ue)$O"],
  w 35 33 100 720516 720704 8 427 ["$6H;MOWgwKGn;R[u=A63sx7g=KM[9,wLX7'[t:"]]

private def r35_12 : List (Chunk 35) := [
  w 35 32 0 730000 730578 100 5382 ["j*{]M_ex@7>,P.Fq'Z8([ALCV}+5>vdb!pP@qP=(-|/v/U!O)Q,^{6'?T'kN5[Mp","P4um7UI_xOSk&+`YT{Gkxj:x0Lu-Xu;o93Cd/6,91N?0c$TwJgA%1~H|=4Q>=69Q","C!UsaQ2tB_z^WOYXj([w;#HQg([)&jCl5s^j-C_`ScB6;6.~nH7@8XQqp/D]Y9{w",":r'2!qCx(tU`h@IP`X4HQ%zyA,O%Xk@j8H6X*)rzqG3bxDX4~1[8CW_Wx{btY]T=",">FXiP>B0Egi07=|)$V>$:n|A+zRF?>xHfs/~k8D1PP?l6cD)2+UA)[f~;=-8_E$a","Br}.3osVdy%JbC`cQf3t],r]zZsiKin4fi5xB;G?JxUnhp)%cO4RM3EeU-vDeoLt","%bMWGw)M)x;;25;6+V|vL+IkV]qS!c4U,C3CzOI~fwaqknLo.eLe:=5ykczh2X4q","%f}qa!Y|ER/hKS]/so*t?+Fw:yj.K1es^"],
  w 35 32 100 730640 730641 2 106 ["&ajm2vw1A"],
  w 35 31 0 740000 740640 96 4981 ["FA<)G4[tmY}N{$#X.,^yoP'>g`Gh9+RL9r`|A45h{zy}r7-DahZjn*9)X=vnJ!][","R<bwZSgCKXaQ~E7]]S*DTO8#<O-gv*jPYWSpJd7fBbah{`aunxBAHznd:)kA_~!(",";$B{nD+S0S2+Fs!#?rB&z-TEty`9Ab4;~+@vxxgGu0}zqP8OJP%.*;OQ7])4f`PY","EwyD3C>.tJd+D>}.6S?BzM>}LCvZ:7w6A^fL&,!!c@10.?Ur_oRB8$IjB3$X]Q~1","Y,|zZ,@>puu5h|s'Ii%&FP)8b@(?xg[v|%u%W87&[jy*J|({:Hl@PeXSV`g[,J_i","{GT5Iwq}mV}NZ7}k~NJi<B#MuyzPC&gYVG^)kM]y<<T.q&Q>!Id`9b^T:;8B^dHA","9&~+nqN^3!o2TW0w70Q+PInF>[4wD(|)G6TXIrpld6aL9#4p$6PP8`UisZhgM2'l",":FI;{]uMXUE2(p704ZG>X?Y7ur{GAx"],
  w 35 30 0 750000 750640 91 4548 ["aG;)]Qf<5(|QSfKf]-[&isP2^DGTLtq|#QeWhCA&_+X_#hW]A/76_nJ.rmlhTP%?","ucGE_^eK/l/&RiEn8WAf/W6kR*yjxl7w1wbEGjZ`~XqvuN4A:v>T9kk)R4?7PEI^","ZXWTw0K{MtO3Fpbxz}c!}r[T(!9!ydl(1+20mw/q4sQyw-O?MC2EdAE#rG]W6)'h","dBi)4.F0m/-lK]:v3Is9[_a4qzSYi)OAZmtgF&.m{_8pCXu>mbT+-../M+gjm(N7","0R^!6v{9i5H19_eh~'~O=i3jWA1>EV|%Y>qA0onLqqxXF'H|Bo1_}^0ddh0}B?=?","Bb(vOICX**oa'5KbWubS2lUgN7_nqkzwV-]'GccW]`Kd5LP*}{)w9s!$9JI9aqq8","&X@8>kz/1A/v-hwn%sJdGd_#BYKi~tgiIa[xiF8Ci[V6g7<+SFZ]TcC]Q[Wdr{ET","$Pur1S+IV#^"]]

private def r35_13 : List (Chunk 35) := [
  w 35 29 0 760000 760577 85 4091 ["Zbv]#Tln7P$T~J|=odgn$x^JEv0e$^<[?$]m#)3}I9AB<Yi2=SjFsjUgzrU&J/LK","HC5j]HcMX=L`{te>Mpk@3d6;u6mSbE~*/<RR5,.~q`BV.5tL+,*](@2[?&M/%ejE","r'gp_fOAMz~>.q4$l!_TF=JS(CWrXEZ&t/IMX{A889<7EY>BXLaO&%rp2|NiNN?}","Jb$ZbnckioH+n0LVlQWQ&iLOEqE@:lJ8Jp&#^U.s[IO(xrh*~V>(;oj0fmU{/`=C","*w>jYEfChwGw-%N.=-W6zxc_#@,/6T#M]oxj!+B='nLXK+aHh+n8nG-xek3`V5Rv","TlzHM9Kq:2(SRKZEWdMdROmN'X9Moe7v%VsIix^O3lcR$yNl8!#BV5C`}JG[r?OD","1m@~t&*.m0xeLM,wwGk[tNF)X;s<N/WD_5TV9HS{yP!/;v:d#`9zBh3eI?["],
  w 35 28 0 770000 770576 80 3709 ["1#x3nJDT;dU1rGkVpRZ~Ur@a1p[EP*ua94G);Ta`Mz^mVFkQW`?F?MaGb`zb'bEp","kpE+Lk@Pgm+Q0?yMdGXLT-hJ7vxEE1M$5Ja^'p]1OW+:us3^O1N|wP*0YZlh%@CI","y5m;7WP`Z2Q;$iGm(i~H&yThy6n)&b.4?Y(AE$ue+IX-y*;o[/UtwsKp.t'v=e*i","X<0:bQ5=xQ{|Yl(m(|^eN_[^&B|]fUUmA{iQ6Y!UEiqo2^yVIH'LBuZq.^[f*vXx","0QjAW4lp:kVp~ZGl9'~3QrOX|G=89M|a|Je^vdtXm`T&@8usC28tVX1Nj#v#DlmQ","^&)'7%ikQA$*W0VdYWeI^*V]<Sa/XD*x-#uUF'=tC;Hfzfiu>9.$Z7a*BB$Mq?!o","Z7.<;pIXTCN|/Dr2J1|/`,4(M>YPmrNU<jr<oaY>`N"],
  w 35 27 0 780000 780576 75 3352 ["w~<P8EWH{vnO(tha>~>6{#zhk*kz>mkGzDp~m`SHO~>d-XF%e.{!VYMr'suZQmn`","5%F@oS~[ff]^a+RQ<p(}uw,%tRb8w<I#h[k{dT}S_Q*IGPMt^S=glS|LqO7r%fyJ","uk^GivH2=@!;WM7^/aEjF!`U#&pj/mKa>@(Lu20~%%NzZg+Jy`Ad9YnUwzrZli]`","l0[O5$[JjW@9nqIolG0DZd/ck=9,;g@&EgYU0J#,DU[Q3LEW'wt2lA>x{:x#)&a$","c9bC-G<&#F<=veU3vIh/%aqVi4a#5z>rv64Wj+:<KJy:cbzz|0#)*WTN'`.X^[8w","I(PjaS5>KnWA5^oFUC%DRNIpz^Ev44{`RZ|>1xv(PJ3]q)j`OW5'&l{<[_&6R@g4","Br_#NUj,2Q#&^jd._G!ZhR(mRM"],
  w 35 26 0 790000 790513 70 3008 ["sZt:{}tDE</>8B2!4W6*H,A>I`YgWmH@!^^;d`_;*,#6NE*g%Wh5NPVfdC.vY+Mp","Xwr+gdu&SUjZF`:T[Lbq?O{aqmr^$>DukxlC4F2tZECs4|Iz3>]UmC|wn=Kh&.@4","oJa{;e6/.@x}wQ@0EF~c@:aMOd|lar&^J&Zyx-R^TV)b*-L#Cu@7!&dWHgWH$ejp","+H[Df)]42%{%o_l<FFsm9$2LHR8vSEi|1ahEfR.qyUx<0m$,=[o&MNc@j3%~=TqJ","PvaQWeS``,=1{GuS5HV5z7.fjN`6v?}/Nswn(X!QcY]ZbEw+Or`{7cP-%_-2<mf5","5mbpBiemQyq^lbU?2UuZl{:4X=:}4_,@<d3'$|u463gHCkU6TGw'.H.`rQmBnJ-M","#0:ZD9z"]]

private def r35_14 : List (Chunk 35) := [
  w 35 25 0 800000 800512 65 2691 ["SMXISa(z>hdb?c8P*`4rFdZu6TdZXPT+Gn(-AzvdvO#hHI3;g:_AYZH:P)lfps>d","6uC_>JFhYd0ir~5F?QRy?4Wp9Lc~;fB@G_@j?]lIk/nPT|Jgs=7lKcO#gS}U#pKI",">ID?o!$V$RcA};z0(H-@o4[^cMXs<`L^R{cD|1yp~BwJN^W}q%!Z4%c4R2]V2`FS","TX5?*(m.GrsDG$D{nOZpXX&O^.s7)an{c!(?D83lS0!_xLfa5:vI)XO$*MV(}%nR","BMax@-ber^J|n+KC~3XE<S%Ixq]]#vHQZ[rw?P;=4S+4T]=]mKEcLn<U49z8vQ*k","{kI|s--LSFZhwDUOW-.AZ%}V~%ojCk9g8B*rO7WkF;,S9k1mAh}l~hbtQ"],
  w 35 24 0 810000 810512 61 2429 ["6:Ve8X~d]9JD8$?u'&S$=RG?e4Q&D,3EH0ibsoWny&8VY?9vZ{AdIplwS**C7ff0","W@I-;.NMKdJG$BXYQ%YwSj/J6H9sC,.'qd82l!I{T195RxPZ=Ks8~r}l1jd+sHw%",":7]R_-^CN-mPYG>;L*}7d;Tjz_RG{G(~c3(7t2kbUZgw8x_$.;S1oV30)WbV-pEb","H3'<(N~Z&$/,?I+V]{[$C'pn3FLf,:,-.gfB65tAhGe@y0?OP=&Yy[@v*Cy+O&FE","422R=IUV+>n0+[jDlO<3@^,qvUQCpxz#7$w%y&L&AIseUyy'})*i2@Wb]y&L,5c.","*NE*j7&D>&o(;+pfO(N,y;tNz6BXm{Bd3`Y-O9ds7S"],
  w 35 23 0 820000 820449 56 2143 ["DDg'3!tbCY9.B81pzVpl%KD1kfhtC{QX'l2o0pL3gL)ITr]i'sn[@AK<P*LDE,*v",";p+f{w?fJkzZAo%gAW!WEq{B?iS9[+Q{e|qcLvd},cPiPKa7Q11q9gm,utZ((#4+","{1T<z$m4ix^GHLi4;Hxsu/%=$'JnOS[2~WU3z2iu4tTPFA;'*pjAo8-3!U8/l.je",")CfGKaDVH_+K?yS?Q1l-nK6E4hXZo0$5+<(V6VR7e=ZNWwWB[2@1kH^evl/a&i9g","u^z!8VOd^*pJ@M_D3Hm?mt*=0B+D1/+z*FvCDsgBgFG`Y?:+:9sTOUoB[Uw^E=_]","6|Ef/HPNoY{_>++WNuf<I"],
  w 35 22 0 830000 830448 52 1913 [">M!dZM9Qr;^>?cH#n[:]pi_2WW;^CHM]c}-l))JE+V#4(~3AO]FA}x[aSm'~&FPn","]*;0ggwozf9-8&]/MD5S-S(Em`yN':bILfSIFG,LKHTN->kdKn327!+F}}dnh[Xo","2(1bG$6SWL,)HUL#;N`c0q^5lH218sWXzv&]%b6>7<|_?c~8}-+ZL1nnn/gwC^#u","s>3T55CeQw3.,cv,RyNKOJMDH:F)3}r=+`;:y'DqNu=<Tbi;,C(&)SQjc.BO4+7'","R<BlOm65HZZLz|#H]{Fw8n$7^CoN/eCO6;So?[labcfD:MNmi)M/ge1|R{E1u|`Z","*5/$C+u^OnwR"]]

private def r35_15 : List (Chunk 35) := [
  w 35 21 0 840000 840448 48 1699 ["[fW%7i=$DK*=3nPdZk;^lcbMnmXZW%=.#@GGbKa2%N$z>&@aBs)Y;SHa4o'.9C&v","VjAl!;;seM+[EF2Pw>q+o%]OnOLJe+G6P{k=RC?O-f;/s]}]2JoSAT!bZtgeh[t-","#r]zg$JVl)D}aL+[LD%c@bkv=Y:ia@2Agb^6Rz8^AC$^K.@0uPbO.Lmk9![V@Mvp","Nsq}Gi;^NU?Vrm5CMmLR>:pQMV|IN]2[GM~sV9,s<tP]OZjQj%1$59IEFv(SybxB",",nXoN33N9n]b[AMs+Hb-[utGI0_:G!65j6wnU9wbYV>vWkJ[`)a"],
  w 35 20 0 850000 850385 44 1493 ["vRrYR%GkF9Ma$?T.Q.Rc}Y(amw?HM6P/b!:`;8QISTQP'cOc73RU%<NTYXy;_%+A","Nb<XFFS/vrTEYp(oY[[QtG?`-)X1])[M(mDyA`*,HO6|>::G?}Et5r)Al3$Y2HjU","&)_8tLwmVH[iY%[vz%u0y56A[F%r8gF.K4T8SENs9QAi+L@f%F4EWm+|h2|n]#/[","`6q}Y$:wmTTV<WhFk$wZQA3kMru=&je+5W!DPxKrQ`Y?}IQ_J$'5nHk+@J?@j]5Z","VOOuvQ]>ev4=W[-j}(a)r&jhfooa<"],
  w 35 19 0 860000 860384 40 1305 ["0$+L_sJ+t*n8Y2Wr>CJnTb|(F|5.o=okE%~%54Lu[k8shpAoD;:Oo!i!)EhVQN!.","4Xqvj;VMXY<cHs2(FxIr`5vYEQF*j/KoCG~]:2l7~%*,$S{<yR^kVd*Rp~$XTCL-","/yTG]@dkK*FfGmwbjLrbeam}uE*DHHx7{g4je-Qw4U+^:o50XjBu7l22XWL}%Jax","+e?Y'+'iU/!vWRlBtTwQ#e8Su`lWL'ip:{qcn~>E#U,W>]uv_|-*>eFJGq.o=v~O","#L^H]IB*O?/5"],
  w 35 18 0 870000 870384 37 1159 ["n%sK,T3sTPv/%4bw}%AmiVu}1FdoXq]/A|+:-CC5;v^fgtIq@e2vfs-tFW;'A_?A","8Z/*s'R.C/vr1-X!zzqno8Hv=R(2E{X$F0IDxNG~M?Qz2_uhQR|/[4Hyqoa/_FI5","u8q!1l.OO;SW'kwyC[._<x>Y_ZzWrFK`V%&@]WJOC?<b6~lb#T$nRQ4Xa!N:'W]}","ZPQ=$R_3<<fK[+G,Ni1?[($jOdbn{ve527l?PM]Fk_TZ'(MDtbc6"]]

private def r35_16 : List (Chunk 35) := [
  w 35 17 0 880000 880321 33 990 [":Wd')rH34Pv$Vv5!HO'/1$n{cb8Y@PeyV-~]z@4H;qa1X0#^[^8WaK[N@3?)SLE:","S;H'W_@>*sL.BX=3|~,,KHVZP-[QG@Ar^vu9Zr|FWq>#f'cKLWcU^?hHOogLGCcR","KzZ;l-fK~XVAh^U>Fp,pCBSK$u}Ls5@jKHh=zqrz>Qg8'p&8XQ8kjuyooE:R;]Rx","%Mc$Zt}{?k)F/J|j4@;*d>3,~$"],
  w 35 16 0 890000 890320 30 863 ["::P-s6l{dP2st-w&5;)Bc?eI1whM9Wq+Fc%]lvqy|;:88;N@.e'V?L@in$UZEC3C","9fh*MR`U?GXPSeg~PDxotbQ<t@qAy}H^iEs%['c%axNgj*x=R%0rA[_%wj6U~}d>","Q-=J6-]4~N2ZR?e+tRd~?%75E]N)NVYFl(}csXAnR:.+~>b}nSfeKh*,3{H}j83G","2cP>_V`^E^p["],
  w 35 15 0 900000 900320 27 746 ["t^K4+baFNRx7/#^J9{>19ZWXY*$QP:]!YJvs3M^Sq>k4T!ZY,U2$N=)gH'(eF?nk","+^u/{(C*{wQhBZ*eEo+m{A~}bf3v,6`:@]25?o{%l]KppZB`(-Gu*NZuIGKJw2^?","G']l,Kja/a0$_jB7<CYXe+DV*y`G7TJxD/>yPVUHu$4;#Ypid"],
  w 35 14 0 910000 910257 24 633 ["?>)7wm^Z^&V)[]/0B?(#.Ni4|xXlfOIVXTyQ7Gw)R7~oZW)|F>ie(T@:fmr,I6CR","3JMgS4M<tA~5<0^'5RwuHk!<-pT`iM0u^{K~+mt2DI&RMc@Q4N%CJis[YL@J7m(f","(90rwk'0x*)F`L[lo!nai_,oCk$SenPpQ"]]

private def r35_17 : List (Chunk 35) := [
  w 35 13 0 920000 920256 21 531 ["LIv++DVh:.}Seujld`GKJF0I$AC53$E:BcRC+wC13k2XGqhnwwZ+12M]Vq/N=5Gl","uT$]G^UJ]V!9hG[d,k+'<'aea(Tb$@Xt.Czo<}kW].?.gdc<0&8M*Ua315!2NM(,","9nbpq!U|JTv6"],
  w 35 12 0 930000 930256 19 460 ["yLD~%`T&)C'Kd(2bt`.J-1wd(Jmd=_QejkK8[*`?~!3k'W1=giC?TXy=jc9,%|fB","(MA{j$29>!2&?nsqoXORx{'N*p+N6!nWs&BV%PHEkJ;KkTvaM.sK%<&))<8N^"],
  w 35 11 0 940000 940193 16 369 ["ys}(mHij;C+XS&/M1(Y6|}TnWrSBX8=<I`Jgi@CF7+$`Y#Hgy%:00%{epW!M+])C",",tPMly*kW|aYVSH>XR!x&#%@aL[T{q~pvxaPD2sQOh"],
  w 35 10 0 950000 950192 14 307 ["(DP}daDFf0Y8bT_qkpxHZKmGlYsR})A_nM;*bf~'TCXg3(YI[VAStawcF*.#aOxK","T^y|7x?g/|%PL@n[A)v_~%(J5Vn%rd"]]

private def r35_18 : List (Chunk 35) := [
  w 35 9 0 960000 960192 12 251 ["lU~w,SmRtfvjVwr.7~CJ=Xy+trl-Fu;T{5'MUoC&Kul>:MmYAD>.G[?Qn9u8(_/:","${PuC'ZTwl3J"],
  w 35 8 0 970000 970129 10 197 [")sY57)z)PNs2jDnLl~T6s*JZx8tOGT!o#KCogyj&gu|XdMUi:ySmz`BN#vu~9B$/","0Xq"],
  w 35 7 0 980000 980128 8 149 ["%0%WCE,oi*-8d<A-8wAi{{)RTAsU,TytS.5(2|0<>yUSS-wBMh(o"],
  w 35 6 0 990000 990128 7 123 ["#};,=ym}@b3*e,z_!I;J4H%F[=X'3ChQcAW/B#^H3uP3*"]]

private def r35_19 : List (Chunk 35) := [
  w 35 5 0 1000000 1000065 5 82 ["Vd-sD.6|Gn|;MRBrZ,H]PK}]|<vUDMR"],
  w 35 4 0 1010000 1010064 4 61 ["Ha[=a#~b*OHNX?kC]-l=}((}eO"],
  w 35 3 0 1020000 1020064 3 43 ["%QDR]ghd*HKB&E'<="],
  w 35 2 0 1030000 1030001 2 26 ["#+{!`aJAt0JNV"]]

private def r35_20 : List (Chunk 35) := [
  w 35 1 0 1040000 1040000 1 12 ["+`/aM"],
  w 35 0 0 1050000 1050000 1 11 ["nv`*5"]]
private def chunks35:List (Chunk 35):=r35_0 ++ r35_1 ++ r35_2 ++ r35_3 ++ r35_4 ++ r35_5 ++ r35_6 ++ r35_7 ++ r35_8 ++ r35_9 ++ r35_10 ++ r35_11 ++ r35_12 ++ r35_13 ++ r35_14 ++ r35_15 ++ r35_16 ++ r35_17 ++ r35_18 ++ r35_19 ++ r35_20
def rows35:=rowsFrom chunks35

theorem good35 : ∀ r ∈ rows35,good 35 r=true:=rowsFrom_good chunks35

theorem sorted35 : rows35.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks35 0 (by decide +kernel)).1

theorem mass35 (i : Fin 57) :
    bandCount 35 (i.val:ℤ) 56 14≤(rows35.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks35).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 35 (j:ℤ) 56 14≤mass j chunks35))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total35 : (rows35.map (price 35)).sum = 322672 :=
  (total_eq chunks35).trans (by decide +kernel)



private def r36_0 : List (Chunk 36) := [
  w 36 56 0 520020 520580 100 9874 [],
  w 36 56 100 520581 520903 64 6012 [],
  w 36 55 0 530019 530526 100 9490 ["'$C{yx<0ff_YfbW,[TMKJX]?2tLo=/~'pZ'IYxJ_yVPtzh1-9=kIuY;{5&62iNrF","8y@^V/e,]k{`W2Z;!j#n!,004kCo3I#c*r<@55!12q=Ozt<mHpi;kM+7%eAJi}d7","#9sLs=bd2[YYqZz/7#iVzgQw6E{6Vg"],
  w 36 55 100 530527 530902 66 5986 ["jB*&DM%&mfWpL4:seo]5^dl';VU8KtRqt{3B?!)o>)|l_9CPZ*[%cf*29:_v]25h","+-Pk@htt-pi]:vR7xR?oBENt{,,gho$Ds[t'7KmPe*'94Z"]]

private def r36_1 : List (Chunk 36) := [
  w 36 54 0 540018 540521 100 9264 ["Iju5x@-V*bq8VM00PoXI)T(HI=,cCT7?6AV2fcNu2z^<hDkEIg09BV_i?[@b!!I&",",+PpJ6vq`id.A~,i6?o3^f8:(&{mM54a@Qv~'Av|S1SHSfm|>GqA[T|~evuFHT^-","EBYw;zoQ(cJ4-:CmbMCjh7%3&`eu&IvkNMc/lg9c`DeI3#YT["],
  w 36 54 100 540522 540902 69 6044 ["+,5LU}1-pZ<KyD&8|0H6MiWnjwb~[}%(!M2[Mt5;>CYszUhLmu&<9.j>![Cnugl`","YGqe@mT9^{@-4-i!jdLAhP=z-%`/d#BZvPNU=L%77mj~gVEV_<UNf1[D(nnlK+YB",",$=]0*>V"],
  w 36 53 0 550017 550516 100 9057 ["j>bNAuo4GJY,Q^52#t9c04yjzUYr12%ym;(zf`_W-*nT:ba$4Qr:I|$rWi(ijE]c","3}'{xi'>VIAjJ%H.6L#F6Gn)b3c+m=V#U}2FpEGbnWE-F<akp|?56eli.*t-)dcH","i4eHZQq58hP(k%D;=L3-yb(9{T)4[)d7}v!+GsY]A}yj(.6OLF.So|r6y}!Q[`%%","(w57/('EHb<~v1G7Jd(q-"],
  w 36 53 100 550517 550901 70 5928 ["*8{-r.Sbl4_=0tx?DqNDM=HT%:r_t>B^9:p[>]A(-S]<L?[tN#RXQuIWnB?]P]_+","%10b][*qfV*#dW9MeGj>gMo7GuvvyC|me`Hr94nsf<t!=8*A#H_RP&[8gs-%:z<p","%_77N]9I_gJYvd!rq*d5|`C[~hIM)@4:[!{}%8"]]

private def r36_2 : List (Chunk 36) := [
  w 36 52 0 560016 560463 100 8836 ["Qm6No1PyZN=4YYV>14i@y:fac$H{pBfr{4JE,+JsLMP]v`4ji*4EM_Rdui@na&$2","hdM)O=mr$a:egK@xq<{'{!V7fS6ezFWh674h/CW=N)5EdSBb7^+l^qBc-(PCEN;[","Iy[-W8ZyBAQ:b[qv={|?hAFO_JxQ1I@i$C29@RnMMCE#?_1qFb])dQR39/XJTBqR","A.l<d#+[kHf,2I(_J[XN1Rb@VOg<(,qHOy[w>Aw4}4+JiC=(Du@R0w/"],
  w 36 52 100 560512 560901 72 5961 ["dO2>h5c7:)D%ZK^F9cPJNL,_[>3*KA{GY])z*d,:;+V9eSd%T@gnMjO)r~`L~dk{","BdOqLyem2/`tpGe6b}LDmB+%hhQ?;5nm@kmqv~uau%@3^M!)F~h[yA;UZ5dhGCP_","#!2p,RbFoW/D4q#xQ)CJ<)NvC|K>ik{&ib()821W[`]:7OBc[q*)Z{),qCuO0wkG"],
  w 36 51 0 570015 570459 100 8699 ["Ql9Cn}{l'}z#h6&g[GfcDa;/zT6Vp@R)YkNuoV8dn@LT=Zaxu9RA%9e=a+~#6{yB","s7F/C=eqbSq!k^Q@qN)>z[u|vGyVJ(6':<U0nekxEoTGXj5a#/BH(/a5M:T_3$mU","$U}*[&&c;_Lt=V/h-4>EGPh+_dIy-9YV%+%OWs1Al(0p[9P0uT>Sf=2i8D>7#ULr","|6w6CbGOH^&sC;7x3Q1X<55|BoV@a.Kl3&ofYb%N/IX_l61!rlD:J$[0Pc[>H)!H","Z~$<K-78m68*lP?!^Pa"],
  w 36 51 100 570460 570900 72 5759 ["&qZKf&RBEC$XZr,zz:/G5@EycO^NdnfTcgHwokz44QKe8`V?!Vp4?R[1UDQ`_/'8","sIvD^:fqJ%|%1q'hYgXg|a:W|*I2czZCV]q1y'uYjH$@{l}fg>w:NLvP#K!$^*J|","6u;EBEQ9)~=pd:.MA%L#>d{Lfj:eTUCtpf:THE0w=oL!UMMdnFEtK$kZ/4;j$]zg","i&md5>sS[$y4ZimH!pt=F)Kw:w_"]]

private def r36_3 : List (Chunk 36) := [
  w 36 50 0 580014 580454 100 8587 ["gQ3>rH-AmV,;rYtp}k)I_)FW!%LA_wTOl-'#LJ:O^,w.@zRx%hFN8UiK/mM}JXcJ","?/}n#z|_3O9EWB:ryIBmH`QIF(UR_);ZlgG+Mf<$z)xQJ0[5E:XO2MV,J;GMcB5T","Nc@1~.$[X`]}K:c:&x9tM)#IP+RLw5bB{uH,2/vJx9D)T~r>'{/F*#],*,!i/'!Q","yc[l]KK)un9#I712L%x(p-xU{svZ$l]?#fY&O,G=p7GDQy.;G}iMn][Peb7UTaY@","#x;EjqfuOE0]6^=wQVrrpL)3]3e6)P,erQ=L+ih]X]"],
  w 36 50 100 580455 580900 73 5661 ["7[^GY[?4*jqk_1!UipI->'=r_`6+doYkvN%u,+0vc%/Li3q6-^#Dgt94z.i|!*L<","U7Qiws-;CZ9JPW_KhT9U`-;FOg,rp1;BRDI<)NV|p6@r{,8/`*AfZF~@9In@HjP*","($PEiq4PMoS8XQl,kb$9!u7h=~RyhSJ`$(E1gGIrbA]DcoZEjc(J8YN8Lh9VD}J(","%VvX,A*Nq2<j_q9K.zTqm,w5Q_zlCh<m2o(R'9UH>NQ]H%M!R=_$5"],
  w 36 49 0 590013 590451 100 8452 ["@e)iCkw/lTC'7'qWs4I_}?x[_zcUIH7p(0TyrqmECm$FL]Fplhns51@'xK};o4Ag","W!Yg]`~Mk4|JDZzQNu=2yM&s0$<HR>'_pQwENny*vm@o5Dg'H5{>g<US)7:ZcX#~","!K_=;$C=,aD(z@Dt95%YsT(2,$J|kjCv~NU?^c6>sFwNM*6;HCZ,##1{AvEg{AIY","`?IYTH|6Osb%,mqj!<CRg'd2!lg0oP[N;.%fvv#Yo=tZZPi#d([PSx#XLt3b3Gg$","C-<Ft=xqtn}Wt0b5i<yFN}7/Jlue#Gq#Xge>Yts0:,OOD!H[S>u-K-it_hjgHS-X","%"],
  w 36 49 100 590452 590899 72 5429 ["L>?{v0o8t_DZ4.kO#*w[x4*WBJ`$RWTfKvhhqaE]Re+G`FjS0&4F10|G'O:9yR8L","aXM@`/o$2;u/F-Szlz#X2{Qq}Jn2RAZAC($Nmyy,p<]$t3'/5^AWLO_X_F(]7aJ:","@oDCF>Ws]!Zdco[p#UbE*i9m~pQ6D/Y&U?,ZOU.1+Yh!>~=BbhogXX+^lM$sB!@,","M~|d{|!W~5pZ]'WQV1|W)TuG;l&:%#(;Y2kblc-{c[x4LfNE1(1=!Jc0<oHyoD5K","(E!,"]]

private def r36_4 : List (Chunk 36) := [
  w 36 48 0 600012 600399 100 8290 ["}eAZ?<Dc4LOnAyY/#l4C2OqvGHBv[j_bTtnNP.T1g!I8GDR|[cfSfUOZJFqMTc`>","v^kC`=Xn$3iNV%U+6K9R9HYOiQQBP97GHAC6E06-DvR?f)!y`G7vw,{+p!zT<6@U","<%Ov,F!V;7uz3q$.(=9s8Rb2M*Kni&GSoV-F;!!O;]mu,#WD)+rgz_EopC@UFZBU","GMYqR@Z`[}8;a7Lfn;J[Uc@{A8*`2z/o`}$JDChej6sK9div9?@%#M6+biS+mqvR","kx=a{$|ENSgB[W|;uBrOcq]ca~L=_'aKCR'{Pf`qOHA<AIdDX&mwb~kAB',tA.[8","$1#Hof&79+sA]`B{Z>88%!T1,|Wm+nIy"],
  w 36 48 100 600448 600899 72 5334 ["~xW+Av=ckoVO~Pry,R*PR=:ZH}nwR=%FvDq.6=R8.M%I'ceEjhrUI;x,#OFZL0#x","@$i[=/G9,edHnRcLojr;O(X/l:{R${wob|p~ndu1S([$]=V5D7SnXvKkUV;fi=:*","q{/&ZSqp7#vU`jXGCnfnEq1Je4>=EY2phgfip`AkBJLPG.hM/y90[7xOc{btmfZ.","^i^X5v7P^YFE@4y[Nimj0A)_b9o;b?l|Q4gL$OKE+VSj%#FM.WIr}Zcg(Zphn^#j","-a>,;@xnGEm_szjx^'t"],
  w 36 47 0 610011 610396 100 8165 ["Rd^O2)=hQm9IqSrxCrayuJf3MQvF>l_'m5V=)}X$3*|?B4nrcnBJ(l$SH-3a)$Co","13+a7h1fU*+)9x8W~QKYq*`)M?l2NEa%Y(%S//GNFEk/Ti2[i5Qu?mIs;J3!SHeo","vlJi}RKR&?9a@6<|Z.],(e3yNs8w:#Hk91CBY|Q-S*z^4rMYDQ+!3lQgjo|asC/A","vQkN|=M%v(i5M'I?WTRo+a#p$r9;z+jO('gJ)T,%D6bNz[HJ~+FR>5`NIGQsC%,a","XC61P9a@U$.OB{(C;eP>(#I*@KDt8Y&W*G'WQk}2t:6o9h6Vh6J;4;P^ul*$FP.X","$i!kZ9&S[1U%-{#dGD5oQg]?Q#dY*xbXg#d6T-Kk2L*}qF3IL"],
  w 36 47 100 610397 610898 70 5035 ["#$*eN`Et:l_m3P>&8MB>!pM|kzD;?'b!GE/WQT9ZD=-P_r:@sSw'/;fv|iKia#%)","O$4&-M,}xZN'JG.h%)t!Lv~}Y5snT[*7Mg2m[GI#_8..471C4KtLxh/c'O=bDm{U","BX,9WQ4ysQ,)m]K_f13'B-d!HE1XIz{u;dT/ZQT,=hdl{2;Is{%xA3VqT42f}&Ma","nZ^Vkl4heL';gz|-NH|*l|$[~&/&x(<Mz0/wYyR_7BhdNd)Cp0VOSD{L{{kR=5_i","Y%Wxgo1%g#,(mb0rqh%]B"]]

private def r36_5 : List (Chunk 36) := [
  w 36 46 0 620010 620393 100 8053 ["'g%(yj,i$g1G)*F8+kj4[25)brEdi=bCvDWZ8w|Q!7EO=D3Xmef^)Jw@q(Rt.AuB","3q/,PZQ#}e:Ns'a;Tt,ETezXWgW4):f6-11(7PX`[!F<d+;sjr2XbX>X:eZGz<9g","A&&8U:gX3S1s_=dFzAv^h^9*^6_$-%KQvTD0xD|PmJwpAXmma&Ka$,/YKn&m1AGl",".()fQ-5s7_1~DJe&(x[aA57|(@3.95VBq8DI%q,$daW%1Uykju/unr^J1XOuh)Q8","]ey'=MumIsn>^6mIpDVYj#Mxf&,oDX/RA}OY&biP49%!nT=>Te4_aFkcIJ]oOhl#",",(S}(7P#~AG:-^j@)g6fZx`*_eQwZG]#>R`Bal|6"],
  w 36 46 100 620394 620898 69 4825 ["WG`0d5+MDKWHi1)APT(HslIx~S8Lygbl,aM]9k1Ns?aw>x,d&[(719L(2d),Hr-C","%M1E1}a7dk0o&WKIqE`{qdE#3bE{i/4CeJ^51Ix[t;|jg,3.y4Iar{@kQx,?Lt|r","5*1qYLxYW!Tp`3e*y,10,9un/Poe0OV,5o4|67M3sz-O=J=Tbk2%]wCr(3wh}y&G","1%7_OWzk!nxiFjl6R0{f+B6[{A8z8PAYs8*y~VU4#'@Ysaxgjkl$Olwi],3I19d.","1]F<u?I9w]'H.P]$%>tIku4T)8U9'9kjZaBC"],
  w 36 45 0 630009 630391 100 7904 ["t*YJ$TDxKzSIWV_A`>s;aeW%%24YceThWtv5VbECN>rfp$ko9SSh.e_PEH9/*QXR","eCVb]]8}vwPu!uChU;JnHTH;@6[x$^NO8Al%AXV3t,ahnu#NC'V%Mh}QFk6/G7&d","N2=2Y4h-2/;Pxnm8/vU5@]L`]Y:8]4_-S$(=SJBE-.Y4~T/|?6Zh~U#j&&K)*+QQ",";0-fgBy5H>HYE<?heI@opZ/k.]ND;_0yFD`O@?ja247UObi%mp4YIbOiZ14;/GRx","&9gIyhuR2KI+h-LsQMJ<!BCc)a!${N~UOl&<n4lJYqiH=Q5)mAUkaADJ|?>1B_TQ","#SXp>wo{cfi`zdor]ph|}])Q.OJKd~KVdfW2lOPiVJO"],
  w 36 45 100 630392 630897 66 4490 ["9W>!(O5JX*pk@aT~GA;9A<2!0yqjS_^HZn#}MM[h%0`w.,`#E]Wbsj>c}Hz:}x^:","I^Y>1PU[eudVbtiF8EBcUCI^|W.KO!WM#j*>UO@#xKsOUL(b`+*j%0!<EWfMjChU","bjFiJt|'5sMM>e09(@QmJ5roVbP6+0k0e@L&4w2MSm{.O8;(a4QH8Xk?]CDk}h@>","P1EjjJ&A[R'~l#3S<W^5R=L(Enr8>5Z{!QZB#^;qw3HeRw22t+-LgwmjI']X_U}|","Aa/8.ZI`q:3]_{oWKN|Ylw#U(O74|Z7nwh"]]

private def r36_6 : List (Chunk 36) := [
  w 36 44 0 640008 640389 100 7769 ["(0Gx-D'BDSEEi.P<sA#x@kSgLPGt;>CtH{a>-JRa&^IIbo^G_cfNPmmtp8LwGeS.","^)PBs(1cc*%+Kh#W<lyUPtXul!hRtpa2lXH)0F<CIK?q{>jEV[68[8MHd$E_JUvc",";_(_;}UXl]kj/7/kdh#9MWY#;rv,(AaM{xE|D83.|71,`25jSzgLqmQGVVX$-Lc<","z:3wy]M|)oqXkT*Y_ioXFl`.IJ$%4Nz;+oW1;qDtNrm[>=GJn1SXMi4{]~Pwoq{l","B>%d6i@qy,9m[D1$tF*FC{0^<$yKx=|lM4eO;U:t!e)?XNU57f9|deg/WA!Iq'+p","aI2}{]t,j9F}!K)2lD+dSEeTO16jd,ZjeN}{1@j&r"],
  w 36 44 100 640390 640897 64 4238 ["$1mhQRDGy0on>|F8/!YoRP/Z32q`y219Pft_Z>ZlI^JZtV2Ziz~BE}~,=.`Pa:?Q","|'FSv5:5j$o_&LS@Wdc+`J#]d:Cw`{2z5i<sQ{3;j&zlfy}'qxA8xu0uRkmHKuq{","J4w8HBH,ri?,?bBE^{o^2[H{@>.<e=U2.u?.VYM}}y>YA;SS7Je1$|5RYc<USczJ","BvuCt:N#ryF1E-v.P`qA0chTW&<g#5`A-H=g,dwn`3,Otk-TlbYS4*8ZmA:sY>]@","&pjjYT@S6.u!ZrY(D3hR&5gMh51=J-Cp[L"],
  w 36 43 0 650007 650388 100 7597 ["i$YpM<Bs=jd()2~O3D6(+eO40NLfWfw`D|~;bul_k>wdu;#8%%0s0^&f<Yv|w%R:","zqt?d`w^a|7Xh9)OcoI03e3%L5eRlN9nC0nx]3Q8Q3^JxF_Tr5R1}5VGCavvL>Qa","NYwdGcc/e6G(oM>O}/ZLYNU*_LqA/<ArwZ^$#+cFHX3qbZehNzraiUKnFp7Z-,=6","^9Aglg8?R4Y}zH5{5yZjLM0KHK_u^(Tw,45oIf(dU)n&<FS,DF1m!cynFtf7U>u`","FPf`UZYLug-$pJ]M/J)S%m5MlOkj@dWv'TrNu':d)Q@CAv(:PB1#c}FjWJYUBY+j","J[8g(&}G?}M(l)]=%bBRoSS{$sf8Y3T?Aqss@Tmj@gudOs"],
  w 36 43 100 650389 650896 60 3866 [".n~&K?nOYtN9HY/#lN/WmWi2:fUs[!7vf-R~faz93kBwu(UGtx8k3k#~gZ!;^8T%","Xp)[[bVKSb2P4eSll0|:hw>'nZQ[!%YO}JyzBIJrw;UG(gQln^P>Opy[:)iA)[U`","Th^^l?&d.2`P=)Y+GeQnLiT:C2,}eRjg|<fU5!zHZ0T1jzqAZ[TW%+(kc3WU|Oy@","`s;,tI$v*d,e1?WHH:=js7n.?;LBLq!F#VO+7&kv~s`O[,K'OR/rmTB!^j~u&2?-",",B-9ke]wm$h>~XRZRb"]]

private def r36_7 : List (Chunk 36) := [
  w 36 42 0 660006 660387 100 7439 ["n42oPso#xRjsNmv1nLX2d1?d1bw9ik3Sb,#w(2rY1Pz_2JK+PSFDRXVTvNaSOhX2","9IqMd`tW,Atu~R5*pqx)k6Uri!ov?wm_zV#m/urAlt4l7i,msD?r?>R*|67k*SJF","^qopILX!9UGgoCvHb!Vt*Vz~;L2AeXXN]7mG??.-MchyOh$bjTC6wAceR^N'8e}u","bLW)l>XZ>U(t3Q%s)+kNHPhfE4xm;BAw/IM1yQ]'2JCCxv}u:_YebT&.G64VwO@~","bV-&dE`{%HhH|rWp67vZ'Y)R(+!vt54T_dee&<K'ZZtuh-h6D@;<-#=-5PtTO=w<","3<[#Q_2V_4A;/V/uY!=|h@Kl;eJ$U}ZGs03JxzrfmfhH)"],
  w 36 42 100 660388 660896 57 3576 ["7$n>;$R5J2vL?#ZC_1;kE0ILiS'N&2Gt>du(1=oLE3HV>am-DcXwm9f#|'GR0+?2","R8K-[]$6LSeB%_#Nxw#Wc_!{=4eiwFF},)oaa{MRX!9pxf#!-NZsHbvZuHWrLEvw","-_m@aNyC#t>Hg#-sFN*@(w,Aafi;A-xTx,7T{QucG'T%gNz,kHe23|(s-7TEDp6H","tm}?WF;sFP>isWLgIeqNd=qG1aX=fM>a$M,!WMTy#BdM4aTx]'dVfp5-?<r9OYS7","-]aP:86Qnpb"],
  w 36 41 0 670005 670387 100 7243 ["_AR.F*1oY]:TjJqga0Q^s3Q|r2u5GJp9w!1OgUWRFxbkh^#]rZ.PdLB(qG/n8bYw","bR=Jw?uRX2y<xO0$rgBX3I|ovQ/pc95JM#ou};O/wWfL6L;.YS=%v9F~wObF4$j7","Qtc$U85B^?~ds+$YK6Al$^{r3r=!e'FMJD0RHO]+;5B}_{S#=,&$AU4F@8ur.5Xn","LJ5M6'bO@YFj=}BW=iIj_9n4A?ie&ZejX:LGSfx7m}W]j^%{e%Y$>}y@3+(:~A{o","|L+lq:E4S,/=x&PkuzL$9dRs/NwHk!?j.2kF)Y<cDWS{b.A[[.G#%/urL|Tp8e#0","(4B0|f'M-&:I:cP>12)FFVw^RyO=z`E*+(zN~M>^nl.L2&V_KuqxQMk"],
  w 36 41 100 670388 670833 52 3174 ["[GUb])RF~KN},@]3L.nr*7JDM4i@b4w*yZ'q*Q1e,'Hf<m'MT0w#OC%tUIV>YUcM","(|Nb0yCCt06srGc_WS%2Mh.YMc$*;SUvu>Zn+Z%sk-bv9#jt-8u-D~g9z(JM0@a0","Z8yR[W}}`3KSar6}[[[k+LlIz3*=K2G-dj,T8GRt=K'v/QvDl#}h+e6&yD_0CS6?","Z8|*1aeHR8T_8d+@!yHG#;Hu'iK5YkWf{zcd1UD&id>O8WFnQmd"]]

private def r36_8 : List (Chunk 36) := [
  w 36 40 0 680004 680387 100 7062 ["1n0~X7m4OAzCvHp[-|DgPvY`xzhWM=^M8]a,X&WmY2}k=h><P?CL`ezDd><0@Qf&","^]aTMMfc6B#g#>o^P!P?A|FOfZUztv+N7Drm}m}&ctyC24a<oud}Y,:#{Usw~g$>","T@6$zr+^&#$DKoY6?$Mg_1*qi]fqgQ~SDW*c=RHB~8U/Ah!fd^zq82L65^nJ#Aa.","|l,qT`O`eoXb|+.#w<j>N}1q=;Ju|6:*6q_38_|4qu@<L7W<7h5Mm}T5K54T5k#A","9jr:.Jg6TR?:nNIorF~F390C%lJ?y,UvdTZo@PTX2&:/4~*)^PX^#Eha5h#^T[$1","A?{6gx!%hX-mH!t'7kRZ{FMd'lnN'JS8S5>7lGU=iNnH0W0x4U4{$+m?o_q^i7"],
  w 36 40 100 680388 680832 48 2853 ["|$!:?6H153qQatCo1iX4xn<O|lz4/Ldy81XSdR'|}D*;IAHKFNWyq[^HW.En9.av","<i]938sq:05[SsIrXj!UuY~szK?=PHrWNa)?5'*!*w(,9yoO]$PQg3QRf+ct:~gD","G2$ffwjOkBV;9#>L71XTOlf[U]*[}6|=nHNB^rYPT)<$a.)_u9Vh(vC2'u)8zt-y","@mX@$%k-X'2<@7It.FKZ93?vX8r;?OD&>pYm2"],
  w 36 39 0 690003 690388 100 6837 ["GEsI`8c'ufJDC%rZHLl;V3j,pkwtI<JN]*ySkub_6..5@=T|~tz2hg<bfMyjoJ`>","ko5%f|57q9@(p/^SsLF%x#|.Bihx8b#w32TV(BsZ4&uMvjN|Uc08jk2/|:V'vH00","*x&}N'}4~fxz#s%A9Bab^eS/!m_CcY&F1A.=t;y*nRtU[DDewrJ&C#MX?e1/!]jk","KcsA7_b2^Y]m>$w[e@)j9fYqYEQL4qrKYq5`vKN2)8ctqX/<{@p)Y~9FfSVu2_Qp","e!?7?b3=6V'S[d2cAOW8|f5IO6Qg:yc(V|~9&RI6(-y;+RcH_)0{^_;_4&FQaAYT","}N<G~*(U4FaqFD*XGMuT',|brPzb3#2u#!_jK=1sra],^c)r=H};j^'9fwF]iPKm","+3e"],
  w 36 39 100 690389 690832 43 2493 ["}bAwmy63nL*pK8%lrcx-_4(z1Dx3aG&ba_hbK.U!ZHF_L9EAJaYWBxye>S%KZRa`","jt@JF<n<Bci)8G8]]P{BD@rcd+!ePJWjO`i>^t4WzK=HCUj^5]B+dl@YsTA)7#x-","':eNUNM1#$s?d|^%uHe-t]L{V%<&%D+5]Zv9)mBU:CD,]i8DPWIg~7}<F-Ka?){=","#.cowjzT8]u?V>*K@"]]

private def r36_9 : List (Chunk 36) := [
  w 36 38 0 700002 700389 100 6626 ["3Ejv*/yBFSgB0:tOO#^^td?2Vk!t8TiQdVAJ%&uH.fI<yTaO}kbK:qsy~zmjI{Y&","0MTbG^Pq};KaG!>Dq`CN&m_oJ5w1I3h8MUIDMM`XMa>njS_$uLV;n#MECbLS6ri@","JRZm!`w.R$ALCqTi+)v7c`G6uRqTTnC1zc224a@~5Nkle4+(}5iWBBCfbH34uHr-","@NB>~bNbyU!^|_)3h7(iGIl->~>VZg~PUY]p{e3zpTw^+[&|S|S8EgE4};iF+[j4","&vMVt@Z%nT54vd#&w:G[bN}'G5'f=?_uk>F1n.a{=Nj))<o'x?X6vA&AM}^T*0-o","TS}k)WJ|:+u5<3#!1vt3NX$nL^-s(TSg@~7sT/+buTcb_[YN&]7g1v1^p4GWpE?6","&0qv,Tl*:g)'&}L)0iP"],
  w 36 38 100 700390 700769 38 2152 [",:t{H.7=!d's4,JwZS}K,F85ESvb#?pjf2YJ@I!}r7jZzK0OXxys~A}euN:3N;XE","+<(+u5;$Jn_=s7JjZb=~L'`6hAgt7[ZCI/B12eayo9Z.NSb#a*ziasmB:z-V>9!{","#%&t;1@N(JY,=k=5IY{WQTvOC+^,9q.Z&&NLbuH*JX9KS!Miw34;..zHMoS1s"],
  w 36 37 0 710001 710391 100 6368 ["8>mpjCvQFM~kdOr:(a8H$obk^HW)>9lxcz.HM'sH]@jeSQ0s31&,T%lPXC'=iJ9g","DS'7c*F(}xkw=5{-59lwe?niQm[KR9#hd`w9/6yj,m.4H|QBs'pD)$1do+`H@#iw","Ilo@iQ:X*$Fh'XC:hE!:f`s02^w*w*'pdfORFY1A+YD-fp->gp{EWn.EBZ({d<ag","QDkMM'0+0pL2|KFwg}]K@b(g>psM'f|V8'A#lfl6E0fc_/wLGS$U*Pd4SUqriCFI","c~!!]91:,==JPYx&_T<[gP6h!jPx&(hiWtCtG/5LNj.WpM6Y6LNVj&v+uV]X#[?)","B=OHIQw.^4Ji5eao#:idOk(h41V#&~cj&#&k8=wiI>>SO2~SdA(}iKqM!$?V%M/3","$<i_GviX'CxeGCD%t:aWKT1"],
  w 36 37 100 710392 710768 32 1778 ["7.Izl-Ctq.Jo>Z9!2U^L/2C2VSk(L^m8lJXDou!?W7PmMlAG56#4L'-'kOB~Ar/J",")eY.$.SmJ-gtqJ`?`'7wd>->0|@KILaimJLR7f/QFqsC7_N!z$qGQG)?TO,NP+z(","'_/V1meu[(l[k=E[Z?!m@f/wX=1gIuhLb"]]

private def r36_10 : List (Chunk 36) := [
  w 36 36 0 720000 720393 100 6134 ["jmKS;E?hfz*l,SOQ,+__80VuDtjo&#'#!X..3^CJ()]r:#5b='2r$-W>==p$xh9V","/zG1OZH-pcT1MJ@W;]G~0z7,t}xo^G5^w<pA#CmDl@}LJo#?)LIX4;5&#|,@U[g&",")[&n@Lz$CH`WS?TVIBr|8-)3epc5pY1Nr['(ahURlsqD,S^KX+r|6^69[6C=bZcl","02b>gE/wLZ}BxmFzJogK+[B8^pr$eh6FBrOIwQ?23a[g9o5'q=/^rPv!;AlJen@?","xaJZ5v#,LX0|wG/|cx:x2/hPxrF_}~|&nrb_v3seS'RrT?OqcOl@+-*Q)<W*Ls#K","?l,?~t9)=Z_gdwB&@j/+od%9O3j.hk*wLV6ZnYG`oShqq~+E~(hF&K*##!)>3(&{","-RCxN4<OxXg8b`al?-yIHl^B?K}ms@7'PP{FwjO6w1Am6S"],
  w 36 36 100 720448 720768 27 1473 ["HC`Z+tEk?{ktK%h_tGqs:%0Lglyg'+dx~b}Yi_i)SrQhILB=1ke%5|<a^g#{5#)Z","?dRoGPwCpw,wQr.q#T9J8z6lFkY.M%NswY8CIjEyq3PLl(nm;3g'#mY#_1]~~4r*",":zZM;&UU"],
  w 36 35 0 730000 730451 100 5859 ["F<qIMV$?[V(bvU@{r-CC#FFLyE5TZB*/6y,BUSzEd7Jt^]qYs>u[diC1@,<o^z$K","QS1/5G|^*&0vCug}<w|HK<Z63%KM-hTrt,CJ{&|h`p>x.}^d-]a%,aEom[)S|]l]","4(irP)%'l}PuV:[i*}{U><iG)~v](d5wcUec,'pF<J%`3*X3J9#;8>,-,3Vt1dZa","37sy#k8W8]L_<b]<EJHuWyuI]0:QDDuWGDV(wmS^;Hge@qT$B|4}OAxc.DU@5n)D","b9AOJ12[~'yr;=`EhR5ceIa9:k6n50G,{7tT-=?&/Zz+fZdBMeo^v.a9J^BZF{8_","3SyWiTAlOEn&HD~ytNhJ#JC;N>49waI+T2i%z?|RuOQu0d#d'D|d9.8F9?zs$/!x","''kbSsh{a~hZd/lR8k(4@J=ksD->!M%iFKJbBj3|h|Imt3&7W'N!nURuDm7OW}"],
  w 36 35 100 730452 730705 20 1073 ["&zAd'T$t44My+O1}thYEsdhin%TZkAOV<E#TuB,6TAaGpRdy3wyqw{xx+Gxs`O^c","F#li%PN^@?{LCkC||yKx#h{1Ef;gv,FVbCI"]]

private def r36_11 : List (Chunk 36) := [
  w 36 34 0 740000 740454 100 5609 ["Z(d81^XeEXQfv.S6`}m>5%MTJEI%8Ps{g-F}R7,J*YD'3%K^/w4|Rf|_yJ)ojy&#",",P2,0BB<S3U3DuvEv`Mf|h`vMECw=@}6`vojHoFjC(:9(UQ9t!.gnAG3ljq4K1Ly","O7`QKp7~S(X2'M->csD(%W8-}n-3/;4_qhMIhoMh3hI`!fZ*TH|bJ45ccy,*LDJv","z*8rS.0&Rhu]FGt`!5/hX^EZuU.-;ZV9.YC#xBU#_Q>`Y>/MKU#sls1qUFk*RN:N",".egw7:_vW$~FYHV#qHT7h[R8;Q'7mlnVck''@wCdmt)Lyenj[qTJWUE0@-%zU:Gr",",aMh;HI|I`>3fnPDa972Kjw<i&9/D/}5Y6'BYQ!a'%f8)&:6LB#SS&$!Fd3jW$92","!zi_p+,Q*;BTd.nvyu$87.l%xUM8>|3|<{<kktnDK?[kD:7oB>F_5O4<;W!=@[|c","#7X,*%FonHoF]RBE*U"],
  w 36 34 100 740512 740704 14 741 ["6%1YGPFV^u+4Gh^*'Dkg`.;ipJ;Dw=KU6UMb^/$iOI3/sx_uRU|U2rY7QU[6uBoV","FYb,"],
  w 36 33 0 750000 750515 100 5381 ["BJNw@Frs3RksyV|WG<Q1S*>)6(.7Xk/o7Wf!faT_DnsMva'1c{%QM:PF4&k:$!I/","3^:a6ox307`%Dacs*Q4^~MLr(Wh(567Zf|jsjfMf$9E$ID]~1JU3#<8-XkSoY^WZ","e,P,P'~]f,.Rtv[vi1Rn+9G6mSYO:_W`43<(Hp/6-h:Z2/>Q`MR.,>hid*%XZmQD",":ivo{MvI9vnMA7LIyD|6d~Y.4o*IU25{y8d%:JbE,G<zAx=n4p~!g>.7;}Nia+2.","*ycpSZDfn/[r7$d.stfj+,K)D/3:Za#h.`<vOZ%.8=Z9J/{#@_QEP1mxJ'|T6#z4","7.5hcS&tn8aX;5#DfUKQxRc9K-%IFO*IR++Qlba:KeA@&8](P4[w?}RFH0iHNNpk","4dyzaP|A1}ym2^><G}n]4.dz{3#Sueot8EXMP*V!T9g*%?R@AhSHU>:[DB5,);xu","$T/42I%~$Q2Yptiklhz!f`P]!"],
  w 36 33 100 750516 750704 8 419 ["ET_Kr.kl*cjc3Eos!J3I]X~Md>-jw/)g'AU'aN"]]

private def r36_12 : List (Chunk 36) := [
  w 36 32 0 760000 760578 100 5173 ["0@?H'=BCAKy^#az/0TxjQQgHLDw.#>jZ^B[+x@-;}YCNJC,;+EMi9^X.2*9B1).3",".PM#RD1lb_eMJ^_Suupe#=WjvJt%|W]|VKs~jr~u2?%n|t--;JfrOEr0JWa;6co1","$y}0}[0}BPf.LW}H?ms'Y0IW?o`J'@*+a}3V@Qo$Y,UU;RZQte!'!vw(>n|<s8eI","37^/!C+p.>DLV6=+2,U7_SZX]G}Gy-/QJ9`G$mC@+Dkvt`M:.-E5(gO=5$WB=)/n","Kj{T^86y%2{u_(TT/s[9-N_+f*<[Hf&hn6-(1KQWg!M[[qC>d!2Re0rv:;@_&B,%","F^[7?m[hvb3aPZI+uGSCUAfQg`Z[y!gK7gl?r2|r+7~[A?Ayzki*1(_ZSRAK8.-s","&jVuZE>k%eX}GqDLxYe#yuk!AZ*1*ZgsThRt,1P_MeEsR'n9>XQ#?u~38m!lV0K_","02%|:.m8$ntbq=W<jj/N;Rl9$voo'o*.j9bq38Ci#k<2x%d"],
  w 36 32 100 760640 760641 2 104 ["#i2GG<Je"],
  w 36 31 0 770000 770640 96 4786 ["d|7={BM9yQ{D=Y(`awXAyjYm%h6;7'c'37kO@(*YJZGNBmN}dC0Rk]KF[8sZ|@bp",".L+U*&bC&L96Muz3F6CV?5t'p}>span[]l1$ZHLM'%<t9xTbFhbJ*WI6Ru11ab9R","|aQs^b3Lv}A8D|yl^t'nN-T4u(]qO#(nE:ai=x$8Clw{V!b/H}I}5fttPTV085+m","g.bmE9hm{jaoKTFsoKamA?09R27CzS7x%<Ko|Ab%h-1ZzJU|9&p|=}v;rR4h)GM$","Hbf@{0P7Np7A[fWXM^Jem~z5(7,qFpAD9ht*uR%fT<-Ua<#S/6A]Tw}r%p$aFM__","5PY$-Mbjlhw:;^dCSJk*Q1ZXoVuPR%Xv()=e>@y{o{(S-Dw!vm='qTx~/,#_tKJG","@+rVB,H%66o}kqKqZ3;H6mrz.K8c&5I$0/PNfr<Og/^|1ix>E~leYgY5!;b,?EH!","2/q2Sm~pA6}!&Up!8w(W2hMC97nc]5S"],
  w 36 30 0 780000 780640 91 4367 ["m9Xrit-.4BXVruv!3DuF*Rju*<oWY@KY>VvX['q=bsFGO:zv|(K++s~TFE@]Bw7h","_MtyV^g+HL1P.1#61=-;Jy[Q*dWKI(27{{kw~]rJ7bBO%0h&DvuU1w^B;NkV~)z/","LsVLh=-x1^BBrJ%hiCo[$|e!bi?viXAv7+]Z)CZ}<xg$jrB*5%c7fH-*!*e?tnwY","nYX!S(sl4%hRR'sI1f15qF%vG^i+A80[ntMfV_1^-Q:r&h]cKJ];1'f<,<_L9vzG","*Ks`Cf:'V}y%jc7NX@O`1,;Z$fjY]DDZ&I)~?JpZ`2x_NGO+9@HAI1]'#`AzrC'o","a9p>Ds85+#nR$q>.ej=2-/aO^jH_fx5^MuHuSq]XVKcB@m&)7bc&5X+m#)&(mG%f","~e}m015pTX`c%5GI^^?=fe.M0fkckHFcr{qIQzH?*)d1:=tM^g0:1NZD{4(P'1hs","''<1pCuCV$Hzby"]]

private def r36_13 : List (Chunk 36) := [
  w 36 29 0 790000 790577 85 3931 ["jgoYsc'9&~bOsnXA,htTiIJ3rJ&<iGZ0(#;i|UVrT{;<YVVKrxh|Q-'65_c2[+I`","5Gr#YMdKojbq/O{x#,V-nC`hoq<}%B?HsO#qrK1#lAKS+80s]ze/|k}}[9Z=KS]b","gr1x$B(moYm+GqZyfzlH>j!7MD[HygPftdvhNkPS!F)Wc;3HIW'1N|RrKG'x]EYV","twP!ghH5)iEN.=Z*j|As`IDR/5A,jjWB(JZ:Zqd4t`BN2VO4=Psh)lu$u63qcv'u","GNtowyNs7x?~8Wh?*u[ZB0sXHXOPZi5@'_XScvlYA*1(<2.s@4FvAqB+n+^xSu5F","uBadE4Y^w%lA+P:dCh^mkJG%JI9&s<VJh0PIr?2'Q$Q-'h3x+J3pri0.9S@mm%4A","A(A3%pNXu2t1#tbk+D)pmgvQ$mY4U7`P8VNZE[t_nx[[aomiSbLh=|La{$9,d"],
  w 36 28 0 800000 800576 80 3562 [";5K$e}L2g(Q]1AkPavdA/6LV`m6<4ub^rhtSi{78T'yc|IISzN!I~f80a7ct$=@;","fPqE9KL]gTabX_FE&W*05oJ8Q2R,=$Q-__(Y)_3wT:]0,z4]voKn|$t^H_-gCp}e","&o1!^7K)!$u7ty5#2j{)O&NqQPYZ/-(3Ia6VX,HS91z~{|ei0,('Xw@?7:xz$-}>","oI2B8-7'.[:O!+U<n|p./nQGp?26t|a:.a~[O.=CE??9hIQ^E}|W12_,(+[Lfz/D","gQ{~HesIM)kJE>%)VOHMTQMaMaCBELrQJ%~E@e`rbM^i~?aZ7<J$%ypLy-yvd]1!","{@1~SP@Gvz0eX/K|kJidCcq=_vK|ErJ)16uq`hfn%t%]W@kihey4I%kCw~k(b<Kq","=4{jbbJR*=]qp#ip:5kD'PxIl~{6Jo_crX*f1B`!GG2%"],
  w 36 27 0 810000 810576 75 3218 [";J*I`3DU>jdpx+zvuS1;f<[87w!4[7dsTAcw00qY1f;klCo?TA{)Ot0rEY@I##V3","?U9[[?$z&]ouI,J]<T^/vQ.++,Z8;^k|h}vV#zw$14Ax]Uq7qs.NtYa/5lCee.9'","92@9#1+mlM>W)H_0BKr9^&RzcO~H4l0#j~yJ}-k?6`']Hba(JoM>o]8v2RlP@DW#","}30)qM3|-67O`QWKpx5$'&gyD+EMx|:2AO<Ic=F5qah>]5D<]`a3@?^eL(YMg`Tt","(7P=~E=I2.XWTAB<Eos-fBxfe9$R]00#?Rk,=lNex[bMqarbK_|FZZxDlY}?0alV","[[t}3>KGR;:D0A$NB[29)L_z,w)l&)B)cus{c1y>E|ZPShs14~oE%0591S]<:&R$","(5r_<b=4'wJ2bp,ceX*@pyD"],
  w 36 26 0 820000 820513 70 2891 ["p.J*v%U%^[GLW/Y-r0wM|*_[)~9PpZ%T>rUVLp<}E)h?wbz-81Wqv;jUn8w@,q?h","uREA}n^6i[-.SE!dL$~KURUO3b{d`_00Y3A+.2-8`k'AH<^?o&pc#jfR^Wv:H6DF","0I@URcP<fUz/h.8^h]=.0`]*AYza3f:L&E,ZLFQXaTFMBPJb#].t|f&Y+9Ts9,E>","vAUP1w_q*NBT|HQ`=5_@zN(Y*hq6P'I7lrTwE$DPVuOA.z#TeI5Kad(49*}vw!{t","aJ[ABpYL]u|.]P/SZ4~irC9e&z#]kVd8PawQ;{xe?5!y:L[IR]*aN_V+!>WP*,%h","/(*jGnl9<#i}vjDyoLl3^c@V1d-?q>WL<jsfcNG;8s_AR]M*V)}sTbf?wGvhikXH","4NE1;k8"]]

private def r36_14 : List (Chunk 36) := [
  w 36 25 0 830000 830512 65 2585 ["gtIAYIy{k~g)YUq*Ow.6c@O7~f,?dgAuJ'K#20SP:7(D!829RNMn>}?.8+.mBe]<","gx=)K/6Be+yIs('EJyCbMgpBN|~7?b4<QiZ)K'{qK]O&YvUgkk[-5X(k1&BOC9&A","Gk-wl^9L84*>LZ02U-}EOpLEAwB@dSEib-8v>##dGBL~1>hKdu6SmlvOj%:_}IB.","W4KlT16GybGRVo-OIsic@Ir<K%wzSGrW[iRoWoiM#<,6Xl+$eELwB%7?.2*$.]Af","JK#ZBSpNp4tW&XRb'wp^5DTo-:TJd/uH!}KhrN_!d(*i`hR%`y?a~naz<x[n_kKF","%q$LmRb1-kyUYS'JC1)uo8xZ6)Zh3@uXD@7?y|gNbg*ic6e,xXwwL<zR@I"],
  w 36 24 0 840000 840512 61 2333 ["D~?F5hp-DZE@q1F#H0-PT*2G?'dkAKEIhh>Ab(%<C^t,Wu~h%mG{`GbN_8t'*]Oi",";pgyHtWcKld4C}i@Mnn>riZ~+n!yALG22s|#N0R724e<vuGfL/&|!xXsOwfT*s{)","8+^JVI28r>g?HqIa?VZ3.By~hTM`)tgav/JlD3X''Rph|tc/65Ut;QAouwGiO08b","c7p:m17Olh4?.!D*veM1}JGBW9Or_@s9cKOrGFVL@S6/ag*Pq2].PBGSN=bl4Z,m",">6cszHyC<O|hk7|/c4;%VaoM15YfpHH:1x-%5G.Z+?6L+0@*o|U-jD*DkE:qzlR(","(kkfZVI?lLhx2CwLg)HYxCPfR;;[hWY{z)n"],
  w 36 23 0 850000 850449 56 2061 ["*pzEse)HRoI9a^mlKK7z8Xfhu)c_ROYoKk%YK5mS5R[Y@{t[m&)g)4YB/{!X|9VT","W^c9DwRTyxg[No^Tvzh;w3MWxJt]{.k**sk/BYhut6++HtBRvc`(P<Iu]h,_OFQ.",">C$}&s~|4B<yG{K5)/-F5roa!-t>8~DNX;17a#jpzy2c{Sd2VI4y+xg~'OW!T?LD","2FC+%<&-qD4j;TJ.}DHWQ_jg;:?*P*&JI3:`c}~r!g%]y?6!-Lyx&/,g9}+a!GK}","EcPQoPpznLr$`'{^yMMX<QAgiY:]-(EGG/:(NY879.vAh6I7X_a-(p/MgVd@/%|(","#_-2D0*vmNg!zh0%Ivxu=vQm8>|S"],
  w 36 22 0 860000 860448 52 1839 ["i9]3>2H-6?4wc)P5i4Suo{5pozD<-!8SIriB:((/ND*Ku%S!9!DKOXOq4;[^D.HL","#6Z]C3'HM+i_[Mac3`Us^>+qG1qpw!k1pPW+XD(5(ssb&0'}xC,%z~TrRa(*vY{N",":jo[%]<-&DO_PYrzfbvS@RdE5(u}_5'g&~-T9KD:NZ*dR{6n}Kpsqs%ppqAGTv9X",":o'H6FwE:l'Wcv~$eSEOp<4d3l_&Hpq]~`9msI,2/l)x}dD4U70M^}!q1G5F!%?)","N;_HE*T#)'~S=Pn`-'Uc8%tsn?EKuYV]hI7GW|.L6-~L]=Z`3`7PAtVDEr1VKdRb","#Qh<!Ewji"]]

private def r36_15 : List (Chunk 36) := [
  w 36 21 0 870000 870448 48 1633 ["1C|9;[G]#$&Jw(da>]<N}p~@K;MH9gShMAS|Lu62j;8:SdJS(0mD6wc'L$h5Kh}F","ka+=,jg~S|7%_1=Dz^V>Mf`qSbk/+<WJbAO`_JQeuln09K/h,4RfzN*~Ot+dvoy/","DuNTYwGGFXGXvz8EKvS#aAj4=|Afa223r.Z2i9r?WpPlNDJXUU[}%xUN~at~JeL-","meX.aScekZMLG6Gn1o!It{ssj~KPktEeZq0l_%wp4-#u=Ri(0s6qYR]9tsyHq+1Z","%w5CvE0Jl?2uo.3{AS[!?UQ:/D3yhG<l/~^,Q^E-x2h{OjRSM|"],
  w 36 20 0 880000 880385 44 1437 ["/,T/c633k;K2,hGb(g5U7[aSr8GY2b-32`F~3yY4YbW+u^TtMH,F]%?=D:GZ^-k^","6DI=TmEyhVHJ}Dxolphe[Bna'^^,j?^Yd[!TmIww@uq86CI{21N=2|,e3R>_=kVh","lG0*/bkux_ddUzGDM,0OW@xMzCnF>Ym($o@Ul5QASNWL,}3W6S~@Nt_v<~@ppc`|","P4Ucv2t-b5SKxVSZt>cU'v7([p5OsBLp,6yB:~;cET'&EM@<*U6pV{S9oVyN@.&,","#X)G<7F*kMugy1O}z[pIc}E|PgoO;'&"],
  w 36 19 0 890000 890384 40 1255 ["3=&WB}^WsA:K3jK=-[[b+[Wis_*!;XmA1+HSu7n@0^j3]j}r!5h{>7PuB]UWOiLw","=Z|mf&zpL7P*{%({43wv8I<M%@u4gzfE+S*k5q-FGhTYmItrjN4FxvB9!z>_av:R","vMvZL>w<Ae`yJ@d<?,dB9*}#8UDrS[$>E487lfN}Yn5<HC?ZME1nJ$S{86.6H4E]","w6`[!xgZyikid)7vze?vIid6~V3AsrJ--SM|94=Y)id?xM*BOUbu=dnjP;zQA7nz","O3+Z''{7p'9/(>"],
  w 36 18 0 900000 900384 37 1114 ["!;2T<))7xLHA%9{F]|;F,&u0'Ih;<'V+#~<H%hQcbCVSKDjp+zvaB6w0]Op*c!vY","f:`^kUV/f;Aq417vK_S,$p';M4WH#NGorT-V;H:~mOYF(zbTsxBU8w'MD^iej@|p","WGm5=A^9q2x%-jAuf9CoYdB^YXJNG{@efB&+/5`:Ae$v!kER&#[.PwwY<CMj!lv@","$]QRv/%8ce$2Z8brL<V*p3Q+0@Jvak[r'4OdW_B={:BWk3JRT"]]

private def r36_16 : List (Chunk 36) := [
  w 36 17 0 910000 910321 33 953 ["[Cq:..]B3Nagb+|Hv>:|[d_?Shh_[2SiF1I>H5E9BYr.6agKgnlJG0,>75RP|-FO","V((}BSt#A][Q.&P9Wc|iOgvga7n-2_:q2bEA5P&|V!wFm&GMk]?lqTRFmoE*MZ)l","%b.C|fh^C?vt=kkSyC(T_7Tt+*oATALPQ?H/$)uhj'*^!-D)T]Q*FA-nl`H<4a!I","+'E'@t`:7M4iZ_}}8{+/dMc@E1mJ!!Q"],
  w 36 16 0 920000 920320 30 830 ["F!$9bX`nB8KAS3X9PAK&ti=PRxY*3ZeRT_6&x_H.M`2l,($TO1P9x{Z6F8:Ct@.?","NW>Q3qu[k}A/Ipsie{YaH7Z*#,4LdW#uZjtP,9O#i7r<Sf@4FdSU0bs}]|h9BWve","cY]#'8q!],8*.tWw)wGB/_Aa%03x4Q6T?d=xG$ro%-Pfy*j*!>CG#Ks7$C181ZEd","*Y;8!0qZhm"],
  w 36 15 0 930000 930320 27 717 ["9]:,*:`)CE3OEWYuW8YiE>Si#wYnq+KL_6S2!&@0,vbC=~~T2h2eJg)u*eQj0!N^","b0S'W<tCF0xYNO9}PyYG@j($r2V:jI@>Q<mrVLyaR[(q-$6pc,o&~,yR8jFNJm2/","&P58|Cw=8VFi.Fv!Cij>MlD>fPk!KN*d%eOIzw1[S^VNK*d*f6i"],
  w 36 14 0 940000 940257 24 609 ["T|U8n{!}9(pq/d*ye8uhs1in<d`;d|MDO]#T>veG[}S~s<=03R(=v`}6nyYqb]A#","]9#~HGul$QZb)u`9=t#|XRW[y'b`MBqnAr6>@=YZ{i/plZ~HygI0/31{p,/^VkV-","&^/b,vd:4y0V]L&;zrukx/p-1tH}`%"]]

private def r36_17 : List (Chunk 36) := [
  w 36 13 0 950000 950256 21 510 ["VOW&bF&l@Z!82>c^Fg;/NK/)9ZR.I4xF4ANDDG><Wb:Op1q8T>dy0li>$ii_9lO+","bX9bv,EziP~kKl)PD'!nt[h4f=`=Z+EH7UDNS~|?U)RhN3fC:$(uDI,;^-PxR)G~","A}+kPAz+fbg@U]s"],
  w 36 12 0 960000 960256 19 441 ["E3%G;?hF=&u~)v6#{d-RDRIkz/M73g+z1G4BHVJ*)SJ{xk3bFLth?^+gS&<i)-]_","%BZwS/,Tk{9s7r5#*6q9}8y!00}^bOq+rv|uM+:k%DYC_9u-OPX#,)si|/N"],
  w 36 11 0 970000 970193 16 353 ["1D(TfwUyJvEU)yU];{o5OyTBLTs6DA1OHhh_kpNOqCJ[>%NNZ`%C(U~BHsdoKr93",")Vg,8Y/PW@-TOXm%%{`{!uq#*F=}F0y0}SQ3qp912Tp"],
  w 36 10 0 980000 980192 14 293 ["C*QU?5oBA3SGXym}$O;g]!iGS]r.XW?Jykck!'zAY-Gf)+:4H6TRFKB[#[.9OF~t","#[~*[lYcE.WE%OF2G76v3;X~bh;J"]]

private def r36_18 : List (Chunk 36) := [
  w 36 9 0 990000 990192 12 239 ["E4j$a{Ca5f.vvpd{GWr6gRs^l_]M>eZXR-Sq$1)}vy5EL*0zG8U01h/ek6fl:Iu>","&!&KU/C`s~|i_<e"],
  w 36 8 0 1000000 1000129 10 187 ["1WX!Um@HI58NLPq.?t1Pr!qy&^#$BT.8U/5u44,oZa>pGdD1$>b];~1hh+0vC:6"],
  w 36 7 0 1010000 1010128 8 141 [":@jO_;A3ATK3;:|@e6<!Ey4OCtQWS-?AptU^n]xL})KNF/Ojlm1_zd"],
  w 36 6 0 1020000 1020128 7 116 ["'upT|X~(:d:~T|OsA?j]VuAT^jtz:IK1t$uUi$&wH="]]

private def r36_19 : List (Chunk 36) := [
  w 36 5 0 1030000 1030065 5 77 ["#Xa#nzcv_Rfdk[3Gu=(@.|wA2U>$yY+fC"],
  w 36 4 0 1040000 1040064 4 57 ["&}21]KyG0[.SJUM@|*3&%e[J"],
  w 36 3 0 1050000 1050064 3 40 ["+lvrYZ.x.tW2@aE3V&"],
  w 36 2 0 1060000 1060001 2 24 ["/1P6Uuw%pI"]]

private def r36_20 : List (Chunk 36) := [
  w 36 1 0 1070000 1070000 1 11 ["<mR&2&"],
  w 36 0 0 1080000 1080000 1 10 ["=@~P"]]
private def chunks36:List (Chunk 36):=r36_0 ++ r36_1 ++ r36_2 ++ r36_3 ++ r36_4 ++ r36_5 ++ r36_6 ++ r36_7 ++ r36_8 ++ r36_9 ++ r36_10 ++ r36_11 ++ r36_12 ++ r36_13 ++ r36_14 ++ r36_15 ++ r36_16 ++ r36_17 ++ r36_18 ++ r36_19 ++ r36_20
def rows36:=rowsFrom chunks36

theorem good36 : ∀ r ∈ rows36,good 36 r=true:=rowsFrom_good chunks36

theorem sorted36 : rows36.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks36 0 (by decide +kernel)).1

theorem mass36 (i : Fin 57) :
    bandCount 36 (i.val:ℤ) 56 14≤(rows36.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks36).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 36 (j:ℤ) 56 14≤mass j chunks36))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total36 : (rows36.map (price 36)).sum = 326792 :=
  (total_eq chunks36).trans (by decide +kernel)



private def r37_0 : List (Chunk 37) := [
  w 37 56 0 550019 550522 100 9684 [],
  w 37 56 100 550523 550903 74 6878 [],
  w 37 55 0 560018 560517 100 9399 ["G=L`$uaXGDJcB;`_ctPC1Bp?9l(FWf#y1&$3cY9:k|X!MEkvOv3]xW@j=;Z}+vY6","zR%ZH%~@mFV;v|=cRsVC<A+GxL0~`]$1J-zm#O_D*|Emn>^eR8.-DQ^wW.|T><=)","#9sLs<pIr89SL]]Aw8_H2;)*~9p;iV"],
  w 37 55 100 560518 560902 76 6831 ["$7>%_Gk(3,G]#zl5nR}@CHbiI`XL5_sV4R(ga]M~G`2ZU#aIf46Ou`]:3`:tlNi3","&td6}9=XgiJ^BAn.hDC!]F:J}Z6A{69R7<?Gcmfiiumh=PI=`[xw)'vy!>OKiP?"]]

private def r37_1 : List (Chunk 37) := [
  w 37 54 0 570017 570464 100 9128 [",o.K0|vu^_zfb{s<`?Pp}~j%}&6e*TzrR@IA'oQNc!K?f3G``xL&V0ARywNXczUg",":us@%P~J{Oc+y!OYQef14Z!yCN0}t3`|mECc69s4#=rThvY~%kN(/%0ftc!dxXBi","YN/,[@9cisem)Qxf)dzG$,Tu*g=BIp<9.8F1l#$}(P3]{eavf>"],
  w 37 54 100 570513 570902 78 6799 ["qhuWykWExO=.3mQuc)49<kg)`0e_Tt{P=&e@ID9=0^3gHHUS^szN;FOQC@8EvxJ:",")LYZd6MW?eLW:|N9{~Mhw;4=z@GK&N3H3sIl'@A$g.3l|wl:r{>*+_xH,$-QzVrp","83qP6$?f1IEU!@PQFu>E7Aq"],
  w 37 53 0 580016 580460 100 8927 ["<_z,l/nn14*/4-J]9mtxKZdBAJYIRVM'}=sMRZW[Ly15S~*H::rJ~9,*pZ8s8.iB","Mui98:k|X(%Qc(u9H.|quK[ohaa4:w%18v7.[jCgzV2a)$V=|kS/B%R8'A=&==K@","x7j2C#>Zo{.IJt%vDc0:6d/OCOj;A_([]|),c9$DM%hU>-unF/L/YhRzjEJ/5(Z#",")Quv;k2d#2pTo%JV"],
  w 37 53 100 580461 580901 79 6656 ["f!0bgzT;!M.nWR^2N,Dxh@`>aRX0@$f.5lmO5HO2S4.#W!=pJNvW;'<i+i?DPbce","5O6ipcx'%]zA2wO9#@<p`m`pU]v;k4iZ>>w,:S>shu*r;=PzVBLsRvn?Gz|&5t@f","';)&pk^Z19bg6s#{t^0v6WF-jV%z-[R]Z8Nup).9w^um&lsn7/WX.&Iz%,"]]

private def r37_2 : List (Chunk 37) := [
  w 37 52 0 590015 590455 100 8750 ["lhU_&#0R=t=ZS@Ot?#}5,z_WFrz?&0+f`c$C)e`Ud)5vn$O3jlpnnW=DG-PP~KXs","+CrA]+v&YSUcs1O?@I{8=[cpUWqbaqo2z$=|GaCcOEkG[x,{<QlN$:+mZ00z}z^U","%d#*nXKXyx3p>jV,JeyFknM>yWYN{tQo:H_Ab'bBgw.!0XwQ@V6`%1UK_<r=wYLq","#&OKOR0gp<cT=)epaKZv(}{wFngg];spPe-`/1-K705{8K"],
  w 37 52 100 590456 590901 80 6514 ["0t1%mjawko!]l=}4>Ea*Y~))O!Hu2H0Yq8WSkw%z<5k~KWb!F+/UpKcj)!&eeD#`","/7M#N~Av;,Td$Tb=TVSWj_NPi4v{?;WyYMCEQ8'|dMTR1G(+U//5+LWD*Jk@AvZ3","8gUh/<]t~KDN,KZxko}KcZt5(73wp(GF:Af_lx6Wg4.>~>:6OAV3sz-AdJUiN+%?","%u1e8h>uYv>Sa%m3'[(`t~6"],
  w 37 51 0 600014 600451 100 8593 ["c6~w~t3Q>^{3?*V0(GH#d!__LO|<t#ZI-_REvr&07E,(wk,6,VBHD44t8TV4TG,B","UN(W>Bgh2hkg_vdp$Fg?g;,AC{Y|[N0gzriWHFFKAM5o9h.wrU=7[hlzUR$Y=U=I","|'/n^c_QATL@k=rU;{8DxY9TWKtp9yAGfTETMKQY<kz5O5<IOg1'x0<*s>VS{mj}","_{@_>UcI;6UJD`;&{zb8H+/hpu^TEv:5?I.5i#6>DP,u)-6%'&2NGyyQ%?UMF::i","-<c&e8-dUM&>"],
  w 37 51 100 600452 600900 80 6315 ["Gp*oo!FYe=trupd@~6IoK'mIgNck.iL0lE|'%H49Cjj4sk!_[3<w!r]gPiagGyOy","~F:Pe)^i~MpbBwaw*~bWy~P$A^@>^]3Nyc`Yq!<fr(TkmobH2;2)UI{5vs3A&A:w","^o{J~**(%Ru`Pn|tF>'^I)k!KO7,KPk~G7(0{S]Q_1W6VDmhs`YC3.}D6}t*Se[:","E0%ZZ,>*nBzfC#8YQ,,~fSOsWvR^pwgiUAbpL.b`SaW<q.`5"]]

private def r37_3 : List (Chunk 37) := [
  w 37 50 0 610013 610400 100 8395 ["kW4[+J>SJ*GlVwDVj#*c<2$d^H(q7%3Wev-_Q??6$4sn)QU9g*E{p6UKp#R|bYVJ","V.4L^Y%IC{%UfQjADRM/$~zOGM_{Civuo#-q+{)*q8$W'?T|kY([rV^uTzP>p@VJ","-Q,Oig*yu4gg!~t?]s|2DiZm?++>7~LKv2K%?X^?xixW4V)hy`;&]q/r87zfvIVm","X_9{<wrM!b[41rbx<2e{;ky@z=,*%bXW-`(~c?-LSn(]+d,~A~~Pl)]XZH?d+!/_","+_+V7Wh2/!ic-8va@-+GV1Te{RL^^P/qJkB_M!"],
  w 37 50 100 610448 610900 80 6177 ["sQIhy8pmkkv>TIckZC:JeSzrJ0YEnW=>*UaV>G|dFemDis_g1~|i4lv+1s|Tk(`h","BJj^gDCiafEM<J`{0ckjW:jx>t=w?1SLMM@'H'|Z>Fez~8HL*1EM$!pWlb}t$z##","IF:FXKUTvYS,]tYH)d9@%RaGkL0(_#>PLrl4S3^]^Q<K55pa?yrK]^owi&ZaVdz.","f]]kBX5-Ukr^E(5lu(iRY4^$82w|siaoq9JXUh.oT:<9/'}&_3DBuHR*,?ZzNa;o","$`.A=38"],
  w 37 49 0 620012 620396 100 8292 ["r}P6525;!EN(MyDJf;m.WNBo,xat=3^mX3;w{6B=7C<QlfT+L;7yo$fEm%$GuVPc","}!:11U3=_~8[Lo!qL%_ep4Xz(e3xYf07}[0wAwwh/2eZU8['P3NlZ~X*F}aptQ1_","tp%HzJmvnY3Q7<&{g8(*%qnm)FZ)Ak-#2Hr].4vDn~Ns*w/'C[0O:X_C['Nyr;lc","MB4cG{<0R'f.D]>U$@{1sL}Xu|(^]-=HG~{x25~[-]!Y(v9XmO$Jd.t0x>e%>oNf","0HUf,P-%61pDX>-9#)}EFF#qU0_Fh^jA)9r%U~/w}w@I?2I`dKHr@8pF-*!?B"],
  w 37 49 100 620397 620899 79 5908 ["!UM(OgZ70wBfx*~+hbVzO_V3NSRW9+qN*8!tb!2r72TGQbh9L!0;wZ;&=HLXm#}U","{5}[yAi?>b?cJn5ce'}i~Cd[pYWW`>};a9I&)XDR=o?LThaoN,iNb%wdAlpApJ-D","7:U@,APcZ;R+W%6@-}C,:.8u=f4)&|!Z0X2q$ev.GV2~@8Afd]mny|;)um0/sM*E","x[LnbK0-:e.[W[N2~e*u3L`XPJ52?$osRsUMRQ+j<~gT:*]W(x,PWY@2m+</m_gC","FnJajoacZQ$AxQSK`muiJN@]"]]

private def r37_4 : List (Chunk 37) := [
  w 37 48 0 630011 630393 100 8171 ["b{gyv_3?PR%C:^|9:_Z<R6>CV<I*n+l%v;:yDyDbPhKNIoE%z5#[t71>gKTb|2Pc","Pexp$j{Lh$3z)6@{MVkL0<np1-oVu5F]7xBzp,M[Uz1u15B>yGv^euc=Eer!fW>d","0IM/.tiRVYv1X[IK7SCzo5T^`7K'J/e-IZ|H@@`~RptNM>=Av|'=RUXmOP)L]R_X","Y(7)(pk)J||aCib@N#jgC-d-`H]~UeM!++A|a~.:$9029},Y.2w`tH^m9eo4DhWV","*lJ'/3LJlKD;H<aG/_@)ay-8:tQwj[_$6Wt.o4Rp9AI7?YwSC$Ht6v,BR&:#W:_~","q`htNWFt_Ta_I+sB')#{"],
  w 37 48 100 630394 630899 78 5660 ["iqlvqCkiAJgD^^eH1xPxR069)9e<Zw*[_~1Q#pys-8Q^l=SbA)@_C'6svExhf2R&","o((40t$PMP,~U>sj[WBGa,a$@jM%oxGA$p,EJIobpRFyWu'St&$VMHSw04@CJZ}[","ZOboT4CpPkZzy:/dO>zBEC];dQz?OCK'/M6i,iT_RLX3@(o[e{?J~dm9?A@Kv+cx","fsY:U=)_=/r_wRFB+%nhfzaiN+qAVf7XQlVKVKbdA9er>ye;02tPK~lIL&lJ_?Z+","d6@1~TXqXo>?'sgo3^_N0m4kVgX{mWgz`Wypjw(}y"],
  w 37 47 0 640010 640390 100 8052 ["Z]'pjI6ihfSs<iMW5O|m9B$}j{iW_we=8$jT,+&t4c[Cm]K)^sZ/wZ:5AOC2L'jV","D(Pol~PJ.qA&^r+!nwa^Jk(ceRL!d-J5vzTF+:G]``<kN`!*g8(t[cGk`q53j]al","'0H|7LpAfMXK3:rMPG}UnL6r)V1a7Q=5te~Xqjm0REGFmP9tlejZ+`T/(S1BFb['","Y|9@;N6D|E<.o!>ED:SetOcZ|JopbbBhp&uCqxEAU}I^V:Il0tE9%&?!U^aAtAd2","(?,[1r24$X?d07nn]Udod)]M,+H/v?kk6lx;M#S{;%4G?Mfv/aI;cI4uZ,tLi9Q>","J[8cP(gCVFrnNdOBfXc.kets!$f`1!?xhEB_0[OPl/R8ET"],
  w 37 47 100 640391 640898 76 5360 ["M.fPL`/KG]w4]x_VR:rAQYZ9'_^,[QJYY94kkgKjD{6eI|p;_3Azl%Mx$wC5t}Ck","^'Vp([oS>p;Vs.5o{+<}/4&>%Ij^l6OwX&bV/((0&KoZ6]YiDYTvyL?&Dg]3blK6","=x4_d9O66~7[:}99W2A$w8|lT2P1`Bf7c3=e(%e:[3fzdTi;!YL{^,2T$)AeOR#^","`R+[67roFGrNx[-4O#HKREsq=W~>IO{Yn)B5qbXUwW/CRfB`D=yQ666}+WC26wI@","Pw.,Oya9!L1uq:ELPM5u/V{2:F%_WK,%i'q=A#Eo`<DP3>i('&K?"]]

private def r37_5 : List (Chunk 37) := [
  w 37 46 0 650009 650388 100 7908 ["/3I0Bb;WBf=MT0BiH7QmF0})Qm]clu*ZD+PU8[6FyfGw,KSXj](36;Obg9*hew)g","Kw$KMhq3eHdEJJoT<h=wkF3>#Pt&xCl$I8z(q4W^Qp@EDAh3lbo?>;sXm7sU!opq","iFwh,`>9X]M3V,.Sv8B]nfv|#vB>~KW_~0AHR*E!sP(u;W8s4IU:P6)*R3SdH_P~","^?/Uv3kcHfNDBK^|LlN{{OHSm;e0:M:nReKnrkAJ|a!h`}KCSh86|L*]tgUM!y=m","^$$ntY#G~0j4<[4{OOfue9OY~ht]|<]-ZFrnM8]8SpxkV[Z+hK%e9phd)P=phEL`","<M=5dg8jke?U'NX&Asy#&A4oLP5p|]S_JwfE!Y;3zIPh:*IRv.&"],
  w 37 46 100 650389 650898 74 5077 ["BlOf83x}.7J#Z$pk.Zm8>ft5pG@S~EVJ&AO1{*-x<,Q73Ag<(te6+}B`4<@1aN58","uUW/pmimDaT?yeye.ZS)pZubbN>_[qIyO.=R?YCtBat=L)5X`LpmZ+gm8`G}EACT","nc*@)|?vHvs&v$~Fz?95m7/3Gx1O_Z&pWw|GeGA@gB~g,.LCel:pu6!ST]7w5dR#","c;t2x'IwG,s1dB1Pz~PQV#$.{>U]P=yD}*o*U/Fe_-{SaEi#$3ZM)V/VuPY,`U1b","2h%r*[R{+ulEw@UgdWCDq%/%j$K)9~kP5J|w+/m,zQ5jH:2;QmNqk"],
  w 37 45 0 660008 660386 100 7762 ["A.p(Y7)3R=BpYM?@{k9?'xSE(V,2!6nrs,b_Sa{;F]mgzhGD[*,gn2ID6X@u5??.","K;Yomd={a9ggq[LRf$3M`RZ?o[&:fzjRL$B!2^@up?llZ}@.uHjbEw,4f.Afiv*0","~C&@rT2lcNgXl^HO!=27e,J9`p7,!R=nb][bNagcdCxPO)e1ZvS7uUtUT;bmp2AB","[(${+8pK@c}`@cQ#@2{WF2c,=94E?$Dh[yl1b>n#,`TuCCI~tbctL{D?99E7&pM9","K)L)w@S_[H4dYh5$;T57_.yB?Yst'<j/O<^Fjsv%P#y5eD5bK,4U4w;5s{@mg+~J","(#VHtgY.o$s?9<hP+ARSZ+w2o!!]`,.ZP7:]M4/f&nQeA5Y{tU"],
  w 37 45 100 660387 660897 71 4748 ["bd@ww'FIuZ?vq8?b{HLmwO[/PpsN-fTl,?jL!L}y^ZACM#'UEmS>=M{5O&ua^JR4","2Ri}9xH!2D_56{?OjcpAGe4EuoDOs/F7L/Ydg+4e=.]2r}vENd/.TzT4KeSHO^Yt","vIvi2L(6)~7mE3nO$KMD+x>&AP-S>)q[8r^M<`G*gK1:;b9,kr]aSRXy+dN4$Jx~",")kL|&4(42Q94v5Z!HO]p$[0,00)@gm,:;5Xs2+tW?k1>L~*tMuf[#A/lZ~QTn:)J","#$IXjcv5OZcb?^L.G}T#w!5sS0t`z~+Dt}s44+xM8_SYf%]?qc+z%"]]

private def r37_6 : List (Chunk 37) := [
  w 37 44 0 670007 670385 100 7592 ["lEq|=s1|>WqCaVO{9mfD1WZzsiu=T)y;jw_`ODA+t6Df{m(/7dLN?<9fjSZzkI`N","NcS3B-pI~CpDUYbC2a1AAQ2,IIZmR1{zlzsW-H3'2N/EUhhJwh`%&J[x4A=:rCjl","P+xLN;l!T&)AD5?4_HkT#4`8@:EA4PqixOP)UU3~kv1J5-nXjD:G/._<]#Y`{^U}","{ip3Ts$qZfW~oI]aU/>R)IExcv86IvPIF=R58{CS;M/<j*|,v>x-dl+nCsXu#t9.","%{Z5rH?zo}C+(*Rdqse7rewB:T)0POZI_@}qcvRMl=sBT*^s::9Ri:pk>*}A$+0B","%xPus<3[!'+8^Whj9x>[X9}F_i9i~.WNjaYE!rZ0dW;|R,u-.'df-.j"],
  w 37 44 100 670386 670897 68 4431 ["e{7y{k-FkOTgy]k;z<q?oC?o0mKxM#x#o0`hs>-AUS/Bzcf/iR'@qTXS0gJ)|Y,n","jg[1tPpW1:aE)8n[mV;}A<SrSx.m_6y@.eM!6/ug[.w~}&SRt%,.v/XIEW+C]Ki;","Hh.cG;Ayc0V!:SK<C.}?KBQIL<[z=d*D3admZ&F_W1w-nYJ_*l.`GbqS@uFwn+xg",">sfTkho$?zE>ISrx!66F[FpLaXTrC3]db[]*qG`UE?:cinRWo5(>,wUFSt}^wS=q","~Z3RG+';gKOwuEsy3jIlKIz_t|j9/;,N&+xsjA{BO`Y+$"],
  w 37 43 0 680006 680384 100 7428 ["-v!u2K}-k%e%D(UQ>6SIE*CS0RfkG3:+JJTX.bfOXOtclfi>tsRiwMJe$&m'1*/>","{>4HMl~phjExK`Dei(^Zs/ND']byyQxWL,KLu{Q!)e>Q4?ic{)n0#]8dVe)V~>M9","]z-faYYa>v0XC@LryWA}4zg!7N9bk0WIO=K=z0f;()p^H$z]4~I>:m6Kd_SBUxbR","{950mL;@e4wz%XtEy~Drzm8go/r8e$fIe1Q:}G06}EEJgq&/I3{M=KZyOBf~|+y+","X^V(by0){TGL<[,NYZ;O64eQJ<9#`fyy$'SzQ*6m8+[/^%8z=4}RF`8M79[]!X,X","#mkjfr-8e7caQt!NL6`G+=0O!~]5n]}y`]*44^Ji=%}L%rH'VQ]@$O#lS+8s"],
  w 37 43 100 680385 680896 64 4064 [".%w;)eBC+gv5;z0HUk+ZcbDa:8-$76:Ce|^f,JCFjiJ_9M_E58zF-~h!X4I@Dbhy","X4GHj+ZD%I8|C,&JmdRA-XI3[g%UM+r.w<dTVA'85G4S??@XW|{~vuF?Y{h|N4&'","_S/i%O7d6.Vy(L2DW,b[,Q9'o<olo-Zj`q|1dt?|OLqVnQ1S#<+&y2mW3;l{Zo^n","[|R[+X&:}Nuv;x=c&mgLKjJBZVTGk%6n$O;cU&7C?85l3@xMk0Iy*=i%tr+d)3=K","%qm2uGiLgNWw>?ImELeV,C>?v>IlJH/UV%(Y"]]

private def r37_7 : List (Chunk 37) := [
  w 37 42 0 690005 690384 100 7242 ["^-RUnmLjL.L6kH$%o.F3:0=9bn|c_^O$M4aMF7Y8qBv2PrgPVlL*v0if'UZk2G;_","?@EnDSy5l-*{e.bH,Ao'(BgK4v=/h5dk.3-OU5hn8{3V[}%h5)6a6H1Uic@XzJ#T","<!Y,`_)C:6N&oWqhK9V3#q6{U>1oIT=!yT~i4ctZo%_vQ{,e_$5LLh61SufE~EMX","&nlLwNCx!Jw+dx8kJ,:AoVD_G}Q`[GsbEo5aO1#'S,9c_Anc63ZZQlDk__m:CjE.","h3F5|AHi1|,Ni(&])EzWlA7a9)(n0;+8@;UTazv8%~Q)ti|ZlSLB1xMK.s&V),Mj","$U)CTk0|0WKAHYg%4-m<Zfu;uE>eqK_Uq[+<M9-AkE'xt?L`zy}U>RnGN|:H"],
  w 37 42 100 690385 690896 60 3706 ["PrS5=Aed`t(xc`[]B0@Dm'QYs1{|R%p'1)K>tH,?QXX`WoT:sUs1}oma6~gA2]$]","&TB=N?2L$PiU%2fb1QN4]e5+bu0~YM!i#-9O0!?-C**fwPs-3#N)dmK`W7(bK([(","ufemIy3|m$ZBUm[19!GA?Gkxy9mQO^i2$h;wWsqnCSQZ]^B.9v(w=OWf&2B2gbc=","r(%M$D!N/]HR>]E#iD46S(<vq%c;~d2~9wrbGct'OGq(GMCi{g9ez0I2losXZfEW","=PCOx&poN~sajSh{E0`e,:"],
  w 37 41 0 700004 700384 100 7064 ["rfzO^&3`mD#|L:sLmYNI}L2,lqDZ(u{|RNUx5:*t#u'QRp0F=w0X>Vf>fzx*!]**",">UK'LwYSk^_1z#vkW|#+)n-R}C=m[c3IEF)_[-3}Os:R)'2pqlFh59(.`hF/K(W[","2B2nP]hU9nGAztpb;Cv_%.U<CHy8P}OOv,U$^bkRD|o%6;2rtQ8$U(XE?=B/H.E1",".pDd>=`D$,z_z3SY++%W`H_U|?;0l*_|y>!&b.mbOLo25{*EgnZm<AZ)v..N1%(R","'e:l+(HSAEo$==Uf&'t7i0Wjr#r7Jnm!H,Qn#Vl~=W^U-!oYy$*s1bapH6_Ty_Y0","J;G.!LuZ%X-dX8$at18Uo{z7~z5<pWxm$W_#?w()NHM'CwJj|d@Z3b1FVYMOR$9}","#Fo88N"],
  w 37 41 100 700385 700833 55 3303 ["#$B:aE5NRI#,W2Yvtrrfp^k~Duk[6g$H=I<12yZjG7P-jy==[K=FB~zU#6Xm`r{_","Uw`}3lW'pLyE-I%VL$=TA7qX^XhoS47[%RqUQG>6H.<Tea30|ULXMA29p:j9sf3#","}i?JRfy.+Vw7fF]?L`fKwIw-o*AM`'LsVW_gZ,B=SnTN:Elo<U;/.`V,]W#'UXf-","}R:39{F@U`/X*0'[l:J#PaU(XG*fgf!X`_I!NWJ_L@s8J;_-44j4&,o{(Lb`4{RH","/6=h_ruQWSI)"]]

private def r37_8 : List (Chunk 37) := [
  w 37 40 0 710003 710385 100 6855 ["@GNwK8'vd<<y]FG:9%!*(F=l_4!v*'O0w>5Ej.P|C_w8*UC_O,Mmx*r8rU=+k1<c","FBmBcVk7od4>ubO%x_Ap-@keVimE[Xrfgm.V~K4'~WnUa4A%HY<Oq8BrG(M-U,L>","b`fZLj5GT&_S!?w#(mrm#cDik]+8JWcl'bWKKs$%QavCi57|0^p/pPNjS].X>ia'","}1(:rD@>$.6FhAvoR0Yjr'[1esg7K3Swh?7^:{6q;Xsxu(_/~aj#,@_Fr+,277qT","xBM[dHv@f`,,Jl;Z^0^#~49oC=w)h~Gm0mpG444gsjI(}+`aYbEWyUK_u5$b~[>h","j[hJkyYMac5SNb!BS^v!L~O`1b]*90i%p$M~w9c!71}>o*Tp5]uJeo8dH6%D)7Yv","1fBf4|QN"],
  w 37 40 100 710386 710832 50 2915 ["LA;Zv#n[[vlFJ6Hbe7vg<mQn~dFw}ETJ~<vbm?DF@5,7{_;R)A[UshI0]<g10cI)","W+{}~0Q'A@,yWs.w4`c<zuu_srqX}|k8#J9Pm-WT+c[ulnUw&(m%6!Viet2G6L~B","np=4;O`@Q/gt'n1&W$:+ow|!&T`FFC-CE9fUf;#|bM9G'h0w9r1qT_r^HBYKM;Xd","iMj_ywS~JQ%N9vTrbk^+Ox=0UQR9$>giNM>6z2D+1t4vl;F,8#"],
  w 37 39 0 720002 720386 100 6650 ["V,*XdZ(ETp-GDI*=MWs<?~I2dW9NGIG?M^3{cpICtOFWx4.0|bGF:=7^[nw*,_AF","DKAuOPE#o=[r!Z'.ptwCHn+DZAV9'=p|W4<2_tnqMSu=Ng,(L)km;E=3wPA*z[,r","#;l3sQY,]_'i|)B#Q.TJoHsI'_CuOd?=iWao!=53IC&n5{EF71pgu+$rF^56(YT<","NDUq2.vf[~fT=i5,0KOq0.N|6[}6Ba{;g#idXzIDhc~Bz2YgRBa{/v$mUOx/XeeE","lSV$)3=-Cr;*NLDM+8lOr8:Vz[i!FQ_F+pDg>W(1X$g_%X4(@4g.M;TWp{I0hXR&","X2N.gsVE`#Q)+Zq9S[v5t8Bv|eYE5xZEl`GG^JX|uy$;`oUdN'9a<0&d+[e5ix+u","$qCBxPQT<Gh)E4-~;w(w|BZf"],
  w 37 39 100 720387 720832 45 2557 ["k8/hw#=+6@&Q?[g=d]RYk>pic0j^DM/hHo1Q{3-T[!(lbuTZ=*Blg11)v0+X(]Q:","b79gW4Cu%4>RRO;pYHWAhP1e}S&.k=l9X*d'lgj9;nTs2O6Y$JNF*sJsny.x]z=y","`G+[T=&~FiyQ<9cd.M:KbhsJFL1jhZY:5s[8r&y$p2YUZ5IOTBaA!C=V<d9k89:>","Z*-yyCvqx1r7vi2_BOHFlpS{.MiAc`}*i"]]

private def r37_9 : List (Chunk 37) := [
  w 37 38 0 730001 730388 100 6399 ["H%Yy~qGfDZgNI5t^y9Pl':!gZ3|F2?k;f]2Wcf{WWlJwsY4vB{lA$.{Y:'~D<L.:","sQaPXzAG<IBA;RHp7lb(z@#[zE}E*d,,Ds8&Ltew.C'^e9o,^=ch;dt|2rIi5Z;-","u]#V9(Cm@*JX*#?{JkuWEs6!TPZ1]Y{J^,].prb%!Qj]cf?`mcM`0#1'yo3vOK=D","6sQH/{,Cu(*OPgw[fIMIq.8$hw[uIu)|:8[PW^Iz6Rr69L|anxvR;WWFJpX&JW(}","KNOT6I{mAjB7.gjfUbmzbmi9V8^MP|erv-j?65m>7T;m+&tU8Dc>Ya-{$nk1DFS7","ukY0MqCbn.)P8}zc}do!e9UU0Upl2yCL<Qy]mtC_!2EM:em?<8>|:[j}GSv9chbG","+>!N7.gO^]cihRIRP#Ll&ucdIkO@<sqZe~0x"],
  w 37 38 100 730389 730769 39 2164 ["6!mV])L{;_RQ(lfcF`)2Dx9ZYUsB2GIl'!Kr!o+:vtzn_).XB@;6U@?h8No!dnko","d-~*2Hr,/(#qc?TSbfi?>TiP^@G#YiraJh8q$lI{/huic1Wvo$l^KbhF{MvP.(zY","Z86W9c:;5AVTE%a&vNS0}FI-h2S/gdHlOeMAuWAoTS(t5@a!/K&Wya73@B5PV[+T","#:&Y~-"],
  w 37 37 0 740000 740390 100 6158 [">t!]O%W@08+VAV[la}12QwHTay.ZnvhWp|oqhRl#iA7C,kw!;IK(+33zuL}KV.p>","u+E0M<<Y?ewCRF2XIXW@|}dA!V=,'8#dW6:.L@qijOMG5`!6WP+`~YSSVZ8zIwML","Ap?Z!,emH(TBf+~ii+?DAjUE'8,n`zHOm)akpe>_O=7I9K2,4z39WP}:W_a$c},K","JO[.oxXi=9x(>.3gZ@Po{~(|5~-*VJrm*[u1/X399_=h1MCHQM-$X8mT0w]?{ZNR","UugUOwQ-8w1mamcbQ,tc^CX1VQ4Kt;;M+wSeclTUG55%8Y-mzP=,)kfz#5Lw~%sg","ch'W}0GssZH#JK^e]uL2E`bR]']Fe^^+lxE&'3+yyfV9`KRRbE5B2O.G_9|(MH)Q","$X)K?n''FqGwyI-.$'j6P;R9p^5mQ[+lt~iuz~fSjw0kru^:FwE"],
  w 37 37 100 740391 740768 33 1796 ["nh?I-`+0+U7;`tW{D,p7JA>Hpq6Em@kvO{u,_Sl-HY2dF{J`HQf7P+[Ux2]AJ}sF","?~j&PFW|rVs+~!YOhWp:clnoSs-O=v#E7_XEuA2ak|6K4:1~Gxi?j(lcjhzXE7`z","u#R+EJCG2P>2D[<jSu0NYk0_GL$RA|xmEk^03]i"]]

private def r37_10 : List (Chunk 37) := [
  w 37 36 0 750000 750393 100 5882 ["}8(b!%oHJCD>a:.>Njmd80TcP*%$ej$]ly%7xnmT*iu!it;%|`dN3M3TEk!sSb{d","ixj2Ws8EKm5o4d&Cgu&5JM+Ly[og`n!E%r9Y?*<MP^,li%UdZeixu|}cwSZ,C|Ig","Yj^ozB}Y~-WfZro>:R~m8cfH2^kPVTq]Okz73ICXenU/!2_D0,IDPdkD8f_L7qiK","NaxLD}_UL|>TnG%b!W96Ml_0C4Q-sM+!%N0%ZF}`VbA{c.-p,YO3?8q&QuwaYgA(","eR3NwUS0G6-Go'n@xFOLN]-Gy:)Fih?)5U>oMGrLh{ddNahG[iuhy]]tSn5ZqCe>","rl7&tEpKbo`I{tP!JWW9o(zM!#b&ueDNia@9sdODZ`9MRz7oX]R8IwB#W(HlO6K4","#r{5FxI)M0RAuM(`)XQ9kZw}H80Gkm=[;^}0*J3jR<tHrW^g1fU/Pl?7-`;'dCzF","5gIX"],
  w 37 36 100 750448 750768 27 1446 ["2)vWA08-JTcGO>*np-C;TI!jLv&ovC]XlA]>W'L%4Wk,cq,[iMk@S0_izM7N>y[K","Nc>s/9<i+hvl,{9+Lr^Y%=;CL/u*z?o>&(AC'v5NpKh{)YA(2d24Nee2.EL[o1-$","$+4fPRw!Y-l"],
  w 37 35 0 760000 760451 100 5627 ["SU#&.H1?;q5V~!mg/x0eF}Rvma-kp-C7O1FHa(9~c%l<PgdfD-+itke:iGIZVIgS","lMY,PHS58menoU_'&jT<Thyouzkzew%0-i`k$~>lDdffF7,!CO2X83Yxd#}F3~~u","OqO47g-.]?4=Y8FISgcM,u1,J}j,^^dyGq&tkmPw|bf&W-1C2Vzm>nn#Fv{OS7`_","U>X0-k07?vwnIIwF7^H|!JDa~A:bO`S|VCd:oi9l,sBj~pC92kzQ|:XvT+[t@<O{",".g!Jc;*e7|pkp52?`b!!*UrRiD3$1SjBxKl@)idCT8fYaD?{]ai{WOT9E2!OEyGG","p!s1lbpM,'=<j[/wy|R@eY3y(3<7,v^!cRt[Q8>hRtPoH:CG3ly!xd'A=Y54{O/G","CiCCP.=@0X:h%b4%:j^m!'Ll:S;27sVN$=Iph!$=Sqt[o<%5}fLqr.uUke%1{*AF","7Ir{-aOjPHI{BZRwisJ+bGS0AJZ"],
  w 37 35 100 760452 760705 20 1053 ["){;gUz&Sl||ywJ6uPdth-DV'b]@+YePo/B,h3ltpnU>$<hys=xH#OJ;pe@ie:{@`","*J'N|V`/TJ6_YEU1pqe*),L1IqKdd+FBJ{|cg~A"]]

private def r37_11 : List (Chunk 37) := [
  w 37 34 0 770000 770454 100 5386 ["=DtQVT:$-^jFvK}0rK)k~G3QJ@XWBR+4'oeMe@qYS%iVoY+WPCm.uv#URklg}j#h","Hw>/UUA;^#!ATlV[yMW6S;7B$8:dlU9>kC<e5hhR_Kr-rd)s2T(n=njWnv6~'ZG/","mVW:y@;)y|rDK3'-tT48VbW*c{7+M2*'5BxnpQ5a[)K#RQ>V67ZD=}_U,=E|g8We",":z_J#$lTz_(Ba8@hQcfs9Kc`1PJr0b|hz26T9ZD5S)Q@WQce$=^#MWYr'lZ,Z!SS","?N?}n2Oa9@=9Qx,(1DH[hJDl)*lvY&G/$h@4g%w&HHdudY[]]42O<c+4x.PqhZ,)","Gnib@XX)n:,mF|m|0q60EH:CE[R%N(~+wcB4qf}n|TvXViUDE$QM?|#=X-hY@Wi'","4lHz{LEX8VhKQD6ni`,rf1$91OWI#(xGuiGe=&>ZRkDQMK)IJ._g4BjNO_A=[2u-","#eYi}:1*(dHD2o58l,m+fAe3)tE.J0O7HW4g3Q]%"],
  w 37 34 100 770512 770704 14 727 ["sLUE$l&L&yH_$Df+jyjIO%du5smz3:wbT=@%(Oi'+DFuS[]T`HK$Ul[$?p@/R;?)","iqwz9^"],
  w 37 33 0 780000 780515 100 5173 ["ELT_QRcV/vl`{d<HCtat!r^!Ou6(#ZB3^02vyr!V.cp{6)se_:mwN*scOw}j'._#","OyqzRrS!mNE.n/I`A9a9J]u{uk^*!~gU@;Oe@E1<_PEz';lBGazs>Ng',s@%H4v|","P6gcFcf0'h8`a7@BE5695;B0b?t{OVVXZU['~n:Y!Lz7yLsEmLvK[;4KR+H3Jh/K","j<-324jOT5h-%D8:emo;u-5CNqgWtT9G@?*@-ag!?M(r7zj?I~n}S.69?2q?)-#1","K#BHTmh$df+B3:e+WRM~wLS9rCSM?~1|<h|[_O%4S6|W'3Z28/%@lH73|qm46l_|","iZKlKsYy`8+TNbj2H]#V//>lh`luYBsce47|M^,W;_9t2f1juWy!qdG!W`Z+rqUH","QRyfHk~++'jpN(XWNy!#j'y~eB,d?!h=ukX9$3}P<oXXNh,{DD-|_0?H/Hd#.>KV","Gq2[gM:SfzLwUI(D)mXAS4&{Ypx!5[&je5(`Z'g$I/AO1|'ZbnMM'Ka@"],
  w 37 33 100 780516 780704 8 411 ["$~:GN~$Qn!kCGcvECv52sn;~9NnIE=]#$9$M2f1bR"]]

private def r37_12 : List (Chunk 37) := [
  w 37 32 0 790000 790578 100 4975 ["r^2*FLq8,=Ul@46.M3AO9[sV+KVh[(z?xnIa1,#GE{v;Phy8+rN!9H:f5AHt;r'7","S];gydB7>st->}a1DgD$-~%i?Z~8~`PE0|%Ah*rn4B}3kCY[%xLkpBMhz?[>Nrl/","bpw&m.lq$(Ug}9%4WY3xUZxxPk@VJ(vU4.^MOfS.']o|VE^e<5U;p/17thcWU1*F","s'Ze;9&:8|Fj%9iKL>%M9(,!iX2H#DYJ26;T5(GH%uj2z(%X$o0d`+'{jl9n&loQ",";m.TcNW#m|#or4Fk5}bIKH+.6:&P;m*0ik5DDP3*MSZb&y<HxTcBfRjqSl;^N$+e","2:/5;%r{L)DJ_#bA]U5>.vWdQ+VR{*XeJ~~%b#Q.'Ek2fg1l4j}qv/>mLo%K;0R'","*V3L*:%%3iHY#Px^F7.J2Ti0W>Iz{[LQ<aHip@C#DT1R)bz6e>!h'!{RgwxiJx|`","7e,kP*|pbB=aEum|:yE'~2hCI_'8?UJ+.}IN02vf(=h}GGZf4^x(-b+$f@orf[c,","#)r^5,.#F6x8D"],
  w 37 32 100 790640 790641 2 102 ["#i2GG<Je"],
  w 37 31 0 800000 800640 96 4601 ["!qQHThc6eZ1md^9HD;M*;yn~!<+[k5^9/YcE$sdpmfX'6(r?G+jgxfEIk@$Ti_4|","-mhU%,!ZOv@d*bRbs-x(qO|huF|w-K6c67LUI>l,8Aai*DOcP4>M-@OzwOy>u.??","djTXqX20)+pwFHQTYWjb'CFS,TZ49lO97<:Vt[[R=k`-i<IoPxfQERG3tbCOv1-(","B0t=r.;B;`Lhu%|Oi#Xi(sc*lRYRWvYL83}.Pia%T]<!qqdOdZZs3N5`[Y*[>aIE","kb<p2BngS;!X=]qj.rTVhezvF+Nm-To?k!#>GF&RliRGUGVN`,>k>UY!B5Y2;B9,","+~ly98tJOb1zMS?unVtCa:&+kC.XND5WkjrOYYK~4t{S+:+&1aYxT*s8wysgom-C","k/F-wXot?lBee[UJ1k;0eWS!{]#rnVoc-(#}f]Swb;E(+dsGoCO|yswdA$Q,P^2F","$U.>!Nr~B,!glZ:*^LfwbJ~YHEtuf_2x$,KN*pGtBphA>RH@82H$0NRE$)$"],
  w 37 30 0 810000 810640 91 4201 ["t$x6D/L/{)KQ-s$aX`k30;5Q0sRL_2:AmWBhj+wmKIhRQ{{[*p8YxEuNg6RZ$aIO","aIUg$xuTJ<s5CHn4o0a_^`^q][>rCF~:KbislB{S}&.V#[3pz{'!Ry0{]M62Y['<","-dE1Yg0Au+okNy|fWuDzG:eKNxQ#h~vlB,(4]TkIu9?G1&r3?w(]tzkE?OiB!A+|","l!io0bd/1iFWg^a?sVK'MXJI[LN~7jTKK,=idOKKLZH?cw}X6U^goPzVhBsr6q/K","F&1o*3?grsn/q*f@N`e2ewv!P#?<k&#$_13#bLSWuYk5YS`db:^dnW]3>v#J773A","Iupc?vm'S{{#l4Ouz)p<^W>/;Z7d/dshh$jU[f~RqKw2;6j(jSTx1-%wVXRfppE'","qIF5=dW~?3,aJ^1XmUPU^N$=6+p#*#JXiYo)=55u1z#rG:K4;#3G^P]P|EYl_u&Q","*vSk'#dq5qd^J,GuEFGWNR0)vK(<UegHpG0aR=r8C0Q"]]

private def r37_13 : List (Chunk 37) := [
  w 37 29 0 820000 820577 85 3779 ["~iijULC|[Fm<%_~z~C|xmW&0;0Jo2`Uo!T^T:?<H7;8/WO}}l5^4)vh+N3m?x3!d","W=O:Asqrwzw!>'w6O_bEVf[y;_wQ|`8Kse+H8K!#FG6@&&$[T={Ibz]*}V'?YbK*","W6T6v&._N1IBE$[&XO7u@;/{yt]*[ev?^Ew5%'G;l32ZnZ~aDJn<s{rjV%r,[J'}","z$$mxTE?A8<[3,B0J[/H<^>5:!.^h|fU|~7+{&`Ltxed6R-@,i:4lw4Do)?FWzyc","1TlsQaauOFVV5fn5j;{QJDAgN4/<CctJs:Sa!)S-:?X_yedA>j8COgus_<sC70NO","?LO9x,W/wEDm$,x%_:TgDJ9Z?{*Cu}kM:c3IonQ_7,^QPgt<{b26]bshsP.QD.yO","!zp(yShSK+c]I_t<sx?8v5.UN>TlGe3aY?23.Hp7[Jo1-}vI#kL}v/g8V>`lQx3F",",pl&dGlg8I'0lsW.T#D"],
  w 37 28 0 830000 830576 80 3423 ["eC(YeqRy}h/f!qzF&J%GiZwkaS1/-YK*;mo$h,^hlwl^I)mH9,&$t4YhAEVvcZ`G","_x+MfIH]L%.7'6[z@R*!l-iZl6LDRL)Jflz.HzF6'NAl4?40|w/Pi=yY<nRG2Uo4","@{C9OD6_q.X`m3ewcNT]i<r7aRV3>~%RNYtMsK]EF3b<^-V(OFk;%f1;_i$-~<Il","Fa!(g~d+]_F}^Hy[{G;V8h{7mTpR;lP8`k{r{v4w]8*6RNi6>6$GyQ97Ro@,vp:9","]M%Yip_m_~Vpemyj@<gYb-u|P<|}Ko]`kqTy12s5[='p@wv0Qd]9p:clTgc>8|?U","aUl;s!oVO-;M<]HxJ:gO3c|=;3z0r$eu!P<pV<Ry4rAX#c[9*d~BZq3>$dlH_bW3","-!N<MtCJHaKoH-jG7!}A8}4'LTolVOf%N}BqEXyP6f@+-'Rr2kI;hc^0Y/"],
  w 37 27 0 840000 840576 75 3096 ["!ph09>z{}rzN7aZH@VUE7;g:RkH,xRvA3bxL~<AiJE,,=(bHr)Ft^A_<rgpx9/GX","M)3_~OZcMPG|Qw3bsw~b2W2yxAOm6&Pp@3Z^x0?j&6$$Tr>@f/xE)`dwce~ckAc_","fFhyr:Ugzqm:}z}8UyoarK6:WY~-=>4OX*H3^|ENb!@Y6Q%4n`~?jmv'uF+?Lfj>","8~r?z(q5(tAnnq/o2@Cc`n{7by^aT0*x;^4(;b,QG$>TPVWgplAy/s*YRtJyO([D","zF=pd=#Cw,3Tz01U/%?9_r:zhq+1r+B$nzfcF;xWCx<P?xA7cr-Gh.Zvw_-rG.Vi","A.zCLeA<bs0_cp%mw$KO[c3Mf,T;gM.lA,PH!I$LTA=|rL-OY'WRsI0cM'[t2VWs","GK3uAHTdZ/jUg~dpv$NM/'#|fm[QCvea{1br["],
  w 37 26 0 850000 850513 70 2780 ["1*g[!vf-!Oc`q+'Y39z*>U`opEEtV}!h-p8HE}N1-l1Sf#SH<W3%5YrG$4ho,q8n","g8$2i222*+G+Pm)t5va;Zz[!/#Be{x_Va%R-(YdIo`q=l]fl6~vzI+vLW9>}4I6T","fM4L/rvfRHN#i|P5kd=*E9^htuT/?&jI[?-X3wJm:f[!P=YBE@u>U?J~Sw?,Q&zf","O?HK3&^B=+z=7'1H.o]C$1n5ehUBfut{fj:j/H6#OSZyFWvk9./<B-ec;[wZ,YT^","Naw/c0?q=$F%?G+kim+[0WKR*B%orfFHxAf~X7YJx30GBGT@?kIa<Ff5^3?H.$')","H8t3c1`vO$e@Jn{p-ek+d11`Pl-He.'m}bJ`fv20HQ0yK{1r$_'.-3/n}NEi*3fc",",V29+j.^EG%'d(u;&R2w"]]

private def r37_14 : List (Chunk 37) := [
  w 37 25 0 860000 860512 65 2485 ["I.V.7P`A>s$dX-NaVEDmYKs'C%5PluN/(Ot.r5'yY@MBbm[3P~o[#Z8C0?[5wVo%",".8(I}8t%|tZX2[<$~|Jsz_~.s}pv/}mE;9p#mo_K,(3<~}'Y!~2SINv~}EfNVP`Q","S8^g&;g:S=R|wL/O?1mG2&_kHceE5Xque&2H?otgMs+%D1BFn4H`(cx;I(^J5sW$","dkbV0H&mg;p&2TAPVI5O*`M`~Oyjo[-eJ|aE{La%*_?.gtsIc%Da(5[|*03}dUnz","L!~<+ky=?@}M!txBjzh6$u~X-B|t|.<Au(x~d66IRy:^d_oMfD?+5+4ExR:x:?yL","1F4J_Dl}8bLd2!1D:PX]q{tMo+o4@]<Q[qq9>L/!u:%1avrfs4W0G~'*ej"],
  w 37 24 0 870000 870512 61 2246 ["}eX^!>sp%K|SdVv0|{?;#u%(sz|71r|^Bg*XA}g3fUz|Rx6dB;,mO|_^A3.y?zzA","t&2ecOR[_Zf2wJ_cY{rELUc|i/X~3vbbe_NmL6YB:/&:=zg|9)ja}mb3MkNVVY1/","QeT4UGa$PW;J6x~8;CBrLQ(%Z4.IA)Jh_V'0'+LykH$.-;zN~e!otgXNJ%PMjK[A","e,bbN'FGRq/stM4jL?]h'3a.e,r8:0]3A9<[FrfiU}7d)Y/.~H~ZeugLh+S;2E!_","bFIHxL8JvI!FSI-|gF,mJF6u>~F$#k2l=ILS,3Yf>u,*ztF2CxN7q2P,/Et*m3R1","%-w9:>lLDo9g`PWW3p5:Lf;R^w<'t`vkijjaY:gR~6r"],
  w 37 23 0 880000 880449 56 1983 ["(hmbJIBh&dfF$e&=TQ{*~>K6OH5-t[euoc?<c<.7+{F_k`RPVw_e>'h!Uk(@&S+j","^byh`(-ylt>K{A4pM.|2,E5X!DloR9iZ>hs'xC/e%FGyyKnbV:9[JG&(I>+(1@{k","sk@)j9WGrJ.@]q.wBn$,@}t'RjrTi2!|$56]$i%-9nszTZF5BOcLeeEWr#qzeeoJ","F!2_d[;D}[PQ5gDFkaW(%7F)MT?k<XI7|OMd!wKX44QJg`b!iX^,z(_l[!9Xg&UY","k[^o3~:Wj4]+HH2A|Zu9,L7K6/ASRs1p']bmVs,k!ezPilyeCj[PsuRUR3*h8'KK","qB,x-O}Ynkge@L9>%]I?eK~Dk"],
  w 37 22 0 890000 890448 52 1769 ["8JWwv6S[m!Kp*t@Yh5dqqR/t*vI`;nwKNX#$1I1GF$]/.iTbbFV2m&T0p=m?hWlb","TD,6I$aZUk{pnE7-!v*$h_G3O:I|Ag.BbHWDprc1US=AtX[mM{`)E,<W~r=/wnWw","<dC?y'H}rpIOr^=cwA#bO);2]]9<Lv0bu:T,X0k!8aw~}<DFT:j(G_Bsk=<k4EnG","7.V!o9P<E4]S@7O8@E{,5`O|^Q{cZ'Qe@7=ks7ee!9%>4~=9U}INw2>=.WvT'pGQ","7:*9AgPx8q0Kg)19sT2v_/A+tP2CGUl/tNzyQvS$R~_J{l*l]>MrG[){*;5)@wYj",";z0Xl"]]

private def r37_15 : List (Chunk 37) := [
  w 37 21 0 900000 900448 48 1573 ["ItIGb5%nZq6%7Q9t?h-.-RDRpd|^^`&>![c#PH{i!?46vS<vI+x,FDmuj9O1nM]g","wsh32Ec4cLrGV|,@cLN@`QxUy+l|G!0MX}'[O's~yP'Hc,&w763=8cjToNg8'+>z","`jG]19OLz!5>'>EKOW*tX7:'{lB/7#,-$uvM#Bv1QCZDep;Wov>+^jQMXsi<B[Q:","c20:i63%cZRIti`h$zM5|NIPqC1K)LC!GQ6*DvHxQ@_xm7^D2DlmZ;<y5Q'TKX}C","t{5D0YTl%8(-lWU5S|9#]!7Uf/~kJbmxSu`w@/e-ur9DG5'BI{Cw"],
  w 37 20 0 910000 910385 44 1383 ["m.Uzq/{*2Ws]@2|vU({:$gOb~-Fv;r;CbBx4|2xX$-!Z)H$3y=mc`s.x#bqE)'/r","[hu3>Hn_*WZ#HD8f1{J9FGS{R~Rl*vzVq'6NGu^*oGq5c`M*h}Pg<w3Cs&ww=u1L","]q}}0R{%D+c*v2FdX-`?Qh*IyxG{@/&irk$z4r&Y:#x5=`>@2Q|3coNu@xF3%O.w","BG|9w]#{|Q&0!X!ra&{ixh;rX(%k/aJeRo;?MTF~Lw;.o`i(_D<@h7B;LjeSJd06","&-]<QmV!|[6odPav{)'<CVGM}i{2@TyINHF}"],
  w 37 19 0 920000 920384 40 1207 ["-{P<G#Vn/PK9Cts&t'Xl')M9wDX:&m`X&#_cJFd[BW.WZx9ub#+b6J_-bv-x=h#B","E+,6mZBr}f..^uFkp}KF@o2|9wfi$q]4DHIt[$3&zfi,y:B%(4G`VDJ9mUw,u$3U","ABA)6khOT:#bnYi{hs3~4S`|IV:Upc#FI9H~0,xtNH>[&iq7,oY*cp]Z/EQsOc#*","-'Sab-Z}]Ws#7?>gV8!3O6l_Ou+z$i/Pc24KZv2-~iKBWh8kC,j?%p~IZ**@@_?]","'ox:N.aph?H["],
  w 37 18 0 930000 930384 37 1073 ["TaSE[6zrDkW1;X34js]S0k3%:_o]8]99ld@`JcZ3#A<E;v|yJ~i2DWje`@b/l+fJ","/0H@'?RNBEP`i+fd8uW<G;u9cxV<o|=T~ET$m!-(mE)?qEPcSUOv^+UvT{B(&h-S","#<V#hv@cD[AM[VH?sF,R/z1[8jne~DMjN_`0BXBpx?/L5vyO@|oSY!?18uT}:jO[","J,JQ~@3FzHA%}Dd;oWh,]D/~'twLKtK8I;,'=$d6m+j7>D)g&2R14Iko"]]

private def r37_16 : List (Chunk 37) := [
  w 37 17 0 940000 940321 33 917 ["<vEEy-2l*%AvRgxYz>?$?H^(r1#[:cYf)F9%*v.7,HU$hHgj4m27,]2wAf/qN.LW","+6GIi~>^{aoz5L9S>tCXNk,&(lI&`uo<?-TuWKwjl]n0@d/d'0+]VxH=u<FJr_PL","6^2a59B<@dJ-cGsL6A;#(<r.9]Cxd%e#2~K%T7~#q):z>xTd/|Cb|>,}_DaS_v-/","#*R(j&XD{/U,9Q@%3v%Um%t0QC?bSGk?J"],
  w 37 16 0 950000 950320 30 798 ["TilOvMPhID$Grg0.*U#^13<A1)w=.<CMXR'Or[LrN!)m(YB<#Cs7eKRFv{frgxyw","(@=#8yWp{L<wdZou9[[I+vLo*Wh9{e/B!:}GVz!$CJco/m`3esSIc5Z.pO}f*X;g","@BfmMuf2i5~|NSR;2~Jmq4MJKNcP)k5OXxanv(=iqS,@EG!:</^xT>_d.AGbEkVG","8HcIM|nh?a#T'L:"],
  w 37 15 0 960000 960320 27 690 ["R9^3+Z;T|>)8tq7mO/pa#cpfh+Z8=$BzO-!cVRBZm>O=F(yfshgFAO~elqM#$]VV","%6mIi!ke{-0z;YjqjTfYU)eP7.@|35{+h%K$g=FbH>G;[3l#l/Tw|7{75u[^!R&e","[hE/P|S&E/dgFKf+@(cJ>Wf},.Bx,$2OO5d;v?I#L)'pEhET=ev"],
  w 37 14 0 970000 970257 24 585 ["ZxwLyhB.L`W#>tEbo@je5pzPquR`E$l-[@TMm/L(=8}zx:od!9smcfN*IK_;xX*'","2qQPM?~-B]^gOfw9v1o}Z,cUydx[](tV4n!_`;nOst}qpD^+:868Mpp'bG.V4lL;","#L=mpryytbF`Ud4`e7&AbjEe3;#TNm{r<4%{&"]]

private def r37_17 : List (Chunk 37) := [
  w 37 13 0 980000 980256 21 489 ["('03EH2n[N?ss4)ucGA_K]P;@K<~V7twMr!_2}?3~_yjznif6?^,Sr>vl}had9bS","D.dfrH*Gr+dqMKt$MHwc%rD*,SEBWy-c7G^UHG)[w@#SwCh1Qdf?8jE=D>:lcU.I","#Ex3W`dS7a2>R|Eu"],
  w 37 12 0 990000 990256 19 422 ["hUZ!UB%4?C*S%R/LOs9E/0{in,rdSBPg`ZoK`h?>r8.U{]DwG&rol,MeYR$j~yU2","Kx^9h#!U~nriB~2{2{Kk_g2<>L1lpH272oQ/a*-i)sTBPURs2zcV1G7TO0r.15A"],
  w 37 11 0 1000000 1000193 16 337 ["pG<M5p=p!oSrEDvg),nZS,ruWP~IkzSbLtRM&#,okFNE<k_9JU1-wNk<)q;Aq.s'","#t`8eW&fE8KKZjx%{$ZtU!nL9yB{]>6Q1Fcs*KG_D84"],
  w 37 10 0 1010000 1010192 14 279 ["R-7T/WFG^wqA?BM4TF@FM_m%f+?l'PW=[8XGf&.Uva3%;RT8YDfWUJRNOV&oTY|;","2~}=D@7_)5Z=(EN@A$@6$qj@{6S2P(RF("]]

private def r37_18 : List (Chunk 37) := [
  w 37 9 0 1020000 1020192 12 227 ["7LghGxLX!em5B@rlOFjM{9cn`Z!HKJ]ityS0711KLIuqZc}CUWZ[{%E(DW=ensgv",">AcmBGp,dkkz}"],
  w 37 8 0 1030000 1030129 10 177 ["p@,{94,']+42!},##GN(iXsVYmMZhKrDb{2L#}uE7;#}h3/(#%:uX!|RI:v3Tj7+",",-Iq"],
  w 37 7 0 1040000 1040128 8 133 ["$30*0D.)MHJ!GkShVl$?c`iQsV2;&zxdX(S6C4&0?Zr9YeKlPQ$jB"],
  w 37 6 0 1050000 1050128 7 109 ["#54NY-y]el{]&3bMkn6m6OHSrF9f[_~QUAe9yB5abO:$VV"]]

private def r37_19 : List (Chunk 37) := [
  w 37 5 0 1060000 1060065 5 72 ["VU%QH-)H%_x6nhjHBp!|?.fK>MZ3)K:"],
  w 37 4 0 1070000 1070064 4 53 ["HUpT(r[_aUZ2(IV6w3S[rim2oW"],
  w 37 3 0 1080000 1080064 3 37 ["%-zgvN]Gsd)6:=%Gj"],
  w 37 2 0 1090000 1090001 2 22 ["#+_o=]eO1~$,."]]

private def r37_20 : List (Chunk 37) := [
  w 37 1 0 1100000 1100000 1 10 ["+]L]-"],
  w 37 0 0 1110000 1110000 1 9 ["gH5tY"]]
private def chunks37:List (Chunk 37):=r37_0 ++ r37_1 ++ r37_2 ++ r37_3 ++ r37_4 ++ r37_5 ++ r37_6 ++ r37_7 ++ r37_8 ++ r37_9 ++ r37_10 ++ r37_11 ++ r37_12 ++ r37_13 ++ r37_14 ++ r37_15 ++ r37_16 ++ r37_17 ++ r37_18 ++ r37_19 ++ r37_20
def rows37:=rowsFrom chunks37

theorem good37 : ∀ r ∈ rows37,good 37 r=true:=rowsFrom_good chunks37

theorem sorted37 : rows37.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks37 0 (by decide +kernel)).1

theorem mass37 (i : Fin 57) :
    bandCount 37 (i.val:ℤ) 56 14≤(rows37.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks37).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 37 (j:ℤ) 56 14≤mass j chunks37))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total37 : (rows37.map (price 37)).sum = 328055 :=
  (total_eq chunks37).trans (by decide +kernel)



private def r38_0 : List (Chunk 38) := [
  w 38 56 0 580018 580465 100 9620 [],
  w 38 56 100 580514 580903 84 7788 [],
  w 38 55 0 590017 590461 100 9354 ["(.HR!Mo%aJq1}{GJA.8ycc+K>RD{lahMICKY<8LR/Uas$C+:{d?:&/z<3GP88l,B","$w/Bu<ZrSos|L<<_&qut^wXBMB-0/Zu),Z)l}=<5?6%1Je[DR=ne(,Ry|5YSZ)j[","%PIv=K';D:<fHiLNmI&{Eb^L+G|Q^NO"],
  w 38 55 100 590462 590902 85 7588 ["__j2oLYgzF`|<B1`|J$OAvo!%$64KZXDih>6W<[+o=Kr#YQx*Ny;H@$TC*@5*J^'","#G_5yLQ]%xoOK&Iy8w.BEt*qHrzWeAux(IfG5%Irz`hzHJd_P)_^gzPt^ow?;R#G",",nX{.-jS'S$B=*"]]

private def r38_1 : List (Chunk 38) := [
  w 38 54 0 600016 600456 100 9108 ["O(jm]xzk^VdK0v{hE&!tb[R4!dYq^rYh%jlK/`~(z+-_LxSAlPn!yl;5(=cC6BKo","@?&GZn%wB47gG}yo5B:B'-9.7Sb&qiA*`@l9t#0Ixs~&skg@>Zy0>_4*+qUB#!||","&V(zX4fK=-,[<ZX'fj;X`g&`&Kawq$QF?jL=G:Iz~X#6T?Z"],
  w 38 54 100 600457 600902 87 7502 ["6zeEK+f0O`{%uf7U}h9)'5~ORkIPA}HFk.-wN!EpCTNO^$~<B[Xtt[/{|YvDn?%7","Pwi0>=8?b3#!5B|.|806%%=NDLGT#BJ/[O%!R2SCJO_Wd6}OCY:*$tLfGo/qCEe{","-P]4a&VuD0be]HG#Q*UoZjn<R&]jBTJcReO7~Mj2N/"],
  w 38 53 0 610015 610452 100 8886 ["V+Su`X{{;+V*<Q7hN_-WD[k[QDmP?)yjc*7$th_i+~?|TX*aQ!zAoj>m@~l8D(#o","qCI-L]e}DZtyQ!{,t_Z~X7B/Xcd/+0h]fp?%ODo~epgu9^DTz66N5o?*mlY8E#^?","/m@JFC|yY=L-`z.s;a~}SGcgDs/?lmvs?{]|z:pBK-p[r7tBO64;|5B$e9yuD{Es","%mqYr4YbYMT;f/<"],
  w 38 53 100 610453 610901 87 7250 ["cJ?mx9y[lMg/DxQWyX_9/9F@<s{ENJiQ=)rW`JbR2C2p/Bl0rzbPWHe+woWA7`i#","mFPw[5r='y8JP%msxB$h3)Tc(ZDxNL5pdxB'j~:[2G??Wo1>I'bAzbs>V]NkF-W6","wuIduJmsF1k$+Bd#|^ie$cZpn4pl`'#?5m7QED^jnJrb(Fq_~g~]9?mp`KH{;oBe","#L7mkYO{3"]]

private def r38_2 : List (Chunk 38) := [
  w 38 52 0 620014 620401 100 8648 ["aCvV2f0ZO:#vLF4/_oaWXM$nj'?Ge0L<$)'+~c&:4.xR4nM^,h}le1]&KPymN.g{","pn[4N-z/!9OI$yGQ?)b>cFi~gJ&~$K:5mzMTPz!q2<<AZpI~?uof8(?Spwpauan$","%-SQ`!2b@@.vk>!~.aY(^JSl2RNAU7~U2iQ#x)PX[]-iW7{EF?3oXX.93ieO[c!|","D2jT-%4JRv2^Tj_kg|9C!bN_W^wS#4:FIk.gW]g.km+Q"],
  w 38 52 100 620448 620901 88 7144 ["pl17uJf_]41OZ*nNu;fDUzA4Rx<)F:Uf8cK@U-}q.*KF0@S!*l13i5B*3V/R0G::","qF6;_BNxsv7>Fy|DETusNa0LJ'6n&[vt}74/o(k^$?<*|QGpw|*.rvyBgRhACQ8V","UoutV6YNopg8jhVP^tXp$hfVC?KvGxS(Q&(vo}O}9!|_vG`X^{Fr{.%[>#@@j]JW","E[*,5E_(i:MG8A=,.FvJ(%U8Jb}oTCX2-%g^"],
  w 38 51 0 630013 630397 100 8490 ["c!m&i[+y7?=C1(=sQ1ZFo!(.^GV6Z82IrEr&lZ>CU}6{nG'.Qy}]<T7m/DZr8H4R","doQk/?|Y/'/9j,_twjV<URkPqI9x=C<Lv^k1?.kg?D=u,${BU)/i}FnWJ>m/+SV+","!3c3>h2{EYwHOd_'_h>Ct(UZ6upcg$U~|83uhz(s0]*1'j9VNQMTlKm>d.iW]!FT","!8^noiZv[</.|Ga&ChOGs5/'sNR|An%M5RuM:#dr$C+*q3fi.-axR'nv3P/%]sW9","(7zSzp"],
  w 38 51 100 630398 630900 87 6820 ["o{;F?ussZey^Th6Q/Oq</4*/YAhpv59JFRtiJi'+.5NhNpOA$+ha,L5-lS(z%z}5","lL=hXd$GJxfT1rH-u^B}S>l/u[<{2p`z`=bic`']{:Du&Yu/_fe:Wqww1]%$q).h","`mrL3_aT17f@JZ*&<lgDtj6VB7`$fsl&_'xn;(/w=p/`X+9[h3q>[Gxn4UXexgVy","H5'18S0}vCOUl8v!5@~cz[f)pJcwWx0_xx|+b??^S)8F--}0KBC_|GL&%d7s>Wwi","+"]]

private def r38_3 : List (Chunk 38) := [
  w 38 50 0 640012 640393 100 8356 ["lh#-:*/j}fr[Xj'_di1Zm;EXu&ai^)4~l~mC'RrR.b3dsBHd,RO8A_jz1FXqq-l>","rChuVdk@NE_Cm/r:<-n^T`c?KMWcHlgShFn3/_FnHp^7I1&26zyRC4!703>4VhQk","uP|esQiR|,)e&6N2kvk*P4='G,Kr+_'_.kiJ`nsW&f9dG$<p&UnaPTcGf|:]oG.l","(W9!Mz1T+AXlY-{$N(tP.%o3u%m#d<US9jpAwh;mE;MJ_'`q'U_FMN1*ADtgT7M/","1o;z>XMTFvt&?FQJ[dx^`N}7Y4Lj"],
  w 38 50 100 640394 640900 87 6598 ["K|z]j~6czMc8lEjjP~sn'Mn.rI7B;VQ.>~L~!kps.?Grch^bm.:~}6x^atQ&pO?X","'m>A`:F5KH$>6MJGK~PF?YNpuC4!GI70f6tH4{(e1<j&ej:Rl?0`,@#lQ@z:nB1Q","K,xV^<22V6}B|)hyj1oGF%Mosa91RBM*Z*n{~io%t67d$kE})(WBroR7[|Ig{Jgf","wns}1E$|Ro<2,1J|`ueU=*}AsuhD<zjlhe'L?!41;M%P:Hy&|ta.mOAOCB0,O~_/","1DZ+BS9*EK:&Y2=+2Rnnh|!j?,'"],
  w 38 49 0 650011 650390 100 8215 ["0BGP}xl-pGvGm4;iR=S?h:7n>i`Q#=~VC)]r$9n-FSs2H}y[#>aA'T9jv3|!FFW_","F?_y?vfO{ls?m|7cWI9.T&xz/QUx(KP&SUVnAnvj0C+px^ox/,`'wO@BQ(+bnvfF","0+G(:Qv_KK'ZeFmXb)Z%8Etv#W7L/x+yH1Nb;YB*t%k,FE52RxIyM[AMxtk3)ahi","GI^2wo`jsr;axsCz)O.Q3go=@TcX`U=#2o^-|}dnYCPo{8rSIDz[Kvm>hH?f[QjM","$b|KYL52l%!SXyH}]fkRb,cHT;N[/9HH_l}G;MoR<MKrBy>P1EKY<"],
  w 38 49 100 650391 650899 85 6247 ["4K:/+USg[MO0f[fc>/^'JmI_9B[.L,YM3A`5-LeT|TLKp;_.[gHMGiyabki&sfk,","WDrltW]U@T1UDOzKG>NF^8l@<0ijs%?d>d-jF|I$Af#;ZDm:hMKx~kR`C:*iW`Ul","MNDF!3#C;]!V&6_l92`V>Y;j/VOu-jef>O=Somq%Q[('/XIQ)4RHx;A}nJ8q#YU}","o6L@5}8@~8f2Nf[hA`$u2.)e$mGD}pp%5$*sEl-O*^6RSdv{/eHhp4cd|LP#0Ik}","lvAQ;b,5RJ0u+o0+85GqdZMQWzQhvis:>neTjM+r5Mkt?"]]

private def r38_4 : List (Chunk 38) := [
  w 38 48 0 660010 660387 100 8087 ["jQMz4#OynNqR>Tep#!.9ZumB.LY6JA?IlB#.rWB/6.tuFnZ$&Ch^ezWJ;XK,ClcZ","ybI>>1x$N}iC#Kk~!wg^e0HKd[3&i4KD$c0_=E;1l-Xvh{w@V9GXGA#FieuDv$WQ","Q]x=UfZ|`!}%2mz8pi-wTNwkf!~&7nYoy,=Qk[R`ze]<:^r:[9<.ItAQ|Ji4/]gP","a%V`=CSCYaG!&m?jbUpK]H/ri8@4(<LDOjCB|55@8k#<iI-IorW0?*2g_Oaa'Kjj","q/8wI;-t-,(<p-j,<z;Ft{TG6AzJ}JlOyG%t'y-,?(EDc)DxVssRbNvH4_)hXk%#","$##iblAl6P<"],
  w 38 48 100 660388 660899 84 5999 ["g=z+JEr}U*-A|K4t%wWve`hfV9_?G<O]rQWvzS,d$d_av|:=q'}S;[zScwN7pAC(","j1q%3klod4}>ieZj42i{~0NmgHATCs.>=AR(j02n+Hz^,gO-z&Z7'yplIge+&pGW","|r`}++>Fx:-Gg[SK5ALJ99z37+l>x'j+paukUuG%IidqO;7bSQGy1Vx`,22dg8}F","15d#jc7E8_#}KKI+ah;[h<?$mD_cybXV4>lN`VV:*/G*:yAmmV#qDuz4{'f=Ie3E","()!5U2'W`Xgi4=Y>NN0A/T]eJ,jkZ|N'b0nhfJ!Z1h&z)=QCh<1?tmB,`6R"],
  w 38 47 0 670009 670385 100 7925 ["n/t#5_FnPX$(qUx<=Y>k?ffkI]wj2mC8$?6Xn~FVQu-C`$9LwT/xy{&RgO[bJI>*","&NRr(J=0}8{uA3%kQ<<q%C^xA{2dTbfFv[J&IPU?h?_f}=fM*|1*I[mOht6#<'=/","{q8NuWlT#%5GPI9Y7dCH4JOR*8hG~w%5D=L6{S7}JNRZ<g7g|I(K5gj[%AJO=DMx","Fd[/cVAS'ED>)(WnFm%KAUc_Iq|_SNc!mI_OQf<u9~Y3hr:ex19[gTQ:^6q52esl","8LURQE*5#mx){[jNX(($,[!TSJAygzJCDL%}zQG)WnQ)9[0r%T}R@v@>Fd%C+FOj","O|8*!!E?'9z(N%BkcnFZ#9YxX'{N06B:K#7S5<s;-G"],
  w 38 47 100 670386 670898 81 5636 ["Si)IcW8H$W,#v/L[+Q#x9$5S[H;fppCM#=+5I@GH%g.qckaEBHhkzK#wHRs06p`y","&x2ph>_UT[DgHaMrc/H7Oi*hcu8Eqb}qHgJtFQyLecJB6m)j6Y<jA#[O&F-6&)fV","ptumxc;E3EY*gm])KU3,/uLdu3N]QcosJ@wSjcsLdLKY5blNkT~Ryx!U>:&5dVF>","Kp4l*@t0;vR)K2Tl1X#Tpsd0XC8n65@V0Lu+c0GVf:sx3YPH;7,#a9`Qgc(QGH$H","[8^`Z4yx&wHjrnJ|eh{@N(5(}f;,(iay:U;p;j#P{r7,=7S(fo&b3Q9#y1RgG?e)","$@"]]

private def r38_5 : List (Chunk 38) := [
  w 38 46 0 680008 680335 100 7763 ["B3BBZg2]nWEX!UDP5iaUDBd-PyzG1leyi5<9vk,Lr0kWxgVT}O1q<4KdolMdMDN{","4Z&[Kukop5)AdwcU~}4F#~edeEV4=s4Y,G8IaM2`!2Dt'q>1bWt['F,M:>Tu99.j","=RHb;4{hyE9W~E/]l)8:>ScGU&R5Qf}~/xY5{^1A^,AW;Ec$F~r8E|.tPu.+`/B`","=t$i,z,,]uT|Y$aN@:HGdGlKcRJ'NtgvTQ#/xih!Tgl,Auv-Me]4GBYB}350n>4u","jxzJ^6>9:~N&CPJ';%pBC'J>351-=QVgJN%T[C5e58`ggv0Jj3N7t3.[:6EJlV@8","#<$TcLbL(l&huNsP0@r8i?n#k=Ptc1?km-Ll)fGd6v<Ja^L#%A.KWwVhJU`b|h?B"],
  w 38 46 100 680384 680898 79 5371 ["_4!_j;KGS+Q|4}%]EJ*>o3d%P=uU72Lb_k#TIoKrz!d&MA|Z=/hcoZ&HM]X>y`w4","B(U$x'_q>1=BNcvNR.i?S5&@skm5WL/cL^DbZhqCcLnYg2Znu}o+!X(C@>LCr:pd","2?#3-f|9zf<uSlq9KFp/0o:``M|8e7,fML@eLthzn'%yiX?Y~(XPipUo.lyp'BE;","''+5a!/snidmu,h%_2>|In&-^_$E$<LmdxXJU$l'thzb.PFQ=pt/oe5zJ7!|]5jC","ST}B0k>.3!%KwpE&ndGVMN~.`Y{yZ^Ev(2zc-y.dbUEs]TlQGPeTNW]J8OFyE6>X","="],
  w 38 45 0 690007 690334 100 7607 ["2g(6D*3^#i^Ot5C^FPG@7syU(9g/q8&4/jAiej%Y.IJX3W@Ns/9;:j%Z`;bDLc~w","r&cW^[@5@/q>WNQ|71nG<4'wi|Y)h@`jXR*/nR.$g2iL%qtu::hexS88+?@x#,c$","N6|;^y0f00PB,vKfih}E0%ElJ(Dd_]%#,?U>?KA+-c'!!6~`~76Ra]j?R+Mf~j8!","S%D#!|t(Vft35U+`n,PLvfo)1LSijF}5kP>J)kRs{Bia]eI?*j|F}aCE<VF]##U9","<Q7@W%!U[2dRT?q-Vkm|[&1gP%'cW]$)E)k5+Z/]r4F`Vkl^?P{+}w_w@>/:{in#","#<$ViN]/GScRTNMp!K]&8d)do%.<m4<Sy0rBk;BQ1tr:mR7.&p3:spz9m(!~kKZB"],
  w 38 45 100 690335 690897 75 4951 [".E-TGP^&ceyjCe2MH+Yu>pW<pdakh!RvqF=1[!($0JkkP/~%V[jl5FTJaE-gNwl)","a.Cy/e^Na_q@JHBWTdGBX,*g)LUDaD}h'*^L-.+A$q!}r--cnRUMN+eoy?U~:*~>","K@`!ZZ51zG[vgbI*@i@$gD7>gsA>q:1AFayWSH-:C4PQ}46g8TZH@Omi::7#n7=a","R/>Zg0hoc!gSyI:bNf:z>JL)C_vF>2!?4eRUs@b2VgG7~m!S)izK`)F8)%L+2Uk,","$PW@Q+Iz;!vSct&w|bV,HYxVWg1|hzM(i`W7kOvxvyg_]x4IbEp)F{H1Efc_i9"]]

private def r38_6 : List (Chunk 38) := [
  w 38 44 0 700006 700332 100 7459 ["P_FgVtw2H'uMb:~'x8h12-d@/J70y4(CRR1^+3JsN2zV^OzUZP}wuXzG%Z~f&#16","LwdBatD6XPHGsGvW49vvk3!N?3E((_'5z5%%/it?8KqXP,tp_>pWV>!d8sLqH%Vl","J~{2Pt0]5Z|uD&-~W]?dMp%]A5U~NE._Xf=3*N*MsSz(aP9d!z5dW?vC8)(T@2~B","jQuW/Z9F8gBJygq)B?BZ/`8%2]ud-mGvmPnXvfoKWB]*U4qs>$]r5ApF-JaXSdc8","]f4gL$|S|,xW35oZ=g{n`9/2vmV3^bHEj[4M5lSab#,uh6#.4L(9e=(pvA.l+hIF","YI.T(s'p)96B@U6.H]:8+*'47er8uM}J,Fnw5e7KQrC4<cW_~tSLF%?8!ZG,pL*@","$"],
  w 38 44 100 700333 700897 72 4618 ["{IXM>Hg3*S?vPUK'&3t$XI^{=Pj?O2&j&FxNFMPz|nWXx^Dz[oRcNd$rULRojPzB","E2Vp2vv{8O/w>~fN8OKw|ANSL/E+|C3c|joG5ol@Q|<Lqj'ux#FN1-}3WJF];oLA","GoTt*QymBy<NjOF[[]h)7<wP!&!qMo.!yH6C/Bx]49X3vY&<+K17p~s<q`0.lXxq","GFh}]gQU4;0?u3#v)~#?4u)r[fIyVZn~25zJ4*dRN-+/&.NW,>1Ixf5A[v6!)Y,'","#Wj+*/*jZ!yuKgFmlc@vs.d9D.s9|6ek=j1Cw3vF8]OVVG}I}/>jk=!o[#AM"],
  w 38 43 0 710005 710332 100 7274 ["sqhfV*eI8K1R*-LDMi@(`>e5U<rDRSf]*=85bB}}d)3}(l3y*QMsEQ~IA'F*]U$B","Z(2ruxb?VsV2|**>75jE_{{(dnT.NXj?Z#`[N0Q~$(X6bEyS~x;*3Az2:]IF$[lC","g-pD?gcQD5Qf(TZW,Y=s{eASPB'ntLU]oXZW0M0Ywke!c.&3lB#Nm]jSJnW8d%c!","UBv9__OLD.T'~W~S1wPyN|5&8=]+@-+N~!Odb^430{f]jcX.gaUKj,rZq~p>8(Xs","|A#tTP&*2RnjgR$PZo%AtiJJB3fwmJEG8dUQ^nQXgiFgdaA^@1D2lH>WlE{58a>U","}><GFvjlmHQZZo9#R#_`LG>7/%[b~c8G%IiL',zQ>-m-k^J}$7Z9PPo;-NSvKNH=","+xgbCaR`j"],
  w 38 43 100 710333 710896 67 4175 ["W|0)F&B-2HzH_&ityp{&_l#J$>D.P/C!`AGQ*j[7y.B,J^{Sm9yy_Y*~=^:T0Vc~","wvnAdW1W;Xs%x1)x=9UI_;R7ZDbXf|jA$EmF=8)6hlKlRg!pbN~<ACJ2o+%>ZWje","BBeDU2W[/nJAe!t/*5.b;AE%Xq7D]$a]FI[GmJ''NAU2:99K}%SUuI:Wn7::>+{>","4:Z6_b3d3HhUz.BO5,y5K%B0?L[chQ@fhw2(:_V9/Gcf0V_5e;8){=?~:z)vu=qJ","HwR&$b)5f#,t]c6q_aD=p;<&$#5)pP]bOmp(41h$Lbo"]]

private def r38_7 : List (Chunk 38) := [
  w 38 42 0 720004 720331 100 7098 ["0=#a:R|7K3I$zJp.{J8v9+}`rNhg)5-2G'3iLeG+2_#Z;B='c*?%~=n)PUyz%Vh_","|yS[K3J?||ZsXB.D<D.|[X#RK,n0TRyx97M[5p&'=.c>ksmhH|l+w1g9{:?rZ+gU","S_:,v<Lh`qY[?rna7r>nS8AC4.GGzKz]v4&t!IjZ;Nk2>PCNnky/*yr4^F?ETr]8","2O<&o[i1Sn:nnU-JZiKjZka7~>nH}8FM@g(a@!fo!U{(^,aJHs?byqGM'Ij=v7!s","]w+~Tj)'qL,B<nEK]6T{KVu#>_h*[;')6Rq~wtPF^-mz|DQ;d~F+?u`_LD^Q~xTu","jr:IMX%wbQ0IAi>F`))_kL{kqI;BJKHEzJfA?JvD~_L$+TMT:.i`GB&U?lRM>w;W","#+gp#Y`?~8#"],
  w 38 42 100 720332 720896 63 3817 ["i_RO0x)SXTHv#POJ('~Dtg6R!KPhW;|i4}*sK[}HIZ;eXwLK3BlTQAAoI2KsM(mo","h]2x2zew+fC33Q/Nx;z`q(N}F6A[B8g+?`Vt]0XX,KiwF`(-Y5tNU)]k4-,JO>%@","}o'0fPy?aCf2<W?]XwBvpDz#AM~qx.*7O1wfYA[2trvMuMRQ(X0w_6w^..`]Ap7/","Q_=lKAp{cu}6y'l^yIE&-9pOu4]i4'zG!{{|s=e%e5a{Euj~=:-Yh++4?{:wrlzJ",".t1sv0T6crt}6cbx!=_lg]>_jR"],
  w 38 41 0 730003 730332 100 6880 ["z[Q/</Hr8Iej_6fCRhKn5Kj$O_|FRXama(wMoh29|r],9f%JpJd2v1Q??65(!YNk","T?5WSyT^)F{Aqe:cEz(EDmnw|so]aVRYVF,^(c3Z&C?ev,<H1JO7j%Bj>*J^W[l|",".V?B,T[iPUv63+~?+'9PX77A/EMpnzf|^w2/IKco8~9}v%D1bk/KN;=ur]L@^Y.D","nZ=!P?{H.4'3o6|Xr+,czt&<^CbXK=W%ny2n#77#H_fzl#XgAYPnR:b/kKlw*S|8",")Bp0TbnG,^@fAp6Z]jZcjc/7HL5}_.Y$-&1%[!()7'}GSI.D?@`48UP518[-U$s4","lZ,SM}8/=E<AdrQG%z#O~LuWM{x{:N26]Rl27l_kf+zV;~*9XTvkyg!M4;sM3e,9","q`IO_xY-mq9&dO="],
  w 38 41 100 730333 730833 57 3359 ["T-ZV(f-Dm:R_pU'I[eawXz$G4}#vZtm'K+uXxpPbIJ39O6ClUMlL}4I|y^7=U{q^","9o{5J|.C{'V$Ng3-Z:*:kIX;{#M4<D_B.hdJJh-jPnOO}Ka+?0;(vP!fze@)*ql2","NQie8,6W[<Oj%PM<x}<>vjB}q6kUJ_&vCN&k|dOF9BhhiAHkT-xkB<&>3K?sBw~O","@ePbD3KYgcO5YoBq2z=StbyULk!#/304f8@g>9>%g_]q#LX48EBM?k)RZU,6/&XY","'(Zib0$"]]

private def r38_8 : List (Chunk 38) := [
  w 38 40 0 740002 740332 100 6675 ["'&Z&O~%3r1})n](TUMgi%UT.;M7sOd%=znbY>VIbh-#Tc%Jfp3/&q)e!CcnP{]@B","(?=TTf^8U(,|BGdV1IA~R5?](yUaJ<z&v+_(t5$Uzc,z:es5BU=0]LDMfy6c%@O`","I6Gv__:lt>(`P']5dD]!WG&[KF-Y2K:YRr.I,H_)srBXMHSd$=0'~hW5G1Mdo#%m","4=Ut/KBbM`kBi8N9+GckQ^8Bg;Zq8.~>1/rbp,9ua&Fk5-Uf$S4+/cQqeC6x6FrH","9.ot8o=<.6G^iUKv49PX&4uAgY0FAsQ^zL;[SR;krFD}>CAf,5j20M+R(1TIeBU-","ki_K|Q,>%b/>_kHNfjfW3`q#1GQt@wQ;sqkiMKrwY~hoi)}<-#&W(C|C&k(@?9hi","#!{2`Ii+?sjrAc1{J6ZN3fQ):Pw"],
  w 38 40 100 740384 740832 52 2982 ["VZdBTBqR4u0fW`{/T&c0@`2e4?UAB#dez{jU&0&u!{&q~}~_l1JdLyK(k=]ge./A","WLK~'9M:>8&d!nO#^EDof'Q%vvY}R'B?T>6U4pLhXZ1U)vfi9KdsqLvT1>=N$+ch","]E4l{9@/)FYMf{49ofI_0}}d}jIqO`y[s.BFr_Y9,0WElgB^@q7K3bGC_!B:2V=F","(@RN^UJIN8w&@uZaPA?gj@=zwGb].(28/A4d./@DYbe$OhNV`"],
  w 38 39 0 750001 750385 100 6438 ["<|hM9WcUVK<E^KQ|is8k!yhenMrrFp-k_CiK]+,@P04.PCx=+f85y=zqmL9cRg-w","kHc}l/r)fLzr]1'xggmY^gO$GO1{imdb6'9Md7`VDlx6`*E;*1GyS4*SsBW%ca9j","h9I`/>&/`@$kkiu0&</5Dip)kPl{a/=aB4.]tqALXDOF$XSNZdBg%=CBCys#X5o9","*O|AAEQ;I?k9o[up/9Di#,0N9]xp>3J#E$9.X{azQK*4$BR@&tt2L:yuhEJ!='=6","z8#t*`JXA6:802tyfh/ep40>4nh`jG-!f$HG}=w[{sM#}r08JK|iCYIY.TXZWKp&","hJTO`{pxMM$B]gU<YI%4b%FZY(_xWlg3pEd9ej(YR[:m=d[,C>[kbxm8]'XbJ>!l","%DnBxDFVN7AlDw7>v8[Ccz/w*$xtI#d_;'P"],
  w 38 39 100 750386 750832 46 2563 [",e}jLWa'qyr0~7^CQEWOM2@)BC0>i+|oo&{GF%ZQHj[{Q2gPjqz;N@N6Am$o?R$F",")*EX!SH_?}T,8#Nm_]&,S$@SGOvC#gw8$vrG^+=t4R@8}*C(05N'|xG%v`vGJno0","<cm$gBkccdOkn:]?7[$zVL@FzD.BOGj~fd5rsAF3ZTzUtlA,5gyjb+%^yYNoE#.H","-N[YIQ@PhI-aHo[jOH|_N~03"]]

private def r38_9 : List (Chunk 38) := [
  w 38 38 0 760000 760387 100 6199 ["MF[sX&/Z^!|6A~eMounc^M2spa_dVcI0aHZ^O5m:/a7F+j<#Tfb)n'F/MyDl$;16","k!cGfTl7daP=;c5{5>>A#OR#sC<!Yi;<N'^m!waj>Zn!IazoD;gb1t,SG,2k,0Qz","MGqO8tPZ#9xEyYwQ$vJXc9hh4Yub6L(t}Antt[zjxi:$9<|DQtO_f1B{Q&PQw8QQ","%wIGH;N]d-WCjZ^4YAOGu>{AvZ!j<Zgc/ASAAb(t.r2D1&+4Qq5;,d-YE0*Ub]i[","cmG~~r.J{Q$#JgtKwD{{RZX_CR1{@WkfV;lROEU'y@F}g`CG-mnz(RDaXSp!|z*.","_pE{5aLAP%&6Q2;=RF^FCeG2>*gWODX''EH<uW($PvsG!wXU:o|}p@ZAbQvbRqaP","4=?tS))dpG[kqrfP^)U;!foXvmR8*|gUB}?tQ*r0,-v}j(S"],
  w 38 38 100 760388 760769 40 2175 ["*snR&tLJ/q}xKk#)qmh_%N'r(M1YI|((>HBBTc3eE(a8tKj>BV{!E`iT22dNHQJo","q[Xl'[{-=p|<z+NY>xpm]pFV}$Px7-e,eBxF+Jc5<>Tnf}^2[EVm,`u@;&34x{C}","%(B?55DGI1RB'a-wYPO]l%m=W5T7Q1YDqbSb_x|dKCNn^05|jXS.3>r]4S"],
  w 38 37 0 770000 770390 100 5915 ["%V=>L[dfb/^1l'e7FPHhA2IB+ALfF#i^&fK=<,@Gfa>4K]fT/#HmLa!ST~a!UAa;","GR<;;@(m[{5Zq`*STL+kTR9^h5,kPWeJ$Yv`@lt8<>Lq8zWLWWwwz(57vaMW']&u","L13k|7BLclGmsF{<6glCA$27d:tlH?&%S3[!KC}{o[XVIUAu^eE96A]'.H7}Lr;w","wo-@l@Zf50t,K4_E8?c5&=4i(j4PE,a7K2{BPlN}x9JUah)8%HJ1sAnr](]bVk)H","qk!84j)SD7itcdVDnn7=N':YynKTPM-!3vwcglvm|^O],e^,C:3R$6{xc|;GZ7I.","Fc5w6SAD<G263an.opcq1n6~5{,xdo'-<R?KV)L:CopB_pZ/?;_]gYB6pHJXPYX'","19SgVJGf~q7u~8|}eYh(@S0OK`*}eqK_cu68e0?:Y@pz=Lzp[N_vWviH`89HBMHX","#&-l[eF"],
  w 38 37 100 770391 770768 33 1763 [";6A}we^{Yz#^y=]3N!gDhWSF'm/&VXRM-hN6:86;k*4CRR/op88MwWwiMc&nV<9B","Cz]Iw8w2UQ5<c,XaB)E'dHwTHBf6S!{>'w3&g~8-529e[~]U5z-$i)k{]<p!dZ5N",":yl!=!S`z17:Qsa!H`}_M4VbT~%"]]

private def r38_10 : List (Chunk 38) := [
  w 38 36 0 780000 780393 100 5651 ["KbY??H,SQZaP$#mrPw<mII'*{Ai6!/;t_ufM[05gM7we;!e`I4k>eq)B9EosKRwC","]k?lhH'ii*wRQr)X[M38J%(&Xo9w|P<waD0Bjeswoe|IO9Kx#JdW@JOJ>no@3o$A","VKxvdJ0JYbfJ:N9(?B;b}e!3IKz'N:#4b[P69#_tcH?K`T3i#2U~4GH3O3<TicnN","<=i)_g7R3Ef,Q:RHP$FfRhdklG-4u7'-#SH*/V<]%kBcwU0b34wX_y/u>fYX^Q*<","otJXkbV}{T0s1P8{|_k/'S5&:;mFp1>lFBr9'xC[ed9*I0v7oPZ|P}@4_q|D(q2d","AU[B{0=<ozYM~zq],MvVkP__fl$eFYc{3D,*3FQZbk']7.=Vg'a?]4h~(jh]_sj?",",R_Mdnl0$h'>G&VN~g0kIQJP21~VJL!MIWV=zMdVuJw,)Fj#UZ,H0nVJm&2/6zhN","%#5:sg$-U%.cc"],
  w 38 36 100 780448 780768 27 1419 ["|W2I!8=+>z;T9Y]vP/jl?$B.9[fy+m^m~yZ$7^E=<!=N=kX.fL$-$?w#m0C4<&l*","#jP.R|;]Ua_wSJWnpRlZSX=Sn;JcN9coV+?(nFEBg3|&yC>XW,k5GkaG*KW,*.Je"],
  w 38 35 0 790000 790451 100 5406 ["HDMUlCLI6!.y=^+WkIuZ8w1zWw)'QmArGed,_d~ur}nl}rg=7K[Rt6_i[!}]Kvdh","TCp|lJL+3|(+'OmUtlE:+?hA^e`Z^.#8BIp#u:xFfp0Cx4f*-^9L}Dy>;|;?TJk]","yTI;JV5sVBW&k2-@m{YXcSgppKnqX##|WeENeW4t<5r6y#:#wN/=V]R3gCAXhWni","d*DcLp'x$'mg5.R_lh:FV)28_Qw}*v,K;=!N[xHg|$,vZhY84VtV6h2}PcqALL]r","eg)k9:c@4|O2BxBz,+={>k<E!*2(e(fTi8F+*lfnEq.m__cVT:%W?T5d.Aw-B)xS","D%0Js`?2d87v=Cf`z%%Xz*4UAY)4l)]%VW:MB$5y0M)8_aBoNHvhBu_KG$mA,E!m","lAPK#|0Ou&B.XP}8IO.=;qE.t`|{g05kv(oJ($H6y{{CD<vncMmEf=D8r`>_QbB^","#{:LS0N,e-{PM!`I.!)9]fZFuX!g[_D65_q"],
  w 38 35 100 790452 790705 20 1033 ["4*QQZ,I3o|B0~v+gvZkL`?er,3$,{Bb'$n+vaKi+$*T4s_m`%?!Pe<B@Wyu5Pdpk","&{s.okH*-HjvVm2'TA,C_eSfnNQh7"]]

private def r38_11 : List (Chunk 38) := [
  w 38 34 0 800000 800454 100 5179 ["i>tso:tuk~}i5{IIe+Pt!UUxL~yh}DJuIMKy3C1*u#HAa]F&DXt'iUtP#fIg==3'","GO}3'/#|$R6**0PVGGpW)b8d9oqcNy3}R_cKDc~OYqbUGf;%Ku?Q8r=|(Fdp.=<m","f{t_=U$$<5|{Z)J5i8$OIW/;B6OLjGZJy'VD!+..Az&veSj_Do?KV<;,ZnvYH1k/","T+r%Y;iDkDFjPR;'tF-:?cDS(~~z`bH<:'{-L65J}~cM''=]B+9|X}v&9H)A`_j1","D]:f&nWGgd,L5=E]LZXPN5&$7c~;,Bs][a[*?KEjqblwro-!/ehn-Njeo#&dFxPg","ZyiwZkhk6A/h;_k@#J~358X]xO_-A`bLUvp?>PeW[Fo^V&P5l][{xj7N0QH>Bv@P","?a]T3dQ~uf|jsU67EHWf!#aU/UXJxB^B09smDtcn>$x{OJa_|O^1-UK~/*>w'qS'","z0EkT1hHR)h5O1$EVY2)1:s?M_Fi/Uj3=2/4<fRF0krQXinr/"],
  w 38 34 100 800512 800704 14 713 ["+ihk-?<]Gv_BB=;fj.q4Yb+3sjg3CH1/|!#/Oj~XsUAS_|]zpnH>OD7`Yt%T!(&U"],
  w 38 33 0 810000 810515 100 4975 ["S3k<cPZQ:b'ZGcn[@v=Fm1m;c%g<lw5p6lAc$u`r<I_]M|UC!|-=GhKDjl=!_mKW","{.&aLAS~>{NX#;Kxkb=uoyUk1(an5L;(It(Cgv$kI@k1|+Ml^4v_(d_}A_p>9bo@","1=.?^'^ao['J=8z,!Fh'j4AAv}oKm91mODX=S$M2Z5MVYg-vmf_V`??4GK9yM^jg","X+xS-54~j%j:Lp]}p%AK]oF+UkyUC67Bh9{N#?~'qlWFUDpGsZTy_V+%dE1h+ePV","8*~:!|jtPE8{haNr{Hcr7ZB]^ZmN[fNxk%PI9q_^|}'}?gedMXEna|^1qk$Ies!O","H5(B+Wh!=W@SMB&Wb2UyKtep'COh0VM7#Hv)?zY!Sdt0e0GDZpR+D4j&A>AQP#ND","NHJ??k09SJ58c`U,bIvjMn]Z.Pk7^.Sh}m@Rc3{R%q_kNd0cC<ZLeJ@9?|C5nq$f","'$1_A6fqkDX^cdDr,B/aIo6knh*Z5jRN=o]98LGE{Nwzl:&Czo-;_WdKqIU"],
  w 38 33 100 810516 810704 8 403 ["&XGGp:S^xjc{`|&eD|,q.@klK*QgRf7gkA;:"]]

private def r38_12 : List (Chunk 38) := [
  w 38 32 0 820000 820578 100 4787 ["'A_<`D/O[.>H}*4-s*c~%=I4ee^-MJI/cr2>'F42E~9<D7eDJ&P4=G%+Ab#.td|h","=OxdZ7!d#7m#L1v1YR)y,JEj@lLCoSrXa?oIbaR(.{WLb`14_!pz=StRq~(_j'ff",";XLh)kJgKG,F,'n?}>B~hA&08=B,/[kjS%z<r4aA3mhdK|9hCnKWDE3-A3bn%$&E",">cd%A3Sr>&at];]tfwG/.A(D=7*@3-Bm4bynxEI`h>{Ln1f~{f7s(So.#w_-hefn","aE:D-Ifxbp}N|Y#.=Unq{@/g,}QGpLq02R1~xw1_c83j'@$#M|{pbMhqBi:MvlG|","]`BIy2HQQhO/|Wh[hU!lCmjb|vxFWV,x:0]w<f]huMk@_n/qQVbxj.RhfRujBfj%","HtK5riAR2j*54pt*d.D4Z8x*l@xGLw2pt2ljx&Be%}H`)FrN$+EeV]Y?I?eQaY:z","zB2r]<@`AcB!EVPG=NvjvmBWRT(ticfi1p-S$]CA|9#4b11|:HpWT$U&XUK-MqHR","'y$9%c"],
  w 38 32 100 820640 820641 2 100 ["#i2GG<Je"],
  w 38 31 0 830000 830640 96 4430 ["tLeCU-#F#0B[dET5L;UjueGXg!0ddp>^SP7Al'rFpCP*K[o.c?)tb35yE3Bq9%'x","i`C'wdna&9i8e~aaxX#~3~iuXpu'[HQMwZ6`ekx%<j73ALG])}X::hu_hKSF@]HH","9(^rw`E3Nlb{dwT300je@!OP+X>sb:.q3GR8J(u%5P),l8Ys=@,?5Mp!/,Yfz-M7","v2Y-Z#f7lB:ua&piI@674qu@#r{%0wzk]&I~_Z6c%g8oo:,1QD#`ORyKDeN^!VR#",">~6cO^5<ib#H<I97X)S,l6dYo^3h*0keNJ{JXsELE*'g]sC~N,kd13%p-idn@,!A","!t{0enZw#WP;CPL7mlsmBLBjl/ju|ui=$>8'>6w{3{&v-[~GvgB`'%y^F+3DH/jC","3TU/QW@1}6-zRUBh}~gt]w/N#h8=I'JDnf;p|7Zi!mCa@)XD.!96Hu8wk>q:s])5","H>6[`e`0Zq-|M(ds*k5{!sl`uwnCHWzOzM@+!R87&WoFM~yhDQb3B8[?04d8z88"],
  w 38 30 0 840000 840640 91 4043 ["8Q@RMDD%<jIvnqH6iY@QIZ,K2T<vr`b{}2N2Alp.5+Wz>6kRw|Y|+bTEUdW&e`{C","%UN(Vnngf2S&1Z#qAJ|W7%q({I_*4'E={k)nxSVX1BUKaxF2/nbwi?l8t;V&EpRF","m3lOx=Kn|a>1)mdXv*'PvT5f$clRU8&v#oaO,,D;WjTlMD;?Y.:MU}(CO(<WkmLd","n|1bEd`AHqw|Vh#4z986BRQxptRS3TA_Fa`63u!<6s&?&})wT.#mJK9jQy>~i_m[","ELI$p4jyWDMi6sXiiIc0cC!hx%1ss|~&6[/L~EaiMLLo<a^5ka#O4~gWS6&e++.4","dxE9MTW00`tfdlw)l=d<xbn8LTNHf~)TFe>KP}OR|eYW}ib/D{_|Cav&Q5ixgRT0","W-PTxptVt)B3J/Fwm*x4m?=+tLq~/*~:3cbV0D#<+U]meK1_?VM0M9^<rC7TR4*G","<LH%W[5-5i:10{n[t3?Bpn%^+%O_nvq!nf_8_c8k"]]

private def r38_13 : List (Chunk 38) := [
  w 38 29 0 850000 850577 85 3635 ["6rKoL$d4VIto36ALC$7FGL5uA*U^(cjx<m?/s3qDl=qitYZnl:r?j5-C$o6;ks}[",";1i&>A:#Y3<W3w!#6|NY6ZH$i_F7tTAbOe#sAAD(aYtH@/.K5p0ZY^r!.5vGN]Nf","IX1/lY*>QLw5GX9J~ih%gX1Zerh)B>F2>|w7Jof_Ym8Eoh+t3Hwl{=l1`%Qx=y/c","<N5+M*U&=|6y8^!.1ESu+z5?0Di=u%&vM086ZG)r*NBVTYF&i$NsQNM6PaHL~9v)","t@'~-[]WaXdhR(Y}Ju8eac$5-6V8k9x([8QmH&_;'Ju1h,U;qoamvb0SdU=;CD.R","U;$@'+d_cN43}p4L~xIzxa>9wdxdbxnYAxKYjOHD6lw+t[#g>(@rCE-U7Q1{(|pB","bpt`BxkC_R#C(+5[Sm<MXb_3n,M0@2&F4ud`k3bsM!234Z6JE-k~M^S@VDM{P25v",";'T4T|H=E3_`h"],
  w 38 28 0 860000 860576 80 3296 ["/5J2lP$CSCV$Q1mk-/6j<:B<ZYm24f!C6T*NIfj`I:paL=/pPtxF/r+%KMfwg)3(","Tk^Gm$PpIPEHaOr,N.73YQU<zH?W-OS8?(&XV_m?Cbvj/S91E;*Ju[nalT.JF~9L","&lI4f;1}9[P:PY6X(C(HYQoC%l:IZEEGlNJY=~.dbXdwk7ge$[,c7s+hg4=M!Fkw","]28(ys5HD1ApRF>%|0/n,3]q_Ik8I9H~%)^x~:Ujzb2AA{X]=*eoTA1+nIp9.Q5z","iOAaU7k?_K%&-!).5xWtf-[WAb!{!b$)d!?<6y36V*YBd+DHU%dFLj&0L,<qH#n9","d=BFCWpO6J)l02F@s%$`{zirVP*j#dOG|hf(E/yyxYA81uMMsE[&dx+RM<Cuk+tX","5VKR+>,j*M><5x2z)V!]KUlf6,CBU3gt}4AVNO2@S2(;//*>p.+sN[mMj;b'=BX.","/"],
  w 38 27 0 870000 870576 75 2980 ["y^X2p2~mIHgvZgMHBtJnco2L=tSO|Nd&_;QcHm>&2^DWQg[nk(8<U,5=5AVYU,&e","kyU]3j{fTv8w'$37-wf&dRwG}K]@-#r`2W;!RO1G)KmQ'^Nf:o8.mRLU<Iud0z[j","#5ExUlpp*RlJf5anEc&:fg+?`~#_:(UsC,'4p;H`So0_j.h6'bt/SjeW[ys>-x:0","k2,D$WCz@p/k4mQ23W7k2qjES>kRg'u(jH,^-8OJFOr_}'-b8t+S4hAl5g0jUo50","%?xN*:2(|'wk1Y-V1E$dTM;K{y-nCF:3CLZ4|KroxI!9%{!~1WzM#V4VDI(6otDi","]L9ALG.+nJ[W?_=I'`qW)#U/?HalW^[Rhx1U{]dzp^guV(TPa'oq[Lp1SY?^1cI[","$#16uk&;Y<oeXxu)r/@awP'^0Iy5vzxbeHp"],
  w 38 26 0 880000 880513 70 2675 ["dk8`2?c,YZl|Og]6j>b+#_ql~@tThqLo8/9*A_Eg66ny2!VjrSE@27QE;ZItjOoT","QVQ#y6WLR6bRu]B#:0$;A{4M^C]YU%%y%t@,fCR#8BS3Le}'Gu@^1eP^1KJml3(t","03X0tr~+u?Sy^Vs?@KKbV#o5x1dX4vNYgB?GJpGg}NR**IYI+Q}nYw={fkDj|T^H","&.|uBO7JY/yS&K3Hu1!*xu`e1y|m'Sx<a11Yv6dTSHXBu&f&ms*$fiX[GChJ2`iK","Y'+*gI,0t:}|LG6!q#d(0M.KNX)EJR|(k$k,zUY9IMW!v!blgri!vNcEO/uGghvJ","v{*@]Tjv$;7]Ct}f-Fz}}4'Zo7M'|;uW$BA5t38hK!DlSVl<>K!}+*%&2H(KW^LR","%'ntlPs9B.#!"]]

private def r38_14 : List (Chunk 38) := [
  w 38 25 0 890000 890512 65 2394 ["IM+KyPzDSx&d<![z[h=r'9R%afE#_8$pAy7%Sd[z6/G+sh{qt2h)mC,y~yilNRB4","%C1n{iKcZ+K->Yd.%{d7[O/0IxH|,Tbq}Ijxv4_f3uN0a'qh)Qgn_1/l,LO@{r<j","c&1.`,w|2#r/.W[=dM4g-3gTq$w-:;CG+!qG/!3SvvuO}NTdshjy{jTc(kfUZUD7","SXNdr?Lb?k)n1_S+i^k9S_PBaU!zix5DYw_z$a1Oi]{XL>q-C'laO)xK{/T}Nh[I","2crW/+Co=4LPK6@TNE7gQ[v<ul4]L,y,VfM[,Dp,K_O%.1rZnt|jFDR_ii1xcY24","AltGB45+K*|hV@Nvo'uI,QrsP,y8;A/moY]/T?Z]McYk98lhO6|9gMEn"],
  w 38 24 0 900000 900512 61 2163 ["HK'/f:aAk6UsX5*Gkwu$_V4p>!eKvCDKG::uJRSM2gmm-I`t@~TeF*0k%eSWm:P,","H?Ii)UW#k}w9@)=M$Z<}OofbAT;DOdG-KiApJA`zb]d9tW{_B7ln=4TQ]2W=ty0m","r]v2RTjrM`q5H]TWgk8@5r8uPn=#JWDW1em51fCuPWL}!A{8z7]t4z9/Gcc]l.mq","5=y]?sF/O(s+n|[.v,c}_6K8<vVfxRq8VF*?3):7`-Ea6x;feqt-6$klzN:/%^Ow","?Uwle0`?oqP}UscuLw`6(s<%]l^zQ~#R/ikLHrXjGE?~JvT2(xOT1XNOqwIVU$hU",")&^zT]zp&#9p_{wGKN<|UCXNoqc8'3#'f4GQ)"],
  w 38 23 0 910000 910449 56 1909 [";v@P:`C,~!oa)2]MAqy]eILk;4?LxvcS4lEy:|y5BC7*_nNIGfVR'S%xczhhKjqw","[QgGC[}4$K!M;x7}w<C0U%nYkJh]Et^]_=uy/|}ug>k%E}l4C4P7Ou?r2iMnJ&NV","]+/FdN(dB^Q6xT:k)NG}w*^LN6s$MA|>FWpGo`HD+YW,f#(Z5nv[r3_gioi9)L%W","G/L,Iq6Ax#t>F=;x]oY|DCdN,RZ}5PX,P:n_HKuN)b$xa&/Z-u/'@TVn,eWW}go&","P1/@a%!$]jQ+fc0p0iSdk@W{V1sJE_2,g.JQQ[:rb}@7MFf=fTzSKTJXWmWxo+ON","*$&(P=afXwS3Iz/m"],
  w 38 22 0 920000 920448 52 1705 ["d7{bm)9>8[_gSZnZ/rI5$br@;BP*F:;NcPa#G:dKt,]SE~I?nH_+7yNFf]Ub3z,f","pL/ed<1r<j&UVz5&slHD9KuH@NRK6'BP<tbc26AebYzRGZ*B}S1Og01m}m7M2|GN","3U'^;D<kfMtL^7Eho&pj})OC7/>zIC-d[/[ptJAr]~4ud4Ye`D`PkTJU}BjFKGPs","`!|RR}hsZ':jl%fQM;6PVzGj!{A9%M~TtgYP}p*4fF=1^M6%_nDDD].sb$fp2_$3","`2#]k[r6N:D+A.yGLt8Osf4:o?CNMi4vgc_6Ra%DD/J*BH4VS@]!zZ,f]enL((d2","%-tu.oZ"]]

private def r38_15 : List (Chunk 38) := [
  w 38 21 0 930000 930448 48 1515 ["H-|<WD&}tM4l-Ojo;Ad,4X[8jR6]=$`2${xTQEJe'w51+*66C~u!/E{7{)~6GN={","i&V*;d+8>^#}#XF(y;fj>=*`SXe(5`C:gIGn[vvRz_U2EAQOvsw9FaJ;!*u'XtW7",",=0m%%vX|9oIFbP[.K:T8wElV{fPr{![&2+eW@Q[av(Ge'%7}CrCZ]B8D0:64(gN",".9SoM={[MZx8.ph=k`,gk%W8jB8pjd1</WbC0ygn-|-u_OH7!d_'UlZ|pL1@=8P,","%YSi;2E-/9PlRr4VqF]bUXU&N>Rcqb+>[o^%RHo.)T{>%ytTQ_m[k"],
  w 38 20 0 940000 940385 44 1331 ["Rg{A;)<#S'aOLbun'R<rYSM-6wdlI/4PlN8e#h,cnB^[37v*+m/hK*$)'^S4NSVo","U!:%UW!$H=]BGI|5L{yjz'N(N0(AQsSV|(1R`z8c^g||lzsih)lsHm0oMyYETb:K","E-#}5[jwGq><C)3]Eq=1[Wg5zZ%%7T&r-@BP6]5`#I(5prJ]e*@;E2wj,_<QT'f,","%UueTAXpBa#y(c#mO1$E`~P$bD3*,04Wc}5?P=D>#C5VN;cEZMxCQgXYR4]D%ji<","n8GFDto<JGlHKsQyYpZhu'(CWg/;"],
  w 38 19 0 950000 950384 40 1163 ["2s=>=v|S2&_Q_Ojk6>}qZ[w$B_r#jKKrXa}q{Gz,b%J_,|_K^![Ij`|%tiEyc8%;","vBDz(+gRv+Uu5,e1`%?D=4JtmDHkytvRg~!iTF#]h0I@24y*LotA1%!vhdpYgr|/",",`bDIWc+|:u=ls~:[[4,h%P#cTO49?P0:!qxd^SZgs`tb{03ptzdQ!>[@KWMQ3ev","l;O)pTBX<1u[:W9jtw55+m0Q(e,VO~3tTRttIt6K0nZ7bh4V;-tsvA0%8sbw;4Xd","chA`G;$h^mdI1"],
  w 38 18 0 960000 960384 37 1033 ["S;Ee@{yHc5{-#+QciLtWf&dy8%$)=+p:}v98M(YSNKs<_XcA>AA<YEh_wN|6D3^k","`GTxkyBn~Wtg;i{J.jIGs;w.#H>#]1AE(GUAf9^%Y;qRF)f:BaP*5muN#[(/e$Z,","[Ja=9Epj!eD98jb7eSka!kE7K71C^us%rrdJ~?2}[e3y^jM=q?a.yCI=n?&gkMI%","$c,l9H4&E@#z4JnO1wOoT,d0[<@bj4@I|gaCPR|'2&x.r^TR/:KM"]]

private def r38_16 : List (Chunk 38) := [
  w 38 17 0 970000 970321 33 882 ["L'gpcN=}z>QJ[Lz8n5gPU#;@z'>qxNHH'PGY_C|9lUpyL6G`!U^f<eg~XtTgc,E{","bwi^RNHoHr3^}ek/LiV,IMbK8ram:z6H!X<ZCd>2rZTg9J$+C3L{bQdg)d?%[CuW","LqWD7dRxs$~vf3F0E/Lq,3:<5MDP/UW0<5IpbjzRLf,En0AvApKkDwpEjJt,ydyy","&D,mrEwJ)wPc6u9jJTGz;*W(0Fh3oyw`v"],
  w 38 16 0 980000 980320 30 768 [")!0`3wPaqDP>A]eSK8FY}r>9<U>wiaPTh.zSvv*]R})3}mTV@[D[N8v<e+US&rhl","ojAfU7)t%,19^zIrXF&FTn=[vS@UjHn[6m}C]O[3hq;C4F9A.x)Y'+#`b)[HKWAw","/q&=XG_y8N>bKt!!~`iF6nO+c2X',2BEEC0IXA7:{v>'Uj3Rh'Yq&_3d_m*k,{s5","2X{u*V!.F8fn"],
  w 38 15 0 990000 990320 27 663 ["GKkQ7&tgRX5yGFnS!>k^-Xp+n_KbC*L,1<0Miy0u_0=-m_4T(/c&c^{FXKA?P]@>","t1hOACrc5yS3wHyv.j:X^RZwiiRUA46/3ojpoO&+#WR!g@uLj|Nsb_vF91zY#XKL","q6`L03wl4q66|jsNKVe++[Aw6>jacJLJc;<=$(@+)I!ah67aF>DK(}"],
  w 38 14 0 1000000 1000257 24 561 ["`<eU4Q5}}*|D'uGICC$NNtE1?w)[q)WG52a54fIK_X(5ohnQGPd,<rs.%^&^{%VG","AdN,/u!Y^g)0Bu3/`HWPcfWN(Y1I},dk%eN^IrX>_Ao%&g<y'_IQ;_/_^`4.FA#b",":y'AfSqq)|7{zuWCA`HTfRSc1O.~=IvbS"]]

private def r38_17 : List (Chunk 38) := [
  w 38 13 0 1010000 1010256 21 468 ["!{]?j&%6j;wM0ui5fOVSMErQJqp(J]*[`];</4c617Nh9kGmz/Ni]Z3hwd&yY%Ud","<z;j)Ke}wOWj+,9l:Udv7?&jZqiS~RodCgnyI^wwJ<&iabsw~QFc(-0D%R+RD*Sx","$aqG+^_nwJZF/]/A]I"],
  w 38 12 0 1020000 1020256 19 403 ["@+n,bF5b&YP)Q27XAcK~aLt|`Pb&K7rY9rl]B^Zit#BZc2.RCV%P|?SM;fSp$K/k","N|F&)4eYoMcR%$/6`uKFk*b!qU]>VNbxoWlrX[-G[8V^TP[aO0y'DR03/KL"],
  w 38 11 0 1030000 1030193 16 321 ["O_|:.Kl&m=F:URsWCQvX8+>jT8CS<5(L=kzH?h'HV'vECAP(6jqG':&+,kty1.]O","$Ss>MVP%$#Xzz4PZr*;Y.m*&:%BHJ:pnOA|maryuAx!?=%"],
  w 38 10 0 1040000 1040192 14 265 ["=<s*kR/>QsKGgE[lRyal<A<O~dNL,5C!J6+vvVv&Vm9SE]OGB7<e$wq<BI-tB!=s","4*@|?+g<xstlj;=yfsV!@jN;OEzI7"]]

private def r38_18 : List (Chunk 38) := [
  w 38 9 0 1050000 1050192 12 215 ["AStiLx8#Ah$X31p2Q&@e1l_MUtVOM?-Jg&X9gzpI[*jy'C2E*;e]C@dVKGa2[(tk","$F@Pp~cL]83AT*=h"],
  w 38 8 0 1060000 1060129 10 167 [",mD|{8)K8jF4NZVKTz*rE_)BX7)>e!q-{/GTJJ6711gCkVt:eC$ULkVh_e>=u]N6"],
  w 38 7 0 1070000 1070128 8 125 ["2s^gLv0tb.`}ae~?A^LLDN/5tExiqC[yK_l1emSCSye+op'#S'%0FTp"],
  w 38 6 0 1080000 1080128 7 102 ["'2J!3}=<[ufM#1:7;4#HX4NW,.4n5`s_;)ovs[T;/j"]]

private def r38_19 : List (Chunk 38) := [
  w 38 5 0 1090000 1090065 5 67 ["#X8x*f-W4%P!;3<)J?dc1M<:%V;a~VBep"],
  w 38 4 0 1100000 1100064 4 49 ["&{jd9e^e@tmOo'0!aB_9^>CJ"],
  w 38 3 0 1110000 1110064 3 34 ["*f]HVLekZ#BSY*`MB6"],
  w 38 2 0 1120000 1120001 2 20 ["/.!8;N]2Rf"]]

private def r38_20 : List (Chunk 38) := [
  w 38 1 0 1130000 1130000 1 9 ["<f$X|J"],
  w 38 0 0 1140000 1140000 1 8 [":^z0"]]
private def chunks38:List (Chunk 38):=r38_0 ++ r38_1 ++ r38_2 ++ r38_3 ++ r38_4 ++ r38_5 ++ r38_6 ++ r38_7 ++ r38_8 ++ r38_9 ++ r38_10 ++ r38_11 ++ r38_12 ++ r38_13 ++ r38_14 ++ r38_15 ++ r38_16 ++ r38_17 ++ r38_18 ++ r38_19 ++ r38_20
def rows38:=rowsFrom chunks38

theorem good38 : ∀ r ∈ rows38,good 38 r=true:=rowsFrom_good chunks38

theorem sorted38 : rows38.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks38 0 (by decide +kernel)).1

theorem mass38 (i : Fin 57) :
    bandCount 38 (i.val:ℤ) 56 14≤(rows38.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks38).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 38 (j:ℤ) 56 14≤mass j chunks38))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total38 : (rows38.map (price 38)).sum = 329408 :=
  (total_eq chunks38).trans (by decide +kernel)



private def r39_0 : List (Chunk 39) := [
  w 39 56 0 610017 610457 100 10248 [],
  w 39 56 100 610458 610903 93 8743 [],
  w 39 55 0 620016 620453 100 9646 ["ULoc:-j!2h88Cqu.xK<ilKz*]E78VT(>1Vz+?u(LJ_6ti.0VKu|i5Qr0=gG1^a&Z","toYg<KKhTos3x'%*_y.TOvyhKP1ts1!1$4(sDNxF_O8SEj)b_m/'7K%3rJl=WO.%","%PIv=H^L9=C:,aAY6!D|@9~85JV+GPn"],
  w 39 55 100 620454 620902 94 8400 ["0fgc_<A58T?8%U,&J`Jo=sFz3</$z:E&9HNTI%!)xSj*B^!Kyr+n;k[Ji)jQRdE7","`v6Gd_+$-F`kc4<,9TrwD<v;z&3sKoFM/CDE@{tdUXO]=b~Wf=H1&[iQ/k3(3{mN","9{-B:[>:z!2uD*IV:6#x#g<u7U;o-"]]

private def r39_1 : List (Chunk 39) := [
  w 39 54 0 630015 630402 100 9216 ["T_580KQ/j*c%4bFKcC;o^i~).7Q/@`ER_B4{9ISY)w!pGc,K!-Ogy8q@btBT;HKN","_YY8o]dQ%8X+/>S!.&g`ViC8PFXmYH4d#YZsurAej!ea3hg|r&R#zJ}v(A0WsZk6",".D}cQ'1a(#Z6L0D1])3&f:e@d-$'aAo22..u;Eu0vGt%+s`-"],
  w 39 54 100 630449 630902 95 8195 ["DBtg-gb,!Yg4Cr3Er,AjkYNBk+UffnW9+]1:'[8F6|wri5GaS`($C5+*c4;{WM4B","<b48X#PERc>v7#|T8J=a20bea;p,V:(Xvb,.q80aXG;^rRoz#u:vaHbi=uU63^v%","#/;|<Y(YTR[YE6jAbfQtCoxPu`&Kr4'P,2ALNQ7VpCX=L.AR`-,wdv!v"],
  w 39 53 0 640014 640398 100 9002 ["AAwdsS5WP7iSF@@T]~q#%g5lD}#,G6V|+OP*l)$:G??a$'cpmj$kDm!~=o7*+Drg","r+|)M~D7RBSaN}wKg*BM#Uf8LZ~Qx7di;WA'~E*0E@tL21Jgk-[jzrJ!ak,)+_Nh","W!o!G2^:+61p}CSDbri,!!q,-z',KIdh#}Fc%Kaih'fdb|*n5Ewi^-.&elXV,]WT","-Sh7n*@8Jv|"],
  w 39 53 100 640399 640901 95 7902 ["#'[FcyihL^YMy{*>;M9yc(tz+:4G#zcsH/|S6%R{.j(?@[g)B&18y*(-4k7m=$S@","hb4KEo)yNp=H/,u&@Qx!'yCCz|%jhj:R)Sj`v;G%.sn+Vn5RaP9r-qV%jZ@3h4pL","duuu|O}+3)u{aP[?TK360cEMH`UMs<2('<i9QL<orTO8`by.6{:%cZY<^>_7:s3]","%-]9A/#0*]}:1AJ)XJ<t.rU#8d"]]

private def r39_2 : List (Chunk 39) := [
  w 39 52 0 650013 650394 100 8812 ["*ZZ%[L&&@Lobq'ZL473,>`r}AmzU)6n+*rS+$o}'cM)6h{P.]a*}s~Vsm{[PW?y2","j))5{,4fJ2.`:tl2(qW7IQ0rA<+[ep<n@_udK/_?Pk2>0%p~yJB[O2?%}qWr9zUA","9WnyN}ib<<K`1e<o/$gT6e;<G35:DT#aBDUKP5F^c|p=&zeQC>V|.h6_aH.3_y?{","(s;}uS.z'X@2ittzcTSc;7*Ym9n{<ZTsg^md~"],
  w 39 52 100 650395 650901 95 7603 [")dQNZo@,AQ0i=%_+ZbA(k,/=P0Oc9m@[GI?~zN^@&-!w(9p5ACm]#w]QL&0*!)mS","@>iuWA^Z(YpK5u-(EHDJyh8*DkB@DWthXPvm**4B}q_<hLU,5,fVBu[7L.>l~GV7","<`_P8_v%65l#vgR|u+[U0V$G*@t>?hlM;)xs_u{e|)},-!}38}`7}W|Cz]P`M[xU","ls8>,y%vy?cnV4@|Q_ij5lYV_n+l^F3z%9Rp;G7PwRUrv(5^rO>B|rR"],
  w 39 51 0 660012 660390 100 8641 ["%S02|I-7CMH4xok/.d'5#Q=dqjE5a}|0_%CXd<ne_6(&>|L|jACZhAF}fdS=]l?.","<BV<VLw1qyT5#Xd7'>~eOlGP:.Z!R-}vA]W{e3}$Tn,ptU7g;.s3Z1f99S*K?r2c","i/nk3d?53dik0*-3V)Ao(mUs;]qnyF&$}vv2s7DD]XWPNT0a-zkCG`eQ1!Gq}?RS",")_h_vTySlDLVKNF<Pge6euu{zj7ZKo'S48y),jYOXN{ixj4f~#6KLj-qlaCJuw8@"],
  w 39 51 100 660391 660900 94 7263 ["FI4bqWf8[;We{+qodv%s9d7sy:#qz>Zv4z8H5;hqI6(B]xfP3A0WnaKDF(1Dx#KO","LO-P,_OsR!>zd9q3cTQ471Uf2jz[%,B7x^P&Dh9&M+b}IGm8Tn<X,PWqymay_PKo","7%BBrQr.By#$;vh7C|;tkI%=-Kc?|m8=#kFk&zwwl?>Ce!CG%=dPuIab(3M'$~kW","Ro$`M#~,|VT?%yck2QD)NL%V~=}>}WPO~h<^ld&k'~3U^n90'XW%/c1m,nLt8lsf","$R!P:_]cR=CV$Z|@C)"]]

private def r39_3 : List (Chunk 39) := [
  w 39 50 0 670011 670387 100 8449 ["T?aKJ5D+?/iOqN)3Vh:u6C$`y70CpQN`.7h'S2aBgm|HkL}%}O/l=48D_P)4Os@!","gKZ=5]F%!zf!LIl30T>vm`ukH>@Ou_ile.So3jZn+=qDm=0FsxO=sH`K8Du0;+.G","$KBJOjS<$xOWute'S6!DB12E[)kOnE(=VU;EFy0c|PUH_#L4MzeinZt}I2yxumd%","q)]g#_JOkeQf.#Hy`*bnNR|R~=#]A,%'i$9@u8ACZ~@g`iuK_NR/sC6Tk2Ldf#]A","&G/~iiUnKb#Ta~LWv@JQcGRe.de"],
  w 39 50 100 670388 670900 93 6958 ["3!<<U`)U6mE2MyX+62v|6#TgZ7uTVOv#oG>squH{Jc>I#|,7+/y7Bl'_pV@H'qKi","0(c'x,zb(x|wn/k*&-=0jEU4>5rPG1EsBU2-FJ-+NfxRDN4G5g>e1gD~ZhbY]b`'","aO|q-%h}VTM[?k194{EuyANOguAjc0uM*P+rI&Y:3qO(z&tp!N<1]tharTvr^5_4","qAl:E%kGehanwU@xL8<_C0$D~V;`c/7&gCkFhKt:xi|%pb/#/M1-OQJ}Z!SbRc_=","$47T(ajJ%rlPTWE|R52's,`WbQe}fc^*?fxyh:P."],
  w 39 49 0 680010 680384 100 8262 ["A3A*:N?3d`69ACAvSrBa4{d}|fl*#m!=0&kL!U'='*c[lY~dT{t18oNznk']9<m2","+uB$5pkr8T7SEk,^^/x>a%Qip`':bG?=HOs.P!62T8[OUL@U_sNJ46nZ%>=TVQ1h","FnRGardEXZ]z-Y,++{R:t5h{46[TdBn')wI_h-63yBp+K=(KT-qPS1-Hf}}m!QxX","JnS[S'v3kU2lp3G%Qc2M&z6i,E<Rl#3vSA-:ZQ'{XuP|E%IQdF4_]EB^^jlNTE%J","OB8EM?6ahR{k-4<#>kb;o){wo-7^O`U3pg#7`<u>E}gsC8"],
  w 39 49 100 680385 680899 91 6629 ["d@~!NO>=Q0iQ_t?<(ae!T$3WVTbOIUV'JCRI4h[Z)__d!?>0%{`W8?w[=+`oXQ#i","tlB5Q}*yOb(xDoQ$--750*L$]potX/]1=N&ov/zKl8u/+KTqknL!!<+<&-~URg~:","*_i#WF`94*m(__DG31gdK=El/Lph88t:}WYWY9dhYr1?~gb,yjYIP_#<^(qnWN,k","b?rg{Pk|_&Q$y2:.uZvdXBZBUjL'<_r%[Z+>/D+8Z`99]{^k-w/^gOd5Y,$ojq.;","$M^,AKR/cm7QB_#O0}lTZ%X:6v!vVJ4XKB_OB0dczk8rP7IDm_gcANF%O!97j}"]]

private def r39_4 : List (Chunk 39) := [
  w 39 48 0 690009 690335 100 8084 ["L2JJSSE~UTKf:%%O[BYeFc1fD#G`m|m95m99rf>?1#%Q9Sv$)j~hbm+q+YY]zU8R","k?;Ydv`(%Plipp3)~=jRY/&)JZx>O~rw%=*5gB6sf]zfnN,%-0AHsv;'RDJ0U<FM","{.xJH2nHU~B0$SlKO'gFH|%|OKL+;]N)Q*^/o0!/za|_Nlyw3K0K@uhe$I+qD7k'","}F68uws*Vq!o`)~sn+u(!Eo,Md^0(j>&fkhW`Sh@UBlb5tULmnjDNfenetN)GCC:","zeTA3'H.#P*eV[bzH:`qk,~fl&wQ&P|0=O&D/:l<u,4+:td-*v6-ytAX]A3a;RlZ",",2K/:[9t"],
  w 39 48 100 690336 690899 89 6299 ["S'pu`hYsQmIi*a}pQ6DSqupFvC0@g%f?4Zh/F*I1]2YUWta6Pndd:j>Re:}'1[s,","s~oNj0jq,a(UZ;/wV^Ebc0]O6$=@.$&4.Mi=FVYG}VRc?U5UW-sItb6sfy.>)og/","cIZV%TZIt;*N:((h>@mMS>DozY^su,:$Lk<K{1Yh]&wR~-3*fk*grahVoa6c6q)W","^13{/xD57)|D;9*FT<%`rBll7WNFl^aYRW^&j'00h]gK{h:Z(#J7xxU~%&zMx[sA","M1KB,oEfX/vC'!.A@E+f00h)wU6KIj.^R2a1~6>*7x&kg:Ya[4+^KTu2c{FAV!G:","pA{Nc5bR-"],
  w 39 47 0 700008 700333 100 7950 ["#hBqh!%Y-Hhw4$4XN&,>kw%^ipG3g(UN?3XP&>Kh&Xt;sx{7U,izl?U0#V$o51Lc","2uXP65,^-9-a5v5u!2jIU9w68e_8|1L>r[#RO`rcX)R>3bT|/JcjOA>lZd>?A(cP","I_2|_s|vr6Jij`s=g7L2b5_k4k*&5/%fbJ;UX.AqYHu.2i(8<#R<bqnAM3GXE];}","!7*>hWu(-A|:vTOOw@r<'a+e^o.`;x`V4ZN04(`p#vz%?=YA59@9Xu'7<[!+{Yt1","(#H`.r315oXP1j9O8^s+Thknl[XLs50+.t189~NF`_A>-^h'Hx[lYvr60+xH9r7J","$!lc%)q#RBQ(hiKxZL=b]_gvnjAP#D?3b"],
  w 39 47 100 700334 700898 86 5898 ["C`HC.h<L`sFqY0orh3q,PWaoa,G~6J!$.R2%&rZNSplZ*<cqg}ieI:Y4)rF:,6Sb","/6DI<!U/})lwr9F8&(*m2SMY'Iw.q*Li4C`wl$0.$E6Voee?`Q'4fCv(r)Jl8REu","(+gTdK:&tne=s|HJRRCN]Nj6}5N@:`]YD<SnljeQm6h+(6@Dk2x'R6~<m?rC$$=6","e`'jwG<0`=vc;`I2:h`Lz@Hz'IMv[G'<w<M0dCCD'i0f`acX=E}hUAjSX@(ETP#t","3C1xc@Z/Lt;K9z'U32I>Kj43Ol^u4wF;^6nGchxlzEMLY90;{HnP|I}Gf5rh=O`2","?c*-@M(-qNn2a-[u"]]

private def r39_5 : List (Chunk 39) := [
  w 39 46 0 710007 710331 100 7774 ["WV)'U-7EWra[uht#IL>oy#J3U,h^2^{/J}J&rK$Ch&)A&*z:B_9=DR-_l.V6TS]B","&xx$5'|cj0*-/|nZ3ta0`/9D.h4lD/U!7wgF@)(f8&Eh$lwIr>qJ2)Pzl?83yi;+","aZ_k`g.,FvM0*t_G%p'pbaC'L(5b;L/g$RkbI0|%0$w;/v}prJV1teUO<1}b^iOq","VGA]u1%IvRqy41f8PMh=,)[Gi%Z0>@]5#V=J1i.ies%n]UozH7PsTJE0.(3|E(#N","Uw'^7T.Y:0WBN>}k<?;zK?ta>(|:N2niX2C79Aj;rT-qC/a<H5OaHtGyfe$/Wz%j","`vS*@@?=&*?sKnv#892]G=fzCDJqi;</2|.R;gxx{)E}OAY2J>G0:%$KDM)`wo}W","#"],
  w 39 46 100 710332 710898 83 5525 ["'9E+cV*(]SWM>kO'8Ok#-Q5#T!a;1n,z;9&~Iz4bZ-z=M<7uKyi74NN?0Li5OR^I","zBoLoiE7k:Q4!`&VJC+S6'1tgIEK'r(w#|^gRXnR;*[v11ZIA+Uu!ymTG$?}u@S?","Y)2_Xwx&3Xi%ysuJ1h?nL|c?VQhQ/YSFx-`W;t+Z^KUI]%%T+@N@#!RK:&$Uy[S%","V-R7Ljw;G'ikIkv?pIW]-[1aRv%QN,pg&z($@8YPw,43D>+!x6eYuC7I1}eptILy","rl/(GZ-mq@~TI{f1_E}^y3hMH4y'^'d]E-.SqW#KLI$6#@P<jY`F&6cr%8$5tKNr","%b=)WE~zK^'0>zxagg"],
  w 39 45 0 720006 720330 100 7615 ["6&Q*.':jmwN/0<uXA8W_(K:{R&<uh}4m/n6i8;Li{XO]98S@Z>@sjfmb<2QwZJ!*","<'7R=1C;{=NaE*p9p<!4R!`L(Sy3d=A%:lBq&R8~|=AqJtOw1^_2lU7,K%aC.8s#","4G@3xbz4&NVXoOrYU;HM#p3*pVbPWp=71L,0'ROG=EwmDPr(?{vAxP5WxQZd`&ZR","Y1gL>e,R`BoT.{gXM,d,bU>ah|[#3W}rUq7ZH!1p1y42doqx58nji$C(]J]H;cg1","t_8[kU8Y&&K@wu#D+uP>9Fp(0X7&z(+|I;i>:dY.qPI(uac,]ou]>GkpndF'cpo3","6%G^~OXkws0,:n^H*%G2&DaC}':RJ|ZH^xBsF:O%k&Vu76Lri}8>wbW-X#x_}z&Z","*Ic^IFBu"],
  w 39 45 100 720331 720897 79 5105 ["^4uEB8tRCHndK|#x03h,+@(P#A_j{M3XN*A0M@biwdavM&CgAx0zFp#Zo~F[q8O2",",a&#^(eUG?C_y*jko>xD8k%gjbHy%A:XcA#E8YG@{[h*x5w*ia0>ma+Vd]]-Ho[a","LXRwpG?VP6H$?^YUxbc$9SLva[i^+@,[$Tzo2^be`{vJFEqAr0Md17>asfoP9$c;","d/*ukM}*2u*IbO&utWReq9?(way+x)RSe#6(~2lO^5IA-Z8;DGg.p@}FF.!G?9K5","4P:5s1g3,@$nl{TOyivA,JCrELFS{XF:[98wG,y6Pkh;LW+g]p.$9>4o-S'es;=x","%}v']7-)I$ZG"]]

private def r39_6 : List (Chunk 39) := [
  w 39 44 0 730005 730329 100 7411 ["gSGBV@=[3UD0340(j_K;PXVa~<s]Lv_a0=^}D#1C+C}36GK^Jo;kMj6bic0Isqb&","e1e%pH!=Nma2p.:cEWVj:4)'kvkk-D|>.'zxjI1}Ppam8.}vg590h-Pr=SRlr$hO","#KvtK%D1i9uD2k#&z`>D_IFuI[[.pF4}Z<jZiWY9wQ*_091`-p`-#_i=&Ob1~~O@","f*<O^E)9+7=Z<@^ZG<>;ZXD:GK2(^K2rmM,!OW/tH=eq2IR7sr+yAEq04OD1Dbw4",")00<P/a@6J8]VPbjPvN>_fJ6n&'o3+kah9r56tA_HC+&P#V0=wfePXgRg,pP4awJ","G|#JLZXWD]CH@5$2t[=rfOi7elus`V7&Mc-,a.@z8%S}gE^yc]JIZwHm2l|wqg3$","'}<0:,SI"],
  w 39 44 100 730330 730897 75 4710 ["{#*M!YE49Wd#=aH<]$f,(Yg*y]^^HtL:E17BTs+8dgas2fsykU'bhqHjfF>JR|Hp","xJB2/1vwO:gTyjfsA',qA];;S0OOJ<)lRz`h?Pyxc$wgN@Obq:9sZ^%fCY,:l.|L",".'[uJ@Y`n[_0T|Uw%|`']2WQT*1($bF$*?[7X[(0~P0[*)'S,Mx&[/098Uj'/u3j","xY~<,B:DD7i^&$(BSBhXH@&FgV;ZnNAoR])'Tu~%/B)q-_D2lmDJI3%Av7t1hXQZ","60!WksBIcCZk(^k'%<@wx@AK6oPg;{T=o<@)V)Abb%lF9&AX)fxRckOURa;Od5QL","#Am?0'"],
  w 39 43 0 740004 740329 100 7225 ["$-9&,+/cHo7frb0K?:co&Npu<Jp2WvirKskmlPVq2APg&.AgJs%wG_k;'(e#KIl>","DX'(5n37XLaKsF$-_;L~+h4x??X?iE'8S/KvP|5.=M<v}ugGg0ns$k}J5yGOLh>H","g!#];zT/nV?h4b-MT``mR@pa>Fa)0R5W$tBSo_0<NKz<I:=o$L$A;L[bl4Me;_{Q",";2k&CxluaOw6Iq;j7tLX!705NDHK|2Rh4nCsinbpx=Rx3l9wU0Sw7TBuf`Zw5Y/_",">)zMI!|'/d,WkQb8fw;h>FsQ?/A;t[A;]EpGVw3kBhme)RA?_%W1rc7(q?O?1T:$","xIQpzCv7*}@O;<lA8Q[ZKnsc6$a*lB&weZ4UB0Um&@.7hfmRjTSV%v3|g9r<|Lp+","LT#/c#KfRw!+6u>"],
  w 39 43 100 740330 740896 70 4270 ["vdgOIt1Yw1N^328eI24<r7}<-R3NVtz%5oOfe6$xh4*p]Qzn>_~kk;A.&u.nzS'!","pjuxFv9e=;:+AwL.2yI8np/}yqV%S?Q@pHs893k,V{#gr0v&xVi3BfG]m6xl*n>W","|~R}5_UYC{IRJlyigRu;]2%h[@A(e+.C'PqqZAd@Pk<iVMr!+o.8<We=XX^OUE>2","By7}J;IL@A'aw-zY,~B9Xt(]B-=0*TARUp_wZ+z*Z$:'!mW#~Y&=Qd:g!=qKFVJ+","C'!um2J2-@4HTvKdB(>a(zZ;Jd+Lro$1#Nzq>j8w/W_EUTArnv_hz"]]

private def r39_7 : List (Chunk 39) := [
  w 39 42 0 750003 750329 100 6993 ["#nH78X(XL?67aPn!)lxWrb]!pjWYxF&jMv/Br-r=Nq{6H$5Q7^{S~h+zRN_&.~mc","QHmY:N5j*gI@{00i1o`DwQayo@pc6|k4)r+A~-h8E[a@m91lw69g^JNsJBnutxlc","{5Z/`n~i7p;;NUH-&qE{@MQg;53_Bh!s(_(Oe]=*jp352`~Uvye+!J0a/U;$_8ms","DoL5Z|X$XC-M+M6yhQf0NDQTk`Yz}ma]==/edfgH51BxH-cuq[FY<T2NY{,yd<t1","8}VQIBOOnN7)2j'$P[Zl^I#F#R[tM%FPfCTCNR}n&j<fwD(Ag*|p:@B<HFL191^<","(*5SG}nF#f1-krgV_(3QV:+CE~ap4|A*4<f:wc9i'.aL2%-16uT|0Ty$iRe<<*s+",".o~Pb<l7`6*Rsz)f*e`0(g!B9"],
  w 39 42 100 750330 750896 65 3854 ["?;RfL-0n@VT3NE=48vLNg|-;gC*@)jC[|>>=`!J`sd/3)_BDkkrq~V/.'nP(1bKR",";EPzlh[AArsY$g;tNUTs7IOfWE_@Uj7-a*2HZ>2LJrTYcjEQ$X6O(>G#?1^t*cFA","a[myl'UVYo8)ml8q5%jQ~%1c&bhr`AOe(k?:>U:F4hB#ZOXs,I?3n|ol?i+4LN1)","f:he9wC2chAaT#ALd1Dh!q.*}Y~V{vSHV>w(g^xhd+^rFH=M+<Xz~t~6Fxt::oA[","t~MzT.$|h6Z9-c>}Dm[MXd68(+},y-)k}L9.T~<I"],
  w 39 41 0 760002 760330 100 6775 ["mMh|PWj6li^nc.uPrt4r5eWr|tzK?:lzM=mA]WiK+T>8F/]N1}n-r]>KsBtBCD?_","0L)&v<8KtKpu'wU_ZIWO2N4![+M~znW!n>yc]x`vfAuI3{n8LIsMW6|:yHa]n]b=","nT!bvXADeP%O!vhEbV}'=4)gL#)Aqczr+VtY-Q(ti+]@QUa9@?|X(sG8=}-WfkT%","NMR%oMcv<o^~HddvFZj.8H+'//QasLIb$!1_]|hV@;[,+O4mXi'%NEX8$b*zI#PM","4`J*,WD?L5-#>_tfP+!jj`H&S}0GF7Zs!I{v9/1{%OsnLqu?5*0h^o?E5*>2(b0|","Qi3`O[{/IOa8p+d=Mw]cot=A<f8VnNC7Zo?cy#<YMLm[}w%S(xyGNt=;W]D<||MJ","$D#h`!n*38I:w;F}}TieeooE(?CC"],
  w 39 41 100 760331 760833 59 3402 ["sIAhx.#TixuYYH`[OMNo1mjo>{S0zt-/.Ob6O/w2]$4(gzeSg_n@VI_u~x?`&#d:","t:Fa8zpI:a}tWegcT:jdu.O-b-ESob/i12cnO)_?X_(j}c#UKd<:YUw+SFqvmE:k","<~>idMy413jKR.dC$zV3$W$zKrn0}u;X_6Y}Ct7U1r_Y>j@.c-gtF>F^QqaCK%z=","qCAQ.|^ec!J%b$ox`#51(5c|%`Pc<uxxK=g#EM2ZX9O3@WR9gWk(CbM;&ulD8<r6","&1VW4h#)[@t<dI=QP^F"]]

private def r39_8 : List (Chunk 39) := [
  w 39 40 0 770001 770331 100 6509 ["iKwvhT{9*a7K=(g}pH6CAQBWk7h8`7fWG5YE<)pH:mt!E8bsz@(p0/:'Xovw386Z","^sg:7)w8;B$=k[;}CZI,-6kH#CZHg8g_Zi4|PnXUdaf%Kzyj%Af%f0V*YOV},Yh;","?F2F{M5}$Tp0cd'*7ij5iJ#1eLL&foJT:z7@A23ugvlo^<F8GSsy1B$zZ-<KIi[<","r6,P=S-Po>[Yd@sp/tv'vR)O3+aGG,os`|R1MPbS<@|RS)HI7+YRw<XtY8L<2Lig","I5:-RWt=hOO`nFyl-[|?3aufrIYnITvWx-9+h3x-OUXr}}VQaRhYUn*:@3&g/8&g","XkzI|04>9Wt'Q%[],f@#T!>eO)mhjMp8DGK]'$U6D17M(ne%~bloJ,P)cmkZ&8re","$13'S%R.kwVr^1'q{]{mXk/MDx2wa?@q4=R&4de,>]q4"],
  w 39 40 100 770332 770832 53 2976 ["~VW%`bpSG={[5&R/L>CSE^mW*5/DtZ4_38D%:+Y_7$pHg:ABD8p6Y+UE%{n07aRF","{,X09+6q4U>[Ul|[%,!S8~x&){y9F>MCunJ$!1eyMjnh4;w5&ekB<L4[p$TN-?~5","|@=jl.gxG(s[!.%E6z.rcmk?yj?VsO,w;<7UD&O&*hrK~2j55G[-l@xXC~J[SuG1","^ql~f=drOd6B9#xJh%w;d{|wK'7{@'.!oDUYY_SSb0Vm.w0nsizsv<y`w5{S"],
  w 39 39 0 780000 780384 100 6267 ["pJiG0Yl2H-%O>~r]`TwqIY/->C5!Z2fcs!rT'.^l@R)B{tKx`R~PD/P4Vs*%OK6*","'i+-6Y:qgDpwu<a]QUDU&Mk3$ZH|XMm^I.P*F:`BMdsVYZZ#Qt/]9{b(Yy1UJ)gf","e*D-0/Di]zk>M)Ut^87,N69.w{)iQG@elI}K@5/S;nnPvRz<mN^BLXZL>IZ)rxDn","6L?{{Qgs(fn~hd<j0b3.Wr'Cd3c:E,L|%K[5w<(`Bo'te;m+t]%RRu[if<w;gGi@","BPigX|QMY1;r8Pc&=zf|new>kh>)`^i(5,+h_^aY40tx(YT`m)<`t{LGhQ;R250.","Vr'Qt>U._,ZTk.PLOYwh@!E!M,7;_H8NTT-*]ae@f1c.p:O[:(<nu}D{q-Hj?CxC","@~6[&3@iRO#h@-B.8ylmUWOIyF}qi3zT-Li`Vhg6^,H|;)?R"],
  w 39 39 100 780385 780832 47 2568 ["/(H7HS^qj:>%=~|;||nM1z<Mr.!nslG?6_po8'8?FsU(vFYc6>r(1ky<i8n)9]dt","IHwKa.*OK7jJrYyE~!Oj+cuHC).E>G=btw2WO:RS[{}9%NQ59j6&u-'{se(Wh8jZ","`B;GEVi8q3f[nWaXI]T|v:o+b0}h1'MT7YyZmGyHbCwdo}m6RqO[QpSy(E52Q,_/","0$$}fXM{f<{mMyT1*-BY4LEO%,yWx1OR3"]]

private def r39_9 : List (Chunk 39) := [
  w 39 38 0 790000 790387 100 5969 ["nKt-PdONbU1DS6Vs}+Xd53El9@EZ25C~xqM&o(m#YpY(or!~!dlNTdAqIO*N:7D+","pln;N-&vU0QAtLmj0HGHHqn>#/-:L%z<|]eK0X;)q1s]p0yB1'rA!A69]3Q3E3HM","fL*yjsQTBk|H]W:)PkWAKwR[V(6}C@r^8z`Yg,eGQG0L/L&31V0<&^~4-/p[GS-0","k|w[!$&(1+u=d67HFQoEu#tDX^[x0QN8KI!{Y.n7y89>->]4Q!~7<';.qo!y,2H;","8sPGEzvcm@;QHWUQ|+d[0c=uknL$A%5|jI{JUWGuttwvk2Kf9Qx3;f`;;o3@ABQh","xddr6jY;/dBNo}.Sl8.'.qKMq`U/:u82Q{(o8)x?lgO]^/|]9_J8ERsE8;dY+uOZ","9aa2Vbx:(cxc6V9,Ge;ivlC+i)):lojx-#_;#O_l/]:7.]YO9MGfqz4U[6vaq:RF",",!G&L=XSZ*"],
  w 39 38 100 790388 790769 40 2135 [".U4(x*.U4G]jX'$AZz(mE4LfqTHvu?;n8uqZ7TTJGBH]7P]nr]*>Er`-OAi(Y1w_","}5CU&WJ=SJK&lpHTd?ef#N6)hX9AP~s}QhVj^-T:OP?d5<q7k$)zsnnO_X^dVz5>","#~~d`hq=w=,0e_<x{?e98_[|#~S4~%93Rd$HMAyE)AmEJly+RCV_>X^&(OBQd^1"],
  w 39 37 0 800000 800390 100 5687 ["-%:-Kz[hkXgly?fry$dy/]WI8hhw[Z(+:*{XBY'g_MBW<iD)u2]<2A<Q?`%7gFVC","KjLyai3T)oJS_FAO2Tg@el_:k-n}ZD[SuRYu)E{*:YSwb::$z%Ws,[>R>-cqP[P9","Rgijn0pCgDk}C>jn6f&X^>k}WzQyCCb*vy2-B)Tq</+*khCfWeAuZ40&;([gtnd9",")pS!5GX.(>CEeXIAKx?'ZiFP<ym%^d*vW'L1mBq:PR0p,NBTO~)DNj/T9*!HLR73","4A#XQax5+d$.%*(sy=OD8/u$~mb:3ypDquWmcs.nr)>Xy/4e1}i@_P#lg8wcoOyN","46[O8Q4~_s/75m8Y36pAa?i*&wS~cZcdt/h;8p#P`u8$8Skal/E]#;$ZVl^%Q7ag","A#,d8;=@%iJzyCS2[LaN=d(8Kw^i-YP;i*Ms(Ai1U.|&[3v}JL/}nopc[osh&|DA","_+_&2tSbezpa{%dmO+p0|4>0^Cys"],
  w 39 37 100 800391 800768 33 1730 ["C'4q`8uO6+nSo,$aq>jIuoMNlUgVh_1c<PgPp4%Gz]~dx%R[$.$CK;[>B'&LL,pZ","MqY(Ii8)ACa<GN/O:SUu&=:<f)'.D`e*L9K5/X7_@^3:kgSK_N#X1eykJ+d.8!3j","hGQ.n/P6DTE276NS1ZN::5aZpt?D"]]

private def r39_10 : List (Chunk 39) := [
  w 39 36 0 810000 810393 100 5432 ["C6C8gX$rK|M6}n~_NX,2(UIt6uzGX8^Duj8f}T<ue?M/D^1'hbL`V&?!0n&MEtA?","Rn.`Hl9E*>V=bSh4&O#[z;>^6R0uZ+|!vgu$zGU>9F/`ho&doS_[<k1w}f4IkvTI","o]poJ1=I$msop:]lZ>vEegP9HZ@lKRh)foQom2fILj%xOga7,j{0V:jMuD=p7e[7","9U`?-=R2[Ns<m2)V23w*nkkmwIugbU/HxZHHlW]C&kg_BDsLme.##}ObmCBI8ZK-","oNAg0WiU^Iq#ss6S6YO1m;m)b$#Y''0:CYG)_(<5oe4nVP~}IT[;:pgubl5R|?R?","szX6Y|i:s&/mfV;Map>tcq,y!0C2sp3,<1i>|>L/P4V/d4n2/,9AEKFbz$nEgh%H","F[RF(4QL2x[(}0F*}m5R6G`hSZ*h8(}(LC1_'L62%zMq5TatJOUg-k]c2vz'wu}H","+%^`+{a=lRe#yslq'{RB'XClKF$Kyjd{m,Dn<a#1T"],
  w 39 36 100 810448 810768 27 1392 ["5P`aj8u-<;W%IteD}8N-$t?3j$9HS}@Sq~K>4{`dO1+K0:|P&.;XPE.$G[P|<8.v","y{Ds:I@zmCQ7Vxj%fkp?~*][Ll9I/{G&|wu|l8E+h~lg>bUrm!y#07^579'jwQ.h","&"],
  w 39 35 0 820000 820451 100 5200 ["B~IM>Ug`9L+CTNg4n(a[f3U;|j4:b^Q;Xu/XQ@[:=hLx{?D,UR8?A#nd?K-meH|W","#DIa~he17IA[zkTvP!+rOK?up1mbeX*-OLuZCshyry%#vv05~gB58*<WTb.;i~!O",">F>v9[&M/?+4u3j-YL6WG?/T:=0AWEAn#M,$doBKx1Nn5M)4bjZ5)olDya443Q?K",";vv#9f'0,FH*!hxP~2BAh0XQ87<rNq[F)Z?>:DHMmOl_{3o9>@6wcN,2g{X</o`V","09DHS9c4&Fn5@D@Ay}9z(J~DK=j9}B#Fqxp2;Yq2kw+I{G+k[c=K)TVv<~ZC%_6g","g3#<JCr1[MvH'~?K?4stR<cK^tgGl`YM+WhD>^[4-i@U^HkO(}Nt'[/S}6hLnogG","N:0#sIM>7jGNX5BuWriX~<I<]iVHa'1Um'yc`rZ7yklUBIJA,jb9i:#oQPcu`.9o","#(_k5a5Y06.z?:o1qc-i18VF^#FlRD9twR|[=Kb*WEL*/`=+Gg#x)-L3WUkWYI"],
  w 39 35 100 820452 820705 20 1013 ["Ac6N/#']2[Off9-g`rW((N&ZD]bC-%/,p2>d3]GR^94:@J4unkB4F&XRaDd@/nrS","/n<~d`O}Yjw*TyFbJ(Vp_|0Fe%ss]}"]]

private def r39_11 : List (Chunk 39) := [
  w 39 34 0 830000 830454 100 4983 ["`7.hK1_n{oZlg*7XgE@3Wa;zJRDL{}8=5s[UF)(;fo*~9!xSVH?ZI|{[bhwK>7l'","MMWK40[29|,w;CO6D_&r3cgqGpL`vv{N|#L{J*dv[b_lYyB7.=[FM=(g3)S;EB=n","f827.^+5&;v}1N'.b5`+~b/VcKVx6V,!ONtS2)82WOz-3I/R1e~[2B;5nMdxRsqL","A6S1|u/p`SF6d7Cb71e^R.!IO*4T?fYgu>3@5O;:tWEt)l=+TET;dUOsZA7'L?cH","yfqP0LS'i@o,qK{|JzB-.y{4Y/4N9{rC>!f-%or2s:w-1YknE|5e2;Kg[Dz`dTK>","8|y:w[Q&N]]?L)ni3@0z!g(N2'*j6zDNtWkSfGcSvi1k[z*.QUIdoQO#]jH}rmIs","OD5)dC^%3/pAz41.'S~3/,`#:7^%;UQGfjXr6{h_YM7>kx+{NhAZ5t9S]WFS-=nc","5l8P+NhAw+uSeo.X#]xKkWJcE_~PLS&torjGT%E!fuO>8cau]fF$:bwu+toZ2%:^","r>1haU0dPMht"],
  w 39 34 100 830512 830704 14 699 ["2u2bOP,SNjy#rvZWzhYizWWgj[g>}40r_%3UF@sc0ri3Q&czf}GTAe*hN{51w~6E","="],
  w 39 33 0 840000 840515 100 4788 ["K5X.*'?KJb!!Yfp=NTo%)Tbz?0,YU|OVVfK1ryQHSaZAgUDKfTBHlOB.U+a$O|,K","F>E}[4VH=aU{kT>/vx*_EM3ee'*o7MWVVOtK0v&ji~D?g%-e`^5yhG?2mFk2@7dZ","!%5BU?aAr/-Zx^hOvxVwvfSo}cRno5Y[x&@,)&}W%#zPXj^NdaOJB0Y[(DYiU}N@","ZR?.e@=zm_E(S<sApj@xnp[H`&ZJm&4e)R3KT1pn*[(n[~4`.|Y'*gE2_F]JK5Tb","RxiR7]5H6t;^Z!*[Le0(Q]f/fu,>iH!B5!Y3SIa:r?5RLzW=|?~Yj).2EmsBye):","x6t5C(p7;I)@bIEsF|yj^mh]t<zVv5I3J(x{J[Bt-6<n=Y/yF?]LeSG=a9,+c+@J","z'iFK']Ec|x?hh:ni3'GuDq_~XQufvQ#FrlU,D,)_4@sB0D]5S1bkD'2VAmv/W*3","GxhIz`H9*x.&oGUZ{qPJAMMA=[P~e]$p;mU_EZ$Btj!IB?z90_`2Y~pfp7,;|/1)","$#~ZQXCt@Rf&9p?>{oT{n8!"],
  w 39 33 100 840516 840704 8 395 ["&XGGp:S^xjc{`|&eD|,q.@klK*QgRf7gkA;:"]]

private def r39_12 : List (Chunk 39) := [
  w 39 32 0 850000 850578 100 4612 [":kw}S2FY!88AFga]&f(Ej$vj,~l-h~!RsoJ=rP4ZGFh5yGcm7m2no})7+-%bJa}|","zc#r4Bsy!l:6RHSwt<,.Ck=@CILceoigd'U+8]G|xk7-1*v6R}/[&;/*{i,y9H]V","OPu)}r!3l4l1?TE&]X43T@;(.LTCk}Ql(i2?Wv5q1j+c=aF`yLHm~5gcb|;(Gjg?","wi@H_p6g#.x=N2^8xN^jW/Yv;3cYx3bHY#I7Ck-R-I(!`LzINqXj<l'@dyhN8+h*","lujd%CQaJ(TV'Rsu%OMmlcp0eGCzlo.a-['084{.&xnT>Y@]om=1W3P'Fs'EG)OU","+2p-M_x07)M_MdSa^k^7Z7q'd-+u)nZo_SAFFUDFt@MAgV{phIhpYX^/#KtD4Hjl","XF2AJ^-qL'])_rfgv=N:Mlw}n8~j#CdtmNRc@bq5MNiU$tp|iq`&1Y88SL9wsA-q","X&nt_DglR1N3N9I4hbe692QFT3FHp5I)!BY*'n3U3~lE3m`)T41`O9.z~`WQolZj","syjmw@/Zk}4g]j+[>z*re9P'Q=k_>4A{m^oQ+"],
  w 39 32 100 850640 850641 2 98 ["#i2GG<Je"],
  w 39 31 0 860000 860640 96 4268 ["TQQDq$i)`BTP<!/%QAG_+].$CbE@>pm:G>LVA>e[!<p:H(x2YNtNs3ONvUbmAav?","H<rae?v!=*j3@(-a)RrkeKsQ_&k4/33m7&MfyhjEf!kwi9o2kT80d$%)HytiLn_w","h9<A/_Hb2?Y'rpFPzS[xxht0KiMF&~M,,%m*YSH,u3vO~s<-pJ?^D?Xr}=Ze`)2L","'Q'q@~y5vpzRYVW/u{@{Wne@?!Vg,>zp~2G9Akr{Px~u$K${YvgV?|i<@S`_!v1^","V1%QTZ'|J[ixl<RURH_3.$p8X>*Rd#RacX!w',SI<.}GB$C?.`sz6u/.zXHx69QO","u9gY7Uv!s2PUl#lldYE!Cw$B|U.>&`wqhmr^6/t^9KZVVnl'#=es[iwDIdI6,!:s","D!}rJ7BznNv5b(G2oXj)suFT;0AX#G=;H;XUg7h^w7Gw?C*g)+o).z63j'PO$292","u<57#('+jNx/uLj~wBiG{sCx0M;rM'0u+?(_e)^zg}E-vdwjd)|QIYPuJFu&_(xH","$xty_[X?V#T0{At%<G8HAh]a-vvFe"],
  w 39 30 0 870000 870640 91 3893 [":T_.[By3@*6TrvN5)7TAPH'{MomZ$T4yzY.Je^S808q`D*H//;kca0v66bQJ[(v@","YuX4.uwCo4#]M6,+lo5k1)u.$Q:-q;O*iEIXY'G#Z7Q[t//FuZ}DhPltRyL2I>Db","?hhAIA^E'i)ssTBMyhb}]fTM3)PY2kp{+1AHN'WN|w.U11`ydmXw3QNa|8,zrB!k","Q->Jd*O!?Y{:lj>E!NUh,?x:-AGD(Ar50E2'9*U2hxoivsxMO7C-h~h%7wS?{UW>","r|m=XSJzgTB3QWI_!M5T@s#m&fMEy:0x1nx]SR}0?o<PM/BM+G5l5GIi|N?desco","IC}B,ba-ZppZ-$t9Xl^z5ZxN9$kZ;C[uI@aQvC@VuS0Klz&gD-]e@|(Y&wV}?^c;","&Ur/B9PYXC.>L;e2RRZAG8L8f=@98+:jP#Kglq9$x**65poN|0!dn)(<Xj5XAsi'","hEvb-|K$SEv;-UuAeLoz(C>>xw,>0:Pwh4T[k)m<R+IwC>|yXZi-0Qz/~WSNSr#Y","S"]]

private def r39_13 : List (Chunk 39) := [
  w 39 29 0 880000 880577 85 3503 ["%!j&PqFeYh*~ge{l0:c[*P|fKTY=I|]p5F<S&uZxtz9ZJR4Bk52:CB}~C8*TY>Yr","aRzYg'D!gn~u)sESr1wq`3/WjCW}$OZ_7~r>W7_'hf]&_3AT/CC|]0a]NKYu&qvQ","usOPwqM:(j@F`_7mCeN+dSLW+9{XbD,i;FJOVgHF/2x@UNn=8pr%reC@/EA$O=qF","`#x]RyfwO@OIV%,9^2doc29S/&4n<r(ov%gP3^[NDMHWHqVnd1t7D>@nNYK9hRwY","=pUZsnF2qp2{A/sJ;^A%}@1gV$y3.I;PqB0`hsDFj8_A<O2p+u[`/9e~S^iIAuCJ","iIavuM@3W)L]d_Rmdn!X;=)-VN%Rl'rK#hl+&ukXm+q!/hXb(+BS6%Stf&feKK`=","G}YyI`9~D_$(PK/re5<Lo?%*gKR0D|<<=cz{]Wr!pyl5IqQ'#1kwSYs?9DOesalB",">iAp-AP$M.wa@#6_lNh:)i7';Hf-Q!<L=vu63zGK?ue'N(0"],
  w 39 28 0 890000 890576 80 3175 ["-KH!$I=p]}Ioc^r@KrPAXI>zC1n9}R$S4N!k~,++z04FCm,>H{g+Ygla-Vou=l0^","JZ$zrM{iJ3U;]cQ<jr>/I2`2Ac4bK+45Q6H/3+:YX_d*>SS=zNf@]t:pyBgtRI%J","5'_C?#6p~]}maq8EO*MhCi]TK*,s5O/R3xs,[;6zTUhMTd~(21_-lD/WQ2Q0`ewI","?e?xagVtRn8{m}yA1bF#0>0I,|uH7@/qF.)Bh?,X_2:R13l9QQ~&49tNE5Ux~B:x","E6fSrWFZi#za&zxp~SL&<_,EcYbp*puQ{f2]-,+4,w[f8~!BoI5sAW'`.,TtAQZY","bE27Yu_05m`[4Tb9otspKG%m{f=`ULdNHJ|{g}f6{>w2V84uH~k7_KB9AO>AOzJ}","MC6BdoMD5|lav,Asy||C~bC#e]AX`k!9:jIXwiq{s=|Ebf!L<!=UxT)~/G*F.G`6","5bwNV!VB!^V=.g5:MwV"],
  w 39 27 0 900000 900576 75 2870 ["kh2XK(nRAT6uI[Z$9dP{5QNn#nh*Yt~>GbVF^UgE6+Ejb}JrkO^w[.#FEr(Hh|K)","G4*z%$1My/I1JG~*qY,p*w0p2qWib8~q~KnnG}(o3z>5|IW`J5<+W)+N$_!VS[^A","'V4Xe<3wqd9ME#qfU!yHM3m]Q@t-<@OIXkPgu$3)](?SSa;>ba]@tw]fu5<apRa3",";K|i8Q=YaKB/z)t>]FF@IBR1,LH;5USzE)|X.RMn/`[H$9TS't2as-BvH;v5mw`p","7I+pe~W'|Rm'uAhTvJcH_nGZy^K<3XF>gpA*bxLB-;.oc#!p~wJ;WA(mn~B1dxlo","eS&K8e?Z%PlW/i{:$P[eCcPmjA]Q2#0mOXa'a|-tmuEbluLn1;c;`MqvNvJtpqD>","l_b{aTn~k+F2[.tB(ObI.|O(?v'_#Br@j;6bE9=1quAHFP,7"],
  w 39 26 0 910000 910513 70 2579 ["Jm+9M33?,/b6'`UXJ)Q5ysyGCHIoc*j8/`1K$D@mLx{0Jur%Tr5%_zv[br:/2Pkv","kITVQ]}<JGZ2~WFG1q6*DYJ#G1v9O:b(?0Wu)ZlPne[ML,{(BgKIFXE+S_e$:`;T","Z00MEeNv}!`y)DHi=m<qMl@}9^kx:-kCCwdX+ts1F2tw3mNb$riGfaqCgfkuWC'Z","-7-gh;<#]-1y:XVoFF3MI_+z,Es^)BS?K4bVIEAC.|[jHul:ae.zNBe)_4BQR(<d","!0t9H(F{r|RI9QK+|4C1i_;_|0TW*j`|u7Tgm[sE:V}yjTh%J?ms3ZpWOUh=6m:{","0fcm&v6(&^ce&F$FCn~UHcqb8&KL}$y_OP0dIKM/`4t!wiF=#hTRln?Ad(S_odcB","5OjnC=T_n<_>`LnrsX6tuc$H//"]]

private def r39_14 : List (Chunk 39) := [
  w 39 25 0 920000 920512 65 2307 ["sRB=p:t.O;Gdknf;,%>+s3*iZZX;eQUj1]KZM(v+u%FE$bl})KifM'%_yD@ez1Sj","P3v25R$+cCQnSQpxyv|ee3H5-&ot0<wSvWVk_o@J$J4kkPC~L8Yly#Wsy8k<K?v<","M3*Lac995rOI%$F]=Cz,c7k<o5AzKK:[HZf{}ir0^@YU:C5R9cy7v~}'GyHC8zU+","e0.f|0Rr:g$`Gi%/n}xYH$W##*/cs}4VzQhzNZ7xtIuHcSxrB-`1#g7*$#=}n/rQ","if'i*/y4of+p*FbmUu|2U]$.d1fZR_1UZOA1dWV~9sTM*i#_c}Ufpw#B;a>x;2O4","gGS5Z}of.%8{w2J='i,>wHZ=Egftoq;+p%{?63&=4({QqI&Y%>m)R$DA2rs:Y]AB","(_o'"],
  w 39 24 0 930000 930512 61 2084 ["9dh7]546RZ}>XIebK[O*auJ-KG),H%y%3BDj;jtG'P=7Y]YL2+0ZJAgo<40r6t}E","9[1[4P<F9To_z!!7Z3!,[UjmL+iq>oXhHnOa,y+3yWm8:0?.XG?gK[8)i7]tIKW[","f<Vy]Nm']k<s#.cc7:-;qa^u&OYg[p,<Ix:?hd[J2NYE@%amO9qfpQ[JWLkJaKmx","CRe$6+:-_pF^QrFGdI*it`NS1x[}_i8t7QQ[-[pw2D{GW)17^+ClB.mZx+^>zV?V","B#}+*P@^SB([!R/|(Yrf<EF0fppV1NqEqrtJ?w=zr>dY>sO@(2_O={+5lX{kJF99","+Xc'NeF;.aWxgKyvhyKQ:_5U-Cs!oz,!0v]4"],
  w 39 23 0 940000 940449 56 1841 ["VV*R@Oi0R|nUt.117ZVyi=(y3CO.bXYa*Fx^z_^w;{N's|1L%C5wgY)R}NBJvdV.","Mc`*R)8fti3d|>uY<;C6Tm!.mvw<CF?Gp9FS;h/{)Qe/?F>?fg.mtzAE|7{d=L/r","QZ~O%}X.[aI08SNX,5yYzSfK%g@^Zkr;_B{WsW]p_pf:|a8L>S!o~EFxs)&>KQhm","<iGvG;X|-m4L[<^77*Y6J'9M;yd8t?EQb^65~HsNIgpH~ir@~+HkPB.lw0XD-X):","EeOw583UZKrLoFHCLzoKJ]pLYETCKY6WC?^3H~NM`D;nQ@b9A0Jo82@i;zbUM>!k",",l`*Ii+DgP]^9ab:Po]"],
  w 39 22 0 950000 950448 52 1643 ["r5Y|#]kl:g]VN_V|,bmr-?Z]guS^E1/IT;SZ94bS1=;sOre.IJ/BQm0'IK])yyPE","|lw!aR_#vVz}!ba}l-QhstXS,P_KC_6]~Uy{{Z<43?M+e[y^tWq>0L|Vkliq.m|M","uV>o:mC_IcyYSin]!C&k?[tu&!>}dPXhEJHoU5b0=V0c,xe@[`it~0~xfA',*ksl","UR$u$`yjM2'[a1na3{x'^8U}dvr|P.Zl0HC8cGvr!VT#*G&hUxKze-E]o`hSUv`|","#LgRkL;|W#8e'k~N2%s$?Aze&c&dih$+k}dU`/x*Q${#<+aaLQq]0M7^&G$Eo,ws","&Os?q_"]]

private def r39_15 : List (Chunk 39) := [
  w 39 21 0 960000 960448 48 1459 ["Z:l3DRn|_uPQ<dA,9gd-M1k74mtl{p:h_asGM(gVpTeZ(Y@U8DSZx=[x8R&wUCSB","lImLt0:R]XW`:SZ((gdV2Q+PFOj9]Ze&7E(e04hvkLp+i`:(]yRThoXUwG7v_a/p","zx-(bsgBvyk;.z6([MuKFeuZZHrd~R]y30N'|S~!X;83#6~x#tdz#haz'qA7O0.7","/`s2#?;C`Z}:-i:-`:4r;sICbfBc9{Iq{eG)@ik;(cyik`@pn;7${f(w@M`Q{dBf","3lf;A4EE=}&g3,4Z_j?l(p#LDH@#eOB!6:i!|Z9}Mhg"],
  w 39 20 0 970000 970385 44 1283 ["4E^Lw`2N)s:zUEd-3(_`JIO?Ib5?5mYr.)VrGpSsRQ@=mu^*V'3XIz6N'e8eoFtS","YNGiK?|$[6sL$2VYx1j&]TL.Nxd6deuUISOVJVBieDf.)+:3$C,.&!l_/K}d(27Y","f(b03=M(ERPkU7yNfFZa@}tmwE)<Zn?`t*g0|J#n%/_>h(-98xARF,f%*q|Eb&f=","W9xtlMZq]1XFfBdruPiHJ@dCz&h<p!Af|tHCe5sIJip+8Fi/QxWW6)!Xs-SMCSer","+({;gb6&2mXYh<~mZy_2{{r7$L<%[w"],
  w 39 19 0 980000 980384 40 1120 ["{xmklim}h0&`Vrk1LSU(g0QOE.ueh_2t9u-6ba9KD/eT'DhR|G8GCqf{I'anM:AK","vA.s?Jq*IHTCgIPSJfRFv&30A7fl|<v|h?1W+2+*nOa:y(99J/hC)w@q-e!iU<bY","C*Bj|GI3(8'v]k;&ucDxT?iI`t5P/f9,<XZmPw]{=^eT}bD9.97._ti%jRIbaj(w","e|^QTQ_[4y)e6W,&W`rIOJ/q3LI^8<BLF`#D!d}j5+F{csM=?1}_*p2lNS.#EA|s",".$)s+|I$L!"],
  w 39 18 0 990000 990384 37 994 ["_j>ksOJ{qP58R,9]5}a<Fg<O|gbN^p<jB62]x1q&C!!{,+UGspIi<fJM&+w:URLU","IN1ti~@D=ufY2HOwFWa(-BX[Q~S>/]@U&?m$7P]En;raP7|;XfWlDJY1UY{}m9ba","JkWpIQW5)9DyQhdW19&}:)UYLQ,@QbZ_5!0/u((G5fbN[~:mVnMoY1]w}e:1I,C2","6:k~9u!YAXIiMLdS.(Da2fT1iQ7n)k;Nd^<<a4'k-OhA~XHXKFImu"]]

private def r39_16 : List (Chunk 39) := [
  w 39 17 0 1000000 1000321 33 849 ["iH-yW>T>tuUs+%C2L(iYFVs7kpr?keY=AM4eM3)Zk`8LI~LYqcoN![gV&rg({zE#","c)HuLAmK2c+njnXN:R8qX@pmZ.%QDKi,5u>*Gvw2ghxDVH;'+w$HrJlto5%AWcH'","J,6>y[ps:J,(--|r[i0?Fa:#V9#&Dcl2YbJ1krJIqOnsk)CP@5c+u`~ZJ{tB)44O","+!Id%lHeCFz(O$_5VKsUDFGAkqK6GFm"],
  w 39 16 0 1010000 1010320 30 738 ["*:q,as[rw##fkONnB3ZO3G}g.d,uHWkW_w3=LyK@Q)qZY.]JV&1UfH:;?66Lppd;","M76ypdt_:2AQ/AVrz)|6hR)<;_q(Q,4fQ5evPAtAs#B,(Jk'?FWRNt`Hef,.b_{y",";|t:F{FhYJIzIiUXMm|]5,6iSuMga_6*SD^nA~msXiGqoXuM1cG_qqvo8!.3Eb%h","a4%$!QrH~]+~n&/["],
  w 39 15 0 1020000 1020320 27 636 ["<FMV=WJXXf}y6UfWw{7.6M7g-(L{?W-8;/5+bC{~tb6I8FtGGekn{:4WfzG|Vbf!","s&:NGRxa@zJ;t%}BCR{ec|4{F+,hA{1noIrf|urMit3[tjcj0i/kZ3T$5t/[;)p,","$Ugy-w+y0n<Dwr!Q7*^~>[KBt<7qF<Qc)tLs<-U'H[?xg'xkzJmf--t"],
  w 39 14 0 1030000 1030257 24 537 ["U&L+B_%Z_$zl@>.6}w{[j3V'fdb'u,/Pkouy,toB7&vY>B;R!tM*-{3|&q;Pw#Hp","V7cV'?wW&NVJW^,n]b~;7EJJZ6cjRxBdPNY;=Qx(b;`f5cm~l;WzS^[xyOYx$vW@","-:obtS(d+[[u?>vhtRdNpm4~>{/d*hOzLOF9;*d"]]

private def r39_17 : List (Chunk 39) := [
  w 39 13 0 1040000 1040256 21 447 ["8X~=}IEOaWqo}7ZTGgs(We4O4vEAm1~~+|#OXeVS5GpVoHvA=k#rht+CBaeEQLW;","NI#2-'/R^.'D?{gUI$.MD]go=Iu$BF`)Yk[G:DpO?[ua#<^S3=b$.!9dPP~fpN>O","82SZc_'8v^tgAxJp"],
  w 39 12 0 1050000 1050256 19 384 ["*tK&>Gs+C.()XRq/ZhV+@klm9C=d<U~o6$-?//H@cUWS/W'%C6'.lJpYh:k.GbwF","NN@M~!4P~#d.P_.^*Fw.^b!QWu`Lyjto=oA@nd^g4X[*/c4IA:gmG4,vLFSaSB@Y","-C"],
  w 39 11 0 1060000 1060193 16 305 ["sg7J2Q[$:K^S<dMuCF-reYcjukLT_P-9.p+Cb_#cTW5?!ql+mdmIfDlV4X)N}b4>","6z>G'3{qlnUpMRwdIZ_DqAv9+DPfKYc'9]#bhy3#%V~8"],
  w 39 10 0 1070000 1070192 14 251 ["'07yIxSoTD=H_;R(vmiUxLc<7)1T`W_1jLqhJZ1I3b$ffb`LO#d[h,'Eo,N2;hl[","-k_n1WG%/YNX*KWnNX_G`8Q]s+16a]xZBX"]]

private def r39_18 : List (Chunk 39) := [
  w 39 9 0 1080000 1080192 12 203 ["q&dfZi|U!{2Kp!jkJYxV%Mc9c8w!*GdY81XB1Ms';AawOJo^Swd9-CMyaA,&R.nr","2P*KgWb`/WC&X#"],
  w 39 8 0 1090000 1090129 10 157 ["xK8`MF|b-%IEM,)bVC.6FQae6cK?-h^wJwSK=5;W{`qG:CUj%Vls'naJ8cGD@4lK",")$'O2"],
  w 39 7 0 1100000 1100128 8 117 ["$2Sb3Qo[T)63$0hr?^DT%L9l},2PTVH}K{W2HX(DA+P_h:ZwHX,~R"],
  w 39 6 0 1110000 1110128 7 95 ["#%YP$nO,Z9|D$Eh|pA-wN2De8x?r^8P`xxMTXI<$mS.&2&"]]

private def r39_19 : List (Chunk 39) := [
  w 39 5 0 1120000 1120065 5 62 ["VFz0L+xq`Ot21~3|+UY>-nN9^_>mkI!"],
  w 39 4 0 1130000 1130064 4 45 ["HK'kMd9]:[lrTSB*49;zhMSDy`"],
  w 39 3 0 1140000 1140064 3 31 ["$gR|26Q,_~d*N5#S9"],
  w 39 2 0 1150000 1150001 2 18 ["#+C^xY!]LnYfc"]]

private def r39_20 : List (Chunk 39) := [
  w 39 1 0 1160000 1160000 1 8 ["+YjWj"],
  w 39 0 0 1170000 1170000 1 7 ["_wia~"]]
private def chunks39:List (Chunk 39):=r39_0 ++ r39_1 ++ r39_2 ++ r39_3 ++ r39_4 ++ r39_5 ++ r39_6 ++ r39_7 ++ r39_8 ++ r39_9 ++ r39_10 ++ r39_11 ++ r39_12 ++ r39_13 ++ r39_14 ++ r39_15 ++ r39_16 ++ r39_17 ++ r39_18 ++ r39_19 ++ r39_20
def rows39:=rowsFrom chunks39

theorem good39 : ∀ r ∈ rows39,good 39 r=true:=rowsFrom_good chunks39

theorem sorted39 : rows39.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks39 0 (by decide +kernel)).1

theorem mass39 (i : Fin 57) :
    bandCount 39 (i.val:ℤ) 56 14≤(rows39.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks39).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 39 (j:ℤ) 56 14≤mass j chunks39))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total39 : (rows39.map (price 39)).sum = 333221 :=
  (total_eq chunks39).trans (by decide +kernel)


end Final50RankReceipt

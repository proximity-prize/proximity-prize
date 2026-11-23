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



private def r40_0 : List (Chunk 40) := [
  w 40 56 0 640016 640403 100 9532 [],
  w 40 56 100 640450 640901 100 9168 [],
  w 40 56 200 640902 640903 2 167 [],
  w 40 55 0 650015 650399 100 9262 ["L>Pw(<*/oKekW4ymM[qV@znr:jqmHy|H4T(O(Z@-XEJE~agNpq&Pkb+fW2u+%;/o","2h%~7}wFth]/XHyGY$XgFh%;|<dwIi7xS<my;KP<M<^RiW-c(|Z`sgTI6$8IIX:a","+h5%kD8aYAXEYs(6b:~RVfg}>Fc?r-^K"]]

private def r40_1 : List (Chunk 40) := [
  w 40 55 100 650400 650900 100 8818 [";P6J}iP8W'/iRM0<l44`[1L]G`JQ]lHmboD6S0@k&G9D3FdAni0?oEOZ.4.!81(C",":tiuo}L}Zsl7,[/#RY$cqM_HiR@>9&RQ|b|tnFMp0@*+eDc[Tkvj`)L%xOaEnG0A","Jc#3S.*3%e~6mS7!Yb%-9wS$Tse$=TjN_A*~X(]"],
  w 40 55 200 650901 650902 2 163 ["G%W"],
  w 40 54 0 660014 660395 100 9013 ["VJZ8iV21%4`kL{b-58Kqr-*bG79SL5K}fO2}5apaAJ[iD[0ZQ)3Ea4{Gb8+&t16J","i*rrU<ehpS{oijR+U-IJfq6E=s-[sU=%u)Un8?u!j$o`G$v*<YYo7o{DG5Xg6Wje","&V(zX4fK=J3++k:9ia>I('bYR6V{y!O4*F5x+A5;KB8n'`s"],
  w 40 54 100 660396 660899 100 8503 ["(~EX095|=@N,]~tLs'sZR?%n<C8Gk4zp*=6yR_Ynm58t*pm|HIjwHv09%LO'2<}d","Z)2hXT13I%!hr@|Xh%Wf=+rDITSWN?J#,XN?!!sm?%%d.`#[{e_dmmoP<<0@Q.c=","JW3`8h1P{Xe518r2'RBz+AxW$Y<PEABJ3:B(~n-HH]G>uS>0@6mC(/8X2z/g|/o0",":"]]

private def r40_2 : List (Chunk 40) := [
  w 40 54 200 660900 660902 3 239 ["1'%IG"],
  w 40 53 0 670013 670391 100 8782 ["|2),?(UFdA;{Dy9Fh-*_If0n^-,EXAvUlUw#8(|Q}mRjtl%vz1zD~VH4M$+hn,_:","`6c@~7'$/%+V@0k$zeJNkZ*i&l|;f(j[1+pmdS0eHY#M/@Ern/f(NvCo|yhU$1-V","n<M]NMEZij;m1_4SR@y-bMOLvO(%nQW%~>ofquNsX&-W`&|a^qGZNCE8C>r~sg?F","'qU!Cx!=02"],
  w 40 53 100 670392 670899 100 8194 ["bfgH+*_d>3v?Mi*.:~iQ!2`YlwK5fUGckVLZi^.n0xY5>9B-RZy~CVJ,z6aX8E|/","*S}{]P|]0=K?cJV@0}@4b%W#l)Ld[@O1S2iEi~A}w^i3fEkmeFhQtG`C$h>j~O#L","[`62|Db=@C,F@VpkAGl,f^a_u:vR%'<)g!k(f4fJqoPP4R;edP<tYMBE9|dc|(9y","]c/cnT2*h%X^u=pb{_C&!eqKyTfP[U1]8_"],
  w 40 53 200 670900 670901 2 155 ["#-#qd"]]

private def r40_3 : List (Chunk 40) := [
  w 40 52 0 680012 680387 100 8572 ["_bkpq~6!0Jl7JKB1<.^W5O5a`CzLm]*a7$VOWb-4Va?Vm:*Kzeh<0ZdeD)[tfp}B","`@^5BWV->~AlXPg;.{gvt7}!?:l^|M|}=/WcfZv{=q6+vz!,]YSu99.Pj9g3fOkc","C/TsmUt%BhfK{&!,Jlx$4BBsDc|R]09PaVF>q,5}P-[Ms}QWJ[4;aeITev7mVT`d","%j7Ob{uv{Ds!(pw2DA>L6Ok>A)2!*cavP%Y/'"],
  w 40 52 100 680388 680899 100 7914 ["U^CEQ,mJu'Y+eS6;)JG>rBQbM^6d]|=`4G^tx;/Bzl;P=^py:>dTfA5..fFa+}s;","nw~JmQICXx%b{e?m7o%H~.DwkL(l='(gn+BosofDHn.T?`(Em'N8+a9PQ5yF9Ks$","oJ>#da5WV;{pG}*NQ%p!a4$<cOq32MrMgcMcyZ)j}W&#9Jt;MuFEJ?+'6s270EDp","i-UB49v+P|I)qOYg6B7zIr5q7[pFkZe,/&wJ1}mxo}M&[^ASN]8k=-XP0T2(S"],
  w 40 52 200 680900 680901 2 153 ["%hOGH"],
  w 40 51 0 690011 690384 100 8346 ["n%y9*$6`D[rj|z*R_lkR4sp>;:`+0#G=a(~vvr2BcuC#x'(z.Lrw,P(gT#.ihFzg","+7aw:i-N+x<I>Uk^c~|4^k;n[Ea%S@ivY!JRNmVi)99@&gFd|#ez0A(k%2iWU>O3","{hrMgF!!K6$LmOE*FUb{EmqE+Wp9mEZ?GN*}_qn3+%b(TTRPIVH6^,N.24;U`?0`","4|7<,}'2~(>8,@9Q{JK`=3%(cX6/;.K*jVA}nb]`zk9$;an0`qJR6+w:6voYO"]]

private def r40_4 : List (Chunk 40) := [
  w 40 51 100 690385 690900 100 7669 ["4Y.[}_i$Ag'_'mX>L0n]RyN>'8Sn)!`3qb!rb34W9UFfF8,g|#<wK9zQ@z-NXH<}",";qx(c(oNLvr?>5t%}Qqjp|SU4GDc{d*2N**6c.C7tYRrp&Wr[r}nKoIs}j[`(B@2","T?qsS)$RKke6#tT:xd!)?'smpO#OvE:VSYWG<Pu7=ZEYp:f}!,}mYnrQ@y4d{<tN","jRr$6AMXL!DsB1}I-z_num6]cyUvB*y%j$3O3AcOU6&m85S>BMtq|~OSCEZ1ErUg","-wZ$CfWHJxD[,H_UXUJCz<UR-H`5S"],
  w 40 50 0 700010 700335 100 8171 ["?Xu4p5Dl!e[4>p2>]?byLEsN{.#,mC]A-A~DT/r`IsV>bG)<pt5m{xJu@`~).JkJ","fw`Z5IajV#=dTpH7%#253=(OG9w9ty>s2yx6Mp/(t'U414O?p6.?}zkG??Vmgat/","@:Hx6xX{NyA8]Z-R7_gsLLE?^J*gaS8%C)FU))&1q]$!mn>(AIcq8atE9XcgP<lW","8JP3CfM|.MY&-Dr{l~JM{%:dm-#NYZX$1n0c6~,q7Swrh.-P|deZvDTYnUJFk+d3","#$1p(-3qsEWwHQOI=v=`:"],
  w 40 50 100 700336 700900 99 7348 [";YEBj,1M;v/So!h&X)q($w-|9}m{dj|vpd'o1z,)!Nz(jXchA.i~SMaLJD{{K54m","[xAAV4`8bl|>g:PjR&)N{6:7tGx|I]bCN9*.fbm{V4-DN&<qY0n5|,P,WV1zy'`Q",".!/Lg#70:.ribj1dk{_c4GjK1/eeIdp=S=}8dM5pjC12.]VuLG:VJHDI3JKse<?i","Xx]u<*=T=R`T!NOThxO`gjt..%%u:PhnLZb!-iBa#_Ov4sGxyyaIC}/o}TISJCqV",">vr{95_K/.&OF'~|.iK+8RPCBLsX{()N_{dIXLH.:5S.*6.;@VBt"],
  w 40 49 0 710009 710333 100 8007 ["rhqd@8zamu~C+RCbH;A#bU-7IT_ub|>X5K8'FQx02d,rO%MuEpumBdcU[nEna{B*","Gcd1h$7[Up$3OJ9kJJ)F#A=UQWrol#h`wk)F8Dp_P>j<x#>8Q@P3[+zaD%J.e!%-","d|lzaib;'@)]KqALl))[0@KXvIwE[JRCx4]kW.{$yr/I.h9]35f|g,h+a^4}lT?*","U~c/?Z@K+Y4GT,QBBnq>;6L?(9J>2;l!Zw#4CSdXYl?67e2W<3dRs3/-j)2;kw8b","(e,{`*_C],jOFTI#(r/.'neFmVNZ+j.u1kBMUyFN2;*A"]]

private def r40_5 : List (Chunk 40) := [
  w 40 49 100 710334 710899 96 6888 ["iav0d^`~x}jrkx(famZZ:!C)3`@F[P0>^B)z+rJo`j/~is99%Jy&Y{VTmqXgNW<,","r}K3_]5z;D|0v9Pr(pZbqx-)j{icm_!..|-fOZn]qG8=&^`UJ+'(pw~z2c&QTPw/","W!.;#yi5iO@G`.r42rP?mLQeh8K.k,O1j~2LAR$eGH3{*w[3Aok<?xx]c>6Vqf0t","o]>v;aH.h2GS[TF3z,Rm@CwE(DCdShxPjKuJD_[YRtB0cSS;BoM>^ebaM!ni@`::","HoH4[g~<#N&J7,H{8*}4yge{Z%<J;GG}_Yv}`6GTu!O,47.IXKQ#l;>~Zx0f6Re7","#LOq,cgB9"],
  w 40 48 0 720008 720330 100 7863 ["<>hPw+;nq`dVSz>k`!wr>l?%+S)%z[/FHvUzx;IOU#5%I~[<;lGQ;@70Td:{[T,2",">JxSIvgat~dhZi>g-%wGee5C'SXKaS<r&V'hV}o0yfW1xyp-XyCXh[S<N@kyb~BJ","?YzOpj[<(fUG-Cb{V,03q0K;3+M86kdh92XbU~|Tc>?#~iQiZjNcg|v-B@_/9ZY$","J1`+_(}>~7`>:nI=6Ah~r:12wg8Df0y`+Vniod=(LYo'$o)G5#?DJ]dZ_'_R6wnW","</@!.2e}=H)S^JwA3tBIu5RR=}!.6H2F3J&r1^,eZG*]05(_VGYTtYx}HA`yJ"],
  w 40 48 100 720331 720899 94 6530 ["T[Hf`J/ii,u*<#uv,@L3.M%$rdh6Pgfcu~7&emS^Z+c%k[f5j.Y5r-9NR^9-'d-z","'|V.Yo}_bi!gX-Yqsv$tB%3V7)$x3=-zuI^&A(8wV]E4w&NZ>e{z[{{;sLmxemLv","'_Y:6XuHaz5$K`J!SaSkdM6ZU},3cP]Y,l%fPwNR-j~v*N69o~<=bK8}R,~Qi7}&","NN|+.e2xyIe2[J#M'73(gmF@au5UE/pT]CSZX>4'B!<7DsT*=B>)w%Kp;b@^j5ER","m.tO!;?k~e[s%1u5/puC(mJ^KpYl*7_d]{'.=s0|LIBRSx964%,hb@xWPL*;zh)>","?jl'0(s!qahnW%wtRij%dX%Wo"],
  w 40 47 0 730007 730329 100 7704 ["+=T|84.Ur~[[KA4LJ5:!s%u=FE@[Bdea(0,{o%@y6m]n</J:<4F2)/_WYvH5-pZ{","e]@vArt.anvWxiahj8.s##_k'58^D`z4jX1xAQ:a&UoQ]~~j{P~JWg[DJyW#0gml","/:{C2hN~C-xFHb2-^`QlO@yqNLC$;MH8kM,awDX_f0M(,W}]6CPk$_<e|Ww&{!}w","^Gk/q`0-?r,R?z+G4i`S3o^Pjbl8p?YT(zjUa>1^~4[[wg7ZJPX/n#FYD:cJEBuW","5Y_~0p/5?CZNf2[Y&qJtRODewtTrvo2P8aQW1t0uf3i;L@)iy_>%_5A6kFfuHjLd","e49Mo,Dh`-.UZYA?)xwS+o}$l"]]

private def r40_6 : List (Chunk 40) := [
  w 40 47 100 730330 730898 90 6057 ["]~oT(]E?o2%}J^=oys=UMNS6dr42opwrRQ4+2`|}`Og0n5v#xuw~FmYJDvDc:?{5","G`;atpiv3m~^P.j0vY1k6UxD3{l{leJ(v$wgl_j<|hd#,MW6OY'xF},~&.|E,&J]","rMuQV~mKYrqRCm?|dvA`I+HI&i,A!oa1FjJ>jn$-)iM%7`<cWlq4ClI}fw&{]gx#","LJ7Al1y9+yJqXcf]029TM'5M=:gA],vnK<iY),rV@1RWMguqs$#,cbDH/$[Eq^$S",")~w-EXG7vkivYIK-sx`jx9}:(PFe1J)&|Xj<[7Q4c9W;Og)uxM.#eilQBK5]Hdtr","2}@>5J+(?KD~7VTc:U_>Ac*qVW%^]"],
  w 40 46 0 740006 740327 100 7550 ["nyx;^(OL%8K/^X-]B'0D!Kbo5~4_Ti`(Vw_Zyt*|KDA?=PatTQ[o`D3|zu&5NbR{","Rh}_D#H7L4M4,pfK9H$d<|IbLpLX.DU^b[d28d5?e*l]1>{yH=+FT}]7++/XK-CC","~=OpHE`IIz'C.+k!jb70HGYGgk@77yV>G#azSRvm|iZ3=dD[x^fK%+]zY.b'Y=jw","pKjKW0?ITlaD,M'0bZ]pz+cqr[VyZ99v1y<B/4Io(@.Sy]dIK-EAfgPmbG}oj-2c","yr/2meN/1e;s+bIZJtJhM;DDw.u&~3%<VxLkDg4_HrGhm`U/!}7o$k3tMhv3vqb6","_.%0#P~<}F<Vxx5+.V+j{[},1Foi/2M.<a-EuQ;;FUkF&ux`}Bte"],
  w 40 46 100 740328 740898 87 5682 ["`D3PC%-25=IwC0/esc')AnT[Oh=h~jR%d<![rYvdM?1h%5->CiPF;NNrR`3%TG)z","'9<MCo=O=M=aDvxf5ApPe{1_1g<Dh})/*>oesft[|f~(sH982Mmg-|LVQR~kXgNY","C9U5tyeI>91dV:_|%Ht,WwoJYmb{*6R2Z@utRj*LE5S^%RywCeAcZ/-ovTPu:>wu","-NSAr4hQ+vu!B0kRo-7([uAI%[JU,r84N%>Rdd|[u[I4[$W&R6)RlzM2uLsSN*lf","(CrJ.v*<WadEE3NHo8zq?YYp{l#hs`il}iT4ul8GKVPe<,yI*B?a-#|KB*;v,:`@","'ru%ZtH+47DK{B,;,w#tg:paJ=P@S_pg"],
  w 40 45 0 750005 750327 100 7366 ["*FuA$5M>CH_S8E@Gk2}GMeKbz!|*u?/Qs}8#m|BF~f}0oQ=,k/ezmLgt&2WvVYNk","d`7dauQ[`OU7]dz3},EyvWC>8i(kA:L7o*DL.Y<Z~P^so8>38[3}5M0=[V4@e8U)","fGk%;}I.=|$Ly2wrovjf0yE-M-n5'P4DX^JJr)HCs>EDy>(K!&!94?'9V6jS`mab","&?zETxCr658L!9zsNGQ#DcK$`z=;(uK#hdxv8xCXp_H5LL`q<R9E<R4/vMyb#!HR","j@B,I?r`t!IY<A[l_!n;eQ7<+%>F(K*Zo|[XfuoPR&Vj&O4=JnNqG}L&:F>sD_VE","f!ImW2+4`:gUIgy&<g{/];.cqM`GBXo&Wi}2b/}*yz/=7LlV[T2=JYUmj-kv.Wt}","'^D:ibEG_F(?S^7RN-"]]

private def r40_7 : List (Chunk 40) := [
  w 40 45 100 750328 750897 82 5197 ["y`[uArBjpPvTz6TmrRtKF^JnLRXK`c^EqEBPiI2:'xHQ]5M3:kjYSI`nUe<tVey6","2k/*^yn@&rS^ON?svBlAF*2u?W^${~/S!Brae_gZ:?M#K>e6FEq)H9!*lk=5r34p","c_uB4;p~Q;2gYX~muHzKVOT/&^u'm6$XZca]eLQoR[f%9!_mH*-dc9dYF>`Q=qm1","$/H1b?u:FI>3X')?uRlL4+nzyhI}:2.1Us,aq|1K_Z5glW;c-pt<`D/O.[/AX%hQ","dbUZ2YNn<LI.4vg:JLbGHim4c|3i%dCBoLoo;}oCd}9>]D98]TZIDU?a2:Mc;Rkg","J8X[s0fuubz*G/'k`1:"],
  w 40 44 0 760004 760326 100 7186 [">;]Kc5q~!PJjgrZU/q<NTR4+3On%|rBjjW0*S64n07{b;_dEzJ%I]X['[mgTHt=g","aaXD5i@4.JK?SBIj:Ric%255Vuc@eO+>F]KPT-XZ_ppTV9{l^VSBT@8uwv9[0!?j","7i-32#Q>AoH5U:^~TG+$JF[bgL:PKfxJHyC'x=g/][{0*o~`3F0yqoj`#-N9:9n~","m_0]-LgXCP.ID++x4d1GF;K{=PArQy205zCqqo~J9:l&8rr>6z!>>rxz5uff6~3$","Z{%@84GSYwEU78a3_@,Y{c`hYVDU(5nf)RCod/QZSFdfl<T%j4{&sBl}#_jDZg/r","`7sX5O&SRc*JBRP@LNQ=+qkQSCnk?z)I]FRdPQu&?m4f!WtN+},nyONCSs%Vdv53",")(+TJbbM%7oA3"],
  w 40 44 100 760327 760897 78 4803 ["1=mA4pqDm8EioSD:3;Lu`IW0Gio`G}[!z&RBlOI4:+=qIv8pG3W6m%OQaH`F:dip","(7V2alEp^c!M4@[3XyLew)C;p8gNmv0=O_Jw)z'j!NOD/T8T<zmou7:JQBFg66ZE","u9:]@n|o1rUWWG<iQw=rtU)!?*Bve;=k|t-d|`,qUaOAJyX_4m<tK$!q2k+`!q~H","=}jjOaRgv.%1sL-+o%[-u9S.^Em]ua1g4hF[gUb51aL/^v0e[d1i*7]J{V]Ih&OC","t@O..s4a=#T'>dhi|SPhO-c,Z7}>7K]OfES|wyV@Z5[4>]-,7t(,QU:0qFuvDvyn","%2Y$_f}hZQ;]{Br,c"],
  w 40 43 0 770003 770327 100 6974 ["ZGV|8Oyop>+gc{Gor_t5A6c#KVI;e8Hi5z@C:<BOn+drMW#fFK]otXl<afkm*Aok","8HSE%)z_<>ah$_Asv4=`Hm)l?*7V%/gY<xpI+-`'U&x12BZ}U#yPn{[in[PhqQ@2","h9PH%(wawn}R4F#:_kO4Ko7w)9*Ui|s}RPU#h[runvBy[v);)qUo)x=QcgH:1TM7","0Cf1wr6j^&xLGLML<B9R>rP39hc~;B.52X;t5zktWY<|7PLk=QG;]:O<Tb9H:#Sf","O(EM}3tAp$oU,8EaF`fzU75sF]WX6q!-7CNlt:(J;~j1-O4mzcaXa!6VSh4Xq@O@","Abi9SvK#Yff&ze#3d[N2dge7zqs=m_c,H4MhLnF<c|&]XfnEHBYa`gOi!BV[F2-w","#{6NH8yp2<OvZW~iJmX(3u830>Vr"]]

private def r40_8 : List (Chunk 40) := [
  w 40 43 100 770328 770896 72 4305 ["9Ku$RE1e9We%,loi6~>}G*t;^:A!d$bi0o;(F2t[fQEcU7Eok@LBvI91-6'qHrm6","YjF-tP~T({dn*6ZPd-Bc.md]O(D6#4n`nO!%LlG]jsKZ|E'`yl(!?_'!*l-:RPGl","8l/mTstT]Rp>/S-eH~JE}ncfEh&{Cn_]fO+H>|+_]8=RkH^-Y>rW&QeP2{^[A`T$","J]vix&mz8[5LonY^m~UeP#^(vX&D8O6e1&s7_u70I#c^#U6.AtfE=t-Q9]xe}.zB","Kc%J)g.B9w[5?XFv^qi(VlDt3^~)+gD!B740?QYk6ufmu7exC06_5b}U[hAb"],
  w 40 42 0 780002 780327 100 6767 ["o>lyyBY0yZGf1>^<:2[y2f7`07qx[uUI{H94r,#H/213~xFsb8U]F50E1)5dHz}c","Bd'7@OA,WS[EV((7$5gg@2h.J(^&OI+X2.iwundxnh!cnF?6)'Yb6g-&3*)4@Rwm","1f%|uCWQ!cX>@%%Th=86+/M)mpyo!.[6yuU#WKu$rAMd=d7}ttm/O0CWtMuj6A)y","V{L'9nsu)]4.)y{lADPWynLe>Lx|cr*HOlXE#}H59JOYGYN?8nW|`%joV)7`h@bo","d+/WvQ[gHh@v(!lSD5LR}FAs1=a-2.)4^OvGsVtHh(o)h8w}O*B_SJML7y-%4q<9","-T9H]iipS7wNTx%:mhj?5cs5!4W0;4U8ltu[y7~&]{#RvUELAL>&e}x~*r}-v|1f","~'1^=!l[vnTZav|LH>Am7^9Y=0;<hd=v"],
  w 40 42 100 780328 780896 67 3893 ["dc?|MDBmiO01HE&(zDyC5<qh'6*IK-cM${fJ@+<&bS6{ePZe{RWp)''{jqyh9w=t","I'N!8Q,Wy]9g4'vC!$R^8o[yYkSjg?stns{qi)]ONZr|+w]2K'l%sMjsDyNQR%Td","V6.Dnrs`=J%=JwSo^Fe!Y`Wf&?'zH;wiA]A;}6ti.'fq3;0H_fGQ?/,(C+4&F(^{","l6P*]b)[&8%Pkxtd@c2!XBH9$zcpq,DoF,Nbhb_O<d^7@^+}LP75x%L3bgRt;,!-","[%]VusD(J0A.*.g0s5v}@'D)B8ybYvdHixF*fMPE]"],
  w 40 41 0 790001 790329 100 6522 ["dequ%,$dy/6v4=P6[{Guv.Hx5V[KWcNU`yVYu6mnfMf*7=q99m;sN{>PlG6p!II6","6'LT`Lc=KDSLR#!grm(@vRU~FG*+Z~ut{VPOR|RxIyw7R4s^[`e26#!EN!K_u:5g","H@A'W4Mp$unB}v!k-B{}EcQeWjcA}or7iSw*q6+%A,PKdwIk_cX@%a:EtP)64gU;","kE;]A|{H~-kNW{)2gj/!Qn(yO`P:'6Oh/|,)/jWjwz9ZWR6z_Y'jG{LN4hA0~)mr","5r>HSo.,`oZvQMWrMl<jFgz{}AMP`u0B'C,hvz=,Bp`-<yG,b~'xk^JFO1W]q@%=","YnHIwCu9YfNv[2h&44_b{:hrM3px##rHo=t=:Y]:/M6:pv3_)XTQt[Gr!MSr4E])",",^rN/x|y8U`el+j?vN,99<2o/=g$xMZqG#lA$`j$=:n85X!"]]

private def r40_9 : List (Chunk 40) := [
  w 40 41 100 790330 790833 60 3388 ["!?7.]p*F!f>FEx)pU'1R7eoCn=6c&)=YcIHA1>?n&p$3R5~29+Rz(S&.7Gj95nrS","Grh(GiiWZH_mb:~q&NNUn-Gj0-7yb!cnJ*e;QETx%&J|60Htgo8nXIg_F]^l4<6]","AqN?[c>#}vE`eI#W<+kmn$&cvx3gp:,sr([^uvI7Vj-s5{jCsG.}?T6Bv-Ai1wM2","kxC;w-m0!axkdW!f%%A4R:m!4;cubjloMD_oD7O@C&Nw6R)0j31.H`d4Kes!2Bja","qSz;X`#t0"],
  w 40 40 0 800000 800330 100 6281 ["1&Y'rZkqst/$|l`fS6{Y)Q^W*;]K^1NEqlUczZex9+Flwg?wc?rE:[T[dZHk>Kec",";o[mD?Evh34zhE+N%4XW}W&6(QkS'&&2:b;-7Rd)(eS4*5PX/=)R1p^x^w>ZBVPn","PdL~X?-,94X!,+nDv|]tZ9,^f'9AyhZuR,p;d!)m*gK;!mos(!&znnYLAv',~M<W","lkJp5o_dU&Tdh)v/4Xdd.uy&|Q/oh%*QNBhVk8exeYN!tS'&Vl2a/-}_:(3L$W!4","0w%xj0yRi'RUqBE9nlGOxXms*w={$~X=6@[(|d,Z|.F$@ZViis%TC2jB:2e(<}nO","1.h1cX[c4b/C69VqwOi|oemXyfp4i(Q5ylTDRhIu4V~,L.C@/[+g3&(U060'u(b<",",wIHGUOtpQ0$SjqB/W_kx1->hLPa-$'%Zh)hN:>zJ}0BY44MQ#S"],
  w 40 40 100 800331 800832 54 2968 [">Nq(/-jQ2tVS9}{7g$LH_.jPgN42Y3vCHHQkM72F=4SHa~B3SrR@T%h`ct~N/+:6","*bD&<aYCM~DlNqVG#a^+VBk88'Y}O|JnO4t5Tj/nFjfmU=PV!Tp+Xyng>.-ITLo,","{dTUv'Neu&godhuVQk|4X:j6T2?n#OGY%~XJ~W.2?bkgmvyc+nL;jkI+3+Oth;K[","/)fptEOmFKY)R%8{vS]7euENh-i%?{zLtM;C8WHbYI>:V/-"],
  w 40 39 0 810000 810384 100 6004 ["OSJha{`N=]yvF/BMIwbmlOB*,7qYjjC-dG[A>.uoF.!W#eI),eOSeK9MXZDt@%7x",">i:,_Qs}nC>joQ`>w/)OI4^r*fWc2T;lg0:(#PJpn3/'2qcD4{lf_O|In~fJ%LEG","e%;IQ)67dr/HTmCP&$sUb`Uu(82V&:tOuE/E+.I%m-@TIGoBIt&.<`P5h.x6;pY<","48B[B$$yelo-|n&;k|24>oyuj>SR.{oPE&Qx:[]X.b:e[`EOSzdv-8#}Zzf/3Yk1","E'aRbr<))wAV!qWE~32Slwc_gMxw|:qu0]=KrDQ,I>BEA[@'ay2-=?w0Zo+|f,DK","tGVE!E4BkdMIRPRVQW5v1.Ub|Mu?LK<n?~f@xmgHl+.pX]lbw`o[tNef3Z$u+tZa","k<zSnaw`z7:(Eg1)m!pQc?8n5$l.5DKm^L.huHt%@u92/b9<19I}TeUz_@EOz^y}",";`O2w"]]

private def r40_10 : List (Chunk 40) := [
  w 40 39 100 810385 810832 47 2519 ["`g3B=R.JK>cp9&9Tf`&L>`,WU6AQ+5C/d<Ud#DC]#U!A!x-N0F}*oY_T}@8m;~F_","%RnL,e]$gqALX%=6vwDFZyW<bv%&cY+}//6}Qv,_b$2IMhS@w_'WXO6J7C/Q,?>$","w=UgzfPZ2O|1MX:a@fP(41MG&VT=)POc5i~+.sx6+0/j9EI4,hr$':EO?8aayn>~","45;DgQ6fy8?/*tM36"],
  w 40 38 0 820000 820387 100 5731 ["vA;wo*GSsX9Sj&S{w|(g7[9q5QkQ&vZRq*ggRf&w#R52{Umc6SvNzqLSq+OsC{23","C9(}zK`J5lT+sS,;/{A,FI5xsq>=!>DrunDEbD~?zA%r4F']M<`HG<Sa:G]'seCT","G-*F9.MR%h!Tx4P$Oml7e9B7~c)k|jje^,Q_cA&<%b5@|{[_u$(V4jxAmBSL0|g|","Zz<YTV0Qhiy8LimK#ACch4pxpb`hRxIB^F4c%G&]$dBNacf$(zYnxArCkEa6T3@^",",s6F~,)>kPgRK%>ppEBd6i8cG4qR9CS7>evXc.3cYKuInP6<1+X]'?Kt39cBXu$&","8LF~n*cBu&S?b8FJa3+)QvUxuzlH62tf&3^]7Lt'`t#|i#]#Xq[<de)E`$}b1o)P","0sHH~1+/`j}~)DNalP9?CpVinOt5]}WQrzHg^+VK5HUd<=)AG=kYH*;n]~R5}U=z","))G>Z)vz_Fo8OFrF%uCd"],
  w 40 38 100 820388 820769 40 2095 [")Zf~+%_c}Uss/hkAqeB3>JWcw,+|3Mi+g0Bq7InmC.r6X4oa0HCE8oHkG~1Q*Mjt","J4Vz~,P4xxa^+LrgsM##;o'rz%^-$=J#njCnuq?%f.>2k2T{l@_%?NQUW,Ld$Nte",")6t`YF.tZ<_R2Q(KlDRZ+hnJVsc_GtlJ2*@gn:6O68<WQ]o4"],
  w 40 37 0 830000 830390 100 5470 ["_mTx{S{[n|@FOS~Dml'2U%V*jxF$%*`sqLr^fn3p&X%YZxX'/YE8$%Fn99=A]t@[","36T0g-^:5vG0+4!9D9QD<i~GC7e:`UAYJRrZapm!~2{_a(ZVwG4h#Z?0TqXA,mGZ","Q+~>M*vJ>D9M]Vyh1J_o5o:k`<9[xJ_`D.U8URVb}=!*;rg;0nfQqmEub%t?kEs|","2WwQ.>;$?yYG1.2`MVv2HF`#Owu^cYO+V?P?f04/T@r:`fFsi@-+/osGV]FG7F6k","De`t}5A,l;w1(N25/K$Q.Q9fbeWkqHr|m`Qb?(}%2.~qWl1UOJ>Uc!ci$w&W{Ln|","3XVd}?Z)>k!w%<^?Jcb*-{01]1hUBG^-A*Leg'@*>#HgRWJCMZh~IL3U1}z*`l,o","Eh7]^T<04.GzTqm$VcmG=-qb`=a:v6%>k_wi7AQk?0TadXZ2/XBM|y;[LsJ-UYWt","#73//0?Cgz`4D<1iGx_{MB{Ey'SdcZ9$z?"]]

private def r40_11 : List (Chunk 40) := [
  w 40 37 100 830391 830768 33 1697 ["M<.<!pBs9hcUCFwGlO0&N{Q_scW5j6f`)-'|?*W#b'pPV+/em!H9J]r*7U<7?I%c","6l>&e7W|zG|n=H[wB1L;r2TMq](sxI~LRH;0HoWd0P:Y9j'o8o`uTi!:Z63DZ$y}",")WvOF9fU%n[Gg.!"],
  w 40 36 0 840000 840393 100 5227 ["pWqHH!f9~BFA_P_+sfe@&@pmb#i?ltqMN+]ooSj}7y*.4,tO0Ud:hST~*ZgE0^{d","aUlYL<TR#P/eX$D.lg9[?~gL55n=&bpC;kE&j^]'3A}Y{{'X)QG!)dtU`Cxw@|?o","-{{o2LJ|[tHdZpH$W0?&r`lY<9J}:h,,0YvLPHF>/KI!fGAl{>U3kOaJy<Mxe`t_","n(tki@Fl.F/I[d8=?E`mc<('Q#V+/(XX[aPTT=u0}Ei;%%/dwZvx:&P_D?1#9zm~","0!]1K57,6G4NZPpz0:@1.((J')_A<$U_H[L3.]2GGdA0#qltPI)r7!f7[m@e?@47","GG>A?YM&DTWx}{CHcku.P6tW*8x5Mj#8nzOZV1pUrJ2Z|#la%f2OA:kSyxrrFbpl","c!l]w:QLa9f!#!,'vxKxi22Rwcl2LR+j}g&Z3RM2E~NVVtvFeAI[QdbF9H}`~J{^","OZ<)Ycx$1S_BXETgt}H]|9Rxqw~.-XpPI!QE8f$Cn'8O5d,l"],
  w 40 36 100 840448 840768 27 1365 ["kcF/pH354GmGoBi-x)P|AL<I|rKjnQmKx]>qwMK^ZY9jv%w[^1v;aK]_&NEPnfI1","SedSFVHjg,g@vM,^!fY{E&$x//4(K61S-d62#S;0n.MA.:ifBEg"],
  w 40 35 0 850000 850451 100 5005 ["`&ndw]GblGRtE&hW=#2Dl*5#>2i8vWAQW|xIekW'<<k`v#h@-Iyh:L2p(C}XJd&3","lwvj{uwk`B$<bJE)]Dmb9)]q&73/BQa3Rk{ZpaT'es_o_l'9)P=_l(.M_d^%)lEr","-`j,;Co%HBL';sLNIpOj}k*^P)>B0'L8QFVx4ma0-U)pyACdfT;_so-$/0U8+n_Z","<>3`#|[[js[idxXmsOnEdrxCmB}~ZU[V;n'8Xu=_i+83&{c7f1aXj6`2%:n.n:Fq","Am0(sPzm=rq+SWYuLf0qdXv:DBFaNp^$ohnc'p5b%+[{gc6yLGw.?!?ccwA1##$5","2tH`A:x/_}l[{Y]6iA(q=5y):7TU]4k%r@fNGQIUCu':M7#X,jB{*ihz|6qX96d;","x:Oj.Tw`O0Y~;o3V}kxe+29)omW=WQut$,-Mj`(JTXCi)e!&e=iXS`$r@}~YBl@o","76#=E^X#cvjom+O^-Jx6eTvdrbhn4:/.Q{OQ1`lS#~M6e9hV(3bC*iulZBO"]]

private def r40_12 : List (Chunk 40) := [
  w 40 35 100 850452 850705 20 993 ["V#x'CZ!kTy|MgN3fhn3a@;$4FLoFW*g^lsN;Q`aKtQMf{+glhu#XMB`WN:dQT.H>","}T6<2(p!{:cLCBmEtJ_W="],
  w 40 34 0 860000 860454 100 4797 ["ghOMG!>w3.e>=TjcjOuAfeLH<&jy*+>#pC>5!h!0]s)11.{>MKkYFYY7{|pca8A/","@tL|_p*$:vK-$p*0WfgJ':|PRu0Z=1~'5*Zp.mnHjTSf3$ds$gy%Yep)N2A-Nntg",".mjy9F${Hu4{),epPD?V.BWjtPV9W{9vd3$yL3Er$/!&RC4WMW<zHNg*:^^a>eXc","sdhk~(O4%Gqv&cl@EC/x+3e4}ZlA#fF!W-%w7C9^9LlV_BfGQ}g5!K'qI{1mb`&o","x'a%O>~C3T&dUj}@Y[6>v^f,U3)(W[CI(;g?NqGn#u](^LOW@oZ<,3zFL-?'0uRc","-?mxCL~=HxWXYo,-I;[_5?Wriy}igOB'@4?=AVhYM8ZyTcQWg=<G}3LFk'1r$b-u","ULo^M`J9S$G(lE*M9p;CzZLAs^j|Lx)dOIz~eJJ9'-KbX%xouNV<7=^EWzwQr}92","wLsfjxFWO>][w/sZx#s~S,~<mW?7TBa:)565q0<`Hd%b`wHmgu0;+&)S$6+a_.Cw","$O2"],
  w 40 34 100 860512 860704 14 685 payload14,
  w 40 33 0 870000 870515 100 4614 [",-?q:b.n)u+D1a?-?XAa:k}N{n5_X/<)ZwW-dM#-Uc`sCAFF]Q%c6xnR`O#=2|T+","V${(g2EVzro+qD.w+?Zed>o%:D&e!)sACtG7+5s@]K}}ZVAed%s.M-p+k5d+,5PI","I2Kygpatjs>}PlI0~2,O#SSbiOIc4iKX(!cU:1PkUHsw?^'BLHp#ik^=JkVY,~a#","$Iycovt}^3ks7+&^#_8;W:XI(%V$tPhEtlxLUh6o*D;@n%XZV2b48fNVSP?<-gDr","Mw3-l>c1<Eyd7@kZK)T5n]+_*HNkAMVfx}!&N{aP`z{Tg?wNNr*0W>h|@60+9`.=","Cys3Mz-X1Fu,=OBEIatF$VnJX+yEW5dalzeO8Z.dQJJD}lAl!XG`PDrd><2Z]Tw(","s[rhBgYYa2!.1Jy?4!BZ.vb=5R?gRs0^9y_Co+no[kyb6=npZrIo;M,GsI>Tm5s<","71(,FQf]:LW.=S)gP&_ciUlgu!^*RKqiB.f/~ZKfg(4X/L}(6@+]y|Zvs00;?'`T","6[w?_g|9=}>&WV3"]]

private def r40_13 : List (Chunk 40) := [
  w 40 33 100 870516 870704 8 387 payload4,
  w 40 32 0 880000 880578 100 4446 ["F^#R]mCk''+hDMz_4r6~;3Rw3o}wL.E?ZGCLf9nPeY^dw]i<gt$<PE1^c+P/fnTK","a#d|i{FM>98{LwNYU.Wu^ZOMQQO%UIcMH?9PVS/N93[f];[6qtR3s].)aS9KnRFy","+ov$x<slA2bo'M:FK{jcS#`*d7+c1R9a1mI5.l_s,Zxy!+T:-,AovA4]2e@U0-`3","N~#yEnbM84s(+yi@2].17e`AJ6EOE6:&1mwYo'iXdYg@k!;CM_g;{[Dpy/?[=]6<","=+J6*@z=&B=Jd0u~:f(q,M(2w/SjifIZte}N=foW;]zrVKJ2EucuWnJv`r^zW9q&","zaH>C]#6P:aDgEMuH(,Pucu|Ua!l>xYE.YvScRR7[:y*,+{/A}A6Rn1t}qzF[t;G","]&dG3>Na|Og_9>v.];~Kn*mFGoR[Pv3=J8&01c_]h4c~_}F~L/Pd:yr1Z>:FqETX","0`t5`<fRt<67x+35T3]0e.NDuH*YZnW[>;Qz[5RST<,3s'BSEzq#w}GAYK=pFb&g","#/,Zu0JTQ~e-cNq2h@U:n+"],
  w 40 32 100 880640 880641 2 96 ["#i2GG<Je"],
  w 40 31 0 890000 890640 96 4113 ["6YiLrLZD5PB|/L+7MTPQ,IF@nbT'iA0)eX,,a}CL-Px32+Ve`RE>;;G:BdY|wW,L","`PayLyGe9`|J&w:}{-'v)/^'|7s<!3GsoS7BQ5yI<n+S~'3TQ'#C,IuDbW#&~Sru","]81uXL}4m~1vtaxFI`bK.wiewbgBuET;n;?of~k`+G;G+k_ZS4$m0XY`*(;~9.]&","GT%.}rm<6kHE=hEOaiYhf:^ni~f}deV]P(UP=Q<%sfE'36O'TT9@x,DMxjM)-vA0",":J7Bhts7#LgY7,|/nCK1`<Luu<AN49M^1&f;9@$y_8+O[w';5f.ox~HQXsOI|<_?","nR;Fou`j,:GNvZ:4$yMoOp@bQH.CtJwFNSyBPlC?PB`-5L{gN=N0ay;D7K&2Bp@<","|Ds{)CmtO&z@cxtl@l%Q]f{r+U:C&FcS.6aR#p_LJ8z2ZFpM3FiGSoS8As-zTgkX","1*)}Msq>85HjhI#_]g@8%wj3d+XDoZe,ep;fpL|Kp5su9!xS(s.O4r?;F1t)N,wW","$o;U@dEEa^"]]

private def r40_14 : List (Chunk 40) := [
  w 40 30 0 900000 900640 91 3755 ["/;aerL}rwHUa<o_4iMpk/4Q`C&;;?yt9f:VeplaBI.q,?b*('N9'!M&WcKc<8H*u","o7a~V7s+iMD0T,Rcof@F,NC/BJ!pF8>Q`9ZtTan+;-k*<'cv%2gH##W,<S[6s>_u","z2o!UA!/ECK*?6MOXFTNc)Y$#^NGEcoo=zne{T^$uh)T64{9b$^OT-`tTVN},wV4","~[)~0,KnBV#6#*r<Zc*QKF.lQ}ArU;s{S~/98XyXo`-dqXJAK*,vxGxqdiClhtqj","702{O'y#4%F*]:u41CV_Rj-|589R(i?I8sz2[RkC0lals18T.ZT9c&(L+I69j+Lq","eR%Yw.DjXX`r?M9u$5?*bEcF6NS$Y|[jCS^q_#JaK~J@).qp,(WOl<$;~^JbkB_F","!W/`P~BfCIF>!ZJ9oo8UuJiPZ9Zpom^sjWJW<b|Z/?V;_,M}uEz^mK_+L`Vpjoz[","tPFrSVL-L:l|x7`VD%}?9pzQN(eHCe>9L!HZg8,jO#D@4M,>cH}?&Q^1"],
  w 40 29 0 910000 910577 85 3377 ["nF^xsoT!j-lFyXAA-E-2I^F2vV,xoNA#saNEkM.ZcU.B-11y+.*boo$3$PG;^$H,","J!8B,3%S,i~H*.=P=B:?P1?u~<w%R>BDgX=@z;V-(y6~.;#RL,zjNbR+*Yw[$VNy","B5SD5~Ad+~X`%@o$`_dEVsC<tH7b63]G`lwXVp}uE`$|R)f)r6faZa@i?Fi52HEx","W2`%0_oX8mZO6C:MU@cmuT'ul!fL`ECEHZic~mAzu.3;dLA[.rVNHmV~W'9*&Y<K","(^=RVX)Q#Ri(%*E<vQ85]cA&tpsgVPc{diT)2A+>]xrs,RUgG9DNgUNClAPQ|lIl","%odb9d453b1[{Fn^Yy8T1RETuzcY`Q3=F=yF3YL`5pgfPb1=m!`$W!L,$%?_pqDq",",zDpBRKkY1VDvNW^<j$tt*LN>WqID&:&!n+vOf6+o|3`fm5y|izpl.=A&&yz^@.1","()sf^'c7|P6HZis+u}^7[^IU.edhv+0wWa4}"],
  w 40 28 0 920000 920576 80 3060 ["#;hd(Jod'kH+1t0!t]=-@H^[U#^1[wR2M^q/%L8cA1RSx.Gz$^:D_aPrvoJZ!^0}","mJZ7dZZR`R`dRl|I5^^y?r`!^?0qsq*&(3G|sioM<Rp&2^,B3ZEluEl'#_>/7_Qq","~gIo$`/a,DLIw~a5,b/K'.rv]j.,,O&={eOl$YYEb|CUKNO_V)+BJ:h(iOvl:K,i","]}^20w|B1;$2Ff6mq_a34V,,5iMYlp:U#.JL*NDr*Dc2Jj-98cL`D:J2$?0EH7x_","6?ki'8,CXh{FW`/2?3qbzXDpy3x;zg#CmO*K3uj)eRhVD[m'Ab<+CA`/9S$p:@#R","8$>:eq=:xZjpD9ZAcUZ$Jj&ca!~%A$BA(_/FR_J6,6Mf+I0>)JpC1Ak]3Fiz<?t9","^#h<!}PpJ58NSo:+;kdbpd*VE!yJu~:[Q*v4Qb;K(ZR+E>pRSw!wT%(YO[Ww+Yj3","%*a'7"],
  w 40 27 0 930000 930576 75 2769 ["}4]E5*Y0[bn8rE41wlM4$C`CYE()?~zc)s)F{CqZ!4b+YN/~5X}q3_IAI7&d8hA@","3Ov8r0}r%0)o^'p6-txg(Pslr~T5t~(*zuxEL?;X<9%2Nru}M){vfPR4d/o0]x2<","vKkBfeM8/C9KRGJjO~4)AesRl`0jPbD0ShrQPwq->F6.BxuDA$mMLYMCyAh{[-|~","quhgs#VO%#o3b-gV3]G!h3xT!lrKtphsgSW>ko`tRlgJA0a'1qVr#KvBuk,2OGlH","1e,-)z+,tDa.O|7nGzy&KUBkavD6BP]mu=Q,uQ;4LMrPbEf+-k$c]h:1M$p?Us2H","w0[c^Wu`LEFQ'iDH_MEJ8|&Z&.7`o,G0gJ'xPx!R,h~`*l?%dX-i={M&|#!PjIS>","$DluO3=LUh^;h2ri&Yi+GtJlLw&_{U%EisoEe]]DcH<u/l"]]

private def r40_15 : List (Chunk 40) := [
  w 40 26 0 940000 940513 70 2487 ["m&Q[B(Se=s+q!dR;KsTj,d.gvxEF9fMiq/q_o;<dOz=Lgu=*Im@Ry+%-*0*OF1!D","pWsznp-Nkp-{(oiiL_*W#7F$Dib|>bw'@cD#G{07_H?F{~qt&'#|;tIu6S2uzHSG","'F0.kqpK;Tb'h@O#i)tze.[OKq)uUY+$BU&@F$UM/PYtKW#1m:9PFNqA4D>j4X$2","WhPDZ/jlq~<42~&}yd|*(~mK=!y8lYP(1}&.iw$2C/d5?u4*+aWx8*G}L1OvU/dD","Y5G_knc}K)={Zm&#XV$<r/zOzTdoLeW'8G5Etmz-m]u)n$T^0V<W7k1%#+&EcG.c","iYz<vT~#e&z!&O]f7KuIbD7N+@c(Cj(?6^jckHO$veB=/:H.B$)2%4__no4!sX37","chSaOx[T--D;arHowgR"],
  w 40 25 0 950000 950512 65 2224 ["GdvnU@I(1EIl}yi2R7b+F/gpo[)KZuFQ^nT6):h<VR0F-Ff=qUyYF=J$O^j!yrTF","9`BPtW/.#PJ1qbAELVil-cW@iL`MLY9)woX9!s{Dcmh8:sWvI44Gm,xL;8p%R;4_","AOh'e?SDOqbe{o&'~f8>`.NzdLbCD{jWKm/W+4G0uwTsUovq12yT,%4+.N#pWI:I","i|Zs#R?B~h#T|)U#F)QDsX?o#a>]KkM(z5^LuX4Oh|_?(Uq5Zj'zZOtzbOx.D[A$","EA:IZ_lG}TE,7]6+uS[QJn@v>uf4n(&yq&52Jr-`,=hZShirNS*FnyBbl73f(0y,","/}jMdFI(;QY.{m5RME`BFRW&e5k}pR^CVB+RmsN)<7g>E#ES-=C1u-Hge:vJ{3"],
  w 40 24 0 960000 960512 61 2011 ["lO9TkEsa1INci~KSX1lL!>]v5E+WCFefbHMY'@zjQ&kshX{=l_1j<Y'`^#DC;72^","v7GqD-HzM)4_TcK9opKKp{;p/>[D!~@S0A-|x8r?P0?wWdhoC5u']SvF1I;}v[m|","gZ.8`}A^tI?8Km~[%LLZ-J{.jsAESpJdbTSoicx[E-[L[r$|$$X)Ss45F$-blHy@","|N*u/~XIx[K@dw19QP(=w)E@y0j_Fp0!ocfdDAEtE+307Dl^$G#_}5/,Hm,IQ}5c","*oW9gRez>--Hm~?>BcqK>CiLC,/jIKXM)U,J!hokjRbPU!i5xHt#|xQ0frN%SLCr","4i/N'`0M)B])>7,j<xWk6GsnQtxSZ?GF"],
  w 40 23 0 970000 970449 56 1775 ["JlGmG/@Pfw<W_2WN:elY}~$H/VtSL>Kc!AYWS>`r/I:~!|$}V1'q,o)dhW4ToQ#c","YCh'Ec?V5FiiWQ:dfZY!@.c+W[^+gGJ>jgUGl-;`=n%yq.`;#g6].8e>VO&m}xqx","P#C.m8s',@Y+eqBwwu2QkP/A'e$mbd6N~U[S*{W_byy&3T|w&4B9qgI00FY+kG*B","T13j(bhDV%9(k+-ilWH*nC^AG<ObG8{}CE0wA?z[+9d{T1{|M&;KDzKdcU3`AFc-","B*enH<;RUxhSU1cnNLmD[jBYG<76aA;h1=k1IL~M*`0YPUbD!1<ug#,-rtEhuJdD",":=7JWiNn]L9[6"]]

private def r40_16 : List (Chunk 40) := [
  w 40 22 0 980000 980448 52 1583 ["_8En06#TO+}rL`IF-/HoXFv4Z'd?[+u{:WXCv9:9[t6/:{!=<m{gt<dz0hC$w!QK","|sOYX-K6;?r?>D*1*qGa{C0zDE{/oQN@]bJ:q8o-!5<s?zo~}6x%k,+cTUc?'~RE","ZmkTYs&Y</g~ye)4xqH&6C`[8|vb$OflJ_V`!&+i(*K$/y:`wY'|QXT2nB;`{r?{","<1!>.rp~n29iL/IP3PY8e*C9sq&DUbDYC|Oz|y!:CdTjaI-3+7OYea<un~%~vG~P","#{v*5C`:CA5`Xy$_{%Oh,L2&?9ed_v0:|m$6H6r8E=bWseZO%Dy@QTOt<"],
  w 40 21 0 990000 990448 48 1407 [")pzhK|t4n`VtU<qCfity)q4r^rQ3_3]8__GN[d~]hRgJE1*oDn<I),L=t2?fH+dB",",tAc!,9vz=aULeU[Kj+bbodQt;IjRo|@uj9^LgOKOZOGay;)]Kjalva6XY.dtCjH","qb5m.YY/>yS(iQ{hyXj8L2GF$[[380XbjTjkG=e;bSVTJMn'.E1tXQ)&yZ%j1B<;","MMJ@E72$9d<e9;Xu~PD~HKecmx$S=T:GYfmG,~wV<C_l(}9>p4]Ah]OQ{Q>C]Vzy","#5svm_,$.KaHL/y8xpwp9aD|+IxE`.;MUOgn$J/"],
  w 40 20 0 1000000 1000385 44 1236 ["1q!o?<_Q}jTjuE4%ZnV9hc.#r%c.$asL;Uh}cc7ZjUj8>s(s_EGsV&S<9_b/y<N?","SBRW,zTCt]Jq$j/`|,]voG1Z;nepDR=A}#pzSEb4+)*b@Gcb[P@lcg,-s[Hr+HSk","GIz/Jq1?K'eZxm6E/P(Ad:BTLXF{A(D&@Xqo;]0.o,@1WaToQCO.GZ(*l]0,@#Hw","3.l^iI7B3)v]yX}hP'$O&;<[sc%9l^]yp:[AUZpN`cB|BF!ckHGDZArHAB^k=.r%","6#}ZlIezad#kWK?qgzpq%0J_"],
  w 40 19 0 1010000 1010384 40 1078 ["D/PKFI3ciq&*SYU,W>ax,T~Ahbmn%vF~4-<S.KKk,#>G.xtfgiu@Z@xnrU+<zK=*","QsWZ_7p0e:d#+%A(L7Cu]eGM%~LqNC2aH7<>jLI$~*P;P@nh5=#!I6-%>1dsh<+&","WZ:_.O%iVD{W8U9q}NPC`%JHbNDPdL=2`'+P6p^|sy^4}aw0:lkf<@o'A31~c'5z","usw2{srji/*r~Zvc96.&22;;4dxvRH+`|L$`t0IotRhe'i@6H96'!^|H@!ECN9ff","(3X4T$GX"]]

private def r40_17 : List (Chunk 40) := [
  w 40 18 0 1020000 1020384 37 957 [")AklB.;ha*=4l]VR:1]o7Xa$oGg,mIc.@G~DM`4uycE(=K6y8cw6+TQpQ`ML:SsV","k;TB7gz)7#Cj@R@&XLB9[|3rBS]F*Z*Li'/PW#((:+yw*[cHGG>,FuG^ML,NEuM<","7tu+L<9[w_kA5YD(cmSZ*+[+tGM'cBbj6?Wb8V7p|V]YX9hH++{JF1AT@KaE`5@2","d*32EU|P~3,syIdzgwBNG@Jf*P6VV'{YEX?.({^qr-d14r"],
  w 40 17 0 1030000 1030321 33 816 ["F^%J/_a<A.<.rmEV5z;yKvz<AtA:_8wQ350H`!-P@8rKE].JKh7;0pX]n0fo^hip","K,'TPR-s2E=P[tsb&v,]3@>0EArFGx06U(t,d&SDcn5mP4&%]UKKtr~|d@]C>#z0",")wpH3{lqPFm?yL&=Rf#L%o-4:'Ph~V}dQXW;gHLb0d1}To*1XJ=o}>HYP4a#zz0s","4Z!f/pSc>.AJf=`7Yy,qeQq3N7V(V"],
  w 40 16 0 1040000 1040320 30 708 ["qX$_by)Jdk(yZOokpk[(e~y='%sJhd]>nKlI2C+cEvM@B=}?'Ucco60R9=6-Q9^C","@PV^z}i1Yy$G9M9'_T?D$UP&+z8#4c<QPVT)Jh%;9Yta7%O(1QgSY$}8j=CmhJ?/",":09*-|oAv@fx}X0A~y#u-jTaH,3e>[Ee{90z+OYMDm:$y!IagzgAPls0fycJ8cM+","&.USBeme%-6%"],
  w 40 15 0 1050000 1050320 27 609 ["!]fI2ws#tt_AtUYemv8-=G,C63Ft<-lkt-B]Tsg9#P)/q8|^}Yi4fO_4El(@cjl{","Hj4H;<UX$`DribZ,S,T>_a/8Gf8eQ,BCa`w4IeUh3!^sNbuP)&l?=pAHU[Yh-I?|","#lH(T%n&*(@1+erF+tm*GQC=GH_l2+4d@wEZ%GpBD,_nvL9Xb(p]F^PO"]]

private def r40_18 : List (Chunk 40) := [
  w 40 14 0 1060000 1060257 24 513 ["b=?b,{&'?HJu<D@]qY%gydtrNINF}<G#8]/^NUx,d9lB_0Q6TYT)ZFQd'VT]W?zS",")O?9MatR?/BTRnP0S?/j]u1.WwYnOFHNJ4m8)ry;sD?OJ[YG6_u&k<nGQ'Go`vpD","&?lA-w0nH'{o7#mtAtL_g,p1I307;g)//Z"],
  w 40 13 0 1070000 1070256 21 426 ["E>g:4.yn`3t)Y,[z03<H2-%).k>aBld`WExRJu$k4|Vp]cdv39JKW8r&}K>[b&)#","t)+42hhF2OyNiEJ#Ja%BMZ|r;8VH2v,B,cwd@eM1<)#l`rC,Bq6RVm!Z_;SDS({;","upoPstk_f!RLdn}>ry^/"],
  w 40 12 0 1080000 1080256 19 365 ["2KfdI={&]PEXrd:38Za|B]i};yT>*:D`U}/2=S(TE;'G?X11}H[[jc,@4TQa@&q^","&Ec|sBd9S;<{~}0&]2m2F._yrXZe`{/p?7HLx:6sJd*B&*q}Z'9wu&F~M%Wu>"],
  w 40 11 0 1090000 1090193 16 289 ["I'?!kU.y4AF^~*ew.'_`I_~9a&}$=rMhz*)mn8L/?`qS%H:Di%/x,q#W[dJ|HSNG","#i6-3#?D'I1Va$[U(HAHFMeCxw6EUuWsKdLu*uF;mgqN4#_"]]

private def r40_19 : List (Chunk 40) := [
  w 40 10 0 1100000 1100192 14 237 ["TCg;;3b&%KL61+YclY;0TCyynw_Lqs~c0ad3{~#kB8@6AujXQ6FSaR&i-Kla4Au>",".T7xm1mAp0{>vyb+.Xr3F1A(drc`EN"],
  w 40 9 0 1110000 1110192 12 191 ["S^HRZE=|iofP|yas*%NLqGL2htmxHc?6&R1=XR)TG|#+Xh3G=U8;**-~%C?bZ(E2","#FJ<}DPZ0![59~>x!"],
  w 40 8 0 1120000 1120129 10 147 [",jNERJKfi;Fi%_TTS+ey2AUl?7+vlDng6d[9c5ox$w.`ew<i~,*qEOeTlD87m8>6"],
  w 40 7 0 1130000 1130128 8 109 ["2nth1sc)>@9?AsZO?6moM{?V550JLUELh.qGp!);369BkRe3,iMHQ#["]]

private def r40_20 : List (Chunk 40) := [
  w 40 6 0 1140000 1140128 7 88 ["&L$KHCYP~*3yMC$X5(94YP[YVNQb0w>.`.j9~7%[t9"],
  w 40 5 0 1150000 1150065 5 57 ["#WnoCPT8fT:<hhDg}BC(3{_2uW9A&SYe?"],
  w 40 4 0 1160000 1160064 4 41 ["&zE8s~C%Q0NL5ToaE[-M8u+J"],
  w 40 3 0 1170000 1170064 3 28 [")`B|S?>_)/-urPzh.F"]]

private def r40_21 : List (Chunk 40) := [
  w 40 2 0 1180000 1180001 2 16 ["/*P9~(B?6%"],
  w 40 1 0 1190000 1190000 1 7 ["<^S/io"],
  w 40 0 0 1200000 1200000 1 6 ["7{um"]]
private def chunks40:List (Chunk 40):=r40_0 ++ r40_1 ++ r40_2 ++ r40_3 ++ r40_4 ++ r40_5 ++ r40_6 ++ r40_7 ++ r40_8 ++ r40_9 ++ r40_10 ++ r40_11 ++ r40_12 ++ r40_13 ++ r40_14 ++ r40_15 ++ r40_16 ++ r40_17 ++ r40_18 ++ r40_19 ++ r40_20 ++ r40_21
def rows40:=rowsFrom chunks40

theorem good40 : ∀ r ∈ rows40,good 40 r=true:=rowsFrom_good chunks40

theorem sorted40 : rows40.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks40 0 (by decide +kernel)).1

theorem mass40 (i : Fin 57) :
    bandCount 40 (i.val:ℤ) 56 14≤(rows40.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks40).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 40 (j:ℤ) 56 14≤mass j chunks40))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total40 : (rows40.map (price 40)).sum = 329716 :=
  (total_eq chunks40).trans (by decide +kernel)



private def r41_0 : List (Chunk 41) := [
  w 41 56 0 670015 670396 100 10697 [],
  w 41 56 100 670397 670838 100 9649 [],
  w 41 56 200 670839 670903 10 851 [],
  w 41 55 0 680014 680392 100 9965 ["|Ya|xgx[ZZ8>Ly1U{+?=4cdNZ5J>6u5{/,2G.zK;>>OVKFlaCjEnM+K7Zg+bM3GN","TDS}`P/_7UP|5uQ^7%nWRj?.%{+}8)|L)s-xCf=JdL}OA^mUF|S!+!/l+#,UI2G@","+h5%kD8aYAS@WHs1wH[ROpv![T**eHoU"]]

private def r41_1 : List (Chunk 41) := [
  w 41 55 100 680393 680837 100 9013 ["Z|]Tg>95h&VnI{E>64aelF(!z/L1imm;HTZ[]H@noPj>Rrrz[VB*1eJeUAkibqR|","f>N-7v2UU<AoAxX9llOzAHILGPX:=77v2Njo+#R:|AYP(UUj`1-I<<N5[G6Ho7`=","S5(q?yj73p9C#@!osqA@I7i^hbV'<Ii1ikw-iBG"],
  w 41 55 200 680838 680902 10 823 ["%at_lBE6UTN1;1y`O"],
  w 41 54 0 690013 690388 100 9422 ["0?r.[aUd~sF;CEY*IOBSF6c*JP;.=A#%Bp<6v#2$l|P8B7Zr:,Y=@W3/j#N5vdp.","d`7$zm'2KuZ'NG#aV<sx'CF66uCuADIanuhWktXfQm*bn6MB(8$O(EC`Tv3.E?g9","&V(z2>qvW`:9!pNq~v9v0T,OuW+m!*_Bv|k2'4_RJ62kg[<"],
  w 41 54 100 690389 690836 100 8529 ["oo?9qh-TD}O#wyoES$.u':DEz'<V5c-wD?zNBomx=z*zhb+J_4HK[k45b9.!ID$C","RWq].XNEh]~2,{V@3&K`BLf+_^t9I?@o!F@X^@0KXOGkpmPXq!Ji~$[sgLt?)?A<","$(b69M4SwbdmjjyTNR=68jMgv48,)1$jAp%I]hEYEKZ,[HxT9<r7gg3xSn-W8Np"]]

private def r41_2 : List (Chunk 41) := [
  w 41 54 200 690837 690902 10 798 ["#K?1fzr`*teErf4H+24g,"],
  w 41 53 0 700012 700384 100 9038 ["w25).-6y+~v<W2NNHs3rY]a~SyAGo1=@Oy+-uRM={`)%0Dk@m?^6{<>VZ~k2>Yho","]cs}rgmAoa%SiOB/MwIT8gP:el2GV?&i0uOJ<kOqnGiA}&8GF@G9y+i4|G:W8^6M","kfQN]gOX*^FcKm?NjG#].4tTlsozbZq,['0>^LH0H|Lh='#eASXB45p`v&jLxe@B","9gfnC7={"],
  w 41 53 100 700385 700836 100 8213 ["Q&D|p.EF#y5'+e+ur9)x]wqe0=H55)BRw&VB_3zg17AmX]Oc]=Yf0R#fSTRRd{R3","Ox..rV|&HQg+k|/+L*aB/>9b'/=j+9<HzeP>gPbwsf<B2f_m9vEm)Tl'*[o0rE{$","GO0HstnqHpV`.qi)'M[gyu&B>,]2?SB~.stYK)S`E::MQR,v{dF&QVcPV3qFM>#$","#7DaZ~$G&VFcSoE[(AI*cg4pY}tlMYS"],
  w 41 53 200 700837 700901 9 697 ["=XU&$5^>1Sa$4X>unl051"]]

private def r41_3 : List (Chunk 41) := [
  w 41 52 0 710011 710336 100 8790 ["QKrvBTYaYVRA1|kE8ktm5J0Qmv^H~=~V=H)^9de$D6fil}&9L'US]`=9&F7!WlIV","KMJx,%*Hcf.pUK;^F#Yi./G8zF6%YI_n*v>1Ko<Llgk&2ucGWoE7J`HVKOac>_mt","$zDmd|.cDU',~8;aPm[2@2k7S^kQ?S1DDWfgfEfc$&(p'A,([~p1^8}Arwd+7eye","+Qwupn2zIvHA]^|6/X@8*=W@gS+KJPVGI"],
  w 41 52 100 710337 710836 100 7907 ["K*EEg7)ej,[64i)ppE!G>TIiu'6=vUhei<!;{bP^4T*YU{Zk~D[LR:nvfY2KP-.T","Pw/+o6@'iT10(V%{XJwQ}wuUk!eLdie~<zF8uXzkL'G&ZDo)/U4)POT;|IF$Y!Q$","Nj.09bV8sn&wUPXRSh0/mWPq91^gFIm-!ycz][k_!Aa^l7r<%Z))&l~}GuQB%J0_",":0`O&ho:{sZ?!ZCs|=olecHU&*RdS@Z5UEPMp!2FEE{Z3?QCg{E2W7+O~tR|V"],
  w 41 52 200 710837 710901 8 602 ["#OJE_N1s)FY(GG|Pa>L"],
  w 41 51 0 720010 720333 100 8608 ["x0ab_e)(=Gv@UQ;HM]{L+3+f$qCd)&D+D!1L4U3i.$O^eaD3p4+ec-lgt&+m;Yfg","Ez[cK+{lv^`x5c[N}3J,n2PkmwR_?,>GWU1F[k{nf_^agEKC'b-Ss,g=yi945at{","|#1yEcZN;4.bc3Bun}44t,FJ&RMT4{.SCq:.x(6Ah?D!2XUFxL_Hhx}rJX06YG;g","-Fk2UeEs$N5?;U4<0iIDLJkM<Lo(}n.lso$Pr+iK;IdUV)J;LQWOUY"]]

private def r41_4 : List (Chunk 41) := [
  w 41 51 100 720334 720837 100 7593 ["Qf2rb{t/7p3m.3@%Rf.;RK{Lj`-p@fWemMdN)Y|jBBJWPc/n{!@6ZZ0ww@#,:LZ~","eYAGyN!*1GhN!#A7d=,#[J$!8qV*3+oSjg#=Zph?%(eoWncC#Y=$h`T.{9Is#9n/","m^*PlL`Z>.`@yKEs9T{f:bJS>c_f'Xwhk}A>],OqKjM@I{DGYH-$M2=h^GNT9I;`","VF_%iFeSCI6iw'a%BE?N,g7,o0qi%`QH(6z?6Z>T+NN6~&UJ%mP_Ol=j_QS@}KI[","#0-w=ky7[!dMZR*g/?2V[$rv)]Tth6BH"],
  w 41 51 200 720838 720900 6 440 ["$h47u[Dzk0qJ~q"],
  w 41 50 0 730009 730330 100 8393 ["=$H~I@U+r+L?AR'4.f4Lv'<&kK;+oI(dP+N<M'A1M6|7HNHQIMo|E9;wi2JTS^vg","?8$$Q'*'$+_>4W=,kJPVG,VSxWV|bCWE0C[csizWEmt}D=MQ7,EGwx34]4[v;l!{","wyLr{?u[G7&fJYCvW|8Q{3?tuelCu}=r,9mU-fdfvO)fLnpaWw@K#eZp.q~.YJWU","zipS:0TET1*h!_QTm]9~I?z.-nvc/@KO3Rh6F-[8.q%};HeD1!rwK4&,V7kQq3gS","+&#R5DYLsoE"],
  w 41 50 100 730331 730896 100 7313 ["Xa?a(}OaQ)I+}ii~pl;p3g~^8q`QY5pVYGqRvk=b4Yp&g?J-Ru,v+9q_vk4u,Q*n","q':n{WNjDhTS6d50(._oq`$@7JCO]j#!r.twkuF#0)>uT!kFoN^9rm:8m2iO1m8q","1O2Ftk=%Fh7e0EDRc;-VJ(g,|#mMGc}v1x!D:Ge[WAg<-$U10s6,%IOd7f^h!#c#","Vu,vlVm7jx2_PEK}.eIp2PH-4Iuy!33ORqALBZ}K4rc=po>87@[n})LG/b?tX,jZ","FFSzgkf]#aE-&Nwd!msND>[0Q6azF--ikvFpG<ccHhTnE/)Lr6|%~,p1T<1kr"]]

private def r41_5 : List (Chunk 41) := [
  w 41 50 200 730897 730900 4 286 ["wCg*#>,aS"],
  w 41 49 0 740008 740328 100 8207 ["-qDWQ)?57MDk?q1~>>!Q1:D#[_EzM?EO!je;,eBq6.@J;DK][}Aoh_odEnB/pZ0c","fg_?>5kPRlBF`/dj'Em6:0]D'*zg1W<Qy65_Yb&5`7NC|qn=Kiu#~gZ>o/_v>F=&",".gUMX)AphEwX.?GrL'tPP/x8oV[{7>4KC04Aw@1[-=z^--~;;m5&V<:PM*l#]Zog","fhD(O9!bR@p}_o~<HfbI:EF(|T$(W1}aAo)/=bhg>FNmj1f-O#+NU)A6LP*1I{|-","KXaDo>i@_q9Vj6XxR]~!DG}2s'jGC]Vq$C"],
  w 41 49 100 740329 740898 100 7060 ["qvihTSf+aq4k}%I<1>?e2{-df34PM!x5*9m^b;3@@CawC4_4C4@JA97T*uN<2C6~","<jazs4FkGYw<b>Gz}fGl/<h3YQhXp}%d@N*_,B*t!cmmPe`[JlzW*ykzOl5=p.!6","h'>lS8zyQ3*S_fgAjJazHfIle)>_*QRR[5k@!32tm4BN1!Nyvde4z^D~?+#$']9=","{KEI9`#%ge'wHPIWM5H?P@p0X/*OKQ1phGRZ_?RZf>SDLfDn8>wM9RW!K@mKcV=a","n#!9rVL,)]+W.3ORbk;~u$I}m0],?SSoR5.WM`gGm{N+;EUxCD]vJ,y(SdE:Qeq^","(0*306}O0Fg3.Y9`{3?z`(P"],
  w 41 49 200 740899 740899 1 71 ["&b@"]]

private def r41_6 : List (Chunk 41) := [
  w 41 48 0 750007 750326 100 7991 ["e%$esK]}U^-6N3,mw6Y;VEj7=XOiNZYiVOOzV}z3T@xtu^DmI6m^l{![__;>@18R","lrK)|y'wrV?iu8V(4&V(xo61Kz$ld0=}'o<)c,AX~CkJ|h5,<$HYFqPBkH$gh|mW","8x2yVOX@L2c*J+#09Q0,]j^-;S.}TW:]9T/PNk:d.JCOPF{>lBG6f'T<n*0feB+n","#?Q-pd_-]do@k8o@z>7{_7PmJTbK|p:'w+IChlo:6FX,@S1II/ny|1|8&me|t)gV",":,<;Cn*_'e)E'5pd!P2N,(*dk@P)9i0#8k,-zH1j^8XK+Nlg#{TQM=a"],
  w 41 48 100 750327 750899 98 6697 ["/@Zu-1rkjQ>I~n%~~&[q?>#X:n7vLDv`_GEiE:]gA.7oli>[ik'6RIX.8K^K<n3r","G?b|A`$jhpEN]Js;L$z]#k@pU5~6+]42WZV<C=K{gN{>_;j2lIHY[}T`Msiz0os=","NZ'utBWB#a`zT.WgE9K>WjuSk#3utT5z%RV2Ga6e3xEn/A|R!;`!#ck)?cqV*w98","&x!krkxxum/j>K{h/>`*v)d|cen[xTT&x_go5bh|33T@t>q<}{lLg8x_l!'L)#j.","B?hQX;od#x:zAjl:x9e?iu@]B^B4~N35'T:%UPXo]j'fh9atktX9Q7d;[;'{){Q3","QEZFe&2C=XE~j3$cBmPEgA@,,;)#6EDe}_b<)8j"],
  w 41 47 0 760006 760325 100 7812 [":%EP%D9jyW0`qi@H*ke;)hp5B+B!]S#ft]rWF.<Y.BAN/wvf.!GCHQ%M@O`$B*2k","d2V]D)|Oe7p,RUv:;E.$2qVdic/FW]8:22Mpf@f@z;A:6obBWe>(KW=C^7?KFq+A","HO8p<:@PeOr,P,j8B!jS]]p.0DHO|jK2A*U3!xojpDO+E&Ee_4d^ai!`w,F]!%##","eYes+lOEknq5`1IE0@D9/'*o!}W9h)&qR2L'=<.Jk%4r20*aXJ27Cuxb=~}{HK(Z",";FMW5[|pn*JWA`2b][&V:!8B{`s+Rus)<Vu3?LoNdWhx6_B5Gb{}:g9ttT$6u'tm","$o_g`bzl`Cst$6?O"],
  w 41 47 100 760326 760898 94 6221 ["e`5DgpV3&?@Av1X#CO,/:vK>bnR1F0(kzGLY')~ub?Q;j_C.`]Iziw?ffZGFL5+Q","-KA~VOC#d#THg$miCA+vb1:q8}r|k)paB>vGxr4;3Mxd!qb=idA{7S@9P8wS$Glj","q5z4o9aW};gIa>8<4HdP&[s`Vsc{dr(q}K}t1BG2;tUq@Oo8N(sUpJwdDm^p?i]i","*b1H85qMl2(rwKRJA7s{rPHS@-]W;feG'LcC;N[97zBUohsf:a`rz;yyD@Pt9t$^","XsoLoR/ueV+l&p@*=S}koL)APfJ(K>rV]Vi(pNX]=K~J]sHy<j`e1]:'~c'_CZNN","n3X4t{y9Hd!Zxoh`-LzSK.5DPers}[QN$F_)cWx=Q$XH"]]

private def r41_7 : List (Chunk 41) := [
  w 41 46 0 770005 770324 100 7592 ["F&Z^{pUvM`eiF+>4fhmiw?`mx1Rfep.ujP*cXcTo''Gre_XW$W#lqv>8if7L`K8s","|-z!eE@7$,jvjkQsLTpx{1b2v>F7#}NzXIN0r>?J!Hs!N##!4-f=/'U;yrXRq)JW","@0s1W^B)&s6Q(3^IxS#?hiZHH^l;pN5TCK`3e@hmv_R3^;_]u~5[#|^45P7~|`Rk","zu1NB2<8QC'3^sAmKizh?TbHG2EG+JTtyZak.$[JlW~GU='aap7Sbc{{6.|QS{mr","UEvw|}pVGn4T$%uY05gT<)Pj;v637K/:M/$kL1GEp->91c+~?I9M*sV.,>''u.h{","x8,$(A63O^(.9'Zup;/2zsN'I?jZeCN[jt&XwXH]N"],
  w 41 46 100 770325 770898 90 5777 ["Z0QP>C#XC?rype9)mZNJbUp0tURG'dn];0OH!Gf-X8II+UT9u=ytzjRkT9Jt:~/r","&,Cz/Pr8IC;:328exfLcH511gKZm^`nK9(UfB{IyeUA&lZ(m|<N(Nef<+Hyr`_1}","x;(v?&sSc0!r5E-Mv{lY+K{tfy_dV]A,w1+s+pmyp>%Ng3#1WPj%Fd{Wjd5S!ti`","A/k:bcOKwZ`)OUBl_n+Sc~>Y][YkJZerZ8})`F9q:0ax~x+wGzLduJ8VkCp}Bp5#","F%]N]Yo~7@p'nH;E^XRJElV_8I!M^64y>N)<OI;y:u);MhH-lrO;teoVKf['#?;k","HXJ^AFEA9zxd4nu~fM5aCnoz1Uj~eL6uz5T57GMK~7[~"],
  w 41 45 0 780004 780324 100 7396 ["0oi)r#tB*aO&KqaZZ2`H!RE92&xlC4LbyZ/cmKxG5;,$W{@6q(GW)qe.U,]P5w-6","bvc'p^8Gs+wN^al1UVO^.V7b4Exs*3<).NRgELU^_E:e.i.r~(WnPxssSXhf]1ic","/=>^>q#8>ac?T'{5=xn'~Pwz*JW&_Y'3Je|h?unOv@Jt@2^>6!B$`e{@4dcY_g7%","I:Ccve$+QE:$r#g8R9McKDC}K#iEbt2-1aGGdvJWe`~F_Z'eGfx<F%uF^##[S;Y(","ZEzbVhjb4h5Xo0rg]yWuj0u.!J(nC7[x`_=(Su.%XR@F7[33'-U~Up[B?v!UXQ8b","h3B[bQRCSSYG:%0UnukgZ^b/HKEw0+T['&;X%xDnM2U8',G-?^.ETj*B1(s4#w01","&9DI%~RYN'I>"],
  w 41 45 100 780325 780897 85 5291 ["ewFd/N[)<1j((2}&^6G:-Ce>qDMwNBF`.?yE%x|(2cc?OQ[.<,zQ!#^/ThU'DSP&","X>q:7AzUzb^#W$F#BdrxhMa#%}W:0#?wn+oWU$G*u{EU'(&+gLp_TKW:&SV+0Ghw","tv<[$#M6oQ0?N4osUm@MN^bgPoTvNC]AEF9h``4[(?A't[zc/o3+GL{%SLHhm(1.","VX}H@|KEO~ykg2r9+/T-eAW2fUh`>J2?K}BgaW?Eb,Tv:q?NO)KS;`G88uH+.|;q","|7m{gG'*CQm9&ZAN4AJCTz[Hi:Pd%,gn4`XldH;GyYef>p?r@VZt0|1%aR?EVcdD","*!KpM8gn>x1.p+%yxm}mY4]yyMjJh3h$W"]]

private def r41_8 : List (Chunk 41) := [
  w 41 44 0 790003 790324 100 7150 ["KG&0h<#+S[<,GaqAmktcI5d:Nd'<m(b-]nt?#,'>{:IT/@P!,zFxA8A8q7or9Mzw","t|ixG15/QiZT|2jEd>oVrZnzsV)B6RlBT}gK:;@$*BZh7*yfAi$DaFke,-6rQ'%O","]<1Bw'n{C]_<L[Q|*X84z)mLdOIL}Tml[&_&>xztu'Ev7!}]QPYpcSu)Px2^9@8}","1pnF7:L%<-RXKrd9RK7K*9d&7a%rdC+sU:[?9cc_$~Xv3J:j])nclCj[4qa|0BSA","xT*7r(pX5Wx/d8U.050YT]p<>)@9M;!J!0@n1%!}n(@*li,$v{4W]$+2K*iODY<i","&PL'*$p29<c#=F(>@|i={Rl=hYr&MnM2?w{Ob6,,Q1au7W&2ep#X*<Q^It1Qb7(,","7z~<fe|a7!V7-6<~D`+GKc%S+$%evs"],
  w 41 44 100 790325 790897 80 4835 ["A2kbWCfs/`t.;u8#db$*AW>Etuo5P8HJ~tfJ%N+>lc6?C]M6L)kg/`s}Wl`&7GvZ","wTWNBU,X$f1Z[15jsb?]nx7@bAF=d2y2G_7KL%}2pFX8*%29gi.rj|o<2<EJRP>i","MUn0Wc~L%{tuFB?b[}({|Eih);*6xV?z8M;xOH;d]w[@r7^`&cX}PXaLD](8Y?9h","n~bysH]36k!k|,RjL!v;|Ut<0pz_e`Sy&bB0J.wlkwZSG|ka_I<yR'GZ8/0Yy:-A","6@[<%6&`VhEQ@2JJgEDbD;x$_'OW'CG[IptON7^)_&v=W0RjUM:R[tn%dY6epe}c","l/h`2~bG-nGg*5ja"],
  w 41 43 0 800002 800325 100 6926 ["fvv0%$aZ5[|=,i//Veiq`Wffvh;},[N~Gy947uPCSpCs|o;tmSZ6B4SEYv2=@2Yg","%B+RQ`Ol0t5}vh)W;9%|U<h&Kz&2Owv^ljzh'5@ZdP][sA{@CZSen8hS?K#05d/R","]+iA$='{#Du>@AFRoCXw1eo6M'-Fk0:GV%bt2Q&xKn5O^2aqrevVjvwA)j6NK+~u","AqcOM}@m0CRy{GxBB7<*pfTq4oYmt:lT7WdQ78.Uu,oP|<OwHDJN@FLODRs~(k?b","%&p^TUC{^4[&Fm2G<qEqTG7g>o+^$o%bks=*Ml}q78mBppPXys9;Vsk]D(@(+f~4","%3js<B`t+ZEE;UV}VyU.seDDFNE,bne,IWz'_.*gsh3_gc_*m+/zJW<42O3l5#yx","#;7o$eQsmKIgCtnE*4'1y>^,a{al)Ws:/"],
  w 41 43 100 800326 800896 74 4340 ["]k-BSWlcU/<Y'6I6-'W0VSilbsbbNdJ>qIib/%YOqnQlzHvI,]0FXvok:Pn&hKqO",">y(]|;QI[TO;G${=ILFT^%;CbwXzv7e0J|m!y-vEw[oxPbaL;ltAM4>NuzQ{x<*i","!ds>!rdlh4<$=V{P3Ii(-PrTT1=Q4cr`k%/0zepN,6]RP<2<Eh6n)][;twwii<v1","AP#]'Gase|bdTlS!Zl73gcv$ceiNx&B_;IA2GU=-v,>nVfS><tjq>at9KAi.SB{E","$JX@18@9P'Ke&-]ns@/-I~x6@z4T8E&!_4M_ZK@weB9C<Fr.C?7nPw)a1bH{9_GY"]]

private def r41_9 : List (Chunk 41) := [
  w 41 42 0 810001 810326 100 6650 ["w9E^yJ&yJmcGy%?uuc=*=sSJwB_IwV>_39s5HUG-?xy*4j0a?^;+`;_cLL^nS=W.","#,;[FKWABm3mFEti/<6fIi!]${'J688pt>H8^+&UPO5jFV++FKhNbnHtJorp)jyN","];o~`+KP#BY]XZc@5{LXgK$fH/2W55`[||nOU9Ck-OViPcdOZ:~_p8M{^-bPgGVK","]#_#}@j,&]W26%_o57H$rktdZ]Fe?{!>5WH8.B)HXpk@$m.D#DP-#uCuW!4M%,+M","?9{$))C&xh/Z8OwK.nF8QA})ID_&Ct4[GV`?lG9qFV*on8.YGxnJ*w[.(Zo<I<H2","@~W#R$1=ytY`S6ZX^u;{m4OLe#3qXrB%9Awv@EX|CY>#R5@Z$S;4D:D+nDOh!yB?","$f^jX&[yiMC`N@+WnSFZBH!'`^%HG[Jpw-}UPhGxH_b%>]Q}*."],
  w 41 42 100 810327 810896 68 3874 ["sel]kOGy^I#/*&$mPmztU@p&va{$U%d8CKBgX])4(M|%#c'mBm:{s/J<3ID,r$Fo",";nB;R&%{[ugi)*k<h`8>H^P|B3whXQ0H!i&AVgs-AwV[Z!B6^KSA+D'W/eMi)EeZ","C9[tX--/H7DYNG/':qj'ig&T|9vUYnUR47z6y3v'(-aOVB^R?_2{uZh`&]MvE4;F","LSQJQoeCGPbC*$axH@hP#c:3|5~/xn(p.[o/O=rQH5=ekoXy4W3v~j}JlriRS_b9","#j}zv*:'zPK6P9F[{h[8z3HJN.5{7s81W{wP;+}Vr"],
  w 41 41 0 820000 820328 100 6394 ["E&McKQ40Hp~&wx8t/?$Sb%&^T;G-5Ugqn&J]!?g'Ugl+;B<`b!1ZZTjZbQZz$@kk","yR+0JMk8|zV^GxM$~87in2,]~W;W{x!tT8Oai`%#x:s,%.)YOjudt+&m}yv>N{,#","9?q)M(?G}/gp=Ud&&1Y%Im)<x#0Ju}_B5O4WYC3y/z616T'Nmiw~zT4+HQ:(TcxK","_{l:8afgTZ'dAwG#Q&q=pJ[|CJ26NhTC,)|Po)*;%z6Z0(~5U2>VQ%PGE3.=#h$h","aDj<}k'c%bn</R**7%OtNF3$ZVn-,300sbfj1jo&BMf=;P3y:C)LT<|T#aj$I>9!","'8<%Vf^nHH$po{yf1'odIH2~j1r$71*~3XVj!qy8GW|=},73@V6'v3#~Jv7I@Uw>","^$uBV&6X*pZbgV{Q^.s-v$&6[KO1q~%e#8Bi9'1N4yD:!{te;YA+@_<QD~~"],
  w 41 41 100 820329 820833 61 3375 ["n9WXaM??v'aTL8QpPIUZJ@2eyaI)g58ZX9Sz&;He<J9;BW$Qoy9?ty()3L_c|pJM","HD%nU5Cw}S&i0;Nft7~z=QvK[V,Z:L@j#EX7%xqo|j_fn{WsWOaK^H|_U|Ix8(G{","yZ}bMs6cE@Y0j1x&v(9^%-2seP]f[+/~:|)2azriNRZVn;J1AAmw|><<*X'k_lZ[","~v|hfc[sld=][l!LBiA/J%+>$'Cpv[6g=S:gF{4aY$8,2q=,P+_[mx#}#vdz&ij$","&KLrQ+4#YjRPhSI"]]

private def r41_10 : List (Chunk 41) := [
  w 41 40 0 830000 830330 100 6079 ["A<eO2<s;$jKcW^:@<%fZV,KuZ?T?oV'QEldy6rc0oZ)i|B3-&o}r&5r,{5k%vWCG","OHdXG!t!>vUo9b.WShNtVi&Qq}JQ_h5uJQ;w.9pE89pqhb,Wrb9N&:U43Ni&Q_)?","~ufCy[/()5@/y-!<v3y_2lNGM+j(q=R-SGw)r]XdtFtM@KYtmhEE7ev&j+IE51dh","/Y+>y[5B|Zi%9zp_agXQt@Wxf39hlAeCs9HVkm7?yr'm}S@#vjp.!^_~nM&TK$|8","nVgp#qnr?T`_BNYxmli%AbXD{AoaFgv|{Mbmk@0(h:7D@c(YSHJFQ<z`Nq:Q8u^#",":liyW//O>EEnwhP'~#la&:#6RZWM15[]Yygz:^Tl1`J:|dW/%8aCKr)lZ+z{F>]9","`xpXDD/;,A.@n^>b<p'U2<Vkr(f1S2O&gy(@GAGxOEv$Td[GrDC&;W9y8?%d!/dX","S'yk~3MKbh"],
  w 41 40 100 830331 830832 54 2910 [")'{wCpSKFxcFXbp[t>C5,[-MCX?nd)-jn].GFJY4B(MX)P#J536pd63zOx-+%;C{","KS%}o*BnL}}!XM:Rv${K3*XS`UwWR8.@FDBr0c4}]ti'!8GT/xA!W)|%!bRRYnG:","0-:rB'8;<C^YnA2/AeuLYnjMkHx^yj((764~&eUN#3rbc0<=GL6SMkbULJ_W({A+","#+>IiBz$rb}ZhDCqs'K1{G:r<aU(,+(nq?I9@,?<#b)NI{)h0e"],
  w 41 39 0 840000 840384 100 5790 ["ZKM8Q~d]o:n{[-<@NK{;DcDBPCnlK;ZM*~'H`91^Ie/xBc@c(N/A2(muVyH-`c6C",",Hgo=NOY/%xxnp0NGG,e)D6;f'4vdcPuS/C!+I#Zr^awZ[rT#QecoQk9g|om>ic(","uYYmAH;kZJx&tX,A6'6(yf0:c~A<i:vOR0p]@V&lHw_AwQ:<iiOqx0.>u/UrHCLx","AI&waKAj5KoE7Jw_$F9HGyXu=QC}hm))FJqPB}CIqf>sU$lQ?j9!0#TL7{wUu7yc","9Ox.%L:A*J2<>#b&>n8AT7o^5fPaS%t~qye8<`q*}]Oec$_sJ8F27AVIaQ{?G!<y","iy,/erW-HM|UOa?T%D3(`{h_?Z(gZlpe3j:nhX&D3*>#x^jpR'&~ic0]7)HQM/yK","5FV}!m',{E#3|&u0<}N!I-{QA!TT2szl[Ieb{$jfPR$5TqU/;+j1<vLl``m-KeKl","(Kd}*lvv?vu}~Pj'*mH4+m{w@"],
  w 41 39 100 840385 840832 47 2471 ["P.NAZ?F-#oycU|q;B_Q/4.Hn]/l9}J$oQ%l46sd*k_0)W3XQXGR3/x($79r%7N):","&{3^F;Km8gS!=r>e1UCGqU|G-z3Tv)D3Nws)rn2[{TV[5xT[p#WO##.m7oTKUr|U","])]{{4~7P(if/q~S)~}i';o:9Q)PKorB;eHqj`3obR7i=`pVErGLU1(+d!xl(T]~","#R~Q+e?>w~(d=O?XVAra"]]

private def r41_11 : List (Chunk 41) := [
  w 41 38 0 850000 850387 100 5518 ["/Lhu0Ml=,O=yX=lh9>Z-ZYu$&]g,(IFYy%}KtfWi5~<EWIAZ8<s`DsNV+r9hsMb`",">rhSVMC${iuidKIPprS>@!{2P9|S*wjH`|+wLzJ@L+8{Jyc6{^[i4Nq2NtHohkTU","b&o*~@x:2v(:'>8Klg$:m&-EO`aWVR1tFf:,Ohb#~O*!D4T$b/m+^DI|XJm'NK7G","r(M~+0J&,Z+?p2-.$|o;:&FEI$t`[iRf0rSB4%0}1q$i:>Cu6>vBOP}GlAdJAofe","j:,uqLVV:Ua`*Vy+;8gt`)T}BN%T>_#_C*)_q`BPF-p@km.{,~lC+6piJt?@wsQd","`;SEy!+x[<t@5!8ibD4.ne=#0T)>'?5w)+4[j.Y6p=iI%Bj(c,o?-r=fBJ7=}#vp","$r1PBqjM#G(ZpVT[`2;X>mt~YZ$&%u-rPc3,$`lkWTgo)F'U!xUNO)53^_g)M<]l","i_MSI/4QUjG|=%Nw]xh#Ti%XDa0gK,.DNr*Hf?5"],
  w 41 38 100 850388 850769 40 2055 [";>FR<,[jS'mVI;b%kL07!E4/-{+h(X$jcmFiq>`{oaG(D[2!}I`][(V:JMY*BKhK","rbBpS6Vb,H>LA;v^vanUr_@L4.PaFAC(qX-4SwmDm8KRMT~qSm6^i}{3XlCd%x_c","6,-9H.Ur*]2H'y|{>2):-0;wv.Uw+IZAkj3UOIG#o@#{wUc%="],
  w 41 37 0 860000 860390 100 5267 ["aJ<AQwPFU+G;jm2xtZ9)'U(NmAil'vC6tKqsWR7.MgDip&n,OA7Df:k`X^J|q7(;","4s2bOZ7f3[Jb}(r'eom;5ibIfv_uJC/RX7CqutJ5z}{%Kt4Mk5O@Oa?y)@Db5lXC","tSYuBW7R25^GHf-R(>2P4MiM=SMpRb)7%Q]zFm7%NH.0.~q$%IR_pIv7XN,]HD8E","0md$@qQ*e&9Lw[};TrZ?F>fTHyy*/zGxZ|uc}'|qx;5w(]~%]7{t!vWeup[.99=b","6Q7+xSLBqJ'*6O!x+n)mjw*],-Bnr7B~C<'l1*RGKXx44Oq~&#;I:]Sz0:L<U{*L","odZx^IB#JM56v5,x)9pUYdf'KUZ^lR/;Rj'vNDhrwb|Y$1Hflk=UTKUyaDa=RyLj","}&E7`bw#]6RmC8>n+5.@DYFPw:]rfhuKR?u{bVlpo~/>wfC4xB&t^-m}qw&_&*D^","&ZU,yMcM!@t8Egmb>hVGzx$?m`{?+RFD9h1!v@!Brhw+`g-ax5T4js3^em"],
  w 41 37 100 860391 860768 33 1664 ["EEaXqMr1do%3>WnH&gsS:*cg78<ml}|)S`+e][eL_G{))>N?]evOsyAv)/j7Do0_",">oMX^4&t5EeopD<nJDUU.1Q]EtJ~X{4b'6;9H8WFTf$95q}6j{cxON,j|AchOP#'","$emV9*RdjmZVDT"]]

private def r41_12 : List (Chunk 41) := [
  w 41 36 0 870000 870393 100 5034 ["acU[jK`^F<QniB~&s{y[T|G`NUPN=5M-x*%SFy7)^}l^p_>/xyfw>c<:OZ;+&AuK","$oF>@^7^LXz9dB4Ys=]Zz+Z{WBC/-$7/W[FIF801^(cXn`%|v)I=j6c^e#.l/W`M","hF/&+JtSGzwBl%9SX6=.bUR&]8?(J<|p=lM]nDn(&NlIQIqb'(D~[3}>uEqdkaw6","{L:2YZQ}:QnRx>eh's#Mw5$+9;%Hl)k=YG%NdtX&<#Kfn~2'3M?lIiq#xb'9b|$'","qls,>o@dBprzEIydYu8e_[u*^Hh,T~t*8)xAQ6B#I*,u1Gk1h.Wo6~~8-xV%gdmU",",K3ucJ>qK);*5Nx:2Pa;3sN0/$J[~3R)Z)B%*w!dS'6;nI#-N`.r4ex=ksj.IhIl",".D|%H3}DtOR24aM{M'dB,N$&.wo89j(pR6@35qaMHl2MA9ZHX+7*Abt|aVa<'^t-","NtI52j<-ou/]lU}b_eQhgb2<vsZ,,04[p;x<WVPL7_sCUrxT>6NC?EcP]cJ>)1n(","38>hi{Gv<j"],
  w 41 36 100 870448 870768 27 1338 ["kcF/pH354GmGoBi-x)P|AL<I|rKjnQmKxN=[#A4xR$jJ}~w6p1]OQPXiimx~;:Ib","SedSFVHjg,g@vM,^!fY{E&$x//4(K61S-d62#S;0n.MA.:ifBEg"],
  w 41 35 0 880000 880451 100 4820 ["}}lS9!{oOcJjf/}0iwW5nR$hv3:*]Q_Nr!`D2J+e8#[?o9&TMMe/'&Ac}JKCmNu|","Z2hg&iVN<MVfScS5SMo2L&P=Tku.A_@k6_vKsLbA56K.+we2gD%6CW7:NAy-c<hO","B2.n?*<QjjX9U%l$IJ0-7&,4jhU-|5y:|}(_tREOcH%Y>_uLr9/>tIOcU$4~%R))","M)>}~XCq'%MM=n~a|$.gn,VvS[oE)CVC.$fk7(zX<.v.MI';lY~mho4fw3#Q+htp","e;h_8DsqYtsyk!&%@M.~--VHB7_Mdq$oHiKf!rA8tJ(N5i#2;mgpM=#ov&@|LU_;","8}}@+{B'*`]*#R_c{UfEBW%D}1R+eSOSx6c>/^t9+:OiI-+EZ}[M5t5'sW{+]7T)","ki6,c{m9Nr#}36['v=g^r3a3C35{S=jkE~C&+}[gFvc#x?F?*`LK*3LZM_vWuANW","@Bw8b^Lpmfeh/h};,In!nDch5&}.OOMqrV>8Jq2>(Pa09t9{e.QhJTCEc[N]!8_C","3p1};]7h63F9-T3$2"],
  w 41 35 100 880452 880705 20 973 ["V#x'CZ!kTy|MgN3fhn3a@;$4FLoFW*g^lsN;Q`aKtQMf{+glhu#XM=mi:@b?=i*&","}T6<2(p!{:cLCBmEtJ_W="]]

private def r41_13 : List (Chunk 41) := [
  w 41 34 0 890000 890454 100 4624 ["m!B$RN2<Io;h(6I/jZ*(.G/?b99yqv7j3ol+';Mk6K-gs;Qf-)>jcaGh_b:'?7^p","Sc(|490~]S5BW!nM&8iVVo5bd6Kxc5I+bl}!:a8q=:}dFK!jXt-9*kG'XMA+_%Bc","tVM<8/O3HscNr!SmIgy(S-%XX=Eh>3_wt1|JJD[q1vV^NvjC|z#0?&Vk+RYQny?9","8V3.NH$RHxdnz0D'GG-gW;3M$*Zjaih5opqU1g'[1**Ytt%ebn0'#T,NCTFWnohJ","2:maeOj37;Wfl5~EKK2=]gFp4{'#]%f0fKwaMF&OA1O$zPXj)2pMD=sq!$#Kn@a+","2TEf:cH=4crZkTw$MWY+;>m`H92=Q49m|sn;&J8#VuQR}u.xp%3sCgWYIE;7}W+N","6>4C=Ai^C%_R(hmWH&%gHtdV.j'+~+4yFyks%I4jZlYsXed7,{a`;D(GS!MX_3&1","SW|PwN$h=gF'hh?9[{,.?9XzPeyYor+G43<E7<@1L-[][[1@=p>Z;1oOQPh#625S","Rp-GNM??sUgX6MT)mF@@7dlONh-Ag4=k5"],
  w 41 34 100 890512 890704 14 671 payload14,
  w 41 33 0 900000 900515 100 4449 ["+X1Eoz(P>0JOfux5ycYB_D=I[4B2QQjIw^N}bQ}FI&zdi']ow)5c_DK$3AUJ$bQa","+=K?A*(!e>u`:A/?RWv:|1&=+S8;r&>i4%zA;Qf(HK?qFe4*e]R*]sZ>uhJ~R|aQ","?I$tRYY2dEhO*u,7K)^?5X*@xuGi!#cl'Cb?fo,#ZCoP&cR##~Z1CwQJp1.9X[Lq","eWOGXBUA8*_-aQE{n%G[Cmc(6bXSm/?lsRF@_NgKCQs9AvLghp[1,YI,+bgs{GyR","@MVB6%niB*nQ6OOk`h?d}~>.'Jd8-E_)0(PbD^M+0;=C->~;jWuj:Km1^l(UwI4b","]Q3)tNtFCmWnBCY`:]=~2<X/S.H|<N*+pCfo+^BKs[0[uX1h,'w8PGgkv%DJsd&c","N?tZzz5bDQsZE=uM'f_5t>]J)$Np']y>XlW3rF=[m|u2xcem*Vc1[|^qiO4b;Dws","|6U9V#C/~:3eSGd2_)9u&1@ukwI=T6ULy/mYFz(o`!]wf/ZI9e/+_WJ_LV<tm`3@","4i|?G59UU?t[M7o<?[>6*:N/,}'!x:h-xZ]$2GO2#c"],
  w 41 33 100 900516 900704 8 379 payload4]

private def r41_14 : List (Chunk 41) := [
  w 41 32 0 910000 910578 100 4288 ["3$eN_SIDbd$|]y'#XAYQufc[3R@vrRk9evC;^.iw<*KN-J`WR*=pc_p%wvv3ILu^","SVkEu&.O(G%#YxQs.C{v]='76:4^1)-F9{Jn=g_:eQT~$*N/r+!WMl311meg,$U&","#6LKa7irqQ!/a8b^B`)LWniHLcE)82=qI~QfCyTmJ1w!1]8oHV$v%)2'0xjD/r<0","[!_[a-!K?<$6Hi8IStnpY:*2/GE4-Xv_9F/4'{0^`s;x@u7=80)i([KEXR7+drv@","OYnO3~Ebcd->g*P={F&&J{)@[JI!j0HH}HF~3Ut<0GNW@l&Vwlm#tkrZ,+~g1C=/","=Gt<IAedc+=5-v8MM5-dHmB<)O[H>Dt|R;L[x*KmQ3*x~Cos^D+8~Y0+/;;3@2&}","2Fq0P~,0-pwW3Y)=T1LI|_YAp_5o8QZ9`B1[RlScwQ_=*$:W:J+zgb(zB/f9`'])","*dcBGaykx{T.+ZVx$O+Kvt>R6(<zt@(ZX#q#+4+,a_l,i)wXiYPe!XRJEd`JJp}d","$#/Y/Oc4^d<CNsNytG!:vw)Hrd%h;c8#jn)ih89JE7Hp0b>LH6d"],
  w 41 32 100 910640 910641 2 94 ["#i2GG<Je"],
  w 41 31 0 920000 920640 96 3970 ["AOJS0MezNjyF$Ah?Kdn2kJIKUX^,J;~{?/bV;I@p8s=f4mYJclAR5hK%Ao<9y5=Q",",?2G~>nm8j]o=6C.Kc*LW.p}+E9{U)fC.(lZy7B&0>xq7/1~u(LYIf8K^(e7V*6Y","A2AJ`1;4MNe%]]-ty(%-6lklat!/v+u<{%b2;~&@_kzp0Qjb7n6Oezff^X~sj8$S","ur[WqjMK1_=ao:%-s#3*8)1RR{Oh{6u<tHez<&iia<-,`<M$(GC|H4yUS.^iBvB+","sY32v8L[TUFaFvBa?3w=e}{K_V8H5NF$lO0)crVjMC[l#`2c:&<fpF*CAE)W]nUE","&As+B:f+c;C*f&#Lq^K:L%m^deRUrz97rQYZNiE[za?HX7S[(CO[/2+WDQ?9w0{?","Yb;ls!T1YS{^.lt|OlbWX/[~5%z`11>{K[<l03SL9#yJ@0J9R%k;Td8VZlYHH{~4","7=?*s!wW-~n[Qs=a8Tfks7XI@kLc7~nHjx5<r=~(B/gK3R!L(LIflSLS(3{.WRWL","7;Wr@YZz.H2qPbQqE!y36MY-VbhvMO1xPX>"],
  w 41 30 0 930000 930640 91 3623 ["a`X(qEdcC5`E+mC{1e4ugG3N|3PxtH|L=*9h}{Pz:PnYbAhUecjvRUUV}0A1h?hY","9KV,M}?KVL%ovV1+t*X<*@$|rRYtKN'1vFZ2H.9rYm4[gGLAgCWV+<h_n&*$OD%B","6gk5`c.May}Vt_~s8z{bI{Em(C..XY.VTk*,!YDXO}@ao;icH$Mh8YT%}|lxKcz#","mgzc'odM_){olFa&,Bg_vDsJX]oiR]^/E]7avYjo&J;uu-fmaYam6bEIT4x9;C=d","':[yVe95m&I$dO2QF+x+jl#MuI&kW+1V$W,enZVXsJ>DD?+NjzE.K|S<7ezA|-a;","<+e4=J^u]#kk4W-!.jCjnlYq$CZAQ[|L):LhwVHOON`#OoLdc~:%[}8<|>DLEY^M","~2_K:;&/WpT5:F7%VaLH`KjLg3X~RuL4Z{XQu0m)I7+ic*cUETCv2W3t}5r()]^E","wt^(<:C~K>#Yq,J87sZ/7gC^!l;T6X9D~EsAf[ZcIVECGQhb/U#gMUW?~e,e>{t+","+W3}_+NnV?vZUp(jg"]]

private def r41_15 : List (Chunk 41) := [
  w 41 29 0 940000 940577 85 3257 ["{AP~@7Q=llIQZF{g3RP,5Nl~#Ft2rrw']:Ti7%[g^'rZ2Ba)tH4M.%EKJ[fG_0)Q","H^uwLiE!eqn`?L+5N<&JO*H.vHVt+oYf8-bi7M6;VG`VA*_.y+GY%xK64z?5Y%tK","X)M?i'ELG/8WpfyLDu)fbVUX(a1+^z0B9Fk!E>VW}gHhTx0ipnfK#&eS`mslo|y:","5;*|T1ut{4hGh`2HARYY_|-cYib`]:Xtg-$Z:WRUdR+[h0X^)WE%UgsZ+mt6-d6V",":jr9yv%1@HWPojw:#@0-?:goSd2pJ;P:r|m-N/#2`Ns57Ew+@#{]]$l,MS-awuZ_","fXHUDm/|xmd1O%Pqz%hH@WV?i=oM~8=F}BXrG]jR4-[EQZj'`zc?G8e3#Hj|nYUi","7^u5C#'O@-m3/,c:>#G>N3VQQXBQxV.@.DcPpBm#+LN%pXi20J2aP>9XX1E65E5-","<y~>[j{>Qx6W_Z<Sf0=P(/bQ}F1*ZUALJ!B.ncbMcdKLf,S!M,,"],
  w 41 28 0 950000 950576 80 2954 ["1}/3E6he1NWIs'*mii%o#2L4-9?]GY=r@)b*KO2Kn,GY.8v[GF1N80W871j;DnAb","a5gxaz'kf?-9RV5:4&hNxH#k}<-;s5/Nc6&8`;9rPu/1F*FAjepU(]Pi0tbK^Z@=","HM`gJT`YyH$Cn]7dIc0b5kxCtX<!}YG^E4TlJQ]nu}Ak@1#8ptlRQ'm+>*QvlL,,","RGo<fn.9|?qVZ4_l^T]L`5Re-[7wBr`Ozbj,!r7>#WnLzo&xXS2>/;*K)x5w[jF,","a4-<p-e?[A-e%8i%XJC@YqLD{;Bs'a6|NG.DD(Z,^lFP;2PdDiS}(y+t>r<S|_[S","svJr/`R{dfy&=<tLFNQ@Qk/uXS`^r7_XAI{5^/zLnMk0!K-`Je*n_d}4r!#c*e<%","%UiFL5PRX80*!y-,)aA{8B`6YDsaZ]Y,zEs8oHeZ[H5Fml'zq^0Z$~|9aBBW,'I^","%!QwhP8'DC(C}RqSGIE/Kn}arzmO"],
  w 41 27 0 960000 960576 75 2672 ["pAvtpZqxM<vNQb|cX]]Ln;Jq/4/0AJUT}wPB%|]Ri$6cYLWtxU%2G+W7>N&'Fx^1","c?;aS:Ld64<[C`a9_D?kqj3Z)GSZ7gno3-X8eX@I!W/ZVgpE1<CFr|R.-;$QxE=s","|6}bisvA*p_~q#A_WIH5<bC7A)Xzk0-959OD.vv^e+.kcLMXci_Lw3NN&~QAM|m(","#,sBs_P;8i$H?*t,Zp({K$?sq{zB%$y@VrQ)15uA)33ZZes@%#ZWV>3)sxTMtmtb","0SKrbiDI-Jyzb5/ghBkl.I=1BP/vrzC=xQew*-?6/@#`18Sl_6:Y9KId$Gc,Z0uG","hm@BBaDIWV>|:n{OPCP5^caun&{@@hCiWpOcL,`wceC3dt2vre1/Z[Id0d0ifPqs","%T/KDv00ZUuy#N(#/+zA6BI`z9z]AkT]ECl$H|pLlyT$bD/{~0Qc+UU+0kLrhe=s"],
  w 41 26 0 970000 970513 70 2399 ["Ua~Cw;%|)p*lRk]jChUiFF![Mu$L;gI#Xpvg[$n@KDU*q_13y>!&cH=RshtcQH=Y","}Q[s^|M`Ltmz'PHKx2L.o7|!6HkN]G_*^KJ}uZx+r7kkP@%Yyhl:Y.9H}C-T*G3f","^>Sbe<^'a2}O|^VeGOz{1m'*AA`p?KyKlma/hNu_Q;?u0{/&GBDF9@Y3J$gmag&%","KXFCBjKC*/8!h?5lGZG[lA9u5>D{{R?Gx-J)~1YB8,UT[A.r:R8sD=Q0J5Y4Y&.X","yC,nw{w9A.!3$TshKJxlMy`yG;r8C|nu9>UFbhwIkXSYxt~nfIFH]~1-hnSh@/#N","!(2jRSOE0?az07SK,Of'tCn,rb?[(LN4G1[IGrhm0zu[A$,ZcV^#*.3k{6B%zaV7","jaZ.v;Uh)&t@|:Ucwc}2:26mPnjt(LipK["]]

private def r41_16 : List (Chunk 41) := [
  w 41 25 0 980000 980512 65 2147 ["ta&tcAgoTWaam;vxr+'1Z{7VS#;jKgI/F;xnjr_vXA=3xD']*9+dWOtR-.!=hf`R","~!I<.J9)=OEv6YC[[q`j{lvO%L#p|lz90|PI8=`1/]D6Ru0l8Z2SOh(G7T^7b~%K","U4|3`(B5Y<h>=nqe`&Dc@a[=yB#O@XnxUecvlB0Db}M,k)>0C#qol_}+sLeiHBBL","/2E2o@/Y$}:pRhI9K9z3|iS_f-ZSk@&k_h:RVU2w?H6Vg%aMO%SBIfU>ys`U2^QZ","5L)62HO`pE-[eeY-6WjtT;(a!>@J^Ko+%J;wD_tWfN={#jJ)_6#[S&A&FD^$9k3r","~CpQPW@0f,YXSJ/yf<YS7u5A5&>GfZqes(<]|'{mCZ'&E~I~7#D:<~$nZ'#ly(Lt","-Oi@l9#B6n"],
  w 41 24 0 990000 990512 61 1940 ["xDW-#i1Sg,W`'W[c+5S!G9V-Pjsr2+3].[O5+OA:<*=+QM*8-I8]AqG(qrU0H5:^","ET8(t*nlE_$FP<sZ{@3n#r;XQoO@jM_dA+~m6v@<lb`;qKey$AjhX/%LN>}r0cpV","rwiV@ZY_eX_[?YdTsi1s=v*cDzP1~Z.&^5{y%&0`Zr|rM7H]##wJj_?hO$g~3@%G","iw1$.a<L:~lYv#`pyY9w.?-R&33PGUolv+vkf?l.G6~RD+zjneqiw?o2,(I<(Q(:","7mmGtCD@8ZJf`pUTYt%j-#iTPr:48V{[>!vBVMjv>{86|k#9vPV66tWSvL[]X17<","#ENGX&oY|P9TrRnZ8lo7~tX:2RHQKEx(`4.%t~?W*)w"],
  w 41 23 0 1000000 1000449 56 1711 ["7_82QJF5I3#O;'tj*i+s)kQNxY7cc])F1i'h{Vo<dRvewUOYfeeZA-eeD=kfWUCd","K^HHA[-3&2m?fmHko8n`B-]YL!TJve5w0_35^*w|Z!Gx7,A_WVYxy~<:Q`RMFb3v","Q|?'_Ozr_ma;U@z5F]TF>w.Jjp3=LY:@2WM%N&?,IzD@*1*G)sg4?1UoP>)FtNr~","~Qpf`p}[$FFfm$J|>ELV&Hgi`?%l*Aof+4S&_c)]dB*'f=T:]i1uVv{kL=m{%/5{","2KE!r{`EDt;5~f}P>BNF$j*yf]]|sI3c}zi,m=lu_t64hlnri!*7MvUmeT[F{otj","$yI,Xy@A/WEJ-lV"],
  w 41 22 0 1010000 1010448 52 1527 ["MR@by;b=0<f>]@7+j]AR$sb=QD#kOqcb;l7.mQt3R!MIA.1dj@qmF~b^6*vu.]k/","'N?R3X!i:/M9e#x_XoE6P`9PtE7Po_~6XA-//y~2)xw.z@oG%qeuZRD=;Q$w&mH~","c5Z#[KAe/x7mO={L#?cz8md+F)pkArkOBnf,.RFgRU|Wz'p'fl='wo2|/-wgq~t~",",KKJk-&O19mHkxi}Hsvb&rpm2sG&ur1##GUJK4nFhzzMJU80zEwnUk(1#iOE9VXo","$cp`>yKNO#v5M8|OEJ^BO2tzb3.q2MbW1@ENv_=B.C+aO3,4F`g'_k*4R>T."]]

private def r41_17 : List (Chunk 41) := [
  w 41 21 0 1020000 1020448 48 1356 ["|]O_3_;}KzXau!7$/s&&Q0T63IZ~!>Np1H4!Des34NF?Ai)R}V{&rX^mS_]?s4y&","U.R~ScZ+)Ii?Z8N',YEu0OeZonc3P.iT;sCL(&9;p:VZ@{;dVeSMqS5euof{kSYE","=VFSABM?LgUG<cnz0,Y|0XX;jx$d0az/KN21@Vc;(4zvHREdX$5V84|QP)F0uFqw","?m%.w25yp#mzKDzo7e-71|NoqsXRjv9`zIxyx-=rHZBhEvNUW]^3^{OVogDqRfOo","#_:ioI.lH3JkxaN~S1(U^?4/MBdlVxOMYRoPNZ"],
  w 41 20 0 1030000 1030385 44 1190 ["jI]$uxC(SKuS0?e$%JNJ}L>^QQ2Q9jK'wW3yMW8R9yrC}dih(|gl{QR0EtCO~4f9","`6p*zf!SRXD@)Q[|'wDj,fU^p}rKg9hap}-,(x'|Y:;q,k<|p]W[J:HO90cAvVX{","ms/20![*}te@?5Rl0$1s[m``f*HsVaDX5q/~>h^Ep<7$=S]@$9Bu<cB6XFI9ub<4","b*Q1;R:MQsC-}@h'~J>;UL.&9VA2CKdXj6$RgQJ@.qmeG[Ee.OGgA8B&85xETq:4",",AFaD+-'0gD<W]+z8~~XdR"],
  w 41 19 0 1040000 1040384 40 1038 ["8TR@m81wE$hv6{a$64:RtWH{JW*-!?GKB7p76)1C5p=5qYZ%GqPJAjKo0L8]D]H`","M.$Jm3/?2x~GALq&FRD{zr$I+shF.8(4/zja{/Y]7{!fT?LPc[]_{>ml0`d0M`jG","=Ya|m$iI#'DE>O'.HopBP?JP&M+;F@JRJr7m(~p<ba=t,IRFfj7x6I7Kp8lEQ`KX","]>rHXf!2F>9t`,%!Oe9XQJ]y3CGtf5a]G|FR6E.ZuFi|1m;T*IR=~Jvk3522>B(1","5"],
  w 41 18 0 1050000 1050384 37 920 ["D[+:B$PI2B''2k:p2EQwq.(`f{@0(;dw<Az+:|N:#_)[c)Uo_cPf@?>O(>iDJLG:","&ydf@F$<zGm:@ArRaV:U|{z6_=5]^ukTN+v?Y&ne|>dj@r;N36>TDi`r1e2^h`:l","h`_(a_EGSV,Mk5>W`WoFO[WjpA3/P6H>bEs@9EqDHtboR[o3eqOqX@c#(6Ki.FhK","iJTbu[ffcGNwL)AlP51{%Y?x>m{w>JF)P02Jb8-oM[VP"]]

private def r41_18 : List (Chunk 41) := [
  w 41 17 0 1060000 1060321 33 783 ["+Jq)_FONLeZ/@^p*SgQPs~qxo/Baxo$N[a]C]KMK[aZdm$,<rB3ewI}Z$(`sJYJW","jz_On<'m<1u6I7Q`DAXINKuCO59(=r~!iKAI/pBTDjs3[}s&)yX@m<M]*DcZ_x5`","W>Ql~Xy?Oa!n$oD6I}Lo'xifkx#56[a{u=j1{)Rq|@I.=o*:q(=X[Bu!r4ol|Ial","%JsZ?/s1kG/c.tBI(&1Lh&I71'"],
  w 41 16 0 1070000 1070320 30 678 ["1'xLMY9,:&4!L$zXr6>8v*vWu{(>,PRt<t;J[y.GY4gZKL6J@F,#v{}Mb2'*@5L`","?bog!UL-&3MTIhGfn#~EuR2PTL)xVtOT2q4G2r@1jUsr[VH>RZ0SzQv^g?C2E^`I","wLR$&NW4pV0h1y}V?`ZB:?V^w>$KN]rkCuuT`'u+UsljgSHN;_HDk/k.av_5h[u<","$shu&}z%4vH%L"],
  w 41 15 0 1080000 1080320 27 582 ["-8B=t{$SYYXHc7WdJjR$|O3L&P^b@G4Sjfz*'QpB8z[2n'3@Ij>TWaB5l&uA<.p:","M-9'c0^WBc?7)8jlc<z;Pdu%r>edXqc1?EB3'O~Qn2_U$<7^E8|ZpE~w@.U-).N|","#=-QlU!L*it&Smu*c#|xD+li4u{ZD:qCB$aa1in1bg<R)jdu?8q;"],
  w 41 14 0 1090000 1090257 24 489 ["0|uMQ#UCKCuFZ/fkShV>P4{44k{wQz@=T~oA!2jJ7~A^IAr|Iame0^M/Kt4MKTvt","P&y^k#(MFl!@X9eY.Aq{OOen9DK!ou1JJjv`c=p9&<N8757f&m!pEF>`Ng>Q6mnd","Nz+bGWHy->jlk.tDN0!-Z(}rsuevcN{Kac0I*i0"]]

private def r41_19 : List (Chunk 41) := [
  w 41 13 0 1100000 1100256 21 405 ["T;]u&uGL9m{V2;4V@.1mLL<<wy>z{FASjT>~ZCwG)XBCRtK3]M#!/edfph0XJ;9R","B1/=P~2N]2'67.BQZ<BU2xSD7?p1u&L?616jY]@e1;aw(I9=m@Pn+7nKbhFw9tX*","$a,7(t0hth{5&7Tob["],
  w 41 12 0 1110000 1110256 19 346 ["7cBAL&GryDvF>V4-^!c2-1n;AR3xv_f<ze}&@dKx@rAI6-W/8:HdrZTLD`4Su*ww","&G(P/wEQ{zn3@%bj+}.jtUzT'S{[iyoxAXzd1gci*}@(svwUNO-4NHnw>Ai]UZ;X","'~1"],
  w 41 11 0 1120000 1120193 16 273 ["p,1?nx`xCI-0at)o7>b-M[|hX(Mb#mUEfR+9sOME%w)FQL0&<*Y@yd~0aW=X(;:w","0Rl,F):TPQ-Q<^aaoMypSs=Tp)AsImkU/==T>&Op,||H6"],
  w 41 10 0 1130000 1130192 14 223 ["b^=Xxg@47}=G#vMoyRsA&;$Kqr/gRqc0hn.rS})I5+B?^6Np-yIlxa%r=|MwTGi/","*27JD|xFB.&syWU1EDgE'F1't*uz6PoUvFk"]]

private def r41_20 : List (Chunk 41) := [
  w 41 9 0 1140000 1140192 12 179 ["iCY2q*?SQJfK2T&K=].TaL=sSSS9BTStN.}lZF~;$xf/Salz4T$3!DUK=XxZ:5u~","/<-ni['apF)A|:"],
  w 41 8 0 1150000 1150129 10 137 ["'yrym4zKna5]9S4a0^Yfar>p[XU/yF)cFO[`538`-y?aFm%CBs<<T|)32(yS@|pl",")!19R"],
  w 41 7 0 1160000 1160128 8 101 ["$1x<6`S1Zg!C]R||(OeiD8h*)_2g&2w9?q[.M}*XBX0'umk%@`55c"],
  w 41 6 0 1170000 1170128 7 81 ["s!QLQ%XOd},!WoMtr%$fr@u]LE~_o#o>Q6p8PBDxW!'jR"]]

private def r41_21 : List (Chunk 41) := [
  w 41 5 0 1180000 1180065 5 52 ["V8qlP*k==@p-R6ZQq<3]yP7'}p#JOFg"],
  w 41 4 0 1190000 1190064 4 37 ["H@<$sTtYqb~U$^-zN?$;^2:W&h"],
  w 41 3 0 1200000 1200064 3 25 ["$C,3J{EnK<@{c,~_f"],
  w 41 2 0 1210000 1210001 2 14 ["#+(MUU<jh_3C:"]]

private def r41_22 : List (Chunk 41) := [
  w 41 1 0 1220000 1220000 1 6 ["+W*SI"],
  w 41 0 0 1230000 1230000 1 5 ["WI?NE"]]
private def chunks41:List (Chunk 41):=r41_0 ++ r41_1 ++ r41_2 ++ r41_3 ++ r41_4 ++ r41_5 ++ r41_6 ++ r41_7 ++ r41_8 ++ r41_9 ++ r41_10 ++ r41_11 ++ r41_12 ++ r41_13 ++ r41_14 ++ r41_15 ++ r41_16 ++ r41_17 ++ r41_18 ++ r41_19 ++ r41_20 ++ r41_21 ++ r41_22
def rows41:=rowsFrom chunks41

theorem good41 : ∀ r ∈ rows41,good 41 r=true:=rowsFrom_good chunks41

theorem sorted41 : rows41.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks41 0 (by decide +kernel)).1

theorem mass41 (i : Fin 57) :
    bandCount 41 (i.val:ℤ) 56 14≤(rows41.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks41).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 41 (j:ℤ) 56 14≤mass j chunks41))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total41 : (rows41.map (price 41)).sum = 334830 :=
  (total_eq chunks41).trans (by decide +kernel)



private def r42_0 : List (Chunk 42) := [
  w 42 56 0 700014 700389 100 9472 [],
  w 42 56 100 700390 700777 100 9083 [],
  w 42 56 200 700778 700903 18 1532 [],
  w 42 55 0 710013 710385 100 9160 ["j+gUa<6E)to=4v#T@nD]#wmlPMy0rFcyJ+1,VDY6,{db&^S,1Asc{57je&-KZkl.","@G-,LC]i0wa#W8~*pN*[&V%:|&kH$*,[=~|=2OGjoMir_-OR`N.I;-8#oI,^$_F&","#1=&KTrCRtuiCQ$on#9c<rDU'`vi^_S7"]]

private def r42_1 : List (Chunk 42) := [
  w 42 55 100 710386 710776 100 8759 ["@{/j]BuyY?:edl2ca]mZM'HR__)Bs|:d6Z:NO'%?SBB#6FR-I~#U<bd59bpwioGO","5IluPM1;xZHtglsSS>+tW3lKM2QC,!'XPz><j0&8Yl&V{XDjfX$[z,}$$=S3p@9}","#Nx)'z?L4|^,y!>0?>k-N.+NRGhz2Y>8IfJs7!KzN"],
  w 42 55 200 710777 710902 17 1394 ["#Q<INp~Y+p!8y^h)hh<)hsbZ$`f.|"],
  w 42 54 0 720012 720337 100 8893 ["-JA8Dk9DGqc|^[p{og.a0GA-.0fi.=S@MBf''&RSbj6$J!.;N92^^Z;u4o`8lC|_",",a(~$f/rub{#jeD)Y|R&D59`I86m&~I=l*o3p!PyrKZ/SqSuX{ctOt^xzPSP#h;*","{~BAv|=d@qye!V$$OvYPEu+-'iDJRIQ#},i']Xw|q8qeQ"],
  w 42 54 100 720338 720775 100 8436 [",`$jXqbrG,f8q)WqV,|:z5AE:W-zPD&c`zj037XqgZ7]l`W}X_HhSK6&?vf#Q.[X","/Tzjk-J?f*o_MNk[i`|M,G;,6dsI*HA~N#w*i8OcaH,}#'3pd~=3|;@OC.GXjF&L","%2ZsM.@P-Ge<P,e2D>K5u&Fe?|}#Q#.GtreNjC1HT61xHw/aVuA/klHYw4"]]

private def r42_2 : List (Chunk 42) := [
  w 42 54 200 720776 720902 17 1348 ["#)C2LV#lL!B13j7%LK%fBc$j.v9C+_Zn}Ak?I~W"],
  w 42 53 0 730011 730334 100 8663 ["gt[4PwL4pvIXLm@ZkQGl?]+}9p#,/yrn`3SrE6:(Q+T~2sZ$,N2n$`o(@0%cZous","X?rB|.<`~K#iW=?eDsP&(kGS!!_CJ);KB-rbx3O.n<[(!cV$pLkiAo$-db_<of_S","P<cw<O7EdGOE`pH362VF,^cEG*ZiW'_5-joPNZ6dpHfun!BIcWmfjV3Aq-cZ~b@W","%7!#"],
  w 42 53 100 730335 730775 100 8095 ["hN0nm~nH2gfz%,I%iPZQbsDFP*TR9)[tjFY[EnU<Hx++c,*QL^p&2~Y16-/ZJga4","{p;|CJ0svx*LW@wMa|Esm/1h3o7.}j`C':TbA;Q]c7|lVPw5*q,7]b~X2$nf$ROB","hwXL<{DY?S`M:7Lzfr$u9'iB'xQSO4UU{N}7msn)[pbHx)N&HB|*9B@7B{<OO6f`","0Z-P3LU|aN^_gAXEj{N2qm_rck{i"],
  w 42 53 200 730776 730901 15 1153 ["$VOcH;E60:SF+RtjNB6/MhPnX=T7^wkAb<NoHLD"]]

private def r42_3 : List (Chunk 42) := [
  w 42 52 0 740010 740330 100 8452 ["?0-mMOX_{gTZ#n:uCBR_c7<qQ%g:C4a47pf]yg6ikO68T|I:mWV/KJX(&#%GW,Z*","Q7e(^?w5DisPo]2A7j%DmfTKynYF7qnFwI#5{|o?kcK!VL{3u_O7p0,_qk:{$oS*","CF=5EIz1`qM,Y3<Ll^R$JCjW6OJ[0x9@b@8MP-(Q`S!$UIfYYK;k2qFCnK:@^ik?","'n)7%[j-AV|QFb}y;AWFr@6gks"],
  w 42 52 100 740331 740775 100 7783 ["'c7ugAoB>zM,S}l@*!F/rkKX|k@cPJlB8pC#pPj6.o5kf/,_M]ZVa%UeO=B{i?:l","K4Of`,=#NDieX~Nty0P,h?[,B6O[PTU:APbGMb29^Kl@F+Fm~>-qw_?bG^(B(J#q","}SVCn.|iQC=w2)}N<m0Rgeggg!1uU<;U4bh&w;(BFX2'rF[uBUAgW/QH~0*(N4n5","'/1mA=}+8sfny'31In11axm81NbV$24S?T~vg9^CuE*`vo!nR{ZB8uDGbO`"],
  w 42 52 200 740776 740901 14 1044 ["E[pot6p}&+li]pJmZ(?jHmirLaa|`nA]H}O_D"],
  w 42 51 0 750009 750328 100 8237 ["~W4OlN>'3FcW'f1R#l;TFttPza,M#YPP8t!O]?1uBJT^0-]SOU~L.VG.QEz~C%gJ","3D[d{Le_#BCO}@(>Mm!a}bd0wgHry;{cn<,x`^!6yefP:T'0LlIKeQ+w}>&JKhmc","6uTbS0`Ny?,<JwVUkg,8Qiyb_C_hduESlR;~:k2_t400-ghrl~^UB9(mlr8r3d=S","p$LXP~PHWNWB@E.w'or22NeCfmjZt,P.TwUQ@CW%e~o<&:]hj8"]]

private def r42_4 : List (Chunk 42) := [
  w 42 51 100 750329 750832 100 7490 ["geL%-c<{(86OcO?JBcepE~n3|Umblm2o*<Xzt:9*08r-Hc;W[Afuam<YfH/|TD>+","*4Q-BmZ9rraw'iUupRr+r`$HjBo0Di^ZI2}x|,)X8BC^:m|LbFNnQ3v3:pklXb+]","P#csiLP,v<=EHBpO%o2t1:a4-=-}J}f8)DLB3^(dZg=^o%_`ZXAewS8d/G]FA75]","lT$Gt#3tx:t0ZS}1l2*?0AgtdSRWN2Wrt{d,{ptYn]_'jbr|Lsl|ZqsG0$ww=0&N","`PA~,v*AOh61_k55Cy@GRI3xW"],
  w 42 51 200 750833 750900 11 794 ["$z:Vkk^<K##HFcSuL-vGs4<[a6<cqFm"],
  w 42 50 0 760008 760325 100 8039 ["-]Q+KZhY+Wc0a+6gu0LGo7@*Y!x_XWAT?a}{NbT<HnN~h'jlFTxvb(]s'W?X23.J","bzjFurIC:zm3w%pc!,>GY1z(-0jvHJ}zx4cb.|>[)p-Rohb%'O*|w<+Ka;*lsX1U","P}*A9.P'e~);V+_p4AR1y$3+DwS{hNS]WufD=9sFQ2@GGP*s(ih5{_cRHQL+qAL[","c1t'jPdQl^huMIZR^N!d|H(h@2hi#CnUG$r`L}Jw:C.dtm]s@+zm~k>O%NhP#l1A","#E>2l@t!F"],
  w 42 50 100 760326 760833 100 7222 [">ui6&DuL%JaE7R;?xZ7Yjj+j{ui}@y:ugvXLk$sIGi}ya_bvdkk]3e$v&]gI{2;`","q[$eF<1Ov~+bM|>!{^l_=pUu&V{-!IaR_*Zsn;`zg'bz#;Jc;Tn*O,GsB5,`]K,-",")bIMZ&o4&3R4}}0f?qhTY<5]pD,zzm!(H*y`/cIN^qP9]popo]WjPuOaE}R-ydM{","5bu7!E8z}65jh8,:C!/dBpeb7GeuEM~y(&^Z&rwbS=8`)-$45v5mIBF6Y5w-k}[i","61<#h~[szLyi~kbXU6Wy+8U6?C5PWBaO4FJe)nn4ijCG|}4b~Y;"]]

private def r42_5 : List (Chunk 42) := [
  w 42 50 200 760834 760900 9 632 ["}E]^k)E<N|u;i2zQQF$1r+:dD^"],
  w 42 49 0 770007 770324 100 7837 ["w,Yq,[k(Jk%L2!0u?-=<'!5u|tlhhVB|J`IX<C)L2KA8FKnhNL4|hXaZEt!TubNk","Si>8K]?*15ONxxWk0a3.ECtQiGy=gquVlLp]Ep8C{E,p5y)M$!+#Q^u0W/E:DoW7","UNTuLGJl9@g~sgd+#;Q22Cm|TR2~fG0z6lR-@>)d1n;ksJ05qZ_*FeF(y8Xhdp0q","Eu5j@'=aF*Y%,xV/{/FgUqPE%dS-8<~7dg4vy)Ss`4T)zhhSN8RMI9#H<8N%}<{&","3;f/%_s_25l1Hq'rPFI5.0PP'pk!&n<3+"],
  w 42 49 100 770325 770836 100 6962 ["2/^V|1|'SXy.@{%KUj_pK|0#>>y-6e=!4{A>mC0Lj!U_DQxl%n%i&%(p&Oo(2Nn'","akl!:T]X21Wsj*NSw1;KUC{csYnP?yq1`X#<4P1-bk*i;+8E0?E8a)Zn!Cb9b/{p","zN{uuCUc%N$(zw&COZbuY@)mN/}KrIU8Jz5u{uLS%{xB}Aui|ty;BpB(fY{o}D2K","(.'s@UYpMp&1hzLhC5/QI&FMp8E8/3Z/MJYUx|]S,$;`U,VWzIv*N!]LYsyxHA+z","L8lh:@{Z5q,!o$A_=}?)lHdG(LFF<ct-(oQ_53$=<>UE;:(cg2#QsgW1j)/(g[iK","&)6lPK:qGyx**;l,Qg"],
  w 42 49 200 770837 770899 5 344 ["Aqb/^?ZkwAS[X"]]

private def r42_6 : List (Chunk 42) := [
  w 42 48 0 780006 780322 100 7648 ["MU(1ZV}c|@DEetB5S$$kzpAy>Ps!)6$tYJ'%;4R4F;m^[;G!qKBX:S*t=p?D6$%w",":'wvW8Fiz0&Q{02X>*U|vbK>Gb#_NFa%tK[g1>+L[^B7heJl7-yt>,+oj$HRei|X","_K_N-UpwhJP!scVDbMOvo<Y8%-26tO^K263)Y&[$Y.V(`Q~^V_c|t*#43it.,WZr","j67f1]<|QXg{HwXS2R0XDH*dU3.;(=Lma%ml+|V)9KCf&1_1&;XeX<Cjjw>?=%,X","n;];]|fTav!U]XJ-Ns52Xv^]*$j|1!tmuz}AS:(LM^mrHkoZ95%"],
  w 42 48 100 780323 780897 100 6734 ["-l_@N=eh6VzR8hm&*ia.)Fp,%4xyc]b;Oe8K``pjQsvJOALqo;Ucu2M3c$fgNp'(","`3,0rw$I26x=SJ{ax]a+Pl>sn_VjaTdY^PkN<Up{5?yV;8r->k'D*G![,rix$Y)C","u.0]Qbwt]?S7D|q$E>zkp%OBL;$tdU~*c~MhlAJ}#C`b90kgv_426w`3]RFL`242","4is*FKIz`Hq{dnmAL/,aubV{i$scglhGjVJnegMhxFec>O*1p^:1QW85wsgngW:@","HvzkdR3Y9s&S@&)_**_UU@h/]z?^>jc6R?rf_/w#aUETe49]u>^]Bt/5QHt,&^zG","#K{!1{.:~xf|nRCu1k-8Lwe-nC:A>(A3*H/~QFJq?$h"],
  w 42 48 200 780898 780899 2 137 [")P6Ia"],
  w 42 47 0 790005 790322 100 7452 ["+c<c~L5[Pd7sYF(/~'7o)A1ns?Rz].&<)1!n[B1YZ~e+-3NGas#xAR`04eEjq6Bk","dlWtnx_B,L::bi2ieJ<1(TGs7]^dZl?c(y9NL+}jS-tGitis3r9NF^=<x6<C8E[M","opZk2^E31lI{w-+{J.CvqA{?AGqYe]IUhD}p+Zjvp?5?]0%=!VIdpk}AIH|B!ts+","[/:a/nHe0*7`VO3;2zG59b1Qjgl_|)1=Wx58}kTH9tXElZ'J<]l/d0*U2VX{;-ec","{|{m/5H!nr:n)vzuk`0[4V[uY?gafL>p*'M.zs_5P_CxgCfoZDTSeZtJt,Ba^{0k","#BIM+QQ`ZX"]]

private def r42_7 : List (Chunk 42) := [
  w 42 47 100 790323 790898 97 6321 ["j;B]gVi>3zJ8hjstqf6[`W2?I|/seBr.ue-32!e(hwMkE+&WFZ6'l<fk;g0'`Z0}","|0=R}Xs{!gr5Yx&Y.:%Z503JaEjs6'5PMhCNNLu@VWL)z/5W]WsPjXg^3nY1n,0*",",iZ35*|]'V{`4cA!~eqC5C|zy][)*wE%?oG}O26/hbF_b2Jar.,hVR$W0<[rA)N,","P)Amd=TYztDpMB[PL#|R}I!.@l7]pRuT,e)Gd,/Sgw/Xw^&pLEKYk~,~>B'ta+*$","p.W**407=vDDu<wP>uC8Hq?is:1X'DN?5C~@`J_#}NBi>^4SP3LI5k:0||`^}6|Z","*8kfT@Kh<0wDR])a,/$9`2m~75^l5)8W{mLYJxq{25W6X7&>#S):"],
  w 42 46 0 800004 800321 100 7265 ["2m$NmB2Ss|Utf8;a&B?Sa_Yo[}v'g@Ka,5k4~$kb?s-5$hFo(Gw2Dim*7K/GUa9F","a:SU<'XAT6?JBz8ICpQ_@F()u3dMP2#[$'qCR-dY@u3&,e]D_o6k*Wa~&WOpf.za","cKs]3'0<pJ5Q@Z4'6Z|<IeM$:k&c$0e>fM$P0s2^IuKfc?wP&[`GU4:U'l}No-2^","og+ow-52[HtL]q@e`#ua[BL-W9ssVN>q8E1CyDxMLyt[>N40sDPMf8+p#Qfz@#p_","g8>Jrnf!=6SuC3_D_DI9!}sM7eE;sw_q'i-Xf0>4oN@P6HW`Np{lo8<0mCN46t7+",".BSm`/hs3xmws|DBbLu'QeDw?55TrFe$bA"],
  w 42 46 100 800322 800898 93 5878 ["H:f8w<zT3CkS8YTsp$(I%hDe=,[@<w@t8DaDLHk[oP/Ak'?lfk53VZp<I*YDc0Xm","Feh,E!]<DL{1EgX.WBBOFMwA|+cv6u]Q2D:T(0FgV?Q5$)n-A`Y2;h)Fv?}mYQRY","4k~r,qpf$$hdq8(DOUotExLI.Sl]ze@;]tU=/b*6mS`?13k}ybCK0<fJ{s}=XIV0","Z@3sN<rkBNvYWBp2E6Dh8_6P_`*v+^!Kcqxda!GQ}dR,)@Kb-xXVQDiZ$Or9egE+","|NK]iKH[9BM6ZXS}LgB|%UU@3=3*wkSz47m/o]|JH5#(k^gMT+%T|HeZ`B1pJ!T+","&7K6Sd}LB%<>~n{2$kMHn7uSe*Idxb;)7Ac$X`qc5:]BDGv!C?lG"],
  w 42 45 0 810003 810322 100 7061 ["E<S%!Jq,#44xW5y`hL#ozHUeMb`hTh?4=d5<VCi(kd~xGt'[{-m0frd`Xc-Aa6Mw","u1y1ZT.ty9FJ?4%L+ocyGo)9Np`CE)JhF'Nw97]0O!XkZT{8S9aGN@X+7C~K{Zz,","*HpMD^|%IijfywW3%qf:T6&$0M^:h&YO4$(LV!W)pwWR%-%,%^,ldCKe&{YY?f~~","!N:=vZ>hl0|4[_ue[;yz.h(~g[!|0[0nK'T$gK~<f])|jQxiVZUkXdL;SN2P)1Hm","T+aTp]99#2d_Di@0@L}TXB*B%AML/MbX_d)><IX<kqF0:SQ}!cu~]Ia{ODl'%<tq","w($pn9e~OZr3.*ki9%:mENs>AlVca?3_t$rqgg?4@uvE<R)JJDhn31&-ptD&@Y8x","AZo"]]

private def r42_8 : List (Chunk 42) := [
  w 42 45 100 810323 810897 87 5323 ["csMC?[PP;eLmsT${vub(Rj<78q3]f;]yllO*-Ws5SO8.MxiW|Ypr_c-InQR!9`L~","#`*&Agp1g>&f:>p%*BYzuNi15l`v~jd8NaI+QHIk]j`&d1Lp%:qA''S#a[<n?#|Q","x2>LlV6L^1D3x7|C8!&&fS<,MxvI/xH.zfi>a:DCuYqV'}@lE}k'=Hb'IEoi%!pG","kO&^#pn*/mX.oq&gYv4WNCqC/d>Yaq#jy`nB=(9dK`7Y@XIo@ca[/59M35yUzm{k","7N)f4HSUx$;C%nK;0GP6.T>RcZ!o0}TBl$._:[/CH(J?[jp-W{sb6%_tW9,Q)Th+",",*~*[x,*KDwKXGyIC$n@OWg;V'8uJ8]tD-N1j.eh"],
  w 42 44 0 820002 820322 100 6856 ["a{i|<s(G^OV6*nay~~]'hc<iKckr+{~NIrai40`d<>O!t9M$|0Sc-=S#e5c>vf|>",",ly@(P>5H^5^E<XucX,eR:u8ce<d;GoS|t!hI]GI8Y=zakG9b8,y!wzQF[>oQf/q","|89VwpllaZ@%x4>B^7Jq<)b.9[X_,Sh}M:lLQE6lX&@Skq(PODLt^S(rXjicbS!k","sUc0v`$kfT25*#CV,>metwEYgP-Go}|[:-Mj4.fR'+Jwx=uk%dS5G'EsbKDcO^|N","%|iu[T0lIr(7wCYXcsK*7yd6Y*??bg9V<as}3N/%5{N7-hIgN5@xB8]5fZ)]V]V3","4Psy>1K~2lDO*#?'tU{~lGv[a$aP_:bmw[:4|aN[h.E/k5:LjQuB4`v3VZlgV.lG","s'NnNu1VUa44xxB'u|&~ka6d,/e%$7T"],
  w 42 44 100 820323 820897 82 4867 ["x*Nf#WGbzZfv3i>n21XS8]Y$y@mg.[}z<;@J&}OA1{Qu4sIiW+<*Z}Y,43ngz=og","-VuKz<]L^J0mF|=eGK-HTJO{l=0DW/oA9uVywAmm<#]<E7E?,tabSNd<ckuvi@ZZ",":r.KDg6,Nmt3d=`V`U<Gl7=*t1-d,Z{h68,*DOJKoNjQ]%9Yael5ubmLOc3t_#M6","-uuV4FKy|]Yg|=5jn:-V:PkEAc%Q=C.-[+120l*fxT=PvQ'7rNmbQR3LQ5!UZE~'","Q6.-~CfL&.E6>3jC#h+]9C<ZP.uhdba]{^GWuIE#DU1Ci6A(MZ+w}W7l)@B8J+y`","-wDfQ4Z(bC&;F*NxanxrU"],
  w 42 43 0 830001 830324 100 6617 ["NQ`$Z=AW'5Av1t/xlhGVwrTGyJTCMT%=&tU'mQLexk[]tZ:OH+|}_b6y(.u7,a-V","9vS1/cYC(gMan~NJnk.oXgsLAf!;EsY~Qx'(pg'dE.$TI&*(GzE_FYYb?]a%SY_=","uYd]ooW23`3YD=GU{<R1a&k*nYD3r4K!lLIG7M4yET6ViC(qFI'7p%Q?|6s+8Y`c","JU7)'2N_4q}`g(Il+,Kn93uVwWuWNd8aw<2sM0Sb77`aUu[8Tvln-WHA_d`7Nv]n","8<hVm~[oZ*x5'6N7{zL=3Ct}AC6DBm^JJ!y|:&qx^O}tyU;Gk652E+X<,=fS{W<z","!lI(rAINRfpih8Ake,DDC,(_w07^7V|,G&r{IZ+v$MN3vVa4^obvcI<ZIVZ@N-?s","IgZoi2lDMDO$f/eP*U;I{7ch6P7/Qt.d?YWlmlW8_WL]a3!"]]

private def r42_9 : List (Chunk 42) := [
  w 42 43 100 830325 830896 75 4315 ["+h|SWFr2PNE!9d>}SiwV@x`BGJhfSf[l,zDBkEA?R`j;nCJWM5n:{@Y9l##wcF(?","&VP2KHjon3LC=N'73:k6Hgv9$b,au(MLtw&0ILR}i)Rd<sh8+3A[*yWP&8{I{F/^","x~=[|r?6[C8y#]tN2TS03%C_IqaU5_4JIc&6ihjSkZq_,gDLruJqI-c$X6aR<r,F","^}3nGuk#,#Hr4!{%2>1#;d^XY3vqHze~D@$Sf)h.|^_-24_To>cp-sz=DnixJ$(_",",iq@ZJw&UL=Bd+($g'x%&4j6t/wxtBZyIXB6r&ZXC|,HRLe$ToqDjh.$Le"],
  w 42 42 0 840000 840325 100 6383 ["b>P='A</c<hJ(c)dy*.nK(BNYY=~%$K}OK_%0a/*3;&DTX}.bn.6)D&y`1eEMD>:","0Bx(6>iM@$aj[st6bA4ruP:$qi{gN>w5OLYXyUu`m)-P#G~:H,vlC(]'/=H6O(L9","f(<T>O7E`2{0=P_CqM6mTj,L_keU!LK0|{GT2<LiakWu%nf+Jn>f:Zb5Yv3+j/DB","T#?Cb/JI7h'8'/PqDAdvO-Bl=Hg0tC^7PtpwnPj17|z,1`CFB0ztJnP0IIl_2M.@","ycd^I0?pIANn!9$~]d7PUktu44aci}?:jIbtw12z]TPrwI.+`ZrC|V.zCfM(k1`(","f#Be=dYy4;0ti82*n6s9imBQ'33$gPcJ#JQ@]nFfv}}@bm%Lcb'Kf;{xz[z@^18N","#0i|Xm.)iz+jMJXoz1>rzXC,S;H6[&|ytisX9Y#{}e(5YT`y1<H*SIGdIB>C"],
  w 42 42 100 840326 840896 69 3854 ["~p#ke=`u__iqz0!/U#y,9qf>0{+1[6391ALl<'d33=R6q.*WTxh5xAS7cG]K*J&N","NZ4H^@jJC$.`Ai&&Y~K%A];LotV~rZs,VC^}A@5oB3m1ExNxAf6/[}<zo07>uJi(","[ev.ITxda=DcF37j;(,S.pDjmuoL9WzO1Dx#/FjJc.#;So~-Sql!iq.<}K=jXvee","^@lC,VsW1d=2F>hA4L?2s'%7m-Y9NyUs:AsX,:;,A/)w?r{AgD^lAW[T&kAHIqs9","_tuY!#JvdD5WQPT|/pn^*wON@44dz-=Dj@Q*,"],
  w 42 41 0 850000 850328 100 6105 ["F2g29Wbnwm_^hftum{{8X/_j820$PQnJO<DJsNdN*4^~hWe-Vaa6x&_XD-0PC;I`","_)Os3KAwLCG.J{iVq]2Qr.7_ug.NfUR$N).U!JbgQwuN9eKHStSB-8lVd'm@,.JF",">;G4&Iu6n5}kWYc2[[X7.Q(w;qC-&c}(e4w<6kcm/:(j&}wFtE:h<)>JPN:w(_Y)","{nuVN?IW(8S?hFFx60pT/KE<Ug>nIo<%F!<*JoY:Na.1UTGD5'rEw[{oEE*llcZ0","[cGJCFFxotw=1M~Jq@/HwoU#mi{W:/H<ej2}Pc/gHGYZ%MZNT{m.GhJY^'@Y[D@2","a=&[iO.riQ?rw=xnw-+%gU'G;?bxf.={lHw_JGpTW&#Fs}z4hmP,nqHO3(jF~lLD","jUJ%#Wfc#Z&Q6BL#=D1rUk~yOu]DsL(l{2<il2tfA$(l(lZ6ewl$zG:WkUX^8uaE","#9/nc?S6"]]

private def r42_10 : List (Chunk 42) := [
  w 42 41 100 850329 850833 61 3309 ["_.k]A|^)dbKf[<TPU_EnS^U/.C$cZ*+1I0Gc[Sx*?xp=S3tFc=J=|>C7*4%GSh#;","m#O;b.+Fpmgi<-3;vP7b|JQqGZack^VALb_|g).>g~Q)$q(_+}TJ07JVP_'H44(w","E?'.~0qI|Ig^^t@y{XsDMZX;kG1i|@$`rj(RrwL6SE@sPJes7}hY46(kS9-_Mc.w","h9Hh$IV$nDJ)r!N5#i;tQ'a@sSMlnDg=D%_pWMoRW?`k`D'8IT-[jy=~,@q8Oqn]","N"],
  w 42 40 0 860000 860330 100 5832 ["||u?9sk?+xa#i@gY&6kj2UzUzB[c#SSJRc#1p33yY9I{i$7Vk*j?k4!f`g0A!l['","7d{NMfqGSp=`{VK,8)@9i+^>j:Ie-:f.S=Fi1]~k|C*UWx8%k^[aBdi.X}~B;'>-","{d:H<#%1a*U.?A<gde$f')Gr!E?4!OT6ywQln@AY-`f'>'s949mewDiysK[K}lg%","uS*?z4v@k8A3p%Qx+Qt-=T,,.4#A|hdnpX[Pg)XB.`V3Gq%`tK&BBkKWUs5Oek7d","r`QJ||&yH/QConRM(>oqmCN0Mk.wb4:y(|T3HHo14m!8-Rf>E;p.$'-})6>.{FUM","|AOR{~SP'8=mnxO$MA|.z<,)<BPMA(/0{C:124_wt>e0{aV-4Jfdksjxl`onP1MO","me)GD4z7a<}jUpS{TO,??HZ){&Ot-ymM!~xA$Gr2R#mM]i6Zml^c0g/#/[*{q&'d","6ou$h@Gfc4zpA!{'n[:W"],
  w 42 40 100 860331 860832 54 2853 ["eHD!jdrGbWiTNzhw'iu^m,P]!D~9678~Cj'E49qmQ2*YRRTa];NSA3a3a^Hjw5Wk","76Z%?o(yK}2,gx!0%X{P(l4|TnYygXbQ:v*kel^+z]}v~5AZq'f'5;Qtr~ZHEPb=","$nERSqs2.^Zm#C2MX$(>!@IN)PWdhLFWKi61`#aVY@,$pob}yB|kH*S-;w..~@T}","%}*.n/^sM1:a8n.[}N'Lb+6PV}PO,VHg(s#"],
  w 42 39 0 870000 870384 100 5570 ["xUP43x-13'Lg!$Mjpl%31yI6HW],n,A?MVmR#..Jznx@[78?k?bGusw6fl:5RZc3","v&tGs$.(z:*'r^.yfaP}Rm(dlf,1@Si8l})M,|{MA9^Kq+UyilD6DKUAxqy)*?Rf","sW,=Vc@J-Rb{PBV#T2(R@Ds:%_y2}^:F0S4>Z-`~s?<!gO28A^#sp]8^$[^}S8Y|","}c&eN~IAADh$ZP~ibI(h{[TzOgNrqV*^^y..s#,IyhAkJ/-h'I'X}R~K^Ltm4F@D","Cg1IA,bmn>=!&xrMcl6zLP_$Nlf;-T%{q6!;$Wa.#ET,3[9YVFf/L}%[,o'SGYdq","T,^4fO3IhV$aV2K()k-;.l9mhO?7,q??DeKUk%r]h]-hS@ih+$XLV(m'+P=M!?qu","+6XjQju]-/vm0-21}OY5>RpFEaoY#+TV>8D:<1|zLmGG-(39v{GH4qdv%}yFP7=}","9<4O7P*LGoQ?}eAl;xIqW5v.uT8.3kUA"]]

private def r42_11 : List (Chunk 42) := [
  w 42 39 100 870385 870832 47 2422 ["|$*c<}Xl3bz:2g,.ASxZucGL;9o'eY0X^1lON0a-HtsB0S-+0_WP-QExsp[dAIBx","haE~H50+U1n'&;mQx/>@02}OHMK__`/w6{Cl;w'&7W03n#,wPJ`9@o(_oWKZ@,O@","J/<f<<!;Un1d2e;$@7-8v3]Em6g#h%aOZEiMyT(PT>YpLF{2|(Jc9k~^cH,8;Sa|","2K"],
  w 42 38 0 880000 880387 100 5316 ["/oHcsoFo4LAMlC,Q:?u{6dWBrA.DwEv&K;evX^2D&aXmM71O{6OL.>/n}s,WDeoC","99N0'dmvnH$Ygl%G&G4[3|.}+k>Bv,cbh?.'I^wqQj/:@r&qh6wJ<QZrKr?g*o;~","$unFfQ$F'K>R`NGUjoB#z9}X!2k4,;yWM)D;>p>)y]BKLvqfJ_*l[!IURirS!<t%","QTsC;Op_J,4?B?@4SjNIN~WYYH=itS]in}J{YB*/%e3_mn=#rnxam6,:jSv^D)m~","cLlh<mG;kVPUdx%B-D-!m9(%8re<C1,o[:a|r_yN/lLxY,{&Yk|<;ReG|Jd`TaWJ","<2@tHtnuZM~8:27nrQS>]VM-uXy[qBA+]cPi+A,Aw0<0A6f>#Ge@G}Y$Lt+;e@^H","TJ%dq*{V*tZ15}ile>|R;C@_S5c#DL0h_YNU:fBzNch2ju9Z9aYD$ne4+HA>ZoOo","(Ka[e+T85hj#LsRsTt):Kg#UP.s(uE~;hp3B=/C5(d;wU72"],
  w 42 38 100 880388 880769 40 2015 [";y]1vUO1ubG$0HF7[7i<OTR`Zu`EM<]pk:[t+YBihsk)H!E/VOE=G{<az25#U<L.","z@*rx[aRmFTk,iy_MsjX0.1s]<NI9H/(ypY;QZQ#/Oun4y~i#;pUOkA2>*HX4GYG","TTo>s50Mq_Cy?*#y/16{VBEw/M<cp,@]N2}"],
  w 42 37 0 890000 890390 100 5075 ["!N@P~[j5BwWmcp3izQhecCUgiRsW(B<n>hEs,u,1Zk6Tmq$NXECv9N3s7KZTMv0;","q$Kt*S6q0uW[}EI/oZ}8p1nf'&7jZ45Pcc3{AVGj[RnehhuX^fPT*b?nloI*4yl|","&#=v.V|.xZ'-(@1Vk;F6Fzu-Y'~p{T46RD)&>gB1gmWvLJjKgeAFywl3hEe];)V4","x@^N9H7g&/(R&^hsv'PGtxB-wJ??S9!Qx]~DJgP=3qP%R@MeEDAQH,*.:0';js^0","{2;`b}lX,#TIe_3gv}xP4Zp#`Mz,t;T,@jZ@Ew_*5e3uyuz(ro1[Lmb9@Tq19|n%","U25`z2K_nD.n)DzhLbUH9m}d(X&lGU@zrW`E7V@kwa]d7U}-8md;Y8'E:7yi;/OQ","@2zxBq@?VZacz^!R&pwaaHcuWw#d[dt9LsXM8Z2&/#N`r(Y!Mn1[@S?Y,G~3J~JI","hcXD/pDs<;^;IA*?&@%qg,;q*}YUvDkKN^]VxU_tsd:Ks/TRxsPn7-"]]

private def r42_12 : List (Chunk 42) := [
  w 42 37 100 890391 890768 33 1631 [".)!|%pZ;EDyc|1~vp)cE}b.dY;e50_}j.-gEF)&rKR1Lib2wm]JHKLfGgedfg1]_","}hR3/91hTTv_MAdv`(2ZdL[<#LRu=P(EYZ<p>Jctp-&r&Yd0;xtoqFKj5A2n[ngg","&LrAg"],
  w 42 36 0 900000 900393 100 4851 ["J!1>R-hV@Cz7L|(q^>N3bnqx9)l3d4p-k,-)mzbD$?seLyPI'>qz2V;Cau<o}DGG","/!C:Qri*}IOn7|,-Bpnh=lzWx@_6Msx6B5ZP4VJKJ>6aD4/WAX,.nKgdt=JkgtPC",".Wqszy7`zSj^Ow6[v'zUPkgBt@5}}mnu}_&D%ZdQxSH|?V={4iii.?{fN`3uv<K#","Ho^k^Q9Vuu-0vb({Z`9g7&@o+J|:GQnKsC_xsN-gU}/7f3O=_Yx4++Y@xQ/!g}Wk","eBypjx*P(>+5#Dj~_A<.k{)pG}EEw<e*&0Q/~/y2J&Ry$3l3um}Vc|-rQ).+dRJ)",";~(gW;9ha,]65/=RRf/r5+@|V(QN.cb,]:BPV[w'=wf-0[>l3{2mRU)ql'$Jyywf","qE)@FsoB:2%`Xs=htlG;trJSHy!r`y2x~x.`{xUgT#XgZ)tu(!)oRbi6E$u:<]rA","plM>nwuE1wj-*,MU/B{Pg<'PAL(azeU&^I>x_:t.)8pi]0ECc86s#d-?Fy8GpLp5","+Pmw"],
  w 42 36 100 900448 900768 27 1311 payload1,
  w 42 35 0 910000 910451 100 4648 ["oXRU4l]7}#f5i=G^+e}Vlz!Dp7fW=|^m{]q+VfJ?W>drb!}XGQZ`>ge&>r9ps<Vd","ImR,JK!cjD?nLy8sYl#ASV1yE|WPvq~Huupg4@$WTk@fXd&Eb1Lz4!]4bD@x|3G>","r5x<M81XErQQ?N*/a615UPD*n8O*5/*n!mdvO1`Z9C5uJgbd7q.:n7A{%U9_ik*@","b-QbZRihz7;t{12K.>[FAT:_q4!4P3i|g.U+dwgS&6KHR0GCT6bF%?4ZZH3a4Dy9","9r(MM%/x|hC`*$-G^ZF3r~L!gT9Y(1K>=r?;q^$acHmq|zr105/URu1dw)o]hse)","KDkr'%:qb%lZ)3PfG6/jB2fCS=t,%'kp9^IjF>KY^[F[*Xay-W4-xQFiVk))6^%+","UC:Il><e7Mm7cU;[+1>U[-Z](B8?I$7-QC{!edEC75u@wIW;WI)vvTkmd;16cE(6","_lI?fWX814b+_I*M+v?lmdg]twWSkjW%WJk#uGzmdRtZ0O;fu~IaE/Jyk?t_vh%d","C~';1H"]]

private def r42_13 : List (Chunk 42) := [
  w 42 35 100 910452 910705 20 953 payload3,
  w 42 34 0 920000 920454 100 4459 ["O/e?GBTa5U|y*+b@1K2-}(vo'jwQT+-tnnCx9yB$W+uxWx$^C~:EHzEKI&BoFQx8","8].;1~6J/<qK4r1TRe/$F'oLY&)-AG0e3tUf[H,|V5U}M<6-V!H2z[h5,E'X[7k%","LrEu2KUYsX1G`L|zEiC>9?*#`}N5DO$ktPu$:56'|~)/sVWRnL.oMY9n+/K'=qNJ","fZvOt6*Zf:^LEY};uCfM@p)}+y{ZPe*UD9sS.lKYR4?P'6?i!!2Er>CLx0WjU&n$","H?&zF$U#z0/Vz)R[?)OiV!mw7?pmJ*tb;L3PMU&os&krDsm%cwWT:m`6B97,kPmC","dWu+|=^Q:cMAI;k$ey>p2{/zw~?06LmK%](hR%y,q~8v^bcG8JPR.[KB%`z@MOy?","qZu]4R$E2vN@fQR,RP>(ZIX|>&vE.!cMN]g5&JHoG&y$oS?0H=eacT7uI&aeE_%2","u%qXNr{O_wsshh'NC3La}_X_,DjU@Sd8)it7JNz@7/dtis+|yr1oRa8m:J(7.4_%","+dZ#/qiH>xa(>c7"],
  w 42 34 100 920512 920704 14 657 payload14,
  w 42 33 0 930000 930515 100 4292 ["^FTOI007sgEp^Rxlr{/P'Bfsu_%'8d5=^2OOaIVj*j@?itX3{;`me{#q-'7!nDf@","K6AKx'kl=vO))yW0z_;s8..AcEco%RD0Z*W2VRy4Y~z(lm'mzwsm(q`4+EuL`h8s",".@NNN`6FlNc|`0_/+eT:H4[$JyKennb@<n*}=-Nv$PRa!qDWSSnZ4jU^U|/1e%pb","j=;_(4<i9^S=9oe3v~!=+vsdL;PNPrp$74d]!Ec#TD7+(G;r&6_7n0A{7C5Kc3`F","1VNi'_~,f5{wYC-ZR5F|*%/jRqea4%p6T&QmJ1/$ytz{&E4YuWKATzC!1)b'7_ka","ba^s@mx0de-Sg{2>mG#d>M5^yx#3[Hsb^l@1HWL/oQJI<!lt;[46V&Nfj-mu/oEI","s/jt#JVPRDTQ0@9|U@mWwiCDhe:a,=vn4oH.JutW0NSLig:f>opL]|QX&[$*-)I!","KCJg)51vH&HFY5rk]h|Rqrl#>,*:-*d-s@O/;gve(ax4./$G'^}BX>dM(GF[p}_Z","+BDuvBr~JkK]KmiqcyiDa"]]

private def r42_14 : List (Chunk 42) := [
  w 42 33 100 930516 930704 8 371 payload4,
  w 42 32 0 940000 940578 100 4141 ["sp_86pPAMU^db}ps9CX_VIU3cfqe9s}QVLAKdn`V3gBsM>aUPvOH/ffISKM+^RZT","#%<@C![7zP2o#7ky?DQ7gh8Wa-tv<RX!Tj:]#!XdygfVXXbkO<Z$fSKro`,].}+M","hOzRcBQN]:wl[sdOd&$2`NaA^pz3O0`8LlRCN}or.^|]('iFi.ZC7VMbL)CRO.sr","Vc2#]SU^]I[8jl{eZ~T9k4=IF}ib./mu<4ech)qDLR'=MUxGPl,6fFw}9(i0,K$g","9j|&52n/q<WNS9wd7WVcPA8yck,O.k`)=Pyg-eQBrQhH8MatD1p0GS6&6M(niWac","nxD?,`&`DL?zOl'&RFS_qC-AWue+&-?Z'bT:mqrkx]Xp$a2BL*RTZ'P~1fK@;<Xx","<Y~@LKY6N>@}(P,Z{/F|$>3+Dl#pd%9oq>B+Bbit$qDwu_XW9^(fj*ev=&e|cmI~","c__TnoeE4Ilt6-h4WL@I}msz%DZV=ANv]7ISM4Itx&ju)15wm<L3f}p;Yg^&L+ps",")i5Z6_S(6&`D~H.RIl-{rj&7T1IQF*B["],
  w 42 32 100 940640 940641 2 92 ["#i2GG<Je"],
  w 42 31 0 950000 950640 96 3833 [",h&C'9TL^4^?Sl~:y<I;tL^ym`ZS$Te^wH)A[3>VL)%MQ$cI2!T]$.8Yo~LUkcx(","Lhn#@#+Nf6g.rjl{qA97>hbwYdq#Pytc]<<;WUl8`n9%_j@FgBgQ'9QNj*T%;7!R","P}@[9uGlcHMZAqA;J;M<S&1|$K+45(B]vpc2y@'h65yAiCZk-v|YjI_hgab[X{>!","Ig#33qxU.&qrGC/m4WrA0t*x:Lbiz@4KJoKr@!E6EZ?xto]pW&s]J>@z;dnM%Ala","{X~]W~BBF=f9!27gfY>;0i+Ygh1$6<GAQ{TF.[nyH'+{et<oKD*0f:e*0@,y0D,2","]2_cnHqFG&c@`MCzN>uHd<m~d21fhtS_:w_v(``%R$1]@BBSs^r|<f)Hq8))'q#R","<=s@V;?}jn+.2A$i'P%1m.twH>qQz/1nr1YmiR%ML27^C-&svwl&b#tzN/YE,W|K","j[PT^yYV,GG114Q6>:'<UTv(c2=AqNsCfvp'uyxOGyr_gL~v>Y]EZy$ll}`Lm6i-","#;~4GKAB1S;yPgIl"]]

private def r42_15 : List (Chunk 42) := [
  w 42 30 0 960000 960640 91 3497 ["<L}2U|.-F5c}ae{'=lf*GZ8tb2iSx4)Rqv-UNpdmsY1V'FDeJ)3Ke<9bB}2h|x#H",")^`ECyyy9Eh;z5S{^xMJh#<pDj08@Gm[p<D~fsW8wxfbu6p5AS/9?T5^b!A!/g[~","U~}^E6B~WVJ0xIu5kF<KA4Q#KtD<-[%y-DRkk9V-/k!Xlz0VU')HY4l%Cd?<<N}W","Z)04OXs3,[DB%l}g?0[/kvLYIr;2lU%9PX`}NX:7+xP%E[=Uh5G&/J?/qq6=sIf7","Gf6sM7Mg')YK%d00-KuHGGF:)sLUY%%s2RM1YU.GUvvW41uA|8lYf&xYrSnf,n_h","`FH6;0A/MMa6nd8hAj&n5gv!R+h$U],kXF+DK5f>V)!S)Eg9/:AufNBI<dXvJ^>%","[/Qto'-Pp`('osn1f$%nQO%g@=l;$b;OW#n4T%LXgW9K2F~v6ms=:G7.C+pN-a>P","+7mL_b1<~HXpf0g8S(>-~o3l'~):+W|qt?RlcEs@WMPJF@856ai?YuZj9e{^J}"],
  w 42 29 0 970000 970577 85 3146 ["t?bg'Z$QV>z<u1uEA'f]Zi-*Lf4#su:S*Qs6DiYn;ae:8M*~2'j,sPD_W(h@mf:e","b@9me:G6$$b9/%4[o8N1lh*6kb5cgU<BkGHX_1CSeO^+#PNw@viYy4[|_o<Z]gHA","jw[65wq=71]naM@EaAY1-TotNOLgs_aJTX_V#2eFX3rBOAoi9)yDTt$2M@R7f=+D","_?|V4kPZLaAi:oSM1>%9%u%!54rN?1UKfWXfDR=LU-4Cejq0-3ZOX4.G}?ym[~ZZ","ZfSyXr&G0]F]x&SNvUQ,Nl*CrfteCZ[=Y[NF!76*v8We;UO,IPal$Baj8:mju/[C","qqw4TWNGK(ovL4T-L|*wgy78JTw.uw=C3~)Z@+?F?229u<,4;61U~~{3OodT/+eg","-]L>0toldTW#m[(%N@*,Ay`['TIUadTsRC7Dfln7]06Rqd/{&!zXFJ/aZ,p=M%ex",":APyV8kzu!taM)NIYyVyPXnRz^[,x}}z'yWO"],
  w 42 28 0 980000 980576 80 2852 [",}&nukK;zyY(uyq^T*>&VA'|j.k:]Ej^hu0YR27lYLUO?L[7K@N#Vs#Ub]LKEecT","Un{b#y.+)nt$ste]$6V)z-3n)<H}p^IV{54zAK~A7m4ma^v'P*)FLZ`8*21f@$*I","LCb.7Lhme8GGu$^[>NSc-aPuaD6NOk=5@!*Y-ecwx_[_M)^[cm;][`bu4HgpL_d6","jD6S!xROI39wdi,s|#onAL)|@9@n#YhorI0R?$gXq=*4>yM@@1X?O(a?dA[s;v|*","<I'zL{4!xEb7='eT@+KM0U{OP?yD(l_%@A_HILsmN]By0aoxji.x=mhx2O(p:)^6","Br8[V(H@gM*-aD=s44Wn5R!yr4nWlM|#+S_7SJx2Ib=Qo$x-T8C,g$~K#7c=25G'","Nd&vG,ql.:cG5E0t0WI'^`)GRehcCC+CkSXl?#J+(U7j,/>X_x[/lM%'a)+udzi*","7$7zRarkfQU=.pY"],
  w 42 27 0 990000 990576 75 2579 ["9esL(d(B:HRop&RRAK|;w|T)mD#<]W@j@5FD{FWca#K3V}?1f7$HvDr'p/{JE8,w","CQ'i2Qo`na,V)X!I#0za9Wky1z2,y-roL=Mjd5#'XQlm&tdA@9<_A=8GL90UKRxe","9vT`_>m{Me/;h@HkK{HgnqWp:d|J`SoOaDD!$D,brKH|#a`n3iAl!R8Sn0A8?oW;","(uRdc,JbEW)&9NjYY!g#?i58)4dl;omC/5Es,`b/#O{m(.Fbs]ubpMc?6blqpwc(","4{A+_H[}hShCDcSkKQ1_bYYo_,^,5vKo%[LG3-+G;Y2qFEI?&PFWfjYGMk'g'#4V","@(+8jZz<tNBY04u6uw@y^!2=iMa+0z>L]<L'_$]?ih;'h>Qw~x}{@0>Ogoh/9*ME","#TWp,JXU;;lbh.6b~%r~hfPnh80P^}KmDx1jw{xS+jFk&nlnYj}"]]

private def r42_16 : List (Chunk 42) := [
  w 42 26 0 1000000 1000513 70 2317 ["<`LO~7L6fh~;x$F2ZvRvQ)&,6g9~yN~G*S@5KqK^Q{5fCC87VndBlF?&xJ&a*Zj)","7]Nk*AdDNw)m~]8lNBp;o~Z2KXmG|6^Q9_Uw>yWMUF=19?ar(5@UyKj}*{M_isSj","fe8)/pq$~?Jm6GOh$(VlE'<@C8}Nm&Wa<(SgCV&l6-p%}-D=DsLd4JyK)ca3SG7,","g4;.A`[b*k.19[Tq_r{NE~)OTP!0p:0T>zeEC-PGY+E,-0j'd9n>$xR#~Wg)jb5v","J#=.uq]OIdlhf]1*(L*L&WI<7nm.>!D7?<~QP3RR$tH{ip2q.W!ifIyJV=P[(xpz","xG.H3esEl(~WO?gY@H{pe[`c/{i@m[x*,A9`Po/$t3>M4qVN0V/v4L~ob.<4h%Tl","=OxQ+yYIu-8KNJ)TCs}<-{uj]WB+,"],
  w 42 25 0 1010000 1010512 65 2072 [">OOQ]WHt;TUb72Bf.@o,RH=SowV%c4${C`8.(`+:C&ki>]9gCKqfV)=?z}y;%OoN","F~v`Ox>%HUA<bENxXB>7W0-bE(gE$gpD-,{I!8HEzdSOYSFonn{FS:ZND}@zXyLZ","<z^;nWQP;B_={&e!EJZX/^3Q$~{4QY(Jw+'m{#|N_^!bqS9WH=#l6<6o<?'K#8V*","vA~mlkuo<SFu]6)><@)wgw=R^.9u.hF:L:DDcdO^F2g-k|l}KQaa>Y^RvFIuM8#^","UJYs+O#qp`0}UY%%Sb?;bp!?&&@l<wXCtNmn`!R$tQml{(I!VHu[ue.)b6|3fgs=","Yz+vy#Hwp]8H`-J/>f9nS{TJt,<C;^i.lL[<4m/lgp@SpbK6.$LPmSEdXt}sZ+"],
  w 42 24 0 1020000 1020512 61 1871 ["#QkCxVekb0H{V[k/=(Y+:m:,O<Y.3a'P)d?hA!fc2-O#i5}_tIN^zjVDh8J4>&@&","1~0J#B/[x!rL%RP&2kH{8+&gEGYXtZW_f_bLY).y~HR1e>Tzbw!]pe$.Jq5'Q(Wr","h~Exh0T>_F|lpR6'C^-&$f8brt95@;~NYD_,00NY+'2w(]$wqv3pFKbMT_%vVG>J","cyym9I!4k0V,RD}hbE{!_/]sUKIFm'Hlao;JAOf`X;[~m:O9q7Cq)zhL,cH65'~B","w@]PWj(YrnD6nF-u.K&~>?l!A)l!w#2N+7+~vuw^r=4(lHQdi0S)sxW8OQvq`vwW","/&lE9a67'wQpY5du]){*$ahdTMayZrIg:"],
  w 42 23 0 1030000 1030449 56 1651 ["#%LCn=h&DI-5kSnHN&(,S2d,tkdI#-+XH~3X%RouP/[9?{yC[y~6KDV2se+=qwjl","!uoG/U,RPw8o0di9>ohJjHKd=^c>NEqh'/9cv/>[1s`d3f/]B$Zb}QH0eV%F7utz","QD>peL=7EoVe3_I?lCtMlVj{ksts&W^)lM1wRbr?#hz[5a.ZpHGh7K#$Zvr0]=&C","%?Bw#_x+6Suxgnr8}4g7~24[XGB}.S9+$G31?`YgQ}mOO]&-I}E6abY*eolVUSrB","T)bp?h$?h|9Tz{Jtd0='nw!0,v+SbU&R'MK9Xy2JF(vZRQ~7:{W$L$ax<`C<:Ap_","+i&qz-kH"]]

private def r42_17 : List (Chunk 42) := [
  w 42 22 0 1040000 1040448 52 1472 ["Fh0d.oz*D68r;]jnOxJJA1`0ht7W5l|hQ5<IEf!0&y$nX`;'Hh*WJ/J7{h)$%kAK","3()8)I5j+jB6$xf74)x~z@7*1.IZC=;Q)XdZ]{`dtvom)cVfg>D<Kb/L)}p_2?:s","Cx>K.RQ7VWcYTDk$$?YezCw5<+/RE0{oy4ov)eEliZ.9b8bd*Q^zg]gPD!Q=g*hJ","*?!D)j8g/D}hfLNEH?Xrm-zJsA}{c06(^]68=<fAv.,5m:^/}v]Z;X__W06t*YPQ","'aV>0!|L9A+8x*aRr%ppwUa:jJxsr{sy!^p6.t6_/0YZ`4jK$M.:Hz"],
  w 42 21 0 1050000 1050448 48 1306 ["=@~O[8Ht1l:1NMidX}5QjafQhmq+nJ&cHi8>W[,~ssuLP8C6}@JB{`9~SZy1.Aau","Ce.X/E(IR_);o1{G}2y8E8_2j=rQCYMY(o?#-S#r7zwW2#Fp)|Hp[;u>_2T{W:TP","cB>M'`[98uu>b~_7XOuq3quxRl-IMcK=@4jg*)pTWO:4GScr[vnO+~Or!~PL+ZRu","{W*gL=InZg3n);{d#)v2PpQ#Q<.$Uqb+z+_DtvN]LBq]7..Jw@,+AIhF0DK1wQ0>","%ig&zAAgcRcd|%WCs1J0KlX&2HR^5m"],
  w 42 20 0 1060000 1060385 44 1146 ["pvdI)!YS|>v#YchtU1S?k2*{HZe#2$Y[DyeUSUvk{0Hp;%E^,VcqI`<J[yhu)oI!","Y6L9cYxdWEd$^u/Xr2o=+W*^-:HR+v(BC:5WT.BIgjQzoS!ukhrJ{Bc!h-OnY_?w","gQI4{&MoNVa3,.[7,3c6_r'{s1o6;<Jrx&4)XT`K~XB-8Tb.Z}ZtjFH5_14c,.'u","KL#4*W$t]C>^BQ:_Pd6LyJK)$|1NW6&ezks-;dDQKMc3I)g~T:@8p<(FKm?[#Vu]","#U+5?DO.Y8tG"],
  w 42 19 0 1070000 1070384 40 998 ["tD{.F8AXJ*/T$;rB&C?%H,yYxlvDu&M2(Hv7s>QPYlqlF8.Hs?}0Sluw?.&tEc7[","&xg`=.S[]{8Z#(~5~pSFmpyot<el)ZXl$%DWdDrVxpKm7SsLXX?K2}?{`rnwBL?(","x5u%<3eCdSF-LY(Ck{/44;?D#n+Nhq7B2;kKhY`|@Y`I&y^-y(pF.M$`jBKaMx/}","#t52}<;FT5diAOv{F#x-+?wCb}i4$`wf(DoN{aBcYhK(vJvdk:0ZG[*9D8lv"]]

private def r42_18 : List (Chunk 42) := [
  w 42 18 0 1080000 1080384 37 883 ["9+k2)ATarFa(^E}eWIQpj_x7-2/r'~`KeTZ{D:/pRI#J{YCp>I4'dnE5y%>5pweo","u,@%HjPBq)~%^g.,n^kg5E%*K:=%{9|$?a?eq&F>=F%h!ia[<@Uw-DJgdJm}{a,j","f%4>;t[C9vvMnzF7@W*#GLLl2tqPc3j]8+A,^-aM/[Fi{+3F44)&MPB+p@33Ko83","#fP&X7b10}4HK=[o{NlfHIs0~2Q%X%%yR@-Vy(I"],
  w 42 17 0 1090000 1090321 33 750 ["C->9~)'iQE#<aoX]4)b>v{OX:_<=t'4}=DGs_Hg5-hF^fzK^9l-kKmsEQP<+SUyO","aFAVveFce$G/$/=To<K!xHd+~^WtMoD@eRud0J&.l+[Dp|h8'.^VI$RXCV1A:pbf","j7bT;qv;?mlydYDfrzD2]2cL$:*PXj985GT47#l|%h~E2M~/L{U*DrYLXX9~&STC",",7B(M#nnMUeQtd]Xdpz7Z/+"],
  w 42 16 0 1100000 1100320 30 648 ["pe6]:pUJAh5~XIu-Q`p3hvR/p3>u($kw<?kaD8!V`g*7~h<&qwh242E4A>mvqhO+","o?U=fyK|<Rp?d:nHFf8Y'`A.O4Z<y/!3~VQh8]{o|]T1eS])H'/I*Z6U|IW]6{(V","qMQPFDVFQ=<DJ<4HaARnT4^#Epyp+{^-CILhtEB8Zs1g{W`=Dw>qb`fIl(@4bJw7","/)!Z_"],
  w 42 15 0 1110000 1110320 27 555 [";@%ZB=Cj(dcZv[C5zBKAib)AT8NG~?jF><:L:KmpDN/2iV2FHd8B*&erL=O$jO-!","'=$l-+wfc}OB:zF#r3zx!-XBhsv:o1~Ny%y.)jc(B]=.[(vh9^*XD!rCGxI*<A3U",")TX;J==(oUKAXn9JyYode6Y!7zhb|v2p;bbVT~9-(W~-xgU4(VN"]]

private def r42_19 : List (Chunk 42) := [
  w 42 14 0 1120000 1120257 24 465 ["x'}KBYC',g=yRxMjIET^j#}']1uVQI0|YHa&2Y!4$xK*USqPuen5,1F>:?4X3W*6","ui!jkZ{|uLy1O+!<sH|2/KkV'5HS3k8%r^Xi(YU$GGiHPPkK`DHj(;>mSA/ugP=^","$6u_h`mdQ'@b6<Zyli4s--PsI]Gl)HSm"],
  w 42 13 0 1130000 1130256 21 384 ["GK`{0cVdA)g/P{!1/O%c7Kjf;}mr-w>uN3)-CfI&7bc4]#t&-(xz?.R$AVm[tF?;","*eN3UIz/w8#~nLHIy=zh}eV!;;oK?k~9`d/I-@6L#(p,_IggQyRYn>W4nb,#=45,","6^U[!rmp`XW`}p9_{kvB"],
  w 42 12 0 1140000 1140256 19 327 ["K?BcCzcu:YBZq'Uhx'%S]G8mdkJsb/6@ZlQf9e[HG/}r.$I0J_v|g$~J<;m3Q;(-","$?Ly~cADh=wd;l?vBC1Wf4sP45b~RmQ+818OBz=zhPK#<RfML>'}u[(ke8xJQN"],
  w 42 11 0 1150000 1150193 16 257 ["Bu8TLGWt_&@!N+S2DuqY47fWI62z|S;zjDxs.[CQ=*po<iv27FgVq&n]|*2SF=+;","#6QV%|~Kx!aTTd>-SJ-/bqdo|n%,2u!j6{.%^AY53iNb>qRG"]]

private def r42_20 : List (Chunk 42) := [
  w 42 10 0 1160000 1160192 14 209 [",%iJ*u,8iy,2hI!9Tur@i|Ktq<E]Z=%*ADR#l2:E{o<)v+|4Y]5/@#^3bb@i.XX_",".Pa?N*p2yW^eP=ihx|a4TwzAc0FQN0"],
  w 42 9 0 1170000 1170192 12 167 [".W{%CM=#K^`@!ra9K'XudVq'I%,6d.a*hqX)5y=S+n}ALH}Fp6-y}m^O:QEnQLkg","#-YCDO6D^OmBW.qSj"],
  w 42 8 0 1180000 1180129 10 127 [",gWl*]o$;jG?XcR^Q:C!|%&8&7.PsglBO;o{z~KZu_R|`9c;9r1/>4sAy$21dq.6"],
  w 42 7 0 1190000 1190128 8 93 ["2j-hsq7:xQo_#$7`<m14WJOwS$E,(h.~&Zv^z3[2oOkYg6EBcMva[NG"]]

private def r42_21 : List (Chunk 42) := [
  w 42 6 0 1200000 1200128 7 74 ["%fZu]gvfB;_GxTkz.yN}Zmi]$ooU,0f['3dZ+oR}Zf"],
  w 42 5 0 1210000 1210065 5 47 ["#WFf];{w;'$W8?MHRE!J6L$+hX6~+Pqdl"],
  w 42 4 0 1220000 1220064 4 33 ["&x}kP:(BbI0HY&QB*tXaqMpJ"],
  w 42 3 0 1230000 1230064 3 22 ["(Y)RP1uQT:v:-x8$wV"]]

private def r42_22 : List (Chunk 42) := [
  w 42 2 0 1240000 1240001 2 12 ["/'!;c_(KvA"],
  w 42 1 0 1250000 1250000 1 5 ["<V%cV6"],
  w 42 0 0 1260000 1260000 1 4 ["5;qL"]]
private def chunks42:List (Chunk 42):=r42_0 ++ r42_1 ++ r42_2 ++ r42_3 ++ r42_4 ++ r42_5 ++ r42_6 ++ r42_7 ++ r42_8 ++ r42_9 ++ r42_10 ++ r42_11 ++ r42_12 ++ r42_13 ++ r42_14 ++ r42_15 ++ r42_16 ++ r42_17 ++ r42_18 ++ r42_19 ++ r42_20 ++ r42_21 ++ r42_22
def rows42:=rowsFrom chunks42

theorem good42 : ∀ r ∈ rows42,good 42 r=true:=rowsFrom_good chunks42

theorem sorted42 : rows42.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks42 0 (by decide +kernel)).1

theorem mass42 (i : Fin 57) :
    bandCount 42 (i.val:ℤ) 56 14≤(rows42.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks42).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 42 (j:ℤ) 56 14≤mass j chunks42))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total42 : (rows42.map (price 42)).sum = 327240 :=
  (total_eq chunks42).trans (by decide +kernel)



private def r43_0 : List (Chunk 43) := [
  w 43 56 0 730013 730338 100 11146 [],
  w 43 56 100 730339 730770 100 10136 [],
  w 43 56 200 730771 730903 25 2138 [],
  w 43 55 0 740012 740335 100 10348 ["SR[&S]m7Q2+umQ+Vh[yG~i+oiS~n3$P2r;2/>=wyAGEEccDZG.h{wG)|ASYd(a.:","P=%D7yl&avtm<+uSip4mwCc@|?;;`ha:g[<olH]a*r9zsQO&+gOb,e5vh[bjb!!!","=.V}SE=,3~vA)Ll?V'Tb9#wb0z#v//O~h"]]

private def r43_1 : List (Chunk 43) := [
  w 43 55 100 740336 740769 100 9268 ["okTINT9A1Z4ACP96U5hATu*b32M*M%{*I.!E~e|u~8#zuI];{YsMch12*MfxCL<#","15t*5mx_p4QaN6R/T{w]T|$W$!oL#p1j/Yr|.Yn[q)a8N,]r[WM}Ev.Zi,'QOTR*","S5(pxT2Px:1ghl,p+I&3y9]C6j)H4fEO:%bl#wY"],
  w 43 55 200 740770 740902 24 1951 ["[8ueWDB/vux^E<^Hiqq0CzbvLNiy[oT4?L[<?5Bl"],
  w 43 54 0 750011 750331 100 9707 ["[(Bw:TVW(4H^y|zu8>7A|]yhD,}dwlQiN=;1G0O>R4faj@N%t'E+Cb!o<{SZ&[GN","RtcAzc3Q?(E5U$0].xDghMJ6k@q}c'r;LyGL-7B3X<O|'29rK9xkdgTO$&vKMu+T","X9:gI_b)INtA4nLM1]g?Yb@D`,w#Eh%,+?XmR.UijS*+"],
  w 43 54 100 750332 750769 100 8580 ["Q_;l424kN]_sZ6k2R#OP%T&%tf#)M(&qjeh/.vhqIpBR&%hE5,@PA0a>uy<IP`h?","K=^<pOIL=CM-yVfa=34k~q73.>7|XUGC>zN'GmhZR<AhZvI}=:Klwv'rx/4($j%R","1#97lZZ%w=rKjUr&VWkz*[sc=u+Wdb#)^)M`<aJ?&0)4ixL@G%ot|:v|Ma<"]]

private def r43_2 : List (Chunk 43) := [
  w 43 54 200 750770 750902 23 1803 ["'+^1A8bGaWH:?opf`l(f8H(qA?eFTsHd&IspB]5a#,]nG>9H#`"],
  w 43 53 0 760010 760328 100 9232 ["zO>oDj$uB3TRjf-qFfC`Cy(;&-#@G1vumguqiH,+tTk_(>yC=6~AqE$R`kep4nON","R4W~kkX&)/{)##`QkBt&vX%dq^@/#DCWrh!3`Jw0cRpW9FJ7N`=laaZtop2Y*<(F","P<cw<O6<$y;xJ0@F~4iD+S5-9|k:V#Av`,E%]Q[o{7P-d`A_C$*%`qiqEnxBvG3^","%7!#"],
  w 43 53 100 760329 760769 100 8084 ["|w%T{$r`iX=xIV^fV3L]j{JZ+f,mbf&4/sza{]S]hj.QuAJMqpB7Mx}1Pd**<4QW","|v|.hny)b$T2a}JGJU:LhxmpjDKKat7F3?pO7O<-OI3]pBSHi^#WV)=[U!MkGv2P","b/d8ye>!F5}Sue{Z*JAq>4}aDW?m_l%0C1^(Wl),jwZv9>LZGLglY.h4o~Qw7C@u","#i%A1S/M)Fj31(JkZd:~"],
  w 43 53 200 760770 760901 21 1594 ["`>?IysRS^7u}4zTMyh{+2-bDHZ(R|W~vP4U]`7v6th`u`'CL|CY/Bz1Zm"]]

private def r43_3 : List (Chunk 43) := [
  w 43 52 0 770009 770325 100 8862 ["Mk!*=3R&C!J7k8=.|Dz>f+IcNcfJ1wkGwf'ZnT^vpKm=JZoX|?nlIVS.eo31tzLc","~i[&S^8p!T}o92bq$b~C,JZpbi4:s+E;=etkK>H{jgSa5PDeLkLW,-HXcxp3^iZt","BCG@fjPj</opNNTR@RTf|}FD/5DdY@Q.lhY~N1NaooF8gcoE>RIE(eq;${:^Dunk","22w,T%0tF_+*%*qNI9*B+p$4%9$"],
  w 43 52 100 770326 770770 100 7727 ["oqy=mQ[&aoHG,!}[}F.$ZU>V339kau=Q(M6eqQvY.:LTn8P'Cc&U?$ckCHzgC9N[","?9mlRH3mnPvcRVDi?5J:`A@iiqpI8[0O'6^~Y4QiW0TC>:p<9(dF3]6O|sMVHi{c","&sa(A5nII%_Akay#XSG3fWKMo$cfL][,f7Tm66=$h[lDau<Z@z:Al`0|<Uy'Iae&",".IKfUVF1gn`<gAcT`y%oX:UCck7lej/X]Z?^@d<[ISw3S@*a2"],
  w 43 52 200 770771 770901 19 1395 ["H1i&hIy0))xW$El9^6TOo0<ZRCpG#w]5i7-^}.k_=F^?7F9xHq.<(u"],
  w 43 51 0 780008 780323 100 8617 ["K8qIC}SD`VP>uB1Q`*+_RLtYu1d[!!(?dfbLvnSHQfF5Q~[RFnd[hs<Q<l[BTrFJ","%FIq2ZpU/$82._X#%l^.}@x?vfKQ>2wvpJ!Tuk{H>DU*T<Vig5*<6(Tbyh;|H5y]","Kt~~/mr0s1XE6%t>5lFD!TYB%p>!]E;fZ~=G?zG4zt~R!KtC$;ffDA@2{v)rM<0.","p#3G<*=8.vp>pm#(nBd%=#T%}~TO;wjpsjt5rDbzrAn?>[qj+A"]]

private def r43_4 : List (Chunk 43) := [
  w 43 51 100 780324 780771 100 7424 [">bW:H.?=?layj=Ifj3mWlBDkO(-PP3/_VvGMb:7>RUka+!BW8{KB7R+S]rU5#:g+","Jg%C~@*GFX$N4gZB4m~MI:tC#B0)/S8q&-3B%WFhU@&,PZ1[I7AP'xV~ES<ddHsD","d#c9R2x^eZthR]H}96rKLYrf8}vK*$H)?Os1F;}I/[{w2h#,!w{|.uw`%6i&bN>I","TwIxQR.uYT'adbA`N.,BM'V)hAZ.!og-55|!<|W&<sg-zfP6y%o0Pp%oNm^P~EOK","zd(p4s;:3/iTy."],
  w 43 51 200 780772 780900 16 1139 ["*kc+hEl)4P3rjU1Z~lEZ,n!5Ggp/GPW/@M?B+XA%@@M`a.t]T"],
  w 43 50 0 790007 790321 100 8334 ["MKzs%)^!?|?k{|>~HOZ#_`VFuH(H=X,7`kppC$jh>L5;n/r%n;'um#eT@o=9:N$2","}'t]}$Xq:v'm^:C7_?O$Z1;E00}|M).og_T%*q,M,k2NtK*0d^U{vN)'^FW<l*17","bZBIT;(Y'tB'6;-F_H~LN2xLYI1{rWJO-%,fo%Vk77v<0yF66x~~xs#F'8yXng%t","02<(PG[d+p]+m9'{+i)SxD%lIoio,H6,C)Fay=:2$c&ius$Nn9#ppZ?Ok>~9l-z4","fzT1[Av."],
  w 43 50 100 790322 790773 100 7151 ["&u9*{dXXj15o9G,kj/efL[)!cRQUf@d4^v4|gdM'#$Fl&bWs6.1Q}*WlE~.TC4ja","Y/0W&DL=nRw/OM.]FG=penhU,h##gT~f1HQJS,9GP[)`wP#_o,mtVGh>Wv3_fQ55","iFZp7;t&lBAE};2%&z.<V$;E!zIJtH((*.,g]>n@rDe;8c4=><v,rA>$;oslFG$!","sml1-PQ{f/z$.T>hUu$*N`:gd0X?]odrVyv?oca25%3.b7j+k<0Cq{x4n52U-.sp","48Cr,V~jjsxSEAu2p6a0g~GsJfXBOO'g/MuS1EC#z}ejz"]]

private def r43_5 : List (Chunk 43) := [
  w 43 50 200 790774 790900 13 901 ["Ub9(zJrt5E<xu@h*u&{7z!_B{[*D!x!'~{*~_'Y"],
  w 43 49 0 800006 800320 100 8092 ["E`]$`bN5(~cxUS-]x^$$b1PkcH|{jWAWV_yqvd+as#mxkV-ZAcygLb6v|!ZW)4N{","}vAzJvmx.h`Xrcf9+yc>~SD98.dlzeTg;M=e{)Z9qZoW5.(tne^E`pG]s3NlUy4_","Dr:8$.WANJ6;kZ{}JpGktUPMPdc0dsnBI3zi<CpAlBE9k}%(+a-'$b<t*MowR1z1","9(bg9gQTp3WM[!l/MV)uF_!b~B^N2lbqTR#W]Y|*Oo=Bh|*~RA)lT5Gd+8^XJ4]~",":4&#?q~B;8j/_VM!Fn{2hcT:jsd>a"],
  w 43 49 100 800321 800832 100 6895 ["65NREs[DI77v}G*6u6.#cQXH`a=m'DP5jlf;m8rgZLT=Q-ps@Ji707B>&4#Q?U.u","#j^`M#WKV>9RLP2FKx&4b1NZEZ;JSgC}!VR)M*)c-1>Nx{R8Tm;dU6Pn*`+QZrZa","XTw$,COrg<C9s%@cs3X`)f1RvZ~g'$b48aU0bU{^x<+4qi7{z2v+MiT@wiGfKrw;","MMo/TH@%@]&!86RSWbK5da8d5pGznjck:cxFqNx&~|SH~$tkjl.bru')&zM?5X3e","{+2tg&l./xj^r#-FL4=KfMu$6I`jSY4f(D}G6$!c9q.<QPDBKft=OV/Tk.Hrj3zf","qUufYhSY@:"],
  w 43 49 200 800833 800899 9 607 ["#S&??gd2orC>be~A:T93+0S!u&8f1"]]

private def r43_6 : List (Chunk 43) := [
  w 43 48 0 810005 810274 100 7814 ["a~KmCm|R^(,WsFJ}u}1qO6P$Oys.~nmrpO6`t#,,6Q}bH]1fcP=0.qJg-TeU<u]2","*4D/o[H$2hSS#}|*{%z(2l~Zt;Qxt_}?nMzzxg'H9X1xV6{L6yB6,2M/#37b+cPV","vbuhE@}&iYm+=w5<5>I|N?)VYPCt8<<h0vD%4Rj0JGT({=CsI`4G/ipkf+#*|JQ~","C@F&Up]<.XCF!q:S{,Ga`ah=/l-4ASZEsrvCC-,U$~=o2o1xU-U~3atT(;ZTX1%O","0}?bX[:g@]Y;C]V9Xcs(u|g*f#Jz,N7(h'lDS54_K,(%yccMU"],
  w 43 48 100 810320 810835 100 6661 ["+1`(1?R=30bMi(u~~?M$/DZVkn@{IZC,S4TP#FN)X=@'^4iJh|`(@Gh&<CSx28Cz","tMI(thO8>wX7Pw,|&!>9eE%=gB9iB,Z36p?j-U%y3a;P2iYB^6,-2-4(u[4&/Ipf","SfTr#_Ny*D5':u!_OtrExC8h*TPYZ*[giP2-&V5NnhbhzQ:/}I[+BXL@+pPf]vK2","SK!,*O4rkcm0%Q^lL/kWQ9pA7%0XdI]&mHp@zlOfqDvzQ!O?8_0m2EprlH2'tym[","wfL9R>`c`~+AP&lJ5CyRn@iu(U$<F<5M2#hBI#xFb5&zeSiNSp0,R2X$r|_trc6U","'dHH.cFG(8MMl@,zgeri]2*7%aC,`17:.dN^CL`0"],
  w 43 48 200 810836 810899 5 333 ["(D645-bBYmzTZ;)"],
  w 43 47 0 820004 820273 100 7587 ["g.Hg=oxf$fbK%oUZaWdFjg~QfJ05j$/y~Kbj;R5hg.Lg@pFIci=RV+hw&g3?x'RZ","!BH$z%Fsr;v3gq[R}o..bfnfv7=WHrGx0xwNj6H!CoUIt7e3+g5W)!Z%[UnP(03}","<qY5?-W8Qi':op.5}Y_7m;0+Xk+B=WUq6a<2rS#,cR4pe|5B|!Twg[Bx?N{:mO`$","{-['O&wlZUe#T$28tIgPsW%bd08RWJ+}DM@Uo~lHWAhlCc@dh^s6y?:f!SmvS84p","6gwj3}qoz?Au=cR43KLB0C~']-ghcyo92v)|0`:Y(Nl@^Ys/QQAz(C36aeP_vQUa","$cDa-"]]

private def r43_7 : List (Chunk 43) := [
  w 43 47 100 820320 820898 100 6438 [")ueif*?k/-TE$WnW,T2,VK=wd6%ZxY=G(TtFxGdX4'v-LfxkGW@H[?aU^QbO6w+9","}DSJT7oW%gGAzz.#-lo8ya8l}<}v0y(;@PC,W3rN?=X.zN2ZX&+-/tzj]i[);S`U","d41:b%jr;Q+|tdUTx<0~3e&OH&/]4fV7$2s8vgBC^&!im0?oQ}SlJm1eVZYe2)FL","W?&8S(g^ucpBm;&?6C>,Vk30d%eyM`bPh>9e!*6vZqaI.}H?O&Hg7+>T&VM17|>P","|eEVI`%WGq[O:hvI_Qx~S/KRg>>rzy2,M|LgW0oR16ZQ<)tln?2p=~t#uhhAT3H<",")!K{z~h3Q~'hPXzWnoNP`r$PR+K=V3R')3S`zFBiDAd{3`rdclkl@d0}z+jX,:"],
  w 43 46 0 830003 830273 100 7319 ["`OKz;>.JBlw,L}|oOtlGoI}5F:@FnK#atjA@35/c,19tSb($)I3wz^|90^!DXAW.",")]oA8A+QaekTaX~7Y=ao!WB`#evo[(ldq{KIlp+b]I<mUVB*ZP[WTRhtCmkzQ(%G","v+ek6N;*9]-!-#DQ;oo?6Y+)SUd>sY&YS?j8`Ga[0%$fh=U#z]4P*x2,T6UD{a#Q",".0dbA9o>Qt$*a.eUnw7/._4R7a~![`]9Fz2U#|-b|3_o#WNb~,W(Y8{<woJ?X-<u","m}W=1%)7QdbA#B/x>mnC&e*_f2ouqwA&ZETlRS~T70^g=l,v~`?NvvA3ILH.*F`a","&`thYczxngE.,R@uYb,;'y%%F?J"],
  w 43 46 100 830320 830898 95 5920 ["OB+C;1/P%0k6;lY+=?@V!q)l1D1k%=H#*,jfR|u@6?Om)_tZ-U!neK~PmRdd*VwE","'WM5*0lb$gu3]gx=(ikFu[HCu|TYxO;!K1Y7.r=YL}KxzMB$V&tF%(U@h5%dM.G:","<q%Cr;C9=ShYe2cz&nt}4v$Wh*~nXkr#Ky>Oq~]3/3io=u(x_0cPmo],ol?|MJ}J","D*Ml5K$[',:D_xri6k$]sO/nbsp/,NcT_OFi8?%+v{~jB[:XJxC*ic*(oTtPu]J8","iLz_+PXxP9nVm<a&tU8bedYp33Kp{C-*5u}-K%&F/a/+BkVNK'1|KgJj@hI)6D1q","'A:9!.v5NPpznXKa&i!6':3ME>4{Vlqi@)8k{u)M2w,T6t$)=hd>A7?P#XL"],
  w 43 45 0 840002 840320 100 7095 ["j_mX5r.@EWI(}a}SErpbVZ)*>-Yfm`X4]at@]0Cm'R{*wU9OMw_P9Y)K/t5DJ-Eg","V*0Xrln1XqblP<?zQbR<DZ`p=s-H3t6=(@U;OJ_Q!%gV|H7xWYvYXI@,9k]acbcp","$g$yB?'#t3nfImVooOx3)Dxu4q{zR%^P-$_K!$8F09X.l0Gy_xL^rF1#}}x@r?wO","$DUq)Ig^$7@T|eK>tJuK#'I[gIJlnM-vgW_:I[.d/V4.+c>M'{B.r@_W%nwb>T5@","ddDIE)A)dZF^M2B;_}Z4XB2/(mb@.C.lNq(G_hq.9tna*L3[#`5cl6epsMrsnN.3","&jyxERH;Epw6b~qevRD=|Lf?E_kP$*VUUWsxstM/:![3OIog[IOYPDrj|CG["]]

private def r43_8 : List (Chunk 43) := [
  w 43 45 100 840321 840897 89 5359 ["+ZU5i.ix/P$}w0eCXg[e'`Omk7yUO:4FgE0)wb6O0~},8mnzxxvg4]3q,'NssV0m","SKf_9ea}<C?l#Qww5@9sEz0^o.P!/jM/YhskBH@VDa>PA#-Q{g$5~'[O0,p9}<R|","Zuh>+/|GsEgT#Eb`Tgd'}kh<c+0J$du-r$:Cb0&L.G2fWx+T|V11n7_pVg*`P<0j","[z5ZXQ)Qwkuc]S_!NF([vH|x{V!dr4),os(:BwJN/q7TwwF7t~q_@L#P8xk!oE*M","_DG?smgRr#4Xd?)oCeuzxy}?E9.@A9}/$@:d1?6J+78l'^ma!nm{T;Q$PX|)wPcd","&W._A4fW4BVYBWJ(,kYfM6^T(_oCXGlPVo@jR~`@CTV0N%"],
  w 43 44 0 850001 850321 100 6808 ["LOY<Xt>(&@78O~T^HZ0O6r:q/b*2t`P9?K]HY3Z`XSUg->J63OTF%mX.|`T!!f^F",";A~N,Xi'U4}z0%81*ta/7m>js%|g`B_Y;0O[!bE`Kv|nb$/yVM[y?16PB|=n_@<@","]T&1ph5T4a=I0(ckVC:L%ik9?fS]bk8OPcMVg&Rw0g^{h6VDPt7/UBJBuCGSMj%O","yU3pg>m{MH#[#ub.`T}TfWo$XZXLud7*/3K_wA`}$4vEr#Q-E,C;ycU>@rN`n-f1",">ca(4#bqD5_eD(4qH&]2&t[PB>0<T4>YW>Fbr&0$@=Ro:|m:{T?!}-ZA4+T>ch?9","dYD$98TnuO,([#M&i+e2#lt5YoQeZ%M$c5COvP+(#AxmyB%c5?KF/Y-5pc30xR4m","$Hj:e&w^@WF!ap=sAlPM{{[,N:vE0(u!B"],
  w 43 44 100 850322 850897 83 4839 ["]hzb:sd1UC+P<M5Xyv1)u3FdmyUw@,)C>1y#d+hbcPBt=N}+C{#Z-%n_2O=ae$~R","2<[)|j$UsY^~koY8?HH1mSW#;Zmw.vmT~gY{B)7SS9]k!g@Zzg`?qZoO>d$J5r@{","b!L*=/9gv8F8l.7i[tU02t?qH{(_GJWh4<Xx=,Mx.M|b,S,P(vf2fe=S]+,|~u>^","T`Z6<GUdud>OJGQU-B0ovdcg~i+UH|5T?(kycH'N52g|n68-[!A)n6d!)[(|/j`o","n&<0i@o}1)8$~Ps=BdNP&F7v%aO3MNwFoCKASLY>'l/TV9<%0S:N+O71Nil^/?qx","*$37:X=QH/D>c#7|Kw.)Jeel"],
  w 43 43 0 860000 860323 100 6546 ["G;.{Txb6Pd`M4D0/X/<^'P3/u_*/Dve.E;Sgb7i)+P@I5pe+%t|u<}m;&K?+kIf&","%+~vjTObd9{dx%!DYf,L:f!@BD*,?l}834m]=`nMSt^Z^*9'Blz5f'?0{}b0wf|m","L9`5b|n^R^RDVA!feerO]Xj=4K3h3'h<cY!AH+9K(l5amW(MhB/S0;*fDhkq@0I`","hx~yp>L~0#}h8gKuWD?szy;ix1BSKc87$1@p=9UG;lj8gi;v`?d>L=r<~JjcT{~=","MT:|4o}]}0['==?l!z^(!bdW?`?%'czZ1xAu3nv~RNVvH~*lDLj]|GC/wNDDUA7@","(dr4#.k72[XaU({}0{#LYc38adb%+zbR/r,*W#Dz?S'4~:GSem0yB<I*yNGvJ&T%","#acA]:f''Yz1X9e$I2nHv-Bven;}KS(+rL&3-KLL)Sp8A4Fr3a)k0h`2UuYQ"]]

private def r43_9 : List (Chunk 43) := [
  w 43 43 100 860324 860896 76 4291 ["|16t4B.XqYjk);=>C=:@fvuMBOEOC`Mzz,vVX$]p%^~I3Np8-LxdHK>6DEz4&VZG","D^.yi=)~RB1c<fP1%H/h]dG+Ad6L5mzY{mP-zNKjoyN`VF{aG<Zd20$jO1:l6&>i","036}y2qSQkw*J=dl9QW<?;}2:8Wcq8!W#8-]/dIZ2^;L-otW*8cRKMO-WJuKhp6K","o[Jm7>LP%3=*6b;h+.D|12I7oMa~V{~6+c3@=|Ck;lg!B.)^*.FRGg_6}5ZpH[U{","@{c5#;[^+z+^S0Uosb$|9W|jS>RawF;cNnh^|:ic>_cKi@moA/z@~<9))"],
  w 43 42 0 870000 870325 100 6220 ["AE$]%Q6tO[+5j^f?S+{<COdk-1-%U-Iat#NVC@Wc(/wFdULi;=988Z`;q|e{:;-/","m1j!RE}q(CL8n|0'OtEtL6VWfUcV=:/Cq5QYVoQ%5Yb``ym|Y'd3@@uLnxw-nDG6","v*AoxjrN_5hxLPw9c)5B]a'l!-6Pu&xBw9m%s%{Jhl|0br%?P8d(8R;P;VIBq(;F","Q94:F-57[}.o@1^-.IIS]CFW?Pa|OH97],`Jm.x/;<mj_Z'12Vg6JXUs_q8ybV7T","afa;Po`:$V&p<Os=`<YONSv1eQ:_[N!k%^9'~XW(btM7#Z$J20fst~`9&Eb']wt7","m^rY<LFaMF?Ig;k2t2uv2BLfK)j=kfR3Shoju2!fDm~*hUFsXGKd3NVVy<&qgEP4","Wua;AzM~>Gw%:*Ek<x8]0B?RxCzHv-PosK4W;Nd%H/hyI2V[NHv;MyhRZo8D0#;I","OE*6-"],
  w 43 42 100 870326 870896 69 3780 ["I31^qQyRQCqmtaoS0,S5LM(u'`h./{9^u!:^<Sy{*^p_2LG,7wmns{ajv*ScNF;l","5Pf#)(aV.,{eMYeBS<GGu(JJ.Ks1%*todC9Mq~c6/+4,i~61s:OF-.PxzK~fWi*;","lU<D|TnyyOdM^^3Vg5[%vv-&!'vxH44egh3+:@FL_tr#])S9BwyS8a;bj55MaR@#","&JH-GmNU*W[A>'}vA_D;g:RUC$kt?z?IL3ytiz$xNIq>YmD{kq![pJ*y8?sR;uNc","&@}gPXp~$ovF~,IRsAVcbQ:ZC@lLh"],
  w 43 41 0 880000 880328 100 5918 ["@8K!f1(B:YPCQKhR}|uK<reO|6`:8lHu&o`Npi,lxh|mf'tG>WFFc<TsgY1%Wq(l","ix6PPkeZ;PojxQm5xVL(_lvL;To8;txCbCkoxYdV:ij!dM`.4ai79<xV7|DNB%Xa","AZ-Wr1wqt1&%];98c9*1RGm=JT-L2_<sjn(IP%w$72lpLibQ|qp'!pw-9kZgZ~eV","kdya*zOR4F**rVRGSd`~XH7ztE+hdjIoPl@eq/fs1i$#;A|'B4sS4#S-imSDX2Q7","=qqvXH*]xf^;I}awn4=GsS[+H6@;fwW7NGp_W00HJXtgUYkFe_+]<uo=$f{;&N;&","'WwmfLn5cml}u<[7>Ue>a6i+cv)t+q{P'NL_{+^>w)TC-76ns3zz(qpq=]z<?u}o","a,m39WEAz+}`b(![DGk/TV`B4+J;OF%YT~'6ei|>XE2gD+Fe!8g=MqgMaCUeJ@}'","#wu_GR2&.WM^^M!:m>9u9Cf[L{1lPN3DUQn"]]

private def r43_10 : List (Chunk 43) := [
  w 43 41 100 880329 880833 61 3245 ["'2Ptb,RrQEB`1vJFuh-{`YE2c`Frpa<.Qm#2Btl?HEz+4.{NV]a,;wDF_K2i?'rJ",";)ExrH^R6ifvu[d%qNr@f)-KeK==*up_oLDTh{{b8!_+_*M6M+,K/ZNSf{f1jU]<","n^~MMd5'f@yHX|0IpmJZzUIJAPJb**2$QTM7(i[g,WOOt''q[sX:W1obOordQbu4","*r}ddW0{E,%3JB]}0__ORY@N3fzknk}YG0*9Hwe9lZ0h1sGGp)=Mi?3>A9"],
  w 43 40 0 890000 890330 100 5634 ["=*{e-]/yOxLs{5nyettann!&|U8`m!E|~Cl:bXt[8!Z~F1Y_=}[rd{BwIs&)42'h","Sr2.XR#QY.NdTGmWejE+dpg~bMs'.[,g<?-L#KJ((DzY9)|T~nEL3YA%;-^8pzSz","X<*rB)(Df5g4p24@<lNuwzsVTdW>;{R0lNrR>@aBgM8POpC#dWYg&oM~`Mt3W_RC","NR,PXx{M#Oez3M,kYo,/{G?H}X#/_{u[>XED7O[hEO>6+x5k@T5diQ:|-#g||lcX","aE-u<vT63k5DxrCuC3)+,B8sm!@[F2eR_f#yB@'2|h4:P<Qz={P8M3~QZrYeK7S#","?&p<Ao*dX~$P=pQO&na+Akt`|uNh{o!p,AGp+=O<u&pSzthAz6Yye,$F}o@j}dNN","=BtNC/*wI1'OGEhAc,|&k,hAd[/WCi@}c]~{n8i;KKf5(}K(%n=pC{r(@],u#t)G","T`Ji{A;^i@:6xz7rg)'C$d;Pv]rL@;XgR7}$T"],
  w 43 40 100 890331 890832 54 2797 ["s*3B(AQ2X#7}_DwQA]PD8[LZh+O|GwvR7+xMEZAY%pJR,%-xQEFtNtv`kK-??jl:","Qn&QJx!wdDG/Jm%>L2,C;nvCDoXWST#6RC-gZzHJ@V0d`3B)G9CkOV}[hEvHud&i","'an4qZT0z]:mlxX5lqzr#l%b4)eU8#.;vPo|+,h)YJ'DM3`,uW5!ms4zjoKT1|:)","2~5Cew0NH)Y+mBxe'dlO<N{R5W&0%k`"],
  w 43 39 0 900000 900384 100 5373 ["93I*qQHljCnm//6~!,*uJeQ8L+T!84l`ew.]oh,%*pyrE5!I@JYvGXmuTe}*CDCx","@O3u)RFrPNPo-FnQwv<L~`n%jT3G#IhME617:w40~q4_rFfa:wNe:F1v#nHQ_+Un","O[^;%YO&*WSG9oASG*aQZ(K@k,0On#wo-L)szDT^xJ`iNuO,#nKmk~ke<dO$.:y3","B;Jx@`'52ed|+=+w<Z0WF7DS|$m=Kh?-/NHyTvgp`)b-zWf3&IEO*`8NXmzHnc,b","k{{;pu]>*gHEF15eY7s4M`(_riG$6X$AN/.c:GR47fYJ,`m^gL{4kr5+)N%c.FVK","zWA8c-`{94h6x>FN$&i|mtC:m}a4gMZYMx3|Eb}g6<k/ouDY/4D`]w7idJCKt+c4","(7D!n5Xcbs>?,^=4Kn[PF&t7L6ACDN3nO>a1;qrR6R2>j{x9SZQ5PJ_4)]){AZC-","5UEkO_p<~8x8Z|FB8<={{,>^U[0[#Apzx>R$W)nNtHUm+bx/%k-uk("]]

private def r43_11 : List (Chunk 43) := [
  w 43 39 100 900385 900832 47 2375 ["|$*c<}Xl3bz:2g,.VcRby{g6~1VT:?%7shu.sB=lZsK0tqQ{v*?O)7E#0(%$5.[+","haE~H50+U1n'&;mQx/>@02}OHMK__`/w6{Cl;w'&7W03n#,wPJ`9@o(_oWKZ@,O@","J/<f<<!;Un1d2e;$@7-8v3]Em6g#h%aOZEiMyT(PT>YpLF{2|(Jc9k~^cH,8;Sa|","2K"],
  w 43 38 0 910000 910387 100 5126 ["tV^[x>=QNgrCA+pBmv7ghZB=q/k$P5QVuO-]G_5eY=A?<=tt2lan(_H}jra$n>M?","QWYRZsmvi}!WA'+:kzsp02a;RZU?_%4^Se1{'h?bGE[cpv4DiqK?ywtOkNqwY8]h","5_NFh*>LeUVAj&W)ivVbD!)}S|FQ`K60~aH8nVg_l_{7yRnl>ya2[0%a4^S4@BJM","A;qS!9>W0^lio@+u+FjZc$w2bIiMR2EzL10~G'Fn~GU-#~_flgk<!N1z,la}N+T3","Vaf9C)W5~)uPHQ#2TkZV?{#hm}=fFsYW_JB^WGAS4LMz&za&o`TES%?,2RSyg?Ef","._]q_@wYKDlN,?J-lRmV=Hb&zWdf[x=#gWSR;.q]88Bm@ywBchTK3X?uR;!gYdA!","ZBr~mP>M+oOgw92DBskXcjw7+ITg}-4$lkXF!HN*^u=merIt,NF9b]-VZT_pln.i","&4CqSNhz&SQG<BR`4-?Ft(P%ltP=Y/,I5i,Q:;uuk/]/7G)^c8sBGoOCa9{/}B>k","#zE="],
  w 43 38 100 910388 910769 40 1975 ["eWtK$pLy`jG0gA'1uQt.?^OMC^9{3'OQ$.4Xd6C-_p.Az]Snw=:@hPhN$hK2U=5c","Bb!h>ed<k17i!%s-#Z#d|ucgzw4/*BqF?m@i2Bw~^B1'?u~]qB)q3(F'KlAjCqO.","41F&[VtEtKnK)W3z#qk6@>tvIAD%25REF!"],
  w 43 37 0 920000 920390 100 4894 [",*I]eE!pd^B`q}rR(f(;CD{+~$xBx:O|W|h@4mbe{2y'Aw-.g6/o{]_UYo,Jyx(;","2|K,,4qWHw8?^Z!JI$c5'(6F)0wxE:T$9|yR&=q]${*sn|~=S9Q'MZros$/vJ?!m","0b32hp&Ct7#i`<`ngp/13B1Rw#kRfLlG|5O{95}f<Y$3muiHEz_v,b1#|0[s1%?9","Ty.sd(TN$8,qy$jG3RE&Mbs_[{/Vf;K'Rb4%w`_<$*<xFJ?Cm`Bn'Y,B&N<13}'F","|7&TJP%3MwvCgSFQix#(}9SGTc2E9u:Ze{77YXWRDta?!mpR;^D>C&0Cm1>u8;}|","HVgf3]XajAqt[%CGg0s$mDg,E5h^DU!<?)A6-]'E093{%jK$eR}H#rToTgKb%jfo","/f}Lt_}oW!piUezGI3Y]y;%PRr8-hLZL6Y?YlwmI!V`NoC&8[%nBXyprFCX831YA","I:|EEpg5AS:qB;+m/7@9Nlm|^L]`WZ3Rl;XS~SaPJ42b~7Zppao3J%B|z18/l<%q","(uNEzn:sg8jm"]]

private def r43_12 : List (Chunk 43) := [
  w 43 37 100 920391 920768 33 1598 [".}X:k8yo<D;OS6T>e(.o@2jV!VxIYh{%s3=6:60%3&r->>;WQi9>;B24]FPJ7F!&","p},Z-vntq2f1bHW)sDt<*t$D{Gupz)!gH``wFGS-nGjS2vXQqJyxMI`|i0.^7IM%","#Y_."],
  w 43 36 0 930000 930393 100 4680 ["JS}/0d?P4h$;nlzepo{oH]W?ud@E^wy?GR6dIv7`z|p:#UV,VU1]e4`<yn|]W?&4","tY](p$bvfd)LD13(9qR(F_am5!//bizLC^&/&fdMY9{0P[numrz%kd-J}(H~H)]?","S>a+#]?`70k[NU4<u(ci>{zAeE-?njz1#N']':&p(`#IR`5AsIxjnss{++J9*0t|","!QlFpgOUmcdx)bGZGtc~'zaaS4IbL>hE&:}vF^HmKv6<#O<u`:YX8V|:!UkkOVU7","BN&4'/<|6Uc0kj~4(8D@yJSdJ3T4VQ!}A2*ZN%1QL:nZ.|g(<Vs}55_uZ%3MRz%%","Ohu5zOz4900_{shHWqQH=D2-vuy`>E]-C1IB$Gx%qyd(!2oCvioyF1mWP,Mori~t","[w;Kdi8}=vt4#N![RY)U]yyHMkn@*Oee7;}lvn3mL7/&=[H&-OVSkpr66D4/~&.X","!{qVOsmGvMLMWk]|;;,fQHbGZj5};Ap'qtse#vM$(Nb~N0P:~3$i`d;?/p*ng'SW","cc/8UKaaS!>f7J]WNJ){(Y"],
  w 43 36 100 930448 930768 27 1284 payload1,
  w 43 35 0 940000 940451 100 4485 [",g~;W332qbhd>c]|GHsF*2|#'SK`Jbo#3Vx+B*CL4mU1V4_e}1{WK7'gd18NRa;Y","t/q)0.(CS+_Z!z3sT[OSOxuVFg*Dk]3C/l5<]OPO_tbsQsZXDk.E7LhQLVcASuS^","|ubt!Zwn[thBbyl9/jZXiW(C7bRkWkp8E%V*.Xm<[Y5.AF@@E+H6:Y].Rxz3U>fw","hC[:/1Rm$X[@]>EAkKz7OO.zUDoLpy0]J,,elym;kc?>E.l[k]Jlu2fjL^k2qg}@","}T?.vJ674%{wG/nX($|+*ZK)?i/P=g[ZLmzdS'%$)~BEqzp=>q$fpPZVJ8&H3Tdm","Zwia&G=UA=%`:>w'!CqdFycoV65p(m}T2?iYmR'J/5K7dryifpkYu)(d+VsfLD;w","qqM~mep.>cgb'9yT?'t:Z[L%#gXZln+FfpE}z!*<+n_:.zn7w.l/unC4,W;~#uMl","fx&0`Tg-I-aO9|I-oaWzYs[>NX~;OrCic|TkY$]X01+Th]CBr#>(mN7}C{;6|TL(","607Or{<:UAK8s7PS2<h.MQ,+I<<}jx9uAkmY1?"]]

private def r43_13 : List (Chunk 43) := [
  w 43 35 100 940452 940705 20 933 payload3,
  w 43 34 0 950000 950454 100 4303 ["]6|:PO`$<l+_x0hWn!A1F<{$PP%$~-wb[VWA~VG6Ab^sq'Wyu$&Pn$fd,Cf$2QL-","a1p0warQ1>]N>ty6IA%s#9[fDfL{9p][H{lctd^G;[Ndj3xC{N]+:,H^^S/bi3d4","d+3,[V4YCI~7HU.l|D@a~rrIj)nB32v0eGq%.G}J|Eu$?N0?DI-&s['@zXa/^4(^","gM`tu_Hmn.H8pBH;&WG{kz6Om%6?zVsTZ2$SX)^'+C<k(S}<^_>]o,`H|Wf8g%tB","!=*N_l7NAv:ete]oId*Q;CtQx4Mil{hETpB(KNU{:2t2<DL^~LF;mt+y7(Ot_L89","^]m6|IyvJI9l2=vgkbG^?hCvxy/q,6>Q~LRFJwhu7oEk5ckPq;FgK4x+ZK+PjuPA","9/nPQy^d*t]$-h}},!Wt/[-MmQB)q=<L[ah&^8p#ATxp6`:l3%|-uyM+t(c?#BmS","x]ppNrKmTo/jAE_?,myY:/cNiXQ1I]a`.T]rbxFl$!BX~qg)~evbX1YEbgaaV@V%","6mhg&]&#[+GBc^k`-z][;0-`?f~{!`L^"],
  w 43 34 100 950512 950704 14 643 payload14,
  w 43 33 0 960000 960515 100 4145 ["`^3tpirxf.B@MJ'Mu91#D=a7qE+|X(h>+#1@Ux_)m~fL{&XlcSmEUr`TJA@(PeJ5","~v@4{,Ym}ikP,`Cx&qn#_~%I*rt9TeO>AM@`_r9vT8p8C'W:.D?Z1)EbHQkB-_~5","ciE;$7)[/5U/Dtrs'L%o#4&MZ^SaUnwNU8<]skqGac#-~Zo:lAfO;+uU_^D'A_1t","QtNn2/e3O{t9iP=0Ckaa<:2KSK4V+g-Q&:.v`?boRKdP_d;fU!`8$'>Nx&C~PyEG","+1q4n<Dsss9%bmXvH8A2HzNg7I4&65lIl^6alRdQ@<:;$Oq|&G'(u,^!k|!<*9R>","%MP`J/>#qQ8=8~I#FW{SWSt/hMnA0UHXMr35Md^LMY7}0B$|CB/3,t0LNY8WJVY.","/5.sC#U~J}&iMcA.@O_('#Q!V+Q~<m]sx2}(tx+n63YGGuyhOcQ@tHCXTRPQ+%4(",")u(NU=aXGo&Ce6k(2&*6HF+Qr7yH>;51vty,x|nIToV|g2;T-:Wv;g3^kKsM'ULi","#+,,&:NOy7?/mD0yXjgEs:dja7}sX@&Aod}#jt_&CIEL_W"]]

private def r43_14 : List (Chunk 43) := [
  w 43 33 100 960516 960704 8 363 payload4,
  w 43 32 0 970000 970578 100 4001 ["N,tv-dixuHf}R|zv3BbmkY72ifsG<,eu=63B]d0:9c~&+)x!dc^~,xnU})Cq!zE1","74=<=qKRxs,{Z&mT~Z_K<JC{;=s|7MyS,Az,pB0m^Ipt~o&?3+#/%p*mv$B!kOBV","ZX2G^4xU7IuH[P[19KR4%1a'Eggw$:f;*jB8baj](|4),!UJ7KqLL[_]ecrBi9g^","uG?;u<)Ho3A'z:p]by)3nN,K&,-<wq'ylO%2V+--zZ4xqE3u@=R1k^s/R{s5c?G1","k9e_.#DuGm(HD7_VU;8R3VX6QK[;!LNF1stnhkieMP35`sz87O;q)qgol|s~U%g&","?.,*wWm$RM-z|N%nWhUw$PHi<7!rVpe3K/j2bj_%W,LS~S<_2gX]Y49.JugAlpFt",")<N=1A?0h1kLO^CO,O-R|e3_GK0OvI{n^9lF!|hB6G}&v3HPo>SeO^eFnPk8L8{`","Bbz7y6]p%rFxzn5^VUHO!.2p`W;M0=u4BVM5lV8zc{7F?BFAdcM*e7eDFo}ctj24","%uFGsvX3`/Pb)f[{#&`g6Q|`pXiwCgR3C+QUV1>rZ@,R&c6,4!Qd|"],
  w 43 32 100 970640 970641 2 90 ["#i2GG<Je"],
  w 43 31 0 980000 980640 96 3702 ["TzL%psFWrjkN(KqziM79(<hCaz}LgSIZ.8uFMfl-nE(az-kKD?%U~ss~M*9(lw|9","dx.w.uQxru*aXGEq!^`k?-8}xDz]Ec]@%L$.@XI-k=W8QswTSZ=msoKUoChp`>5.","`$k6P%g~oM.|l][xd`^6UOVc+l+,kR=3nkvkhV3'oT^@9VdX:|I;P~vwW#D69<ZB","IB>~|q{pRjpBvAnfcOW^_ol(5xxP[1~,NXn|Z52qkHYB1K>OXAbsn)^{{'d:77_0","aI7([R!HXPMZBYa^1wj_i-8=&0akz%1|Vl]RQtStlDNbN6Gzv@z+S!:p(6LDaH.~","wY_lBsw_E7*Rkx-^/+<,)K@J`lup/}b+da{44^U9Jr4h}GRO/|u(!>c66_S<R$a1","g+;FlpZ{ZQU*ztVdhVgXH(Q$@ao!kVO|B`5@bxan|/2slW@!w&pJml)SnmuMR5KK","syc>`Iz[i)hC%;0]x{BppmDg;K9<Kx`j=a/VE/I.`(3lW7E$<Ak+f{+i1bJ^U3Da","*1!#.c90:g=W[odO0#zCb;5jH~C*#z"]]

private def r43_15 : List (Chunk 43) := [
  w 43 30 0 990000 990640 91 3380 [":P6_L`efJ.IrRyw=uh&E!O*aPpnT+jv[Z%Tl2b?C(Uevh)&}}'}i2U,Mka]V]P}~","'2r(wB)b~'lb>qO)>g*W$do<RzN|N/BcR^=g~wLv:HQG>(2ylU4(rHLl_v&/aZx@","'?<X{%*90Jc('S)%y,J@iA^Fv>:28'geIl6x_@dirj7~jed9q45va/d:r/p1@>@t","0[T8Wn@&q^;B7OafKQr}pyLy2p9[MhWjA.+up;R/8_[M/d!F.FY)!cXYF1?#}H6l",",+>/-Uddm9EW&:DuRd0[#B3</YT`Tua;]I3I(x0`pYHW1V&C%~KHuG8V}I,7~xt9","b^oLLP,W5dEi4TrV'vc@1t*Pvj.j2+s_`wS5;`Z$>:/,CWF0rLL{zwUAV-X+,<$3","#e>x}#Vt_3YUZa7shy%`]@{^N;@2,+jxkOTc.*1Ywwj}gcBKOaFP&(!/Vm47EeX_","'.E_7g%;aOV~`ndVTb^FAoSd3mEHCB,aES,iEU|j~T'<8qF:o+2vRYF3-bB;a96d","]kxhhz[Eza7="],
  w 43 29 0 1000000 1000577 85 3039 ["SG<*/GliK1**W3+g))&qXpT33:HFEY!!LG#h@v=9coJ1cH(3>}eH;Ec/|E,+_XMb","gz[$tc;n[UIq,^GMjg/L98%@MB@QXn6??h5C@#kS^x<*vye@q$(nLeQ>PuE1iPPH",")*ocii@gWczYl)Sjt]npRyJAFq_EOP$VL+5L3,%J(gE?rFMcY=:VT1FVb:YNT,ig",":gOdYAg'W+M_!EKw=2FUr~B/~4Mh7DRp2{0Y2N(*)Vq{iqSCY-Ms|!!:%]4T<xlG","):SsdOG$mu0m|vuowjTn?({PKE#'g{v(Ft/:!.gaFtMdmZ-4D=0BkHR$O('.mw`t","j//m1tOwH%-rpC`:Z~5sdgz@m4KHyian+^pL1w:x&vwM!53E,:pd*y+(]*0L)KCs","R@LNiI#_,vUTambk'RVes7h@7-Kgn=2+(pd;ZFZN1Di|1loU|,91g*--RGH)#Wtw","$HeHryYf8~E~(R2hsI#h3)mC0Q$OFm'M1n(||nBN3|Vm^lsdBc"],
  w 43 28 0 1010000 1010576 80 2754 ["H7.aGSVo?y5o4^&B81F=MA/^^b.hF$%S]H4h4sxi^6`.3a).8s=AWtJeL6dv`HJ-","%Ma[{U::emoUAD4e;}ygLY6H:./7&j38.ls)?PqN%`=Z!N@(8-hI_e3Dc^C;nU.h","h_{zO/6nl#1VPDRCz9E$I?DugJ%qg6llxT`xC]pmHOsr|9v~$plaM:m9p!,'UGIG","bz.^xy]56hk6d0~DL*LcdIwh0gTYJAi4[vn6<|b<&{[:ICmdS$Se'Rk/u@Y1zG<L","KBSeeL*O3/Ia2Zx=w7OE$#)YozI=tLG#w_^iP}*47D,&sMQJ4a,72^4X0Dyu)'uy","=|mIn@c<-?QOpTUUe#~f/u1e]b/?}K.&A`qXR:V<KCnZcA'3wN@ej<QrzB4jPivm","`pUo$VxUs8Ep5s;I9s6D[%6lkt8):IS;1k}:~J4(^Q1mYB#.PX(K!wF:HL4Q~VHm","$E5JF>3BzR!8R>68H<I_U"],
  w 43 27 0 1020000 1020576 75 2492 ["?1b%|!yV0z|5i|18Fr0+3d1A[_NY(0}.il]:6<KQ3U?)Cp|VAg{pAEx1u5@*G-.o","ag/r0Hj-1^-Y[yOV3C:1=-r9Z+x/8V%&/`c;Z)odhvcNjF/s}yP(40;Jtc7{K,bI",":/[<UaG@u)tCX_O7|N'ZQC/ohFpm)K?'cnWhapjoJ_qC$Hb|@TPyjJqUc~:KJk0c","5hn~7#{5+([;A>,?q49BHH#5Jz!Nn^P|5k[z0xRphLKuEVRMBW_23Jen^,?p$}G]","X5t.)dC/z~N]Nh(_|H[Pef@lpW(aaLAsEN@p%SK^XRnCD*R%Gy}y<:j_Re)EV46>","uS9@Ac3a(*,j,-:7i5VAXCE(M1u~iz4*E,[wy^fO5}-4KB@G4d+yWmXiNx]zU:ot","%T/KDv00ZUuy(@bOnu^CoCy_0u#e<[jC>k#1c})0u2Kgu[ZkjuXxGG+^G`)8*viT"]]

private def r43_16 : List (Chunk 43) := [
  w 43 26 0 1030000 1030513 70 2237 ["[MUSk&q2NRfSFm*D<091vJq*?(Hfk@W7!cp5<bgG&4UFiK,tsXpEQv[7f%'bKi.>","VmkL|SqQ7xI[BVz4a`e55$.91jU;qVI3TW1]z#y@&hBV<]~a4n(Nq>=/d#lyp_F/","KOl@[DT9;nZMiI@dP98<G#7N&)e.0#rL|~O@4Wo!3E8[Fo:)LMnzm9$8`SwE/x9M","%&MuWj@X5CAN&Xb7t>!5b`0<2(m)Mzkmp9ufyXCUJ{R0dA##5._^$/wbi)WJ6K_g","FwnAg58rQ3h+FPtEDGyQ5VfYJPp3&8`1(q)I[SbWX9[<}O4)1YB8nq[<KY#~EC!$","O8$:Znq^prykAWd?[O]-]2'Vhajx]mwM/}4oeJbvf]@gs0JuNwF`!893>iB+'97z","$wX;y;ueW;=M,f'g^W;BF5<a27tx5WGq6<R4+#J"],
  w 43 25 0 1040000 1040512 65 1999 [",o38UXam{M0w)Pb^gDbru1`%=+.2YYII4v&fuBpb%M%E<:c}u(vc;X/j|-hwKGVp","#z-23^jg}2){'@<[&FFUcPaQ?c$Unu-{B;z[k50b?Vmt2tL7kp^_g`k=pH)M1M!,","n9d+74iq[9z@P_jH=95(>L![Fmt:]N3XeV:Qf~iSlcJFzMSkI2R?{*A,b?fi_[.4","agWE'~rzz{[g/30twrK$6o3Gs=kv|G~(pI-5Vxe#:ey7L#w$@l;FDA_'@!!@N+xu","u<}Hk3>vL|&4,m0iub:HhdHoUaTO0sETLohhYqRmiajhyQ|kRp$1gmqk@$_oP8;m","eL#wm05S}nxEqSN6lWvlxaKI(<cqFIAzUnFsGvU8A1M]hY:M=$CjbUq*!-J#~:)/","$sJWhML=+7"],
  w 43 24 0 1050000 1050512 61 1806 ["78ORPEQWU_9(.H{KU~cG9uEY.k'zmW3K_o`l:VGXGkc=0'd=wnhNzTeYpL'h0yH&","-=g7-r3t[SaT[VAbM<xD7X'P/UE93;JbIj9c~=USQmS%|f345dl>HSOo'T4(0@HH","XpbhMYl+n%]s$t6lXM:(C6vQoQ=fc49|V8&l]*5X<cr'[Xj4L&5BUPT]ny{4$&F[","F-/4i8OF<:kAT0LM7(dlAP.TWmT0twkzjzPAV4hI]j1Nd>syMy`WLhbakV[<a~|5","X5UOq7{.@LjV53N57^)77o#M8wSoHLn`K+_VMMN?i6?cut]h/*VJUQZnji]7eUyo","v(xNiR,R?(($N5E[!2cunDz|y/7VQWd3.+TzYsbEJ55,j'd"],
  w 43 23 0 1060000 1060449 56 1592 ["egE#c!74OVF8ORp#4A9Fw^*^nk93{$hYt@]Ehz,Kg6swD@p4Ub8O'L>[`_7T^:-{","](]B+^Fp'(agWS^si{>:h:PH^z3lJ:uTv_X<J$,RFj<t!3P{?F!)))sS+E@6JQXB","c[+,odM=>6I6-fy-C[&T[z#(cM4N2yynuZ[I^`.%?3Fl&GmVx$oj&ZH1z#%@'gQl","$hFoBghkc90-#|aC[vmrVyZB9xnd3RUq,x!j/98e*&C0WPFYG5;(cM[<FGZ9k2,S",".'XrcL]OXvq^APQ;hbLb|.+[Rx`;@Qz#Of,)b8OCl;5VF[n2$JJag4K*RhhCXIw1","'WT;E-,c9JR3hH.tYSIyc"]]

private def r43_17 : List (Chunk 43) := [
  w 43 22 0 1070000 1070448 52 1418 ["@?`L_)0I*<Dcltga<z(*HZM8o;zDH]vyyTao'a2d08l+ObV}#6rn0S8H7B!n${Kr","mw}UzmW]m}<qkSp9+ji0uG$>%:%1-e&toI8P98hK4OvP+{'A2cQQfQd6U'^kBqaV","{IQkR=)]:O|$:=,#Q&<jWWR4(v`D8$}7Tsi3fbElQ80x?#uI8#1.7{|pYwKC9'=q","h0@3pm>Xgh0Tf>z:7?G|*prGtlSOvUU0>bIXVm|_qeMT+sv_zVU5d(AwMr,o2uV6","%M!-ct56.t24:G(U;#Zyb.s>6^l=f%0`i{*3/4pn]tdS4i<g=gdNYtLSaQmw,Jj"],
  w 43 21 0 1080000 1080448 48 1258 ["tz/qF.kuD1b)AOzrCvNd4&&^r&Ofx?Kod5N]QL3wf2Z,>bG%j'Wx,WNL=h@E{m0~","'rK6*:z:CRQ8cn)2K>}r*V@%8PtNwbul@Tj,ZRo2R@p*`/W&zP:?nwQMdM8+2s*W","?F*sZftEE3~6uF45y*:(?WSehNk]:'Fc1M6Zu8-R*|XaK$tXjX/iY2*`#L}@Q)!Q","2d/xWTW1#`c/gug6I^dOx~M&=;/2.j'ejx(T9<Ib;@M?{^H7doo&Wta00;vX#s@Z","'(wFQXYGQj?iO:6y0x;Oi>FW<!wOvT7@C"],
  w 43 20 0 1090000 1090385 44 1102 ["[TKGoSe.=|BeG&|]olT^R4#eNAW@4/12yi6T`3G)hK6}0_:iB2C`7/C'd&uUbH9B",",4_Pax$Z]MvsbVdty.6hFE5p>]C>X5g'/58~yP}Ri8`BTx2:2Bq?^(6k(c-<!jMs","ZS9W%,~lL95Avq]N^m0PHl6}R<co@SC>,]QvZ5WH)ZQ%3C4lNE)yZ,~vPwPepliN","C3lAY,u<noaZ/}8C$=U9z&&]8U}=G{m2nDK4FL&V(2yGd#d.>ybG7::S[$u1`bIe","'o4XcUa}25sXe<M*"],
  w 43 19 0 1100000 1100384 40 958 ["G[K:niE?z3w0WvwsAl({GMaIniJJEi'NVtS-x&@6$ZCB[}b3+Q+M2M/&y?R#qM,`","mV_^L_:7L?cMnvkq!xN7nMh+ex}L{xXY1G71~*>A8}e)]j<KS@,H;d8x}=vR>&}6","dc#}HpXwmBjh4i`44|6G4LUK!zu1=.S/%.mS`Jp'to(PD2cb+~RrO)z=K3FTHbk&",")dBJnQjV}30%H)|S~{yDSUdRO:LH(f+#>iHhR;5+hB2Za*=7+X@Z|2;m$bY:"]]

private def r43_18 : List (Chunk 43) := [
  w 43 18 0 1110000 1110384 37 846 ["ZHfED-Yb5:$.(1X)8rq~~6t!hnz$CqEq6sK<.Qp6Y'%Yds4ewW<(W7yvx/p-kG{6","5VXgj3z3cFG%tnrTW5/Wl2{+n*#v(;^og)=?3(=,==?I./DA^e:[Wk?)2boZ[('s","m2>nx3_n;z,,APRJxKo<e{SLQ8BRZb1-=4YckN6sjy36~V(;bN'NM3UQ0>plR8Z<","Ghm3PW9=+n(HTE%^T_=<&fD(G:Y0g?n/RYGC7b"],
  w 43 17 0 1120000 1120321 33 717 ["'3[h6O2A,wthw>i%w7F_kNxD7#7%pl[~FARI/tCVN(kNc}Q^!Ox0Ko(o<f7XhDvt",">hvF[M&^):Z&tYHne+s;%-']_AWKmEYinSxfW$V0YdZ_YV3`Fa1zy8(b|T6U2_Q&","NJmW8w`KPTM^3U~smF$3#}vUy6Euqis~o7brhnn!Ta[@'9kD'IfM:Y]Y'V?yiWQK","P]17^W{nv'oPNnL"],
  w 43 16 0 1130000 1130320 30 618 ["cy8b;iZ/MK'TX:xIy[z=plIBM09|Z>5_I){o_pH!RHJN4f-h;.OaVQS+l^ww<YT?","{+X)JOb9Hn;Ubm2H4B/`s*'4FLzt$]Nd~#@as,Gw;^`0S651_mEbtlkG:cOeAr)]","/`IBvmYnfE[Qbz-I8yBUfrjT|kr5wP=dUON?3f^AC!f{+ICyZ|q%6.UluSxi~jca","=$."],
  w 43 15 0 1140000 1140320 27 528 ["oV<9piNN6_vt8~w+|<H$|Z8QOC+0B{d(#@9$1,A-f7a&AKWsxr$H.K/w?O~DH%AQ","HZ?c5V@YaZ,g];V,=JZ'9T>KPs@@,3<*M:=6W^3hMz#LD:q|!tx9@hsA<l+bir7'","T)qz-N|oU6o(Ftt3qZQ?p7uaKR}->4>*.|Y`x_`('W5a"]]

private def r43_19 : List (Chunk 43) := [
  w 43 14 0 1150000 1150257 24 441 ["i8aY2xf2v.'lB8?{-ds;$l6W(2EwQYLC05nkJ{;TtNqbL:RSm>rLp8|^ob*86RX?","|)PR@v%k=+0$0rD&Ch$^!/QkjtF8AVRZ5_aO,96/-mbR|#t-%,J'v(fi}#aBeSIG","33as[Zu(,tYK0K&xUg`_(<*1)|+7,XG7tO"],
  w 43 13 0 1160000 1160256 21 363 ["TPR!dyaiC@x~;9-:G0wZhm;lXmT'!ai-2#o][z0/{e3<Jm~R$<{m23]P,@XA(5(N","x#gAXtvUSg<@NQ3}qi:jV$}cV3_/wwSV({PH5UoyPcA;y91(sSjgy{6k<l6KXu68",")wm=,8'9I<XDP8y"],
  w 43 12 0 1170000 1170256 19 308 ["$eD01D_MXcC4ndJ0-ajW1D8|%&-Ls,^%lT*b[uF|3Q|>$-$f8coGp@}^=-SDUiwV","bu,PVwI0z$6@c1=3,*oAbmb56e:SuWS=g6>huK.4sIt_{(5a@=<m:dkHZAUN!9(&","C"],
  w 43 11 0 1180000 1180193 16 241 ["PhHc0fa;dso$k5]C7O,kZPtOWfB-zS<aSGb)M7hqumeZJ+K:XGI%#6m!ISEt&c!&","0NqM!T%<3`a{b#@J/FMap8G3Y]b7yaoT]07w9K%pQM)BS"]]

private def r43_20 : List (Chunk 43) := [
  w 43 10 0 1190000 1190192 14 195 ["lEA()|~/J+Qw,'PrW&_T]p@`&fN86ESAlnOHotIX,BlR406,yb5IkB@l__6Q2E7l","*/wVM,d$PlPg9<2u9fLfw2_}mMI>'J`VZ-|"],
  w 43 9 0 1200000 1200192 12 155 ["aaN])G`R#x<JR)?,0_AS?JvODo0PZbD1e,E9'@,NkQjDWwj8r1A,tE]zwqh2!<}-",",(13k_IcS4l^BQ"],
  w 43 8 0 1210000 1210129 10 117 ["4JO6/!x6R>~t%{?_gy)8|4y|$N_}h$QNB(dt-15g=4kzS8Pza1id&,My+KMcAgu/","(};#r"],
  w 43 7 0 1220000 1220128 8 85 ["$1>t9n7dbFkT8v4(nB(}d%8D342|SlGR3g`*SD,mD(lM&Bz08g=Is"]]

private def r43_21 : List (Chunk 43) := [
  w 43 6 0 1230000 1230128 7 67 ["cGRu4X(E1}p}ju|yDy.~T=)#~L-aGR}b*}-uWHf&Zs)E!"],
  w 43 5 0 1240000 1240065 5 42 ["V*iJT)]fx1l(sL%(Y!j|h2|s@#e(4DN"],
  w 43 4 0 1250000 1250064 4 29 ["H5P;;FQWJi38PgvmiDiYRs~j0p"],
  w 43 3 0 1260000 1260064 3 19 ["#|bGdc:R7V{ow$|k5"]]

private def r43_22 : List (Chunk 43) := [
  w 43 2 0 1270000 1270001 2 10 ["#*j=3QVx&Ni}o"],
  w 43 1 0 1280000 1280000 1 4 ["+TGO)"],
  w 43 0 0 1290000 1290000 1 3 ["Oxs;j"]]
private def chunks43:List (Chunk 43):=r43_0 ++ r43_1 ++ r43_2 ++ r43_3 ++ r43_4 ++ r43_5 ++ r43_6 ++ r43_7 ++ r43_8 ++ r43_9 ++ r43_10 ++ r43_11 ++ r43_12 ++ r43_13 ++ r43_14 ++ r43_15 ++ r43_16 ++ r43_17 ++ r43_18 ++ r43_19 ++ r43_20 ++ r43_21 ++ r43_22
def rows43:=rowsFrom chunks43

theorem good43 : ∀ r ∈ rows43,good 43 r=true:=rowsFrom_good chunks43

theorem sorted43 : rows43.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks43 0 (by decide +kernel)).1

theorem mass43 (i : Fin 57) :
    bandCount 43 (i.val:ℤ) 56 14≤(rows43.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks43).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 43 (j:ℤ) 56 14≤mass j chunks43))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total43 : (rows43.map (price 43)).sum = 334528 :=
  (total_eq chunks43).trans (by decide +kernel)



private def r44_0 : List (Chunk 44) := [
  w 44 56 0 760012 760332 100 9396 [],
  w 44 56 100 760333 760711 100 8995 [],
  w 44 56 200 760712 760903 32 2681 [],
  w 44 55 0 770011 770329 100 9105 ["zN(j'F$U9uEBb/aA:ARY(<qv(1mffVI^3PYF.%b3nECaTu[]L-e5sQhO*-PSvTaB","xYRhkHZucrR-9:C|mUGK>S,86bI27+b'w~4MD'V-dOO&&?$=7j+|t6'h]X1s]U7I","=.V}SE=,3~vA)J.`Lrn&OjFpKiWA:F4EL"]]

private def r44_1 : List (Chunk 44) := [
  w 44 55 100 770330 770711 100 8637 ["(>93C{22(38>~_3utM~:1?0k2SdH:3N!5j,y2YFyqX(H15!z$rf_1Z1.yOLAj'|O",":d*^,+Vt%X1d7Gx=LmYG(HN{b=s0i:QQn)n2XMLcLfN1rPU@UYDf)Bkg:CzEc#lm","#Nx)'z?L4|^,y!;V>vkUy3Ix0sB%w-20IPoWHlH~U"],
  w 44 55 200 770712 770902 30 2414 ["#'8V5[AsyIFH6V%z[2]T:vfaI&8QTncI.@lnL.b&2usUxvk4Fbx"],
  w 44 54 0 780010 780325 100 8824 ["#$b4-`iMnEk~Sxb/UDg?RoTaY{[&M{LMmCer>v8e+{LgjH+;%=Qj7o&o@'U3#tfF","#G&4wkIL@HOFAym{+13JZV{^*51MVF#&F|2p1A:y'DlS?tP>R@;7oRv'rVR^/>k-","X9:gI_a1qCvdyD`x8dF])u&HTWedt<Uuf4RXWM+%U{X["],
  w 44 54 100 780326 780710 100 8307 ["_pM`.!efBHB/k%6E~L/;UAYD4[Vpy=Ch3RXGVbjfpJ%O4O*S:D05-/gf,O@3C%+/","cWhV&_rwO87-GqdE1PI!W:n6kf~yMI|2`h,Z;OQ[fE`%VNB-[C#lPW?DC~:7iCoe","c+~g!Eomh5MFlLxa;BJa7~j}#5ACqj]~/dr~H[rutJe%b*x4'W-f){Y"]]

private def r44_2 : List (Chunk 44) := [
  w 44 54 200 780711 780902 29 2249 ["$$o#dbNAjxOQJhLec`:1fW4dp'RYRNva|q+5_>s4,B^@SHRB@/fZC`c)Bwh?bHR|"],
  w 44 53 0 790009 790323 100 8558 ["Kp0K>)tijNUNQg!.?SaPf'h1gItSVU*j{.fNn~8o(fklTYpLe3bZMc+hh]xk!_Pc",")DdGb$;%r2BP#-L!Yk[wM=~#>g5IBWW:ayC'Dr[Z[j8SI1w*ItmpeHfv?tQ^ut9!","WVqmuq48ZbbVqkzQe{Qaa^z/({{I1WJPLx6-s<^YJ~>xU71d;]WE4wt'[@edY~dl","*}J%5"],
  w 44 53 100 790324 790711 100 7971 ["Bg>8Yc6rK=I>Q;uE@eB^EHE*Y|SD.C4zRhs)!;Y&>!)gXuz^3Th5lG@BB+5Z_Fwl","93N0X{(W]MyS1gK#~X3*erS!N^]Lwwg>aszMRzl0'S&8BxLI6+&vPUv^LB1p,>O|","f!m!I9|t6C5D4N{('fkytR+.'t0F'Ni47RS&!M1!hk'J8Nm(V5+R$?`-m_m:tJ2d","B-?{T&x>Sh)D"],
  w 44 53 200 790712 790901 26 1951 ["VB]yyL@Y6SY;1Y,y~C(}I!w&l:#f<&r#ya_7,7K<H$(3&_(q!qpy{Yu{uHidSxdQ","*NItBloi"]]

private def r44_3 : List (Chunk 44) := [
  w 44 52 0 800008 800320 100 8298 ["tyHyi4DVR3z`fW,&'zm*-~cK1nk-qk1RoS=<^IppW%9]KEB0MQb#~jYMgLNI;9<!","1k3;-zu3LZ^2K]B1v<n?}`i%O+.PeA*@VhHF_7Gj9nN]r>HS-`u><GDA}PW1N-/_","Ry.R-<XkF=O>60>p{7E4{IU-`m%hWOM[XWv*D!*Q3M^i|V3h)*hy%9~&8~r9Ge!R","#tNL7)?Cky|oqUuE5K,{[+7W@Y"],
  w 44 52 100 800321 800711 100 7674 ["aUe_a>8Sc6>WF|b4O7^<Jv7YtVWt;O#nv6PygipjhK}2#d(YKP{Ug/i1+8Fpor)P","/WMxd?*Y@[XJ=C0ih[?~qQGTi1}s8ATe?!Be`gnzTlq5A@1Ti?M<%9(mts'hN%j*","&2Q|_=6c;oV~E#E4&Ae22?w)YKPU_E3lYOA{-eo/:HiLN&Z:nM$Aa@J}>~@vTs+v","#Ka8.F}=4Zm/&>cck,^YiF{k>w?UP7Au1zP+lRlEk/"],
  w 44 52 200 800712 800901 24 1744 ["B!d}Mi*cJn>A|,^-1@y>l?&c.wru-%<kbP*8d14#J'|zaT*c9RHn[X#v9f7u=4!E","0c+Ak#"],
  w 44 51 0 810007 810275 100 8050 [":DqvhO*A3YqalnI5m~XKg`db=l5b&ICc6w6Khpe>]XGg|DuHT&~k7DuY+*->^2qc","zQL?saUScw$z*lS7%#Q9:[P:FTe`c}c56D{NA4_>+tQf>h(s_d&dnoUcK?:pr^%0","jZ.ItpK+xDz%S|YH(@B~Yc8!pK<;,$jiL@kjf*np#]J:FX^apIe,'+BT&jvRSpRV",")~hevZ@LGRwukn$+*C$a@r/4bawigEykU>)z>#g.V/pyKuj}"]]

private def r44_4 : List (Chunk 44) := [
  w 44 51 100 810320 810713 100 7373 ["h-)w*jl(Bc*m*|/|!)d-ibg;08^Pd7Vbr,*n$R2oq@7ZBr<sj_TWIUs5B}aG`fj@","UzATtX((<$QL!D9$i-N[o)3<_UD/=j9~lN7L%@$?9kOmKJ8hF1:i9~iEGjTJQV(|",")#^_C~e|tdbKro1ai)Nv?3=C!GznjE2AENs~R^e>j+bgBbADgi9NiKOQ1l}-5X6C","Vr6JXQ=bV<*~bz-D(A@PI4$D<_%s5M%vV_gMS(6tfz=h%v6:[/un)icbK1fUeL80","'[,?~O807}`"],
  w 44 51 200 810768 810900 20 1409 ["#m3dMuwM;OSi{nY}0k/U4(<imTgW=&-zI6n8?QA3VGyc|yb}bfCp[.Jr(6<Q8"],
  w 44 50 0 820006 820273 100 7840 ["HfnCxg?CTCs+%7%U({>Jq~bxQ=N[SU=zU?tvuyFN2hIqxlbAUGP'NN=*dn`Z4CHs","ZXMvAx|&Sl4B5mE(U7yRvHvyJ>|YhPd[<DSSL0xd|lS]v[[CPB~joku=3R*FXyvl",")(Cs)#:`Yi,U@@--,rtkCyhay'/gHNA'=m*}nTaj>14WFc_R5xtD(l=?-iy,X9nC",")Gwk4Jg`_.5<@8DOf,8EucnhFr2(FnK*bC4W4TN*u@Ve4CPm{gCFj>u6RRL-JyRf","N(6"],
  w 44 50 100 820274 820769 100 7081 ["%faAi%:i*ZAiZ?]J7$l,3WT{/NV|K0nP8RNt'&dHQ-1:.<EJJ4.&ZSN*YW+I=aF,","d[]sWS*ZPL>BwZ*z(|M4[H+h9nqg=>'*Nj1FYEkk.*n!IP_k'|ROxOD8}rA2f[69","~iJF3TmZC+5qPywZ.hwM;lJX5rP{f9Rsl5d_@%'#i).Xi]%Q%|w.nYw3XmnHeF3?","Ci$^j'S@_Z57iK%t6cp|UzlJ^R]1T?~(=8J2VX.=tSAa]],{x%!fx3]E}/zET$Hv",",?i~Sw7LoPc~)n5Fgc@$$4Kh/poEE9,imIa5yL%"]]

private def r44_5 : List (Chunk 44) := [
  w 44 50 200 820770 820900 17 1159 ["u8^NAaH1O2D<NxJh:gU.e;j%cE;E%0X.qMpA:MK8!aMfIcC,I(;2m"],
  w 44 49 0 830005 830272 100 7612 ["SGb#w*CLppG#ZB'WO6dVmu}(<]e9(LA2Oh2O]0j3U[y<nl}'+jmDVGh|Pw?VF:CN","waUe){xM=D=19cnyw|5ho(`'!,nEeGt-`y'*mH'bu>BJU?1S-RV]85+AK'nEGLVD","WuLtYk~XuT?_K{v?4dp+9:yL(l/(*{jsjak]+lAv/rvdzN2RiRStZ)Xc9mFO]$u=","IHt^,,6SE9;CyFKuJS<*%aXUspuj=G]^b})'I:2Y9?^L;8$yICGV8*!+-/xa}`vz","`S(o|l1}8NtlEhH09bg|!dSFt"],
  w 44 49 100 830273 830772 100 6803 ["=lot)PRJa!,ch^bmv*?)hk!x^YzUEG7F:}Oa/wUccW0>rP+|qP1wn>CY#zV:3~/8","~Z(#UMB3}H2^&,RsU/GfpylQ|QRB^u+*%x*Q]GFo09zZE@h}S$GI8LY{9?uRnqoR","]hSqVu]NCtdg{<nmDil7W<OhW41=>AO1Fm6B[lWQ.HU8y{|$Kf_=$ny_ke*6)]01",".PI4FpP%v9H2a{p~]7/W$:lSHn^7qs~bqj-X~oRn)x%p2SV)23&%6$<2}';<1v!o","W=,CHzx8E@WlO>QS0t8%!A=!Is#!8sidA5[R)HVR{!Cr73`A-u,vxu@avjL!9s0F","$/UT8("],
  w 44 49 200 830773 830899 12 797 ["%[A:^Omh[yeuN$4q[YL|!vGH?KY@.W?ke$<m75vb"]]

private def r44_6 : List (Chunk 44) := [
  w 44 48 0 840004 840271 100 7401 ["sP]kpRgcunY|DvX`Ij3/h_)PCW/@&R]XkMi0Yt6c?PX)&{rAkBWo$&re^OaO5KV*",",{Lnfm=.N$'n.>$erX}Hy1~v9X:BQ,>Nr<uh_=0t.fhX[_11`@ke8Kxb.5WcAOAt","YrD)~I&4*hd},9jg;|m,y^d3oG%TPPXJ~yL67^)-mmJ/ChicTlloCb*akd)e^NA]","oOp;$fSH@(V@'Ln09'}{Ra+z/:5ye;^,kMbs0Wz&-yK$DuC0Zn(t`CO%<@bXdYLc","(h)[wlkfE_LTB>T^+N!+>o0g/9~ZqSW]w|?!JICiFKb$"],
  w 44 48 100 840272 840832 100 6551 ["U,lh_[KrA(/3Hd&:pZvM42J%ib^k.(T7*Rb#Bl_-_-3;fIX:R`G@u1Z@I)_@0>qv","Y:KMOWmBe=o+R<7:R3Qkp4XP4j2PkhI#E6,&.RRG{ruLCu}Uynb>?@,yN-ca-*&#","HbX3lBJY_4E#d16N4[`0]!b@*mq6!]c-;dE$uMT?f[)b_!Sly:;>U@M'T`f@bKR>","V8cyzsVwlHA]DM,D{ryuR@TtQ)BXtiN%_N[BIT;gq,|H!3K,]K3o>s_p[Ey2aE.8","N]`4(WayxV&Uw8[wVU=;b/B>g=b)0rLR`gu$tHSEyj35?MIa7]3)c&tjc-=Jfh10","%?8ThQu[JkT]1&PmM)'5L_<I:Eab%h]g|w"],
  w 44 48 200 840833 840899 8 520 ["1'IB;JL*{-0!vY]lGYmR3;Pg2<"],
  w 44 47 0 850003 850271 100 7167 ["%k-?@0i:-<%seN%Vw=!OJ]d=hvVuE+aKV&hy{rA!%)TVU!_e;NWfs/?<ZG7gmoTs","af_SYLwhL%_H19t=E$8oK|@oad|'oy|q.#kmWv6._T8<Q.Y#;QW]m?1u<K01yV%_","Sjr|a^5GTQ82f*|HOYF=9r8Y*^{i;2PuHFVzgKEDj]y:@I/^|q3W{JgOE.I<%zS`","-^y^6oq7n'H`9Tw[W$TxA=&26KM/8$9S.6_va60GLC2<w)E0G{9:&5B|ZGwN}6gv","%v^)%;v#Mcev43$iI!ifaN{+bu>UZ8YnE+n1#Kk~S$mexORECL{AaQN+^ND]$Z:2","'Y"]]

private def r44_7 : List (Chunk 44) := [
  w 44 47 100 850272 850896 100 6322 ["]r?>Oa5%;)o[KG1qbmrUCgle#xg=<YUncgUBB$$<d_:R~rjkyE)OcKW$n0@1X3[H","u*@-0U_L&_$Ym@](viyhP(P*6Z3cc/6)0i.CmHo@7|Ic7V0Qf%w$c%XB5Y]uuLDD",";n`{`/j#^m2m!2dX)'!Adfvu36glMDT<|DZehzCp(z-jES:_*x;QUG'W};p)p|(_","qO[Pf^ZJ~wJ?)5*^<=D)sSe7pMR~}2:p6eO#1>j]gU=D_q`x)&QeQe>D1{MwvgDf","i=,kXtGjvJEh03VPI>p~NFpaCeQtHyY,`4JvyD_&:Ex;tN+p.]NB1!#N'wPX4L(2","%r?Mf'QR8vjZOyR`xuLcVow')n$qj.i6Qjm:Q>ZB+@H471h.9Rj2sX<wD+k7"],
  w 44 47 200 850897 850898 2 129 ["%2<9QP"],
  w 44 46 0 860002 860271 100 6949 ["{_o.>qq''t;~[|<5c?&o;9*%CP7=tA*>T.EU8Uthw?W]CNl];+dJQrRP]DMbcy3.","zllqa33x$'>NZf/+s$o43|sEfCT[s)VZ{:lqBp5bvvUw4bf4v!]%vwK^>.~dlNIh","4DD1D-^omrL)C1a5.&@#vi3n^^>%9xT7V%lu`/6+$:,Y;W-WG`&7{_M-PJi?[S~-","v<:Tb0[|q^A+*Plmssb2{gZ5&yA%VPbi[U%rz3@hozs:;OmUq#wVEyP68*3<0@[E","+#p+[]n*0NrH<&T09S]8*q8{;=@j~PN:(.P@}v9Vi!/Y%qPP[nG%1#mPd'>[~]O'","##DXVgn$fhf@80&YMAW47l"],
  w 44 46 100 860272 860898 97 5934 ["-Y9/U}Q6xTSxGxg#zQ%?g1'OWaOaA0gRD.Mw@u=T9:~pHI){rpWtDP=bf=>XHFU(","~.U&]%:ZET-Ed!EYkAOL47rhYkW]Jm;IDo+1|-ZQ~p<3cQn80EABV(M)D7]:QA%T","SDnDE&QhfYREk%5_Xc,R{:_}z}pQ$k&U2gEwMiN93a#`2%&.iiv3rs9*/n4L3EF1",".wpHM,3u(I&0eXl0i~i$vUJG_V`]A=qC9ho`?X}((#8Lz85e.IjRdrd22vCUp'(;","A6aUB&bZ]H-`g|_@6VOsOi!F-hcUdsJI45Pa~aD5o`weDXggL@E;Mnsr#4en240W",">i-r*WPiHj@P+j|Se5HL=;8R7+:V732cLYbHrs|}nI$rwFE`Tr'Q0N)L3:w,XU"]]

private def r44_8 : List (Chunk 44) := [
  w 44 45 0 870001 870272 100 6703 ["62ic}ygKOWg4D(^AP8Ff7&wdwnxPD,;%`/MC:`C^$@pLm^Xpyv@^<`=p~;(f2td>","8+7dkqc&Ey9zA69R+h/iL5$>b=|[O6%<H,3ZdZpDm+-mO#I%_^'Us:tW}7F{]sp5","Tiv-j;i_&03m9}?jKda<uFQ>n(rLcL0Rp]cPP@$0&z;UD3G`Z[ahD$~9x%~e*C|D","txao7H:tWc<HdTO]_isWH?KnogAk4i;+R91t'DVMXvs:N,;ddx6ke,0qn=%)@s27","?0y,Cw[N?atk;~4ML?jc.hcq:>#`Cf53K%EO:XM:Av`SqSL7>qg]#Yns&H%MD<P^","TNW'>b(g?WF$U7xj*Bi[vC>cI&9sL}X(^(f!Nyb6(2AB$H$kIZI"],
  w 44 45 100 870320 870897 90 5330 ["PZ%i^}=OkwK,^-[[U#^SyJ*LEpp_#>x&bCF,U,T[p06-CF~DH^dHu@@@/mtRG4ge","t('F.L#qpn7Gqm<X;YKV68-mq:%@a{Pt9TD[[>Ozz(QPC&MfH;B~+5l0;=tp}:X1","]0lQf$E+QdpDuS@3`NG;)TL<vpA*Lo9~0HGtof7{-cRRHNadp7g,m4Hq%o|,@B{N","|J^lN)HjTl$r/=ig4~W')a#YSfy,}HK54EL6jd,o?UlX@ab?Biz#~?KTOX}N?2]}","|ut,ztU]uhxt~L=}l<`O6<X*e}MEtm[zpm$_}Pw`N~HGjL>DAcf-5url=^.;5_V|","#+utf4[&B:W({7;Qw22:`y5[P_<-zj7J>k%;.DcW9yp`(>CE"],
  w 44 44 0 880000 880320 100 6478 ["Ho>Dus!069-:{M:C>7U)#%!1{[tc{c{@&.x;#&LnUvgX%a|O!>|mOe,_fEZe@fbV","*fOZyo*vDR5Rhb:J4vY<k9-+G*eM%8[>gD8p8#-p|H$xc{Kl;N+2x+k37&vY!P$^","mXEOZpAO/E*XG~Bde,uo8_>2yHH=8M~%Gb>8.Te0%_zDU`l`,W,)L%&+6+iip->#","uqI]E#Ch}D:BVXyvTAZoz29?/Ro5^FhBo,nk-=bGNR/@Rt5o1JL?>:k)vkSrJAHP","9f$YKkLYw)&Qe.+9X3Lf;Qf}GzIeEP@e;DRhNiYO(;kj>l`^g+mSl$Yt|_}h,)%3","}&K|K1=Xyc:-VlP/}F|FQ9saT/a+a4ZblpxMP?D_w[Y-D/[<503DQ[kR^zAS/agy","1rgDzFlKlcnr}l-+2e(5UVhV"],
  w 44 44 100 880321 880897 84 4812 ["w:Six.V8_@4fu&iNU#UUQ9M8$[{!c|(z@#OFRM'l0DHS:U*0AZ8SV=V'B1&K(F6M","ZXlTG/(m@rYC?3gqr/fz=Z.L:f`%Gb^8A;ee+%LcP6T{S/Yp>W.X+,kdP_.;Irg}","T2{_9.`t(PvJ!FV:YPffqBSj6V2dMJVI.(efW7n3iwN}O?h`nvRUQt&pA!EK_?[@","zQQYs18|3q=QQ0]&^y:)T[EycVkfOz.)55i#v8!-!rMHLVT_zQ}$Vy|p]U.TfNM(","YDB`eK^-`0L`)IN{3e['mbVSv+{{)unrwZ@'*A.d!?[b4=T=Vcxj<r6gZ)BZZ`&I","#yZbWIFgQO/bmk~W-C&oxaWE)4"]]

private def r44_9 : List (Chunk 44) := [
  w 44 43 0 890000 890323 100 6211 ["Ne7mgA!xzM]9Aa>Ag=M$!7jK1ADk~mJDo9TK*mF#RgNsVL?HJd09C3UQ{pMUO-cC","PU@2V/3:M21vhu+=nbt1VXMQn()mS(4g`JNMw30*JieOnW%$7MKgZc)5l8xxBBEe","pg=eL%q_(}rl^Q4kSy9m[(7VKT<fN%8=[a89U1:jHSVq%rp&,30m=WE^9*oh(-Mb","U:p8SN!QJ-#0dd',0SL[/a#ur!w3eFSIe$Nn{5A2[W*w-OE/KCL>@]a7p.q!:TY8","&KR?n**pK3C+gf5mN5Az|`;rF<Od5Ep&i&a/1K?>7Gr1n>4NY`B[9aXwEuglf!Bv","C<egiOS._&oE7mZ`^eBG>!30#uq(D/H&/7@p*_E8Y`GdD~}<GNyoOmMQI';EyQ$`","P{{E(T8.DzpC><anz*$#A3RrL9&UP~3W64nNxITG|IWV^I<lO]f;v#mLd|"],
  w 44 43 100 890324 890896 76 4211 ["F&m^Vkuqz4n<_$7r6_GpRrj0lw#S^pI4*&40>CImSp7;=GPeAt*i5und[TQiZWZ6","nl:J_?2%mj!MH?pVk@flebD4<4-%;hHeB,JLzh{;%8'@V}A.aVlixlnjl[ZOe*?P","al2,m(BUCaj'dFF^nX.OEA;-#@}]lU(jlALaK)6&|/(f>bXO5svgIDM*@jzwT:pa","YsaZ=%5/`f::G%#PBj$]qCpKSe6r.@wS&H'gPdEnW1fh$(05Rbq=$MBvD#2j%]I'","%~vi#`]z1L*/#,Zs9By90xE0E3*[C.P2).VCn_;%&Y36-lgDcNv2<V@"],
  w 44 42 0 900000 900325 100 5947 ["JJDf_IohNbLPM6W&]t&|>W}Q!G+-B4ZGtZHolcVys8DbUQ2LaK~h0!N(SI'nK38|","{5(hUXuUb'5c!>A5H:#Z7MdWXkR`*3o?G|htdL#JFw811K+Rta]OP:lCo*_,bHJ`","Nkk9ogmPUd/7#lu4%V3Jfe{1cKy@Z2@lWxqZCd]~w1]+Oqea9<vPqo]y8ZC?)jqI","9;{fkc>~R]8`S=&*z^Y97Q3{IF#U8']Hv$ey1ZVXL!^c$m[m=unh^;03E&Kyq8SN",".n<oaBiN/hrw~GUZ04q7:E<~Nj)a3e`^eB-9(dnW)b6XJi0$!tGTt,Ekc]'>07k0","`t$!)liaSNsb?``SV%X3[Rl5l-%WV7}R+COgW$`C0>>nhQn,rr<ZeXt8s3KYOu5(","!RNi_~d[S08L9=V&pMf*`IOm+r@5/LTAC=xQ{P/o`knn`0?)xJ[(T`uy=rEaxmNk","'D$-py+BFQ9tq{"],
  w 44 42 100 900326 900896 69 3707 ["4S[.+LY#FET=.qHwNK<Be_UI!V~Mh}qC$aUF;L5C95RyCfrHm~YSC%wd#S<k&If!","Ht7h'DlbOe$2DiNtF@vx|h][iq+D2>!A|jUR?Q6~9gT9%*',YW_=gUW54hqOwG.|","a09UbFmW}j5f4:._(H:Xw1V.ASygZK0]{%}Te@TXM4t>.u54d[y+~?jA-fn%Jekl","(G3kg}ajRKYKIYU<S;`*>)(S8@}dQ(9RS3zUB>L<uSu]/EjfMN4>3.S[9tklCC'^","(_:+e?AsXdd:'NUdELaWvc[F"]]

private def r44_10 : List (Chunk 44) := [
  w 44 41 0 910000 910328 100 5685 ["#T*.WS_|&}N-V{H/^M4~8Z,}fWRI53j53l9:dV|>XX;a{Y'1SO<12,w0zGUXex&t","?6;{dlw$E)'WN|_m+~p_52O:]smOXk37@T:&`Dh+t5z}oiTdoo#d?JtIu]2h!q]Z","p[IX1h1BbC864_.M+NQ_#9d;n$yv|IXgI$=GFE-aEx2j0l=IyI2:WWc+Du_(V%7&","v07~oO}72Si(*k5)fcZt'2CANG`|?)zdV6i)Dne!Cf-&#V*9{vcCB3C+STiUI#iV","/H]YS4l.Z)x@:C*DO5R8GlXEn8!NoFW!LFPcG!fEpczWTy,E*3h8fAaE3qL0h(+z","2+sa;@[jqRuz4jsG^_'H=_4}o#i=:31ZR0,oC0r7c[F!r-*e2`nO|Vfy&Kqe5=k{","54BW[R|.0Kh9jQg{!ptgIul0uicBTnw.-KF(YhJg'Vy1XnmB,tsr02dtyo=CATly","#/(%w6.0;,Wz'8:[ts3cc6P6Yu3Cj+Y$w>Z"],
  w 44 41 100 910329 910833 61 3182 ["[7!8XZ,CR5BezJPF{N`^8paL-EPgI:-aIT[Rqr,'vZQ{*o}w66fU#NuHwU&n{g5(","N_#tQy9oK(5$mU8sv=+;x~tDZJ5'4pV#tHtUW'gRL6y2$5oC_(^IQ3cG7!IPNgUT","!+xZ&7.'^b-oJeiPjV|a=`H;1-YXPQ)TyB+C9b]q3gy=JAK>Rpv<h,|3)~@u84|K","],k~~`g}Mfr<`U*DjiY.!je{$!D?'dM=~euO&hI?!LaaUSk!G"],
  w 44 40 0 920000 920330 100 5428 ["Kl[/$lm7oZC]=;9+bJ&6X}}]%KUb'T^mOYc%zC)uBcjz!FH,2=1sjF~aLxBHIWdG","h@n+:=UkkU2gFxvoW2M-pWv|A,qm'FbJ*d^V-B|^=BIWpG*fPM/GK&0%AWD9n&r,","9.SxW]pb)(yG+UBZ2o}8;GGE7AeeIx&P`+M_Z<V]{!MTJv~u2n<hQTgqqCakAGBi","#0I^w&$$[4nZ3h)gUTs39M8ov@-QhpffydfIb:8%>q0SH6Uq;XVGJpL](!^/(Dn0","~4Uf#B|t)I`,21gIW@FlH'!(rjak&z[EtJudq8p{zBzr0<HQdZZZ<*`2jMIrWtGR","qN/@S=@s,b.jqhB|18Exwp@iZr/^oz+!hm+Nc3:cxOd:y?:v|IOhtQv=V@2-7_)d","^*W'*8[|y=/Hb`r!O7/hVcWgZo(1b+lKYQH?}E`ZXiiv?gNxZ{Ej5`3yS(#T,z}V","$j_J85DBph&9/lz(g=Z:Or*sC(L>j>|2[@9V$fIeohHbl"],
  w 44 40 100 920331 920832 54 2743 payload19]

private def r44_11 : List (Chunk 44) := [
  w 44 39 0 930000 930384 100 5184 [":D`YK</YIlr/'yc=?o8A2>oY}h2{sn);+=qt=QgNLna>mW.QQpPpO>TxnNhG_&ZS","(wB%h[dd&VKNPhB?E'!%/c;H(c]w*[+OB+7mlgc{s|U(4OM=!cE[9[CJJoh]vv/R","~KbO;n&aIe@a%##<3Vnr,gW{`@{l$tQr{pVEuac/,6..0F#`fycR#smohGsMAmlZ","{LZsWZgou[[AhRJj,b21g(ucde^755J&OMOmpsSry.Q^5OH=i4;G-KI^L#4FQvvG","npbyt@%DAt,OkPk#YDi6x#&=ZN8,56(hr6Jr+bj5N`Aw`VhfrLHAPF'iStt?odx[","aH&M_[YKPN|y8biYkU,2-P:b`|D<bh]+$Ir<1!c*'UbcOeA=*a;+>t%14C*O%:;/","f+r|'G#44!n{Gr0I/;MxtZf1ulwuSTa>z*z'.nsp=_C!CT%`bMME}3C6#]x9]X*`","3p4@pZx9+-Sj7UhzXU@sBx`qI!q5ll]ZjHs3<wqVjUs1%;r<"],
  w 44 39 100 930385 930832 47 2328 payload28,
  w 44 38 0 940000 940387 100 4947 ["bEQS?Fmo^n(]F'R6'1RdDaQ><8M:GMe_*WxksdZ%![XRbb6{%20,zwQ&kVQ+B=i[","K!)8h2>Z}mpT}KwiutBgOjNI99q?L2OU^M)6W31l?AbLA'b8Cs8A*uS9C!5mgoQ{","PEX5#4ZA[3Y[NgExAJ.V>u;TX//v5vU@kzIfww3z(brlZ,HY,.Pb;EvtRsZ4?yee","3@q4O6qkC$(yg,^Ees5wP,v=4Oa@H'ato$i8`(^n=C>C8UQ;aCU)74.a+,4=DT,W","}2q$}VM*3hP8j!dAVT3VO_Db[w:wc'(JaMO`zu2bxNXr-S1b!OF&@j<9)uG~a3m5","5G=|T'-Bj$~WNWYkp{H15dvx25cm]J~X)zA<lZxC;jVCGMy1JGY=Fjw1DpUp-y1V","(7%rvi!Kxf}~[pzabrJVG5(4ktoxM(`r,6(/C?(i8Ro%RC<t-5q@6]O<h{{ip.:I","#mRFDa{i5'C{[MgJMU78yA#*&8{VCDBg|Slwq6{+1<%~ExhA7G>7H1?eXTx"],
  w 44 38 100 940388 940769 40 1935 payload17]

private def r44_12 : List (Chunk 44) := [
  w 44 37 0 950000 950390 100 4724 ["6F8{GM6Y4#d0*iJyHo-&E'}Hc|UV$4FN+;oH*O9wv'm48J:$aV/Q54u6=?0XEn|H","@=`rGHobkm)%S-]_X]M|/@o*R'|?.HrGVOZ7@}&}Ob!ztj#A|,8oTcj#hdvE|C]V","<QHg5Z[$!e!6|q!VI-@1m5/3[{3.a8)XLfaBKDIVYEzb8/p'L+;|,+U_CRQ]YFnq","79#*~|jTzm/HHyJHI@VXFl00fU(Fm]J%iz|h>t>.s9%r?WUDu[g~dd}{4g6NRwXz",".,#3>IaWi+YB<,;q(si/J0}sFH(>a|n?l_8$#fmzkS'!EYW(MuI)0mt-xjfb2]vJ","30E?Odz`Y@Yjr>{.1z#z[Y|4tAC1.a2^M.7D=R_J>u8NVT}V~0XO<3vt-w31{x^X","VQ<WM~k~IKsMYA)k0!DEx8SGk~X{V<wk8(i.w?3tITV%N&h3O8#e@lpCjcrCi_py","_^K`Oiw-D$7;)njhS51R$xL|&x=|Z6&B8F$`/Y~IM70~e!=1zX(Jpqb|`IHlUQd^","#I~rw"],
  w 44 37 100 950391 950768 33 1565 payload22,
  w 44 36 0 960000 960393 100 4518 ["X%HlAVyn-ze_<)Q^5U^T%*_ig*4=v)t~K%^YD+1Q!u'aR8;4Lpaj05RI0fF/,am<","~kRD=J4ofjg7^f9PT^@yg3Hhi;D94Vqr~}Y:Qtk<h`&)oZwh|I(H^K(<|>1!}o*,","{ZP9K9.QBS,+)S5Vo11'=W}6]u%*b$EON~>H3VeK#s6Ax;r5SY>#<`Ua8!<yJ}iZ","JjAG(pCsBj25$0|W#|'g.DBR*}7~QdEr+ukbR!}JoAZGQ&ltA?ab/T(1(q@CIR*|","03!?j8vlcz~>J/?$-~y&=+~EuJkEb7g|Hc'/x-c}Op.]0Ck9e&f>#qf2WD[gk86N",":=;^m+H/hNX^u%#S9N#X{-yC$IZHquku%snS*4PkIwmXVoCVC-N&Q+>.u2nUQ-lR","~0+&:5|hyZLtJ#SVE,g~DL,Pu!bd7tUv25qgxfn_^'G/2mo?=9^GW6Dd8l*RNSCN","2fS>ugU6(y|Y_+C5vkKUzT](w'QR[NsVIemw-';_tR5>o(Yr;Si;'B?,qQo>wr#S","#tZVq"],
  w 44 36 100 960448 960768 27 1257 payload1]

private def r44_13 : List (Chunk 44) := [
  w 44 35 0 970000 970451 100 4330 ["W,F%r{qK.aJOvhu<a#e};@qD1BqsdjH@q']D{{M2T[dfT38h)R@(MYl-q1@K-|8}","&8adSP1tlcxf8tN_7x<bN7aa8l%-1P,O]#+QXb5!$QxJoS+P_BHcmuk*Zh.J6h#&","?CToPQQ!s]/__,@i#d#2&+2L1|xFGJrf)Prv>*''JEkhc;|V8mo/Qd[^?=x7m)Ja","(|Lz^{W:=j^nLi|lh,fFt!M^V-$bS;DCha.hKL-s{S&KBgD[hgxA*4YoV{>EIcjT","`j!pMU(Ybqp7[=~'J4%c(p7Y&pdZR}vz*'-ZBFuHn[[jCii-z5haR/<Hgm#{wOA5","{Wf;+8MEW5j~b-y~6jTvJBo!_EwuSx-y+J;7H`Tj?7yWDV))6bV=SnsnK)0-#v}3","Pngw17PO>caScO#!-63}Fu^|z<$nU{`J{dX?Rtr8DZX!NR1|~~cGz_~PM}8V`@3r","#yCil`<`qF2uz''nve4$VhQvYIz1p8OS3O>v3$vUx!S]M!qW]I1$5$}xTO:V#^%6","1GWcPac4wTu9"],
  w 44 35 100 970452 970705 20 913 payload3,
  w 44 34 0 980000 980454 100 4157 ["8F8Ls-V01BX>]DIEHnNeejuuo5+IYt;SV_*Vmv<J5e1$C67T+~F'Z>)zM&&q66/H","yj[amGruP!ywI1<M7+.FZQNisRoZEv9B0B>3mN~$[9N(t1#.5?H9PS=ZsFM&yfNI","uP<jZs@,uWu%'Hq9dV-=pVcH,=-_yWnV4L(wQaO>g]p'J?W;<|UJYTv@?(7)>.)%","jT3%te/6Wbi>oOTjBaB`R?SXYR$(uO0lIIo=0Rw_lPZj;)_v{|[-W[w:x#?AdcKh","XwEqlQD59-Oxb1[;%$s{u(FmmL(T.)EwJb.[*)9fu{7Q5T8Os~f9|vdB#ksR?E(-","2w]n;V_K,-e7+aM{XS<YodCE6iiYp=Q!^E>7q4#7mHX:B$UcLYdv+tz-veKipISD","G]zIPBT?>]U&@pjvf_PQ6CIu`aF$ZT$DCTsp{DwHL`G[K<Gap:5R%a5medG)A}vz","(a`v5[UiE&:2UTuP,S15UT{$NQ.<Q>=x=up2(Xn5{C~vKV$gv70&@x|55jKTmUgi","(h]{l]k}_-Y2E{b7"],
  w 44 34 100 980512 980704 14 629 payload14]

private def r44_14 : List (Chunk 44) := [
  w 44 33 0 990000 990515 100 4005 ["~2M^^dx;jYU[M*Q:vCz7!a?luU6@8ua7JfbgYvo.mS8Bn>iGs,GyYW_7-J:5m6R4","<4E[7M!HsRJ#p;$.tNQQ|Wd;7S[kQ?Y,.'QE'=zr={Ue$GD?y<G*t!SP@_E#K5;8","3dI-D`D]t^|NEH8~jgpU3)ulI:mDrX^4s@$a#6uwj9!{ahZ0'1uHs`^yg|&k}BNx","9B(s7*;Pt=iUMuvQy(r2`:5XYWR]5[=,k/_p5H}2)DDv~F|%?MClcg38S@mK/?JR","R8KjO!;bf)8Z<qYSE{{.HN0L<,h2y*|^t;^$8W1NF9{k[$bP{]jBRRjvJdkq|C_A","x,GA/V'zOU!|OWus!&!Vb>lJd8&DB/z.y4r/PMq%qPA/p7zo8f/r=0}{1949`U}6",">C0dv)#&NgGe{D:bxM1Wt*2D%5U.Ge)V-,h[hAfGopM&E:lA@SMyvfhD<_pZ#nNM","&cV;q3*8*NAt/bxoq$?_$JXCgpt%qL->CW[Kq4|/;WA^e)?0)3l6EZT2w3Wd8tST","Ixq2e,eaq10->%[sK"],
  w 44 33 100 990516 990704 8 355 payload4,
  w 44 32 0 1000000 1000578 100 3866 ["M@e;hTq.xhT}.;uuCy2Zg3I3g&%cUh95!1TP`GC:WLby[Q^V%9a-}3Sr7];rtNXL","8vJ<D0K-Cx2f%Yo1?3+mOfdtup9DBXhCvQJE*>:|?lLFy{)^~gSPU<9}~mY!xW}_","f.H|X:b}E1~Jtj9$gfP>Or3EiS|YC?8c>tH.mc)~IP)C)+Fa2[<`=zjX!z{*>'</","KRC'ify4r{7[F?|OB22s:4an80zkL1K^7Luf{T4>k]#]%/XdtkkKx&#jRP:FdaH'","%=x+}`;376ATjIA6ypoL4I(uT*#_x4$9jFS&J9/X]1wrv@kz@Q/J{q-}gk{I]7uD","l,AcMN[d?qiW6xHbc6hqpfH<^1@$$hq]Aqv|?BtE4c;H1gm%2CzMw&-&/]wD_~u9","9%4c<HV6Yl?^Q:B*4Ae^Dc_=WZ4k;oX#$OCsa+<rx&cXJwOQ?u`IFSgCV!xYfn+.","lP>Or&R'Rt,H#`{F.v.t_EvNs>`iyt^$_YD]F<ONcl@PI;3nhbUg>IU:L7A'M$-S","#(M&wnb%8.N$W/<W[>YFhet.7,"],
  w 44 32 100 1000640 1000641 2 88 ["#i2GG<Je"]]

private def r44_15 : List (Chunk 44) := [
  w 44 31 0 1010000 1010640 96 3580 ["H'YCPaOXfW87|r*'5Qrx&y1/++m*(rB8-^Jz3rzQ.`QK-B(zT:SQ'@<luKdX@KhX","!_#VS/tf;Uo}aU;%vT$XHz)03$Y@yL_ldy%B+93z=YSMfJ8bh{NT}/>}ISoSFC1K","l^&Rd(7lMhD59#=Wwz|mf6Qx57H*xI,YQJ/oCBFY)(d8lA{^ig.E]H=31mx(Byoa","rKDLp4xh%WoPrnd38bVu[9l%X><m0Hphs6Leu%'[T`ZLLwly|c![)f%S?rx+KPA^","U7UymM$5]CmH!#9(./QK;D[q0gfq{v19'X/m(0@U;GDzoBx]$E)RZEg=Qtz#Tz~A","H~gSSB`u4B$l2I+N9dp01Q&yx`i-Uj5E,SmuWm~@=|W}'l<<c1y:UFxU)<rV}gyR","fC4~aRl!XEU^qv$W!<@m>6~[bEmblR26n!a>whN/ZGt=K'a9d$UyaIuogqS99#5:","L!*mI'`'mPL]^65Rw2wZ{qK10ohS^l|rmWG$I,ruY+qUvM~z$5nYwC<Q!W/*(TxF","6Qr4Q3KXcVQ&-uwo"],
  w 44 30 0 1020000 1020640 91 3267 ["OcM_@bJkZqr5|eEfcp%afy:!ut&=8-+HUm)&V(VLX/%5D(/6joQ|@+k>AeoXkQ0<","yxh3Rj.E9UlfT74/H-^.7w=$7qvTtj>}U9e;!{i[L:S#^AJJ}Cx^x@-g9;N6Jdkm","%X%)5R'dSMnmTr<l6I}AIcDk|*Ebv.@ZYN]^+gAV=@lBoxDUyhVbZ7tm`wCp+2@;","OXRn'+.mD&#:,*yhubyfHjaZ>=Pn#sW3jc@:y&bA>8DR941]}S~^=~;_/8)3R5?c","aG.-;&j=X3a8L^[76HAyle|wdRWl2lBpVUGVv*yU;kmm(TE4+`=w,NxQSvK36H:%","||CULl.puV:1CK4yO;ov`X65.kxoGUT|'3=NF&*4q:cd#,fzO5`='f#(4o=U]S0f","OavjL;EIEc4Ek/Y9;UF=uC`<Vq'PgOd[drn+cd9f}5cfV-N:!T5<HnR-w/^$5nZb","L+b(74x#(=!pKYpuNufi~oMrHq6Me.L]f>b)1ny$7oj|DOpp7Y;MMf"],
  w 44 29 0 1030000 1030577 85 2936 ["V;Qg_l58DP]6*9s/{/^QzX>SWK$NRL=0SnSxq|kV`(N,])Dm?}`@=c4Lfw>tBs)*","bO}[.OJ#OZWW0mXO445uylLBky46Ev+R<I7:Y-^^|s1s7}44B+k;!%2qH3WXgB3N","#TD#|{u3Cw}j^WmcQsdgLAQVhA(KJ2:{|WRiSbuq7uo+MJe_gDJC{Uy6x6)|e1W)","yGM]Z<)P#mZ2~ZmJM7j$]5wR=`mi|Nnfrf,wF#6Pd5=PpY=h0';*>&Y8%S|-gPjD","ZAY%~TJ=+qc?Gtw&v<D*<b%A(2pB+w'GLt_fV}1F1SL&R0-3FUBjmzaB'wzGt4!B","9%OT;xj+>s|%H%o&B{'6Dp+4K1GE)>G+1z93ssmkVbJht%%Iu/@qng0b`ls&h/!3","w'W&ZZp(2uzyR^$EE7{t0[iU?ZhMg&#,BE7#,VdC8Q=/n*]+NV03-q6RHR'/:7,=","(Oa$+Rt^tTu7y~1-Q#Hi7|%/|POWBV-%"],
  w 44 28 0 1040000 1040576 80 2662 ["=24JoaW9][QIXr'e)J3KJh8[TryFl;WQ*TBipuxTrHR;vrV+q]JSlj!,nQ]G>9m%","X?LK.aW)<oOVz,yUAN-cz`AYO>'~uK]fw!p`{gfYh,,0jGyqbI!3F|S.&mRB9UUn","UXK-/d?AEckFvzWB;F/T{ud2bB/rr;?.#x`m0=NG0xU|yfiwA68l}[Ghea<q~x8&","BLByB1UNU,Q~[,v=nK0Yw~vIj'K^CcuK6u1vQ=igc:$Xjx<m-T37Kwi3DC3()0d^","*%e2%[U<H'*iHO]pMV!,Lng{8x1SrP+w)z|+a}(a.pA_4G0as88F9cf%(YUrjs;(","'?(oTdHLLdmV#[0N$$]{/[uAi~f~>m0Z:-|VX]_A<BH0TFYyEl{D4[dZm(DhORwo","R4B14OuRf2S,;|+3YZwq5AeS=hlY6W]vXx_C/9rbwR+(-FW_am)FwK,u8Cvqo[t]","'~&nR@("]]

private def r44_16 : List (Chunk 44) := [
  w 44 27 0 1050000 1050576 75 2407 ["%]i^K(W8HraWneC<T<A!<jfKU_/=]PW}`N&<y&U(0(GZPvSf4PsC^hR9fD;_H15k","h27A/OG;e_5Ce6i!MlLr%byi7']#C0XED7<YuTsXJmO]>/.Bs@-428X7vqJc1.}~","~5_G]L*z7emQfP4Z2-72{Vuc3yZoR9<u<mpI<S.jN[zU996RtgkNg>'_3aDkE1QM","X7YZVGp-`BUjM18X.RLDMY<daU!<EM7wL?dCOba-M|&G?_9%rXV390UW7NW!ID5y","V]xChSibR[eIq#m/-Ah!ilK]Y&O9$kf||8YZWS_17`8^J}9uqeRLsEFN$Wl.w53@","=H:94'ED{l1'T~&'+Or(yVt<kGdrE:RL3T:uVS<;|(qC8V51{{CP}c_.v8~32yH5","*vrVG%GcoCBfVQ<~yO8}Y|27W.GH8vLNe-`N)O>s!$Pq3EB4d<"],
  w 44 26 0 1060000 1060513 70 2159 ["g$}jb7Fi|wk8,9|/[+GToH3@iw7&]49hVobsZOFUr%dd<~A%0HWGn~K+3KIYlf|C","$/NHdDzWC.Zy.r+34GR1T-r~UEg#le6N@M~jIo98!fS``ygOb|S6}8$_TrEkp>_K","Z&V*#gv8$*{Mz9k$,A1&zBa%jwEjf@S{np5hv/{VHbbXZ)w=q.DiPYP{13$7N>J+","KQ2LG7%!5PA=]4gCMV+@^H='~rfd-f@Om8-gW`]bvlXU@DIE!6[yPasD~u.kX.|B","?X,(U&c|$`]uJb_M7vb>x`iO+/TFL=%eJ89r|YVUGlgH|gZ!fK^1N0[r:Bc)c~!<","MCum,*#luW<Z?Z;LkE*TRds>Knk(22BCObiPLOW!]5FOKa*N(}Fp;k-OB*4y!3[g","'KFc_|4^?YQ^p},r33AuL_"],
  w 44 25 0 1070000 1070512 65 1930 ["iGM_8x9}#i>gE,(A{p0(T{w#u[=Wi8p=M';N>9+D6_d!$=GpkDB{{t{@jg&mX-I|","0R}W~dl~K0*`$Z$zLP_9:x=@%oywJ;=Yy[:f[f+%MxNZ+xBx%j<qcm%W4<yXOb3L","0*!WzL+SB,{3IMSYklRJfe!u0~~V@'X*qKt1!EL'yva+U+,|noJs)blO<P'i]kI5","f)ME}gO)`-*nPej0ZQzcwjm8_Tm<34Z5!mANY|DT(7@I=Vl#$)LgInPaxSk]B-#8","RiJ6p-/?3ZbXkk=o5y^cSdzWwM[dFio;*gcFqOw4>+.u9]yfp!.`a<ur][*E{HDb","Yz+vy#Hwp]8H`-J/BLK@~&txK)@84W3E.=e<&Lz;;Nq7ps9>IUO]]pKYogd<b!"],
  w 44 24 0 1080000 1080512 61 1742 ["JX!?t,6CbVsg];Yy,#4Vnan_I1lGiHj'JxG+K}QGRRDmL#2&U*{v*J9Z'jtnr:!n","I*Qft'=l<2&WCR{BqI$:kA802+%0y2_}S/nhl9ih]^^;D5e^K1/CN7wk4gOi}oC{","Qq?s*5=6j-hZm5kf5`b<R`Ju]u8)zLapPo$EurW;=x_>'oa3KjwKnj%)*Zs8u:FE","S/y:vnn`CfEWuV.m7/5ndJ3O[JdD;Og$1Paiu>C}!@?_3:|byj:M:Y5H>2S~y9HD","j[$!@4B#}n:~h-VI70y*2_nm9@tgK)`T_HUF{%>e_$c^iG*SDoa2D[u{qk&}g{Y!","#W;FkIRS0KsgSbC^V1!~EwXzwe$y}<aB$MZ"]]

private def r44_17 : List (Chunk 44) := [
  w 44 23 0 1090000 1090449 56 1534 ["5X<vHN:?YG,WqW]Cr_h*MTh'B)9>'Ay*Xa[j/N2WP=P%U2d7ndbi?r$d0tk6(?Fn","-%N8;}Jn0{Vm:B{k+7_Tlzu+or!<R9&f`?iwgzCwUFNcKwRvFm~Qn-pM`Kp.}:pi","!7nf/mnK5e&]6Xo@W.H8uy9C{{.C`F{AxMG|mPr7oSh,(eN[FCgzdl^5aNLWzj9K","}`q/<F2AkfvF-AP.@a4I&t_VLRwLsptvLkyOxUE~`(p$r:-^q*$x<pw35w[*R(k&","sLU7hvQU}9dLH7?[1o0O7h.}s%>*H;b<1=^PQWYF/kgxD8lJiNDf@`DDJOnHOf1d","VW8ha{Cl`a7"],
  w 44 22 0 1100000 1100448 52 1366 ["|&I)2U|a6v-M;K8SQyp'OH{cRg9^fqd{P4UdTk4'+I(Q5!R?416%TLUX$(4?S3C{","?df)Si>K9e,D^[/@|a+1&U%@#~w#u6A',9S(i[`~`2%OkPkYHwhxSEkvgxE+ZHeL","t:d:e]$!0qJSq'YV*!8Ha~M:@vW8~.U!u52uF()OV[D=A>rzUW~]dZIV8dU,5;yH","}PTmud{93IU;+/dE0?obrWhSlX?jMP7}jk<,33V)Bhfx`_/Jlqxq__oa20']7t.Y","2s:c;^lh%,YbAg^cK-FBbE/vTG&V+`aa0ws}B]s~A^E4@6Oe.1/"],
  w 44 21 0 1110000 1110448 48 1210 ["Zh_bJeOkT,pY|*}/DMSzNY`V&+H?DT&OwrK2WidZRL;/AQ%VGegrfIm?8+$c~rK9","K%+4R&tePnTt`@C_WV5`1Bk2NOBFcxf`'1@h{^x:ECD+XZZjHJRJ`o'ib-3Gh[vY","38=]/#;8(ps_NMRUvpE1b3$S<hB1'=}sLmEM)S{(U+-]jo;BCyB6a]$,MXA+9AX`","].Gn1)6f%/7=Ir3e'K$f*:z]K<Sw{b:Mz?HrXz)vKoOAB;_32k[{]!X~;dLc@{NK","2*XAwQf7E&D9V9MWwqV-(66+H<"],
  w 44 20 0 1120000 1120385 44 1058 ["ns#t!{q%B8,<O.tV%z3{i{#NLA#qK=Mf8T~p9oFi!+cGr:*KTqD[#!{4]*vlY/{w","d)x6p4eT}?Dn]'O0E&W/ZxX@WtVk6VKWnUQE2)ewvre1X^#D7WrEtgrW3o{!H*LT","-IIUh4~6w;cO/7j=!r!Uh|XW4n`zrjLYK*!Rp#|z]U[@DY#hGG<n2kA>[n_nm;KI","%sb))OX`.!S-4~a<#,=lMzcPUPSXTAG}6{Y@<1QsNn5&J|LG3'#?N]i$%Cbt;_30","&p-D0PgKl"]]

private def r44_18 : List (Chunk 44) := [
  w 44 19 0 1130000 1130384 40 918 ["vN6L4~VEAXp#NUeSGvW^xDzT.x&Hr`)IqW{KfdZv8N&JL(G3>Ntz1psb65r@:-.'","UO/m5a9h;M0YEfiCx%uRjeUNKN,LqIOMwAA?Cr{!f0hLtqzrg2-spCf(sgd$fdqb","v<@Nut,1o'D_#9O*#*w;IHB)!-q)#|Xpc_'jrS=2XEZJ)UV+^}Br6G&B4{X*)H<:","$n*l;zUDdPcI`m>?{/S?GS;ygcxorR:i_mG-?`{NRKD'7q!:(ErY%tw"],
  w 44 18 0 1140000 1140384 37 809 ["7%-#^?Ht]run^'uaNvbhx|E{g!GsG|/Ai#|4<RQCqq+Hab5Ps95r#m:;p-XN,V!g","?0^hBQvFVGKHSO:w7%${71}5_t<v.coPf,6jbf$B_]p6yc4`v:dOw3*0~%8L+BFT","~Y$s9G)%bzMQPH=aD^Z2y:$Jn:l'e:<+)a*qO83pbr?Zbymg9.Ml|J47PKgi*YEG","$*Egi^@$aR=Ym`?V]9Sg4.jxU$J7j"],
  w 44 17 0 1150000 1150321 33 684 ["1IonO@kvxc~GXQyLJStTge2!,dkB-0Fg{U{26Ul3W~q~S}uK*GTZs=+OAPv+BN>W","-S^#Z`9TgcE~fwrd*sLegQtJzc4V-R=~q/[;A10w%nn~V5NH}@SZ$/$qxz_9AK;@","<zV8m[c~c4w$$DK,`8Ud*Qd256#,t^c+2^8'Y`8Gd%Q-*~_JWidq6L+nu9$P_qs:",".g]{?xO@GqI"],
  w 44 16 0 1160000 1160320 30 588 ["<P>k]3leUW7zhH$P==pjFA`a>aznl(S./6o5-i4t=S!nS5*[Dl%tH%K)}xk*gOfB","`b#KaIgF>s)Vf#PPjEU`?;b.>l^lMU~B%ZsR%,t@J66#Eyh@sD|Cu~,R3-ib.baD","#A0CF?Z%(WeExWh*@`cszUk?[`HxN19fDbA[8*H0|/4We/f.*2n8m%AU.e[["]]

private def r44_19 : List (Chunk 44) := [
  w 44 15 0 1170000 1170320 27 501 ["5j%LVdw,4(4KG/(76@tnH1hq$N%5iN/&QW7(8L?E^#Mgq|#(H)8_1~eF|r7p;O@N","h}V#r4oaC2J<-1j$P|R2/O~`660(ft,<IGf!dT:}LMi|{?j6Yao^c'>}T.U{$2g`","4R):kB`3P?!v$sJ,`P5h]wqu@#%)vTe[#<GOQG|,R1="],
  w 44 14 0 1180000 1180257 24 417 ["!P~y`p|)j$$1*(]LGv@9n-n+xE5smb;2#C2Gg.G.*N-~IBl:>*(OCNCBG,dr-s[k","j>%#VJzBGbuTCI0KrFPg2.>D;k)<+P3>aVg3kB'ef+ek)&]df#TUNWt'_u^@5xYY",">1:)t}T>j>R0zBPdwwGh_XRjV"],
  w 44 13 0 1190000 1190256 21 342 ["pVNtu0T{h.xGoL-2+C3E5stVW$voN#WcO6[-{jbW:'4c+G&`Jg#t8$XaOR+&`7K[","c_wp*w|n;[f[n)9_|nV!hu?`8G`J~[<*%=SQG~W-,ib6fJx3F5rF:'>TQKFL@mf5","$p)1J:ti|Ui#ad"],
  w 44 12 0 1200000 1200256 19 289 ["86C}a:>gL[1])Q?0Xg5h'p$K!#S?jQa]`Sp)@ZTxY5XL$vd8PNO|K5#w&Zs+@v>f","(jo5^^J6W.Acz8QU2(+#Kor&?[6sw+BTupfe)je/4=n-)|oQ?Vs#r06V)X"]]

private def r44_20 : List (Chunk 44) := [
  w 44 11 0 1210000 1210193 16 225 ["J)yC9sz$m6xz(?Q[JE1]H5257nfQD6q`CB;1UCOIo%[>+'gDtGp`4*@<Co]?io7[","J?0NYf#OCnUw3RzR=s_Zv#||)!#=w=A)P|xXl}}d{(g{,$"],
  w 44 10 0 1220000 1220192 14 181 ["`dkXwXSKPHi/AgFm>4KP~V{os_,mCd(NR(@p[CP~WH7zL?0mc&#g|Q7[9wrq(p=!",".M,d0#s$&!A.*_qHfBO5daUZaK*CVn"],
  w 44 9 0 1230000 1230192 12 143 ["fROT,U<'.LY/%k`]m)d@Vg7y*2GQ~W$|M3!qpBQQlazW@*jFDt#ZtS0~O`KzHr4>","qiIiYy/.}~Ou<F0S"],
  w 44 8 0 1240000 1240129 10 107 [",db4_p4>l;Gt/gPgOH~)heRaj71+{,i{hq&a5j(>iFx;YY+jRZ7J6w$/(a,+[K{6"]]

private def r44_21 : List (Chunk 44) := [
  w 44 7 0 1250000 1250128 8 77 ["2eCiWniLTdG}a1qp:EQVawa:qpYjayuQB*{u'E1*Mj?qbw&R<3Ayfz3"],
  w 44 6 0 1260000 1260128 7 60 ["%#5Ar.5zdM,tEgU>(mei],v_O3/I'G1+K8^{6J$AB5"],
  w 44 5 0 1270000 1270065 5 37 ["#V|]v'EWmUkretV*(G^m8zF$ZY4^0N+d;"],
  w 44 4 0 1280000 1280064 4 25 ["&wX@-Rj`rboD}T4#m0'uL'WJ"]]

private def r44_22 : List (Chunk 44) := [
  w 44 3 0 1290000 1290064 3 16 ["'Rm)M$NE#Fa[FAR>cg"],
  w 44 2 0 1300000 1300001 2 8 ["/#P=H7kXX^"],
  w 44 1 0 1310000 1310000 1 3 ["<NT9CZ"],
  w 44 0 0 1320000 1320000 1 2 ["2Xm,"]]
private def chunks44:List (Chunk 44):=r44_0 ++ r44_1 ++ r44_2 ++ r44_3 ++ r44_4 ++ r44_5 ++ r44_6 ++ r44_7 ++ r44_8 ++ r44_9 ++ r44_10 ++ r44_11 ++ r44_12 ++ r44_13 ++ r44_14 ++ r44_15 ++ r44_16 ++ r44_17 ++ r44_18 ++ r44_19 ++ r44_20 ++ r44_21 ++ r44_22
def rows44:=rowsFrom chunks44

theorem good44 : ∀ r ∈ rows44,good 44 r=true:=rowsFrom_good chunks44

theorem sorted44 : rows44.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks44 0 (by decide +kernel)).1

theorem mass44 (i : Fin 57) :
    bandCount 44 (i.val:ℤ) 56 14≤(rows44.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks44).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 44 (j:ℤ) 56 14≤mass j chunks44))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total44 : (rows44.map (price 44)).sum = 322422 :=
  (total_eq chunks44).trans (by decide +kernel)


end Final50RankReceipt

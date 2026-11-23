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



private def r45_0 : List (Chunk 45) := [
  w 45 56 0 790011 790326 100 11741 [],
  w 45 56 100 790327 790705 100 10517 [],
  w 45 56 200 790706 790903 38 3348 [],
  w 45 55 0 800010 800323 100 10835 ["u&FTLn0CT;H[$#&%:dR3gV3~qNd+#@,a>vCw>>5~FytZe>uy/Uu2(jqF-4K%y%FJ","[q|SNf8BXv[vlY3a=lL#tw0SmQ:+FFo;foZk3gpdw:k@/}Ix]GL;qY?FuT.tcp*~","=.V}S2[Ya~qy5$48@#ujO:4M]2d@xc~PB"]]

private def r45_1 : List (Chunk 45) := [
  w 45 55 100 800324 800705 100 9573 ["^50xHogbvSC{?rmUq;NbI:98'&f9aGP5ik^nEC@E7q/B}`-UdE`cYl$E;'M$5nSO","mbIXsNC+9V^TlKWP(|%&T7^anRZ}reRhz7j0n81k]g9qVm`Ru3a&x:),Ig%A-s6F","#Nx)#T}l;jQXN+WQ!3+L+FMk,%vR*6+Y7n1ZX8Q|X"],
  w 45 55 200 800706 800902 36 2916 ["#l3!(F%>(F^rGj1{$H>6}0Nf04{j`QUP6_6xq@62NuKTeoGlY+1;!^vtwss7O"],
  w 45 54 0 810009 810320 100 9986 ["rbV;C='@ul,IIffpK^1~tMU+XZEU0Y}V#UqPFCQ]E;u_@2!)j?A=C[#*6/o`Cj)w","`d^v+U[ZIS[e6uU7wcL#oalo0@=o>Yly/uq4{M63&4Z|0PGO|t'{pMmD]>nrp'C,","pb1r<?B6PmC=xl0JHYDrNRRJWII.y9}k7AE_D!]+x(P?o"],
  w 45 54 100 810321 810705 100 8805 ["'9l2x?~`}s2I<1f/>U]iL0$|SM.DX8Og2Rt*{a~PL6%)0zGi0%FKzPltCg7<,m*[","O|S)(TO6=w=E%%xNH4cXK)6;5GLRQB&p-2S8{-Dzu9U-$a@'+U./@/l/f?vjM!8V","c+~fcC:V4zzH)_q%TV|@5uRl@kHXQ:/cjb*<TKiWJ}jhHe/2m2#$;M/"]]

private def r45_2 : List (Chunk 45) := [
  w 45 54 200 810706 810902 34 2615 ["I-XecX600$%'7d:UuhA|%!v%rlL7m53,Bj~j|ZER3we`|K?uSPJMs%*y7nq9mXz7","09TaAH1."],
  w 45 53 0 820008 820275 100 9380 ["Lig8jT-f>+$@?8/>_E[3Ld5h2x#6X*1#(=Sp),<mp2]?!2C&[+ox+a~Ul|)RHdhN","%Knh%F5.y0JeLY0QxLY(bN`Ua<|C>St-N(IVebPj4=loXJ@;`f|F$nnH2<j9-yWp","`$^{1?VxcL&ok$evXvG&E2k9idjtG'=t@8G}|?g<l+f-j;5INoB-IZVlJmu+C=RK","Nl"],
  w 45 53 100 820276 820706 100 8162 ["+=<aoYZd_##ZSWO/Ts?@w@(s($OS8-*Au3S}$+Pv-B+lx:=~BURkuf}#!^[^5:K@","_7U]47qxV}e-^JIAaffH;qL{fc:iZlK|m(MSe@6!y+RbJ2AEkdg!=p++Q|;B..=D","F4FNk_%ElCxHCw_clt48BNbLGSHf$!xXFWqlIF^Ax*H[gpz{T#.c+q23Nd5Fvkn*","O?}&XTu*ltHp"],
  w 45 53 200 820707 820901 31 2297 ["Y8)dipjX@jG4l[O;$W5E%3{D2]{pQXiXP[DkwwiN5aQsZ'U+N1;3(KiuJXkL|m^G","'#+[n/tqjx,6:zvPG(<"]]

private def r45_3 : List (Chunk 45) := [
  w 45 52 0 830007 830273 100 8896 ["GFOQEKq_D-@'uybW!h.Ti1vmyKcaR%4hs3sq+*E]<S#03Me`?ZxhLT3n6k,E{RrF","uLnny_6$,%}18GO:8prl,Rt3GT&n>?`O>BUHt]&Ms5g|*]~O;tS_GWjm38.hD,j1","hNrntJ;b=a_VH8|'o7I]YcbzAb.EO#0cFwBa/]f%Q^E'S4pv+Cw:(x/rZdsC!j.K","/`#J?FR]^F#gCIh~vS05Jw"],
  w 45 52 100 830274 830707 100 7658 ["295w6?v5A6|0'8x}LP|SANRLh]@Q'LOIR=:=E;,>Lv(_%6a?:+B7FpwEuyJ5IAfz","3,M2/nEC8@N_63NBE)j{@fMdhCFUPlzF3z:b[&d#56x[D780Kuo9wR@_eEJ9%Pn6","QL:KG[H=^u9HHS?f>TPEH7#W`%_z.4tHQV&KLU(,48cvkSG;&45:%63,'>~LFzU+","0ld^k)|'g<+r#G;^e-b2(xzD^0DlWS0?B(3a<#"],
  w 45 52 200 830708 830901 28 2006 ["3O/:#]]U`g7!b+?>NZ{{Ioa{l7Y,*M##-tqFO$~.ObJ==2}Ux8}q_tZP^nLK+[ny","9EO)_@2B@OrdZONnV6N="],
  w 45 51 0 840006 840271 100 8556 ["~?o_;RS((!?S$_ZJ*'n}>U1{//Eo@_.z}SYv/agTxb8`B-L$m?f]C.})&<$*>l2Z","-%}8m+B*|fB#M<CJ%&tX:k_x)hqZGKh(`G-u+?S;>/MXm&N3e8onl&IH&6G+0zw&","`$h?@ScD;DyH)Vb4kM#i';I?jcb*|mrn0?!~4tf1RahOyrXC<3fDXvd[;WdTRV']","#8hou&[gwD0u,bOro/I]<G$ND^|'Pv4F'LgX$4(2$"]]

private def r45_4 : List (Chunk 45) := [
  w 45 51 100 840272 840709 100 7288 ["aL[?N_EZV'~JjU,o#kr|{}^S'oev$5DI*UtEJ~iorV5R3L:7;YB39{p#VpPYV`2-","LQadgO`IZb39!k$dEBd(<XpcZ~YPSlt~<cRIV%u(>9*Z;Tj%j'5#[l-7}uXPgJnM","Z)K5I9w%}>m|2z^AUP%l{d->`X83^01w)n|}U%#RlJsRVR4dU8D^@Ajq0=le7E(t","ud,_:sZbm)|les*3YktGn=&I:.Jn*{/w!.k4Z8ZM1duk[}jJ|cN|B.'w@Q8/ft8h","R6}|#-K`"],
  w 45 51 200 840710 840900 24 1664 ["W|^M*cjMYy8sj,R&xn{9>}>rQGQnU$D'.QkT#(.^Vt5|*NTjaOtlY#kcp:]x:[vY",")~qsQX(8;#L:"],
  w 45 50 0 850005 850270 100 8244 ["W*d&lu[ECD{K^8yZLuk:_&|H&'lh?auZur}-,bQ*9f?1~@k3~MS|e0C;iZq-h`ec","hXp<|WkKQ#T9olpL%kXshWs;v+=puF&a]JeuI@p!6{+bCvo(?TGd{Xmya^(zoI96","ims6HQr7<s'E'jt)MmK5<Cm^@D8KgP45i%E2DO|y>haoj;H[+~pCi_12UyU/G9WG","#g7}EZO3UKhbI7(%;{rKR|5Bsw[J][Gt)`s4Oc|b_M-?SPg^2[/akhgnTU2Oay}"],
  w 45 50 100 850271 850711 100 6980 ["Tn,PAJv``Dfdv=1LR$LTkqo+h$RP-{7WuNO'g(:X9s=)H/fWc,yKX_2<@._F5@pr","@%'T^:qW@K@~$f~22!kKIv39,66lW9]a/dv[KHJw}#,o>9F)>'UH}YL*8QCrH5Rz",">a+[&6rG9)$x0tm/z7rUJ^Km5K*<]fAwN6,<:CG?Q]cKV|*5);L@.g_,KgR~d3X`","cf,asRb]j&Ih!,A'q_S9|%jU`%x>V4VI@hd[4-QpGj@1d<>c2HA3!/!YnJL'.lCv","09,6-:}YQ.|zsz*;M,XdQ!#);;Rb@]$lnuB!PVZ"]]

private def r45_5 : List (Chunk 45) := [
  w 45 50 200 850712 850900 20 1346 ["hqPQ]8d%d=SE>lyMHRiv)j35fu&ay(qh-[qn%ahIc`OdTb}{[<g.NnU@*2TKZ,M"],
  w 45 49 0 860004 860269 100 7964 ["oaRm5]mh)!-]&RK>+}Dg-M0;E};ib^Ge-,j6'jd(:+WO)4k[r%CQ.AOK7JXUpY96","SGbLMXiP*]S!<^%2W>1;OoXbD$&diPlH^/5b_RxvL$<h*6Q/<f<'~g6X[?AMzM4]","2/_<{LYZi{6:>,IWH`N+K}JPsd+HP'6^.y=-/>+,uB&l-),kIqcnS]f<`(A1i`H$","qxp[K7r!,!ndvYmgPJ3Sx$#r>kIF?@pwd7{l+TJ]bt0,g`sX.iGu}Y|o]vT{Yf:8",">uR;_':$|[~k8q#pT."],
  w 45 49 100 860270 860769 100 6704 ["du/^xqM;2=fa)RmmJeOj~Y}9%,v/IbiOz9y[NqQP8jAsS$DNhL/,t-X~#SW|%rCH","3Y};dM*w+0~wdgg$[Y&dg0F|D0(~OC<d7iVL*xT^C4#he^4'{B_;QdS)j7&|$bdW","q2ttCrAHuSxD&9%0CTXmGd~[Ntx6TpPt14Jz|+Hc[c)gh-QZ/8U*_<mK%/t2pS{T","G>vCu2lncbJEol=dllRr5kL/@E!<HTT]B!Lw)-J_'%'`0Y1ZMwq4[-%mwKLldx>N","07NDTZEc#M9bp?ukpva)u4jz>7WEy^'d6[UJu}LTPC0sCqkGv%Pj-dk<[X|}*azh","kq;4"],
  w 45 49 200 860770 860899 15 979 ["*UkgDIma%;aS+WQZ=y;<zxD8I)DYbUTzs:#'ce8-@agVQHf9R/P"]]

private def r45_6 : List (Chunk 45) := [
  w 45 48 0 870003 870269 100 7639 ["@)blLwkuuC}l#5vlWB3,ugQd!XpCH7f^yg|@;TP:@{.rWU%YiDNB*v8z=K+~*`J{","$HB(hE,$!%9_Q!<_hMS[oapR@eFj@S8.$C*xP.]S!{'gcRyEtu.$&([)bGKC#=,|","Rww;(ltoMf%T{~tw]C-P6sm&8Uo29?%3D>BESMt*!WrJwQ!ox(N+ic||DC-&]*fl","2w$aME&A{Ao>U`!xI*HJg?iC@}z<-9~#30oRh`Rm7LnrE[a`>Yeo20G8*OV42^w*","JJV7Y+zm-DJ>ePb.ezO.ek>pZ0{phH+a)wCR.j~?"],
  w 45 48 100 870270 870773 100 6446 ["rv%bT6$N|XX_5]cUJ!$ZR)+}n!?Ane]tx3*U}T-OU.r)*!-CnMi'OtaC8r:=Owvj","0GtK2*sywsR](iu6Q-c8Uw&#ifF/X@0kaD&}e(tuz!^gbNIDn1P9Fv1si@=>65wa","WP=KIZnaA'x+1?c_Qn,rV,vF,07Av_3?Yv7LxbT(54cyhN_*W/uE5`NMunH/pUW9","<v5f8]I-Jallv@s$V4?{'^UBc|m]4|BX2]0zSG|7@|=<jQ<_{kqPme:5;p{t21uy","f&z5jr9{x85V,tt;*S+1#;x_qmQ|($zS_1d]6]HTfs:d=nOaL6;JIm[/qE}z$oj_","#ytS|h)[T:9$%Txjnr<{jE()7SN:$4gqA"],
  w 45 48 200 870774 870899 10 640 ["4~[f]_RxG#{/o|GJb03/IcErY1Db]n!SH"],
  w 45 47 0 880002 880269 100 7353 ["|Um]A*wz#_8m/UkO[Xzv%A.PGD-r}3m7xv4#u52KHpo]?c~Of!vb@{y_ns,~U'Vk","jko!R495T7AOvd2#TEMN*|2]Y:Li8/+SQV<'s0d,6tC!GjE79XAs6l-Hu9pX2}Q*","{LQgb^Ar_4l}z8OqlCn+L{OrL/vj6<>2GXfgyY^7;D6}V[SQWer1Y:h/%nR3,Xmi","hB?#n):H*BEN+L7@p(:7V&+L!3E:kp7O4Xx^lM?c.0H-i8E6s5$iz*[!lt59@Hm7","6A8qn!sahZ'}I<j36&a~y@zJAiOT5l)FJxFz^0bF~Q}_QQ.Wrt}1[j'$:9,i#"]]

private def r45_7 : List (Chunk 45) := [
  w 45 47 100 880270 880835 100 6214 ["Jr)j=ckcx)Sg<^:q4qc8<%:+bqz;'n?XjS+amQh1W7MS.tqmEUC|5`Jpw[>>JM~Y","%}NPmmGO!y[Q'!+qwR1Y!dv)vyv56Q*M_XM@I$k/?r!LjkUt'IZ<=*@&H`s6WC`W","HP<5'oe~Xd=x1u^,YTJ_{$j'rq+]j~q{^1}xkyp3OYZjC!?cxtIw9dm>61Z-[@*p","+U]l6~FWe|<;fI;4vz1abq1<3y$2+c1M%5~mDWs2%3XaHI,JLR!}Mt)gyloiE[A1","n?NoSM3m&hheee=EDHAbB>Bo(fBB$$j!T{+H5xK>t;'!SR%l;l*q;wf&J,Tj1{3[","$qwcvaZ'CeaU9|U!*Kr:V/~,pxkM:TC:cwqet|`cqc~x&]-[fpT/]3'`L3yF*"],
  w 45 47 200 880836 880898 4 253 ["#JP,W,xmRku,"],
  w 45 46 0 890001 890270 100 7017 ["G}:wPP-jP`Q+n{<@^<a%3D?FbNH1vbn^&%iyqWk@T+#(AfO>NEVC}2m'n-F`bp6k",".csi#{Lf;vDcLpOdKsa`|TnsWSE)uFkKYRHT@[A_08DPvxTEGsIkoX*TdN]K~pO)","G@q3<%QR'5*g(U&36]icbF~yr@o>('#VJ<)NrAO'7h(,_f-`v?9?4&_s9r-Lp{/t","a|dB{wvsy&&Z9x^h#re+R[)PbL;`<_r=eP>[Oednht-AoFGWpU3~Q4/)R,<zWQda","iDA~bVNI4t{/,+(}Z>g52:t{15:|di3eJg/W(n*Pm_g}O+R#m_&B]1&0({;]^%!w",");x2_LI3&Qn]%]H.]_"],
  w 45 46 100 890271 890898 98 5891 ["-AGAJQZ`R#,j8_wZf&}[+VmAO4J}v(Sf:BU-y@c;f6o6'T{`ALFC]ZM`K2xIXFh1","`yuT~W}t26)5rHu<HxHBT#g4[0,$L7Jl_5Q#U~&>FE,oeK~t%?9*JP7[}a~x=0`)","/#a[qn#|?{klxQ=w~wq,Hs,5jg0&guxOB*C@1%isj<;jExO9j31CadMx:[!>pfF*","hxq+eTjFxBnG7)Ry.`t|U|:3J8]hOQ8>m<FX7ZdJ%b2Ob->z)_nt`>@CccWJ684v","3KWm*WK.2yzH#@{z5[gf)Myu:o4x1Hm[3+r+(Q_1iS|krZ]vSQ%59_Bbtdz_uPfo","W3`N(8!f5^g6exuM|o3>Wwm=l-7?8b*g%Ar}c!Wki$AFQu[suF^-))`?T-ubsVF1","Wt"]]

private def r45_8 : List (Chunk 45) := [
  w 45 45 0 900000 900271 100 6721 ["*^nX6HzS=xd0Du@[wZAcqEtn@6PKaYyyK|,D3%f*.|x~NkIx@U3c{X'-C_6E+a{k","?VB}>-fEP.!)wa|Z+R^~$-))@;7`:c*ay'G8{??)CjXbo~.HzOL_x*mkG>=xb8$r","YlG5njD_o?4qSjy@_=is{#CGx&2'uR8LGdwTM2gqnoA<F:$hR+-DEG>PvMX&8A%0","4&~<[smF%bMBtE-Fc]`M6R]:)(a5n2]q5vj<]6.C65[mZq@vr+4Rr<KvV*(-n)k,","h>IgIa_t/&wZ7*?}7'%D/[Tz]E+zLRR,5gcB#XDQ?bV^n^/Ux}mo|z9KQdF^7/C)","%zik!E%aDw:3mf=sNUX>/_Rf!)8}.p@=zKqx!%o//~2re"],
  w 45 45 100 900272 900897 91 5292 ["KjJ'R>O{FF@tF[z@9UTvR5Y}h49tUs}Ic7`U,sRg+*W$J1g32xXKf>eZqEgP;Q/a","Wy3(P:w_P?d5zu'e{g'rlPw?;`u2{Dl@IuJXM6LE,Fw=C5XRXPB{Y=O*<W,EW0go","vfu.p7|H)fIh0t$0tE!P828@-sl]F^x5|<T@ND[,q|DRAT^}ufwNL0,3HqKC|J^]","DP[lUhLeX$S+lM8pyFWag8|N5lQuQAG.B&*-_Mdq%'kJ8tL$:g%Z0Mh9Lq8Zd8F*","NrL^5wUf@l}hob>0pp!+ON0^7&-f1^N=J,;[8}vPj?0SMsan$pj@5{;sJ7[z#uSK","$(w&_%ous^J~$E5{Y17.}&qn@6ikjqLi_=fg[jMp]nt?u&Pq~n#u"],
  w 45 44 0 910000 910320 100 6375 ["<7(>AtQ|#R0=2glq6#8wK[q24141:@=XDqt(SBwiF@aeI;4Y-;@w/O^d]OBAAkbO","*_=!c+QAO>NWEtF:G*LF,u'k`~3xi4cX+e27CIy%P%6{aMa+:=t]8cAq{lrd{/Ej","|NL->1~tGxMPQq|S0L8HsI+F[L3=t/UIny}_Pus)[~M{>ZoyWUUy>oAdG57jw{1b","b.&6$rv*V(>T{Q9'[mwnR{HylvALs4+TD+>(b9(*lF?]&#C+nDM5.hG*?A>B_k4G","P{zA+IW=k4MZjoSz#M5kMW/7oDYqp~S1!f_]TzuOG*/X$,+;w'T-MBLkscg}#[ri","?MSu%}nCArE~F*UW,fO7sB,+`F+TZ`}ByuqD[tm(lcZpp{cN<|[JlM>Q[hiJ+,,2","=7>:^7LsGxj-+jfVz`M"],
  w 45 44 100 910321 910897 84 4726 ["w:Six.V8_@4fu&iNU#UUQ9M8$[{!c|(z@#OFRM'l0DHS:U*1,LLmjfer~i|hF~e=","ZXlTG/(m@rYC?3gqr/fz=Z.L:f`%Gb^8A;ee+%LcP6T{S/Yp>W.X+,kdP_.;Irg}","T2{_9.`t(PvJ!FV:YPffqBSj6V2dMJVI.(efW7n3iwN}O?h`nvRUQt&pA!EK_?[@","zQQYs18|3q=QQ0]&^y:)T[EycVkfOz.)55i#v8!-!rMHLVT_zQ}$Vy|p]U.TfNM(","YDB`eK^-`0L`)IN{3e['mbVSv+{{)unrwZ@'*A.d!?[b4=T=Vcxj<r6gZ)BZZ`&I","#yZbWIFgQO/bmk~W-C&oxaWE)4"]]

private def r45_9 : List (Chunk 45) := [
  w 45 43 0 920000 920323 100 6065 [":)QSE!gd-_{F[@Kn&zoho(2@l2|)j3,p4-|e$9)T+zyv9CYRrBTh%m'p!Zp[.`I`","{6s!uLAT.#S<EC#e24&GQBZ|8@K'SJA4Qa8NU#U_^z-)$cDiF):,|LNvd<!lC+5#","v`ezU`oVy&&5|1peZ|ZX&2`w.*B%2-_,kl=h@hV26WK,h;tZA_d)7RVuc[|jO,<t","8WrC5YO8ISj&]QX/j-zV0QhbR@]3)5F>LQm9y.g$fiK]OPZ$yfD)0=+i/L[[<c*(","*/EPaX_K2fYZMrJEm6F:1iU$,7<^YNC$E|Gv1dJ9trfMX_.6KcrSbef1:X3vuL#4","I#-fnaqTy~Q;*L=v5J9AK^W=wx%PKkZ%80CyuiI@WzpN[U18HH%n#/m]vc6g~|9%",")2|r6)Ga%`>9qp1wsx~ZBYz??'Um:3<.q)U<{M|q7Jq*#,('9:{l[[=`"],
  w 45 43 100 920324 920896 76 4133 payload2,
  w 45 42 0 930000 930325 100 5775 ["JCL6Uc&m}Kb*mcw)69Ot_+)OR=QL}aKPgISBPZk*L2)Gttan<(;`1`_CM7,!W^3'","maE/DC<dJs3Rgx?3HA,idrBZ}6WiNU07)]@u]dy*?)E`Q|mhxv^xD!=g&sUnAx3d","8jIg|S%[7^VF{35re.^t'2[Gq5c%*hUy#,m?r*kFc{:&W:w$<?|}fQB(q>GLNFuz","8G7L,p$vh?Xovh,uejb`jQW~i$3c,Ta;^elAo@l&=8}SFMQXsF#qhgjO#h(o@GHA","xDZfa)mB9XNhJZ>!bG=xiYZ^A.=4n4pnmHln2=4B/E8kJ1#^PVEj;7i=Vqcq4'&{","!Dg'Q-c_w6(DZ}w9,[`6W`*C|o-R?I6o9QTFkfzm-S5dVk#?bRzJqBX(KtCE=A]W","zVVe<G/E0MndX%%6S;pAM`?NDG8L0_43=K$Uk^lVMwQ~M{jETo--w.vWRlv8<P|?","D|quw<9U9dvvLM)o)~~Vz"],
  w 45 42 100 930326 930896 69 3636 payload10]

private def r45_10 : List (Chunk 45) := [
  w 45 41 0 940000 940328 100 5502 ["+)YZPB|EG;JiaT}ZbWrn>!:r44hn:IWAYnW>!,kx](xQ0Rit<H/T~@Zz/+ASa=pW","SZHvybfe.S>'3z}XeG4o*G&YnY^->#oAuoV`pj^,{z*Lo$QQ&I_9g;(_|jIrKtZ1","mm4/MX!@F6VRg^~uF1D!S_BdYQ'!v6~(8TZDJ5q<WtP2nnZk2qGcDA7r7KnUHmC@",".%o,78]w]%Bk'ZRk3Ruf)ymdt3Y,nC)KX=S{5(!{o+'e|>rb^8(hy>2gb^D![@3j","Nn5T'@cX<!7|$>wvs(b*LJj>7vH1N:#3`#AS-D)c}t1H@W{(MBOWr`$?{yWX6}z?","{@:6i1,A'SqdJcXPkZ[kD>+;::eW1O=Nw}r7!x>E]#*-%e@^8_,n.1j5SP4HeX#.","GBKb@-6pu;sO2X{|hI`R{.B*;KZJwx6$2IfJkZp;!<7*BS&>3Qbbt3M56J:+T+sD","/Yd,A0A^CPcVg]+D{jsw?[pOE|6)I0`?"],
  w 45 41 100 940329 940833 61 3120 payload6,
  w 45 40 0 950000 950330 100 5244 ["5*F;uA$hX:[^0((crBMw*zJb$*Xi1TsV^6nT&|&tZUdLD'3N]yuu0[iS%S=,!'y|","W<pog1y*=5<Vj')[js7s_0}iB~kv/kfC4c2O,x2oj'JKK~aZC&)^Mz{v:U_/Qt$/","Hg-4`4$j6={&{Zvg&r{=XI?Q<HNFQbxm`^StSZ<!j5)?'ZGwNrNg2?wc(6|(9U5L","a5u,Cr_}bA`D2fq}=;6;^2A^&jlnS4B]<:5DTU4si|,o5ogc~a2~B?8}I3!qW%WZ","^]GdR&9L|x*aBUd^qQHt.qr0t4ftIb,DY%W:A0S*XxD|8>J@,s8A=X1a#XP_/eu[","TlBlGAQOhu^m+posT/]'JkD<i,'zr.E*kNvB?fhdK<f%]SRjhS>`-?)EGgGp{:>l","`cU[4@6(1r^yA59Kgl3ONe:ol=nif@'9Nz8*#<}6lt(L/{sLA}$CL*&zYkq7]kG*",",8KS/zObO!u*[(d5ICNHf/MxG4M;1-9ZT/zQo_Sl['[2{<)yW<t`;h!Wu"],
  w 45 40 100 950331 950832 54 2689 payload19]

private def r45_11 : List (Chunk 45) := [
  w 45 39 0 960000 960384 100 5007 ["3~4N<<#Gx4{iN4^kj?`/1;If?5]4hR*]NyRdc3~qjowPaQNebvz&V5<irO?vk-=P","Q=CjaOwWa!k[D}pWL46.Q;mnl$}hH|FBgR7^uH1yW&YK&T&I$I%tcn'7:/*uf:%s","ASk:A>QFqB}|roTfhX:]$$AM/SbgxASyOGpd4S<0WR-UeU'D.tTujUG;atI_7M4@","gryin9,oi*`.,v3?EO%&PI8RP'@_KW$jKs2kp>*(&9429lGvqSNh*&Bsz$d+G|`K","RpSY5zndpYc_vDu)/MN>k:8a?1QxWV}N-u#CVohG2-G$LQIC%'F%OwJ*xDgg,-h~","4R#S;o]/)9h-oJz)QxN-Cq/mFg?Rms$$!oQ$Tl92j/Bt.M$}~;>1'w2x7c-9ab3p","/NsYGVrMDe[{+k!zYEAToP_/K=iv'`.:OPNt|xKS`a.PA.XtD[2@Lv_&GXS(hj~F","#j61`HB0xqoGkfeeOmmD^Yq@2W9!8GpRz=B*[ukDZ#d+@a/e#AUmqdI}#k,{Z`"],
  w 45 39 100 960385 960832 47 2281 payload28,
  w 45 38 0 970000 970387 100 4779 ["96tsf?DJd7@U:p-tQLxC(XzCF]ldT<pS;K>`4s>x~n{rS*4-:-uVAAviUrfk<UVU","7yKS{I#(H-;L2!%IaKUe+x5#M`{tf2:zZ?5rtQ(tj]7HT(e+t5*zNU_)kP`v{c3u","+6P3vNBF~JGOc,%Q@9~Cv1Od.[E?xW9&kYRCWyWQ1IL6PE<86PS$Ot,~AC6{ROx5","#9P't2TlD>tBQV^w^@vG0=W14<}9j/wSR[vvlfalpi=<QC8hE*pnnx$@KpCT^QP1","Jt[3KhINH)e;/1N)i/7AJ>ENe.V7=]Aqr*tWw(b=}%S/gtfUjJ%>)]Ee1W_ODm=N","(1GdplPDa8d:QwKuod?CC^_FB()cD:eNHw!]^.eu=5D6:vuoa6!1IN93ILdcr#U-","zNmX3K6ugYv<i9[9OZ[5WpY(cH*{DdPLX^oB:L*:a&zInVQH.pCt0_6'r80K>9r|","Nk28(J'HU;,Mc1t105-AZ>tz|^N.e|7H_'dJAh:.@mn:B,D~lwDSndT;&hW>_|V#","@$nYZ&WR+]yruZ"],
  w 45 38 100 970388 970769 40 1895 payload17]

private def r45_12 : List (Chunk 45) := [
  w 45 37 0 980000 980390 100 4564 ["&:_jy/w6Dz2^TR,kTJtvg20$j:{LqXH7zEXTYbG4NtI^8,)G!<Q<eC`w0W)'tv,-","CybD:uPIAEUyn2LHqQBG:BKzE1WO@:$C%7~h4#B1/gm59L28ngyUb=H=R~xJ^tQi","CQN$XZr:!2x#lk697i.x#}'es@6paSLN&dDN/u(miW^.SBcjn!NXVtk$_=GaR'>:","-X^48,yw{1s`W<N(ad*I7%W?#|nCyQ0ng$o/dO}$2IKzsjg3]-<8Z3DO)zxVqzKk","G_4MLYi=DoX=~;v9EpnVhG_1^WDeD>U/GTmUrKFE@DO71y07lHC'ZcUf5&[Y(GM5","WD@<'16=JW`rfDU@v>8-GJ1nBzWP-VySR+@]00!4(9+TT4PM7*=8grzZ5<*i'L;W","I/w6D_7_Ns5:6xhDNy,BrznN-4}YVvE(!x8s86kNp*dPlmQ~qz0b+*=ppl{.,F<<","&X95s3B'ezqhhN7M=sL^)(s|y=M~mPvUQL@AZKx`3H|n&.OUWz?)xaRmc7ab4s:*","FRZwLsTm4/N]gqj>RXP"],
  w 45 37 100 980391 980768 33 1532 payload22,
  w 45 36 0 990000 990393 100 4364 ["AIQ{m1'f)Wk`7ccO=K#`P#|`?OFxEObC2!'_)bF|dGFB_+2-a|UP?zgywQmKk$RU","=ZyP.zI'+]TdZNS]X_T,]tq5j:zi|[*zu`4KbZL$]~;E?I;B$#^HUw;>uN+zScPk","e9bWlWG#.cDOvNTzn~,7^i~'e;xNWphA|uO/*YOj[pt)s2a:Ozl`('Yd{%T{d~C,","uM<^*xu.-FcWOZ&W_D58@hSHvYAtRU6-y$$R~qZQ6xW:g-hB$8AN%h^)NUMTt-9S","vWG#|8J*4>Uomb.!Jsy/(6yQY~9Aupv2v,?{ac'a=&}5a#sI3RLwt33$mBj`ztz[","RAyp_lD@OV3w@cmha^eH0bR9]{eSrz)C8`;+%0y/T_]9cc4wM44I*t48EyKqZN:X","$NSRxo(7aFOh9tW%x*Fq!!w_0>5Y2gP>OtE6(&/2eLRgPzhJrICZU3a!bvQPY@FS","gBS/ZuD%3WqdP^vd{ZmN(/;R(;cl%aQ&hz]T{3C+o-fF&(FGZdTHU`lw%VZ&8lOX","7jjf-G>1;D>wK$+c/0aF1ziY#"],
  w 45 36 100 990448 990768 27 1230 payload1]

private def r45_13 : List (Chunk 45) := [
  w 45 35 0 1000000 1000451 100 4185 ["(rzGlAv:M&kRTLbY81N_!rz'z$V:Q6Ay[#%XJQ@RvyX`jfKWSoV`L0p}~]18!9Nv","_n4W?ueII-8IGLGQ?`/o5T~A[Wb+=cPt<YlaQ^B[|;[nR/=mG?j0fxrKlYk4|drC",";Pn]6<c8AR5oeam@ds;J-;=pe|3jP&.=go7miy%p+nsrr*yd5p8y]<Gcha1C?VOO","Sf3:{E,Ahc}J?<PJ0e4mzFc).!goKr'7(@^*S%An5Q^TvY<~d+p4,9_i+-dI89%S","jr.4^b<P7E@:LJlc2%CaN2>3%*o/|jn<EqI'<^ItRI6Ew!)E4Fq+~Ofayf;_U&X}","me9a[ekUQ5|VjqidjmudNpkr6i|o{lPX~wlg78E*,r!rVv!/$>99+{oh@4tgeN)[","|T!#z4i)iH0!]00B/)}+}LIZD-:U^'}l&N+#zhJm<DYDd(r,lQMjuKE)ZJ_bpN-/","PmC&*B:iw6/%dYaSF&$xw]xE@`Igo:Vd$rN;4,ns2-$#O9BXc<uzI%$dDN6q@f0R","8|%Oear/_~C$|'0bUk&Zvmvu.(oE>0"],
  w 45 35 100 1000452 1000705 20 893 payload3,
  w 45 34 0 1010000 1010454 100 4018 ["qE0`K#U]vq4FeM&LN&N1F=/)d#(S8*)UItNP74iXytLzXW/vh!$8V{S=T<IoJWZE","Gcb_nkgqZi?ZdtD|e4E1,|g?<r'|fRU_@L~|Wm-ZrdgxGBjFU]_+hOkyXIu2/%pq","-nBp7K8O<@t.M~hF813@5hi#i3d,Ru>[R9y:qDyO%n@ZD6h/fc,_.a+S5:D-Wdcj","^7y=Nuf|[WZfwOR);ug^/$kNEQ!w0MCuV|JWKrb?O|tvF_@eOudaUCv2z{QwmeAe","MWi__UiVZHfAxEO}JMa&~yZzXz3;tC<4sUvg`CLD:~t<VuWy5fF~pMCrs+5TBhp*","Q%[qOWwSNdpHKrkzFiz^d#@kvF^;r1RbX5PbEs.rHXu5(#Ole+IE:mDx$IlFTQva","d_h#aTPb:c&krIiWq)aR{(W;~ntjyBiN8D]a_lqD{jgDwgV^c,Q&R0z*vVt3?K&|","iEk/dfT5~zkPGD5coz+}?E9^;~jz:X3:N`k'%(:bbO%v1vURjaQaXx2)`U&IR:_F","(UouyDD9OsV4S])zO48P%7qB^D><ftf&`@c{NY+"],
  w 45 34 100 1010512 1010704 14 615 payload14]

private def r45_14 : List (Chunk 45) := [
  w 45 33 0 1020000 1020515 100 3871 ["1s-*,>C.%mPfX.HT}zaoE.nj)U|s6=hU,ZnMxSnSb!/ZDk@SdF`lG{`ZI6@|`225","HtSJ&v?9~Dx|40g6}&ez1hMi|;u6X0xXVzsMNk9XGS!*a|0KafMO1GOS`^SKqzta","'MjCJjug4#9I_3av@Q_~lu5jIA'{^I*i0TzDTU,ku.'t<LqSAzf~qrij>cb_xeHF","fJlBg,!:JBXC<,8&Feca}4q%}5se4lRnv*lg8C[+biVW%4k0l}8rcH{)9EsAqF:$","VB4<*_hW4ndV5rPVLvP-F-&le;w#reu~m/IVBKLfq)py4.OaD*J^d20b),8H-L>?","Yx/[m#Vd*VY[p=OuhI#H2XO$eG~%^xkddsFCec,3]i&`)??^EqW6&kQd$H`{cUDJ","XxrvavrUNByK2dvA;dTK6.yHJ.%W+B[Br[WvH-%n/;?z(A%9:>&$BBb+(M(M&RSo","=DSudac>xYq7fRcN5Z#9d8BKi;P6'GSAx^XfQaFx'k*Il2vx#Jxx]rE/liv$tX)9","$X*omd0X['^H{hfZ@+S'~>}%j;*rn]n_*$~*"],
  w 45 33 100 1020516 1020704 8 347 payload4,
  w 45 32 0 1030000 1030578 100 3740 ["l+XBx8nzrsQg)'uu!jdfGGRchc87?)8EIrRoU;=q![Cj+4H6|0X9=|{pijv9QWsf","L+nm`M&RY}&QA3?;=+>C9nxHk2$Da6Ly,YtZp>%]wci//6c8F~X7/tU*gGvAJ'[<","7i8{xp$ahV<1NEIwQe|chC1L'u|w2g;q'oCL1KlF3hr>T7j{r=}hY2zF^p}Z)H/)","DhHGd5=IcP,8%It1Dk)O_{GFKa-!R3],|ERn0+I>H:={iYV)2?]GjPSAs~WhgS]_","}m)4?fyknYUFiGVA;'M|Cww098&Xs{VT8`W-C0T+OAp6#WsZGD3TY+NsnuG<QFx3","QRoIRR8~.8g:z6S4]MM?)!d/A|z,8Hk|au:zJu;/:L1?b?4}Ndlw61NhNVl-0,!2","+n>%etfW_n/(bu$:CV<K(nb[I~?n*<(c@:u8sI?Zww-*:d0kCFc7$F+Z@FX(dK+z","p*`^Y!w|9q3t[L*B(mPdNi-|~m5T#I8K5*/*19s'{S-3hF;Ip/zM,`QPI_QBL=t&","nnq4g$d@GGC$kI-C;CN8#.Zt.[>9K9o.HV-aX_k{D"],
  w 45 32 100 1030640 1030641 2 86 ["#i2GG<Je"]]

private def r45_15 : List (Chunk 45) := [
  w 45 31 0 1040000 1040640 96 3462 ["1b@!t'67jUYAHDWK1'CMDn1p(7Ak$X[4hI7#,II}1T|4(D$qv4i?kbk|?Z19{`EQ","yA)%buQR-vo9i!wAj`p;4j%0cj;N7:3MXgC79kE,sYO1*QDp`2>}w.xx9_dj9%+H","Em[v:nILiJB`WK4bsUbEFQ@F#Yzj+yzYda1:,WfhSC/**MFT2D-$l^W7R~42cS1#","~41ZXaPu+f!)fkd?3w5x>vV>t}}htG8g``N'AuL|}I_21i:26tb1Ay$.Re;;d/hf","U5F0xYMiXz9pCT5r?_5#RL,PkC^JdpVMuVr]cW5DW^XEm}#JOC'&7~DldJyqM55B","/AOedb]u;T8YgHbdYQg?(sB:k(n#;LbA'm9Eq?d)u:6we5HQN;TU8_,:t@U~aG'*","tf=X.kXNTX{^,C}*}9OH+s&$eP`P'^cwz+eyEG^VNSrzrKfc2y,P-'k!@^`zWXHS","|7a)1B}vJQyA9n<_fO*5LKXb(C>nZNHJo'rslS-v8Gfe6jLo}W87b@10/ly(&:&Z","$%h!<2'kV3(uGL2D<PNpHn=yqgp;!N"],
  w 45 30 0 1050000 1050640 91 3158 ["[BQ2P=wYhU*YtMIIr:dTY0BmB4rHe'AP7A!'zMb+[)mzHxURnb5K<:YC.l$I~!(E","?O#tpM[k.)2ss]8m!Ep,^V1VpFXku>0o>'ZxY?G]@eTDmkgGed7`hbQHx<ok6;YK","V~{zQ|J%Jl8fdQ(Zeqy7!NP~+d?aV?h@+xKY<FdwlVyT{iC94qoXjxHTwwqZ8^=<","+Gu&Jzyyb58V%o1xf(Dn$tg1A_Ex+110Z7XG,A6-(iQW7s1}6~}r!$rhMl>z#!T=","MT%yp*0>WZ2JRp1@HtHmClXwVKB~+E2cuG[4y):2Pw=$;'sa!24t$4}62p=H83'(","63qli_S`yc$$'S*KAVxGjSu7%*S?Hn7?3jyH0O%xfnbWS{|Mj?W-iI64l*eU*[m'","!R;E[?<|aR8/]?z,f5};t_Ca!q;fYg_Qg2i}|CQ6p6bX'3)+f{{s<t4x)`>2o.{i","&M8~9;s:tm0Cka*@E6ZgH2B:6}a~?0n.Z&Tgd8h.SRcvTKHFjwmDq2nfoj7`Cqew"],
  w 45 29 0 1060000 1060577 85 2839 ["ah/LzcEXQiGLFR<Oq9_|@NUZQ`P&7l+$PCLVKm<+:MxVO<h[-)Y*Z1'=AQEH5Iqw","qU@&,D6jy*{,Y7KkyQRL&0nO#Bmk~N~H~[`UTE!D`tlNcs6$+/,I6*@=[4LgwT1J","7mTsv4WgJv6xN70q/WFg8*c&.b~i%AP}W[L^1XWb0bBdgTn0Ju/aEQRRFOF<7Ot{","i$%$~&X%BqqV.M?JwEjb9$n.K/nl[S|$j@$hf@:Ie-bzN(;urz=J_tQHo+%m#~K)","ybX5}!a>=/4%n4<vpd+q;vsGUY0#6K$Qtn;oMyhh3>x#r]z_1(q`s?UK=t<Ueffi","!N[U.;>2]kkvT5>2M[,RzIPO8F9uQ=j*%n9p<H'J9sCnf6Cp)Fd'J6^Rh<w2*yuV","JeWR?|l^VehEe~lg3lA&}-rg`33a)]M>S^otsf+?G-60Y#Tb[d[QY;ik/q*]1JIi","bKXOs$4`^tTBF[C@PLS-iSe{'$f=5<aF;#Y%b`YxP"],
  w 45 28 0 1070000 1070576 80 2572 ["kRdx9h~[{{2w7WH*j*!Wxu*r_Qi^rBkK*{?}u6~K6iP>.zLipB#WZQb[6CI$;Uj;","[>[yT@(_z+@QKrH`M:,F<]*k;63$kXzju&%azUL9Zd7g^Nu4SKx]#=a=!-u]LEi0","k'4]R|I04GG}7x7g*GEx=c98!?QkLL,R%-[y]wCxc~Mvc3)^(uE{3JZt}K*t'7DQ","6'Cu/*0}P2A4MT2G.#ZOG%!@zolO1w:d2kBzCVP8'{@CAP|e^EUVuQ-B^]DDL:Ap","VP.J]O|Kd3P5>AMol}m8Z(Q$EvKX+k$#:Bq%''[WX'_@dI(Dr{$e|i@_]/5>]y(}","=al7h@g&OZp7bapCRQC|f<-jyFih$F)mCG0Je9-|,s~z0xv+xW)yn)$u?DTCsyDp","yo5[ZMI2S(lZpR^R]?c8_1o7PyYv:@ZS_.rg74.o_fZg3_eL8_`cc71YogHvrmWe","w*zm,fM0y(72UDG"]]

private def r45_16 : List (Chunk 45) := [
  w 45 27 0 1080000 1080576 75 2324 ["M2=oA*S=%<d-2fr+'f.uA6Cus@ai:>J9P3tT`vlrqR{$/DPAhQp/&cG-sj3$lke6","TuE^Hg^)w=kcb^`,V?wleNIs:MIfIvf+d;lYk%}Be%ckYeez2vzudOoC538iZ>NO","&FNsLB'YwB()Ij;v%^fDzExN>95s}o=q7A=2H.]=1<R08tBi~).>#9`,QYX}*~RS","lsOKxW'dUmU$yu)_Pp_S+s_NEhK2jOeZxvt6{,m]VkvDWwp+(;4;Fod`:5z^0[T~",")5eqg#SSX*hZSw=Xl(tpk:JO=cY*CtP~XW^Q&8.PG0S,wFcOfr@YQTwnh4K,j:^/","Y~;58yOhg%Vh:8X}t!hE*$CzktU-lLU~/WI<%o7l>u}/W6{k-%QmX-,l8/w(:AJ'",".!$9Q[kAlNM=#4_HHpZKzXdqT5U}*KD7Cl*p_W*e}kXr4Ui!A{5d0"],
  w 45 26 0 1090000 1090513 70 2085 ["Hz.NLx(yDc@D/L/Y73FafLzB,eyW};3WDoaHx#tdnnAN'H|>kj[jJSa2;*a;wZW!",":jtQa_bjLlOzev!daiZf?eK5v#b%fhqj<cVx~D!}D];QX&!qmEpw(gcL8dfG8~0y","-xbcGWuV>0{5Qf62}x7}K|#~f8qWXWUY3Z(@%>~AnTRsl,!6?4Cs=KvqT'bQ)&sB","w2C|Riy32#N66D4>eqgu[5*!Ga+9]p?0eBQCMfuX/tN#~o&.+*3.|{d}<xJ$DRsH","jtf?+3[r:$.pf*y)<IMznUm@?%SAg+ZvALYRQ:MfiC08tVolETox+Wq=$amyuByj","nlT389gK(Lyx,1SQ5$k>5E.l;~obi8,%tu__E]FrAkit5|IT7!P^E:JSy53,lcb0","5-zNiw8Uh-nZqvt9%V@m2@d:)A.Nt."],
  w 45 25 0 1100000 1100512 65 1862 ["s._N~qgmG90:DcCh<u(''m9l3mwp,wL)0h&MDXrFHSU'N>p+:Y>K&CpHHc+:[hiw","_mglAp={&^Fl[8o#i=|1/gpYAv.ceI3_HW-1kEiMZKM1#]@WHe+Bh'`@]LmMrS!>",")rsYxK3vN{!So{~7LC?AY2smEY4OoY0z?8;0W(1%7;mx:FZ36x]MfAwM,n2pjK0N","A(~p!@%18F(Ojic?43B=k{an$F@l?=;'ub%#`9'G#-b_*Grg@Mzzb$:=E?krMZ&G","S^DR&K4m^x~Mda3B_w:,FoqF(<kG*Q/1uG$^B,CWC#fr#lYPk[P:(],EnsWo]J=u","#Mg3+7no8xYKeJr-`8Z|`~}IWSHz)vv;-u%n^w(x>Mg3!J?E8Xk.c,Bf|x+s?9r^","iVgIm"],
  w 45 24 0 1110000 1110512 61 1679 ["~Gj%3+Y.bn$98EK0X/hG8G=G,;7H#,1=)*kgG5Ai6kNkSy!A8/0Ho-(WoQuT%Y!~","{*&9XTpj$<zqJ*Ck(R3yrEiO;8|Q)gXC#[xj}|o4(!O*.dwYbMqK5,`(l'T&pPfs","8u84:Gj%>TmivTQN.UuALa21W`kSg;(,4lDi6RFGQ?37Zz,Y9f$P8b`;^J;4-?S|","nQnkb[(,(OR<Kx}N#f7W+.Q{L~S`+W<~FVwf'_ma278r+ZPeqtQ0Xi*C]84gJMP%","ggLWMb-W|df@nb#<k1J]X1,xcJYmEs-7HwrhR(Sep/A]**ujAx0]B,?rY^'QT(j6",")L`W|dH?OfgnkwH&>Pj5+xks?RvIOYeb^Y;NN#('61ggjc"]]

private def r45_17 : List (Chunk 45) := [
  w 45 23 0 1120000 1120449 56 1478 ["IC9fXzaSkVFoGjlj9)E7w.X<$oplRRC5g-<QI_WPX[R/AtX6mgY0NZ~M:$/dw+zR",",t{Otnd^6ldB7o]Zh)6nk-y8HVQ%2q]iAS1g.;<=#&iR1ug-n44+nm!%Uz|ILR53","lt4Z4+:5>/ckwj~P=Pe0iV~%3tp_yj`eN_L>giakMJ_T/Jxf|w'%V_g(h'm^2];&","~wYW>E}b[mM~Lv,o/)/2f<xfbDY38)}0a|0]r4,jF5mjzGtdzCctP[fjb(sj5F,T","1`LA;{QNu5[v&wP&4DA}DCNeTV`R#4{v^uj6H2eP%G@NN'Rr1U`c*}H9zP:qH?NC","'WT;E-,cKRPj/}843^@R4"],
  w 45 22 0 1130000 1130448 52 1314 ["CaxSpE+x#C2/,R+zsOw`>z3l!N;uAT;oBhc{/j0#]LuOBG39}SCN/Xg*'vL$f6^s","B.7y.N~ozZL3B]-F_B&XU*u![qYE-NJ21Va3>8Io/k_i#]fUbz0bjZu/)AW;@-U6","xT:^rm<7JL{imkAe%gxdr#IAn3uo00dO&:Jw{5@2M:G%0Y,^6~'jKD1KK|@UnZ]p","El-P;636TS,r-Re]iNeeq}K'6*)EsX6'nXgNgUi)s]F=rSdDwTOQ2GtU0G'6]vT1","%M!-j,,;U*{Gqu;hF8LlXBUqO(fc11~WZR&8y#srh3PF{VMPT7g!AS<#oLD[b>H"],
  w 45 21 0 1140000 1140448 48 1162 ["h,{5l*2/2yX(aF]gp8qoXs)42epEG_`f[MvLOOZ<['Tzm|y.p1iE%&7[BN]'B&SI",">l+}c8t/YGEWq%ym~kr%4l=pBKL._}Suy|PNMQ4m#K/j,xdr%oHP&DoA;_+l[V.$","]:?]o~Z$lV*]C3QAEyp)w7B.yQ`^FeWk)$iYg!r}/xe*z*(Q1856CGDKuPlpi^{C","O*UQCr<f*f/tY7PV*4e@ZO<XSv^}Cc6zL;yd1GK-{K!2x=2h,#p~44XxRl;nXs[{","o(7g1iEKp9h7|d&*Vxg{U[WcfNZu8#h^lY|+/"],
  w 45 20 0 1150000 1150385 44 1014 ["_;6%]7`kyZ@=>;a%v5PphdE-&rWI;~s7UY=$H?)[eMT:H>yI8B'a]dLn2e?#}1Rw","'z?K*AbHSZ|}b-52D%o>mFx<R)D:)tl:dCJtRT{)g^y=jXL1./zbv%gW9PRr?tqT","};7IA6ILrVBQ;o'UZEgL4AFS!]a'{NIu6DTWq-k14<a_MA~.G2T<$LS2JFN!4ZDL","W`+WFwj*g(]^[+hL7]zG8{pi]8QR6t8L.TWJ>)[WUJvam_,@.e_PA@_cN/;ra!|o","Q9YP(Ga#.ji9')O[ui"]]

private def r45_18 : List (Chunk 45) := [
  w 45 19 0 1160000 1160384 40 878 ["_)0f32&2F[]{-;Ryh-DrZFp2}bH{iQ|^Oh'GbA{:+I}1jGA4Yz~MWR~'zsi51hJ7","*7];{+-;`XX!o(vfB0F2.4ID5L=<bebGMm-@%0U]t1<Z-!).NrC2p,I]B#CcXOR*",";wH6L;Pu.o'eOwiI==Rs7Nm,@#3rp)]~0&>.]?oJn)^_x&&XcIYR7tdme~6Fa>_{","11Ws_h?kRex.^wgv[6:=B9SqIM/otO8WJ>1yJae*i$A:Fex4`,|XhuCdp]"],
  w 45 18 0 1170000 1170384 37 772 ["3e>/YqmOC$~.h(E986m%w*]oKsl%Y?UVm3((rSIYSDaa#n%#0=W~LEpa#+@P~$4N","g^p?Jq%ZpYtyg7`J&Whg<zBOHw:EtST+0#Cw9RY]gj6%G+MSuJxi?Z0H>q27X:zI","&0c4w*gdt@BoIHq6cp3?W(?%jerw,A'Nl~O`Wbm1!NK%/aYk(!SD5T.C}qxW#ShV","7lz@lI5`:CFLW`*%fE(qbY+!}64XQ3JU?c"],
  w 45 17 0 1180000 1180321 33 651 ["+}5@/)-]d%,IPy}Jb6q]0B-b#RWAk-CW6oC0wifyT>'^^zt??}=S'RzUW43>ImCk","eYpi${9GW%2<I,ky0Z9RSe2V1SNf^Au*uG[[^Rud8W66S3je-3U95-6Q49iA[%Sm","%*A1E@Zph)n2peSta9otS)s(5t2B/%#+8zNvPrpn*D?20|]Y&P7$uzo|HM'3:v4-","%30g$<[TW41"],
  w 45 16 0 1190000 1190320 30 558 ["_/itgb~qZ,oXmytH;?|DwdxlHb>x?/FMQd,s>/fcn8q`R>r2-DR~rXs{GXdi:[5C","3`)phq(u`iB(e3+y17SK~+nLCEO>0^;ld!|RDBFR%.{8Ly9~Z/?@Wu&ri5~c&7_(","%n`!5/UM}Re/G2G2JLVL.v12L2kIyFIpu.p):Q5d}M}}-ljbbsv#..qc'IJtf"]]

private def r45_19 : List (Chunk 45) := [
  w 45 15 0 1200000 1200320 27 474 ["dJbRVaq6&/Z54#XlarVc&1k*[G`lb*s`9de1{u(D?y46!^6[~h%JMqd-z*=A?hhI","B{3e6l/m'x2H,6btbt^.[&ws:2KS~4-`jOj'E'4D5!t<mwBy]}I6w3UK*pR{pJ[E","r{MB;}S-r4GGQn:R]}[>+)G|WDJ/m#!|E03"],
  w 45 14 0 1210000 1210257 24 393 ["&oh*r8pSot&%1D9/JMHr:njJhdXK`y/],Fxy+YC^yN{*!P;Wfz)fW_8n~^~V/;4`","K6Z_9,.Pg9rFGH2{9g6!9X#E/K=OTGGa`}mh;&_ttA`c}&!1[Hq~Gzxs%(PB!jdu","%]Y@=|9M9!.27GnIJb^bASc"],
  w 45 13 0 1220000 1220256 21 321 ["RX='|S.}<qj1Xk9cb_YR`5eio|ZhC@vfrU7u$Tu4]:{79aWkk[Q,9},_D-Z].;3{","-`/uPfxA(x6U@B2K1amk;Zrcn_II{M_c,)ekK&Z*2BBU#~^ei,aad_%qx9e?<FU+","Ugi}SB"],
  w 45 12 0 1230000 1230256 19 270 ["=G~p9?rTBJWh$4_O<+G/@e!q&EdL,HcY=:KFyR0ArDzCW{hB*+mRW.*D~<_V|Pd*","+q`NUDR'PFtLu~,3^S7uf<QlrmA37*&U?(EnA-~H*2k&Q]rOnn=m~ErhY(0"]]

private def r45_20 : List (Chunk 45) := [
  w 45 11 0 1240000 1240193 16 209 ["!>H(!2vw1[g-C?wvl$@-<sSyOYrTEo%^|SyZ,abQ`<b;15r@!D<*o%DDs[.r$Gw&","`aObixCxj+{4L.Hj7KZ;{v!cj4|$'*/RFr-3<#rpS"],
  w 45 10 0 1250000 1250192 14 167 ["fv-.qo5YGoyi+nz?Z<2quC6W:1rtA.p)Zqn:C/HR(PW[ecMh}OVsWdgF]w+cS7e`","#&Tx.+5>aMVvCLkpP/KwRkED%ZymjD@?="],
  w 45 9 0 1260000 1260192 12 131 ["X~D)>f#PRGpIrZWj#aTQ{IQ,6,jhso4K{)jcP97cT+nY]0gTQk_&iFeLT,VfgD'9","(q4Umble7#Qyfi"],
  w 45 8 0 1270000 1270129 10 97 ["@y,OMmu~6zk-oEJ^A6Ti9TW*IDinU_z:=^m+%/2nLM:6`a}S~M9-S9sb$o!rBQyO","({Dk4"]]

private def r45_21 : List (Chunk 45) := [
  w 45 7 0 1280000 1280128 8 69 ["$0cN<{y9i'Ver;H2V4I5%nf_<g35%Gul']d&Xi/$EUJs3v,;0nE_&"],
  w 45 6 0 1290000 1290128 7 53 ["RmT?u.T:[~W{||M}up99799GRR9b~&/'afHT_O)1_g*}N"],
  w 45 5 0 1300000 1300065 5 32 ["Uya)X(O2U!h$6bK[AfD>Urea`4HbvB6"],
  w 45 4 0 1310000 1310064 4 21 ["H*eQa8/U$oDx}qba&JPxHWe|:x"]]

private def r45_22 : List (Chunk 45) := [
  w 45 3 0 1320000 1320064 3 13 ["#X:[}J/7#rXd-yzvb"],
  w 45 2 0 1330000 1330001 2 6 ["#*N,nMr(A?BZF"],
  w 45 1 0 1340000 1340000 1 2 ["+QeJf"],
  w 45 0 0 1350000 1350000 1 1 ["HJI)1"]]
private def chunks45:List (Chunk 45):=r45_0 ++ r45_1 ++ r45_2 ++ r45_3 ++ r45_4 ++ r45_5 ++ r45_6 ++ r45_7 ++ r45_8 ++ r45_9 ++ r45_10 ++ r45_11 ++ r45_12 ++ r45_13 ++ r45_14 ++ r45_15 ++ r45_16 ++ r45_17 ++ r45_18 ++ r45_19 ++ r45_20 ++ r45_21 ++ r45_22
def rows45:=rowsFrom chunks45

theorem good45 : ∀ r ∈ rows45,good 45 r=true:=rowsFrom_good chunks45

theorem sorted45 : rows45.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks45 0 (by decide +kernel)).1

theorem mass45 (i : Fin 57) :
    bandCount 45 (i.val:ℤ) 56 14≤(rows45.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks45).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 45 (j:ℤ) 56 14≤mass j chunks45))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total45 : (rows45.map (price 45)).sum = 332665 :=
  (total_eq chunks45).trans (by decide +kernel)



private def r46_0 : List (Chunk 46) := [
  w 46 56 0 820010 820320 100 9268 [],
  w 46 56 100 820321 820649 100 8927 [],
  w 46 56 200 820650 820903 44 3631 [],
  w 46 55 0 830009 830276 100 8970 ["la/s@,0x`;+fV/Wx$$_|QL7P(3A;(y^n5u&.@j7jFJ&2s{Rme$3[sPDMCe7v8z,c","a83HgxjG>z}P91VZa]5k@3$;5EF)Snz6uLdj`-:j/eATU7,F%8&c;|6!+L#Gd)rx","nP~IxH5JD)fuNj*$:rK&!(F[Do`8Y7w6P)"]]

private def r46_1 : List (Chunk 46) := [
  w 46 55 100 830277 830649 100 8560 ["0J#&;nL#18P_:1*ygVpB-'aYV'Ib67aYvyc$3|Z(_fG2'g%}@GYqmV`9q+4h+D7O","jo,CIR}lB[f}XC;T02A],A[)S@e7_^F.LV-=G&#M9o0i7p~mti>rda.;mc1@h$7T","#Nx)'z?L4|^,y!>0A~)J}yNNagKO0?A_Cl$&vpZB:"],
  w 46 55 200 830650 830902 41 3246 ["M-uAYRChZda`({>FqxH4xa7?JLZc1g:.u<e[(Pi3.e_BJXj$D^&$*UbU!Zgr[4VK",".Y[G_"],
  w 46 54 0 840008 840273 100 8710 ["b7,OkWU1c02?FrC?e/Ezv`5mz&=E#0jLsuY|vHvR%ar]s?fgDtx/Nrm|k//2Q(#.","!;@fY7,fe.ZNKZ7ac[aF4xA[KbLg#TfU.d0m[k*'Mm|dw|Z!kvTEKY|(seF&zRFn","X9:gI_b)INtA4nLY(xO~*iSaw<!~noN_<}>A|Qp1Nr+,"],
  w 46 54 100 840274 840649 100 8190 ["Yg/i*TQr5R6X|K:>i=8(![u#P2z>O+UlISpKLcPF<G]E+i-^e|]+@kMz@{$};-7`","C-sz_ZB0H!^t+`kRaGL`kq:+{>3V[H#pbh'/?iMJW/G:0E%e41nFVhG_nJwhy=8G","c+~g!Eomh5MFpL8*ZamJ^gI#q.3w!jb#eSOy5q3I*~ZjL7w]d:oyL}F"]]

private def r46_2 : List (Chunk 46) := [
  w 46 54 200 840650 840902 39 2968 ["R.?=~<ADFh31&i-9{?#3>so%;%;uJ6YOFlZp*trm|%nEXc:19k>Eu0'e#Lkf#Wo]","%$N>bZ(`wF:oMy&&CG"],
  w 46 53 0 850007 850271 100 8440 ["AUSNZIUVq{frIZNZJaZkvvS,hD7Ec3Chpo?c9wPQe&D_~Q#^FJn*e1eBw_2-WoCN","LTyt~.@MS]pPLo3{*J21z0%|p1R+6,iYUqN|@8}b89''n5'lO,%Ig;$180ejN7lS","/k4P%-m-hZzsZIu8U&)P_AN)-rZ,<a/N^_D?STX&[;f-<f(z$/62e$CA3xh'eCx?"],
  w 46 53 100 850272 850650 100 7833 ["D37*tj9@/Fl[_z5kpxJJ*R>!)~TP{o/N^G15.bq}[S`:eX!1Y/pcT~+qL?_>!,@t","m^ukA>8NCV#A`=G%fGhHv3A'C.,!93,-_i_b.#5>.U;QuqlrO/F&p<F`RKs(t9Ao","?,j1}|eY/a0?f@Hcm~R!A89+8'-]c18RA5kmc5v:ZA)z{:TB<]pu](qG>)3'Ws!Q","VyH?LK8!qiBP{"],
  w 46 53 200 850651 850901 35 2569 [">D=.s/gmY1@SE(m6})s#xFcKLooaja7`CAxbnz5#Oo,AG)WIvbPX866JT]E&RQUy","&F[p1$)taD]utti<9X3u3=^$yHz"]]

private def r46_3 : List (Chunk 46) := [
  w 46 52 0 860006 860269 100 8188 ["#85Wy84SQ0/_SO-Df,%KnVik<{+[;+'{&aODZ=7ZC)Prmy?mc};YvuklK4MP+~TB","uRqQ1[vMb]|.prMt|A]%%,=BEpX)as3}kfX1<xk3hFQ5*^VbS8ww$`QV?{?9hdzD","Hdk~A?ae{PYkkklQ&QY'GP#]1H=1$jTT0g^X^Jyk=-hW]kB9C6yqEsX]>/WWW]!q","#0&3i:_}Fqkdk5/O1Hr"],
  w 46 52 100 860270 860651 100 7494 ["O`n7DXsxi-p54/|q~!pm:gcoA|GS:6J$(O7#{u=K*yk&n+wIWXQw?[=CdATsB^+p","@$<z.`{e'9#X'<2_=D_J-,g*Bu%R~WWYyq|[ztX'gD5_iv?J7]iXE9z.bKYINz1w","3zn&U?TPnei+0'0W*`,g%Fq[MX<G<5ln_=~wc?,SWm9r]o[?5G=<9^{6&*NsV-8D","$I}@<gfwqvz^_VNsY)/0Tz$#1~8RDd0QYHr1"],
  w 46 52 200 860704 860901 32 2272 ["QTL/wk[t5L=ey_R2w5?GV:Wwx-)p>DEZWcgyh[?c${}qUIv_$Q<%_LgrS5<CiL9X","&m/DGWMCx~0ls^E6uRoLMU.bj,3d#$$t"],
  w 46 51 0 870005 870268 100 7922 ["K+BfV}E*&{ElWdwk5mJ%JMXs.!/SO7IjZ_w[O6S$D;)Rj}y(#=JQW(O.$m!8qVK.","c;gM`,&=Ir['0uZ_Z9`-dY&:z<3v6uD-%x%c~n^UUgh{ujuN~3(Lu^nb{0%Ao<UW","$m%?.uRpDsvH[fp3/=~y{_F&#sSMMUqx};y~nQpRE)>.xTyz|nlle|Qc:]UKc9{|","*HQaQHbU34(6J4JXQ$V'rR.;bH~UJ8Qxd8zN'"]]

private def r46_4 : List (Chunk 46) := [
  w 46 51 100 870269 870706 100 7184 ["$IsOTdKER2=Q[+M|uTq]{hl6AE@*Sxn_!>`R-9_tg8{L9B{%9X}4J*Nav-*'26U(","#16ZwVHr'Y*IVFWHb3p${zqY*GMD74owKEx4QMreNz6lY23MEu3~CT$,,e~nj1!x","a+:D,[HL=:m'Nd!.~.Aj<!sZRj(<W9)+0`^1qby}Nu)XIH?RQ{|:?-H-!~:j_L5D","(To93>g]WuZk+|ttk~>CZ=BN/5s6fI$K?x0bL-~dU{jQRMG$_,DQL>pZj!S)1sPy","%0PS0"],
  w 46 51 200 870707 870900 27 1846 [">!gs@U0H0^0T(TA1;oA.u`|T~Qje!8b.I1P/vREq;{PZKP3.{C8<t1%DeJz,XI*m","4v(OF6uf;j?6k:igMcN`N:T"],
  w 46 50 0 880004 880267 100 7674 ["@1.O9tuIwYDI,G[PDoB{iJ7$AbjAY92a|khujU=%z(R!Uz/v2_fGyPP/qGoduDN:","=^P81yKVY-vr4uZdfp>oCT[>q(68'D*2vy<14UYQCWN'x)>1U='^24YK?|Zv=wM7","^TH6dJ5;FCa#rWw|E1mR[ji5sApbITeEMn6hb#J'=%t6%w:}-,z9&<[u=l*%xGV(","T/)0zgzF3NlZ.$N$L&IB..KYdLF^6^iW^3=<^WU1o>12!NUf$|6^pa8"],
  w 46 50 100 880268 880708 100 6887 [".XzVyX_WT7O`q]IoGPF8FE3&gNxDC/O}k/-yO?3N?1gki>eM%mL4jYW5v!UAMyzX","HnEa.x@FE8@TLLDWSFP{-/z1IIs+B.#lT8H4:vbW&iASo6c4pTtu`b?}jNT0kzVI","'P(F+<z:#yW*;UTG`MuB_4;beF(Fu:h)k<N>b;pnMG*qc6Y}~LwB_O#kMG:mz*/1","~4uqbHi%1,HanBv==GM37gFz_+-X=8pvcbUCVCi{>&c?aEq**8%V;vCu]ay_o=7j","MtDDBGaL^eaWL*,J~a*.X)9nNs$hxnLk'P8"]]

private def r46_5 : List (Chunk 46) := [
  w 46 50 200 880709 880900 23 1523 ["7%avV,Y:b;yY~fA-X_j7}P^8)QTp5?l[.Wb$f/S+%;acT/SY1XLR0-<n+5NUrn0E","&~D')-aR[H#L"],
  w 46 49 0 890003 890267 100 7407 ["Iq$-SB/HJAr+7]tL+31Q1@OX]A$Fr9nzx_`)kH_q$+^+7Jc2S6.c?-@9>HoIbPJ*","!3)fEWH$%B6J6>N*ZR+]_i/B]`Y^*M#Wl@_FF<EpWD68D/XBc&xk)rotg6ip02]D","t'hSK+F0w0>2GVj/NR2yWo,UPv{:Klk>_I:Qxpp&'*C9]tVfL;L9J[u#tcIbI74v","u1Wh1-r,CZW6*oA%#kR&:28:^)-@Xz,(y_3hPF,P2mx6-tEiqdDA)k4DccY9!tEs",";2p+JJ{$[,<x"],
  w 46 49 100 890268 890712 100 6606 ["Wn+<;k/Ft35!J.4Hd{0xiai@DG5';Or&TjU(c8{GiMuOyu~;H}kUT?1=`r^z|Q8%","Z{'7B^EC&<bASU2p64tU>q]P#e6R/}1'=;?#sTwX},pAHas7V&W?{h1+j2e*qPo[","DHNgakHw^X-cF9Ux=U[z~.}d(PIow@&E$xoXp*1W3r8Lhw?i{+R;U`KG4JFzq';'","yuspMX&j!ePlRSWnoV/Pe)HlU+F&kT9VmB3S!Tn@{}49k{w.G],OxlMKj_l1374h","])b5S4H/}Q)q;1C.VNs#E7BNaK`9S<OSt46})sE.j6!>'rapGl!X9=-YlyS2VQDW","%%_<~+"],
  w 46 49 200 890768 890899 17 1093 ["%t-i)[X/sSRtkrmk]sC9<.<=bFq&}?ww%h$JDyU&y@]U=hM5}PpU4,8p0"]]

private def r46_6 : List (Chunk 46) := [
  w 46 48 0 900002 900267 100 7157 ["wPiKe0$L?,8P9?;D^?PZptK^WfmKi]Hsu*{y$OLqmPhJEC1(L>-be^*W`>q*47xN","Nt|CPR.H0rVHs8^AaD_*d@9vb&WmwW&-y1$ZlUaE?VHe0q'$70+gZ'V/E14@rWtZ","6hm'/S]j[xF_(fgi2OlEIkL;Rt5{P)n8JwfVetRD9)D4fi-II*Z7QMxk$Jl!&Q^k","_:2Pk?k?E;FGQ&1_'5d{>3tv;V~_ikL&ayL7Gd,RuQaB`ukF2:zlG~WndLH+Er2Z",",?/^Da{I(996J#-q{h}Hd^g-H-z#Od<Gh"],
  w 46 48 100 900268 900771 100 6346 ["pmo[q96thU;d@pQvY2lox2r`K#xDX?jO$b.6-N>n0fa+g[h&HA,)d{{3GUG}?z]L","Q:TZbKjgriVLG>x-/?7pFbB>|0Xr;tBI~b^_-Z?MgNmz4HU/pJ)7&tLpLOcm7;}7","R0*u[+)$#F!50`/=dhrNNBifU2HHN[Oij*{3fYnhwK7XC+^8$BJH`A/tRs{Ucal0","Vjr_}GCCE!G0r`7h9L5+cT8E<i/SV=g&m_{A9b~:_Z''BG_!dGC{_vuAXY3(}jbF","Ut{~g^kh<|iSPOl1YND_%v/m-k'vwS)e87mhRZGZiq2MBkE#,8a.YKr$b$a;NwtC","99IrOAZLXE:z,St-6XBET)ZM]-<E1Y"],
  w 46 48 200 900772 900899 12 755 ["ea>x*v44y<xeZ'UmjB.j/)Fn7_P6ymz't<U?%Qmhz"],
  w 46 47 0 910001 910268 100 6881 ["!=D^piPj}{?K'PdHDFrH8jx1c}Q}UFzHpV_lhpn12-V;.J~eNq`]6ck)/Ud!A::J","<9:DO{4E+)h7wekNX,0FI$WJIZ2ao:0Wq+QZ4gt@t%#:z[#Y9s]XTM3#LlE[P-m(","L@)tQ#Jg7(]v73XO$neu(V&MBXv%>&SUf3eo>VKlo0a)zk;^;wF9Ih;[Zma&<@gp","|ldz:rJHJxikmY3Q9NklM}(`kU5zwaMHsy.hD$kyH@dp<r{Z8x.a4Pz,*%/ht#c]","A/!Oz[JKL4WcMb6d~E%#aNytR-<wX4ly4g;AClX:gU)SD^S*Y^wH4:ym"]]

private def r46_7 : List (Chunk 46) := [
  w 46 47 100 910269 910834 100 6110 ["fusdu&NsQ9;-VlJJqe&6ZkWX]{?g//#nAg<;bjb$.e[s/-R}5.Fc-:/6ad>*WzkD","7iw{TcXykPrW6adTV4A&Yht*yZ9!Ps:C2nf%';[9(6{)d:o97>BR}z{FRJ:)BUDK","Cz:FXaBsr_8MddC{>LKB0:])?3fv7dv!1a#1U*lGQE16puz|6_^c6y'Y_zK[717u","-{K0UpWQhp&bqDGlM!0quXRd%Z3YDOTR'_gnf.gS&T/kd<uQY)9m#.?7B'aj:<Q3","l66et&1QV0P0XPLvJwWL**1d]H[E_/I%#of#_CdFg6Wnm|Gk>f2`'79r-$l`|@3+","D/Tb?}r-}N-3Tz*O?@ozJ?BT4ora.7p.KIqmV!.lC6Y[=2?rxaFYa4hp~i"],
  w 46 47 200 910835 910898 5 311 ["$c8J38XInl:w/,_5"],
  w 46 46 0 920000 920269 100 6620 ["NWc3O^j`I}ur-A:JEz</9:E?`EWoj65DQx1{#-e;I*ZQC!VP]a-(EwrAGQC$0Eh.","G(nW<@I>s7]}$`HpXm'/snH^Y}4vY6`CsWU#{A+J[Z|LiP+{Quv8,xqw;<7PNb_<","0m-ML2o%_Vm:#<FiC>9x@%_'St5{V!'bL`Q+2X^W(Q=s3/M/#6i7Lm9!=m@ho%N,","..%bX?$d(p5is;t`,.&C=7izRA('jMO/x7-H^62+]i]VfaK{zHw/a7J5Cev%40Lh","#/hx?9rO$tJ>U%+*I`VPsTeEQmSpS},RIIy;7uy>&KN1YQk')]:4q'VG3Y3LtN+h","-.iM]gg_!sb>-"],
  w 46 46 100 920270 920898 99 5849 payload27]

private def r46_8 : List (Chunk 46) := [
  w 46 45 0 930000 930271 100 6329 ["ynd%aga*,F{CsklvkfQkuQ.%]wollI$Zj~SKlhVsAms:r2)u?PZ4Bo0Q37OpSf)?","4Qj$o-UT~#qZDqJ9|I1DG5LHQX#3p2NU7qnc$qa@5NUYiIc}x?nki?z~ob!cw^jn",";{c#G/V,a~gstEKw(EAb}Z]FH'!*xIYcI8;M@c6zi&uZr@0%3XcCjI9XZh?l7t%$","`=wC%MuyA3>!9QM!YMER%U'B]gl_Y`l;0IINQ+!0bWv:uVX'>'G~7ck#5ZBb+%[f","b;s^?3?9K'`F)9gJjhq_)2?q4X.?26j<,Ur@|fh;wqhK4F4kdT!)~*z%z'Mb:b-z","((68<AsE[:}oC(c,:>$AaY/Ua?}Gn8t}>#,lxs;W"],
  w 46 45 100 930272 930897 91 5199 payload9,
  w 46 44 0 940000 940320 100 6059 ["Zo2H&gxnQ0xYp[FInC_d8gT(Uwj`Jx&ll3eq?,=b;(6@HG{.]T:pGEhhk.'mFr!C","m^DyvcA7XZ]*R)tUMC4A/TB!;a='G/hj<QEa+t:;bd:2QPqF2V{QU1[Gd(Ok{~8X","IBm`_O<<a?hB/3qh4;n{Nwa8Iil$P0444:}s5q8f`B_[!zTd;q/GhCVvykUX=Dw[","V%]?$!pDrVr9P:rKa29,P6K6W=V0_=,k&<#=npzZ5xSh<2$S3^EC),NLL1qC6UgO","Y$?fPfrXn1iwy(jv^-wo8C-Iexk03)O6wdsiez3A]gCQVl@D{I:o']O?D=:WB%!f","y}Qb#JWY-3@2d|B.0AEdr05?(0fYC(SFi][%sdJjvv?oYV;m96L=<VB+`O2WMtt8","*<8Wj8R"],
  w 46 44 100 940321 940897 84 4641 payload7]

private def r46_9 : List (Chunk 46) := [
  w 46 43 0 950000 950323 100 5807 ["?Sdi$:)FJ7h<]gNE:G@9VrIiQwyExRS2CP=71g+Et]L%CK'+vSbHp,KcjO@v'M8[","~0x>Kk@gyLB@;F7?0(sOvu}KcfCKu[Xv8n0OXf4*U,D=):?BG;&T4,!_1Mlk4+AA","-'k=_9M'2So`Q7521)9%hh)D)`:_P.FR=do]ThBM|qAT(E>V:S[eR*jSKP)66X?I","St,.2@d4J(In~#0kQ{3oAKW+A2ORdv+K:$VVs1r2xns`1+|1dS4Cf09*;09qg(L?","d-qBW_O??yc{d[:pMEx4?P9i>i%[-Qp$4v0X7uEkj(,H5$<1b`F6{j-Z}6EguO%O",":~9u}^s+z>z+(H^)?(sD,B5h`Z0rg5SuvGA%uz~AY3hF,*9=#=[Jqo9E7TO45/U1","#I)$'G%8-]wA*i$QgI(O?v!lUW74GW'aF.aq%|2{dJhy;u*_$"],
  w 46 43 100 950324 950896 76 4057 payload2,
  w 46 42 0 960000 960325 100 5556 ["Z]O6,4-<@$/8YRFT~z8_Rv-?8txgd>WbJUlD>?,W8UQf5k^^/SdX7sK`0$i7TH]|","YuxioC]{Y1M9P'aIK3C?8@Ep</Iu0(}GWN.:r~'fNjSKG5D@dai79HjG)#+Q$2-9",",quP}~5/}~HGq%Bnx$zK9V{]Ts*gUg`H,qgNwyXBf3:@9/Y>=HGZa-VgR9Q&e]|5","TjQj}]i5pVC8vB<N=>1s;~tU;oS,FW$_,TN<HYRkLz#D/@f(e95Pc%.MHE&#3V0~","zkaQ?;7b~E]q&Pd>DDSeS!>WemR8ch14X@f#bsQ--o-VP6*z(i&zYApIJ8+J&i=m","+'$3>:h2+i(UXJH1NJ_5<O`seoeGxf68*5f@kp^I<PyRyS8U*gHC9;,@5Y}XY|u,","62%(;nv$6;](-EZZYR_)Kn7rVFI`[lm+~:RDZn|1rw@7a2Dwd<g}=%RojN.rz232","%o!Q{qn'"],
  w 46 42 100 960326 960896 69 3567 payload10]

private def r46_10 : List (Chunk 46) := [
  w 46 41 0 970000 970328 100 5310 ["e=8Izk$|n-?8N|F^'DRhVEm?J'^XOV(U[(.=k/lsIgkh*.G;GZ<HnQw}Xp*;|}`h","h(bN>bkibDRP!3:]n%ZS'LD4fQa3[.j]mDv(%fND8Yra>67Z>,BaSSJ1JlheIbyX","XaD=Vb(,IxurRwmTqTc_k^7i,SJhT6]p7D?O0[3kDn:p/lfj),FA[Ud:n+#kib#!","3t!'>GE^APz=!]*C2,370eF}Q,Z|x4DX#t?9!^|$x;XzScccqGV}!a6cJUGhSPE|","[H~-rhIFchN<Uc)<}))WCZ;Cu5.DS^'Z9TQKl<@lyocP>@[ymKyYD4p(lTuRxkj1","Qn(!s6?9{,s]7F097`m$oe8|EXUAT~AW3M=6g-ZRigD4+x=qa5$Pq,0Zhhg0M6f@","X|$#=D,v{{+ff5AN|+bmt`J)OAwj6Qd[9u6oC;!Rs0_D#,H6!mW.0-:L)X&y@P8P","/Yd,A2-E|T5(ap&Rn1NgnUm).}Z~hv*^"],
  w 46 41 100 970329 970833 61 3059 payload6,
  w 46 40 0 980000 980330 100 5068 ["09l$(GN*Ag)5bL[e95wX*XX;2M}5F?F6T*T[JbYWUwu-(po}'1xUPgjZ?v[ZD&bP","&a-O/VRv4b0^$YX>pgLL6~&)r)J21mgaf}^1-)$/Zey.w8O;E~T66Gur1rK>PS`4","Db50d='mPHP3'17o3ERp$!3s%%@e'z=U`FzNjQNay+n6g&riN@wFy<kcNZ^BZK,>","$jk)^ziU]S,X{O0:h!J'p*^ubHtF0{nw<3RUli&jKvlEigLX{*^x$PXS4Zxw[jF[","Acx39V:4Mmh1fAUQ_C}l*4Q8pG?`+o1YzUJ2bVVl!Eey@SFEV%[GV[fJ^CL=b5>=","`c%:OYB2}$Dd<,UD]!)?/m%pAr&1PNET<E~L?c&n}5nZs9}r%faFtnLNLC_5id+k","$4.N0Xrp,6Cs4)cv)nfu~Cy~SIIh9FUGJk{F;`^U9#@ym+WM,AR8uU7d82ZuT]ED","#-!Q}`BDy#;?1W![qb-mNB29c`3:~+>L7s5[`Ajy](#C"],
  w 46 40 100 980331 980832 54 2635 payload19]

private def r46_11 : List (Chunk 46) := [
  w 46 39 0 990000 990384 100 4841 ["Zk,XWFz7[+(t:'K`QTGBAq!kwrc25SXL]H.!sT_et^02PkCcW;*t^$F}Q,%l,-},","$C=w;$8R.TiM}u0?g|frz%6>UVYQ$E,/{O`q(sU+X;YucZ]7>ZW,PK)Z]mXM^|H6","/zuJ:XU#7t#B2X!P*.OgQQ/]*s$MLdk_E[X/K6/[@:f8p+qL!JpNOb@xQRlK$'T:","#7$.cgufT).R-d`Rund)QWn8i[#y$2e~^-jJp@@9b4>!>A[uJ3cV,,(%B4EvVL0z","BT@?xI?cOi,hxuRx3@|7NY9fswks5Oxf9c4#yL::guV3jZph{p?w{q]_Rr,NXkPR",",<=C8}KmvFg_m6:`j~k9#gVfPj}BPl)U(qY_B<)Y<oa6!pgvLEzaQ8uqBbOP$iQ}","2Cn+{.fK=.$Mk?k=.(saSBmL^jCvj_PxPDb@4'3A5'sOW:!$N]@/b%N/iRGvVZ?6","#P-_h)IUVH`5*16vc/A:KNr)Qy&/uo[@VJ6Zd@HSB/WVh?GJk^v"],
  w 46 39 100 990385 990832 47 2234 payload28,
  w 46 38 0 1000000 1000387 100 4620 ["(f]E+I%GUD<V{Ti@[*>~bL>H*Zn!-_!B+2/ylas2{v>v)=Y0o&'qJGiwh.]Lc&.$","JvTC*N1y@Z>yZ~U4u^mNLkVr(p.fAhi>.xgmVc.gVWS4YOJ1MjN3Nb~NLOtY9e]3","k*<)>})Ox'RhP3.4@d+/6iL=B*-;<x^dgFKX)2!O^3G`@v$8ySD,xn[W@x&IfZl[","7VUG3=t|a>V:u(|&W3-`G2aSEZ}/@k7Z)ZT<k@iV@???<.=6yjTtsuAiz[R/wxN^","neb9%7DU1ju|$Kcjz9-D3P)Rm#0wE)7xpCdMn'F-d1b*6|SMAa'5;VoY2^CaAYd/","~06ICxzvq;1])H,FwG58cw7!|idi+Nr&|^g2@&NiZ5qmGtI8tk'tietkR;J8LBs@","m)FGh&$1RH98^VpO(P2Z6pUNAzSd#eZAOSrQb|iUxDfP<l-|&oSA_eIb?w{x0G0=","#mRFDa{i5'C{[MgJMU78yA/:f9wIiVT)w}|3p^:xQav2*3QHm79xlZqp6%%"],
  w 46 38 100 1000388 1000769 40 1855 payload17]

private def r46_12 : List (Chunk 46) := [
  w 46 37 0 1010000 1010390 100 4412 ["X;&k5PV-s,]2`|(OZMhP?`DQ=g6km:cX;(kj$n1c'.2s`jWU.#3o(W>~+nxyLmOi","/T:<'D-!F<D05kD~ZTX52$j-]e4Mhc4b1vrF99HX)I;t-Xg%?6!Wf`~6^E[vZ^G)","<r{;WQxd75U7v:I55<:imM.|JB[krKB;prnQ!Lxs`~NxGJy9EDtqd.@|i33BndUx","t4PJT4'AnZ;P=s/DZIu&_{sM3-~K^b>y5>+hg9WT5<{_~]@.xsxz`<GQ(?@uo8Jb","P,@(@Ky4x7|v#Vm~$UMc?C3^yoMxWwPV4rxM%pOBX4$d~qAlJK},.e>BLh]oK:$0","I4&rNDz|l5lC1)5N2$!qvL1Y~pR}w{g{;=3gIf:-v/eaPjrpQmw.9.MQcO7*uU4v",",:WY:OA}RE1~y7la/zL<xD6X(P5^pH2}2Wk4HlY4[wz1ka;~_P0O*n.HQ|DzG<(k","*m73Yl)?RQi#wO=~6,vTn866V47PnkRwJ?u+3<mMUlGA~kQ3#t`~Qy|XBY,~me26"],
  w 46 37 100 1010391 1010768 33 1499 payload22,
  w 46 36 0 1020000 1020393 100 4220 ["g6k%t]Ji^Sz&JZk.ec-#gkONrha{%hR0DfC]W+VN5ndw4F=(WjLPRLE<BGt{'aC8","U:T:TTOC4Sq>0kZKY3Ami1$Yflnq9C/-@0U`tO-ZeyTNM_'N<&A,g@#KIi5pX4Ej","Jnlgl0{7}8.%:!|D)BY4Km|.1@n8$'8<e>{L;2KM-zaH^+uCoF3Jppx*:xu?2(i7","m1E5D+uX^$/8$2k1c?e-7&raHx^]EXd=&AbQGhsUej[jHRVtINj$QGQa|'SPWn&}","<!/AorM7Ym~PF<d$bE:1ahXk`cs['=,^4z}%L9Skc>vwlsR5ga2Y]2)4'vo#Ok{/","Vm*=AWF8pL<h2nW:v-BpEd1)wg>.k9}3,Gv@yc$7x}S8KKtHbDx0^=u7CMuP;.$5",".MV,Ih~aPP2KsB@De&/#r>W@y|~K5nU7nX40EZX_}6mMLFm}Jxz>z|@Bv=n@=hgS","9ct_~()K>'AJ{3dZXH]8MTFz[G#5rNjX1`oC{H/O5#)Z'?gu)F~}v~n>_5&)5pqp","7!Gc84"],
  w 46 36 100 1020448 1020768 27 1203 payload1]

private def r46_13 : List (Chunk 46) := [
  w 46 35 0 1030000 1030451 100 4046 [">:m*X[fA6kNcD<QTj``R/05iOeJrn`r{2!$uuMhHK|vN!6EbBumsSM#K8zI>=48m","S=@C.vzSk@EbRrG5X=wV>tA<S3h`>>}T]4Stuwk_NtBW#a3.t4uk^lQ/zK8ad:>,","?URRkGU1pX]GX3J**jm%jO/vdEU2P<TjDum/-KsQmy&:g|b'UYA9Cu(mfKyHUOPA","U%F^ra)+'*FxL@IU(h#U,fllP7p8OPj&IF&^WLP.<NkvR?pnvs0d4D+sDHlJMfs/","]iBFv8h&y>{<w!<e4&sCzg%W>c,~/~V00(e#{X7wSxnB,0h#]b3&HS{1B6^Q`eGM","<_2z!7.GYkDoDeyd>8_?[4D(7~*wRzz7R7Y,(-%ovKig_y<[]uv9x!2J6p6V)1D9","0wIR^=?,nx&~[nho+Q|JiF<$_F;7F+~H#J!fKe^$kGbbppeku+3'<nt[E[*,>#Dy","2?Hg',xaD:46cWTdpi-h]<LZ68?#Q4Wnt0StYu7-l,Pr#T/_:<-ZUmKqTg;Y4?hL","#$WDa$vW"],
  w 46 35 100 1030452 1030705 20 873 payload3,
  w 46 34 0 1040000 1040454 100 3885 ["f/?oA8PHz?xS%=TiMw/)?{,!ZPgDhD+SH3`xugt$GHVZ{#&aKEQr'6!4N)]Xer]m",":[c>^_8zdp!p,r1=Q}[Ecq'<2M?0sDkZ].&zxvSP>)p6'F&4DVDft'7eyx/IEhE&","Y35%ha]Z;53'O,1yr_7wMEBYB5oXuXP2Ov%@4Hnxf8e*7naJNN)4,!1e`PT}QmDn","{8=LBDD:1:=j4y@mq2'd}#[yQk1[Bjx{;~sby$]mDTkvDK6+Rp9iifP8cVHKC-}$","+>QQR*^DPS</pIjvsJXnUDz.j*Q{{gm0v8{cW$l9Td>$_2;Vle5<Kn}yDqbT.^qU","_i+4Z:o2EXCyY-BL|k<5II[GQo[!U4-ELef@@]Mby2]>toFz-FAJn395xfHPM5i;","{F`pUi..8r.n#Hom5tJ0k($O{R7/0!cH>:+rT<)-Lkaf7K`n|i!!*wCXI/zB@*m-","8M;Y28#)wGd$7o!,C5g=sr~(/VFbD8-2UW>W.fy<g$bgbY+lrVq={GU-AXn137o4","#x+Ao8%L"],
  w 46 34 100 1040512 1040704 14 601 payload14]

private def r46_14 : List (Chunk 46) := [
  w 46 33 0 1050000 1050515 100 3745 [")DmP[jDUTN~V9Q5H.&(B?G!gAE5FiQXku.!<{ic:R>Gb@6cIyF=1]rqC:&4$>e<<","tR*6Oz8~*3zD>lh)FJhDGXg04KhC~k@aO[cono#04)>UF[/^6`!zs{<Igs3NVGa5",",$lQ8tSA;>;jsUM>)!}t,E9M=*R~o4IA-2.l]vDoJ%=guA:=hHJkuiKXGu@CMA%}","DYaDZ`,cslEhb;Tv=1,YLDs1)k{|fMi5[Veyk1Wj1QBNR~=:q*2EVKVYw+@@j[e{","K-j2l)Z?n#`c`W^Kgvc}?jw;iKZL`}39vH4ofC$28.WE<#N#GI/-}U7j]w=sVP.H","^8JOKB})^tPkHZ$FGeZdG5e695~?yoH|!T94|SF)i*Aw;89@[HWcbY$jkgx_8R+a","|}o8F=]5`P#UA#CwO#:ap+LbqR3vdvLigXF}hy:OS-)5wA&Wv6<#661hkdp}$7>A",")`dT]K:3~yUG/H,Gc(yxVCs2=:3]Q$7&T);`PJFy}lDtDjX[ET[J.)SrOD]nwsqP","%oBaJybLY'~d"],
  w 46 33 100 1050516 1050704 8 339 payload4,
  w 46 32 0 1060000 1060578 100 3618 ["}2QO+Ge]?]}t~#-KT07<e;pCx,-F)_y-?[eKIb0a8BcXP}qpC3NXJY3`E^Jzm1'y","v$!EwiIQ%xv&d>&.8h9yCxB@=>aSqA=T{m6x#[,GV*&j*T+!OC]nN?{23Pd07OKn","C1E$>#:MF5nX*#5LP0mrNBM}>-+t7SO6%QYNh2o|_YGnL)9lu(e`K.O@0uIxk)>9","[~guh-B+)/g=~c$V%+cZ|o5f,A/,$~09p,uPVZsf^pN:6O9G/IKwc>=9[AZ5px3|","wZJJ9y6HK%Hs_LEwL87P|bFRX(BDg'Jda1QFJN:~:j_LyM]Yfk/I1-a:hEIYZIrv","Fa`W^<bC0aj]OBLNx&nxVAQ:S3i^[tt5A6|Wbu-e8r+#LTXQp}hqWtOlJ&T6/Esw","S)J7]$;=y)$rSSp-`ZXozW`1#3!@Oao:,ig,(n77l/fsU_xRd|Fj6!`c7O(?`}WS","0`t5`<fRt<67x+36kKe<xT*p96VgzL(6wrQ{U:8Y7.vKbjW-|=C/*e|2t6lL}hS^","#/,Zu0JTQ~e-cNq2h@U:n+"],
  w 46 32 100 1060640 1060641 2 84 ["#i2GG<Je"]]

private def r46_15 : List (Chunk 46) := [
  w 46 31 0 1070000 1070640 96 3348 [")Jl<>ApZ[k}P_H|Q?8$@wKbRc:0dp)4cG}Ysvk>_0[6Yoqt!vh@(x7{VkUV!?69k","{tvBKWz*+l1b-NV#e0z)=G:UM{ggO~/vuEAbtN)UOU#g!wx#%v*Br';1L;XU]..U",",cwk|TloEytbSws?.XKS>AUm`0{|4i#`~'96Bqi2Z-D|c'yYyu6G'mQIG#)9X|9o","wzv1pB#WT3uAmj{H&GCI<;Q=CCm4Lp)Zjop%MU[LQqib2Fx[dpPTK.>eg67n}sH_","Xhd?eq:_w(S95Z$rao-pO],?aM.(@5|*Q7E..6JTr*_3?[K}$AL1l8b'UKk.Y-bA","Sg;{a3h,nQ}q{5tcFZN5Wl3,nXyQW5?W%e-c>/CN'@[k={;{>{t,E=PlX{>NJVXB","hSYkAeT6^K]6-f#f9KXd0|k8nREoexiRYua@RMeMio(dS=nm:YZH;{a$Ol8zFS_9","Y((^u})H:6>dC1G3I?6iz<7%!vFUth`z&tE~}!sdvz4j29QN]~:kp.UIS1!NN("],
  w 46 30 0 1080000 1080640 91 3055 ["V-Mp;,F9~i#^}`ie[!<B>aK<B2|QGhz4VClIG&,|MUx<81I}k%1b,Rzvbk<35xDf","6CKis*7y*hQ,^F1P2`Lj$t8wg?]lDAWPo8Lc&BpHYqjuy#=5ft3tbC7H~I|Gx3_o","c.AXM%!_A}k^s<v8.,i&9$@)U/iqwxuV7FbISX;fMTmMEE[W~<f^|(%$u.t#CpPY","?d%_6kA?AAu7a[ZS*mF9gdA!SRLJXNV`6A_#WvpiH]=q-|FI3kIu,@%xf/>r#o|@","eVZ^/46U1ZtXC(v4>P^J7sgV&z,aK7b9[5])a2[LE~co+43pZc4-HO9[]ajsx:A$","MTv;y[mN9V_th!H4d:#rz5y~@b1H=[Ut$Gh,n*<+K1=]xOn.s@:UwPsM1xQ4:LlD","Pu;5pk?I$uK^:)}Zu3mDiUfLf}B!C;XL=HDdRNJ`9Oykv9f2.Z:&}otsL|qiDk'F","(4,]N'QQq[apSZV1ojS-u7T7n3WU!{U;V7^zY6z0#o4+"],
  w 46 29 0 1090000 1090577 85 2744 ["d.[EhCI#bth7p'KZ@kTbzi,/t1jIH*SlBEMx.S7[,8UP-}C-S=yzSDz:OP]u|=L'","Z*.MnF}aPimdJJtzU-rC!-GP[f'3EO1Kx:_@+I:]p,K-tN$8B]:nkecA]X}G#p;q","fDK3[4}pTY1Qa@&?}:tzSu}M+vux<#oOn''4e^cIva)0#c7M4w9H/;#Ha:rc*$Fv","}G[mt7uHQdqIQe7Z+,2:oGA<_'{W>/PNT^N5QCNay3yW^0~}B1pOcq|MlBYD9SY8","Q6~VJW46J1@:T1E)B/A@E<yb}YYN.hO^/~8,h!2Y_r5rCi''w/h>`U_|gz}%'+O?","fwHxPT<4|fjtRM48F2T@~?yhhxc4$KKpj.BJ2j!TsX!^[_@*-II`Sk~X3G=5<${h","M)&'H^MX5}*Hz]n*:'Xeq[XU2HGI>cU:hx`x#+nJ9#iVOGh|Q^t4*2x}1;(bN+=$","'ry,]7eV!|_-=9?$p"],
  w 46 28 0 1100000 1100576 80 2484 ["YQ82GjsvrMeRF>XCn1MY}r:8vprVfvK/.Xv7&Ucc74_vS'Nk6'k-!x%I-2dvCf't","ta8#tFU/@o&`Q?xzCSb~j&YZSL2kuFpi>Z_[ITq:+dU+Rut5'knRv7r`UF,=]I}?","}24fFtg=8v.A%;{oKp%#oiH0E0[@tj}d(!<AEHUN#Xpn#ak)$Y!u8EX!rXB-<C2Z","=bUbjW+N5!$g@EMHW3~=!=*rIdG'O0fS;'BN-ON{eaOyVTnYWnp)Aab;'%<?am$>","i}0[7`Iq,4(`7W5mn}_6MnZup+9'U33,zmB**<{^SK,g'6sqpqC8k%)fha=Q~[{`","EK^43K=K>41L}BDuRr~SPu!'m14'0:xZ?8{Ui<2s}1b'2C+eO'I{LjbN2pc_q<g6","NejXr*VNN.xMbI#5RFSw~-?C-/4Ns+r#,[^|OU'E&}h!)k}/;y]xof"]]

private def r46_16 : List (Chunk 46) := [
  w 46 27 0 1110000 1110576 75 2245 ["qK6]MWCzs*XX>?yz4QmB^$YI$hJ1!c=Nw)?p+'@s_*KqV<t0h&.okf/NN4n1E~j9","|/B7ZG^}VM$U%f4P|d5PI{ghvqTrO;Gq9WN6r>zPH#`-5.t%8qsY`mk[5DLORN?O","t~8J<,5t4Q=r|j8%{_%df+BE^%:19R@J3WL-yP$_7==H%@lC;sfzH7t{=g^gVOmV","`AhD7*LV1r1Q`)>,_z9Y6tVCwT`qE4gA|2xMb[S}jtZqxCCRkmPxrx;k?VT:$;/$","#G!QIeLk.@B$;}dD8VEiV-z'c'uk2}nQ]->IiYO>p*PzptQ7sNmuS+'AMY2@){o(",";7-VOeGj.7b7M6L]5T'(FhMhDlx3g88a&UTkiE$FKzTOX;,pBI0QpK7l4g<;j*1Z","'}$K,oW27u4<}+7U>2b`W:7]XtJPQg2p"],
  w 46 26 0 1120000 1120513 70 2012 [">~6H4'V]vjR(40TYP|@cQg'MV8)'DbHyJ#DT9&wjBiH*UO$?06kYF_[{&{jdRw7c","[xWSB=O,uO$nv:O|g#13!K=&(-!=0l(`sn:dqdl2o93y9dwblE/I>2KErhyl+&Cv","G+K:K$D<Dx$<25FJ8nr=thlk-s2G#ACP>NA`dbbZa6zdAU_eu#y.sAdw=29V{-a%",":r1Q&yNIQz5#&{!D%BVpbYOs}l?Z_(ILzD:2iL>M%rhq@3f(KTWfrN;#fp,Ua`/c","p`*:++Yx<gAQktJv>@S0Jy+q93B,%z;_Pd5mfT%MSU+diEg%x}(.@7])rM>nvLFT","#sDh+rw3{Nw%kruBC:`h'2h7.(%61f'L|Vo6291G(r@Or%*pUD'E76V1Rs*e7@wR","ll'hQ/_LBd?"],
  w 46 25 0 1130000 1130512 65 1795 ["%+@/8ql'Wv{N2$L<!NtA*G/G!m.bH+z{&LDd-:9vOnbY6Bz*,BwiL/t2MvqA4v@5","B'b^Tc#|{D#By1)A]#W}K&2Q3a)'o1#9XrIlAE3V[-e]'+W3nvc}&PJ[8_X26<#G","ScEj}-#)ke:_2`ZV;Q%j]xV$i-HEAQlY_gnc-rT)[-Wx*r:XHIhv@e?a3K-e;LJ<",";5?-69l:7|yx3,|rCbq4=H`yo{~@E+?*3S8HFb>9Ll4P,np@l*KM[2`vH&(ew9T+","ZW+K2?cLGE3wol1>R3]0rOI<LMWQPd?JG[_$dES=;5bdT!B/SUs71;Fb=[)2.3!Z","QAn5'0EazY.[IL4lYY6dd#_}kR+,ZbX5rbpY.{YNA4,(`=(jE5_"],
  w 46 24 0 1140000 1140512 61 1618 ["`h~u_SHG!?d~$YmW.1=mBKoHq_^0$5W:?K1YrS;z|}ib%7R9k<a+gq_l2p[3:Cy.","pM2x1vtxzt7Yl1O=ePO,{$MxvXEz!WTss;Kj]Ttz`~sgxK*fCL],PS:w~2s%>d0w",")[O2q=D1vN1[9c}+5]{l[Zr{S+Y5/y<1H>@=oG_X_0`7$YG53~!ds5=NS3[&H-HI","85}Xf-Rsdliui']%pldf@[I@m&@k`{V<CK[yaxCO=0V]/*a~:qbSvg,;OQyX6A5m","fI<A-c[}#&$$a<[i6<ao^)QRY?uH1]umtd$O>sS:;z-@j^OL_/FLTwtb6}{M|)(y","(g@eL@9V5?DjdhPL-_i$ZWzu$H<nL?$"]]

private def r46_17 : List (Chunk 46) := [
  w 46 23 0 1150000 1150449 56 1422 ["NJmlWhMl&C#97,_&~lDNHuLdF#xN7a)nlTmDCWUkvHPwIDLO6ntiUY_]q3'`>QI2","G?dD1ceGPSiWr(Sr8WT}qh9ZP(Jr01s*P/lO'KHno&}HrE.8U0$gIXh+A{g.:Dpk","y|7n`151wVVJhK6x'vbD'w^M;#T5W#45K?[ec@;!3~q3@,3S'NE1{G/z[UgyNU4(","@C}zM#uAlK,L<3R)#C*D0`0uY|5N9HFzk<y-As!EOb)&nT;!_GajwQu4giGpP9QR","dyw20$g>-MO[;:Ou{DRqYU[I3F#B7>$>W8ms=LC8y8@}bOj6^vV^fV.YEsg)Afnx","nWS{`hRX/v"],
  w 46 22 0 1160000 1160448 52 1262 [">A-^/PPl.NQ0d'~M0J+?Xh_2vT$uq2C(RhiI;BR:!+1@Xg?`lKwU)U5WRR9w@-VF","Dkx3R~K?`]X,J/8{s03Xiigz63|3wN3V7'rY$|Q}~2x&rH(cbojuO;CR$oB}/aN#",")W=0!x1'g-v*fOdS8bd.0Q+;gd))N4]zTycM0tv?{q'%+7Q|;ez7.2|g/i*oo{3A","u0:nA==SQVIa+tV=O55B,e%mz|Td4SNngKE`VcWmNL7).yk_0L-I;!?/1+KY:Sl@","B_iiQ5xt}$k`FxWMvAO444AM2$197$lB./Xf4+0)~4E3'dE]DYFxi"],
  w 46 21 0 1170000 1170448 48 1114 ["T.Og8(6X=Aq,^<$hEL7YAyxlmrk`?!MEX/Qio+*:z}V]*jNIDE/?O88e.7Y]02[)","*m8-.&-[ChI>CKwtktZTA!{7z`[aZ3&*JWexv$18{fLE=GVJ%dsq1?or~/(+Pt2`","dbOcQs@Q^:nq(#U1[cVVbi'XFqHac$&`F3HsL.}B)0!o-jGLi*8Tk]#/3I%Doi>P",")E2N/_,MU5U#i<>mAN9h0Q)V~[T;jXmAnorlO1~>v!4XX%G&iz1C=^{HpA4bQ8bY","#BZ)Wx4kwqa$^ql}61;=P0,qG-W<}"],
  w 46 20 0 1180000 1180385 44 970 ["ie[vykttbK7)^nEO_7yHNFp_%:r+<q<'>Rn)H=VksuVBnow2$KUf*uW1=p.v+!>V","f{o~RM@C2_=0)!+wqtY]F=%Hw9We[=<B[uaWa>hMtyalA;#,vy3c#(*_p)mLE;Os","a$R~x5#La_Q35}d[#n5NiPzz(IC*FSHwIKVuRy;i.?t03{&&`/r(aY$5*LCl3v@S","2NF,b1/0A9w&gr2R7I4@Q/8SizUS~vqsiuz9/ysO2A7olz+7nYo$|X~aS&9)hk9;","%XU*N9"]]

private def r46_18 : List (Chunk 46) := [
  w 46 19 0 1190000 1190384 40 838 ["gq<0xn(7;phepXn_<yX8fxj)<pej;Hun5s23Yld_dlH(Ss'-N9WlttG!D,B>~Q$?","4wmT7`e}-9Kw!$d~@`s_._h6&AEa5UVO~m]F.Kx=pP#=#;q'.Iy<0l?7yO3ua@<G","-2V<pbh<3O5b(eg{|xr68!:E;q_RA%8kTfdG{yzq-N-1><b6}t])2Y<]:qn,8)!i","3<DIl-r]#%WO1%x>T+P!a_@#-;JLI;0<8,r8L-^u6:M#eeE9B."],
  w 46 18 0 1200000 1200384 37 735 ["G}=m!)kA;`i'+N`-IUjf*&ESr9a2AtFvV9m}C?$dcuzxdZq:EeYx5wmo7>3Pg*GY","4($2=>D:8B[IyI$M7#E78H{@q|fsee|1$N6G(-:$?(Szd,{SAvOix:|<K!sd-rLz","ew0A0f&gi8m?m)(sYXtq]&'n$ZgSCHk0oY8i9O`FCtHj|!z9<xp2V8TbvJt}-({n","Ee$14*7jxaAUX4GY}xR$vfS:l"],
  w 46 17 0 1210000 1210321 33 618 ["*4sHbGqn6}|oX-|HsS|L4Hm{^m>b8sg6B_~W@brwtDh|5fOCiBP}k7s(`5d?o9;;",";9U?%49nq4~o0Nh>z7$zX<*iMi(^j&5Iw#NC$-vIkH@u}PZ3&m<iBZ6#HML,J+e~","UY}p>!O]agz2S=Kl~T#|PINp2~A7itSs=bJX,=O`A6y5;2!DN+vi.k1Xnnpf,oyV","08eTf!f"],
  w 46 16 0 1220000 1220320 30 528 ["g,|];0=4y^zq2bpx^~o)PQEk-:pk:4=rRp/a{d}}PfuQy-IR{'(MerG2_Ugz>1Ng","MIQP61M&9mbL[9KM1sR6OQk4X?K!j>Bm@>FdTh2,fv$Yf9ED8>r9_jBw{!z4K`nO","'{SEYv[`oI@ebd}2R0Hy}qVkgT's<}$RSEd2~2`_,@80,K$$n08u"]]

private def r46_19 : List (Chunk 46) := [
  w 46 15 0 1230000 1230320 27 447 ["(J]Eul5kG_eV|aWVM3M)Tk:I#ayu[~8dcMK/h9WvP1iLWc!l~dy##&vtOgVwvGX.","}oH]9/^F/n-(C<(8::ag/Bl@VJ&'qv~H>o{,db'Ih.^18~E89]A4jt1RLFH3v}&Z","DUy#QYmVrIMnXMZwC==@0Op~A4X2Y3/5"],
  w 46 14 0 1240000 1240257 24 369 ["h?jSu4/i@E^g|E5z[o`1,8Vq{?m$dgVbeZFB6uv@=fyLL~{pX[<53[4-1NAlHx`k","5X7q.(1bKk'2a|O+O?BjXlECaEw<V)wd[T4$]zJPQ^or>Kd'lb+eLQ/Pg?TK}>Q>","g'y=IPgeP9FxV?X"],
  w 46 13 0 1250000 1250256 21 300 ["Lvhv./s@D,H!n(iNs/[>.gg]K*y!AO,i<}v4@|P(,}jSL*;]@Z9@3h>B{iB~'evt","WHLlJm]93*BPsZ_IP8cO,,AIa?9W(wO'l:M'T(9K?uL^PKj|2a-Z;%Eh^5jUHu,>","4XVqp"],
  w 46 12 0 1260000 1260256 19 251 ["4H'VCDy<uPw6V%-?a{q<g63q_C+%9@.B)Vkf|aPZXTHu;(,ebv|~kBic!~;T$k=r","e[#hIPU;i>}(.~f<W*z>:Gs/T!AF)Y`7N?r`qV#uj.,m/;EC{K"]]

private def r46_20 : List (Chunk 46) := [
  w 46 11 0 1270000 1270193 16 193 ["GfnK@{Od.6w**l(lOxoZ}rj@xSK+U0sJ6mug8n*4~iKqG}#h.<d$smnP3j[ML1MC","){yF&qL2(h7kX1(_6e1Ly!qyviz%9XaD6I1@q$7"],
  w 46 10 0 1280000 1280192 14 153 ["V7/8=(02f^65>ep=KlWW]1H][LZ$NxJ5IP#G=&7M#yr`x:PfU{zfh(O`^C1/j;fB","W)#{=TOy*T;mL'8s26PJ'7O|bk"],
  w 46 9 0 1290000 1290192 12 119 ["3CzA<3-7z}=rGFv|OA=|%g{~5a<Nquw[X^H|wO/>.d@YL!AJ2nk4`^7U!k4_W%-B","5E%^w@08Kh7;`kQ"],
  w 46 8 0 1300000 1300129 10 87 [",akZ7%VY>jHJckNpMW[0TH#-P73d%NgW$H:EMTb!]/?WSyQ;lC=f/[1y5@&%S'k6"]]

private def r46_21 : List (Chunk 46) := [
  w 46 7 0 1310000 1310128 8 61 ["2`Yj<l=_1u~?A?N#7{rykFq[2_oK=._%^W$.1Vd!-&r+^Ydbruk4qG|"],
  w 46 6 0 1320000 1320128 7 46 ["$<ll)QR2(_WBpy?`!a{T^I&azSL=!^XWp=X>A%Qc)b"],
  w 46 5 0 1330000 1330065 5 27 ["#VTT1om9B(U05K_hZJ=2;JhzMZ2=5KBch"],
  w 46 4 0 1340000 1340064 4 17 ["&v3rglN~%{PAD%sbQHS,'^?J"]]

private def r46_22 : List (Chunk 46) := [
  w 46 3 0 1350000 1350064 3 10 ["&LR]It(8NRK}_hmXNw"],
  w 46 2 0 1360000 1360001 2 4 [".}!?-nPf;z"],
  w 46 1 0 1370000 1370000 1 1 ["<G&m1!"],
  w 46 0 0 1380000 1380000 1 0 ["/vhi"]]
private def chunks46:List (Chunk 46):=r46_0 ++ r46_1 ++ r46_2 ++ r46_3 ++ r46_4 ++ r46_5 ++ r46_6 ++ r46_7 ++ r46_8 ++ r46_9 ++ r46_10 ++ r46_11 ++ r46_12 ++ r46_13 ++ r46_14 ++ r46_15 ++ r46_16 ++ r46_17 ++ r46_18 ++ r46_19 ++ r46_20 ++ r46_21 ++ r46_22
def rows46:=rowsFrom chunks46

theorem good46 : ∀ r ∈ rows46,good 46 r=true:=rowsFrom_good chunks46

theorem sorted46 : rows46.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks46 0 (by decide +kernel)).1

theorem mass46 (i : Fin 57) :
    bandCount 46 (i.val:ℤ) 56 14≤(rows46.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks46).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 46 (j:ℤ) 56 14≤mass j chunks46))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total46 : (rows46.map (price 46)).sum = 315672 :=
  (total_eq chunks46).trans (by decide +kernel)



private def r47_0 : List (Chunk 47) := [
  w 47 56 0 850009 850274 100 12241 [],
  w 47 56 100 850275 850644 100 11014 [],
  w 47 56 200 850645 850903 49 4432 [],
  w 47 55 0 860008 860271 100 11380 ["bSJbxX`Cdh[Sk.Yg5qC,PuDuC!J,o>W=EW1Vl[3Y/xo0LEew(r'1u=y2%}8.xhXs","It38h~Tz63g4aN]-OAXP[;t'HI6^<jCg4+Tmsb@*PNdEG{n#HBu2HP-Mr&yJ[kbH","nP~IxH5JD)fuNj*$:rK&!(F[D]}owiS[v}"]]

private def r47_1 : List (Chunk 47) := [
  w 47 55 100 860272 860644 100 9903 ["&Pd7;A6vQ]R)}h9'l&,je$}f3|tNV(m%~aMJoD>'>R|^m:<HiVu,{Htox,L2]ISO","`S=jW%',##FUBepC:Z[C@Hp&KKM*Vw+{#g}OmO@AS=e8Hxm:I+H?!/|!6^<.CY&W","#Nx)'z?L4{lG[_GLn<heq$DIt=FjP]2tY9G,AwGUr"],
  w 47 55 200 860645 860902 46 3755 ["NT}[{SI>E&Ox'tbT?$;~ZRua;'%18@Q=Fl*KPjt>P.S}Wvh0iU8MT[pj0zpu-{=h","{Ngs/y!y^{&Bl"],
  w 47 54 0 870007 870269 100 10513 ["/u[%W:GL>1Uo?4$e^A8jmGGf?:~MuElRm(R+#kv>#f[`H897n{7VN<B+ar]j1&dN","aQlpBp(GCe]WT}GAV!P`IqvDq4#Q{9/9v(24r!j<Z;[TK|?;9V).PN=j<<1UDn&U","#]{gqHBrR`su@oC}S9;v|NE/8xGf?{kG-QKKKW!cCu-b07"],
  w 47 54 100 870270 870645 100 8918 ["vnG&`FT8(mZDU$$'s/S'@%2$$Pe;D(NPIXSj,N|#N/FxEsm/J[6QTHg@Y{Byu:>K","f&bh#uo?%u;$)BK}98/x'?!c|'^l=;?_}5$:.LFu=WvT{:0qtH=+8+eQgMBS}.yh","c+~g!Eomh5<ykJ;e1o`q3V8_Gw3gkv$l7ij~wooo[?I=$&^XitLu!zg"]]

private def r47_2 : List (Chunk 47) := [
  w 47 54 200 870646 870902 43 3252 ["J~5LS}WelRFAAnUq8wtWyKFfpV#fivz;9y!>q_$>yDl0xQgoa1*2aF*QX6|_NHpO","znXLUO1R'lFLD){V0}3_jOPr"],
  w 47 53 0 880006 880267 100 9762 ["b@#/)M3@jAG&G,4(ec?=XyrcK>lE*K>!OoRPnvR+c<Kx.wo)!eir66&ES{8~hVRk",">*`()mYD=o<WHJmL#{kyq>_8i-qBoP<VL9czJwV%u.2I/Y~,ygOHWluE@&oB@wFz","/k4P%-m-hZzsZIu8U&(omM7`X?bZv1i-N]$e(sl39X)sq9_T?<!y&C()<Wls){Hp"],
  w 47 53 100 880268 880646 100 8124 ["l<;4%DH2<66MAxuBulsPn!:1>7R-~}RjNhJM&}a':M|4&p@zS96@Kvo3Q)%&$jV;","NieErfM9ZfWI@S@C!B5<wN&^A.,[w-]{u{HAgpjgflK*=TNTTbNR}%w-z[yt`B6_","[dQfv#-?{:PB7BO-fx.X=YZRgK5$*pQp0+IZCaNKpC_|W3~=.,9oEag/dvZ21lFR","'qU!Cx!Gz="],
  w 47 53 200 880647 880901 39 2821 ["HS_;`4)8tf`Lqs#)HO&HIR`6=c3fm9Xt#7nzyT*+@'3gs4PF2a5f{l'r&F-'EEa#","?t;8yE]B_S$c.&UsDa;|QlgvFQ87?oU!2/[^i"]]

private def r47_3 : List (Chunk 47) := [
  w 47 52 0 890005 890266 100 9088 ["v7<UQZVj1yEzsSJK0IpOXJ:uB|PS$8QuM@.5!h+3fWPl8c{!7D$J/oS%Muotq=wJ","7YbP+0[.ZlS5Co,Hs[EZdE@kw]?0;x9.n7,-$yLwrg6+j3ldz[ga1QU34,p*97iT","1~hz'5m^xVA]c28u{]sNV3Qj[Ps0;'LCx[6Wvs:l?F[NhiuYI^6-?c<@6KwwpHQ>","#0&3i:_}Fqkdk5/O1Gu"],
  w 47 52 100 890267 890648 100 7533 [".8%(P2tW(dii=czly/euVl{V/:acb*&Qa9B*ldl`8icdQIn.1g!v2c==xP-ZZq<#","By)OHf8n788]8$=M/7<jF9c`)e|9u6,%rX'q7ai.3<AotWG3HHMs-A|d*HFC}#ia","TU3WQ#=bT#,w8]onqc9VxV7=~s02L}_,Y0QC}mqzT1TH(8*np5{7SH8&0WR|`u+k","'lm!6<2njLlx)qcJ;SytkhUEpCbh}_p2"],
  w 47 52 200 890649 890901 35 2446 ["8TYw8dSA=3@aTRi8o-nLWG$OE`P|JG7?sq_Ai3W<x^sJbV-KsMB'(D~FaLVOl+>^","#Lzf&!D5OWu_>P<.9!,Q&+}0U?4mh2h&LaN.E)1I$"],
  w 47 51 0 900004 900265 100 8561 ["pCdcN26)kE=2SH:uc$&~rT!N]tz?rMu0rG25j'u9#SQ+}_m80UuwR,qIxjQ0{&-w","UN`BZD-a:Q3*GA.kOGJ)dV#/pB2(N%DH}p?NuvFoSO[LV6+]&_ivrMh.)~REiEM&","V6-_[P7cp2Ixr}%/)j8N$YO>IC#_0qydK,ti%Vbk|qk*}b-FKNG%y+M+0=[1yE8U","%$APv1ALoZm,64-d)~B#Du3g'5h0Q8m<GD9n"]]

private def r47_4 : List (Chunk 47) := [
  w 47 51 100 900266 900650 100 7110 ["@DWGuVfNNbYfYm&EsqDi56aUK#11O{B%+_<l3m1rnqvj9Y%$vV6sI't)B-jQt]qt","4~lsqOwi]i_zk|d+#n'SgPa(z|<I99Qc7uMQa*8W4geo?0R*<K8;'r()0p^LQJ6`","PZX&,S?fxAW].Xg!st<tg{z0,,5(2DI_ykf[.A{/ya;Xj/kKi>w?`%-Ew$)-fB8T",".RMbDUb_-q@+'o'*dJD}{>SQK(:@21FaY5u#vjp.]~MfAr5.Cw?~UUdUnp+D_yr7","3"],
  w 47 51 200 900704 900900 30 2029 ["j>P5dh<4)!Dcx/g.1vQ1TZH<$P7p9n;o+8`}>|!oVkR|I%{T&=P/[1ZQ5.&L(TzX","'im7.sV2^-B}'s2CQ-G4G4:R>'MyC=eB"],
  w 47 50 0 910003 910265 100 8106 ["clL21=E11MxvdFU40'A@8G[M{tw.VOF<$hfHZCpb)u@p.NNf^u'XSy%:ee::}M%g",",RR,|8A%:L|M|K7fa*vCc?NRS!IMGa3Kqw29z/s(Uf!)u_?.s8y0^m[f$zWrt,sr","D&KZT$]VkvtU@}eD<DAS4Eq#27SEk1Ly2H1?2>k[sj$!t{UrLaHB0|!fbEy)@_yy","7BBC~d*u)/0lf~1R;_C2V(ABbG583,|e,u[nrrpqqF1oi7R]GpX>3O"],
  w 47 50 100 910266 910706 100 6794 ["PXxfHFV[0B_l)MkSl(x/fef9;vSpg@X5v_p'1c]mGo6aILj:YVQFmq<MyaR52EyC","x]B^e*+[TT0_N`B7#HL6^7Z4n]6g5D1d@i1U60uA6P^4S~Zx]~j-P$4O_,|Zj/AC","4&(+5v(bxzTB>}p>7xBR2iH]LX|Fm#2R*]ENxfOk[l%K0iNOqnAu81Nh3##;d3!H","sV7J{!v:j|6EYO8pT({Nxq^.G/z6k+=Gzz[F_b/<<.5s75-Vp]][C'7+;%[FSk}A","$s]p##b#$5Lm:PO25s|80ia10Y#vL1Ku"]]

private def r47_5 : List (Chunk 47) := [
  w 47 50 200 910707 910900 25 1631 ["!,gO2gV)]co$lV^^.{pR14`fZb&E:|{5XAE)-Ab#m_|*SPtkC|:t,dK_oiG*7$uM","3RI8(7B*XXT,3}p!oTs$"],
  w 47 49 0 920002 920265 100 7763 ["cAB8bfVq3]0tc?~K[.^Kq3xUT*|_MBe7!}SCk#MlrPTCa^Sr3Wv&lwv{N%=cv{SN","SCKOm=F]>3U-R$R?+UEI>;?FFfnWcg@7&}#IV#}#@BNxDTyifZ=sC[4=b<=e>XE4","~`v>CKOZCsY8-8&w4Oe|c{k~XGTBEf[Q4):EX'%|0gy0J5X$gzyKKC:Tv!Y&]m_M","y_wu[&}gWPYe)Q}WyC7iXirb4,$AAv~=Nz5GcTp@8Cz/b{K4>{v`Yp<9UQ;YQ1Cl","Oc}w*{{"],
  w 47 49 100 920266 920710 100 6512 ["LSRS=@Y(lw3~d[,UBpNsV@*etdz!TsUh#S/`4ws3fzT,'4*E%2U3`n*Od1{~%A8$","97c=-DG%'Hs[1#)0Mbl;xclkO>Ja~/q77,@0ORn:8Ry8$,tZ/1?e*wa[y$fx|1SS","X18!t#61w(*J^K|p$}yAT9rQ9B%4.G=1nsp3HXR/u|.=7,AjGN(H-IweY<`jCrfA","fc/PS7TfJiwN.z:#+*yhgW,Lt_^,]eKEEZ{|aprG.?ZzptSZUi:AK`YG&7',[.U^","lleFMV/t'cZa@?[%Yif&j]1MLYpelc{(^4$?VqGT(Nk%L?RiPMW4,'jp[Fdz_q2+","#*R*Q"],
  w 47 49 200 920711 920899 19 1203 ["&uOHat^T/uK(Gh)P]xfk6Yt)BS5P]8uJEI!^79b7?@t1VE_~{&p5t5|rS!Apem2E"]]

private def r47_6 : List (Chunk 47) := [
  w 47 48 0 930001 930266 100 7374 ["uP$+yI5rC&L^(~Zl[tQZ<C$!a.^$[L.nv~KaMb~wGVH5HI9xpJ*l?#XepKM)9VkJ","^I_t*=kc2ym=>(:pItOJ9x86W_B');~l&~4hh_gNy3IwHZ+>%0+w_@DKX)Xg#TEJ","m6NB#'b/EL5bmuczn$'vRRA5HB#NIhJ90th*n})/OB2=p^U8NO!5lVwgG4thKekk","?p]5|41^9eim`I;)xc<,Icb'6[}*^,c_UjTo1P:e5Yc}0w)~8v)'>INO~3=Ek}(?","W{=N|[3}hX~m^3~X34f'8SBj`Pz0l"],
  w 47 48 100 930267 930770 100 6250 ["JlG)/8~JvD0/d8QBQ95UrY!^nW%<!$%2dfRqo}ON?_+rorxN.o=]66](_P)pA9RM","<qg`NcH@[;EP_lLJr^#7fqfm*x9c@{bQjb#?ock?FI5eY]GJyWFcfvF]1a;FGWQf","^8*h0j7(Zj8u(pMbWNl'~b^9%.jz_m!!OsOm(bpE.^#4X5_}59Cv#z9H>4<hk`Qi","Mu[@S?`ZA>qS9MNV}^_vD86:6t+P#'aZr,~7*Wx'eR(8ns)CRgJfKP<`uzo{t%#-","&.[}H-HwBhfxEqLsM@EsX1$|sk49{go/(|<fsg'Yf;bLq$S!aL*OR31_5<KD.-Nh","HwEGHM-bkrO[[0u1?W5mh,.pp)B53g<"],
  w 47 48 200 930771 930899 13 803 ["Nu5Z7*)mb1ATDR6IChRB:1mV*P80K?7eyS4M!]e#aaB]"],
  w 47 47 0 940000 940267 100 7023 ["$M~FL#/E=y}<Ys51Nl,'@XNy.7bNHhsr~;QEsnJq%'A/8u2hz{kH=def-p_<d)R:","9SYb),f!PIU*tie)5`Dnh<vf+hzycU=*QtT<8$*!;P)%C$IK3bC,92F(yV8'ATmB",".4}=iM?|(N](>X#iE%{$Fc0,lG:q,GjRkR91^%?M3yg>~qn2+GM#F|%RCv)H|&vT","XWKcw$/:60[$$Rl%u_mpc5MTJw}rcVQUhYZ(_Y<yx)pv`5HyU#e35K|ekIXr48*;","`[*Mqyd}_g0U/dE^0QV#bp$4657;hHc^ra8l~'Gw5R]_:29}!oh"]]

private def r47_7 : List (Chunk 47) := [
  w 47 47 100 940268 940833 100 6011 payload26,
  w 47 47 200 940834 940898 6 366 ["''*<pfK*jt/{_+Rwy>&v"],
  w 47 46 0 950000 950269 100 6618 ["U6|$7FH>Ay)g/sjTA2y;Rod<dEh:]f/.;$%zOWXibmw5@R%X<]Pb7,i0>N#gaLL|","%!3PgMW~wKR4)!e=-br,;IVLU4UO8Ovcq!pKNc=02P'=(U_0uhr>i-NoRFl%c((p","zm_A4-afl1p;ir8zly]`}PiOk#=.EM){aIA%N,ZNb@pAY8ALz6>Vt]vsvowvI6VJ","rlf&?tzU&,9y:Hx+(,,WDO5T<9a{~K,0C5;lQ@QvQ:S_8G/:}<G_~_z0h;=h)t{)","%{+9beW.hD+/&Q*=cpPUxpne}Er|kKjP?2$+V'12P4k8)(hwh@`JB}7bPQ/YJ2-Z","&!;@'=WHn'~h"],
  w 47 46 100 950270 950898 99 5750 payload27]

private def r47_8 : List (Chunk 47) := [
  w 47 45 0 960000 960271 100 6253 [">ue^QG1hDKattO@Z_Sde[IB/ZRhGyj#Jk6-Jo|7z+7y|Rj~~W>K=br0W%F0b3gq+","BP`VjnMmuX]-tpl=7c=+'teF1?!s-{OFF2a]'xzuNy4{M}4q+HTlNQ{{FBvZ]z9*","clySWvI9CJ+EVm}kBk.5i}eO+sm`0a3qU-$yw}cuWTM?Zto/qV{~_D:29!I37Iq-","{0Gf*1N6A}XZ&dk6~5u/We2J0IfAtzt;J&0Jh1[tMXl;L>ARpT^<#b>p^zpK#nm^","EwFy{b];|{F~WzQ_CR5RnK+I@7?K*e`]z$+95Z:.Q;GL*E5U3.S,V/duixTuh.QU","k*aJvyerA3VO@Bi/I42dg:!z*7.4~Qo3i`kxr"],
  w 47 45 100 960272 960897 91 5108 payload9,
  w 47 44 0 970000 970320 100 5934 ["VFoT.gXQwAL_%f6Bn13k;63eB.^;^4+DDSlROV5=$A.&rm5iI&P1By9g^og=@yJt","*V.4OZU#o?U|C@%vUE/APdZa#+VyjZDdLpDkkf^G[+uzwQ&13VSh[0vQUOkJpNe;","lilQrQ&J2xQ40n2u:>I#fm/s]RLc9jc]N1+|!a60>/2=+B4qsEO^O2PXvf)C3!/d","iga$tt^<5:7+k|I(23;w@omltSN-NJJ1D[Z2SZT=0D@l($W;Yz}+p{7CeHpMy+vN","{e6QVqwe+do?#-`,8Jic|ghNEm@v4~@c}P[4xF<)]>f0#t4t3I6q(xL*91F9/JLt","zvbdpw:^pSUGuz^L'hOrL?G(>u&quJ'-A[*v9'i6BQ~/Trk5=L;vzO!+:BGq?qy,","EDm"],
  w 47 44 100 970321 970897 84 4557 payload7]

private def r47_9 : List (Chunk 47) := [
  w 47 43 0 980000 980323 100 5651 ["2X<:Bby-!w#ZnrRtLbk23B(!Qgls:imn8/OLOlH!G;3,m5)(FV7vIK0pD,.k&3~p","v3Y6OL'YI@:8WE=P=Z4{:]g/+CT%<RdR@=WS(2{3-8]QTF#Boc~nWsmi70sIBO)M","CO(oW[Hsc.t3dVL(Yn2&7<H*S{x#~M.X#l,_tQ5J<yx@afs!8S'KGnOXGu[Ic{]M",")!-o*w&vtj67.?*jawM)ns'KAqWOgd^:2!4K2DavjUPoqo'6U6RoFIpSufez8n@b",",&**on74+5LUk@[Ur1Fy#aQ);`R.29Kp6o0S&)WeW-z6A_N<v^aV61Mu<(23QmQv","%z=E?o5|@gBO95rMwR]iu`T<|b8Ss4[N>xr%7&I;q|V)G|/<S>YQM9=V0fm]w$7(","+@tGdRE}F^u=4s&f;QwWtD@yl~bx7{Zq=A[_qkBt"],
  w 47 43 100 980324 980896 76 3981 payload2,
  w 47 42 0 990000 990325 100 5389 ["@7dM36{loLyz(x6jG6QE*UrRK,;;'wAn_;|wsJnc]yXJrx)6r|o:MzPCf`54N:1P","f|diK_~,/vC=#PeF6rvp<7B:JH[GgTS*FyNHwl)@0#A`K>kgr?4Lu4<0hB$|>,r'",">de:2v'TWqOuX&-Z>(4h@wG(Ga9:-a<}%^McL;Uk{D9hEU/50e&|s7gl+V=c;$jp","Ef#Is6dwb/*]!tNt-IUG6aQk(N^-O}KxiW?OzvaH>V+//}1eW'2f{BThaK!d{2EM",":LXx`Xt%'84D]>F!.jF7Ut|4e:n<1*E8-_5dP9z,qa>!|Lb&WawBtIm_{tA[S3U&","qmB_7(<c403}E0'G/.Aj93sVcSa|7UR_aVNE&0BX{Nfg4W:P&H2c,HQXpv{i+XlM","Lj?Q2xuk<o*:AH99M4/`rS*._y+o4@rDM-=<ybsDRF`%!'-96iOBf2/I:qnyXv~w","'s1"],
  w 47 42 100 990326 990896 69 3498 payload10]

private def r47_10 : List (Chunk 47) := [
  w 47 41 0 1000000 1000328 100 5140 ["_s{9Iz6Dsf_SpAMN1}(!YM`59sV(=W?'ne!L82cGwY71+Q%X'^9Fs(c%nNd6j6#Y","oWV|h-,oj/CaZ8bwuzP{~HG+uTn^(K7>Bct=Hdtu=ZgOR`BnCQN1lS;,qN}gQ'P=","@}6q:iZpr|17Mq*bExQb^7y.i,&7qCjYqb)oJ3k?Zd*6*Kk8T.G4~Y1pOGDO]Via","EK^lPPIG4rWzGt?Y4-@g{112Z2=lG}4C4h+aL^b}(zwMNI^>+eZ0d;h+Ro0@Vduv","?-c;{gKd4.;eS]:ZerEZD|v+[l=h}G)SX[S@V}U$t8ahQAc#rc@{eiBl$#izV`[3","R|H`dBvdxVamPJ]Ku8t|_m?btT{Nf=Duk<NSK2FXNBoqKj$uZNqb+}I<js{2&0>g","&1JZkAFc==_G~v*EhB$&8Y6]{yfS0*m^XNrP('8e1He@`JgWXUwX-<aKp#TZ2W/r","&toX$W7AZZqf*5'yT#9:fG>'JYV+|mI"],
  w 47 41 100 1000329 1000833 61 2998 payload6,
  w 47 40 0 1010000 1010330 100 4904 ["(($:q<z^zCnO3Jt4X:lrs[Q,AX)llu_U(E!<*l=+j,]Mrd=ubzfBP%>%_:fa[,&f","@b(to5&[$_=>p<Ca4aPhN(9DyO%C!D)KaWcfC}UUD;jKXc(u0UdL**AC#80-oT]j","BgL3F$+/7g23V@M#N`8f!p-E8mj>DBTUX2RK(HBmGb$0`hX^l@X)6:J!qPNMM^p}","!5e^VexPBuelq^|_gN,:mb+gdSONI{Qi}yink-@(mo3Qe3z<XUPg1$08qts5%Agz","rxDb7TV8/g,Z.-w9yBRr2AECRFXW7D@l~l<tH;/v7u=mjh>SXYox!OWL4~b;G{gQ","sWBp]-yemO*]_-AwUn(+69YtY+xG94a~OV};fZzNRE(fr>iN@#wdFwlW3<uAjUmV","dSEl*`.W%lCb.vbc<b<Xo)Cw)-l{DNx3#BNyGygBE6[+G34WfQ9>~!(tOs{aH&<r","/=uM`k5sQ44|Sq}h_ps%1EQ}K'%Qk{jhu1E34?`$b"],
  w 47 40 100 1010331 1010832 54 2581 payload19]

private def r47_11 : List (Chunk 47) := [
  w 47 39 0 1020000 1020384 100 4684 ["KmTzIW~?@w}/|O3ueOoFIpl7Q'E?P1skbs_,!J_M,iKqVBf3a.Z6S1[HE/bEO#nr","xD.ov/>L+}#]!#H|Y-{-w.q~Q;wc{v}+v0oVjI`v,+o{|+E`l4`_b9)@#3?V?)]G","O.(`!Bm>0ZCR.Ivad5|KXYezoD3o9F4Gx6!&KJad5??XbB[e~+Nt_wx_EruiaK5<","ZH9d1{?cr#[.LzR+'ywRIC}/i^{q4w'i2YWK{<IO~*oL'sBKXXA|4p|6515$]P!s","%B8k.HA]N>3+bXZSa$kG#$p*nJ%j#4`bvRFU*i+;U+QJOP?N6G<o&[|:,gQ=hO=X","@;j7(Ww)t&PHE$xp*cjrIPR/v0}Y<UnE8X#s7>](5[WbrlH_A(Ph+,t=dK@4*r_E","WKCKzZly0,JfP4Xdqizr)Md.+9MRCZ=hbCv:YG^BW7rb9v}XGUy]ehq&8I8u7?*V",")VzVG%4o^P&[fv&?G]'4cr@uD<[(a?PJ*JPZDKtnT.[pn4kG_xZ<ued}9d"],
  w 47 39 100 1020385 1020832 47 2187 payload28,
  w 47 38 0 1030000 1030387 100 4470 ["Nv^$6bW<f?D!We7LJSWMYp:0swefO)K#|]FhR_(a1@qkH(H5q07O}4X/d-b-;]jQ","rXlFo__^tmUY,~,gG6B^zd85^_yb]4gjbT`IW&0W/ILa(xC0J~m}Y_HF:!>rq<Jz","B4=ovBEd9;y[E)yRXTi^'f6;%fV}Dbwt!FmR+}7d;<CO#HqM2,0_Byy&M)z]|,YV","r^+{QXL|qx&^czkDHq/dGt?.v%{Tx]PZ@3}&ebKP39P`<`2Y!=(r6sPG?b++It[J","xs3K]2jIBKw_MGKdT[b6G0Fox[H.fc(Wer[q's$*!<PK|-KUlZA'Zk:`3)%)xMIL","7GA(<Yp8-pn,Kun^z'vd$;-jA'ce?6'RBMv6Sq4!Fw1/G:/w#y9PJ(1oA}f`7?f2","cQPOIA`f'Ma&b&r}TQV0sfP~+tIX`ifF%]~9ot'cyKOYQ&!/X***X5DvD;vuYFgC","kgaaoRz190wDEVTxB;eG^AkCc{N<(|my7(bB9_F|:UcG]_y|Ix%3Hh4@_CeCn9xB","id{C"],
  w 47 38 100 1030388 1030769 40 1815 payload17]

private def r47_12 : List (Chunk 47) := [
  w 47 37 0 1040000 1040390 100 4269 ["h0yy#u-IxEt|4p,|zhfxB-D5nTJ]:'0dlTu__?am%Fak9CW${A7pcDS?iMS(A+O9","8wfW#}2Xskk'Si9L~my[ZnAl%C*b;,G{D#{76lm+i>(V/+3NRJZ:^i67~+*Ftxv6","Y'Kec~Qb/@0P<f/[e&dbJ1tg=AgYjr$pTk5df7D$WB.nL0F_}f;&s|#?*q~;5!AN","%ye#v>(jcOSl=sU}~mq4C]w6FXPG-xe!Au>i|2}G;V,[{4f5~.P]L7ZE|wmj`L:A","wWe/YlA>%-7PI3oYErHX7xR`(l*pc|_7ggBDT8,ojjz|L]oL#GHf/t!c-B$,!3C9","R:}2R[j>T>V|VyQRO/[U#%{Ft|>`#x:AX/TX`!L]<:C')oD@mJHBY|1{tt1+6*M9","C2'g%B0!9k=)(9Y:W/%Z6rwW-Hkw2BbXI%MwDMoKDI-7{J(`l%Ok)O$l7-*$x!Vc","-bQ5L5gF#)ud4;xDz)0Z/*emUB#}PnZEL9T0zj5Ass}b=j'(ESfbbiw<n/9<)L(n","$J6(%!(>>wnG:IY"],
  w 47 37 100 1040391 1040768 33 1466 payload22,
  w 47 36 0 1050000 1050393 100 4083 ["IWx75mgB3r%oSWd&Ka`ZeLZAijtJufcJ8>QLZB83V*n^MWD3_iXvI~{6NI329Z(M","eEy^rF')p9*Da0@#C/qz*Hf<T59#U6iJWgimlrLZ>KjB|!q<{(2UdK>^SQ>To/T)","pOicKpfPB*#4#3:VLIG+BCv%;KqD2XrW}UEth(R!*FbxrNfv!|FQZWDQD}Z+f:'?","Xc`i`bNwB,j>@UXl+Y6=xlH<1<~8g~fs~^g+Z*y:|8W1_2Ebj^q@Q@ZOf$X7WiW'","-1P!2k8YU*kSn@(LspFcGBd]@5iAeQ0x*8[tbV+.`$k9Wy(hf#g3/>Hmx$|*Dom*","@v^HKLvB1$cpq[G<(HwYs?,9bs18zwKH0f9l.m'trds1I`+/P_z`/B<~2JV>hHgh","jvrNU.T+&]g8vR[DT3jx^A,OD!P%4x,dE+FG{=j2Gq)X>/DT2WJdw<cA-K-V^Se3","/ZH1hs|_ix>SaxG*GD%.)=7mcs^-HR}.*Loua0>]eA7pOE}7)?M2jB$U%@pbkWa=","'mi4Pl'w.JrMjK]W,2S1Q"],
  w 47 36 100 1050448 1050768 27 1176 payload1]

private def r47_13 : List (Chunk 47) := [
  w 47 35 0 1060000 1060451 100 3914 ["ikQgaABDrl?4&r@N&oAB/FGYEKAW:hXoL2^TE/iuo~-T3CEs%9YRXPN?d/[I3aL~","j.9MYGhV<@o{Y/j%021?NC]M74.xMZY(,T&?v>x]%)5]c>m<u(-ANL%t]2gzrw.n","-6!a$4dCt33qkRf6'a<8e`[rJcN[RkYZHWGb]-h&1OD-kt?IVGSD<XAK-#vY`v;=","1*>?9Ps;$R30P!S*ZdanCV$+;};.,MN()j._;e+.[jwqu{(AW{~yq$;6!vpUaHSD","M[wo)E=rYD;ku$^iRgThPEn{#I3O>y!5@=WWdt>h?tybQjWm70Hk`qmf!1rD/l|Y","EuujP'6&A9`U%oj*X;;JTYZV:fv]z&<M=vW3H67|GMq!T.Uh72Xm2>018d|'?,IM","b##qTPK=fZSZbkFW9<:uc!s{iprvSNd19g%1{4IxD`x<slh/k:Sd30sM(^jipuUa","dCH[}/A/w18IIzJijSn)anW<WA?-P1`J4E+fUySu=)>$gE}SuGx[#8FdcmhQh'XQ","#]OlJ5S<3f^;387,4c(Xm0"],
  w 47 35 100 1060452 1060705 20 853 payload3,
  w 47 34 0 1070000 1070454 100 3759 ["lp+/6eLC}&lJ+OfB%+}E36ed9h:9ia<,k#8cB-YqiE.e8|bWI`A'C*_nm'%~+]_E","{Y/(K$r^M~LTZ_D(ACs4$oOJH.zuid.lgw+#%yZ[!,VEN~]?F-Yrv_b<;.gOcU4s",",)*g}M(A'[uG[[4/^,u:b4vtI{M:_H94?VDDX[O9j2hey]N;nrkK?fmrPgD**/XY","hE1|Zl9z*,m4jl|J}_}An6Z[%~2/E,b(fkNG6!<}5qy!a>V^We4>9-25u2dWjpAG","?OINa{?W?u,j>qa]HTH{'DR)4%47&qXP`Upr22b@fuGZv%M50u7{*uHk8WLqw,uO","ML?H@XD:R#FkA:leC?F'Og0R47d[>=ZN;_IP!7m'Pidv^kP5,0r[QvHdU_yf<;1B","ESj<n_N8lN}i%^9&(H|m#hu+9Bwxy!w?`K,`Qk~,H{VIuP*GKA0]<dg<uA`]t#O9","zGX6u2ECPj.*~J7bHZvw1HvcVn.RMnLG]MQ)GI}_=OG,n)0W^DNP;~,LZT:5SD]+","$r}e<ST~Pb1>JlFhSR2v<V#tw3"],
  w 47 34 100 1070512 1070704 14 587 payload14]

private def r47_14 : List (Chunk 47) := [
  w 47 33 0 1080000 1080515 100 3624 [");pON./xZEDL2s'tv&O8nP+PO`ev[.!hsZZ+t71wX(oF,AU~/qv^LCi.8i6b%?Kj","1-QmcU#{n@iB^cGQ5l%+D]'h>ci~X&0+?[Yx#_T4UF:QPnf(Y^d&N)`!NB{@MW>i",";p0PDR(RA@%2xT'qN;-K_8x$72;#RNA,0AA*,57_kMZ~V}b0@n,!')(W+1ykz'WR","IC0()H_|<zt.zc-sOTt>F#pM|T1`+09:Id&F2TQk~^&g.O1CRv@Iy<1wq+%ba')5","P+Q$H,!6TEUzQ>_GHC)e0PUE7]7;}D^B^l<~D8iXGO/#%p2fAUk;s_j8y?n09<[]","tMM$ShVM1Owzzzx9Q9SlWB4:Xk;`eBzUH{C)g,=.,Tq&u.H`!`7(dt#dlhUXI94S","1@uwm<P0u8::SK$-~^&Df*hLH2[8/%L=$S&v:<EtGi$$zE%F`8T5ol4ldfbf-_(%","f})hM?8bj<q0Vp*yi80qj=%<83;/4]x`&K3RFL?SrUpG+5b)M2N]W{W`)y+Oo}PY","Q391stV$4`v0^u+{Z-O/X;btQ]wG"],
  w 47 33 100 1080516 1080704 8 331 payload4,
  w 47 32 0 1090000 1090578 100 3500 ["./|kFn85de76Q4j#c3#ip,g,3]4A($*8iKx'<Y{=^7k}dl56TT7RidWFRqd9I9$E","yvmo`R5t`<Mbv+({R#v%As7/qj*j)4U)y*?slvSF+h};tjn6`TpMbmBf,B=xg'FE","fuWcC2Yc!iW_+)wmT:uNLV!)ZHnS%:`G3[i;Zjf1WYs~Q_$Hj`@+q~M<rKw}fxsx","OmY2*Khc5o4Cceg_9`[|aYS,zk9qfQ${9a0[_HX'sYWgHgW6b[QOh?8C0yxEO3Z~","*%,2NJ~`7eR@ADD)]TafxSQ,$6]/pti_bv#?[|HRtQ%T)7-f7WZPn(guQGbL=G%;","3<Y_7S21%7IDwUg~4zdYzHv.6V5u}cdlEd}F'#ZZ3@{S$#tLk}kZWM<O_d;Xg2nm","TZP28/,}&p&HIK?.OqM$`/5+P/e'XScP*4J]|c2p@0amuYDJtG4N`7|y_RHf[^OQ","OklfGAe:==Z]PYG$OSjNa`#nZP0VDo(D+K~nYW,>sq-!S`Rqhv`7h0J{7}nIL[Vd","Q^{n.K]J;QV4i)^QEWHNRCc2N2k"],
  w 47 32 100 1090640 1090641 2 82 ["#i2GG<Je"]]

private def r47_15 : List (Chunk 47) := [
  w 47 31 0 1100000 1100640 96 3240 ["K9?*ZKjclX)9IBLA)YZ;5]2ikm2oS]H_M0t@~N8sUkwMW.z*>|YQ'!wdVRze;z){","|pBd=_n&oE%I;Yf(4&>+t&lSI:%XkAXUeY-=hbh*h{,~QqjDwVE2}U29}YV?sv#V","][Yzg[O1b?|UES03zrwW4kj5/n?r>JQj5^dEV'soPt}B}VcJ0[Me%7<u]^rG7;]~","elxo^cOhj<@g6[Rr_V-Z928/yE0H8d??[mOQ#Q<EF|p@c)vBu!CH1qE0;AI@2wT!","C}iAa.w#i<&,qAS'R}eQ4`xlY0+(hVsF+qRg|d_KA]UjHyq?``]qXR2HIc7PQE<l","W`|lqP3|B9S9bDK0b$Li}jvgObVRgx)HumNbw=vL%vJk?4L@=7j_z!;njwh::yLl","ldSSO`d*]Q|l?c{ethFOh_SS~s$<>@?Zmy/(d,67rHo@pS,n8)IJc@/[@~Q7H6A{","[GEf]'ZvrDgN(k<T5t9oagE)?cI+8s>g}p`Zwc.5-I2ZJtmuRO*4e=fA0[xTf.n}","O:JxAD04u<"],
  w 47 30 0 1110000 1110640 91 2954 ["=`ck3g&Mig,y>s![g{?$UE0dB!&X_|XxebOe_Gz];TDxt!CT&sD9tA3{S?yZ{Nh!","@+4_oA@h}tpW&/-|_'2|b0v<aB[xz(pW/r)X}797(8%Hh:nk!:vBA!=y(Qs_jVc~","Mp^:'gl+f$g{[yX?Qv@ZsyRcGL5.bce1s[i(zJ#1K8A]toVMyyH?U*:-HIeA&4?&","xev:NA.J{1knDK:}:qI1/k+37y7s6gZ28n&+PYrR#?{qPUOdEI|<OAMd0?4t2b?u","}~gc66/Y`.^)5K[S19D6]/_}$KET/h4lf7|5`2K4=867(CyG:4=aeYf~)a@rzCcu","hVp~SUJT![g>6CaTI3R_(:/ge51Q{B6gsfI]h/VJeXG49@3AkR'6X1J-YHpYiLS!","n)plJTwWR>`80*3?+&soG}MoDLl3c*1Y1*PA8!K8SO.uAx?MtyeOYYo{(B#[{v^9","&%QzmrW-M7uhe0)ow--vVoCjexM~BLGqg6{z7c)(aG:/b5nJK"],
  w 47 29 0 1120000 1120577 85 2651 ["RP4?!%YyiY4r(]J~k6S<r%/ce6p/,$RyhZup!AI'~e2>=mFp7{yt-q4oRp}<kIgN","r~b)I/9wKSk2KXK4Wfd|x,l^I~`n_#.cTJKo^w{<=7rvhE:O:fQEDyq;LIuboT*Z","_8LNK4KzzSvSJ;nCn>;k+mCX%x).z^=GsZ4U;[6jM.p%CHn[CFlgEk^Hxw(iaT]t","&}Fi`j37eN*]m)`Q;Sv;A6JkirP/6MDM!s-@<lq3P)cSJdCU8}`5.11]!}%s-_{b","^;WDdNe8^aWBhSAU*eD>vYciQO!y]<hOh<%4{IRQtR0)R(;a3@;mZSO'1Ygx>r%j","8_nOA(~:y|}rl&vz0oAEsLQCt_L>HV,Ep))j?bRsr&_~QxAHRnJz[/Mjsdm>kb-(","DLp8IPbD&.*zHFQ:wD+y:Ui5fh>zFmCKp9rS*mJ%HbcI!`;}!>'GMnxEp-Fpn+^^","-C1V'Y*aHGT-)dN4$.)"],
  w 47 28 0 1130000 1130576 80 2400 ["9~A/GTFR.TwyPn%^^|M.6xZU1q=l^&P7?w'4]lX:_lF8v1fGKOAKX2MC=UU$zzz:","5)jE+mk`hDXm#Wz]V}8`Fvq%&^WO*dhq]V{4Q,y`R8%Bx>ns'adYBUSht;It$v]$","P$e(`Gc+6Bwk+'7f[)gP#h/V5HMiUj:wc)BW0K;]LKUNQl0+nNi*raB`IK2Fs7]O",".82z{07ACd~VQTg/<nm$-H7nBm4:YEW)GW]+8If+9KDK=7bByZA+sQ8KC[!`nRl9","N<!]4%k`4nzX:>d+A;T>~wGs!4*J/raqb3Y|7;Xr/qEd9=uhCZ9<TrrS}8OXyl4O","U/*)nBrS;cF'wO#@b:DMjCC+UzB=-Bd+?LoT8NeT##wcX:%&z%y{1TU0MKLue&_H","ZHRM6S!6LVaDFVohy_<qiA_rm2;Tf_cn[@UF0MCQZ_ge*EKI-O|,F1',g5jMw"]]

private def r47_16 : List (Chunk 47) := [
  w 47 27 0 1140000 1140576 75 2167 ["E.&no$>V5b]L4,~Y8kP2|/oht8P-DN$bFjBX3Ym?,j3*73Z`xp0/WJ*P>$4XFRj*","s2J4b`[#f[>9/~?D!'W{6*:JN9G:/1h`Jzv7!5^=!ftSW4MdshPX(q(JIRvK~fWY","j*`d:#-o/_F]MU!Fu<FCwhkkQ0YX^i6&1aJCC1jsL.yY=qQtXwW>H:O0BJd;ybr,","}V'4MBiq8p@_=n|_mN2%k.u>y-5e(QWRZ<cz{YP](qa#Cc%ETXVena';wUTvrBu>","j61=5xil@6)FeYdL@+Bb:AOYVrQZ!J^0gLs6[e&2Q'%~)c_?3&i!F8#'E$tUm+;V","n::67S&>y<No9zNFJ6HvZLr+f7eSSy29N%~/Mw.4iF=M>z9{ssuy.DSvgrK9C9xY",",pD*Wn_X~nZeau1GRh/g-'7cC:}dm>1dY=<c0;"],
  w 47 26 0 1150000 1150513 70 1940 ["BB!s,5c^0-4`hs+MT+U>'Ag)T7#eE_.Y7zc@UuG!!F|WPtkOcN+t8|X@Aq2_Ht.M","4bi-xn:6j=qri@s,<6wD6eAra@E3`PRy!Lc;bjRK2u>n0#V`[=*kKF!j%aqS:o_:","f4MhGyd$Q|3Q#3STIFH3Q%N8Om,8)06MW<0HJ.Ad.;K:~~hfcg)Ehr=w'^<+p.2?","[^]]gB9GdmfbOs].BSZSBN7`Z7*A8|QIYWg8>xl~qfCE?fw3%1/#pqh(Yu<`y$|s","Of9NU:SSgWo`f)MTu99P67ucsW4qWQBlU2Uc-eEtpEju,*T{Jaqdo,%v!R;q%*I7","Q]1_rt1X}n+W3{Bx9/Cs>/XYuUU[b]cL{uYl/+f>!jBk<@S^vMV[y)bZQB@fbl_}","%!Pv):OE?Z$:-')W"],
  w 47 25 0 1160000 1160512 65 1730 ["}6bDeZw2)T0qp|JM~<e$l{oQ<O7E:><F]Us9[!NJ(04wff.^:y0}}BZ~'XLN_;&&","h,@>oV<a=*x%ym:6tOB@T`e$2-'}ZJXl(=EBJ>~&4M@:s;9@}1gIy='w&R:H5dd_","h!lEgy~z<R>&eB4|&t+G0Bg40i>f@;5q1q6s2H}JG1;~VSZk<[bd80#&%KMZe>Ej","c;AZ87MVyO,$ISOKmZE_P<jvw[/mX~.{#%j*|lahEWvHa1kb0_C`Zc2^,:P-v|0|","X4uD<)<(yS.o2l-F>ikPQ!,+!7y>Oo**-5<moAAJ[*>O*4[E+q~U<V-$A32{b)&d",")d[ee>*1hAF3Csb?(*1Ko3wNR12VLj)flh@J#H`=+J_GBcmB+6j&CA4n"],
  w 47 24 0 1170000 1170512 61 1557 ["%y#*P>0`()!x5_plrG;,_[u,j8sf;uw-q6~Xp%`tq)$4h~Q^F)Yf88@VfGvT!/3:","G6u1])V6NL6Z(q3b!k1F7a35(`f+@99:9bqw#kn$B!=^#Ej:*F2mU:?uit9$Huz_","E>[H),LN,tYW&!Txaopi%_/dY#f0Rx9kzhLu}p2Gj)accIF^U6XAPf954WoOh2r3","O;YM91,h7!%TzZl;I(+6hf<qBw>tN&8T#ypC@9>vFi;70QRhC5RGA54=cHE9_d@h","QU/FB6l[Z5E8w1?fR^(PXZdW5qO7{&GX(QbqG6BR4V$TV=:h4B}>SN3R*BoDmi[S","*PQ$]?]Q2/~|W_nJ>m_,23S$}y9onpY:XC$wCs"]]

private def r47_17 : List (Chunk 47) := [
  w 47 23 0 1180000 1180449 56 1366 ["~0EXx6h{,.(j%?m~]osCRTDri<)?K`DC)<AUT0h3)nI?LXYc<sIJFzI%=,^W9ztZ","v{W20q8A;CTME`tMl+}Q~Zj/nTaQi%OMRAY)/dXq_duryv'7tgqlRkDV[eFnr#oY","P:o(*~t`k`vA,}49`R)v#4KrG0Xnr9}<T58}oVGThePnVqr{7LO^CTrL_)I|:2]K","tSX[iC2xnSCYpcevFc[IS2uSFci3pI3er@N},NBD4HH'w[Z9Dtx|i}vn]y&n~+Ir","lZtj!D?47F0!}=:/p)tFb!e,27yt9kZwdE3]5rJH5@O!&`I,Fh[KV1_qe?nFi%zE","$/#C}F6(N%:ya~(<"],
  w 47 22 0 1190000 1190448 52 1210 ["Kj[IUaAd|aA3FHR?3s)>F/W^dd;h=H}M~`{@nJ>de)&+@8~^6goGcdznp<162*M2","^_*Vo:-hS&hZ^aH`%t+PdG@i5Ia7G+5R7]>`GT361{Hn`$m5a6A=8c#&#$z[XUp3","Z/kR|e#2ocP$]/EUD>H3Lts7I23|VUJk.^@n~q[5ZFJ<&daAN:i8KAL`W_)l&H8*","nR0vA(p?^-^<sRBCX+Cr41A/zo=T-([+;D/P[9a:GuV]R&;a[6r^[CcJp<Tlk7vU","K4?^$;!,5n_G|T}wsF&NPXZp%Scetk9~}+AFE5k>GNhy%.ReOq<_<3xBLRJo"],
  w 47 21 0 1200000 1200448 48 1066 [")I-R=KPcFhBqs*>.]@3c^9.=9CZB>#y,&;]1Vms[MLZA_-wwz+L:Xu2LqB>R*z)1","r~e%DVR]9c!=Ro!cWMkO1!!cDh%!D3+Me-j!YuMhR.tZ>^x:RmL;XyLuWb1S?9X8","F4&syB_>tSjas2,vQsvNo{ILJ&YPNeYcXI6sgM'^o7P|P0n%gQ#.}T.9+|=pn$?,","fp&)#q[_1g@2$l9Ik-`4#kc6/?NTAe_PxObxQ76GJV||N.s2Xd&f?qxYO&Kh:u=|","6=`Xx]3!^EO(j+/#epDHNQ5y7'uR&oI(@"],
  w 47 20 0 1210000 1210385 44 926 ["E]|^gGc56s@L>K<@u3Wt05T+!nE8>Q'd=2La*%<A`WGSkyBm|Sm=bC:7KM]&(DW{","q&3FYGb9w6d5.q}#m*f1$Q?6Y:lqpf!fi^n4rz;<FM-?/[S5%/=rq'?J/@VY<QmU","Wt*+@6o19kb`Nd7Q0W1p4,A`nuUA&2gTvXpgXtzSYbZ7j.h4rJUWM{mZb6VlR%s[","gBSTd:GYqZz>XlEshr][LI/3I(Y~%@UC^BEZV:wU}kr.Wjd:InC5IG=6o#8YFkm^",":G}%6g0RAe[a.aG2"]]

private def r47_18 : List (Chunk 47) := [
  w 47 19 0 1220000 1220384 40 798 ["N6np=@WJGDLlqm:DQJYz`<Rx?Yn2G^PtW2aaCyvX'7*$0&J,8y+b#Hskv/tVe!+k","!OOZ>;]N#TIGM)Jd[*sUa]6BWxewdv1dBvVm,0LL}y?OzB2G,;2R|1-Fus55Pu2w","RvzTlxy'HE<c4VnWtahN-<mKWm{%t/u#pnYbt9$EptpVn.vv;N6.ZbVPC|'o)&t9",")o{N(=!T~X<?LN(FC#S,9x-Pcw=RzA8Ac_=Q@T=uhoH8|pED1+,7mbX%"],
  w 47 18 0 1230000 1230384 37 698 ["b/aAC^!Xd|[9lFil;fg6@B{?nN_m8bT5.qa'G'H6F>efBQP9D)[<eu/)+)^USGoF","r+<!{l!n%6%}?MD0!,*_rQuTOCp$j9P$1K%XMYoZXaf+QY^=:+1Vid_gIG}]q/G@","Z*kKtBY'tIIkF'^ASz5dK5>X-?#TsMa~WcH+fz6e(zvp}/DqBob8Q}Cc~}]sn'd0","L4|HoQDWEVW>9^AZKE]h.>._0Jmh.-~8smIk"],
  w 47 17 0 1240000 1240321 33 585 ["$KXA,tk_1Y0rto5du/_o5+R|hZrHOW_7YZSx1,proztWjB9IiqQk3@}*mFjv'.oV","/q,L,]UB0j50Wy%.>#+M#`H#u(/_?A/]?~t/$GJ*C+!Th1C9}.Rks[8<6oJ-v]$u","^vF'9~5$,ZQvP$d$E{7k}#^fEDhVf#$1fl<0Y!C%;l(C)inPTwia2zrZs6af|!k~","og&/%LYEWv"],
  w 47 16 0 1250000 1250320 30 498 ["?6nQd}v0oUap''86pfZ@`EZ+f0S@I'wdx7.Iq;V0j|U>GjS.^{zY,gOv@yO*{[13","5{<c8&]~s*.n}h'Zs?9y%V1wcB<=WvmY52{0`^o*qW4-e7#5]/{^uWWA^`_?rr%R",",m`UXL;|@@;lYTy8)B9Y~-:QUrUmGRhJoG@'j4_y_9fM7nZYUYQ`|_JdLs"]]

private def r47_19 : List (Chunk 47) := [
  w 47 15 0 1260000 1260320 27 420 ["]Ssh}vQsqh*-4!*SICSc9__SH'j$_(QI!/j?RSwT|_#E(x4sw3GNc.SW7ZpL:mRE","_4[tS.P~{i6OYh-{_U:PM3&JVsMtQ';c%*T`l]&/<}HK&-emS_J)6T^TU0o4VW{-","DUy#QYmVrxu(?q>~#MmYc!<9;P'SmPd-"],
  w 47 14 0 1270000 1270257 24 345 ["i*(xTMA6eUH.6UWU3)TWvOJX_V9v=6?w?hV5b-g/E2[iTPUcP}XT^Kh~n5e=H-bS","`.II+QY}dBXk+tuQcB!I<*CrNdO_}}|uk-)!mJrM~0i~&czv}#;[2%]`i=9*I-G.","'f#[ozso=zI[)ew7If"],
  w 47 13 0 1280000 1280256 21 279 ["qW:F?<>vp/Q}ZTa&$~t9J.c'V%;[Wh=Fmjm<K`eOxKb88Z-v0*,iR[Wc6oKnw@vs","%k`|F:ULSn/m$ykcZ.xH-)<$~>]qKUH~z*86J.q<d$euw6am<@&pPN?&A8)s)C"],
  w 47 12 0 1290000 1290256 19 232 ["!kU{ho|.xu=Omt4ydZp8(QChc@_4cZTo$oN$<d#aS`??x|'YLu7_1/^7glE|&akg","*/i>K!}B4yZD~1dHh*>|!>Y,SIUyG2Frz'aaJEs@,G{uSNHx"]]

private def r47_20 : List (Chunk 47) := [
  w 47 11 0 1300000 1300193 16 177 ["1{W*S8+#eR]d31=oRmXLV,IEKnCd#g(MJd8`m3gR`<?]@A7(Y]Ep%(bf#tihb[8o","&F-P1l*{JU]BSR)&EBl',5bnp=z2TE_!r"],
  w 47 10 0 1310000 1310192 14 139 ["8EAIqB%x11qUn$zkir}+/Wq?zA~:WW/e~iB;!`*@7Wf<rYnG@EY=Xam35{g*qGO+","W)U{;U20j&v6hlb@i.i;Ehe.'i"],
  w 47 9 0 1320000 1320192 12 107 ["#acM#;L!Y=8wv(?xR&8?CWykk>mm8{};LOi@Uw;Y9lwnoIOFNK{TVDx.}2=f#Uhj","1Q5<*MG#m}"],
  w 47 8 0 1330000 1330129 10 77 ["CVIzWwiztz#L^]^O5,8MoC}4K|'@tF6N*0f#0MM;._O@%7Jgl7j]Nlpy&MJ-i>s'","uL"]]

private def r47_21 : List (Chunk 47) := [
  w 47 7 0 1340000 1340128 8 53 ["$0*)@,]loeBvM^]<?&jIDZ6yF<3JS$F'xRh!_018G&*;AK;F(uMs6"],
  w 47 6 0 1350000 1350128 7 39 ["C5UhWb$0*!?z2%}%HgCPw5Il'XEdVU=J:Nd4fUI<cZ,W{"],
  w 47 5 0 1360000 1360065 5 22 ["UkWe]'A[2pc|Vws2*K{^DTMO!E-?Z?{"],
  w 47 4 0 1370000 1370064 4 13 ["G|yi))jRZuV[L{MS@P99><L1E#"]]

private def r47_22 : List (Chunk 47) := [
  w 47 3 0 1380000 1380064 3 7 ["#4pq92#xm06WAqy%1"],
  w 47 2 0 1390000 1390001 2 2 ["#*2yKJ/5]/y7{"],
  w 47 1 0 1400000 1400000 1 0 ["+O%FE"],
  w 47 0 0 1410000 1410000 1 0 ["@y|sU"]]
private def chunks47:List (Chunk 47):=r47_0 ++ r47_1 ++ r47_2 ++ r47_3 ++ r47_4 ++ r47_5 ++ r47_6 ++ r47_7 ++ r47_8 ++ r47_9 ++ r47_10 ++ r47_11 ++ r47_12 ++ r47_13 ++ r47_14 ++ r47_15 ++ r47_16 ++ r47_17 ++ r47_18 ++ r47_19 ++ r47_20 ++ r47_21 ++ r47_22
def rows47:=rowsFrom chunks47

theorem good47 : ∀ r ∈ rows47,good 47 r=true:=rowsFrom_good chunks47

theorem sorted47 : rows47.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks47 0 (by decide +kernel)).1

theorem mass47 (i : Fin 57) :
    bandCount 47 (i.val:ℤ) 56 14≤(rows47.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks47).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 47 (j:ℤ) 56 14≤mass j chunks47))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total47 : (rows47.map (price 47)).sum = 329578 :=
  (total_eq chunks47).trans (by decide +kernel)



private def r48_0 : List (Chunk 48) := [
  w 48 56 0 880008 880269 100 9227 [],
  w 48 56 100 880270 880590 100 8728 [],
  w 48 56 200 880640 880903 54 4398 [],
  w 48 55 0 890007 890267 100 8915 ["1Q,FAAcrpFR4O:256d/|utS+0yPIZ[b@Iw8[}x!g~i**U<p$771p+&qEskXh[yjF","#UkXPm'c.kI[mk0bbfD#x3gnYG2c6kYUcWke2MR/+>a*$W[oV-iVm0p9#8f#BCTT","$<,iI+a@*@pRxRWm@?3(5+%`Q;!_XLz&^*Tq"]]

private def r48_1 : List (Chunk 48) := [
  w 48 55 100 890268 890640 100 8369 ["ryVK<oyN7/@:.(vpkO,^4,(UMowdpU,;*=Hr%){*ls:U];c#.HwE&jBxE.9T}BWO","s@uP?pcEU]F5v(@H-a_|kx>u,wF7y%tC/bj68YK~{Mf*#(eY@NWRAVmW|N5&LWgU","#NwmUBAf.vCx=eb7~mc'?;,;4][WCXvz;Qo$f*Kn6"],
  w 48 55 200 890641 890902 50 3893 ["p7!{5E,vrTnTUk;m1By>9DT{A![gxO)`5a!%H^26r;:Ozx|oRjb@=#0ulfa8Sd{l","=v9^{bOWjA6co9ifED25"],
  w 48 54 0 900006 900265 100 8621 ["qvzHhJ~`%mLo-$+J?448KMr19}zF(:S*A/=^j%aFX}&^{`LWorE-!E##MHNs@*8B","pTQ=Q37[~(7<.P')tin-bnfeNB]oq?*_S!4|'ACl/-w/AD&,=//V/=;BSLlF6[m$","#]{gqHBrR`su@oC}S7z$@mo7y6WEhHC}/v>avPNoO;)5'+"],
  w 48 54 100 900266 900641 100 8022 ["g(=A%JgYXx75^iGP}*0kTS<4/)cg>hx6G~QBp<`d'P,ziSoU7HW~BO<t_WZ2oC%7","71%Gct6o}uMW)Cu,8M%g/%Zaae~`nS&+|Z_%WA(+]qjmhH.XgPHc62E%uM6`KF??","c+~amwTL,W2P+G<M>[?$-Mgnr''Xwwf}ej/'qvB>~}_lD!X(grn/3Io"]]

private def r48_2 : List (Chunk 48) := [
  w 48 54 200 900642 900902 47 3502 ["8c[G1r8iJ/|s2M`r~Bf])W@U:mFA1Z+FG3DKg<?uD:B?c#li$,mKc_RygL%=0?*+","=b|>u2_z|F._U7FOs0:O*3+/DRgV9]V"],
  w 48 53 0 910005 910264 100 8323 ["_)ImbC`]r>Qx)n&Wv/fuoR)(06)2NRlnkinK{X&>q6pk'(Zt>^hPh0gjBZmpB+vF","dd~m(&fV9Y+Zg8vgKKWnO.cmo%oZj&Mce'v%Tsg]1(Cd6Y)qk]rt~2*L)]:v.0)F","/k4P%-m-hZzsZIu8JO+k#Q:Fu}Wd5F&olk:z@WO-O:13W`T13cEO)YYvWA'/i596"],
  w 48 53 100 910265 910643 100 7677 ["e2xq.>k`{_Muwy/F?8Zc<vJ:U{^pdVV>5*ax55>bLEc,:]:UnT#ZD,U3#G(q>0,d","Q/bz)M_$Vcj?V)ek'[/A2E482$SG@{)K((~tFi}WaJ8[%&5T!HKU|%QTF2+]9+/`","|NP1hN`M.iT60xk6Z!.-@q+}po,c6IRJq^G5X4<!@/Pu`83C&ur{!D~2WW_y(_ZG","'qU!Cx!GYo"],
  w 48 53 200 910644 910901 42 3001 ["OvLodXz;gR873sl~;{~k#Br[tLDZVx<[VmOp[G0N.0Epxv/spkC3i&aOREq!fdd/","Hz2cp;-)3!$g)U|c!%f:3k)phy;Dcb.Af/Ksv'cYz_"]]

private def r48_3 : List (Chunk 48) := [
  w 48 52 0 920004 920263 100 8042 ["O([4Gcl5`uFD.f8X8d:_8)<xf9)7zdL.ljLOx0b;CgLR~_UKt]M&IFTd:Vx:1gvV","?[@E~2>&xX-^kbEstK9WQZ2SnWB#7qE/]HICORd%7*#BR2+>W8-M&cMdMQ'WnWY`","]lN15'%(lJc6$-pu7npP,M5@5YvO3^OVg1lvcefUPFuDR_l6vKLbY4;(N|dbV~9l","H,..>}w7s(!^#-%<u"],
  w 48 52 100 920264 920645 100 7338 ["B6R>Q*w]/carum2GX):w8'5UlvLfeNO+HybB2C%8.1Q-Ba(UgK64eR8lsb:gC4<#","LJ*S<&Nm|9%J(uLC}L$Qt1(NK)T-1..%qeiWpNA:y^a3F2%=9tHtt`Wd<;kIJ|jj","/%{j8'l2Aw|IW&!VbYw%Z}EO!YSAX2:E&k]{$5;Z}WyG.+1z%$WRp=k18Gm[vIsS","O%('AFDRR>sow8&jggmk^DrB-^8C"],
  w 48 52 200 920646 920901 38 2617 ["$')rh~85*kof}76{!{RyO!qf6J]OVTsP^Jiua6]n^]cFtz<L55dyHWHx<K&%K>Nm","K3Wdkdr|LrZ>=g,dgPe@}bmOy]?<xy_bo7Cy[hD;|EED=r>y+"],
  w 48 51 0 930003 930263 100 7749 ["wb`+&Uk'{5hl]C0yJt0hDfOcD8;K(b74ZU$3bW2$[g/+7sm.HMs6P)1FHevM`3::","u|hySeVJp&z[wX+?20[$LG5t*ugXE))hh6vRZOEcJpi/YV$x=v|2_jw?h=_/o7Y^","oD$?S/(m1]2a[<Y```B,)!+Py=MCaSBmlz=H-fj1|g`nz'0KcZ;R`5FK[EW2sM+q","#*$c=#4OWG`.=E:5%->BF,ktuI=~m.~#}cL"]]

private def r48_4 : List (Chunk 48) := [
  w 48 51 100 930264 930648 100 7006 ["lIzW<1i8&t/mdnZ]`1jEN7ZG/`v+dgK38{Z!pakkOc3VVYmDgfU4G2O,`Hi8}CCp","@MC{(5U3ZY>X{}kGOS}Dh@&y`wUuac'v_?Cl_TpJy0|~fHfl}iDg&tnUb;/YV$:3","F]7IK.B{%9RX.~|s'J.nW])_Y;Y-SyfY^w{H}Qm^}CFAg8vpQKH`AomdEIN#t+9k",":1n[F2V/-=x3}jtVI)+8<_xm2&k,RDPDDUGlyj~_[O,{Tv}[4t`sU4@o[NoHp"],
  w 48 51 200 930649 930900 32 2130 ["#i3/If~_|#h%0gi3ve'A6nX-Vbu<23W=z1[J<YFRa6cR:jRa$Eef-]~K^oRJDrhj",");W6frGK>wO{tkHrG)S,1{L*^i'5Tg$K!w-spr1"],
  w 48 50 0 940002 940263 100 7470 ["3MGQ#B8'{4EfR&W-,vSbU7YJEIuK0Jdo'%_tN?E>*X;VGACgOIPOZmJ(JIo'v^MF","y7NddXvq%:hd9;.7MU7!!UPJE/v~NH^wPPE;,5&}I!jk:li.5rY9s6-45LV^IW?v","h,I'L{&:-Y9?S4QY5:t6fcv'qQag#uncO)]7}edZo&Kr$$Y+u2+h`_Xems@Gc'1@","~1q:FBT'XO;i+Kw{tfOhm&OH`VC2MyZtwjk;YvYcuXW=I]wm'&"],
  w 48 50 100 940264 940704 100 6702 ["/|$ccEy4K<*sLk*3IYiJ8&{8$7JmFI^Chf{p##gNZIS??O%^@!PsB0oIcV3i]N]C",">z/QA*qe0j(p^{h7k(Zq77)(B^]92h^s<'`3$oPLE8>%r-}N<8BN#PDM>iQ`Nn@r","!#NZO'jIT^KG~!c~5$B=,)}ZmR>,~Vj3Jx8kg5glfH?pzL/t=-6#4j$Qz)LB3boe","2{tTEAtAL#Voo`N$HchlESY|ly+w6D6mW7R6|JposEs7PlEdZUW*pbgGk}+o^Hx?","D2G;,/re35nUA[a])Hw=a8AzgP)69"]]

private def r48_5 : List (Chunk 48) := [
  w 48 50 200 940705 940900 27 1737 ["C{9?FQGTNF[?{+>YJ3cD*B$~Nnf3d+3/K%s,xa7XpH%.FRJvc9>I[*0TEJ5*ah7a",")y{3x<%~BW6EXnX5R9aeRxKsNO"],
  w 48 49 0 950001 950264 100 7167 ["=DKr'H9_RU!QD3*s0e6Gj0%TM}U{WsJRvB`/(91>3L7:3RXnW'ROs(LK[1O*gWQw","z(dp:<8TB#zs~s%f+@A/5sckwUSzo$~hR6IGP?@~_oi-,!K,IIvJi6?N`%yQ*j1%","26q@:]'W-^&Jzcorsyi(.61A0#,FP+bfWHz;,zq1Uw[C^h[Cy9Flc4rUMT6[)Ppt","H4%K'o!e2+i}_j4&'1,S/.Jv;<=[rhd`BVH&C#pG(`Zc=tYsYL<I{clwl_Z>t/yu","$K`D"],
  w 48 49 100 950265 950709 100 6417 ["C?^&`#SQMDD?+Ug{fIFGK/Lk`IU_cTQNdSloJ]yX=C=kSg~<!ROG!563~2gjd9d0","5Hr:&L.)r[TwMe/,N%^!]z5.qAQ:BxEF[Gpz/W.I2yzri'/[!S/|0&M+UFz)RsY<","K1&~v.@~l:e7elVRVu<>}kVg,*}q7VF9C1|/$uY=13z}Of$M<D9$<x]-sR[moJ*]","[@P!j]|R(<D?U6/0;*&u.646_{Bm[Cf.*vJ0pQaUeh]B9~DbkI+/$3XJD#'eFw<R","'@C2trd~al4inZ(4(6SDCOVhwx?G30%tPiChG0y:mbV+1qaV9d9S=tYU3gYHMeUI","LtC6"],
  w 48 49 200 950710 950899 20 1245 ["'`G4#mbv211,+!TJ5B6p-FulF`N-^hhWZF{xcjrW^Cmljv)N]/renD1;kVsLNd`@","%=?"]]

private def r48_6 : List (Chunk 48) := [
  w 48 48 0 960000 960265 100 6878 ["Ed1gA8J+2Bn)#;)|4HmOop`+^1<U`F458(+LVI]%m(}+7sg7m2aE'w2h9e]s!73>",";@*B9uD{ii?O=Uo(vc_oTRIFL4b=VoM|uI(I1hgT{Mj(wXbv/BqXAlAxlwZ*LzQ2","YN:1sW*d6KYJ<t}k;XLb}CoVQKcn1rUgsg,<dc1,+4o%X~JROM]AsS/.Zkhu@-B`","0Cb{eC>Dv4wAUB$^NfTP']5GO&v8P:c5lffu-VU0d0?>S%#tGv%yac{1Dxlu,|p(","._O}J9>y0]53RJspAPqbz-"],
  w 48 48 100 960266 960769 100 6153 payload18,
  w 48 48 200 960770 960899 14 850 payload11,
  w 48 47 0 970000 970267 100 6560 ["7'7UA4,3/dLXeIJTY|:KSDye3MHbwtRei'c*7W5!_h%rq.k/~N?_jzFf!ld[X*rO","ra*F]FL.=eG|%,wbe)]Va}7dZg^<U(SpQ~9Hp2OWuE1`zQda)ySHkX1;f8/`{d_k","dF=`j>[@='o=,!LJB|t[{%UZXzP582`i0k0P[dxFm<!mG*n+z#~CWT63UNv[n}%z","@QZ7`R$-?IXeZB-WjMJ-8f(nq:spi!p6kdGfPJq8R<nGSz;,d!*D=%7}:2(<hPBq","#$UM7J6,'>p@4oF/@Kw9+MMgNmD{8[U/~IS;]eN`p2g!K[W"]]

private def r48_7 : List (Chunk 48) := [
  w 48 47 100 970268 970833 100 5911 payload26,
  w 48 47 200 970834 970898 6 360 ["''*<pfK*jt/{_+Rwy>&v"],
  w 48 46 0 980000 980269 100 6255 ["}=|dDR6(zWyF`G1EvsO41,*3AWoTD<G?DI(EaW%k!'%J::fDi%'/(1QC4.{-AWM/","P5nV8v!bl${*r7~Kn{)}#ebcMW3Q0tktLa;v|&3GaQZ;KN4VN-.mzGUy>vu{J2kG","cgV%s]uiJrOUa[P,?rl&lC]L>9]#k3Sk=fh}hTTiyWn507c<f.X!rU>ZHg}xaKOp","(,fd2=wN~#0,Om.L:nV^M`.95>(nq$?uyp36@Wp~k5!%m8k7^{U-((Bt;+w!f!8e","!(1zSfpUoQyaapYwCGjbQVP*H>OvITU{V]+*]yOIdJC~npo._vsHJGO5oo)TP_ec","$5*i!Q"],
  w 48 46 100 980270 980898 99 5651 payload27]

private def r48_8 : List (Chunk 48) := [
  w 48 45 0 990000 990271 100 5966 ["I|N:(e0tuyDubopejAU~!5_7dV2EC.,P}KT2Ub:E}~M2eJz_Y2X.#I~t3`]2J0/'","-7{0$qe>`O;wmWUCv*+uigy(cJ{KiyABes>plm!>i98)CZHKg9+i9Od4]:WdY't|","C$Q}5LOLGCvAc7-(|(-&Jm+@As()LYsf_Id6n/KE.>7SvhF>N@K$Jg60:-P)f3{p","VcS7?bRrDDH,K5PN('p/X8xseewACJg~n.-s@]fu|5&Tv]X&@xTYR:orv5,vX6/s","A4AzXw!bNijd5L:sMjTU>_IQ_u-#k;5PX?`PEo.'gV-Fw7bhOly|p^1?G6)h[2fR","#4].Nq_B<Cq,2s'mW(`Swc7L1r)$S-/dD"],
  w 48 45 100 990272 990897 91 5017 payload9,
  w 48 44 0 1000000 1000320 100 5699 ["ezxzf_,e,tc]O>Gxo;':+L=T7]7v8hEN6_ooOo}%_?V'<Dn~js=4[9`N2{&RRy?h","OEgpe.G=y|B9fU,zac/qu$?$L,gHwJ@DJl&vx5xFyEaZklvkQbzK5CQrmq9w]'9z","p@5u(01PRUs0FT@i0A`7G+[IQdg-5uq~tsN{V=y/|pLls=AnU#S@+b^SicI3]nKd","7Zy+yb-$#5Y!=0C$Wdik>)%jleHx[{}5-)/bJ5sH_pMiDBT=rL/v&S_Kn3cB^PF$","J&?52a@'nilKo3_Z^<CFNr8I<j,Mw4dnF{*Z0BR%u+WCBW3U_|>]ocCkLq2}V^N2",")#'aI_(UXg7X6m$z5Z]%@H<~H_4_q-);w:*hS_KN(=%Q{Xe{hQAyv!!clA@D"],
  w 48 44 100 1000321 1000897 84 4473 payload7]

private def r48_9 : List (Chunk 48) := [
  w 48 43 0 1010000 1010323 100 5452 ["68i#{[$I9+>O!pq/`yUV$lPzGY)|Y]lko{m(gex?}c+2.}S@n~$wZKoWgW/|xn}m","UFbFYcL+r!El0iREg4-!iq>l}ZWM6QXJUE<t_.xi{P?U68<l733BJK5W?1Wf[|TQ","C3%'PvJV-}LE6[Pj`+FHIofMdxMMJ=p`9t<rDNW]>~$cdRxm&b6D#z=n]<Y5$b^W","J0rOD1)]I~@:ycd3[m?tuBkBb#b~-;Evw']T?g[lBG`[>~e55MUCO}x}0Tu:+E*{","U@GTl1nY>RZ2)hqGB|z4y|!W'N%Gj'AvpC%>BK@7|GpQPZ}KH)Jho6[4vZ](pWbo","XSNBxAd<07;'%0hamU;)Jn;#+>4eV}pHy-=7-e]b*iANK+{!t;`eZqrC9:SFE&#l","$p5<WO{2ecbf-Nsl9tW'G<mO/pKg"],
  w 48 43 100 1010324 1010896 76 3905 payload2,
  w 48 42 0 1020000 1020325 100 5213 ["cr0t7@!'!XR-.>K:kpW1HNp`ll.#!d=#bax1ym(/|hLgL*nPjxt^|0Zyi;%*@X|X","uZEH&$0*Gw[VY)d#BH;_JSa}%>Y>a5,F0upm9LN,,[|Y**1=j#fVtGy)D`.DhVI%","QG2p{A,ZBD@vM&TQ!QRn+GXSIyTxx0L%[ZvZ4~$)PG(0}BV(qdC~>k`48lY'3IcZ","yUlkTZ9|-PY'A]M@Ym{uGHm~i*jUl]kH_%?:[C?2uI)(u.owmQNg3]!P^o*R^<rz","LC8Ors9I5J}T-J&p%cw}D]nCk`nAk#t%2i{njv^-Zh2]H~{+dLa=?XNMU5#J.XR&","RN*#3pHEh'Ql-lS[6v+7N[#R8jKW@0ZxlnA%5L&_POh1+;</pGmiC`:Yi5=}PNp^","%7ttl3[jxl=;*U?a7duKV8t-5#*2`{ttGBpDXhba}&4Yt_@2sE]EUeCL=RL@v"],
  w 48 42 100 1020326 1020896 69 3429 payload10]

private def r48_10 : List (Chunk 48) := [
  w 48 41 0 1030000 1030328 100 4978 ["NON8^Nauy$sTD.'#$I13YNo@L#Ec8Ol<X)6C,C$Q.y/C$Md?4l$bveVi)rd7bSb@","ysak{eFNq`xm4ob&dFW@.uViupFt_ae:e1~nfwi9}1?7:y+YX*4TFl<BK9&-:Ltf","cE'LQ'6)fh>V.cO4!HR~LTZBu7)/_Rv=-24r;Sk_#'|,izo[MP#s4XGSP61<c%ee","SHu79[<<Mb8-og7BW=c>e|LxDKj3C>*AHl@z[fB5f5f{$T9EC{]CA#q_5_|jMz5{","|?!ChqU=bj1+/A=K29mb@7~Zk-8*@}<oU&JKF,`9H.7;#P2yX-H?OFs=q1Q+g$H0","Mq.GD1aGw9?B&;(d'dfMcB4!xxHXZUs8Q>jux6W%-&8&eZ+RP)0dEON.vdAl;O,!","d]59E@f:QgFpw=$!h%7w?U'63A3mtGP4PjY5@t1lcKPWsL;a-almZvFEe;O^;,j%","(B1=KDc@|>:jr[2"],
  w 48 41 100 1030329 1030833 61 2937 payload6,
  w 48 40 0 1040000 1040330 100 4749 ["<xT4-b>&XhSU,0|wFjpxh2UGO>?Y$e}Yw}!Ca#WMtr|!66/fb_P~,0li1o,iW0Oi","]9`kh`Q|!5AIiKfw?m_sFE8MwbGq+[zN1b6en'*IxP>^6dV%%^4R:z5/&Lu;E<2b","1#`4/ZlEFJZ7+.R:bO1eptBKBt!+?d:+&hLke3ME&y2VZo69s%{,Y])hW~PB'jDi","nPxA(5qLvUHSaD|3K2,-F+VczlL:A97Hd/,`;mmNt@l%6=g{J.`!u7l@:g?L::'v","C^0[-`uyZ7}2#5Qik^vbH?8d^zg;Hm}.QDTB5Q})l<{+@'}U+E3D1_oQQ+E/:3dv","j}m{koLYOtxj17e&ItYt/$kohXIg@YI)'VNRP]B/6Kh:KpF,'D2HE/HOia'+bK])","hqRLv?m]_EcETU/85_K_q'$TKEp+/[)5x(<'9|*-a4t|o0A7g&7'A1A2l/eSNYn/","z1^eIOz#.H9Jf1r,.wt]1=GL%KGECnBD"],
  w 48 40 100 1040331 1040832 54 2527 payload19]

private def r48_11 : List (Chunk 48) := [
  w 48 39 0 1050000 1050384 100 4536 ["6qJC]$gnsJ]o<xa,47jvb]QF&>JB$_D2;xaj(~#F:5TK9g)Z@.%0I2+bL9[rtbJ$","9MD5<4Vxz]9dIxnWx-5HL,coIdb?&(EwYKHl2@2891)b/5&)Rd&;gAAk.XW]0?iq","zy*HtG|VW7pKHd07FL-&<Kjo7?R#r8ns99GBO-OLqa-d.JOFHrILZ!}|m_W/~O/H","zPY/3{,*=Q!w`+f?|A7;KIM](bEbDIp&no}z7[QS#u!L}_Hrl%xO<oMIw8j~}T1W","E6`Ciy&2aW:.?(=?Coe[#-4I)5tm7imy(X1P>Ug]zb,']YLm}~1r!kh:23g5~zKf","EqOAx!SbQryipwK`X0X3`+T{_^oxS>[iB-cS]-#r$f*],^F(/U8XgQopCkd!.u6A","p',dVA1}fO9h^!W[4#}w)18?jNXw=A,c{R5DWu*Ap`S'~W#;|RuaNVq@=EBJDYBj","=DO;CDx~rIv@p!f?M$-`Ro$>MI8)2aM%,oy}?QM-o$F"],
  w 48 39 100 1050385 1050832 47 2140 payload28,
  w 48 38 0 1060000 1060387 100 4328 ["gikBsMNW!He.Z[>1O).[NOwD]~C9}:R|qZWenysZ:ayQa}NT)e3a7ZeF,DYY~1N4","u8BaV~&Q6t@gOh/JYWj'1n@mYfBdzU+cCwl!Kp:de3Z2$VAan-OK@G!@5JLE2It>","KY7`]oi'`2+]U>p{x:wo{dFNOSex>*tqi]m-uq5]~B`%e8S7K,l_4N|~-r|JBr+{","&SZSxQ?xmD0tiWL[fT0p[rnKpqV*%%0b7i+u_Y_v%4z/<a2-`M/)#DG&ZXB3)(+B","ZWcVvBKgb{1E^PFjT2(3jAK?:hb[TTm)E.Ko_}0J$?xAI,z864_Nsy@J&'36et&'","?KF8z:{zOln*i*kce]L:3pPmU}{.$z'9W4V>dJq|Fs/B0zU@l,y|)'AqSaI`+vPT","}H'nF1DWTRuLjDx2Qi;``?ff5kWlr*,@$g97G{}Hd>qJifhj6YwLZ56[(b?zq3g.","#Rx,Zpj8R'?bp>7a7Zf(]<.P#ohw4wIi4.wQy,*3`2^.2#|c"],
  w 48 38 100 1060388 1060769 40 1775 payload17]

private def r48_12 : List (Chunk 48) := [
  w 48 37 0 1070000 1070390 100 4133 [")sTu)peiNE..{IMC1)kn.jDv[QM-tx[5+6>1<-`8@MWJC$:)KzF<EP*gl+N>l]}}","Kqs@c,<O])TF_wM/{3lQZQ!8v,Cf%JG-qsw38n0Cf.ZbV9@Zqi/6<ihmL:f<hb[:",".%~GHJ@kn-3By/cd&gVg.jEJ>3/&Pr'~TLeTt_Ml8l|[GdYemmJPMPrwC$eggkAc","YXm=!1?C@G^i<IkU,u~z5Fao.VSTaLO5OC0t5}7-n{0j^L7!|]2-PKB:TVR]$Ofv","$2o4mQ?:z0[TIstm%P2|OM}2_NLO(@U$1u3}}4a6sZe#!94J,Yoy.$J%olj;caUd","j9A(!/+XOgg10pP<7e&X^i-xrLWxH2*7M&[F/|B~AOm@>9~NjkY5WC:f;'E&ThK|","^D,BD|Bf|b_:wZUJ,Y./,GNG#d1rIQ]^8oSjS`Hb*Z^^J#KA4N*+_k]DcY'l~opK","J/;'G;T_~(r+cM@(v48fs=obS=!{0+Y#Qffk}tN}GmP7i^.IMJjElG4,"],
  w 48 37 100 1070391 1070768 33 1433 payload22,
  w 48 36 0 1080000 1080393 100 3952 ["pwIuf,1:sFm2.BuIoi@4[V&<Mo5tmwD4F4b9sJoy-5vuE`2Tg+e,:hJ<1G#%E]O(","KG5(9yF`RfC?-OtxUkoZ&CN`g*'N@dKL?zw^oWJeNpUL4DZnGyRd'gNg`MUswD8B","%li>d#e$E<$|U[Lq`_}a/Rn/->*yhFaK;?TM{s9L?21eW27HaM-yrhmk-@>ml0x~","z~(m.-<]L)Y+J'tS^-``Z^9:<4|z,^JD$`y$Q??Z0^wdntdxf{N^/f@5lb('}LG]","-383B{ivcqWUv`X985Um`5%*=!5R+.tp{$ZGpZ}Ml,Z6EBm&!?QHZIL4-@YG7:3k",")aQhDy-8#z9hAF[/!kmbc6L1Y),&`56ot%tr=S92QRWQqWqw+eMd.VP9SX;V'lBm","+rID?5g0?YQQ!>4MuS]TYa=R7&KNFj%`mt+J-l|Vq`t1!Mx%13VeEgbn~S37e(3Y","-WaL)43at=vjq:6vQyQz&.2BU3i,EADXO$YJR/@4Nl4sdCI;g?ySB&Y[1-9go>ap"],
  w 48 36 100 1080448 1080768 27 1149 payload1]

private def r48_13 : List (Chunk 48) := [
  w 48 35 0 1090000 1090451 100 3789 ["18B@<Bx>ba`#ph'`A^dS#Xrc6-L:=&6WFY$Rl(/8B&lOL?=;Y]'P]avyf9Q,dPim","k!Vrc_uVGOdmoqC,/[L,}.nJ5QXTB*ot+#;NPZcR0m1djwBO6&vRP0BDSD+k#{bE",":*0hfl+K9cclo|}=hnX<C{f?ksnZ@oS6Vgb)xFnY=2_!@JCLV/U19;Y*D7*g:.4:","FU/ADMC;*sFyr{N-ckTt!,iWW>^)a&(IH$QMXUx]rp*vj-3/4+/0FBoHn$l~^^ut","(|514.O`]Q[uW(jOF.[T~<5$&QDk9)B`2/IT%|81{13%d3lGkJo)a|%1|y:d,a4%","I48GN!p$kMW(v)gs}S`'zO$C`;Ee[UASpYFQii}E^|;b?/pn#w(Y_EUK^OunOzhk","FfWDmBzX+<RWso:5fQ-&z='y&Bwjn>2{be08yI_xrX0_+|sh!a_mLRDwFp9.x^zX","0YjRCS)=1sSTZ[8e=O/C=b([^[HMNNUcBu93br3R%+{[[czj^Hv(boK&q4oG0{',","V"],
  w 48 35 100 1090452 1090705 20 833 payload3,
  w 48 34 0 1100000 1100454 100 3638 ["=62u.Y-kV4{XiC5/Y-UVh4)me?X3+u<FYn.CNM:?Z9%$$LP)5Zc+ZflHb-iGl@ty","&kIEg`cb0vV+dfesf#2gqP`]8^!4Yq:VlAdOO`zEJTWi|o<b6xx03<w~6EJ-'L8S","dgwll06c-EJ0H2f1)2<MMFVKOyaZp'WN)pfq`^~TCuT[z~V6i7S|G!t8?2C-A=5D","fcywy/()yVe^X,9MT!&mG@U1Ze2:mn`(8>b)>J>Em5z5[|GF),n!uG:*H[v~/`)Z","N0M%?aN75vg[ZnSh^w<0tp`+>Fl7(FH<srhIx#WLQa5EQMo~BJ8?*w-uLP`YPO&(","Nq+=674K>rvyVZ)=SU}s%uDdDf5C`YD_r3yYr2D#L_$3(K>[C8_UNU8XQ9|hn1hq","$P]G>Q1h$Y3?yl@{t@sJs=DlU|=iecNo(U%5-#ejWDA8nX/GRw?S@&D'X:ba&CJQ","(QO{-vuDrY!9AnluL4,oJ3MaP_g*~l/E,rYhgV)LIN;Uz}WZow^6;xE?p:(:A"],
  w 48 34 100 1100512 1100704 14 573 payload14]

private def r48_14 : List (Chunk 48) := [
  w 48 33 0 1110000 1110515 100 3506 ["KO=]10Z&ol1(&QZbB@d%96bC3kcOYz0kQ#PgX0:vlB|T9#r0v9,3$rpnfi[:]u{o","k_NHH6iXfS)rn$UoFd.!/%kF]Ig8DievaLNd#8&Rn0.bwmJt0&bAbBfTw!(_4?!;","GNsAzV|]AbvECn?#V>:m>92Ke<c9|LLUcap*B^XG9J2:g;(pCf/yFh+E~;?&^x#J","Z}>+)R`{bd4e@L0Qa%DT(fp]p/_ov('[..SUbv#/yA[%<qi/+#xJcD|ffrC)s$F[","K!{?0^/m,C,in@To*!A]o)l=1|@:no~6kN=6K@U-o3oSMzwxs*='(Bn2IS-%R:5x","0ecQP;X[[e]FR~BUeL0hoCYk?(5K-.ft>ZuF0CEoAm$Vnq'c@h~KLJ*%X/'V^^W=","o=?xr^t&<*uB'O.yw-hi^Wuy.lGQ2=2hp/rHX58@nU4q63y?15's+^DgC%&0(0U_",")+xET2PKOp[+/M&=dbU[14}r*]-Pzr6L}rYe}]V>YM{~9?Uc1J:<4b#w0=*P8/lR",";*o"],
  w 48 33 100 1110516 1110704 8 323 payload4,
  w 48 32 0 1120000 1120578 100 3388 ["U,VTFeZ^h4H!PjUH0%Tn7O2Xg%3w8E;@@Kw`cWF+/uO||I%83'6]{S.9PV49XJhc","{1:_`$T1l|F`d60)@K{R`+mL3=6wSxXc8Sh^-M8Fo-$]M'kedFenRmlxjD~)E(&H","ER;$*gVDL|CAYrK4Q:-V^RS~}6gy0u(`eF!s+f~|v(;i>;e-:&bw@#keO3^rqj_B","q]i.>B&!owEC<]7hSeDa!jPCe~:&@JF?|!vU]&:<:*H9H3Q@l}g|,=g6%H|eoNP1","'PQ+{.dK6iY;@;q`LZ^XjfoF{h!VB,'.`Zo<<i.@odpj0IN}s@U`h,`4C}g}:M9I","[RrV1WKSb)i_y?70IpMZSI.1I[_D!1jP&i7J$pr,pIkf&yQ37kuGIEDH0W97p(3_","VQ@^%KPh/VVA(s`C1$e8e^7FM*ZoAP2{J>BzO<|J:Y7.L/dQ?[y3p]K#mabFLng7","jmLDGi.=ImsplR|{<8$TzKOM[+$_Q`=!2649]b'^&EHq)^tEj'8m?3Aln;$NDTW;","3[y"],
  w 48 32 100 1120640 1120641 2 80 ["#i2GG<Je"]]

private def r48_15 : List (Chunk 48) := [
  w 48 31 0 1130000 1130640 96 3134 ["2yNT?b%v)HDFUzPT%:uo.:_AhCo;>v#L&T5/`-<#ExzjN$bx/{?19AH@cIwoLQ>/",".KKsL<mQc/R^!*UQv[HI%ld$F5x%qB9nV$9%0SNYUoE,;JxA)}*I<Mk&!~o`gL(^","z?0nV6yF>Y}Pb8?fkezIaQ.uwYj~+5dC?3E+&g?n1^]9*RM1Y#&n;H|eAwKBL]GU","fyygFR$0sa>}~SA*qcCqh9D+WSb[G6lWF/N/eT0=WyH`ETO[GqT:l*;9Z?]5c`^y","![V@0WUvY7hPPr2&G-;[+tIb;q{&ixQd1||ap0pK%MbxkH$Sb$bJ{NfeF~hA]TzS","x].Zs)re1Hp(Y`jaiG(r*A#5/Tjm`@R@y4e@'(1>hrBvm#a>qzt#`u;>6;*a!A>@","k?hZr<3']X-/qJ3I&mlA}rqVYF^9[KMcu>+8YY+2hL#U<FGnIkaLvGy<qXm{!4fo","e}vO)E}4S|,4:Q|w:~K=,E;O6MjDk4_D9(U2`4qS:H/H!8k,b_"],
  w 48 30 0 1140000 1140640 91 2855 ["7,eE.Ab<Um33Ne2.W5+lOGu@#e5dK)w9]eDb>F)06]H',1KIC)xD@,-Z>5|_7;V-","_O?tkJh3wJA}5|eF'nlxYH^P]v.&~X5z)Ku<E@s?KYja>rTU.)~K@Zt?%E3C`j;?","crMPt.a-d~qiP}8b^vYuZ#-s>Ux+(+7Xgk$7+xm5Fv8%'d7.tLVI:([{5bwXX|;L","8&(zSx>s~yFd`9t9cO0&JxjTg;/(h^9:neT[31Y]Qj>O%#S,HTn264G8-PK9<Up8","!CvnYydh!^i-1Ki)5fs(|m21_UA2uCX$@/>vFf(ss>Pl>[3'fv(%J5<+qfcDV;[g","19S8>?llJ)e<cC#Z)Q.?sZRA;,+bRtYR]0VjFj;Tmhl<WH;{n#5OlQ$ZD`{g`[-;","0C<=m:jjR+I9R:q)]$>7VF2e,`Z:2I!(:4Aw}[>nX+ztP,LdODorF8h#V}'cZa_f","(Dx6[k:KI1wrl4q,vhYn0"],
  w 48 29 0 1150000 1150577 85 2562 ["=&xb159!Zo,/^.c(lTnaSj$k-bH/TS[bPm/>^q$teLne7ndA=:W8|15bZ@wH^Ao.","$;?n%G$ws#LJmYS}};p1KMy_%[_SxBxQh~gp6D=Ir?4&MO[#HTXC.~S&;>buZ^6.",".Zu.kih(JnX>i+]!/E^3B{A8}8'N56x7~yt3AbFi%#Zgj{A7~[r:7!zQuy~.[-b3","AoAPeH4X<G}Hrqyu5~O.J{o:?d@iTO0:^ZyP_^XVU]2/RQa'gzXS)AOV$_O$@B||","@H0=mL(^?%Mnr<*DxITx'tc;dyQ;Ak>(Xrl@AJ4cq$M[GTIUb_>T<|!5qiSS~29W","&jZCX@/LL9c2@&h#ky,jW2rdQ5ql.(J*434B)4MZ&@UK]m)[QRa#(Fx[4^lKwQX]","#H25A!;1EI_/Rn<{s+){@>ye:AnlI0?7z(Z+E.6|#kO;^DB8_7I,eP2wj_+}tc"],
  w 48 28 0 1160000 1160576 80 2317 ["DWhd(Ey3{>e6so^;DH{P$S~0,A~.@$Cl3d@VB$M771&j;Ro@kimr7Ai?BixT@Ne6","Edep;^[1n;;'|1-%Cj)ZOVpW%/h`3aflzz,Jk#@_5OSGO>s<UANf~Od#7ehY7C9z","wrNR?n?p'y@(q@[)H#x0tcB9Wd:Bu8O9PAi$aIp'*~OGFJ8.vK97|hCwg)^#-V;#","MiG'DNy:l1.S|'QO@)D;_znVy*OD}F[75a4yoWKXEo`zSC<Ni3f:7fh)Z|x=%29~","lWXIctzL2lCFrG:IYu{NJ{THjrj%0.!iqZHkm-4=kQ`8|O*43RI-.Om'T=YEJ**[","'q_J{S})@{b7*)*^2k24fl(Rp$v^AU^SzWEU+~.6@4[R{2;Mq1:_I_Ro`FNnOFH5",">+xCrTq}52YH8{YAld&@AzdWeh+F9*qT@CyDEz3;"]]

private def r48_16 : List (Chunk 48) := [
  w 48 27 0 1170000 1170576 75 2090 ["jl@kZ%<[^P()#S.%{Fr]%*=N+whpwX!mCUX.~yG'`9P4&,CDj7EbarW(ChK};:F~","T]2T9^@~&%;&%eqTQe5_Z_RAWO{&pU/:_v2[6l6SRkl(k<cb3d`n-rW;-.kwqjat","vzo{c@lOtD*SfPBbPNTN2K(N2s}o}1yr.)lU)J^HU-0|)y0uVh8.&<eP'C7MKaSE","et`>b<W2OBh$5C$:I,vbFsR:;S=cf~PHo_S7UZ3&/G;hlw*+4EDm(l@pv>oUu^Vh","XI2Ycd)*6D&_DEeOE6#UDebLN??)3*Y>Qm9)y-4a~2{[i9]lO[/fG,-1M*`GD|SR","dhyp/&59{e@b9MH7*rC9#*m5@;Ck+K'v@,SKsNgc4c|>5G4vE95kx5elu|/yo>9p","%h`&s+^?)p+L0HTgx3"],
  w 48 26 0 1180000 1180513 70 1870 ["?'{@_aDOAX|R:pr|gMv?4P;{hMUW&Vru(=Y4{Q_o$M,Ru8mrw0bR{(`N{n+=Sk{F","^s&0u)VPMWXTyq+e;x@)YZc1AQ09A/:T/@Pv7>}3*fO^rnz5pXKL-3nsyWNi-Ths","D$?!W6CSwSiF7TDJvD9GK,$O/gU&`M>Hjb~l(EUaI)afOi,C/cc!0g}jD/{nqqwP","`F:#>^?NUr9b:k_!z'Wz$Dk<1WO+l<@=nArLMg*sW:aPXy_DJ{uS/1(Ek&sm*]80","q5*;5r'$%Cf&8eq&Styx^sqik*3mO5JR8!|b%5K3Ee-d_%r5dtDB^DfI(84k0H2$","-X^?2|.eJHQX'+YD{945Y{q~{g@:)o.k:AD{*d$+vx5)%MaZ%}7j;Xf,I?^,h"],
  w 48 25 0 1190000 1190512 65 1665 ["W4sQct|nAww?-3v&X!D'y:9<Eb}x/wg+o-*PJO8v`<!Ae-d)}yHEfqkL~>lZ'j'*","_(qQeNfw%MB&H@BYmJ|[:m6X3{lPR3osd>`5[Caq^7jY1uBAXcYqi(8H5s-t=JN6","eDo`&]bi+x1P~b`#8X&TQFlgq4ec>QEE%~6hN+$B!Y0pG=YFkFb^#$>Y;dq{B'qP",":7F*^CPSN;P+Kp$,hWITRDOP%^Ol^PA2Z%+I;1Zc?AbDX=KkK`ik66JQi7YNbh&r","I('dUr|q$A~xXp8PnN.=~j%483*J=>cy_.F6UYeYss{2/6@h=)MCl@O)~EY7$+NV","$PEQ3&..(s73X^qW'vFHE~<{oA<~H;UffN|>iqWI"],
  w 48 24 0 1200000 1200512 61 1496 ["(Y>r6kY5r![Hm#rR;OZTPf%+O[<'Buq`BUU'CL+5XHu3[~h*1JWxzo#4}>?4FzRw","+6oP%GL?lh#(::$de`)#6~|R/^C!u-~uspo%#6kI9eO##]i=5Sw<bm!gdV=}abj~","p=]5R]L'A6vdz*HD>GEF~WA-`q?d^#0B4zp?5tJwvHSfO)KvBTrscMeeI{9#Mpy3","|GH*YF@?UgW~*01A1c8hoUxPU|![lW_?V2J[8Q;X1t_a`dFfeYi@tVf'|#2U#P{d","$@A4*Qlbk2!O#+HyA%8D40Op3#h25bA/4Ayp&-[9B}p5i-vWT%7AjCyrLI@PRV`S","1sjSFvP0M8==Z`hkUj|{s"]]

private def r48_17 : List (Chunk 48) := [
  w 48 23 0 1210000 1210449 56 1310 ["6gbve+#jsb`WaD1#$-$*<xO7~/z7O;f3(egeWH4Brbxd5vs9bY?u!0?VMr.e1$G{","Pv<<iZVNKk+qa&]HMr1qr=@]7U_ttFg'a:?r5d}>]nso]3#eg3-PlNOiQDV>s`6G","zO.]6OI=GEs@e~{O;m_fVQDcHZx%f3]HQ*EnhK$j?tl}Y<~{Ll!}~!>TT8z}C(T;","QxOCS-wic::4%C/lOS&|mdooB=R.F!bePBB6.GD6./F75=<|XsUtm<j097:c8kZ?","x}DF!C.s8GoMT!LT2Y[otyn1FpvlUA#TiGND0GNWAoRgf9P{|n,tzp5^$1n}Y`$H","#"],
  w 48 22 0 1220000 1220448 52 1158 ["!asVxktm<'r*s(XGibIof$G~:Q'RHom*>b]A/l-u]Hr/U4^3S4G0D'0-0Cd&QQh*","fAtqs!E+a$;Yffj9Fms^2CaK0eDqfLM*m4`7g/9SxC$n5L%MuL{/,7UGoKqm!c?z","QN?y%5Q'h|{Su_]nniR]cE>I#5&99YJz,S$?8jd(.1iQ{>Mh&/1(zC#w{+7g@8O=","djQ+jeSj6~[.?b,@|vA,+Bn~xWv?RD_:{)JA(SRE(dPPQWW+cwQ5ir$m-UCo<{>8","/DU:Ys^)poYV[m`}>>#3jE#ByTi2fh!FPy7vN]YYKL^+"],
  w 48 21 0 1230000 1230448 48 1018 ["SI1vx)SW_1-:+O'_3Z!|1Eb@l)I9{C5Koi]F%g%n#MFlvHT$^CI.5m^o%Q|Krw^r","{NNqk'ebYz(!<fk&SG#p<USK3<#XIZrfmg0[T`_Ke<1XR;Y}e>?zPoFPcCRF5;`g","QXu&}v49LFyj6=.[trSyqkv-~xN)~Q=0D#Uz}!2&9N}!g6(T!|n1=@tz<_]G(}>y",",;-bv:TvE$fUf:OL:.3r05^AFFJa_B;-Yk^')7eNiK*v4+$gn'&s}nW]/iohfW]|","*>sT*BUu,<Yko^,Miy~8(F9%"],
  w 48 20 0 1240000 1240385 44 882 ["{?.ml!Nz3C.Ze0bf/0asE9`V(yaW4`i&v31gt]ITc|<w<z(W0W)Crx,U{T=,OGVf","<ChoBs##AV|J/1<~XdTd[e(ee}svIK-J;>$/MlhpK,`JtJ-`D;:3#i$h8KIR@6ZR","#<-XYMQ;W0VId*3wVBDy{)_mm=3W'4Q+Jj19rb'p4$.*K}<s/aKjaV51ecAmQHZ>","Ih,WN1ydzV'TBv`m@!wy0ww-Q&|efi,afzKVy?oxmYO4Q6[B6GHy43=mE7Socbh~","#qiH"]]

private def r48_18 : List (Chunk 48) := [
  w 48 19 0 1250000 1250384 40 758 ["t~zo@)R}C3uwKA!j9(8Pa?h|WHck&<E7xAP+7m.kfI^QUV2!]n>@`8W}}tp'<j_&","d@^U<{59pxq,jXY:^`y6yfdsB>X_mt3;HmKMhPz1ZfduCPOb9=D[e=ZFL^A*!xfb","~kLz|,wvR[I2WDI)#jBBt}Kr1#TR=,{vXRU;>/,N}KV!({o:K#'eZTC1mtr`EY5`","UB/#vE.>akIHuhL-.9|TC1PQbW>KfJxw2x@>@quKiPpRRIR"],
  w 48 18 0 1260000 1260384 37 661 ["}:aE'/wLSkMODi`H9+4-0w#YdEM+snvDwe)r/@3maR]F3H:6`Nl/Fom_cK#k(5^A","TDa-u.C9;2*bcnZ$@>_>1@PY:V@e/6L.E_Ao*HV5}R[q=788Ke#d)qb2zCu_#y!{","xYMITTJAI*{p-<1qYy2D#g$!O,q#ybzVo~RMLjQ!YO-'jdyYTAhgoA:s:dgIENdi","%57%Q}Wd%gO8;r8Gaov|>)Et"],
  w 48 17 0 1270000 1270321 33 552 ["D2#G8^X]=DLN0kCSJ/WVeKHiP6TCJ=luWKh+NPtFy}}7nx.r.hq^B^.t>dCXcfbR","__Z7lR?6wE_76p|p>eP`D>iRX,t&0]V=S:FmLE#Z)JE`51RAj[>a0gqe+Sc^NG/b","3cZjQVClAraf+UaOPu^Kkm.S.7V5Q;J1IxM[TJKCe[ZH1:mw8hMRStCGGKG}mt9<","155"],
  w 48 16 0 1280000 1280320 30 468 ["kETk&}Ql(`Tx#r)NZ5GX{,-Y|A}u4QELsf}eR%pyFu`+&;0sR+RgKAWTMY*@]*-2","Z7D2^A.^F^%*InEs3LS[dZDl1!9F9>pEY0W^6=V[HX{<w}1iNAIJak=a3mZBU~U)",";L:{`;]we.{F:/9dI2j@+=`HA]HopeTeTOFyGNUja*$I~}Qw"]]

private def r48_19 : List (Chunk 48) := [
  w 48 15 0 1290000 1290320 27 393 ["&C~i%^+sl8Pqd))K~79O%8wb;'C9ZP1`56[qTGHE0<,SE{sb'}:3nd`cBlDw%,q>","r+<9A?iFOK+r!1wKR4lCPwCv4;Uu&L775^&a$whs%(kl4`7+`5/u#o1ZQf=%@4fq","#YXItUJ~X+lMg'CxrokcyVM?L}/=2"],
  w 48 14 0 1300000 1300257 24 321 [">[LPrWLq7Ri|FMKp4lBC?Usu}Y--_oMW[WX;=BnvrMb)an-y!SQMOt.%]gpM(wtJ","5`tdvRA)nxn]YeU5md*18>P^]Uaq`Us|wrmBND&4p):Vl>*<w$Z9}Wurng/8KK<*","I=Or)D}d!"],
  w 48 13 0 1310000 1310256 21 258 ["k+9SCeul-CaXDf9#!^z8UNQ8%wNPuC.Xr1Grx#/.MFDc,<K=Z(T8~_qOdiJ>50YC","Lt=z[Jpk#-%fQX;B't=kq1~ST6')AQq@gdB]Fzuuc~/W_&4#z'039MCu'pD"],
  w 48 12 0 1320000 1320256 19 213 ["=T#t7(]kx++8f5=<t#}06wNQv%^9E{!<M=EPFb=0!hi'*k!nD.b%w&1l9N`6@S6f","#B_xp-C%I]l[9tYl=5..)LSg8_]W{jccqczN:|u4%x=r"]]

private def r48_20 : List (Chunk 48) := [
  w 48 11 0 1330000 1330193 16 161 ["!eosL++.T0zc`n`o?S(if[/s2!`ZPepP!<{~Sd_>[f2s4OC/gFE,9=tCqPio*L</","#[EjjQ$sbd&H:J*FAM8<vHLPa9a+nTJi"],
  w 48 10 0 1340000 1340192 14 125 ["%5?ggPc&1NR7zYIydg4PQp$m/7K*k2g9)*^j$<=JW/SApUf7'65r6|fy77f}9${&",",Q`y^Mp'N=u,&%a`G'F"],
  w 48 9 0 1350000 1350192 12 95 [".N$@rD]=Fu)J0;c.b&c4Tf#j!CemT+5<=BU]RYaohgdmG&}~u1-M2UCQYQ4}JkoV","$(]E$I;E"],
  w 48 8 0 1360000 1360129 10 67 ["ON1e5G00~SKsUQ/l+}(jv)b?{5#*ZLy#!o+o*Z}Q;!n!{rN&p3~!|>&:$J=s"]]

private def r48_21 : List (Chunk 48) := [
  w 48 7 0 1370000 1370128 8 45 ["'|IKb1F85)F1mwN}~o}a.22t%iL|Sp[cdvy35!U}/#Y(51jFx$D;-#"],
  w 48 6 0 1380000 1380128 7 32 ["#VF8=uoFIq%o>.*#yU4@_f3dGtj0zu$(7BR_K^#&n1"],
  w 48 5 0 1390000 1390065 5 17 ["#V-KJZ6wtW?Jc#hI0LyT=y-s@[/z:HYc7"],
  w 48 4 0 1400000 1400064 4 9 ["&tlGD(4>672=hSUC6b!?`7'J"]]

private def r48_22 : List (Chunk 48) := [
  w 48 3 0 1410000 1410064 3 4 ["%F93Ff_+z_7Ax2*s;*"],
  w 48 2 0 1420000 1420001 2 0 [".yP@pG6r|9"],
  w 48 1 0 1430000 1430000 1 0 ["<?UB{F"],
  w 48 0 0 1440000 1440000 1 0 ["-6dH"]]
private def chunks48:List (Chunk 48):=r48_0 ++ r48_1 ++ r48_2 ++ r48_3 ++ r48_4 ++ r48_5 ++ r48_6 ++ r48_7 ++ r48_8 ++ r48_9 ++ r48_10 ++ r48_11 ++ r48_12 ++ r48_13 ++ r48_14 ++ r48_15 ++ r48_16 ++ r48_17 ++ r48_18 ++ r48_19 ++ r48_20 ++ r48_21 ++ r48_22
def rows48:=rowsFrom chunks48

theorem good48 : ∀ r ∈ rows48,good 48 r=true:=rowsFrom_good chunks48

theorem sorted48 : rows48.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks48 0 (by decide +kernel)).1

theorem mass48 (i : Fin 57) :
    bandCount 48 (i.val:ℤ) 56 14≤(rows48.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks48).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 48 (j:ℤ) 56 14≤mass j chunks48))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total48 : (rows48.map (price 48)).sum = 307371 :=
  (total_eq chunks48).trans (by decide +kernel)



private def r49_0 : List (Chunk 49) := [
  w 49 56 0 910007 910265 100 12831 [],
  w 49 56 100 910266 910586 100 11316 [],
  w 49 56 200 910587 910903 58 5448 [],
  w 49 55 0 920006 920263 100 11883 ["*OC1jNndiMH4Ee#N9M76t*=#t)RzvtOC$UCx*}IFYP!3:Kh^,zit)b&@M,){b[y2","3EfS5.*t%Yx0fjP_&!u8&G7UbWSCZKACTF%bc{|aw2g|{B%'_m?QA;*xxNM[AdU}","$<,iI+a@*@pRxRVmo]A_[b,0&t3V)j%Nh{q)"]]

private def r49_1 : List (Chunk 49) := [
  w 49 55 100 920264 920587 100 10230 ["=w,!qN43,DtA^+v13osU{#v5!SJ5PH}NRm{ZRTGj.!_C:bN*}l(&:BKwe]:rQ%-x","5D/*=PJDbo$Lw;=BxScS$0^}*;K!wADRE6Fm#}ip!h{R))iXAhf*6|]OdUYc<n-+","#Nx)'z?L4|^,y!>0A~4QE?f;3W~[>ge=s+G9-GHu+"],
  w 49 55 200 920588 920902 54 4530 [",(_~!xQBt/L](K92yL1fa!'~}a[/poH3FI!I2ir/&]FpV0JBADf<FH%vm7JnssEG","*lYrZ(+lft:wxL5q8&v2H^,PKsa"],
  w 49 54 0 930005 930262 100 10944 ["2xB]^V:=r:@u`q%Dwty1Mn@^?8T2.cjNPT{B<xMx%u+4aF-@8AReV7@k<]6ZX*`>","/{O2guHBd</-Fn[I4y>~wp.R9={{>l~pu:C>CwZvk>t#=k'F=md&P(}>CQe@DeuT","&V(zX4fK=J3+&yp7h[&RqTrp38|CvKnQwGO`psD#,JCQ8~Z"],
  w 49 54 100 930263 930588 100 9146 ["aPjhU-C;Rk7]$*2xDN/{SPfc>hUhD+{L0)<Pd1dP_`oNNH|O(Ywj_b8pfjPRkW@C","u=J$im}JN4M*En6=(pc7WA)a(Y)V|edsMq]@)]m7NC13'hEnb!i!{yW|0[RO1a!k","/X-=Cyt$;Eb1[Z3=[{]vt05DtGN3`_/y,ekN~?9CE6EP=E!Bl=I@7S"]]

private def r49_2 : List (Chunk 49) := [
  w 49 54 200 930589 930902 50 3817 ["km9|ew9}4KI2j(AE;b6o=@2cNh`!|wf5PB?nE7$+BN8wB%HMjg+9<s'H#Km^ODmD","#*JSX@KK<.;-WY=jPum+cr/@zT,]PyHLuCNM0g"],
  w 49 53 0 940004 940261 100 10059 ["qR4yz9iuj*TiVWUR+g(hGpV5<a{dN|j&!=}Ab()[+~3{d?h+B=6n{.bYw<WPj7ec","jzH(H%,Z,n|5r4<BML1./kM^;]T5V:qwYX!dIC6rro|/.+c{r|1~8lgjY*5jIiY]","/k4P%-m-hZzeqyie#3@l.`,^L)G_BM3!h4k3S^9`GLpz}Q)x]Ni+!+q|BwTB,<P{"],
  w 49 53 100 940262 940640 100 8245 ["ryjeHFk7:B/J;ssQdnONr+vA+&;(Fbjsjeh}_5+#YzaQ8RdgG2Kq[>f@N%ZgU73/","oa:6W:_p:!o`:0[[_FUGb)NFfOP5,$0=HS78(xj+2xf5ntXu6l9+08B/'kILDx-c","L'4bTR-kDk]YvYdGf>XO5j%]VgFWy^.)gX_2e[Sm,bG'Jf}|G|.cH[)eUjiT^LUN","'qTUC:J(6p"],
  w 49 53 200 940641 940901 45 3198 ["v$646o7w>(IB$0%xu-$y>gsTLLA6u+3Z2*8V,#}$x6`hE)CG_<VZV*nC>j_%AXc;","Ti$[d8J0n'BBoJ[NV2U%i#-:HX-FgSq8wCtGJ33cl[H$Ep0"]]

private def r49_3 : List (Chunk 49) := [
  w 49 52 0 950003 950261 100 9247 ["kLzl6XnZX(w?8pO=aYdl6No*ey**=fdw!(WvFT5YQ^jr!.)y'YmBytUpC8;XT8,2","M9{3nTT$0?OA]L`{H=w;{MPog~(L#C[ux7[jtl$_Hz7xg7>UC/^5+*^V~MKV(Skh","T.qj.%~A-,s'+-{Qe&fiR{`DH`(j<i[Y27tCha)P@W[A<^*OD!cCR-b$b>|j#[b/","H,..>}w7s'z9KhZT0"],
  w 49 52 100 950262 950643 100 7514 ["9Ov4t?T!P]O2NfPZzFJX$<>m?OoEKEK]a1Yp8c4QJ>8?6]&d4~z@J~|vYeeq%PI7",":'$%/2!XV3KVd61_D07z32cpTY`0:hz3WWK6P`hEY`~/yp]*Z%crfb?]:1)M;z]X","^YZ(s|pfc^?u<uolOp71ZD?H~++r_!5RXW}W@ex[nnelbk+In7tlw<#0oC~I,v'l","O%('AFD08/LY=e0qUQ*7D,#U2b;:"],
  w 49 52 200 950644 950901 40 2716 ["[g}i@ZM]iMJ}oLMnb%y[mc'</Wk2R!2p.!6IyD@|{lim296SPzgzS|lKxL3[AI^x","$Gs,>i#*'#,}G^?zv@-i2{,c2?Rpv&b!)#b'-,a86L}fs#jp'_tHo"],
  w 49 51 0 960002 960261 100 8574 ["E~|sp.YYJB_3>VJsP)Ri&3c3K3bpdNe/CM9KcVT#G`Kr36@QCo~_)1A3@ewyMFF:","!]e:{<OO7<@6p;ZkJ&xC9$ExK3X[N4JI;f4Vr/`kokNly(emGjP7]/W+RdT#Cke`","n.-.G^F7'6Z0Ofu]?-^H8Xo1`KK8v).L))LmOX*R*A%2F*YbN~ZvQLk`QTA-|l5e","Ez675,{9PY$f^=bU_g2?w0DE=K8_7|[Dc"]]

private def r49_4 : List (Chunk 49) := [
  w 49 51 100 960262 960646 100 6985 ["*%+OncBT{pH'(jxCG-f(ku[Btfw(X5FfsE%niopaR/Aa:IKEmMb?jIZxo]>oupG?","Es|W]U,[-lCW8n$,rI0r7Qk@FO%{f.]I);EyQ_BJ<6d<ZhxdUmbf(aLUJdhc!1v]","w5u%fTth_wj15Y-:P=p8OI)a209EdjaTaSl~naQKE_4FiJQ~3MJH>FJ2zHb.#@D,","{:]k#^W1nb&74)b))Dzej2491nHIwXO>?sPfrPz1lE#zz{'OLCo4_:9-"],
  w 49 51 200 960647 960900 34 2228 ["RKRuHMxFU8AI,]I[^yugyF/&8B]vvx4tb2rBuAto44srX3;<<{-p>]Swd75ztiu%",";T;=0-Z8K`BKiX5WV4=ghdu8I&kS@yC)*OK}qgDmC@?9#g_"],
  w 49 50 0 970001 970262 100 7943 ["fQ1hEtgw-]ThNTg'3RvDFC$/(iD:raeWZ#<^Jw&6a8R6&,q1O2_u+mXcfq%:lq2J","07{RZsSuG8bet|qsw/m^A!}}:6h/,^+X=^MVJq{r#Bw$-r7(=)HOZ`K,*Ly's|QU","E;RF`>gZlW'rBgJY<}#N|nwmk95F+TM~7_!7GKgRf(}^gJno6|9g;%H)*aKdHXAe","~1q:FBT'XO;hcd6eyH.oHMN_Hz{%Hcr1HMGYwmW(Xy7D'b;/)c"],
  w 49 50 100 970263 970650 100 6610 ["_sTq[^q3eBb]>L,-~zBq*T!Unz=rlaGNww|DYXEEMXQc4>;)zO@XK[U$gj-xTW(d","3h=L;j)X>H`WTpf9-=i?S|~R3=mDttwIuykS3;?do;mPR~Y~'7>Xxo2<C6Ho4Mt9",">jFZ'qPDVgao>^*#ssTm)5IZ4$k3-t/]BgA[d'r,F`/>;Z^of1]`J7{}7B_j31/I","/jvjy!!Dg-gc;wbdlH|*$u+p.n8KSUbLG:8<.W0Vg'P.dX2fzn@8s$]#o>av'AA=","1YVLI@81O]XamMYl%?;XQ+_%hR5'"]]

private def r49_5 : List (Chunk 49) := [
  w 49 50 200 970704 970900 28 1776 ["SByVka#<~,;|Zjqba[jeLRWdHn=lv.4Kr1evT9OP5w9{~^r#x*.jzE}5}(`C4c;@","'B/}E@#fb-7i>W6Pja*O;eLyEP_gi"],
  w 49 49 0 980000 980263 100 7467 ["*}8nd1~Vj?B(dz^2=]{jkdkxX,f?xX8z_N3TpR`Ov`QJ]$kg]BU(/?$_fuSsGGOo","Rs?[fL>-q[Y>kf7Dw^K5c0TJ%1R=35<(:7SYidF}_4R~dHo*%^>>fpD]0a,;d8I,","`S@O^Cjtmq(d@m9NN%w:V;4WH?V4T6h=G6aVuZl3!L!h5/`&ev=pucL6kesiy,|^","/A8.c~l]daK_Dq|dv%]3#.q;EEKKMvGY=}@5?wTGXMKoQ_KI]'P.OX0,e$njkr43","?"],
  w 49 49 100 980264 980708 100 6321 payload8,
  w 49 49 200 980709 980899 21 1286 payload20]

private def r49_6 : List (Chunk 49) := [
  w 49 48 0 990000 990265 100 7006 ["w]/5c}Z9<27~8jJ4ocoMg#cR/|dAjq[*i}7Cm49>*6WjC+w.;c6sMgHAi~JNeAf/","/JKy}t%EN#)de484n?4q^EF(KA>F@8vVt;<Tb~e}nZG~q5(OJ#dbO;&0zBV|q@fy","-R}2c|dL*BmH7#Im+L5YS},WZK}E+7WIYVbaZs=4+r`M8z;)dP]@jv[J(Pj,j/.G","gc+7TVY*i&$Nb*Ez4P:;@xFfB0h?w;99),b0@zS(tMSd0V-/ZVIvD7oRV/O4/WbS","&TO;>pDo{]=#}eJTl.RGB"],
  w 49 48 100 990266 990769 100 6053 payload18,
  w 49 48 200 990770 990899 14 836 payload11,
  w 49 47 0 1000000 1000267 100 6588 ["uQ;8jxp>Lc/`8b*iQkY$vVZ-46bKX6|jMHc#xG-x<%lj9#,vW1[WF}UJ:L(?~fuK","DEM_'@=0F4N@>V`A=,GxY?P|MMv&4{l<{8M{J7^I%S$yP'e|<SfXw`3zl{.&%&*O","BvTpAQR:MEVn#cF+5=-IO?{7w{b9v=ns|tj[}FVE}KzUHA^6,}QUrL>QBdqP~u58","Kjb9}J)c::/VVjC#];QtPNpxl!?6Pfv!Q1U)3MY5@z?4`8ZWR'2T9Qqz.GMZv@Bi",".5Sa%{6)#r1@b;YB|f?y3iON'Un79#{%4wXmuh8KRCO("]]

private def r49_7 : List (Chunk 49) := [
  w 49 47 100 1000268 1000833 100 5811 payload26,
  w 49 47 200 1000834 1000898 6 354 ["''*<pfK*jt/{_+Rwy>&v"],
  w 49 46 0 1010000 1010269 100 6208 ["fkQ^hBdWFB?_|sb$Rd5%XdOpsSMS8ZYTmQAOMy%]lsi4f?9Xr![UKvFbjfB,)qg#","ytb0o;pMO*nkBXmw5Q4+L_yTX6dV5_Di&7+9}HOl%oBE8oX++YbG)anDw?u|=k?v","!S&fAnM&5RBoKKnIRwR8C2JL`PQ[zCyyqWkFH8m_/{b'~s{//n,CLu_`dp`E3KFL","2h>Ij,z-s(6~i'=X_@rU;tBP_=dl46z.F::#*#Jn7K!D#[r*^0YBw8e*QNPee7{V","6W<M9Jc'4q5';,ugDbZj17Efn:/]/gfn_xQvY>Q()J_#.|lD.GZXF25zf3)LPL<r","+I"],
  w 49 46 100 1010270 1010898 99 5552 payload27]

private def r49_8 : List (Chunk 49) := [
  w 49 45 0 1020000 1020271 100 5868 ["$@FW/B!U_LHdiO*ExaW:vh84QbISU%K$U#(?#b-NTUhz4z5ncZA&xiWr!ttO?.;8","el9blZIBl1/S!RG4q]Rr<x4_h|eCJhQQ]w*$K`>6Yv0KUqi-v_{hD[,jtZh[^q8I","Tq,3zVg($twgII3I@Xx|g3U9x:E*4Ue]|>yWq~K;,0g`V9)V96bw6E~hRH91D3SL","@v{ocy/wXda~TIF]8Q'v3)d(8330Lp-n9@Tcw7?cj&Fa6]#M0[$P/Qg&VlJ}-7SI","3mK!#$Ndc@-/mlm.}OZ?|Inneo$up=9+Ku2i:z&qC2nm_.wf64x2WF)u7SrW<QYE","0<PyE6b4.r<c%@W7!I|x}7L5kuvzA,"],
  w 49 45 100 1020272 1020897 91 4926 payload9,
  w 49 44 0 1030000 1030320 100 5568 ["x#p3^/+vVhbMx%JV7(m.C1G[m&8L#@yz|]LvvLujsx=f:c+9[9NiTsh<~x1}qG,M","J$(H<a2{0xH!]a}<r|$(]cY`fSnx?{UyE<p9;>(]w'6X3:EO]f^5IM]]A/p,ab)j","vjNE@MafT.Z{BqB@8-2MrO]#pXOQ`{?7KZ0#:WM/{fC52z<|,@xwR>b3i];xfjD0",":;n$I{E_>2&YU^6Nrn^@%<Ul*vPg~-nBgztC{-cC/EQx+e++(|FF?oFCj{_ckBWD","w`]6alV)jhtXWU'~yw%t;MCnvfM?}Kw|V$h9jD$F.qNma|r8zTm@yU:/Iy^Rj@4t","v>QZfh-o?0wE(zxsq[e'ZE(+D7T>P`E60Z=-w<E!;3G|qOJJ8Fdw9Yt?X"],
  w 49 44 100 1030321 1030897 84 4389 payload7]

private def r49_9 : List (Chunk 49) := [
  w 49 43 0 1040000 1040323 100 5305 ["IH#22%jh:5MxS>-X$I,BDCp?$kVCzu,RJ?lF(R,Xa/.J1)-MbAWcqp{;S/(Y4wjr","/06|=e^98&7&Gy_v~}*oR&A)%NNJ~AZM=RT%&D`)!6,8l_CYGY[.i5UlIbg%TD?a","WXBJH0xQQclaI(|KF7<BeRtag'I$j|unX'Fi&YeEJYsRQHpb{u&T61mM}=[hvFt{",":X.$atH+.t&Px$5dfl^w@VFVrYVnIU@'IZql_s[~IL!~5G3)1$MhP}XYSV]%xB!d","cx'^>Va|Ked9#R<&V([Ms1<Na$8y:R9V;o-k!q_sD)42DnD3)c$la'[;(+wsn%MG","UoQ{*?HUMY~v'(+JueuK2vFHF5cSs:0SnQ:NCC^E3F*rnG,go8UayrFW=ct_Tb%;","&Bp'w4)(5eWtSxQ:nDY(1&?"],
  w 49 43 100 1040324 1040896 76 3829 payload2,
  w 49 42 0 1050000 1050325 100 5059 ["nyI?KwKi<~sX~/mx}efHkm4$~uCRY4#,-cCBr[xR:<sUC6.BP1f}<[y7j#V{up8~","2aD)fx(JUT2jM&XW{]RTzr&IvzWLN>s{E$,oN1!19&o/3/nSzhRm5tEGCOyY'S]K","%B?=<7VL:R&D^5tH+CS~$s[YE0S%YC{dYO0GWn]$HrdE/J94=aA!'T?kCoo4[f:h","d*J}oddC`t_cNQZl#q->?{X*_UjIBo7!i3V1P!~LJCR&hUWk0#cmj#^'J#O-h,P!","rj?q{{oS)!]V+yS{H^M61.X0<)MWdf4:bg[h!iaj?Ufui-9DzIi_D1{CHiLw0k0r","0sJf2n6+81]UguO-p}`O|o2KqCV$O8*tbQy=jV*J2u~yb/uO;k3@m(nU{nBT}z&;","$g*^N%Ab5311acCiW=LdNmLkaC+Lw}2Ld,9HfK[nn+Q6)bZ:(C"],
  w 49 42 100 1050326 1050896 69 3360 payload10]

private def r49_10 : List (Chunk 49) := [
  w 49 41 0 1060000 1060328 100 4828 ["bslcVIuQ~2}5GHR7fPw&U;1WILe3'RLt.(h,nXWx@Y+9oT_8p4x_o{[a@A0G*$Zv","JDL92{]B|1^6VP/2hN@&w?UrTpI`Oge82q>=<?/8<%FnY6e-wUpscs&QM)4i7`^0","Oi3tzLe<40o]pxp,uBKAk).eT<=?]}8h^sv+jfB@tkpP7v:-/S6<B#&i8x@Itk1]","%&`O:Lsl[=XHRzk'0sevjb!H&%]ePjPz<4upS8xKd(@Ug;Q~k,<G|CQY}p/QJYQE","uE9v]WaGC!+eT^i`+;l>,ZDRQiv!&wi-AApYIxd+WDwey[Z;pT[zK_xf+vS6|)l7","TzP*y1|If;j1TQfK(4?r[OspvU~_l,kZpub9z`0}TgGI.^2r3$.2HY;PVr#i?Nug","BE@zHp,D5Wyx7zC?F[|Yp/U{WS^-4:^F25EMU<ru#^k#xGaF>ek9*7TcP48NA`n]","=,GhAm<XCDf"],
  w 49 41 100 1060329 1060833 61 2876 payload6,
  w 49 40 0 1070000 1070330 100 4604 ["k4v<tC>5u|<Ra]EF=<Ed)aVO]nWc*F(eTe_di'.7*16.:![CqyR35Q-]3so9%)H^","I{OjS%nkjy^S>#T8Uput3~THl0'pj(IVcn4+i+<Pho!MY3uEmNjHU|jB[=)_/+Ys","w$WtKY}S8r'>}}mnF7CHMh@0/KSH/}:mc2fZ:a>GaN!PI%z+=V7{7M-KsvFE.Y^!","N%=4ZtQ%}_JZUhbuuAA.~&Hz:}&hP*~cwX>#Fid#(K#}tK}XY;5KlGdDCTrl$H$h","30r',PbE=74]l!->9%8}vxC?G(SbCE7~hW~&)z]D/({oH$'EKJ{y6A/;7@]7e}9g","CE_wRn'p?6m)DuckoYs3kQgRz]KQ^&]W5wQY?>ASe06dB_NZN6&cD{r10J/`rx5Y","W[`LH_(.nDv!5^0H/FkoX1%y<yc{[8eHmLGX@kejx*c)#mDGQX;,?+]yMN53,gjj","#KiP75I:#xj+fSN5h,KEf_$_|PEj"],
  w 49 40 100 1070331 1070832 54 2473 payload19]

private def r49_11 : List (Chunk 49) := [
  w 49 39 0 1080000 1080384 100 4396 ["oqimNCf,/n,#|AIBob^@4Enl'.BaYQ{U|!oLZG<J^Wz/#C-G',;=;IMQW?a^FSoU","!yRQNt}LUW?JBYSq$hXE>qmsXkeM;U>41EtvJ_^/mVaa~sV54Aq<Qc+h-6(`SnzU",";fOpG1Wq>S8b#Iz~0&tQ{tbbXG:}`]-kcM!@_c0DGRz>,fYtXJs5x7BfJ|Wr/y~?","bU.x?ws](TV>}J'!Np5_qq,!2;#F:WlBVr@y;5EvZfZggA*:r]ICY],UwKZcs&a'","v/ocFo+7EdaXI*Nw#{cf[[J7KisW#5ZX(l8?kM2Lfsg$#:;gZA/51s8IES};0wRG","C/4jIECw={t;#d*dg|Sz2$[$0DKXH^8AZm.?K%Kgfr?L={wjHY}_MGwC3ZxfDR5c","$I`d-,AV]vOd<!@Dk1n8zI9iUAoRPIgLZ)nR@O_V0h6eC~Rr(|h-%h;^Oy[dFpbl","#:u&Pg7|JIAF-kTZNzHk4xMRBV.58j%VM1Je8Jj@"],
  w 49 39 100 1080385 1080832 47 2093 payload28,
  w 49 38 0 1090000 1090387 100 4194 [";@z.w}6HN^%_m'|1!~%vXm./Fy9[CqEc>-$.epf=txaz<$#Rp1y2nhP73rlQ&MSj","30.2]^wjCN:lt&bA[XrwPmDv`ruKmdJ,6y)OlBHa!0r5w~=<lxBTf=$U_9mj-_Kj","P~+m3k+cZaC76hfopn$&b$P]{>H*4(@(*SG.Cftm3?%0*!Ouo[}MF/,5$Fe[6wOJ","@6Z'=U2ih(7'Z(L)HD+!9SfS!xyhovwh/S6g!@ba{{.$Ghfg.vh@|{MB+va0H=G9","q;+}MBPZVin,yy^OOh`YB1S]q>LK.v+>6[jU6wvJd(J*3-<y33+g}A!3;n]oGT9a","BWu07E})T`d2:Tam/z7LT}@NmRg%Q1P5x){J)*^xQ7w)NfR[&M%K.e61BTek/-<f","}7i+22U)!~u7wdk{o>hCSx,m[pl>X*CX>9IL|B[t:>Gt-Hm4a_eT7Ws]v1?6r^$O","7P]I(D{-yMFu:2S|2V.Pj2Yb%sQ!<HCGvJqQ@qplMX:{ooWj:BO<Y95:"],
  w 49 38 100 1090388 1090769 40 1735 payload17]

private def r49_12 : List (Chunk 49) := [
  w 49 37 0 1100000 1100390 100 4003 ["G^MBwV#vq+eaIR)JO5T%!R44Sk?h||VUsZn)jn6:;7KVLxcU?Qkc58sYLTc+!o7j","TVa<UO@_Sr|m/A=Z4P<ctApl1t1Mh^T3~DR@Mm4Y#bvuhV?ERt?lYb&vCnzu.u.1","iqa`)]NoW<4uS~c=OkzlBM8^Mxf$MDgrHBSQCmxEGdhpz}=RFnWu2V+_/*lWS3)n","DO,Fb-YEt@mcwr2{&I|;o9+iX#p2hn8YnVMi}|G>8u!mdkx'Fox1QKw[MPfp-uN)","lzzoTaH<QGs;l]f}iZt&0fl2h,t:bai'O4CKKs_J:~D<GBU)kqyH;kg_?>PFpax<","ah*`0'x5:>4F;A*rM0x|Z44d&Oxci/`s>y7-S3MdLF9Oby}nZ)f7AcDTMg(~GCMy","Iule-;r0nS./h.'Cf!I[(C|c1]_/#;Apj?9{](]BLmr|c0mNj5G[.71qn8KbbZtk","_Z=,_w#&Bow2:o-Hea8cQK=p9Do_EnZjOqK%jqlMBY~E7.dvJHstmo>L]AkZe<G*","QJ4"],
  w 49 37 100 1100391 1100768 33 1400 payload22,
  w 49 36 0 1110000 1110393 100 3828 ["qniO5OUD9b)zacw6V==_~9-{wK7g}%*Kx8VUSp,m{l$*@6N}QMv5jWRH)[yuw+n1","0S(b'kq*`aPxc}xoZkGaodva-U>ZP.9~_'OG+gE+thj+[w&P'h@[a@2^F0,TE9lg","@;-,(8+ZBLn&:%(Po:s7k|^vPdBW6KfA1h_Q}z]SO%WLqLe3UJiVr-!!0/Dd)1i'","{X5d:tg!GcMIud!4&4[8#n_ysB$;mjhC;lDoDp$IBV<vK!J]^N`zlc9U!]{Z.Hf,","Vp4tR.X-qBcJ&T%e'Tv;oz[m%!:>8a,d#i|t?+|PW?|i-8B|!NEz*5~kL.w?YI9:","P/|APt?Xd&[KT1JeVbg@<szKGl0b;Y]32^Dc|cYB(4MgAOf[_}L%w<|K)liPZ%vP","=:jihVB1'/P1u{Vy.eC}dv^8BnXk@G5Gzg)k5XIHrP'V:8P@a-A02^GdIw7*u[B5","?pcNUOI'^Ivab(cm<Xqq<gJmRj/7!3h<CJB[T'Ql{.D>v?]%v3GV*6]_!%(<ceG7","&wTe.{g7%)"],
  w 49 36 100 1110448 1110768 27 1122 payload1]

private def r49_13 : List (Chunk 49) := [
  w 49 35 0 1120000 1120451 100 3669 ["DNM+?(naRiBj;TJ)3xM}/q^^Sh.V|,QTtOlw:|{Z}LU^=VP[!aIt{H175oD4^i2U","prM+/A`Z^U(J>KG(&Jy8o`?%8G8~t?)Ocqk!)MA5hg6C,jKK*(&S0HH4[;~U#Q2z","Im@jkDmCP?:?6~)|JHd(3Z&r.,8y2~f;&0Akcu&msM`V}RUx%e(3na7TbEB~TjfH","S_%WK1&tl8IdQ7FSBjG%DPK`^,7Xv?l2NG;Ydn%r(v</F%YIk$F=s>jNSCa6_7u:","j?t@~cuMVH,E(re,D)n5_qBt>}WnGaGrI8)O8(panoC?N}[=XEk:Jbi.u#9=zb00","X-]VcoCP=~rx9<if#wnww$@0w$JPq=g-(U<)LKDNY'x9UmFTPZQ-`3g-Xt/orIIv","Dj84;<[*p5amyMApn6@YV^m=??[h~UOe(vDt]pU5:?r>+Y)8+3v)19vu3Oi^S`MK","W=s%y2sJTg-6{Bovok_^3l8S!]:=iDnPcCdtVD,+MfLbP8Drwzj*+oii+1tR/gnK","#rP?d~Wq]W,MN7"],
  w 49 35 100 1120452 1120705 20 813 payload3,
  w 49 34 0 1130000 1130454 100 3521 [":8Ag%C2=T#9&]?.[~{uF]+]='KbJ}^/uY$T&*[Jsv3ymmx.0@-;kU(m#'_.kc!9j","[IZi/#0Ly6CX1;LCGv.xH(ZOo|JXL2OZKb$yM1{WG~G&W5_t5Oy^Wb}@PTbuS|`4","L1TkOa3lcC8R#QSk^zo-v2!U{Quk=}TIwVsn<5#^SAnO,-r8-Nn^^qpUkx}Y7>K0","BOADvI?.)IeparG-o74y'TG]Y?3mKW(m7v[[(fx(_C:P3bd%zjb$I|}e`/v^s2_G",";HZy1y/If>y!@JH3#(>ib&&]5_L**^TqeO#(!0A*k{U&;ku3ur|@hO<2PX|_=oZ1","<T:|T*2[aA:7pJK#BZ.<;angPo?!XFj5T?'NH9b:$$4'sDL%PH{af%XfE,f>S~KB","_dC6TF3?jHUn>~V7?c$2NA<?9;?U^1xP=#8.>%Ao2$}<tXjxW~[13TpPEesV/6<u","HngU!!BP(i~Yfd#<i{|6K<Kc.tKJJth>GN?n.dmNju,9SJJXl$6s*&+$cTN1Ioo1","xcs+(?0!k"],
  w 49 34 100 1130512 1130704 14 559 payload14]

private def r49_14 : List (Chunk 49) := [
  w 49 33 0 1140000 1140515 100 3394 ["3%|:uBl{Wu_u+J1D6n57VcNbz{.k`auF}[e5daXW?Sh3,`axKK6!Y+bH6H0Gn'oN","`;FH;cG#xy[v^~y,153L(hTGrS{__h<p[+N_&B2gAW9k!.sI;`SpEv&`vIb;8QN)","`{'Ke~hF,LQPHvrTENrpx%q&9N(L7fI]nj(PkgirjLfLQKMNwDD1Gna&g5i#E-o.","/{A{wjA4A~D.{?v1Fxm0kz[MnF`Smt}MZFax8R+/<O+^~Y${$Phbb=&9wB;%)oY9","av,+|5YGPQR?}DKK*%)$TV(s);*+S0w^T=CGCH^.i#b3dX,h3[u1U#RkXP|d-JIt","f%KLwBWz*_d>ND%.6suZ0(b}m%'P,IHK0VhXVPar]ofFTX[qP;@TaCv9cvLNLo;E","2bk*VhR/2?M!fCS1S<fEWg9LS2e(_V{u'6%qJQ,#,y3TnqaF:hJ{Z%l.7KYD|8/H","#2RQWG-kZXpWWPE4q9)X,N5}AJdWNuxBvjVO3(lz-tcVxMw(a|>T(<[bhGxv~B+g","$p`+SD;dQ"],
  w 49 33 100 1140516 1140704 8 315 payload4,
  w 49 32 0 1150000 1150578 100 3278 ["vT<wx]>.^}Ee$.xGcSx|?mTOws6DLtC,!'6PiwN,-^QTP/ZV0:G]}1MT]J]d4a5{","-Gs3M:(sA|$w!ZteZI.RkK73O|h_G(!H!D_Wl]_(7KOv[vAtuT[Mg-zg`2eDZK#P","`)~bND%0LSF:eR^5T`b48Hx.x[@y0C,3le})?Z?4-BU#Nun8ZRap7qL>On$h=Yp|","O)-(Wes=&4En_%8n9|RHt?HX<E,&GG5$yl(7yeum.gjp.A::,]->_#S..CJQHX/C","q=[~z]vI1hO#O0wKyP=V5R4V(n0WQc_0hY]%?uAJ^&0<1j0YyJPCZAWS<Y]'cc~m","hqW.Sy[W7#b?N;'*=/vim?)Ee>6ewY,iPvXnV<*Q^:!'}If=I_4l9tis{>df-e5O","$yiZ?Vn8cS9oX)U^Qd~v1sPz4Gb+xA?3|=aB{zqu_3a'J5is6/Tv8?T7Lv2DQoML","/b[EDX*o?epj67E^g%Y3P:|b.J)m8=GV1=eC'>7SVObb7C+5GLeQ}FVKNX_/|6@r","1M<PEFIOt.]"],
  w 49 32 100 1150640 1150641 2 78 ["#i2GG<Je"]]

private def r49_15 : List (Chunk 49) := [
  w 49 31 0 1160000 1160640 96 3030 ["=aiJP>t5:LX7t*!b*Z[J'D.R+^TOB;>VAS}.CNMgNw-|@T9$h;/&B?i;<hlt]dT&","v26=`a(:(QCCat$2l?8/|ApBL{`o[_[<stvzhYpICKqfyLG>|5+aV;cHQhQb)wxn",">'F=0ojOkBc6aPHasXUk&$&bI)rPk9&:@j<<.O0#7NP3>)NygEb^@Jp&0)0M.%et","rk|9V#S*4VsSHG/SG91fqbeN]!3G16763GqIu(f6|avAY.q_J-9D0wUg*!~mfS1u","VI!VomDg}R~IUQ8>%J%ZwQ{.t:1lSD/9Lcr4%GpapwOl(HRBDzb;Ksi7w|r79WuF","e/HzIf4rPOm;:qc!lfRKF*u~F]ZF<wxi[Mlv{uzD`,3rR{C;gg|pDm9?Onx#SvUf","A^-KCRr$!%E28?cb^!U;30d6Ss`<Nniw[Z,Q<<yq~x=*--Lb#{`ft^3oY&LDx1n1","#PI(OBt2GY+-D0#Eym^Xk46IDs&54@YleL^3B]vt(53#-?}4x"],
  w 49 30 0 1170000 1170640 91 2760 ["U-?+T?UGD.`O7Aso5e,8xKo?801oGg@(TuoM$HmlfpB]Ti:Ca:$pr'r>zj(QD}bk","7|mUFX%Zq0|bf@j7B>J]9beqT[~1n#ZR,WNdlEhz*N$VT]%Z6#6ActTwdc]TLL9*","UtA}qN,,_M$uSxG1gCkyH:r&DpU/#_~Z|^C8X*X63#w}|H>q(6Q#1ad$+Lw`e(>O","K#k#1@t9[S8kYig'KCO[3Y*D#u2oC*w%tQ?G1L:;$EQoN(kd#Bm^{,X[[A&O}^7X","b2W)X4;Fd_~.*14Z@O%@e`R-yS!HErG&f1+B7j0ZTYdt84-HM8fv_;@:kGZBmtN`","1H^2'~nOHPNWhx/rnJ=#m3m;|OR/&jC<CO4eJ@BvPgWij.hkxRO2YgI*(nMK8}_N","%=q{]2Y8l8Z3gXh_cscF!576XvC(/n_`Kit`,lr9l,:,!=vyXUVVl+_u_n9g/+.h","$#*P5]RoP[$'#WRz]:P<E0lR$g[S"],
  w 49 29 0 1180000 1180577 85 2474 ["^&5*EJJ]zBhn1^<TV#H;79_92SCKP?Fobw1o4Aaw&>Lnt$-i+Q_TGIoK2[?iZ6z*","n31.1{bI~Rp5-e3y$UkX0=M1GQSFz1M4>Dc4+i@.D|PmFE@vHKIwu5ctEMKUrs+}","K>|9Q~<w&}&nXl79c_2-]*m?B:s&:CsA<&nY^jSS{7AYYOS!$sr#v'.d,?aZlp{o","b.:@|iS_H91(H&0~X1e#YO_lc*ibN({H[SdO'>?&A'>!*86V[Y+_%}w|@!yu.CKJ","X?,DE!hXNpy]u[b5K'~('>I37h1N=#8$QU.=86e7ddd3d^BOHx9[myxgeZiu^4ZY","Is/239YcYm@@`>6Cxcf;,*yI9+zfqoB2pmi(-t;jFv9O57`&IQD&CK!iIn/eMh0)","+KfJ/[^-^h;KAmOcmtXY|r$ZaS4uBQs}&:tId6.J=joV9F!pc$4bKu>6)xF1{h3%","75"],
  w 49 28 0 1190000 1190576 80 2235 ["0n.iu+fP-PW#e^C5jD&l{F}]<7(I1jc2TT8^'ukBV{+v{eJ/nv9c1jA>xTdt}r0D","o!05mB9'DZ&f62iJKa6Fhu8=f1PWnE:u1P-BsX,(uowD&yO3k|gl5S,mOCrAL<Fd","P8K#w,!ms_DgFtE<'%hg]L#k'[RX!dj/u1kozhok)?C-4lR$ReAC~Ru3_SKi<97_","MgK8PL:.iZC^-8e:>Kp)X.y1:jeP&ZE6&#GKtOACA}C2or~yV^Q6~.jz(w&#bT|*","fq+/}>-5tTWp&{W;MgJ$jUS/w~7bK.9&IH$I&]4D=~T7h1X}~.l0[wkLv'F)?)9n","?,`;US-D{3%zV9Jkc=Q#1fn0Tmxe{6M|D6W|JsK#:t`*mQ#XO.KkjN%&kp$le*$E","#h[)reIJ.c<L]y%L7qn#uOfB+wnA#Jlv^F[/^gc@"]]

private def r49_16 : List (Chunk 49) := [
  w 49 27 0 1200000 1200576 75 2015 ["rdxd<v0gz6u}T&/dEJc9gbf@HdI+Y47vl,[2090SwJo~ocuC`q{;<FfCv;.6NeSj","d7-,O<esIM$5V'%N>E|3rn0>!j/r7f2YFT%7,8Ea53@L_~y?R[T>[{z{p5^3*IsJ","c#C>e'y;C}qTWO3o}rd%N?N&2E<cor~h}MNos!wKr88*Rq[81kNqbUK37V;;K&h>","<sHMq@jO4|R<r65k'J;2ZS8lxL8jN2;64FricD7HD@{[+Wbe@$XQ-fI-DE<F-&`w","r9Th#:xe1b7~wq9VOx)g0F/ToF6~t}Mp9_'Qvk~nIl_2sJv-fhTtl]lCyJu0c{i?","g_G`(xF`e/B!@4Xa15.!i-[K'^P0VV+{z@G-~-k`#4-[Ot0!R/if;eMGe#cG)_W|","$ZLMEed:7K]W@$n=z:?"],
  w 49 26 0 1210000 1210513 70 1800 ["#|_!KcC*Ir?L;8h)m-*I>r4*}2K(wCnB}X7h=pPTHbY2<gZ|ozkcv~J~5S`p3@Wz","m+w<n$jl[fhoV_g-A:7Ofwv39|+e!6vM`0Zgc1]^u'jxbs*B$C+qCcvl,xJ.r~g<","mXfE2QGWK}'zq-3iX.N!En'Ilq&8ns*@w}CshqIBOgUab^'~4^o6q76ebl[<E2~,","1,A@.IFhS_Dvc6+1C[b>pRrYO?]7Wj's.i8gyj*D:#(^J+DF%v7']-`oJ4EQ0LGA","q5*;5r'$%Cf&8eq&Styx^sqik*3mO5JR8!|b%5K3Ee-d_%r5dtDB^DfI'OCa.7`=","-X^?2|.eJHQX'+YD{945Y{q~{g@:)o.k:AD{*d$+vx5)%MaZ%}7j;Xf,I?^,h"],
  w 49 25 0 1220000 1220512 65 1600 ["NQD~?7`*ff5p}WP1`RgD)k}c/-raTuxdgBP[mhx/'J}aGE|<3b:xcj7vAz17!g=1",",r{AZRup6cH_I{g)cmZK6X-Yc2>q'CrT{}a?|wJo~h00'<gx9NQZ?MtHD`{i<)[I","?/1|)^#k*fh`=IObqD%?NXd!_(}7K%pvi^W{YDT!ws^6P`0zo*X1U_?CiHs.wu``","5e;P>D~YohDpQd2Yk)htHxLKPk&iA3V:[%tT*MZ|R2/SNjj,5[,GB~Jv^ZymhF{n","l&~G#v[VGU}tSIw/-a.r{BU1q|M!g~=(L0=V|bWe()@m=SB&d=Ssh=pEu3Y_C^h*","J(24{e,+3zb'PG`7$P@a9sbK;Jbu_J~jfnS!?`<q"],
  w 49 24 0 1230000 1230512 61 1435 ["lhz?~UegT-s}k]Ee/t}U/K-i^N,iEy=->@`t&9.kUBDypsh;;,2[hC_y>#bW][Q1","PdGG^?h2_kyIm=LxJ}?&2pcM.887jftwk:drQCb!j&L%[9V,VB^<F,xX,D$u5.:I","XG*%F>WUVI{#E6YYVo)k6&:Mj_Eratw`ud]8IHuN4{e`FV)1(6JSCN8##Z0M_KrK","4$O}S;*3Ztm`~o~9VW{<_bs#-HTjJ>0[p?`ceq,DnU^fSj[_f2ab,rf_03'TXeX^","[+cWx9:D5.A>iU*'X9Uk])tbp6-;c'`2i6GXs)o8z3dgk</8m8q+^ZI;QC6Ck]mi","-&3iCa*,()P~5H{TN$(Wn`"]]

private def r49_17 : List (Chunk 49) := [
  w 49 23 0 1240000 1240449 56 1254 ["B#5Y#^wK'RkAT#2=k=SDCy@)nruy;ST.pN5j|9b92.h>0;5:oXBhCN.wZGnk!xb1","zS}XKeb1-q4Od;U!<]s)$:hVdRAZu&d<YkSB+fTGC%^;|b+uw`^XfI&BS+d9aNr*","tqjZATM]h@DA.X9iG*!a58|z3vGt/eD-7yerpWv65Y+Dw+]e:i}d4A=H>qK8x8<z","AMU@2<|2csoTA'Y-a-LJ++`Qj[%Dy-m;U/)zI1(zvck&!1j2)LV{^@-_j/K},K?j","mrx&9&znX?4<k?XvTc7O!F<d]4=1dW)>}(ri$)#,/7vmkB`uN9W#+d`'Q!r$eKal","#A"],
  w 49 22 0 1250000 1250448 52 1106 ["I8)h)WBjO+rTykYB1s>:sd<9PQFT=e|c8W<WZEi4&w]V>d2X10uItvr'N|J;{o>U","HNue6]xSmi3QE>v;u>H9JR:Bm#hs6vnx&uh]]7tU(;PGa00EU<2%x+%|#y3'zh8^","W]C]S@3fEX`A~JE_dB(lZ[Blk[/s+y<0dr&OW&)$&0PUAHd(TGo9PkXmEJ~C@av^","R!E9WPF~>6mu:2x_A{hc1KhQ&F&h0]>sIIt_PjzANw+@~}uelO08=:z}z~Jf-sM_","T,zE/_nAf:s_(Cb7jqTKm;{p<wBSbjKIy)@)#g8e@ivoC,~,"],
  w 49 21 0 1260000 1260448 48 970 ["8pYB,R_:E[GAOCqL=a%H5>um:9LiD:T1%H<@<ThllT[!O&=&/V;z.c3n:p,Pn,*e","pWs?:J9bN7-hnq@a@R=9MQje}H>ZOn2Jh}:=|Tib=#iuoyZ-GcaQJ<Vi1NWd.'yR","SF|e7xOnzf;S{Qa?sMW`S8=zg`,>3*GhN4Z=#%nmEsDJWUt8]ZO?8ZP+EkWeG-6S","9gl${c(P.i_pKN`h#j0(`=D&2fDkMR%3jD+.H_<+8~-OLzZH+%?Ghd_;MSZfGvFy","Njv6n2n)OR1@.PdN[8$c$4;=d|X"],
  w 49 20 0 1270000 1270385 44 838 ["1.yGPW~vwUCOU(mK%n*L3s&8(C,lFPGV49PCt+jmQ3O2:@|z]LYy~nDPTjZO{IyN","D&pPgQpDgA$O&(|G_,m_~>/~Kjv(;]^4s!ZkRYm~e_e]|nXw6![m:xbFpj:lmBvc","rA^@EPVZllVe?e[bK5ghGxoF5xbC([@*4pq?$w$QT6Ulom>oj:q!c8KzM7kPV_zv","z??Ms(a@1N,yZJWjA:Fg@aC@Q9)?ElL>rDeF=fd_j_~!dcAe;y5oJtsyzba~Hil,","%C^vi*Q[3b"]]

private def r49_18 : List (Chunk 49) := [
  w 49 19 0 1280000 1280384 40 718 ["v_C)Z[!MtCv9mcn:j-9An]g}qTnSkfoR,I9+}j;Kq4?Y.6Vzp%2R$0V${colgGPM","aa8_gR_}nTM83~]?LzLh%N0ZWyjOUab.TGK^ZN>0{L8PmS{z%GS8R{o&zj7P%WSF","v[DcIaF{YTJu3*Y0b28pNP=fr^PYNDL02c8UTBcdUht(+}QgydggnH+ml>]iqm[3","#)F^}nO6sU|XVbOWS4bKA6TtB?0`b6-'kB(V'L1@E}&i([wb(L"],
  w 49 18 0 1290000 1290384 37 624 ["mDEqvm*rtX'opzy8Bb_xMpo,ZpR`AI[u*joLs?d3ary8%}!5nsd!Q;r%m?q},_EQ","2,F~3eNzFz.I%R?O>{%Q<VgPZ+z}05*p#|pD1w9:*hl|z20_?w=<yOiyy{{/)j)3","N,F4y5NL^Xq2WvYj8G.WEm~PZLSo-HjfT'Vm+n{QHxnXmtAi&=^]V@Zgsf|sjxpV","'nAMWP1:w4,,|733AsrE,6CXq)}yUG"],
  w 49 17 0 1300000 1300321 33 519 [";^70Tj%rK5U-<Ox:8J9|ymatpT.5#(A@l!cFlCJZm){X3pT4Lk<Xxfse{V,3e[5A","ON`EGrvp^Sio7gBiXCT(Pbu%d[knIDQ,xU}$`:'0p4N7/zAq,6&B:_hU8R^~I!C0","8xI(sIQRh4d7AilpO2>6:u3>~O>o;uW8D>.K.B=3sXVQTDO0'.8%U`71-Me3U?Gx","+vm=<ZQ!"],
  w 49 16 0 1310000 1310320 30 438 ["{bP<E`J)D8^9`xW0aJWVzv?j[Q>TV7;'K1.<W/V:8?YZ<)'[:/+HOf#UR(g>]Q.g","U6!Q?igUzb^9+m(I%oDJ[=kZax^J<:PbM*U8t.C<lY:wps]Sl&!o)`#r$RLjyvz8","#FLOZY,?^<2t1;MpbfV0KCCb.kg9kq=W@m$WDx3/J}rnl/6f%trVQm9m"]]

private def r49_19 : List (Chunk 49) := [
  w 49 15 0 1320000 1320320 27 366 ["?O`iBQCM71Lao!qa.QR0O6o2Ce/+};&]~etx8^R(C3#af{hEJ?}Tn%WOFU*F4:@^","ofCc76VWK9YTuQw>^!)^Xu,x:N>_[cKGb-F3q[du:(0O*y30G4}wPO!koB-_P[rc","DUy$im-7yB))>O.~F9m~o36g@yRb@20Z"],
  w 49 14 0 1330000 1330257 24 297 ["bk|;d,4.'&&^K+`g8~fV{|y_-kt(J^6'.*1^UtB!l;b)2k6zp7}Znq85S<Z%ZlGJ","Ck]$IdXdaVTzTC?[xPIAQzA6yk>7oz0-iTO9F,`wGGu'buYj+(a(a*Fc!dxZaJAM","j:$w@O>@1q/'#OJ"],
  w 49 13 0 1340000 1340256 21 237 [">&:14,J73VVPxBtgblpZ?x|tPm>=49.TpAk3D+n42*OO0d/GGZC%{j7U0sk>#Wk6","%Z&.Yr&*2CdofnkX|K`3i%PX63deQg3OM5IP?rBFBh&JLdHAC%Kh#[B@LJ{'$q"],
  w 49 12 0 1350000 1350256 19 194 ["exYW9fGe~u!M=XaP]E[BQ%D1-Db)u$!z9x)o!&:.o=nR#!!6bmBgdpEC-T>%{d2V",",O8xPef]&-/Jh>BE{AtfCLeuMMqpKzU-G;H6NE<Tgyoc8T"]]

private def r49_20 : List (Chunk 49) := [
  w 49 11 0 1360000 1360193 16 145 ["q)E9%VS5dL2cf$`e.#dCNPrR'ot4~LAseDsS7KSB{Kr($7,U?R]OMX>Yai-pmsO{","$O8IcY&$KtBB#@D2PS.@91=1Y~X"],
  w 49 10 0 1370000 1370192 14 111 ["&,1S#utY3,YJ^CL%&Yg0A{#M>4n.dk&z11GQ}kjScc:duO,L8p`Y126'vsix5?Vh","#Fo+sPxf5K_'b-L$k"],
  w 49 9 0 1380000 1380192 12 83 ["fRc8qS5N#bM6IoC*4d}Y%!>XFR]1rT+]>2^x&0?C:/Y[ciCPE<C&?>T`.C[/.FBf","%#-"],
  w 49 8 0 1390000 1390129 10 57 ["OMGN!dt-o&SKC:-0/]&4ArD5uQNBT[O#sVWjC7?*gIMaB~|fA$u7Z$bzY9ZW"]]

private def r49_21 : List (Chunk 49) := [
  w 49 7 0 1400000 1400128 8 37 ["+16ZdW~LMgAV]]h%UK:<6XQ->BJ#t+#.,oaW?$e!@Y$4sjK8o"],
  w 49 6 0 1410000 1410128 7 25 ["$;=Jl:mZ$F5=680!FPMV!'z0&X}z160iKtP>6ybmEU!"],
  w 49 5 0 1420000 1420065 5 12 ["U]OCa&4'ma_wx0<ep2T}376=AUnz?=c"],
  w 49 4 0 1430000 1430064 4 5 ["Gr1!MxGP4{i>z(9FZU~W3~3CO+"]]

private def r49_22 : List (Chunk 49) := [
  w 49 3 0 1440000 1440064 3 1 ["nI(Qvu]XJqKUiw0^"],
  w 49 2 0 1450000 1450001 2 0 ["#)ti)FIBw}QrR"],
  w 49 1 0 1460000 1460000 1 0 ["+LBB%"],
  w 49 0 0 1470000 1470000 1 0 ["9KR`z"]]
private def chunks49:List (Chunk 49):=r49_0 ++ r49_1 ++ r49_2 ++ r49_3 ++ r49_4 ++ r49_5 ++ r49_6 ++ r49_7 ++ r49_8 ++ r49_9 ++ r49_10 ++ r49_11 ++ r49_12 ++ r49_13 ++ r49_14 ++ r49_15 ++ r49_16 ++ r49_17 ++ r49_18 ++ r49_19 ++ r49_20 ++ r49_21 ++ r49_22
def rows49:=rowsFrom chunks49

theorem good49 : ∀ r ∈ rows49,good 49 r=true:=rowsFrom_good chunks49

theorem sorted49 : rows49.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks49 0 (by decide +kernel)).1

theorem mass49 (i : Fin 57) :
    bandCount 49 (i.val:ℤ) 56 14≤(rows49.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks49).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 49 (j:ℤ) 56 14≤mass j chunks49))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total49 : (rows49.map (price 49)).sum = 325591 :=
  (total_eq chunks49).trans (by decide +kernel)


end Final50RankReceipt

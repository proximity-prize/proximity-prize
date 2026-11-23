/-
Nine-factor witness construction adapted from public Proximity Prize peer
submission 657, commit e07f14a81dfe2cf1bda985e67040ad4d31fe81ab.
-/
import ProximityPrize.SubmissionLower.Final50RankReceiptBase

namespace Final50RankReceipt
abbrev payload0 : List String := ["0(Q2mV0*p[mwcM{W7pi{f`GUdtV]Ym&kN3U'kV7tfxjN72(x7L:=6;S^l^Zj^*'O","xzEDRiKf8%:)234Xn<;+bL#i.Xat:I_/5JKdg'5UjIn#!{Q+@?0b{xV_.<VL+[u.","#7933~mg,:rZLuSd&>~/9P+B:EV=ior)-i-.a`|q9"]
abbrev payload1 : List String := ["1I.mO@f?C{nA<>gdP]VVYo;.56<i@Blp?FA8RY,leJ5Ev;NKDQ!tc{Ee_dd%SID<","#;*^@4m:q~jj*W=<ol&Z^q[/g_E;B{]~G3m*!2Z;'M"]
abbrev payload2 : List String := ["YNWN)%0c;OdcIiK&}<,5B2-HQ!b9Tv?:/b:Pj:V:C|k?500wBM)Ws=^'Oc{R?=WA","wErQXr27W-'F+qLB3R~T82j^ez%]XCbh||191J1)<8erSl`5m~Nq:&{AT8/QZaUr","v}-wq]8GV{<s0~'u1gqF,UQ25iwK49UHDI=-$?._F<<9}>~qQsL#Aj^nr2mfS(V&","Igzxh+dp?B8f_QmFM|G$ER<SFO2ZD3D,9D^aJIkDJ+&6%8>)}F34(p({#5GlX;gI","#J6%Y6dgcO>la5[mpF;8c=mK+ioGrM>*_'znG9*~_X@[T83EM=]^%l"]
abbrev payload3 : List String := ["`:<(xiU7|qxCPb_$bBtq#~qIt:BAe]%{yg9xUv~#oM+dKB;Yi%oN]!oL0D$6Q?#9","#Pz*)01bw~(.>6f3."]
abbrev payload4 : List String := ["#^lnGoE*Y:@S,in!qb^{Km?%F@DGV#8OJ/9"]
abbrev payload5 : List String := ["<}Ixk^>_2]2zOHOju}4w6-rL^:AcKSooQ-,0S<.nA|%o#*.Ix(gfqCF!PJ%{E{Sa","#cBM0tDgm,.$b).=Ro_j/oX?&N`o9Jfn:h<gK?]qZfRQW-L,Z-}Y:A47|KPmlNoe"]
abbrev payload6 : List String := ["8Jar{.p</r(=>d,q6=RrV/l5am(G9.Oe&s)zJ.!J`;K.X6}B;b|{.xB=P8B7OO/k","9#8pF$>e;:znLY`-jGo1=aJ?%t$NIoh8V4zQ^}apP9kX12O^0OCz?95XK3xBPjJr","=]5zilUe)_wd?k411GSB}uP$*<b`I##g;@&Sx)hWEo.B9PzEwjiJ@R1T8/{pkkvJ","#he%-~)nzhco]5<1>jcKGH1X>xW%Nru2Ov8/SC73Fd<iH)HRC,{"]
abbrev payload7 : List String := ["w:Six.V8_@4fu&iNU#UUQ9M8$[{!c|(z@#OFRM'l0DHS:U*1,LLmjfer~i|hFwfj","ZXlTG/(m@rYC?3gqr/fz=Z.L:f`%Gb^8A;ee+%LcP6T{S/Yp>W.X+,kdP_.;Irg}","T2{_9.`t(PvJ!FV:YPffqBSj6V2dMJVI.(efW7n3iwN}O?h`nvRUQt&pA!EK_?[@","zQQYs18|3q=QQ0]&^y:)T[EycVkfOz.)55i#v8!-!rMHLVT_zQ}$Vy|p]U.TfNM(","YDB`eK^-`0L`)IN{3e['mbVSv+{{)unrwZ@'*A.d!?[b4=T=Vcxj<r6gZ)BZZ`&I","#yZbWIFgQO/bmk~W-C&oxaWE)4"]
abbrev payload8 : List String := ["77mXx!Mz0a@WgzzC~ka!d:F0rQ0R#ukwTRnm#Pi&VYT>,YnAEc{Ax1rZ[P0nBJw+","$!k)6z_b#ogWL&@p-d'C=$LH$X`C%3.^;=I/9#*mX$YDSAzI&#yM)c2HTgkl&NbE","6#Wvup%r{hRy!+ch.c2#saC<:Jo/u,e!LZMbSeDVv@~,4QdCQzF]/)e%hhSvhDE)","Z6t5;:a2C4M'Ty+xe+I@s71ihp&nA:b'vambj!>W<cr>W-Iyb3v%fHZHk9@ISK(s","}[cfw>'lIGqe9KQA%2]2$BdQ?o]~a.9^WK1U'o?UM#A_:>7o_G:/C0q'1FAfU@}4","#"]
abbrev payload9 : List String := ["KjJ'R>O{FF@tF[z@9UTvR5Y}h49tUs}Ic7`U,sRg+*W$J1g32xXKf>eZqEgQ@L}D","Wy3(P:w_P?d5zu'e{g'rlPw?;`u2{Dl@IuJXM6LE,Fw=C5XRXPB{Y=O*<W,EW0go","vfu.p7|H)fIh0t$0tE!P828@-sl]F^x5|<T@ND[,q|DRAT^}ufwNL0,3HqKC|J^]","DP[lUhLeX$S+lM8pyFWag8|N5lQuQAG.B&*-_Mdq%'kJ8tL$:g%Z0Mh9Lq8Zd8F*","NrL^5wUf@l}hob>0pp!+ON0^7&-f1^N=J,;[8}vPj?0SMsan$pj@5{;sJ7[z#uSK","$(w&_%ous^J~$E5{Y17.}&qn@6ikjqLi_=fg[jMp]nt?u&Pq~n#u"]
abbrev payload10 : List String := ["|U6d*_us/JEj:-m2r7eX%.Ktf4u=-H*5S8RBpe^f@]_5$<OzN.W&U8<Zpj3y1.>-","<ES?Ds~VBt,k_P~L!P-,%WnA..R3gAfUsO4Rclqk7=6?UG&@X-B67M@%>LaN$-^A","pPj8pQ6H>$I|$X!&TA'-df[A`y)tNk%<nmiIf+LYU4F|Xa.=$G{E9dt.cDG>G2(h","sR=g4{%p3)B4O)&0,|Wk:TA<k?X9|`My)DxQ;^&Mz<kU9iy1dy'nW9GV@]uWMZTb","$F$v~FHi^v~#L6@)b';Cgu0"]
abbrev payload11 : List String := ["$T%yUEpkWyXbI}$$OUC]%U0$&-,3X2_*h!,cZ*Rb>Bjr=,>bao"]
abbrev payload12 : List String := ["%-{k7s{Hiie2#eFU<)cd@Fj=$o!bGR_ZW=1z_}}^=!e5M|A}RA*}Qtw!PB2kkFu#","p)Bjmr:?,B8/o<{d(cg*>Nzj.45Jch;w%!c,mtb9((-]~t#%%sHm1AmW(?s`n{+G","P<cw<O7EdGOE6=v.'*!y7]#rjb(k,yR*Dw+GH=0}U[d~D>#9Sa|HqpUoVym'PEKp","%7!#"]
abbrev payload13 : List String := ["nd<Cc]_,.ggqk#]bW@K}>YxH4w{]cU(4$8jyLV#_8Be#(~'Ja$4qpg!9GXL)Q&oT","%YCQ0q_q~NI@hd$dp=jiU$TfIufauXN2"]
abbrev payload14 : List String := ["%gl7wz2}(n'5?9%0KA|<|4rk]kM'pbA/Y8ePdjN_zG|>G$Kjt'.8k?<@C}<"]
abbrev payload15 : List String := ["rfACbL1D#S./kv$~KsrD<@Yr/r.FhR$*D|A&Bh+SO2Y&20/j(a$!;m']-7/ZwfrG","V~Ea-B`0nxR?j#tR`[pEZE#$pH:zX(rLTG*A4{r;@~7AB)6>@tNI}K|3PvOSl]vt","3^zMQ[:F}P:y@9:0)+FndY{-@{ajN@e5a_*]$@KG(btTvfM*52z=jJ]^4&k9u6WP","'<>3-g:k6BNP-b+7{LM?=Ogj0}j5Y=R{{6T]/%I$.Sms?E^9rb=5X"]
abbrev payload16 : List String := ["?Ay{><'~4p?H8FTVY9vvFP;6E|Hq;PKLx,o;f@xC^ol-%m'fGJn>BhT&y)GO-M%W","xS*e;kjHL}ZrI'J`+gETc'R9Q7L<C<deZazp+}]L%]p,I8cAzS'D%]<gP)&&'#$8","eL?4G0I)(smF=KWUM0)o4WjCU;dZ?al?ld|prI6k_;#-?}gm5S9*Dhns.>x/oTJ#","I[)3ahOU^xu'976s3e/)R8.,^U#F%`4X1</V%a.&?@73t{k4S:y9<I^8eK:6K#Py","'Y~Gt5$6l/NO<Hrlid1oe:3q-!-"]
abbrev payload17 : List String := ["A$*}k3]xiZuylPH*tj/YPG%Qc`qh9Wi'~As;7<KQ.)x:cT-OYjaguE|tGu+,9okE","'2~YB}:`1UJ@n~YSqB}xlkX`xQ[MD4#TdK2b14*mcb$t,_:(6ubnD%)n;R{AZo3$",",#fO1Jl!P1fCyZ1rF[ecJn_e+d/N"]
abbrev payload18 : List String := ["*bLox{HcX!<>(o*}}zo]>o&]y[y8v2^#J,7(VdeR?h<wVBnjLxK`a`T#;J'nAm[b","$]Q|?Vdyiu'$dMX+DX#w)).!2,3.>}n}?u806YNF6lZ_^a}~N6{(jb!Enf,Z0w7d","q0Zt(_X:6<T/IU:,E{8Lh'iv/p%Mu)Gm@8guN>x(*=Cjk}xr.|_6:SLg!U`])!,C","CTu:Ef&%F|4{l:Bd<tIl<$XIK#}0lg_ch4SST9-:g1A&1mKnXdE;<_Av|mK<u$#4","wZhEZikgH1hzJufj]U~tMAKXt>6GX.3S|zMy6{QxZAO^1{*f[K}aMq_6vDZ!/[/&","04y%x4y$_U3kuo}fn3]oO`K?{J2>EJ"]
abbrev payload19 : List String := ["X5Y2'Uw}kN{uH2*'A3X-$p18>==:A@5dDe=A,a.1)NlQe6yzEOG^~uz]8tf2==kU","&=2lkCLk/5*3%S!>r#@mVR292<{Yp|Bq*&R@>&<1)HpT?@bYbSmom$htvT[?#j*s","dan=Ur]p2{@9t&?z)4E4-:R5v+7tOj&_tLS`LYmJ:!,Vez8GDXun0z:OPsl,xLPo","0DtwbfO]f3ns%`WUw>>>"]
abbrev payload20 : List String := ["YX0A7MxRGn-hO]}8ASfG6axzrRq0s1dC4^j,$d-5Kc*b2-Jsx/BRB*T}`2r4>P#k","33:k=)PH"]
abbrev payload21 : List String := ["Q@JgI'qZ1Z)4OgET8cC>_^|d'rGN%|xj<SDT:}yX.p+LS<;jXgOQJT0zy_kpwMo[","4dfMp]+LVGX$|dBz^>vLXl',!-dDMSk$m$G~Nl$(B.$OoqRUQH^Hif="]
abbrev payload22 : List String := ["vZ)ymJ1lWFFwImv+j3&`V^2gYjwd'#;7r.K@B^U+Z1LA<Ey<^~V3WvGjHrbuAY/I","(FQdo|XCd_r5;EQITU}7-[,}Y`|:_iFQ@Rn0xDLJ0CJlql[;lXUZeVP/vC2C.TPO","5"]
abbrev payload23 : List String := ["|F9A(*Z.Dx5j.1{IO#/4S>=&V`*</S68,an7'MLIw=c)u[.y/}5[[mm_iH!Ww`N4","F;)|f$a#0'.xNRCE@f~7)D~l'dq%J8E5iZqqq*S*~sUT7MO!WWGjFGf>(V:6+;3V","9%XRs]si~L,&O@yHWrQyAGb&Z:ZWgI9%wM{6xhbO$|,$@!T^Ft]ZE%"]
abbrev payload24 : List String := ["ISLh=qf{2p8^}y:'Ov7'2DCgs^Si&^]MQILJ8`guUd!iA(<~A~a3jdC}ImA'aWAH","B6e7wav`YTk*Hn=qA{Khxjl6,b%iB0hD26'AB~Nr!6O}kL(py3b7C$"]
abbrev payload25 : List String := ["k[~}Xi1_U0`SdFRQ3m)+KX!OO^k|>*Qc>n77jecQ9EwVjc={?F$TTN#*iX.]TA7`","jG*pZ(y{~x<wK9G'W3VvBB;_w.ErDwa-Zi@KVY+v$x%/D>~M,@=Jp.&z$dI^cOi;","9B_{OWIGcJ8&2bE'gAGJ5]rzGF*fBZwNSX)8VyfI_0{;=Cw2o[Q5+WEemEBBuOh,","D6D-t.&e9Y`c=dJGZy`L2)1-Q'W("]
abbrev payload26 : List String := ["OHd#-H3`:0^H6}L46fk[`QnEQ(^t?%Ol_nh>c/1`{m_IX;5)n_/cayig^)_*mmhQ","MoTXk(=y:{QFa~s0r$gA?+~*$-T|,j_~?Et^~,+Q/grSi|VV^moI={+lyQ8?AB_q","X|X?_q0(41eSYc(fU9Fi7WLUew2IiwJY&>m$]NL9u#z;AU@._KP`<VR1KF}Sz{rv","7*_$#k<ffhIE<l$b=T=/#Ug~pa'GKb-^QXm7bvw6|!6b-TcA14salW</%x!S+A_O","e[!=&p7E2a_G7o~(OQ=TGtGv!N]#Px2|fuwJY(UDo6v[iTo'~*FnthNpDglU587y","DA-0EhI^R[IFcqCtz8'tprrJFrvNL&XA.-d1sYb]z<zewp_^SQEg&H4_vs"]
abbrev payload27 : List String := ["~@N&l$bii3'@kEdE6M^_/cX-l$..+4y~F3HFt1xkZq)ajJXRCNUg#1?Fcc]9S+H]","J~!?G$i!8[sW(svcg;YD~LaBV&/[/hcrS9f3_,%QNN:#3Nqw9(n-9q9wmkarL<|~","<6Bc,jvkeUk0_N9d&@^Z)C&f1[-,-tW%$c91<i8;J~f/%|pRz.*FGpGSi$gwi7I>","i^ANt{~KMqko}h6=-K@r0$w;Ze-9Vx^O(n`9?+)`t0M:1_.^1bE!Xv1aJ0p-.2/B","4|'JzBn$O{oR|5/tvwK[T1D-5l^lo&4<&`ckS~YHLC2!>k#ppW44Z0O,ey7j7t5C","vQJvyMIWL;/gCN5u~i$!g9ZTr,'xR__PJpn4=}SzmFM/+GT[y<?DCvps2{q&!t(j","F;wc;"]
abbrev payload28 : List String := ["e?j.4V`Jo)'+![U1MyqY{F$.j't+-CP!wRoOd{A5F4#C8R(:Rmjxrq]Ht~'tuY&F","Foobq`Z:RP}CyD88`g:]WW%W3nAcyHyMw//mLGxhk4b_ft14,[R+*O3LZU`v`cKC","Hfsb?]g1KCnKWP:JQN8@Dx5fB:%'.mRQp3DVOB?`C[)B1~DsEg+(M}CD"]
abbrev payload29 : List String := ["|]d^D(.!M2]f6tqeA(]Cdd.NT2eH?OIVPJ9F3AawVv'8Dq1fAoZa';khxU37cq3`","h|.ty:&jsIRh:#Wk*d+#]W?}=_No#x{EDpqNZb{&WYEt*;tJ@^!Q]k!Zy.}"]
end Final50RankReceipt

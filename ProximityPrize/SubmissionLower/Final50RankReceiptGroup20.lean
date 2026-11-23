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



private def r20_0 : List (Chunk 20) := [
  w 20 54 0 60902 60902 1 102 [],
  w 20 53 0 70839 70901 2 204 [],
  w 20 52 0 80776 80901 4 405 ["*<J"],
  w 20 51 0 90713 90900 6 605 ["2%{LJ"]]

private def r20_1 : List (Chunk 20) := [
  w 20 50 0 100650 100900 9 901 ["0SL7Oij*R"],
  w 20 49 0 110587 110899 12 1196 ["4z.O93$Q/pE^ss"],
  w 20 48 0 120524 120899 16 1583 ["%2~k4~[n#bqNiLu&s522"],
  w 20 47 0 130461 130898 19 1867 ["-TXVIEv{5w}OB?xvkjKmSBjWRR"]]

private def r20_2 : List (Chunk 20) := [
  w 20 46 0 140398 140898 23 2243 ["&o9]G3r!VpH(ME6BM,Q12V=^g@/t`Yo8:"],
  w 20 45 0 150335 150897 26 2518 ["3Q00<'5jw6)|#SMJ7;MAp`o5l=V_RCQ/[rn!z4:"],
  w 20 44 0 160272 160897 30 2886 ["(sy%oVH]`;s5DN?=89O1~UHz!|INf<tJL@}{)3?U%V|-)."],
  w 20 43 0 170209 170896 33 3156 [":yj'lAy:~TGr:m<;y<TuS6L4$~J@8(F>=?t'KsGBzj<0ApQ+'Q>c"]]

private def r20_3 : List (Chunk 20) := [
  w 20 42 0 180146 180896 37 3518 ["%EB~kICm:_t#}#fg=2czEt0:Qgj%24*0GllJK[:4g.YEzm_>n^)`rV%_]J"],
  w 20 41 0 190083 190833 40 3786 ["$>yMt0P_GWmxn%vm]rCFwE5cm+3sB@X*b_ky[O+M&`^FETaN_o~O2])pJJ]u2IU_"],
  w 20 40 0 200020 200832 44 4146 ["QE[|fT+C$@-}cQ*qsw.+IUH034RaE-O0]96Mkn[45%2D3N||B|i<q!V:7&dKgXE.",":.7Ld"],
  w 20 39 0 210019 210832 47 4390 ["dvI?h{g+rEUZ;_uVQ-[n~1ha^V~AMVVh{wsm4pc&2`mRF@b7>[0_zUB*G1Ab`Ob.","znI_}Cz_I68"]]

private def r20_4 : List (Chunk 20) := [
  w 20 38 0 220018 220769 50 4646 ["rJaRNq;<(-q.LQ4S[,%TT<M%(8ZpZ)PAuWZ]&t/%C$J`oh~Oy,>r;<T_X.Y=8u8!","$?cpqf%[^oZ/jdE>t"],
  w 20 37 0 230017 230768 52 4790 ["m'mRPT,8U|D9]$tf=&BhP[rzsh7%:xBBSWGj6+0aop!R]+ZH_5T8'r!Lg>1Esz]c","Dn&@haueyZ/(*9jws=B}x"],
  w 20 36 0 240016 240768 55 5022 ["HI,m'nRSQH/nxMNDMN@S`-O4zP#4yL2u+VAH3T7O5E0;llB#?A]?(PV6qXC]=Fh_","OL3yDn'7$.hO[QNVs7kdO&=<@r"],
  w 20 35 0 250015 250705 56 5070 ["h&D?b|Z:[p:2%YA#8AE0}kw&qC,|2XJt(>g_,PyL)>Vagz6(_<ca@jM-:(ue'TE6","Nl4_)y++5|m^v(4t<[Rw5UJr6=I:C"]]

private def r20_5 : List (Chunk 20) := [
  w 20 34 0 260014 260704 58 5206 [">GAN%1d1~&#_0O}UT<mEQ#@,UG**tC_+C(X<ge[]S+Sgi<<v#Ht4/p@}/koFImuR","$[<B(Mxff?.Cp%ycwo#i^*&g^h(?[o)Ze"],
  w 20 33 0 270013 270704 59 5234 ["(Fsh.T#tORq}4q~RwEH#m!{xVmpe7#;!Fe;^Nr',w1>Er>Nf=:^nlqOxVZ}Ie+9V","#i_]aS'4}ohM:>?Y{i.YTwzl{iHZ?zGl.=9o"],
  w 20 32 0 280012 280641 60 5278 ["$~bRVANF1FnsATOcZMM;oyP3`)W(p}LMiGI%g|>ed8S!.}=(B+l):O.:mi3`eN;o","UmFk=t2X:>X*Tl{U9^XGm%xci4=G6FaC'{}U|"],
  w 20 31 0 290011 290640 60 5218 ["W|}^#({2p<ZW?2EpH'Dk0xc30mo+@L{TdXRx|AXy!1xU@UHU7zXYzRTXc7h!0,1&","#V1$wq/hd2on/p04.{j6f4mR_pj3ob!Y1>q'KVp"]]

private def r20_6 : List (Chunk 20) := [
  w 20 30 0 300010 300640 61 5242 ["bjVY#n,*'WgT*u{Hi3E}-*wX+T9K9qud(@6{yDs44L{+o4M/.+.xW1En,<~R_o4s","Dw6s.:_&;`eq83@MS?Jx`]3a+~?~T}/1VPO-B><2"],
  w 20 29 0 310009 310577 60 5098 ["*Q!RtK+uf`o%Bm.Lxcb4*Wc2A,HrCyJql!Op^9/5m@OW{PiaeNnH[o!GG6M{?{9&","'GxqeBdnWh:+8tl4;,~E6`7516c%{S,GzkV+Q.pj"],
  w 20 28 0 320008 320576 60 5038 ["M6?8d#0.s;_7#p>GWW$#Pa2Tfk)NM0j<CJBr9cb&sKeAfzMFoG#yit7V)'E=>S}B","'Gxs<+8.xG*/kF@[`d21Xa0G7[zOPE7t~Zd]RKCz"],
  w 20 27 0 330007 330576 59 4878 ["Q$p@=|au}-`kPj.sEI(RyoqH%xFKfz.[=wkcAkjF;u*Rm7+F{kXk%h38eP?w>4}2","a<WQyYwb02jxd+=zkH?o+mi=axC$(h&1xEzpgFB"]]

private def r20_7 : List (Chunk 20) := [
  w 20 26 0 340006 340513 58 4738 ["OCu|?[T@7FuVzt_q@4E58}t21Ad;)+R0@r5aaGNLC73C[5rm6|OA)ve,5ez<OXwZ","%A7<D/3q%ZJ+RU;ix(([w.v;%gs`6h'+B_:x<K"],
  w 20 25 0 350005 350512 56 4502 ["?A0urAR22r-%VPoIiV14$17sd'+didv.O#1J;'Y*J4{=~vU`z3S}z2]n,N?7hLvw","#eduGqH%#0h4bi-Z~)?}o@Az3W<RK7YNh,5-"],
  w 20 24 0 360004 360512 55 4346 ["&CP#9N3AH7(t$3B4c3REEE!]T#Eguo;w#LpODGBT;hO|Ug%ih/B#kg4/k%J~7-;>",").C9t=V)-;BMe.KVI:_o=N.mGdb[BP|T5("],
  w 20 23 0 370003 370449 52 4038 ["ad?ZU|Q$Fj<bZD,ID+9rv6,./,u;*9l>Nv#7.f|1N@3t4_<!MW:NPHEqO(_a6P)F","3cC+0YP2;<~TgAT(4W'$`.qP[,BKB`"]]

private def r20_8 : List (Chunk 20) := [
  w 20 22 0 380002 380448 50 3810 ["q%[o(6BfOHms:6_Sg*fJV-kK||FZouohoywH-3bN~04Ac;o+TM<'[Kw*Edy;TnDB","%<>ZzN/_rplLR~gsrk0~:m;lm)j"],
  w 20 21 0 390001 390448 47 3490 ["~X,qSBY<yd{eAB[EkrX:1T&WCvaI[t-4eIbq>,^#XMJOTN@&~bqN'&I@&,?rF_@!",")#ktt:U_edg4i:~Nk)y@x-g"],
  w 20 20 0 400000 400385 44 3194 [":_^bV;iB/nL(olxN:*53/R$b/@5G:^bfZ_8ZH+AJy*o6ACu:_$/RPn~#125'_B#N","(.SaT45UkS0*@0l7Tj"],
  w 20 19 0 410000 410384 40 2810 ["83>izE'Wbgn/BQp=sZ(uMZKFuI=T))OM8zi=i+-62x)h@FLo+-8)j#iG^EtM&d1?","X/<lU_#uK[Al"]]

private def r20_9 : List (Chunk 20) := [
  w 20 18 0 420000 420384 37 2502 ["TG<RbGmHhj5)xhvM+GH:7bXljuD}Z5WxH2?M;7FU^CX_diowWgnB,nBq8P[P%|np","KUp(a8m"],
  w 20 17 0 430000 430321 33 2160 ["YvSp2j:p-Skm?]BB$4NMH1OcaCs]+R<Rh1UaY4o+uLp)[@1)nZT'qg'<6&)-c<KW","#"],
  w 20 16 0 440000 440320 30 1890 ["#7Nb.I[&TQ8m;?<neIWT5%ZF<'~u1ghe|7%9~XNgNa|:DN@?*rLhmY<=M_q+"],
  w 20 15 0 450000 450320 27 1634 ["z,:T'ns<&SQ]}?vphi[UD/WG/Ee3j]pYTti0_siM5~j0I]qGSg}LOh"]]

private def r20_10 : List (Chunk 20) := [
  w 20 14 0 460000 460257 24 1398 ["m,[7H~V5/iKKviza%ki6?k0B4$,Gu,/V`X`;R74qAcH]=Ob3h"],
  w 20 13 0 470000 470256 21 1176 ["Zrfu%VL;pV0(X:T*}6OuY8nTX$V>uhkCUQuOUHhmKH1/"],
  w 20 12 0 480000 480256 19 1014 [",U`658Jp0tw2V{xS*.4{nA/;9nFi:@+7%|L)Gj(#7"],
  w 20 11 0 490000 490193 16 822 ["*ucqVYk}%2q42WaSQXX#0.Sw^bFQG.z['&)/"]]

private def r20_11 : List (Chunk 20) := [
  w 20 10 0 500000 500192 14 686 ["#^~Xtj?Jh~.kiKUK&rD2|LlA'8vkh&]X+"],
  w 20 9 0 510000 510192 12 560 [">7#O'06cf|SpeVP*D|NY,n:gx^SFt"],
  w 20 8 0 520000 520129 10 446 ["'d6STjrMVGuL8;/ysvX@HIH)]l"],
  w 20 7 0 530000 530128 8 341 ["E%v|1&ZsSf#Cc~8d=PP`h"]]

private def r20_12 : List (Chunk 20) := [
  w 20 6 0 540000 540128 7 281 ["#Vs,?W.'dNW|4|tiGA+G"],
  w 20 5 0 550000 550065 5 193 [",L0#q;O}^v:UT30"],
  w 20 4 0 560000 560064 4 146 ["1S#XVE?_6m6]"],
  w 20 3 0 570000 570064 3 103 ["9)&S{g:F<"]]

private def r20_13 : List (Chunk 20) := [
  w 20 2 0 580000 580001 2 65 ["Fs*7H4"],
  w 20 1 0 590000 590000 1 31 ["Xi$"],
  w 20 0 0 600000 600000 1 28 ["XjH"]]
private def chunks20:List (Chunk 20):=r20_0 ++ r20_1 ++ r20_2 ++ r20_3 ++ r20_4 ++ r20_5 ++ r20_6 ++ r20_7 ++ r20_8 ++ r20_9 ++ r20_10 ++ r20_11 ++ r20_12 ++ r20_13
def rows20:=rowsFrom chunks20

theorem good20 : ∀ r ∈ rows20,good 20 r=true:=rowsFrom_good chunks20

theorem sorted20 : rows20.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks20 0 (by decide +kernel)).1

theorem mass20 (i : Fin 57) :
    bandCount 20 (i.val:ℤ) 56 14≤(rows20.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks20).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 20 (j:ℤ) 56 14≤mass j chunks20))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total20 : (rows20.map (price 20)).sum = 140630 :=
  (total_eq chunks20).trans (by decide +kernel)



private def r21_0 : List (Chunk 21) := [
  w 21 56 0 70903 70903 1 102 [],
  w 21 55 0 80840 80902 2 204 [],
  w 21 54 0 90777 90902 4 405 ["*<J"],
  w 21 53 0 100714 100901 6 605 ["2%{LJ"]]

private def r21_1 : List (Chunk 21) := [
  w 21 52 0 110651 110901 9 901 ["0SL7Oij*R"],
  w 21 51 0 120588 120900 12 1196 ["4z.O93$Q/pE^ss"],
  w 21 50 0 130525 130900 16 1583 ["%2~k4~[n#bqNiLu&s522"],
  w 21 49 0 140462 140899 20 1969 ["#!FgUHsH-V%^)7c|n2xCnY=w@!B"]]

private def r21_2 : List (Chunk 21) := [
  w 21 48 0 150399 150899 24 2342 ["#1OT.-{<fZ~R-G9|1(i:A5I~H&Ar|u9vum*"],
  w 21 47 0 160336 160898 28 2716 ["CuhP>K29qxBpxAt}S-/IWRhjn'S8]N->(l'`-J)Gg"],
  w 21 46 0 170273 170898 32 3077 ["G'6h,n1ek`8om.U;9u:/G%&M'&JkEk7Gl>#-jO.+8lO`K]u}*"],
  w 21 45 0 180210 180897 36 3443 ["BQ`,6;,0w{V&[Q(}qY_gqEP6[kfjtfZA3&Vvi@r_N+VO]}vvmDuOjzHJ!"]]

private def r21_3 : List (Chunk 21) := [
  w 21 44 0 190147 190897 40 3795 [".;ST`U[)e=_w@*Jtf:t+%t{ifdhysMzNyb[mBugTs=Dr:;v}3}y:12sNtVa_Nrss"],
  w 21 43 0 200084 200896 44 4155 ["r]Huj1CxOe<I.-]gq4nXG8!X/Y5a0K<su_4?th{X^Q&*f9vP)WYNLNS:|KE>}~,Z","%s*|Y4R"],
  w 21 42 0 210021 210896 48 4502 ["_N'yGjif0eCdqjHWB^X4XC>vNgcgnd%<lJf+%wR1_d5^R/eCHiVLvlPB5-Yg_bv_","%zztW86~y3M`Pq3"],
  w 21 41 0 220020 220833 51 4757 ["@CR@44:K9QL>wh,=A-.v|0?psDenb{Zg48+.?LO)$[$_!`+>Cq%OuCcm!=_765e{","p'qLA6^!yq#>otNTLPi"]]

private def r21_4 : List (Chunk 21) := [
  w 21 40 0 230019 230832 54 4999 ["_Ci?0*>AUw7AlFsTxHv_W^?+i6&0/AP[4,X@p]&Ws+{p[$1$F[=:Ty)h[I[b'Z^6","%%N<vL&Rq,xUZHLr/l*^]Fa?Mj"],
  w 21 39 0 240018 240832 57 5232 ["3h*={HpIwA[hf-bKL2LI6B.r(EXZtIJo~Zy9B6cKI}$|?.4f'2P`{)7_y:GivPO_","-'#|b*9/:DXg$aV1<5Z=)%l`FXHE]M/H"],
  w 21 38 0 250017 250769 59 5373 ["gc6<;};xv{>g#r>(9zQ-@UzpGSQ7$@cp$kkH9lN)Twya}cRh6L}9)5'F(8z.X{g:","#5!'/p.<._IR+/mp[C4ulKhG8?ag=Ilg;l-j"],
  w 21 37 0 260016 260768 61 5509 ["[%_4jct7fIEE]:N|Bux(umF0W:+nVk.m#?*(q>Y.%QMLkz7$9txjw_':4]T]gF^6","(Ot~3SESl!@y*#.bc$q[0I;A{kV<c(8G-dc+fl-"]]

private def r21_5 : List (Chunk 21) := [
  w 21 36 0 270015 270768 63 5628 ["/&L[430IRdN1e(-IE!+lI_V7ST{RC;0o_Qx<t-Kn[T$Nh.)~Y!$m&8PaL2U5Y@to","$zS+glvM0@-B0Uh4'[/9^LA;P$nIklb4w`d}n8/plWf?&"],
  w 21 35 0 280014 280705 64 5671 ["h5f>n1q:=B)F:C0nj/F?gl5HJ?I(5vXPcbX]ssu5}-`Oz6Hnn6Kf&|X~lnf_SzU&","DSJPp@vBjHcw~A6&I`MO6Ws=-Q:4!H^6>`++e&hDj?c/r"],
  w 21 34 0 290013 290704 65 5697 ["pMDczS,e_A0E_pZZ}BJwX_g>1.aef$4?PH$.]yQVsp(+K2~b0~W5h:Cjow!m<tbw","99C6Wsh>GTqB<j#mtPCGx|i{ar,s)grgt$sf@;LpUDelQOr%"],
  w 21 33 0 300012 300704 66 5722 ["7vbPt9+w@JXpP1-XR9(}cWPVG9,FNwC-;yT2D;+8)jGYY$#Y9}A{9MuvPVDc`+fF","1a5Lf463n9NzN1fexxWs]C{E1Rp$0n`ByZn3.nWv_E$1dsny[sR"]]

private def r21_6 : List (Chunk 21) := [
  w 21 32 0 310011 310641 66 5659 ["0RfFz.J<toa2O`6xW<ciGqbm2.eo'myzFX@_2)t~}Q,X/.;_1bH:hKJ=<KI[tH%w","6[t=p{qn5lea:q:=-]@<Dc7Q24D:5i*'&+qv%64,Gy)F6qYao8K"],
  w 21 31 0 320010 320640 66 5599 ["$QAii9?HMz{g`'X>,'Ni[6;F,Rma0TO`chSL{.tRE1Pn!^,~=P~Oug#XZ??N_h>J","6[tE7FW25dIb&OpZ+!;@re{'z5hil[gh^|]_KB3p%/.e(ps;u;|"],
  w 21 30 0 330009 330640 66 5518 [":.<ZZ*'5mtqj,FOBHT2mrf,'Hbn}w}V'L,P6)E>}ZD(8Ya(]8@8'`}IU~3h?^0^V","#fs}uPaAN?U/y+i0~yeXe`hKC6L`QgQF*cdsyPS(&Bj:'.,Hi2kW?5"],
  w 21 29 0 340008 340577 65 5377 ["#UlZRjMqrbAHpBzBg|ZgO=T%zJ>Z{VJEB4ox~e;iG#@h3(7Xvjd>9~A/,TvnV/rw","%4HK]TTlKMtb,#*=0uPkz+?Xx&3=Qbeo[@I&)3nzCaS:$7?keGC"]]

private def r21_7 : List (Chunk 21) := [
  w 21 28 0 350007 350576 64 5215 ["?~EZQJ$j@>X)Aqe-gRNqQ_kHlPIcp0vG5<9<oXQ}Ayr{<Uqnm@wdoo&_.;w<lnnF","Flm?J!4?[+kX--xk9juP*FH]6W%.+cV%/Suw/`+f)LJxySKq<z"],
  w 21 27 0 360006 360576 63 5060 ["/'w8YcM,FG@fjk`3?]dlu1Ico8GDy$G{QjSZ5Xtcjw*f43'YYA1JTI5&f#,^CUR{","&YT@GEL<AOa~G.@t***}Eb!R)r0~EQx.IFn%YUh6ViO%Co[_l="],
  w 21 26 0 370005 370513 61 4821 ["~>_D`pnA.s*Bpku8GB]VY1~6Id9BUAPB>t%^y,LjmxHn`/M+z;v5i7Z{(HVj!e6Z","##og.^YO19B=]$+daV[+=SSk9|[e,/8X4|Jp6!S?&Z!NCr*"],
  w 21 25 0 380004 380512 59 4593 ["IwsI'm!iZEc{6O?d5_w,)hvHrkZ$9a+Px(p.|h'QrIp'9N4I|d/0k#v:zt=qaxBZ","3HcL%Uuzw=!}yuH3;9r/yH2|ykz;;aG_Qn1D`wC8(n4"]]

private def r21_8 : List (Chunk 21) := [
  w 21 24 0 390003 390512 57 4340 [">Ys`X3Vs(ZqM?s*~L`K5hqRun'pP5s;F~j+R~QE5a|eN?m$Bk{ERygaR({NT3!/>",";'Am^6p?G'CI(1A006QeFGOuDY$Mmv,cln$MV2u>z3"],
  w 21 23 0 400002 400449 54 4043 ["Nh|PPq>G),9aW86o.]yg:@i3{U.:jOUN'k/tLZ>d!UWJM'+G1f@>j`'-i'&KGq8!","*$Wp<DgpVuD!o(hWv<u<N5QLcHQ`so6x;XgA"],
  w 21 22 0 410001 410448 51 3721 [")8OX;JmRy&.)Y1*Y/EM~Y?$[-epqq'edo,>`EOU^6&q>[`3D::qlUoifjpkaMScZ","3.u-t}`aK|8@GgPwz$SV+ea>2go1Hy%="],
  w 21 21 0 420000 420448 48 3414 ["cf*[3.4f.~W*&e(-(e$~/4^`Rfl!e`Y`aP9L1tUtZ1X`dPNuMmHhoUf~#]mHe+<B","FZS%BUx/aL)-{!.aqU7*r~oTO/$&"]]

private def r21_9 : List (Chunk 21) := [
  w 21 20 0 430000 430385 44 3027 ["^?6ea2$+YG%n,!U&A'nxfJtFwnO2SdkYRM>m/<!gt=IE#u*#uHAQey`EB4E'}$NC","#J;-SsFIJ/tZ;<%Wcw{3gj"],
  w 21 19 0 440000 440384 40 2659 ["U?msJl{I%sHZl-]!@vBwEz>;3zv6SYFIn=-P6RT#zVdm!h)s|i2G>OuuFU5DNgHK","&UJ3pA#m$&3CWuD"],
  w 21 18 0 450000 450384 37 2364 ["Rg[2EQ1FbE{8E:%&Q/]BCWRC'u'-O~7I8F/@>9@sDi4wj`o1wN@3afLVrL5m!(0K","+fx{3~/P/Om"],
  w 21 17 0 460000 460321 33 2037 ["~=CGGJ@skC@9F'-Zk3}Xpv|72Wj<Qc2de]ETB6h`Ll,Rob0t1%bzr2QM7'QS0Sg3",".Ke"]]

private def r21_10 : List (Chunk 21) := [
  w 21 16 0 470000 470320 30 1779 ["+U)p(&$!J>i9<(-WpSh#/)FFsCJ>V)lZ!vh.v))+2~jD@o+/e)tNT)XLDVT4YO"],
  w 21 15 0 480000 480320 27 1536 ["6G`&5Z.C9UOwYA4%NvK%X>Bf:14!T$BsrtvwPq=cWT&2MF5:kt$#Q0WPoC"],
  w 21 14 0 490000 490257 24 1311 ["(8*>u>iu6vuB:J4:jE-r7utrqwFA3]~uCL?H(Kq([:6T#Qwk{nk#"],
  w 21 13 0 500000 500256 21 1101 ["&kNN0q]o1ZZ$t)'{]-XGwFJ-Plwtad8>t0YjKCTdZ/nk8{3"]]

private def r21_11 : List (Chunk 21) := [
  w 21 12 0 510000 510256 19 948 ["$M^(5p^+z0j3Nw]Y!Y~1Mu?zO](-*k(:<@Xw:+5WHsEi["],
  w 21 11 0 520000 520193 16 767 ["gxE*QMmt5u:]]F$nne[M$xN]&&{|`Qon*eFnDK"],
  w 21 10 0 530000 530192 14 639 [".l=c%#iI9z$^>+>:4$JBpIMAm`4HGod`Z3W"],
  w 21 9 0 540000 540192 12 521 ["$D^Q$NnFYpu[ewN65q$e[:-fn%AYsGMp"]]

private def r21_12 : List (Chunk 21) := [
  w 21 8 0 550000 550129 10 414 ["1t{FVjd@tN_m|R7?*Y_DKJ5P*U`"],
  w 21 7 0 560000 560128 8 316 ["#'Sj,!8(i/Y.*J@1|5't2L["],
  w 21 6 0 570000 570128 7 260 ["&E8plH?IW|Kz/'.]>`CJ}"],
  w 21 5 0 580000 580065 5 178 [",LJ?uu'-7-Z5XlP"]]

private def r21_13 : List (Chunk 21) := [
  w 21 4 0 590000 590064 4 134 ["1SJ_ufApRLN<"],
  w 21 3 0 600000 600064 3 94 ["9)aVC|tLD"],
  w 21 2 0 610000 610001 2 59 ["Ft$H1i"],
  w 21 1 0 620000 620000 1 28 ["XjH"]]

private def r21_14 : List (Chunk 21) := [
  w 21 0 0 630000 630000 1 25 ["Xkm"]]
private def chunks21:List (Chunk 21):=r21_0 ++ r21_1 ++ r21_2 ++ r21_3 ++ r21_4 ++ r21_5 ++ r21_6 ++ r21_7 ++ r21_8 ++ r21_9 ++ r21_10 ++ r21_11 ++ r21_12 ++ r21_13 ++ r21_14
def rows21:=rowsFrom chunks21

theorem good21 : ∀ r ∈ rows21,good 21 r=true:=rowsFrom_good chunks21

theorem sorted21 : rows21.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks21 0 (by decide +kernel)).1

theorem mass21 (i : Fin 57) :
    bandCount 21 (i.val:ℤ) 56 14≤(rows21.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks21).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 21 (j:ℤ) 56 14≤mass j chunks21))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total21 : (rows21.map (price 21)).sum = 157140 :=
  (total_eq chunks21).trans (by decide +kernel)



private def r22_0 : List (Chunk 22) := [
  w 22 56 0 100778 100903 4 407 [],
  w 22 55 0 110715 110902 6 607 ["3w>|g"],
  w 22 54 0 120652 120902 9 903 ["0+*V:U,3&"],
  w 22 53 0 130589 130901 12 1197 ["@A?M+?L~hWK3?#6"]]

private def r22_1 : List (Chunk 22) := [
  w 22 52 0 140526 140901 16 1585 ["%*.XwKbKr:}D_fvTfWzu{"],
  w 22 51 0 150463 150900 20 1970 ["9JND@x_LmBi+!)~1JrXPJfzw}i,mVcc"],
  w 22 50 0 160400 160900 25 2446 ["/6el9V-4iyt+<Fk3yYM3S#oQF<'bR^I[N~6B"],
  w 22 49 0 170337 170899 29 2816 ["#Vs)$kYE|->H:<I|Z1s+WjVEpX$iz48[]U[a4bt{cfZ>a]C&"]]

private def r22_2 : List (Chunk 22) := [
  w 22 48 0 180274 180899 34 3277 [",1RG;B6Bi&n-nS:IE^I:jiF!wod'czZ2kX,i03(rcYN>k9'N0aF7VkB"],
  w 22 47 0 190211 190898 38 3635 [")IX?T;U@z.?H#3QM~6QYPZ;UwR!K{```5_|.%2&_dznNj]bKR%gg&B#o&>SZ5rh&","="],
  w 22 46 0 200148 200898 43 4084 ["6x+rvw(FcwcvtyT<lS=I3fO(vTN@U?VGE.sNNeJjXhBh3|qBuDdNU`>xO/5{Rtpg","$Q)ZDd'4["],
  w 22 45 0 210085 210897 47 4433 ["D#9tlC6,U`&sl^-o$H180_Jt_+tHl^+^2UwFUZjAweKQ5^W>*;yHZ;iSoXGEMe&R","0)wMAo9[B4#ojVtQOw2&"]]

private def r22_3 : List (Chunk 22) := [
  w 22 44 0 220022 220897 52 4873 ["e)Gz!fs+5QTYiWTbG;;j#=+:_)]bAiQQiYs]hl4>fyx8A73VKm'pX^^oFdr9d@0{","5;;n9I=5IOrDu^8On}``diA}V"],
  w 22 43 0 230021 230896 55 5114 ["{y+6[/GMhJb/t4<3Mm<0ec}S)!H/CBid)GC#)k+n,kk$%V6^Ky#78N)8HaE?VAcs",",t.?Xh+pC,<+p[kg:c7_ykU21I~wSy|$N[MN"],
  w 22 42 0 240020 240896 59 5446 ["PlhYYCcYB-t_%:!G!!ZA_(OrS^wI],D(^`A/@y')*:@Fot&wP~|PM|~C;$}}/^s{","(2[n+#=tXq)S[?$j1.&h[eZRVd-H$5N|wgY'27/gJI"],
  w 22 41 0 250019 250833 61 5586 ["*p[NX*gPBtIsqxX#KAru<3K)WAiB/U#'N|s?QG2S94+xJ6+=iuC.a/X|861_H#$c","Zg15sPfJCuX},a-YJ,17<4Hcg,:`v!3wGk@Dvt!WV=^TtA;"]]

private def r22_4 : List (Chunk 22) := [
  w 22 40 0 260018 260832 64 5815 [".}(;`_*|j<MN0{/9mT<-}IgB1)xQidTTto)yZy[`qq4-g'7VH(DM(=hBaRAJ5R-w",";GuOU%f-xM,L@}D|uI%7-^;6X!KWDa&(>`^m1w;*nPL)`o~,J2m"],
  w 22 39 0 270017 270832 66 5936 ["[^,=qt9mF9X&*$wX~*_mJwf#5GJ|j%8#1t:v#kj_>g_jW<:un2'cnE)ZL2:SryHc","s4%>fi(5Id(D,{a9VeW*.L?:I>0#2iEI0_lM?dDnXXe+B8X]Ug.Rb&OshAt"],
  w 22 38 0 280016 280769 68 6068 ["F|>VB&nJXWsv1ZHo%G0Ds9tL^$~k1)pk*x?dy~&Dk$/])4;h4K5;=SBelwKsgFnw","#x}#P2cBlV}#<ibEPOP<1~e>xVb<6H-Nq]~iySxd}f4scN)lqFDiT9|9ZL%h0Y"],
  w 22 37 0 290015 290768 69 6093 ["Up}:OkWxLB}M'.#m&85x)Ldpo?<T$!`bNquR4S?pb~E?PQJw@+mN{EH64Yxz=Je2","8/Pr@Lbm8XAh)>+.`H:0O2b=SksZw;:,}Zve(3(1CkWO$FGRlYTB_%&H8J0*#h3w","#"]]

private def r22_5 : List (Chunk 22) := [
  w 22 36 0 300014 300768 71 6206 ["%P'&)s5_neK5]ooWOw,DCNHg?Ly'`Vir+>.`MP={Sy'X`APE0d1`-#8K*!BxJtX2","T01~!Nls0]3RncM,y7vkBrN'(^Yz$oHLsN;A-3sZvW|S*d8a}ZV<XA.u{P.$`92c","AqB!R"],
  w 22 35 0 310013 310705 71 6142 ["'I6f)-JDb(8}OsX->e!{ZrHU)i+XS?0P5a1-8z{+,cp<4f2~>sblJVe2(YAYC=*Z",",@%'7D(b;}Z(LRmG*A~-.Q;![XI35CejC-a[;UH:2w_JifCIb~(Q1i}ZnY8:w@Z_","5WF5Z"],
  w 22 34 0 320012 320704 72 6163 ["iH=(Y/wKU@^)^NdE9MK|{3Hffl#HW7hgUsDS-w-mHPpX'TP=W)I>ML1nHC.rhS::","}ve7(!/.%$b'IU>$K<40/#]aEBqDm{6>>Y{1A(Ih6Mc]Qh/=Iz-V{#v.z-mqAq^3","&Q9^23Z"],
  w 22 33 0 330011 330704 72 6084 ["Mh<e!l?GP}7`3yU)NzG}/q-er/?!|_rb$71P=$tA9r/jOaf0ky$^.be)4}5gVQzw","cL&_A)KSl@DyOtDbW/1.Lkh*t6F`]zqX=%w']`+@Sg`sZlSQH!M^zj5TE7D}Xw%G","zK,w(y!Yl"]]

private def r22_6 : List (Chunk 22) := [
  w 22 32 0 340010 340641 72 6020 ["Gk%^xvRz]AzkSt2gyO$R,%=0$zHfh0^jILgH;^*Y'$eYa,04Q8G@B:/OvMXVtg)&","g`)EJr7D.Q8yDl@%-lM|xE0R<WsHKr-s^b=y_S<~@C&v*KYA,s2ch7;QHZ;Y(}xv","/6L7@/fu"],
  w 22 31 0 350009 350640 71 5857 ["*Km6hYLt#(CxjAl;n<j=NZ.bVG}gN)T3uXNNZr%#$eX%H|~jg+:P%q%{.,Z?]UB{","Jzb/9shJp,c[6Mt=xx~yhe+Y>,%,L+sziP:OAn%l)t~/il9OSV7KDt<_o3;[5kwx","#VtMHSiD"],
  w 22 30 0 360008 360640 71 5778 ["|3?0/gunK/eEjw=PPjBp6Y.SX`alVEiMc_=zC>~wIaep#K0]wZI$gv'A~fJYb?Oo","0|PvA:YVEgzgO(W7&$;>uo,_^IYTM]R(#a{Mm}P^0sW*#9Y5|R<pww<,)/w`K@wk","0G#y^&2`6"],
  w 22 29 0 370007 370577 69 5538 ["DBj)ON'a;dt*dZpT}Rs[Dak]zWqn7TgaUp)^@uB1`|tSVcJS6vPH}A&tG&PUnA0s","WLvEEJ.LdvN`4ZV4#jFvsZ~c798{4E<=FE3.T6Gw#XY+k9$UAcWi>f[Xm>4xd{9i","qk3bE"]]

private def r22_7 : List (Chunk 22) := [
  w 22 28 0 380006 380576 68 5379 ["ma/5V0fV@/bC!C.AVpP%}MLK'w:aCK%[5jGycv{~K6H`|hfelJ*T7~G(wV<!H#:{","925`*-IvPIg*Py;2,Nq9~a-|tjQXpN4},Ahoh+K|<>P+$g<-*ReRLB6~G^J4Ishm","%D<e"],
  w 22 27 0 390005 390576 66 5128 ["xGf1zr0`fwumI:l3K|ar&HHM3{.o+:K6Bh?_@;i$HIcVZ9k^[PnZ6o$TdYDU^rIw",">y|f;%W{q]rF3fxIe)j?/~o<jy-Jo'8;r#51jCb*[G^M0kH3^27oG>}s1`qpXHm'","5dc"],
  w 22 26 0 400004 400513 64 4896 ["fbT2NsYtx,WpiZ$t:J*w/$c)uUsPAPVO2]J}<U3dIKU=VGFKW]VKgl{(YVIF(CK_","A?JOUbQ*8v2f]T2%Gr~/Dh:ZTb~~XV{A0G&H5U#'e#X:Up9dhvlx3p^>-ie5eP"],
  w 22 25 0 410003 410512 61 4573 ["B4m?o,]`,8tv538]EdA|^yYNbZo:cg^WF{80c]K%AX.r#8L'<Q)[<I;^&`F$d1$B","bfM1I+SFSOV).][brsI!I--h$gP<D~C(G_blh6|`|#}VuSFL4t|`GMSe8u"]]

private def r22_8 : List (Chunk 22) := [
  w 22 24 0 420002 420512 59 4330 ["&|jr?(/+Dct@Ci|PCUM]~Pn8[7o7+K?3g;J4CrhsN^f##?Drkt}TIP,SJC/OMCFk","#fEnZ&ruUl*rIq<xx6c[g].jJ?CsGX8F'R4>6mW+wC>A:^h2~g~@01.um"],
  w 22 23 0 430001 430449 55 3942 ["|}WYiaF/K}w9G{/:3o%3r.K+Cx#w1PTn_7KH>*,/Hk)+fE`0=qzx|Dc{)3oX0;oJ","#3r8ha(lkPlI4l,P*K@);/'e5*}'e%1u]$Lu'P($>9;l,uhK7i"],
  w 22 22 0 440000 440448 52 3631 ["s2fE8SDj(Ibt4~E+%-*V1yV`D62C;&3JYEc%{UEnwB]XV!?Oiq]w*?ND|C*(73e!","sBK0Dy-oW/PEBa&ghV*ip$sD{fmt/zI.Ov,p9VVb8q%g"],
  w 22 21 0 450000 450448 48 3236 ["lret;|T^eQEeV;Q#05]2wy,)kQJ8h[2<5pNg(eS7AthD7/,=}v(U[mY8XhW%,P6#","#>?|Fszuy0zE)/^(f{;hoLaTa$?<~8Ex0v>D0%3ZE"]]

private def r22_9 : List (Chunk 22) := [
  w 22 20 0 460000 460385 44 2864 ["9u[kK=-z[Y)X5k~)B4n=Rsi%[,sWj.91,-pEcQ4&W_h1c*xYMa8^0lY2VT%hSFYp",";dFL<C*wgQ$Iy:tv@z6zvD#bGi8f1%Y'"],
  w 22 19 0 470000 470384 40 2511 ["EQ(l@G%o~b0M$!XY,N4mAg&03tf#@d=0^Pq+D{Z]9Ms<%]@j35c9h{Z%VvJFI1%p","pf!Ds<n*'](m~S~JRiQM'@ZpY"],
  w 22 18 0 480000 480384 37 2230 ["[y$CNVKze8xR3)*s1DO(!(Dq$3MIGd,2=0pJ@V?%,6lYm{I`;Ey-4AE}O#k+AcbO","-P2L->iYIb/HS`%Y25y8tT"],
  w 22 17 0 490000 490321 33 1918 ["n=TC~$PbY0{s(1hDUy]uRS(apn^U9O6(/${6/A.O0a]bTwAn5$dTR?3|:_WJmGH;","$0yBOh^FW%aApM"]]

private def r22_10 : List (Chunk 22) := [
  w 22 16 0 500000 500320 30 1671 ["e8q,Ib3DFP;EN%,xF{2l.Qx8l8(J`b.8$0'2}qCg'SDN@z;$<sKw,rz:EXZ+{p`x","#WT1PLNQp"],
  w 22 15 0 510000 510320 27 1442 ["HHa^MDJ;DouhF5G[kB{9z.~8TZN&|LQsXz2(Eu/K#bth:-/ITmUM>:^EtX6e;M|G","*`$6"],
  w 22 14 0 520000 520257 24 1228 ["}-/~0_o.PoUZmv!e/=5.y*?!C2L7yYm?u,~/(`hq*$lUky(Z?kEJWfE4`c2<9O"],
  w 22 13 0 530000 530256 21 1029 ["9c7Uos~OU-tD^!B/USic]T_f1hS'dk^r,wFG}'o+9{`)mib$e2-`Sd~/"]]

private def r22_11 : List (Chunk 22) := [
  w 22 12 0 540000 540256 19 886 ["Dewov`@G6]Jrrz7Gf%q_SQ}E@V;<Nr9Stg)j'0m!X}x><fs|M)IOW"],
  w 22 11 0 550000 550193 16 715 ["#;DAC($35S#Sg,+KJ_q9XqJ,=9GbY$_t,{(D!I/ZpIA,krO"],
  w 22 10 0 560000 560192 14 594 [")M1,n7~*&ocA(4EvO]QlJ0h4f(SZPEwBh_&~6c.v~O"],
  w 22 9 0 570000 570192 12 485 ["&>@j>uHxoOQ:[<o9~11y';o}@IQNu6ZkRO-zSh"]]

private def r22_12 : List (Chunk 22) := [
  w 22 8 0 580000 580129 10 384 ["%5v8:=BA|tgggs>EvR>!>8wu#1P+*{W$+"],
  w 22 7 0 590000 590128 8 292 ["(i_pD*7^R^74K0QOK}O/L]#5@aD"],
  w 22 6 0 600000 600128 7 241 ["#$GB?ZU:<Dq'q6X+M$fGhHYW0"],
  w 22 5 0 610000 610065 5 164 ["9>dT3YZyA2gM7U^'`0"]]

private def r22_13 : List (Chunk 22) := [
  w 22 4 0 620000 620064 4 122 ["-s0)0xs^!?7y/a"],
  w 22 3 0 630000 630064 3 87 ["#yaQ%n%`@#pq"],
  w 22 2 0 640000 640001 2 54 ["=RLb;TnX"],
  w 22 1 0 650000 650000 1 25 ["0#k="]]

private def r22_14 : List (Chunk 22) := [
  w 22 0 0 660000 660000 1 24 ["#_Ha~"]]
private def chunks22:List (Chunk 22):=r22_0 ++ r22_1 ++ r22_2 ++ r22_3 ++ r22_4 ++ r22_5 ++ r22_6 ++ r22_7 ++ r22_8 ++ r22_9 ++ r22_10 ++ r22_11 ++ r22_12 ++ r22_13 ++ r22_14
def rows22:=rowsFrom chunks22

theorem good22 : ∀ r ∈ rows22,good 22 r=true:=rowsFrom_good chunks22

theorem sorted22 : rows22.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks22 0 (by decide +kernel)).1

theorem mass22 (i : Fin 57) :
    bandCount 22 (i.val:ℤ) 56 14≤(rows22.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks22).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 22 (j:ℤ) 56 14≤mass j chunks22))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total22 : (rows22.map (price 22)).sum = 174160 :=
  (total_eq chunks22).trans (by decide +kernel)



private def r23_0 : List (Chunk 23) := [
  w 23 56 0 130653 130903 9 913 [],
  w 23 55 0 140590 140902 12 1205 ["%xiHF9eKFI$os"],
  w 23 54 0 150527 150902 16 1592 ["$)^2_OA[?%1(j}|Cp_JB"],
  w 23 53 0 160464 160901 20 1977 ["9J%W`7e(4RD&L?Cw1R!42x?SkgBzm@{"]]

private def r23_1 : List (Chunk 23) := [
  w 23 52 0 170401 170901 25 2451 ["j9bF}z5j>+PksUyj&~Y@`Q7Ah#3Oi(,ax[L[F"],
  w 23 51 0 180338 180900 30 2924 ["8bmkA^wU[Q_RpbLaOIaDNH[/dTh83{-$AdAj?%-D[[*2@rZen(=)R2"],
  w 23 50 0 190275 190900 35 3381 ["(bN]>#.Yt+/p.2u>D%S(!ao/ck4kKB!k{z(K)D)2+d9'rQX#^5_9EJ#TAgB"],
  w 23 49 0 200212 200899 40 3838 ["._Met.+huuggDd_-Y:=Vb;4E42yNIdOq[I1Kp[GsH@uHJ%@KN|=)-wi#Vh?7.|tw",")z4~KaXmyHh("]]

private def r23_2 : List (Chunk 23) := [
  w 23 48 0 210149 210899 45 4280 [")2]?__olz!ad=6C5r]0Rt3KUx5+G[y?!;]pyP&VibEL,N];Jt5t8_g^Cb@|rmq)>","#&}XUG&MIs#.{%xg6{PKm"],
  w 23 47 0 220086 220898 50 4725 ["~/x#PwjW3+)l:{S9o4R;j<=F'I?/[z!@#.%3x9%[%jH1e{RM~UKK;nPx]'nr%h}:","#!$l}93#eED@5-(w=En4>9R!7B.p@27AU"],
  w 23 46 0 230023 230898 55 5155 ["Qcj,}$1VO@Ww8h>L[lj6]x&Sa4,AC|{,*ZtG5u<yaj2y@!3]*4qUZV_Hrq}$Z9Gg","4#|+j.gdiN%(NnMUb>T0P4830TaO=c3)?Q(DuQWNL"],
  w 23 45 0 240022 240897 59 5488 ["ss~~^~CfbG({EX@[]Xa/'{1]T!s-c2p#')0*lW4oDS>5e^g#THJE.k$}K#6fp=u{","-5EIehmFH#<zi6ovk+XKr}hmHUi)/dUXjgb5DYu(hxan!9MXA<H[j(5"]]

private def r23_3 : List (Chunk 23) := [
  w 23 44 0 250021 250897 63 5807 ["J~(.$Nu#NsyC0u%~s`Jykfa'(H#SS&='j^[3$u8|sGx3MS[Ra@@i+q,3<ul#oTG>","U0a^dE9+.UI+b$(!xJ]gz8xd4CK:>J6Iy4;W)(|%V3{[g^E`?2uC'9>5$M"],
  w 23 43 0 260020 260896 66 6036 ["M:Y@m,ZEOc}!b=)McSUPQ%_I,baGO;!pu`J>_Txor!'_xQk*`-r%7G4ml4{MY<uR","b&jK't[gnr;:(|~G,=M%+'&L7%E%ERRHt#R?MnJl;q+59[$PIQBM1$8Ce|f~Bl~Y","#)Y'E(l"],
  w 23 42 0 270019 270896 69 6250 ["Y0TveZI``Bc6Jjtp8*{3AbdRZdEZPFFdl}dL4Su}zbQdu9q?$$ptR>>&f_s0sb7.","+*k=$Zrh>T>]aM45>rh@{qDgU0@LBjgxf35;|w0AoDCbq!rYcW|g_kGCDWLjGpB*","$.65I185zF."],
  w 23 41 0 280018 280833 71 6380 [")f,<a^0_gZO.I6]He<~Rm-08NKW6@;$BDUfT3iqP~VTYCJ1tt%AbjdO>z<S'z`?.","*O=t6fH&MDk{?NpI?hMoiKNmN/%8Kpgw1Y}e?arbb=A7}yxE5Q#:DnZQCI(vx=us","*EY'S5f#zi}<D+y"]]

private def r23_4 : List (Chunk 23) := [
  w 23 40 0 290017 290832 73 6496 ["x4g)mAs/y'rcd6D9yPKSkJu8L^5ON:U}SZYw<U(2JVSm5YV#)#Z.KR.~7t)LmVHB","NJE9zlq[&:@KhPIy19aAj6[-}t5&nSrJLHZ7FUZ}E=!6=u0{jY'f0}#FZJ3+dL&U","M3<XU_0J'nOGC}C[FP"],
  w 23 39 0 300016 300832 75 6609 ["hd<Xq1u/?JWAcp$-P3^0k(xQ]TX#,W1K;$~25z>R*mP%&{@?mfw=,_!bGD!TB^pN","pK@A(tZ&R3KjtLg.Rpnwh-s/Ul7ArjVt%e/&tc#=jyfZ^3/8PAO(ZJnlQU%6Rwod","&-/5iP|lQv=dHxO;W?5O9w>g8l8'"],
  w 23 38 0 310015 310769 76 6629 ["kNV$Pi#0xwMTQONak]p%5]QOiv?M6tZ/)qh+aIfvn0n!$vma/]0%08ER8PfWr?UF","]{;7kUf*Nji7@LT/`Pz(WWBVd78+kR*9M'Wy$ndQI;*xN8r#z@[45,JRGXFMRpn%","#hz%1leQunh>/[+x%K3BDwY<d"],
  w 23 37 0 320014 320768 77 6652 ["p8AU_yp2|?'i}:hpbq-[RAtx=c6puU'W/sbU|>&-4y9^wBQS,HGS=eBl9>nzAjeB","v.{j])dQ:S-)#;YU7XlM1O`$/JufL0)VXLQdpDMj4a{?<M|i69iXmDY'dv2QIJO&","fays)S5}&JidMV4&HU5s_C<{.9w=9-~e"]]

private def r23_5 : List (Chunk 23) := [
  w 23 36 0 330013 330768 78 6655 [")p>.s~C5plwrXVjo,]XtNA=36$>[!ugdmH{lJhnkDfKwEI(2[,b@>>%l[],6=@<2","gJMxic`[-V.<[@+6/bvY@MG=H}{;E+zkAUzb5xa?&xn'bdX)MMWn@r:V0L5(jr?s","(U<^lx9h20*k,a}2Ygv#!IDj3Gz3QHr,b_(V[/"],
  w 23 35 0 340012 340705 78 6589 ["~D%%Zy/Ko.O]6)b5BD;tb&!CXiAz1(hK{t$[H'7QebPx8FR4$_-G]FR{Jx~?BNs*","1_olB'}P],!<z]o@N9RyedUt97y>LnX^wo/6E/@!B_7Z_XREw'as7j!K'QOJ#rH{","(4-y):KtW?/<Sx@<h.7GvSPvI{Mh7-Ud<"],
  w 23 34 0 350011 350704 78 6506 ["G@OZcH>om/01417}BZJ,{KfaJ9q|){XXD'3`H+Z1d[=X?KVtVYIqs?`0IMT8!&(B","x{C>mq81NL^Ws>&dq@vHL&K`fOf7tKi&{-3e0[Ou.CF*g&x[vK]l`$jl*mGvQc)5","#E4]ad|:J/H7!1wd(nXg*7*9k>?fz]c^_J@{n"],
  w 23 33 0 360010 360704 78 6427 ["s/+9X`L@s_}kIeb7C}%]=:@g[Mo?5HA3FQ5/qYm^%mj48OH?nS5W7Y@`&=h6St::","Y$,BP%/mjZF]s//]ZDp+;)-G/Mjrux*@lbFl~K_`<b)ruCNfJHPl@pOp;}IsXWOg","<hF]zpeU3{d~Q5zf$2-_NQG/ex@kgREvc^yHv}S"]]

private def r23_6 : List (Chunk 23) := [
  w 23 32 0 370009 370641 77 6259 ["BY>Dd4JsWeKq,(#O/={v>D2elbP?L/~x(Dq360>>AcEJr>tKH3Jpx=4Q5Q(nL+J:","?Ob'1L=<1Js['u{`0oK#.d{S2tY<j#M<@8`/aQnm^?e>bi-_wR5'+l3dkTfXuc*9","$0u+a?wl1,{C}L,`78ep`y9:KOTV$Yn]FH"],
  w 23 31 0 380008 380640 76 6102 ["2)<,!w@H&FJ2z[*VuK?7^DV[EC6gBLfFgDZ{dr~R+E3^~6+qHT[uno?O`97p_j5g","R6&Z=l[Z&]-0CP6Ab?a8t-7:UR&/7{Y=r#p,S>pcu&2^u|c+3O#1)ou`^uVFH*8.","dwCmGpRxL{@!Mr@(<|Oy^4Y/0e{WX?4?5L"],
  w 23 30 0 390007 390640 75 5921 ["Hi&3O>%[H!Lo4vPLCk4M{gYz2,)y4-h9!dx<9;'?Yp6XbRs=`{bAXT7V.Bp9|e{*","9-`p|wZa8>m&@iAhyN-EMv0{-c|L+TZk9X+-/&Bw2woe`YSXF[.vZ|7E^Td@^GeU","$;NlH29hYeuP?O7QYo)|K|0c<w_Mpzi4_aJj:"],
  w 23 29 0 400006 400577 73 5687 ["X4~UrpxFL!YS#iI?b/T>RBxV69eOz+%4QKiB-3ma2LwM[kSXG_@jV<nQDvJ1?^Yw","C2Qnygwa,e3-*ca9For>k'Y9SM*Pun]iw_aQLI67I'c3U5J*)knxMMFlzHd5ax>y","5.-ddCm}}nBLZw*{4MlE9-oebsP4"]]

private def r23_7 : List (Chunk 23) := [
  w 23 28 0 410005 410576 71 5432 [".c_Mi9F[)?js(tWB5U:}mT|wNH4_*F3:ODW~.tj9`-2Q5%].?E9NEWgCUs}/:o/>","4>R#8b^UtVd-@NheyR@H9/[+Cg88zey;:4=X[yiqJr/<f4N4n7d/=sEl4}^N]]+Q","kxG}4XyH0l/NDJixjXPCp~c%u^7t"],
  w 23 27 0 420004 420576 69 5189 ["6`SZU4lP@nD?.8YUyi93H@xagp$Cua_0B;j^z!Bv4Zvs/RkRoc|u%*7a7oh&m6us","F,UP-bPb3cgVtE1QUH|k7>1|gG/0{Y7]&]t@Ye#%!+bq?XMYab8w4Cb<jq`Mr5+W","&[{X9IGa{1^KAY%LJL+7=0}j-_,l"],
  w 23 26 0 430003 430513 66 4861 ["pS6u&XLTm0occbvy`|xbLSW5r.-b5$j!ru_CL{nmE}^Tp3G=j2ct*iw+x&+Av40B","D0F.e0cehfNzO?$,T%L2a8gcbDl1O01-Fn>L&cT9Y}A_5(>/M~aXGh6v-,=el5!m","%xMmZW`}>))LtHu7D_Y"],
  w 23 25 0 440002 440512 63 4552 ["}L^YjHmK7zCBg'fN}IDC/kVT^#NI{Gy`3Ga66`!:+*zfSD_m'o%JytR7#cXgpl-g","=jsZ'Ak!@`>dIxl2S__Z;Z)T79HN>`^H3Q,yXCV8D#mO72s!)/oHXJU6|3{),$1%","88m)q8wkfTmq0ze/"]]

private def r23_8 : List (Chunk 23) := [
  w 23 24 0 450001 450512 60 4215 ["'*E=QQ#v--y|UDZqp,5bj+O!`[Q}F$/X^F=dmU&ZJPS6*>lOoB$]PM.6_.,u}1FJ","w<YdsWLJ0SKeu|x~1weZbTb.CyYb5,wc%t84Y0;;[N<Ip);StSK]Tm4&tlvv]JYq","5ABb/C1aKCsdqx~"],
  w 23 23 0 460000 460449 56 3841 ["h(.+A=O.C[wjCWBI?LsuxEfaum3*f@Xc~-vPs)B_FxT)Kc@x*_A.uY}=uY5;MG]B","Ktto>Wr7T[F3c5wqbg-3fh,^^+i[sV=;RmjBF`rjJZXNw!QzePdKeasWrk[IK#b_","6M4"],
  w 23 22 0 470000 470448 52 3442 ["%}*JUm;UqQ.6$+lo[;yJvPX}bfxT]l|a{|6C:vQjvIQBL9H,A:WGMn+<|gLry,};","0O,)Pca{$S'ja[@h<f3oTr[L);]u23>h+`1Zvcpt-Y<FG9l#.uES&TS)e%{s|IC*"],
  w 23 21 0 480000 480448 48 3063 ["K1|V,H~;}U=jZSI>ALO'W$#4P1:H$qD!B~ntXn.EV@M'GO_zy;{zS0-ELF~z&GMp",")l%Iik'0patP2Oy,mF4g88,-*iendP7Jiwmuee,Y^kiD}WYf_^le[)K[J^H"]]

private def r23_9 : List (Chunk 23) := [
  w 23 20 0 490000 490385 44 2705 ["KJ3aL`'AVB+LIE+4W[ZYT9)ohi`?gt$~p5w]DU>h0K(UTY._|m~jIz<eVxsRN-P|","5lIt-o!5+fT(Hq>!q#2ktS9uBMr&9@8[fbhZn>NdgT1*<9>:"],
  w 23 19 0 500000 500384 40 2370 ["iXix,98X*nB4oo)3vE@_0SPNXMFG2t/4/0?!:zqgD=.7bl2:z_)t)s1{xw$SJBhh","#mTKDeZwkJ;:=5T/Jv~saUL(m/q-<N5fy0Xl^n9P04G"],
  w 23 18 0 510000 510384 37 2101 ["O).V8uZ`vVg*7Y&Gzclu3:O5c>xqqv;&%yk$S8Zs$XC%'`'VFjGQ!o@`EYl>46HK",":]>@xfcvL,BKEi~G8J)zuI+I5BCP*j-ho[w:cF?"],
  w 23 17 0 520000 520321 33 1803 ["'dn)I9/k.4s$H%9*oszfA[96(s@$J(qnD]_N*2V:4aTgVM.(J&A}8D['qEcUtgT;","Y&n_6.8z#t@z?dxq`,bEwgC6X8yJ"]]

private def r23_10 : List (Chunk 23) := [
  w 23 16 0 530000 530320 30 1570 ["<,,OTJ:q{v(XW1Z1DpN$#?WHjrt|v'3Hb*Tp(QVl`im/xFU|=]NblNzC74Sqq^lG","J;L|Nm)9_>0~$*R9_6FE`=d"],
  w 23 15 0 540000 540320 27 1353 ["Z!h.bN.,hO6P)9u,KXJZkX[5Gsqu$ZM^iNmYH=IKNICL$=fPzF^Luy*?Jlf{NJgC","(`NA!L=-=t&1jX1W5mc7"],
  w 23 14 0 550000 550257 24 1149 [";*3)~9ylSrE!{yrp/:Nnl5SQ[.2eC[xyAtRz=}tk?ynjiqtz5&P9;-~rl:x&C}*t","%6?sS`Tm>?N"],
  w 23 13 0 560000 560256 21 963 ["jgTQ9HVFS0#TODJ?n:dG'`3Y7Ran+C?c%/}5;n=xj6eaG5M7>Tiy|v&lG=`G9m]|","pwhB"]]

private def r23_11 : List (Chunk 23) := [
  w 23 12 0 570000 570256 19 828 ["/7%])qKXx>E,UXUM*a'`imp{ppI&tuFqZX5JwQ>QNb9q_fCj#8vNb0W1NS;R`9J#","#8"],
  w 23 11 0 580000 580193 16 666 ["SpVeP@9q3@`YWG^[zMUS;>P}rU+im5}Bg(|J>#?kEHMt*Fw^lj>iqT?'"],
  w 23 10 0 590000 590192 14 554 ["#.ru7WSHFW|O'/5U6/bliw?k5)~8L=s#^E.ga.+>O2V/Y=zN#1?"],
  w 23 9 0 600000 600192 12 452 ["#o8v$^-%uV>Nbs~}`j:!r6/5nMFTNo?t)NAJ}}eiZ&IJS3+'"]]

private def r23_12 : List (Chunk 23) := [
  w 23 8 0 610000 610129 10 356 ["'oUe!7,1P^l[DM%HrBLmMW4LF]r`dU<Z`!mwuDT"],
  w 23 7 0 620000 620128 8 272 [".;(-7(%v:elz4j`?[KK4'.500$AkhFy&]"],
  w 23 6 0 630000 630128 7 224 ["#r.8!y.lzBusj=y_6HZ1`k!NgduL;zX"],
  w 23 5 0 640000 640065 5 151 ["'L:D(TI|N}&>9hf@L{@xWP"]]

private def r23_13 : List (Chunk 23) := [
  w 23 4 0 650000 650064 4 114 ["$jibf,?c1u~5A{gf98"],
  w 23 3 0 660000 660064 3 81 ["KoYH4Q!'{)vcyPE"],
  w 23 2 0 670000 670001 2 50 ["oXjW|lNN^"],
  w 23 1 0 680000 680000 1 24 ["I!x7J"]]

private def r23_14 : List (Chunk 23) := [
  w 23 0 0 690000 690000 1 23 ["#_DpY"]]
private def chunks23:List (Chunk 23):=r23_0 ++ r23_1 ++ r23_2 ++ r23_3 ++ r23_4 ++ r23_5 ++ r23_6 ++ r23_7 ++ r23_8 ++ r23_9 ++ r23_10 ++ r23_11 ++ r23_12 ++ r23_13 ++ r23_14
def rows23:=rowsFrom chunks23

theorem good23 : ∀ r ∈ rows23,good 23 r=true:=rowsFrom_good chunks23

theorem sorted23 : rows23.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks23 0 (by decide +kernel)).1

theorem mass23 (i : Fin 57) :
    bandCount 23 (i.val:ℤ) 56 14≤(rows23.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks23).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 23 (j:ℤ) 56 14≤mass j chunks23))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total23 : (rows23.map (price 23)).sum = 191338 :=
  (total_eq chunks23).trans (by decide +kernel)



private def r24_0 : List (Chunk 24) := [
  w 24 56 0 160528 160903 16 1618 [],
  w 24 55 0 170465 170902 20 1995 ["&^NY[/KMa,M=/YiYh`']Yb:R"],
  w 24 54 0 180402 180902 25 2469 [".oW}y>&3msD%ffHFd}*L#jT4(IJU8(xc{|GF"],
  w 24 53 0 190339 190901 30 2939 ["$yN%S,eg?cs+&oOY>%Io5oo&AMhjGSj}A8hY#10or7!Nd@9KtPa:"]]

private def r24_1 : List (Chunk 24) := [
  w 24 52 0 200276 200901 36 3498 ["GaJIJ#<K%r2m/VKM_|+nz&#xKWuuYtnNcHG#o=Y2aossS}k=ry9I=YZ;%C&_=07w","#"],
  w 24 51 0 210213 210900 41 3950 ["/Bcg~r9WL*iB6K4e7rgi*|LUmO|[71.0A4v57o8l%.sIsVF`-g~,j^{v{NTjlGpg","#:$e3~JbT{7II3A>aw:"],
  w 24 50 0 220150 220900 47 4491 ["](t;uHW5tvCQbm*L5Bhc9Ls[`G3J>5Hz&(aQiTRe2AA5ERjYI+<J8VT<vHL/_~Wg","2HK{@goR[/T0}I}[M``iGwTQ"],
  w 24 49 0 230087 230899 52 4928 ["Jj`LYo0e`r{@yH>047sMEr8kBWLGFke29-I02G]f[Q78wJmsR-8<2988r{GP;|uZ","=!~}'z:IqwCz9+[hoj0aN21!M:S'wz4>F>~p3SuZK>v"]]

private def r24_2 : List (Chunk 24) := [
  w 24 48 0 240024 240899 58 5453 ["[9e6*md3P%:d?j,wQ};sy&:XTR*.rIEs=q!`L)J<ep0dM4z{B,(|Q+=[AG6F>1ss","%QgY!Vzb4L6m.OEK.uz~r3prPxT5D'}]H!Xt#rfRqR~!DDMj8]=6PLXa"],
  w 24 47 0 250023 250898 62 5776 ["1)xeSv&^71F+EaZ[W*Nm*jdH{ykTrfI7^4FWS|{SpUDZ9(>gCwNPx[~{Jl`^?`jN","hsr+)}X+iV3@ZR3Q|W<,|Z!uoE'wpN47CgR3Xuq_Y648@kg`GDgoi;cyxYjVBv11","$5n<i"],
  w 24 46 0 260022 260898 67 6187 ["v>'V+a<vn{^x77NH0*[>fsDn`u*o&TC''}P'7>ztrx1nc)ngx)@U5S*ZzwOw42Yg","G|H1VN%?gY*'y71aQi#Rs5GaEe`1{Ay69197[jen8O=u([UsN$n;fE~DM)p7bDC^","$<+Asi&)LLgyEDV:"],
  w 24 45 0 270021 270897 70 6402 ["lv]J1'pH%hzzZe(]s<'zzk0StjkBR<j{6_eP1KR<h~{4YNRk@RXWpwoARqfiwDX!","_J%#]+7o^4.gQV!^16y<<].ionfscE]Be~Hh2Yb]a'7<cb]l?E^b.lGLs'HM_12X","ern>^Dc]:^vS5NW3f$}VXI7;;+u!hr"]]

private def r24_3 : List (Chunk 24) := [
  w 24 44 0 280020 280897 74 6706 ["RTiy!ywDx5#6hOZ*m*%F|eXUYv;X:f~4IA'w}2M<uFPF'wJ?L.g(@e:/pT)AhLqB","]Nt+U8@v}dKtG;FhUNO]h,Y|TM`ti^hx$0>)bgq^=eidwryD0)x/58G?Mi[c8M3/","$Q_/ST7AkwM8hVX(/V)?I8b8~Rfj3SQV<`"],
  w 24 43 0 290019 290896 76 6820 ["&>(q^|l_6[V,Gv:?uk$4qNUBVZj0sK)M8qqzyfs`>WR5ckeyti*tpQP_:Z*4/IU&","yR-7~=4z9$+mVq2doyBk]b5*LE'E<D/w|=/-C0+*;K(`zU2KFaO5fNIE/0*(^nJk","<b3c1H:MR/Qm5xr/Gyy#Q8PiI)ahN@Qek$QPa5G|+&mC"],
  w 24 42 0 300018 300896 79 7022 ["|LHZKsV?h8ZP1|pB.TY[54!us}ChQ41.-u9^#_1nb9A{~zZfB{bUy]fcJV)h?lng","j^Vw'qr,g;9LS;T>)Rek-0HfZE_HAe5eA~fIR>dKIC_88uWtt.y)Q<XIEWk=yUNQ","%VYx:&3kZb|O}a/iqU_l;p&yzdZ||p6l?kaPY]^LonCrDXo6d%U"],
  w 24 41 0 310017 310833 80 7041 ["u201Lvwda2r9/B;yjVy.i5gs4oa>=i_>dEx8&ZSEe*VD9-R/w2C'sXVM71y+v3|_","8IF$7Q3iRjKo%DX2)eT=/s|?I1SdS;L1a;/vz!]$4Q'%;!J=jmnnUKlr/X*XK954","jxr3|VJ^K^jqTS/y{K.T,(]S[rN`GH4rxm^:^lMtgj`R52aB<Azo("]]

private def r24_4 : List (Chunk 24) := [
  w 24 40 0 320016 320832 82 7148 ["Z1Vm_SHD]G5qutSCvL)&BFQ#-2V9hy%|R5$bdM8y{Aryqci:Me02K!nE]-(D^|/.","Q6xQ1E-NYb|]>rF/nnt(TcTc>CE-qDKn$UO3=kfk{#Gm0BKt=teIhinm|Aeuw#$B","&$CYwM~U82BPxmxC:6<3pWt>817U},zk(+b`7%?+'1>eV3nXD7;Q5jq?D"],
  w 24 39 0 330015 330832 83 7151 [")Hq>d@UA=}_|q#XEKtdp*Cs{'X5TcD/I5`0x.ZwJ's)DCy'hz{xcK=<W-!3cN;~g","Z61F$tdNA}TAN1y&kl]O};2<ec|%.J9536#rftJdqc5uYP(b3JfXf'u/GDeEhb`#","VMI]65!g5>a{6)jRD:s#Gfk#QuWB_E&^Qmd!?^eb&}^T$Nx(c*6Ka!Oa~/!?8b'"],
  w 24 38 0 340014 340769 84 7167 ["OJ%Uj@LQI|AW3Hk+YZI@f=|a8$b>?%]!FI9:beXU:-6]KlM%PWG>[,$eGnR'8=DB","#b&&5m<rvP-)%WfL{PDL^c'EiB9UK2V+CD$pbeFRN!vb0cy-(b1lDwxy.ey':;6r","8NzTk?5Y?*E8zx9@#:=o4Y%|!$xd.Cy(fxzrn8+Pd]8:^/!kY3U}7qpRwsi="],
  w 24 37 0 350013 350768 84 7083 ["qb_77J:5asX&6r!;AbN&>20=XcU5msG;a7ht;M+4gz=Un|?4#Bk:&d<4IE|7=vq2","<PQ<wR][w<>oVc4&E)A23,$|ga5{TDF9;qyUhyU%W-(p0.Bi/YSB_,(k<*l1w)xf","f;K<TvW0IW8C[:S4,@v.RJ&X(oM*D#p+2dbXOZM3U9DT`]e{B9(^Y_'C`-G:mP47","#2*)"]]

private def r24_5 : List (Chunk 24) := [
  w 24 36 0 360012 360768 85 7082 ["3}oc9xcGj>B#?5oVvbQ2b;+%'tMC/cyc@?!Dg@O}~7r7i#Awr$@cm7D`R7-6Pzzw","Nimytz~8MdhV`F0=6jvCWi|wwkyi<<WQU^.?Fl+)PNN(OtkAQ-l=Vw|%Q*]!'o7o","BY6'KPC~}rmRmu-N2gx3BPpoU(V>DJ^E^T|`TsB;wBMeutT`)N[k+sowu)FPZ>8s","N]KbQ"],
  w 24 35 0 370011 370705 84 6915 ["WKu^ph&3kv^w_`jt#m*v~IxQOGVnJ$$+)8d!*RZj!OQ8kc{a}1mOuv.hrmHa=)7o","T~H$A~xZS@Ho:gHAep;dS_!(}{j^oh'^C)2vP-%g739<%C/5rt`X<#kJ}rk+e0PO","TjzW~$)6+kLN2or'nqW!BH$({>cx?pjz}K3vTDLKaiXoU8y]h(1oJ=t2XSjOfNDx","+W5($0"],
  w 24 34 0 380010 380704 84 6831 ["EhA-7.p$e65yMZgXKKq07gR7T^HRXCIeTFqi%aVK4f^]Ha4>yp_`AXLI{c:dhkw:","F_I1^n:v<FaGIOB^lqE2n(k7&P35C_Ff<%mqB3Pq]bT81TmGQPeo?q8%h*dj2ig/","*r{;or[N(E5Ygc.Kr+$+8A7xf8(INI={Xl,;[-;Yf_P$jRGTx9mh2jbc8`Dx-iG7","i_@ng38L"],
  w 24 33 0 390009 390704 83 6650 ["lWUs*VVwa:&R<w}_;?LPi)HA$vC.rV'QLt21BrJLV6mzw1!8,ABMs`&xLDnWZX!J","o&,,n{/~YF.k~TivZ^uu{L0_4$REUt_E7|Fw$=rl9.7poxZWD7-LAh%$hwD?U0+!","k1gC.&&`Pnt0NI_b(7`uAD|04pc<+yR<~4h5CS}e@2D%9I'YMaaTl]<`lkhJH'(U","8&.R!Z*p"]]

private def r24_6 : List (Chunk 24) := [
  w 24 32 0 400008 400641 82 6487 ["'U1MZkxwAbcSpX<.lFX-e!.Est:!1U1aAs7b}S~iJM2;72Ramwg'316*J83$_q?_","J#NfF2+`sqjLF71c$:uzMqH&WS3]Q'>1>PKXrY1Ud'@F0N:]%Qw)<1#1M.d+V)>P","@(K9A9!KrHt,B'tJI4fK:Uzy&pV9phQ.i_WWih/A{'#*a'6>KE+uoIQGa|8Rrv'S","&{W="],
  w 24 31 0 410007 410640 80 6231 ["&TcffPQ&u*373'U3XBT+3#9?+{%TRfdVA)j/IthR0GTWKwH/p-[QUX8tkT%T|uBJ","5q`dtH{G(d8j1Kq}kYs.ef#h{t'EM2(7GrJ'xL`.M?CZ)N@<NV18Lc:+fL#LN(`B",".syLQj9!1(lF8m<y5|XP~/[TQT0nBo9Plly&Fp''<[j@lwP8z63tTx44@2DS7zl0","4w25"],
  w 24 30 0 420006 420640 79 6054 ["mo,_[QRLzuHL]Hl4wScy$kJ1u$[r0Q^Yok>zz8L^mW<1FoQ6h}9U2W!^?xDyp96J","?<z3lV#W;d-SQ@'fWp4*acO2xjYD6_)]%CjWIfz`5g?45gBJ|@buy@Wk(D<S4/Gi","}6+]4#?T=-o-/4BsJx+wJlZZV+}=ym+,iu6HWML*n!.;U<@`G!@Om78o:z*wtpRb","$kJ"],
  w 24 29 0 430005 430577 76 5727 ["{|$:6Mp0H))d]3/9+p,ic[>:;9e,0b_3=r`5JGm3;#$}_wQR--6~#Cl_1?*wP)9w","t;0/3$]w0$y<D!q1k2M%JbrCyQMvq{j65%a_EgN&-puo-4/+OUzd'`cs6&78$^yU","8bC=<Y#a*hXsj.N?RK<;Oo)m)SIAUizhD%w8*<}:M]04SLU<Rmy{rx*GOc8D"]]

private def r24_7 : List (Chunk 24) := [
  w 24 28 0 440004 440576 74 5479 ["D>'IlNv_qtiZ7vV+RS'&iCW2+{Pwv}Q|/h0[suAKVdM81hVc5&OR.)roRCd7vSw*","{n2YLm@ATU+j^NCr#1{0ERr>))!~;aV4i-h!u(VR~W4bmw^c1O4{mk3>dQ6(&#nL","A)MFN)6$|+=FA?7^085z[x?gkwBTE_tl{jAv.UW{6:{gB/z]P'y3u!V(*6^"],
  w 24 27 0 450003 450576 71 5142 ["Z}a-1N6.br6&b?}1z_k['BA3:wveTpEiL&_KMTxW0nHiR<W~PrA3<ChlE6:}YI$B","{EJcr:rXEsp7xm`L^^d.Q4&37!!pxIkAFE3rj18?44xwtYUS{YQpmDRDh<z7X5yS","#&o!)x7rD@^-<YbF%+tb'YudE(T5<V%83)iu.U1b<zL-,%NVajQY0(X"],
  w 24 26 0 460002 460513 68 4827 ["Yl3uY%Q577:h8`UL{nVr1']H9!BKRPdcX}TD3*4g*D51JtfA@&9oea!gl/:{8zj6","@{#CPK,V[lP<Ydj/>!l'zq8+_AfM>%xIqiaED2JtGc~1a!d:j2ZZswrD=wJkiCoZ","(wb@{uXYjC.!%dZ^DiTZ5tVla)$UlyZe;NwpjLPQ?Yynu>;}"],
  w 24 25 0 470001 470512 64 4427 ["un^wNxtFR'3kz3<:V[%}J&fl/&#d-jW1`hBK*$93|.pA^Q<N6.J1NFGTm(mfP6,R","m[/z<tx)ySF0RI;m3hOzP/Kar8b%LrUa0^YU&D|1[;9hHV?Is}<L!sjF41PSCTao","#hzH85_G`ver~%s]Xs@=g;%]zu#6K>y#zuRfqeR6M1fL"]]

private def r24_8 : List (Chunk 24) := [
  w 24 24 0 480000 480512 61 4102 ["&V46#?}2n]p8iUDSwd^;s]6(6J!^v?yGma#;<2[dEmvrNR}2v5e61XmGuNMSP+16","`9Xq]OcSqbVcXiSw_7*KPdN`O0K_.?1Lvw7BSozO9g^w^-'B~A2ORyP#EPr]N5(.","$Av{<fq(V#*getB2Qvola%;S7T44HA,VI;bg^A"],
  w 24 23 0 490000 490449 56 3643 ["xIbXU-Gq<J}Rj=B{xn0<<TW(+>bj!mN09Y[-ZIK9,HFsqa^!Ll]q.2U6P1=XtTBS","#4^8rD|avN{56g4j?9*NC+z~5H;=WY'jThr9eYt%TUc10]%p3RhqJK>f!<X)=BIs","(bmZ+&d-cUeu3u/Nma?^23KIFx6Zk"],
  w 24 22 0 500000 500448 52 3259 ["MFZRbmXm]LjJN{fBr0bj+:guQz4aQcTrBzBCht0B{KK8_9/)4{Vkhp,vxKxn(:v`","6x'8p;K+F6>(dnBf{R95@<.}}ETl9rtU@@5]37B<HT<JA'q:L:GzO5i%|hwU'Nq^","67J#FQ6N]j>y$z67vFG<yL"],
  w 24 21 0 510000 510448 48 2896 ["0Oeo.uq>^tE/'c|j:6MNC[}noYgrK/!Qh0jsoHGOp=Si.(uNhRzGXvdMQDybSoq+","d>D-;<xKa.TxKG{->7z0;@pBDHLiTahy`=Ap3gdl)f?*2ZrHRnZ4<_C9{{!6P4W<","#G7rAb,;[Pwq{lZ"]]

private def r24_9 : List (Chunk 24) := [
  w 24 20 0 520000 520385 44 2555 ["0!$)?J,`<8/4.u|mF+QDhVx+eF$3~Fg/$)k=hY76vjBWqF21Gi)?^!Xi<spag)&S","!<`nLw;+5.4MoV9lozlrw$<:eb@`TyenJ^,.E8ux,f:eF}&Ry_=KN~&8aVciS':F","=^<Qw7"],
  w 24 19 0 530000 530384 40 2235 ["_^.`v[g-6gRx/0U'`@':d}n[.{iSD[Y4C,X(7_*JM^==ob~5E.&C2ZA`Ed9Jw;$l","vVkp0MX]sKdP?T_o5n2(F,Qkl@[Nq3~X*g8*YWOiJ~HgB0V]&):TDZ41A('B7%P"],
  w 24 18 0 540000 540384 37 1978 ["]f$g+yp|viyzZT&r-_3oj[5S|7E}?{R10yNS*F$hj6KsJ-XEqyh15;fS+LEDCMGx","Vhi>))owf6?g)=!@z!P+u{:1h/x!m{7R[dGF1oAqd~ak>$o3:Nu-6*gH"],
  w 24 17 0 550000 550321 33 1697 ["eBhTds=Y6C)jrJXpw?sP-W?iH!A{qW]Wk6wqR@HYchcoO#CT<C5Jmno$h&Qu/*a+","+xC15[/I#xMrt*d4(57fImU[W//DRsyw%cK9q76Dy>|a^aiN"]]

private def r24_10 : List (Chunk 24) := [
  w 24 16 0 560000 560320 30 1475 ["?04&,r,[$'<tS.mnq^&K>b#hm*nnE`VQc/pv[UX!~w1)w${bBPs)}U+_cLtbTq4[","):6HNKt<}bfXe3]-r>(GbcQ+-!=ZOHA8u_n1e.4mkyB"],
  w 24 15 0 570000 570320 27 1269 ["!]=!NL88kHOSrVP}1y|6y&CISC,|y(n78&eCo{4%_QI@5qDzcoxOT|`RmYUuCIWx","_}aY6{!&e/lGOfb<eK!]iteCA<l{QE8YF"],
  w 24 14 0 580000 580257 24 1078 ["y2YU_m|=0ZJ6Us%)jI7A+i2^gNjveQ_|8!,NQJci@lN#Rq`>RaMfQSHG/'G~?<7G","$N2TKuC,RZOPQGYX_UdI904Y=AV"],
  w 24 13 0 590000 590256 21 902 ["YD/[_B&6tIh9e}2T_?+V`SV[1fj}_'mvX@Jtf;Km/O1nLCmrX&rg3Yp2Cm1{-Bql","_!2-RQlZDf#Z_;4MY>CE"]]

private def r24_11 : List (Chunk 24) := [
  w 24 12 0 600000 600256 19 774 [">$v-8Z#b9NxVQr'Xns?mU7U$0j7=#4&%[NKzi%]TjL1g%$5{E7S=!_ZUM'?&0#['","RKgvy]54hpd"],
  w 24 11 0 610000 610193 16 624 ["M^/<[Z#uF1Uuv1=u1l+0N7P:$]kh/>Ahy>[N2+RDx^pfg[u*r3Ej:Nl<:3!qa?0[","#jtaI"],
  w 24 10 0 620000 620192 14 518 ["%gmwU&qY!7*y.6Tscy2AU284qOOzq9gE{1_G]mU/<z[jA88o}lm`8dp`0#44>Bt"],
  w 24 9 0 630000 630192 12 422 ["%>}A9tG/%4tqm&FYV|`(+h.]cNL*pf4^tP|f#7nUK,7X(pl>?x5w]T"]]

private def r24_12 : List (Chunk 24) := [
  w 24 8 0 640000 640129 10 334 ["ttHr>VE3DVGXmq.s$,[d/zAkG#bc,<AiSv=ikh1]2:|Kk,T"],
  w 24 7 0 650000 650128 8 254 ["`wvp*ge$=kX+1ra$lHS7]u'k%uOaw|@~r9c!CC/0"],
  w 24 6 0 660000 660128 7 209 ["0F^AN/=$<-6zAI<s2CX/MBW2%V@-k)r_m"],
  w 24 5 0 670000 670065 5 142 ["%U=kNA94syfWb_4naF`?z@&e@*n"]]

private def r24_13 : List (Chunk 24) := [
  w 24 4 0 680000 680064 4 107 ["^uXItN6{Lgz2~BYdnp'NM"],
  w 24 3 0 690000 690064 3 76 ["KnM#^E+,;Q/,!~z"],
  w 24 2 0 700000 700001 2 48 ["$?.51rq!WJw"],
  w 24 1 0 710000 710000 1 23 ["I!tF&"]]

private def r24_14 : List (Chunk 24) := [
  w 24 0 0 720000 720000 1 22 ["#_A!5"]]
private def chunks24:List (Chunk 24):=r24_0 ++ r24_1 ++ r24_2 ++ r24_3 ++ r24_4 ++ r24_5 ++ r24_6 ++ r24_7 ++ r24_8 ++ r24_9 ++ r24_10 ++ r24_11 ++ r24_12 ++ r24_13 ++ r24_14
def rows24:=rowsFrom chunks24

theorem good24 : ∀ r ∈ rows24,good 24 r=true:=rowsFrom_good chunks24

theorem sorted24 : rows24.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks24 0 (by decide +kernel)).1

theorem mass24 (i : Fin 57) :
    bandCount 24 (i.val:ℤ) 56 14≤(rows24.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks24).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 24 (j:ℤ) 56 14≤mass j chunks24))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total24 : (rows24.map (price 24)).sum = 208338 :=
  (total_eq chunks24).trans (by decide +kernel)


end Final50RankReceipt

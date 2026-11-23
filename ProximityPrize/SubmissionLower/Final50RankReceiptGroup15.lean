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



private def r15_0 : List (Chunk 15) := [
  w 15 44 0 10897 10897 1 102 [],
  w 15 43 0 20834 20896 2 204 [],
  w 15 42 0 30771 30896 3 303 ["#%>"],
  w 15 41 0 40708 40833 4 404 ["*i{"]]

private def r15_1 : List (Chunk 15) := [
  w 15 40 0 50645 50832 5 502 ["$-B?w"],
  w 15 39 0 60582 60832 7 699 ["-FE!6WV!"],
  w 15 38 0 70519 70769 8 796 ["#s75qzFRc"],
  w 15 37 0 80456 80768 10 992 ["%[M&--|a0<k"]]

private def r15_2 : List (Chunk 15) := [
  w 15 36 0 90393 90768 12 1181 ["X55+(~T}wf*Be7w"],
  w 15 35 0 100330 100705 14 1376 ["YP@:_V7E$:e!r?$Z"],
  w 15 34 0 110267 110704 16 1564 ["%9!sj9iQih'U$%z+sHP:"],
  w 15 33 0 120204 120704 19 1847 ["&7(5s8zj0vN$ns[vMi{)~/Or."]]

private def r15_3 : List (Chunk 15) := [
  w 15 32 0 130141 130641 21 2034 [",n%WQMVfg2Blw[ir71mq41jRY9o"],
  w 15 31 0 140078 140640 24 2316 ["'(,:t$A=a$JL{Uvekr'cXf<<an8C,XZ"],
  w 15 30 0 150015 150640 27 2587 ["4B,w0`k0_x?gj$:_5*t#f*$[=/n$:T;8s}dd6"],
  w 15 29 0 160014 160577 29 2766 ["N1TP-@&#?MYpCl<H=3dXsf+0pCx,8`+H_:;&D|F"]]

private def r15_4 : List (Chunk 15) := [
  w 15 28 0 170013 170576 31 2934 [")4(z+2vF}Z_<6[8#hlW!k$CMSW`mq]&}'_JoHKnISrN*"],
  w 15 27 0 180012 180576 33 3095 ["#1fQABHooUy-[>~Ta&/Q2)RLt}[kqzfVjbM<%FeS8KFk.j9,c"],
  w 15 26 0 190011 190513 34 3164 ["A2`Au:CWxN-g?=j:E9KXdn:r}2B{tYQcu17$TA}5P;!fo2_Ns*"],
  w 15 25 0 200010 200512 35 3230 [")T2+4'[42ebjOhW;b~PWvh#Rvx_Igjcd1}DT_FH0f7Ibr}I^xcEV"]]

private def r15_5 : List (Chunk 15) := [
  w 15 24 0 210009 210512 36 3281 ["0-0?ZZT1~qMI&iH.7_XL1/t24k|K9aV<n5B<w5n7.Pv76n2Te]Ee>w-w"],
  w 15 23 0 220008 220449 36 3256 ["'vUJ^UNw%uifEsp79C4W2~FJ$s$>jqQBDaNng!15~@kR'iI:O$4#lng"],
  w 15 22 0 230007 230448 36 3216 ["2JZ`+82ED`'f:VasCJIoS[el?:UYww1_`EuE/C1|!~QhwlUT[)Z)#J%V"],
  w 15 21 0 240006 240448 36 3177 ["Ocpz.Zyl]I`h>O-x&[p#UhO]:'UAher0Ich7r4%O&omV`DKFg+I-ttfm!"]]

private def r15_6 : List (Chunk 15) := [
  w 15 20 0 250005 250385 35 3050 ["$AV]@*anXa:.?'|2irD.9,9!3c[f{5Xeo>i!LnbQ65+|kvp-/AuBL@W>"],
  w 15 19 0 260004 260384 34 2928 ["+a|Mpi*5H!lA~5H,DA$@0kHoSgas|a,x?laOiKAX,jym(^d,UJ|k|o"],
  w 15 18 0 270003 270384 33 2787 ["%CZ]bhkK[vQX()D/|[a233Y,x%HM$=k43n>u4D#/1ixY1kKL/'mUims"],
  w 15 17 0 280002 280321 31 2586 ["96$=GQ0-3ryJ9%W~zLZ)xST>q1rM)ev(Mk=kcopy,-Udcfxcg{"]]

private def r15_7 : List (Chunk 15) := [
  w 15 16 0 290001 290320 29 2366 ["-~S#e25Fjedjv`x-#PSbu59Oqkkecg]hBrCVF(}9085dYj,c"],
  w 15 15 0 300000 300320 27 2155 ["(3Wm(e[;;HcwTk>LAi'Gn4.ULOT_)B>AQm=jcA2$:<0vjw"],
  w 15 14 0 310000 310257 24 1860 ["';<![cH&>54:/d_a(Zhr;kM{H-/@idTo;d_$?,7Bd"],
  w 15 13 0 320000 320256 21 1578 ["&&C;A'{6OrDxl}7h$(])9H{n/f!KRjF$m.h'"]]

private def r15_8 : List (Chunk 15) := [
  w 15 12 0 330000 330256 19 1375 ["$*4M+`q,kH&Zss>we3i'm2VXh!jXeQUI{d"],
  w 15 11 0 340000 340193 16 1124 ["];3qF*VMQ?wr}eE/E&Fl[9njj+G"],
  w 15 10 0 350000 350192 14 948 [",nCzp=5F0mtNLT;4($*f#]8l"],
  w 15 9 0 360000 360192 12 781 ["'Wky|S3D7LvA(ynA?v]M:d"]]

private def r15_9 : List (Chunk 15) := [
  w 15 8 0 370000 370129 10 628 ["GEadB8?EY=ADJS'}K"],
  w 15 7 0 380000 380128 8 484 ["(yZYXmKQio>r*d"],
  w 15 6 0 390000 390128 7 403 ["ri?v!4>ANu}GG"],
  w 15 5 0 400000 400065 5 278 ["'iBt_]m$["]]

private def r15_10 : List (Chunk 15) := [
  w 15 4 0 410000 410064 4 212 ["9nzB39`"],
  w 15 3 0 420000 420064 3 151 ["$|k9${3"],
  w 15 2 0 430000 430001 2 96 ["&hw3"],
  w 15 1 0 440000 440000 1 46 ["5`"]]

private def r15_11 : List (Chunk 15) := [
  w 15 0 0 450000 450000 1 43 ["XcL"]]
private def chunks15:List (Chunk 15):=r15_0 ++ r15_1 ++ r15_2 ++ r15_3 ++ r15_4 ++ r15_5 ++ r15_6 ++ r15_7 ++ r15_8 ++ r15_9 ++ r15_10 ++ r15_11
def rows15:=rowsFrom chunks15

theorem good15 : ∀ r ∈ rows15,good 15 r=true:=rowsFrom_good chunks15

theorem sorted15 : rows15.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks15 0 (by decide +kernel)).1

theorem mass15 (i : Fin 57) :
    bandCount 15 (i.val:ℤ) 56 14≤(rows15.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks15).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 15 (j:ℤ) 56 14≤mass j chunks15))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total15 : (rows15.map (price 15)).sum = 70905 :=
  (total_eq chunks15).trans (by decide +kernel)



private def r16_0 : List (Chunk 16) := [
  w 16 46 0 20898 20898 1 102 [],
  w 16 45 0 30835 30897 2 204 [],
  w 16 44 0 40772 40897 4 405 ["*<J"],
  w 16 43 0 50709 50896 5 503 ["$!W7F"]]

private def r16_1 : List (Chunk 16) := [
  w 16 42 0 60646 60896 7 700 [")Pymo&s"],
  w 16 41 0 70583 70833 8 797 ["$h`r3/%=5_"],
  w 16 40 0 80520 80832 10 993 ["'A%nYvCRA0$J"],
  w 16 39 0 90457 90832 12 1182 [">q)WI|E(mD-&0;F"]]

private def r16_2 : List (Chunk 16) := [
  w 16 38 0 100394 100769 14 1377 ["#.xs[9Z+Slzx%%E'g!"],
  w 16 37 0 110331 110768 16 1565 ["(/5I,T76-@ROk@+kGPW-_"],
  w 16 36 0 120268 120768 19 1848 ["$t632(.E-y/+g)V+f`|b#TdOg"],
  w 16 35 0 130205 130705 21 2035 ["8j_~la{K6|,y!z.c3nCVp6Qu'?.B"]]

private def r16_3 : List (Chunk 16) := [
  w 16 34 0 140142 140704 24 2317 [",`V7g)Fk=gFJS=We;(Ll^P06kJRRDj@k"],
  w 16 33 0 150079 150704 27 2588 ["/wu/Hv1--C@19m#~n,<<^4']L%/|>8c&;sd8*"],
  w 16 32 0 160016 160641 30 2869 ["*Xabh.|]#g23Nqyr-:QgYcyyaAc8r4>5AKmm6ka`V"],
  w 16 31 0 170015 170640 32 3037 ["#Fms6rb&~I~,QwJI~`dfVL~2=?a6q#vm.t`3yHTyS`6}:!"]]

private def r16_4 : List (Chunk 16) := [
  w 16 30 0 180014 180640 35 3296 ["#o&)1=rMge;A;)'xaZO-i=XZqMo_:sKKf|nL*JQY^6&q%wMAz5&"],
  w 16 29 0 190013 190577 36 3365 ["#RGrX!j%q}rkQ'n>wc=X>S4qp{5UuY/h?o8CJLM2'FSk,p2'B^k!oZ"],
  w 16 28 0 200012 200576 38 3525 ["*6>Lle/MH~k|JD}Y&E^P#E!O}adW.(<@&lNVl5494]b7d<-gJ]k<=p&42"],
  w 16 27 0 210011 210576 39 3576 ["'SY|:youn@4AWV8I^gq!]%f_KJ7k&d?f(9seBvt3:]r#,|/}!66[;v*ym2CN"]]

private def r16_5 : List (Chunk 16) := [
  w 16 26 0 220010 220513 40 3641 ["#Y7db0cNxId|$IR3QMRUoY;~i@Bm,;}v(]R)`@HB<XRhL3n'uKSImTcyN@G]f6"],
  w 16 25 0 230009 230512 40 3601 ["&KcIr$Q!1^]mf|RDQW),42rI`'X0YP.n7sHU&i$|1Y!Easnc&.EVh/%?Dn[rOu!"],
  w 16 24 0 240008 240512 41 3648 [")4+*<y}Qu5;Z`^F-O5';1~B^+fAdM*l}O.:[VpvH-5kgF}>(aR|bX^!mhrM6Y-}c","#"],
  w 16 23 0 250007 250449 40 3521 ["0H%<nA0ZP&`*8e;I{nB7mC14B,jmMq%sim0%TJPze-=`Lf;;+][*#C)p6;3#@Dy!"]]

private def r16_6 : List (Chunk 16) := [
  w 16 22 0 260006 260448 40 3481 ["0H%?nXG4olRF<*`Abd`&0+YlOmy1/:/qr^qS:|c`Eg8#ZyvmxbNG#H/AwVvD9xC>"],
  w 16 21 0 270005 270448 39 3340 ["#lpix]0pHPD>,@UM.I}=lsVwUz_~/d`aRm}Om|b&b-O,%=.s:|G?.'c~s$W|b..Z"],
  w 16 20 0 280004 280385 38 3217 ["*O-'U{xJ#|{v-Y5>vS^Rl4A5!3^nB+o**f)?-EA:oJx&vLF}U(i%0<jAK3.Xi!"],
  w 16 19 0 290003 290384 36 2997 ["&ERW2V6a<#44l[|'$-'Vwa?{zbQ/x:7j51>8c6B0B=7!^|sew`<rC|w/-,jF"]]

private def r16_7 : List (Chunk 16) := [
  w 16 18 0 300002 300384 35 2860 ["4.P^GLm/b3GTaQ>3YN@}OAm},)4H1Vl:Hudb^&6D]aX;4KAiG.usFcL-z6"],
  w 16 17 0 310001 310321 32 2565 ["MLW1P!u|0Sae_9DZPdoa3G08!C+xxXpUav1V&%tL5'AQLJ1MofgkvV"],
  w 16 16 0 320000 320320 30 2353 ["*(B;v)tUH<OA4GN(E);hd0#N}ro1I^2mUs@--r#$;)UZbOgD`8s"],
  w 16 15 0 330000 330320 27 2048 ["37Z.x!U[KS-g^z;7l')Vwx+?x]Zc;YRVsH:G1-hW{t5ND9O"]]

private def r16_8 : List (Chunk 16) := [
  w 16 14 0 340000 340257 24 1765 ["0`;l8HZh@Itgt82;[bryRZ&Bh*~X%kmW~(M%c(U44["],
  w 16 13 0 350000 350256 21 1495 ["-9:Eh0X;9KA-8SOX{i@5{Kz{E|LqqfG#yteXl"],
  w 16 12 0 360000 360256 19 1300 ["$*;<i^wCXi!%9^kxK*]%Nz3b3IRSpSn?n/"],
  w 16 11 0 370000 370193 16 1061 ["#i$aV(7,A<tad_:]mOr>:ALdFWD<|"]]

private def r16_9 : List (Chunk 16) := [
  w 16 10 0 380000 380192 14 893 ["@)N5^Smm8I~x3`6{*W&<5iP[W"],
  w 16 9 0 390000 390192 12 734 ["'W|T)iEd+>_/Qkp{WYHqWG"],
  w 16 8 0 400000 400129 10 589 ["#-{2G(XY./+)*gP:;<K"],
  w 16 7 0 410000 410128 8 453 ["5=[R#7E)=F60v7x"]]

private def r16_10 : List (Chunk 16) := [
  w 16 6 0 420000 420128 7 376 ["rkbI{YH,^|JY/"],
  w 16 5 0 430000 430065 5 259 ["2$d>ZC[d,K"],
  w 16 4 0 440000 440064 4 197 ["e8cJ5_0+"],
  w 16 3 0 450000 450064 3 140 ["$|rgnsC"]]

private def r16_11 : List (Chunk 16) := [
  w 16 2 0 460000 460001 2 89 ["/7b(["],
  w 16 1 0 470000 470000 1 43 ["XcL"],
  w 16 0 0 480000 480000 1 40 ["Xdq"]]
private def chunks16:List (Chunk 16):=r16_0 ++ r16_1 ++ r16_2 ++ r16_3 ++ r16_4 ++ r16_5 ++ r16_6 ++ r16_7 ++ r16_8 ++ r16_9 ++ r16_10 ++ r16_11
def rows16:=rowsFrom chunks16

theorem good16 : ∀ r ∈ rows16,good 16 r=true:=rowsFrom_good chunks16

theorem sorted16 : rows16.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks16 0 (by decide +kernel)).1

theorem mass16 (i : Fin 57) :
    bandCount 16 (i.val:ℤ) 56 14≤(rows16.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks16).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 16 (j:ℤ) 56 14≤mass j chunks16))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total16 : (rows16.map (price 16)).sum = 82990 :=
  (total_eq chunks16).trans (by decide +kernel)



private def r17_0 : List (Chunk 17) := [
  w 17 48 0 30899 30899 1 102 [],
  w 17 47 0 40836 40898 2 204 [],
  w 17 46 0 50773 50898 4 405 ["*<J"],
  w 17 45 0 60710 60897 6 605 ["2%{LJ"]]

private def r17_1 : List (Chunk 17) := [
  w 17 44 0 70647 70897 8 799 ["#n2jq)6JB"],
  w 17 43 0 80584 80896 10 995 ["+kQi1cNNNu'6"],
  w 17 42 0 90521 90896 12 1184 ["q2m6R2c47HWtD*c"],
  w 17 41 0 100458 100833 14 1379 ["#bEqRM,%5Q5`39^U1=>"]]

private def r17_2 : List (Chunk 17) := [
  w 17 40 0 110395 110832 16 1567 ["+*}xKtboJ8Y8b51(}Ki#1."],
  w 17 39 0 120332 120832 19 1850 ["&;D}`sv:=WQ9$p020N}c}-q*H{"],
  w 17 38 0 130269 130769 21 2037 ["M5/jB59d*(j?dr)='Y!uVEdWs}&ZB"],
  w 17 37 0 140206 140768 24 2319 ["67t:MEbK#Z{Rnfb5G;A$bF4p{w>(s|l#w"]]

private def r17_3 : List (Chunk 17) := [
  w 17 36 0 150143 150768 27 2590 ["<I(X'J)j0)5{COh]aWWuot:3bjgW`1tgg}J(BB"],
  w 17 35 0 160080 160705 30 2871 ["4/Gm_o5[vt:vNR)MNm74MwX+=[XO_hH{5'v]j76O`g"],
  w 17 34 0 170017 170704 33 3141 ["9^jI-7T9GbF~p_joy[MV$ls.x{i!0JkNk}H,!_~ZrK_oJ?6"],
  w 17 33 0 180016 180704 36 3400 ["@r:N;:Wqw]Zmeby%p#3rqE@>EbN?Vy;xJR2T~F(4rJIX=3z_SI]Z"]]

private def r17_4 : List (Chunk 17) := [
  w 17 32 0 190015 190641 38 3567 ["([Iv?~DQxt!ST3rK9MHBR:*bf9`H'*8l93'tm_egMm)V4X?b#Zpm#*L$R"],
  w 17 31 0 200014 200640 40 3727 ["Ea]kna_[n^MmWXX[Q>:=_u>mC3GnCA*WLIXh~~Jpe=1vQ7B)QpR6I32NVD<2"],
  w 17 30 0 210013 210640 42 3872 ["n=8_l{OLq8_WE6_FRK{nrrAddS)!:C)U2DC<'xP%8S@Y^yp*|p:1ZM)9U5P%>b_*","'"],
  w 17 29 0 220012 220577 43 3937 [":i~E2[sTcT@$QjySagRanuOXCAP=|[|pTKfT~>NEp6%[+MpKvHZf2tXNl2DnV/gk","#gd"]]

private def r17_5 : List (Chunk 17) := [
  w 17 28 0 230011 230576 44 3987 ["ca{h;WR+`vNv.KFZbaz<Hu)F2%ByLnQ]I(-F*f9SQuz}|.rEzQ0i6WN{O6?5m>3N","#24sTZ"],
  w 17 27 0 240010 240576 45 4034 ["`jye7z45;u::{KWNk2sOah$C}!PY_[_22/r{,1*7&k@Wv3jJix-p@y5_O9:p_U96","<4VnnwZ"],
  w 17 26 0 250009 250513 45 3993 ["=`nf;0(dfy8uT9i6lFDb^)1mm/-e?m/2gzcH-3>]TwrZv?kp0L7vE6p4]k|i5!%V","z&@g=e.i"],
  w 17 25 0 260008 260512 45 3953 ["F3B%@r?kh_@=XoJ6u':6J4,?yGrZuN6*o#w1M`-AkaK]xKx<McUY*?-7r$wxM~XR","z&@|E'<'"]]

private def r17_6 : List (Chunk 17) := [
  w 17 24 0 270007 270512 45 3894 ["~GbdQ/lbNdbotkhG(_S@mcZ^Oh^ISC^TMGeRU9tnvlIOGV!^)]^k4^swmXgiHd5F","$]D9xe6Lta"],
  w 17 23 0 280006 280449 44 3771 ["`dDF5*WX0/>E&r%eu!qah/.)$Mh&,fBwPS*Ttqe9esUB5E1G}4fY}E5UZCSm5_G_","._9~hYO$"],
  w 17 22 0 290005 290448 43 3629 ["bv`,dejgbYt<R,ca}tUC&%8}g'qbZepbgm<ykms[N+Q6iTw(D3.v5S6<xzQUA~4B","#WS!=P7^"],
  w 17 21 0 300004 300448 42 3492 ["B+S|~!1+.+5cOShx+q~>jCcw(&e7{Minv:8(=$}4p>ZmO*44L'5Xp<qdSaPsF!G_","(SkSsm"]]

private def r17_7 : List (Chunk 17) := [
  w 17 20 0 310003 310385 40 3271 ["t!z%|Djp1&]<>M,;j1pj(!AKWU$EHDdO)E=.(N$9V#jhFN:5Gi4Xtk@W!VsWP(gZ","%q;5"],
  w 17 19 0 320002 320384 38 3059 ["dj&l@]X+f*-BVbJ$PwRhjF(]Y>2URe5MH13}}ML.(/goKt^<){H~yQZI9sI#{vG."],
  w 17 18 0 330001 330384 36 2824 ["C~NU_~D$.>F.&TE<iUs)x|5/Zp?g9FDKJlRwwM8i;K>!8NG'?32T&-d$$NK(U6"],
  w 17 17 0 340000 340321 33 2541 ["?;E&L[d0+to;fcp~bTJ]xYVM5'7wvi!>;jyOW]XZk4B.m33AHci~a-`wk"]]

private def r17_8 : List (Chunk 17) := [
  w 17 16 0 350000 350320 30 2235 ["aPH>Lb|G_{Wk&I|O/WQp/c3Toee?~p$)PvH(8kjXl/cTvvH4j1AJ#"],
  w 17 15 0 360000 360320 27 1942 ["Q}#o)^ycHzm>KH:O$cv|Adou6?H@D?v5'13Y7LEVFI';PA)?"],
  w 17 14 0 370000 370257 24 1671 ["Jn{}iBUgu>QP!&'&dfo,FcLzg|=g^3CFi{/)N)]}ubp"],
  w 17 13 0 380000 380256 21 1413 ["A?q(Cc3p5|_Zou#rlU1$a2zoN(Ipft&>48!De["]]

private def r17_9 : List (Chunk 17) := [
  w 17 12 0 390000 390256 19 1226 ["'n7B1/b'9Q^CS;7l?Epfswb?^rWrH^65(m|"],
  w 17 11 0 400000 400193 16 999 ["&v$#PaB'=md4;A/tMnM,U8r.k;8!B3"],
  w 17 10 0 410000 410192 14 839 ["vfQb~E?P[>*Im>[=/Ml&I(+k0l"],
  w 17 9 0 420000 420192 12 688 ["1Tb@[LlZ_9$'ZlNi{iSk|a["]]

private def r17_10 : List (Chunk 17) := [
  w 17 8 0 430000 430129 10 551 ["%/Cy0wT~Iq`?|vsgtmqK"],
  w 17 7 0 440000 440128 8 423 ["WeLKZ~sF6%9up!|x"],
  w 17 6 0 450000 450128 7 350 ["$H*pQ~0;9NCcgZS"],
  w 17 5 0 460000 460065 5 241 ["NZi'8^3YPe["]]

private def r17_11 : List (Chunk 17) := [
  w 17 4 0 470000 470064 4 183 ["$!F5PpvfQ`"],
  w 17 3 0 480000 480064 3 130 ["*<<h}y%?"],
  w 17 2 0 490000 490001 2 83 ["Fp;b/P"],
  w 17 1 0 500000 500000 1 40 ["Xdq"]]

private def r17_12 : List (Chunk 17) := [
  w 17 0 0 510000 510000 1 37 ["Xf8"]]
private def chunks17:List (Chunk 17):=r17_0 ++ r17_1 ++ r17_2 ++ r17_3 ++ r17_4 ++ r17_5 ++ r17_6 ++ r17_7 ++ r17_8 ++ r17_9 ++ r17_10 ++ r17_11 ++ r17_12
def rows17:=rowsFrom chunks17

theorem good17 : ∀ r ∈ rows17,good 17 r=true:=rowsFrom_good chunks17

theorem sorted17 : rows17.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks17 0 (by decide +kernel)).1

theorem mass17 (i : Fin 57) :
    bandCount 17 (i.val:ℤ) 56 14≤(rows17.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks17).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 17 (j:ℤ) 56 14≤mass j chunks17))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total17 : (rows17.map (price 17)).sum = 96050 :=
  (total_eq chunks17).trans (by decide +kernel)



private def r18_0 : List (Chunk 18) := [
  w 18 50 0 40900 40900 1 102 [],
  w 18 49 0 50837 50899 2 204 [],
  w 18 48 0 60774 60899 4 405 ["*<J"],
  w 18 47 0 70711 70898 6 605 ["2%{LJ"]]

private def r18_1 : List (Chunk 18) := [
  w 18 46 0 80648 80898 9 901 ["0SL7Oij*R"],
  w 18 45 0 90585 90897 11 1094 ["$Cu'rc@p3*HuZc"],
  w 18 44 0 100522 100897 14 1382 ["#^CFq~<J)Lni1)^ugR"],
  w 18 43 0 110459 110896 16 1570 [":_?./Y0`_+b'<7-6h59u,*"]]

private def r18_2 : List (Chunk 18) := [
  w 18 42 0 120396 120896 19 1854 ["LY&6O7'4W#JeHxgBe|>z8^NMJD*"],
  w 18 41 0 130333 130833 21 2040 ["c*%a0Z7k4APc3kYewB:c+I'5'-cxPJ"],
  w 18 40 0 140270 140832 24 2322 ["@#XX-XB3tM=rc4K`W&N2EiEJKpiVXBv^>!"],
  w 18 39 0 150207 150832 27 2594 ["#37a0Uc4A[%_B+GCb=y}1>jpl]X=8$Enc`7T|W8Eo"]]

private def r18_3 : List (Chunk 18) := [
  w 18 38 0 160144 160769 30 2874 ["DJL6T5W~8XCR^0[z(NEY7o{@o8Ek0n/eZ35@SEJD;{s"],
  w 18 37 0 170081 170768 33 3144 ["NtQPXczgiy2IZn[hfV!Dn~ia+{e-0[!_.ownbxGE<Ub%@L=N"],
  w 18 36 0 180018 180768 37 3506 ["02_deV/V{qv2veZ!L!kcPQ~Rq8}+3y[G]6vx/WI%oh=;{Fx2+mxZ.`w"],
  w 18 35 0 190017 190705 39 3672 ["#5wzXT1BDyJ=LW/&_w;w4xDj]BSw6i`6d,crsXB<0Eu0UQh/.PxRQJWp26s"]]

private def r18_4 : List (Chunk 18) := [
  w 18 34 0 200016 200704 42 3930 ["#Ws6BqtYW%pX]'s6=w9O>TJUJ))YV;GViv3{xWAJqTtS^)@n$f0BV>|AY6M20YGo"],
  w 18 33 0 210015 210704 44 4076 ["{rcd7gIZb*Ry9Y{O~q~/J#THI#+&DTar0JG}sj_P@@.l1BPpMxcsF?ULe5-C9KBZ","e5AN<"],
  w 18 32 0 220014 220641 46 4234 [">%&`@G7s+VbXxK(V&T[!vZ^`{_6Kef1s$|m|%4bNcR<(LO7kl&KZ^KXnqOo#ABAF","#omTE4C!"],
  w 18 31 0 230013 230640 47 4284 ["1@~#DJdW)u]k`>dL?W&qtWs=yYOJckB_Nu.q-hDL|<yGTh0X,$rk`V8-@d|.@b]c","#7_`^WSNq;'"]]

private def r18_5 : List (Chunk 18) := [
  w 18 30 0 240012 240640 49 4422 ["(*S.n4F-)P.60!g3vL8'Z.'vFrDkY<rP9+T~I=5Z4~jjWCC!wgMAkNGqxyj~RxcZ","4S0>vi-=57Px|:A"],
  w 18 29 0 250011 250577 49 4380 [",+GMq]+fp/9IJ>%kk~'2hAMZ=$:I&P7o<&[(`~%]Uop{k7a<=(iz#,vf0g]q{XA&","8~@(~.0Np8(|@KL"],
  w 18 28 0 260010 260576 50 4426 ["L`Qan4%qH74qT}/^Kk(3hRD*eCx_x~$l-Kg(-e}dnV&KvxqfAI_CI[@L06R`0AI6","'Up%-Y/{613,jF>Vk"],
  w 18 27 0 270009 270576 50 4368 ["ql//.R<)Io2-=MU`|Y$]`C&L%Enz:BPg2:}d|/G`XA)VL5O7mvcvomE<|haxvnas","M,-K}]cK*T['{@(}86a"]]

private def r18_6 : List (Chunk 18) := [
  w 18 26 0 280008 280513 50 4326 ["M<4-,C2g~LS%i=2-x;e85UNft5a:I[uH*=AZ0zs[sXtlgofbw305jV|}0r*EA*V:","4OOBN,i}W(pP2rw+.9"],
  w 18 25 0 290007 290512 49 4184 ["K~x?PP*8Pt!m`TL~yKGN6:Oegq3wOr/0?ATd8s%o],1}&=i`mv9aV^}@i^'Rcivw","$>b2,}my_X:xF1tQ3G"],
  w 18 24 0 300006 300512 49 4126 ["8,dXKwpkiT!XxKZekkl2'(4r!9WghSQmws~mzFQr4mhp?|L&x.Yw-s7cGi(*Sv4B","(J4K7&2b?nj-TDR3vOp"],
  w 18 23 0 310005 310449 47 3904 ["D@:geT[bQ'%C((F_J*~sZu.%*tU7+n07.{+k].4$#28;GJ+Y*#SL<mQ6jQp~=[&k","#EjTpTj*@7&&I>qY"]]

private def r18_7 : List (Chunk 18) := [
  w 18 22 0 320004 320448 46 3766 ["=Xi1b4}hIW0n[/E2@<_fUiGj^hoFiLSfp8758`z+GxyES[heI5uS:4/ax(a/gjFJ","'g)PedfXukQU/7"],
  w 18 21 0 330003 330448 44 3532 ["5q_{I[UFq=:o)1$%;:h`9%v,T8.uei138f7q0PPTH7_#<%:[$.XVPep<Eb+GuJj&","*9S#T6Ci.yBAP"],
  w 18 20 0 340002 340385 42 3318 ["4_UkX_0?C,9kjg$igsCw;!toI0MK3B?a:8UhIX>AN/WTvjt,NxU$M@sLxc#j/xOo","[gM7[G<{"],
  w 18 19 0 350001 350384 39 3012 ["VaoreIns['?dHqcJOL4q`5Cs_}A,hB2CGw,4'H!igks{g1%9Vr1A2SN$11[:xI(R","#A<6*"]]

private def r18_8 : List (Chunk 18) := [
  w 18 18 0 360000 360384 37 2786 ["6=3g0@jC>C6mIw.6;saCV1{hM%XWkLqv=C(L5<eF=TQHk:mYNBf^SZ(x%{Ek}vVJ","be"],
  w 18 17 0 370000 370321 33 2412 ["$LjR`nX1_aS%3yU.CkTfuCrE!42Fe7ls]}$+s1M$A@9vhPP4]z4<$8A#XJlx"],
  w 18 16 0 380000 380320 30 2118 ["#u!!6LU6Ix>Io8-~,m.hk3@}a_r'DX^y7m}_s3)#w!r=7enw|6]4l'W"],
  w 18 15 0 390000 390320 27 1838 ["&%^|ctXG|lvjj4|8#GUe>fN=c>=}in>m?:c7a9q;O0+)>FljeIO"]]

private def r18_9 : List (Chunk 18) := [
  w 18 14 0 400000 400257 24 1578 ["#7^H;QY2iU{%;^n'K=gA26U*L0R4Sb9v$>S2t:?_pn:!t"],
  w 18 13 0 410000 410256 21 1332 ["z4/]HO$2rg/L$L)_Pl63cu5~|-<k)X$YNm>7(Ap"],
  w 18 12 0 420000 420256 19 1154 ["O'q?)<&3Vqk~`LR(tz>wQ2Mlf/32)ImCR-sbO"],
  w 18 11 0 430000 430193 16 938 ["/^L-;5dE:X/+YJxV:?yW+0_C?5x9[H;"]]

private def r18_10 : List (Chunk 18) := [
  w 18 10 0 440000 440192 14 786 ["$S)F`+u.W6*TkfVydgyCcn3xj'<K"],
  w 18 9 0 450000 450192 12 644 ["#>KW7FHoNz!Wh[E*325Q8%btFt"],
  w 18 8 0 460000 460129 10 514 ["*hL;vg7Ypmt]c9`pWKK:C"],
  w 18 7 0 470000 470128 8 394 ["#[SCN;T83QV%-FCqhG"]]

private def r18_11 : List (Chunk 18) := [
  w 18 6 0 480000 480128 7 326 ["4c6YWf|}c{|)QmuU?"],
  w 18 5 0 490000 490065 5 224 ["#B3AO7ku44^3h"],
  w 18 4 0 500000 500064 4 170 ["'W8l~ta;#|h"],
  w 18 3 0 510000 510064 3 121 ["9'kO0;$:,"]]

private def r18_12 : List (Chunk 18) := [
  w 18 2 0 520000 520001 2 77 ["Fq5rv("],
  w 18 1 0 530000 530000 1 37 ["Xf8"],
  w 18 0 0 540000 540000 1 34 ["Xg]"]]
private def chunks18:List (Chunk 18):=r18_0 ++ r18_1 ++ r18_2 ++ r18_3 ++ r18_4 ++ r18_5 ++ r18_6 ++ r18_7 ++ r18_8 ++ r18_9 ++ r18_10 ++ r18_11 ++ r18_12
def rows18:=rowsFrom chunks18

theorem good18 : ∀ r ∈ rows18,good 18 r=true:=rowsFrom_good chunks18

theorem sorted18 : rows18.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks18 0 (by decide +kernel)).1

theorem mass18 (i : Fin 57) :
    bandCount 18 (i.val:ℤ) 56 14≤(rows18.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks18).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 18 (j:ℤ) 56 14≤mass j chunks18))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total18 : (rows18.map (price 18)).sum = 110040 :=
  (total_eq chunks18).trans (by decide +kernel)



private def r19_0 : List (Chunk 19) := [
  w 19 52 0 50901 50901 1 102 [],
  w 19 51 0 60838 60900 2 204 [],
  w 19 50 0 70775 70900 4 405 ["*<J"],
  w 19 49 0 80712 80899 6 605 ["2%{LJ"]]

private def r19_1 : List (Chunk 19) := [
  w 19 48 0 90649 90899 9 901 ["0SL7Oij*R"],
  w 19 47 0 100586 100898 12 1196 ["4z.O93$Q/pE^ss"],
  w 19 46 0 110523 110898 15 1481 ["F[MRDTiW`-VZy{!CA6B"],
  w 19 45 0 120460 120897 18 1768 ["QfOpHJmSh/Dum^SbL{U4CoRc"]]

private def r19_2 : List (Chunk 19) := [
  w 19 44 0 130397 130897 21 2045 ["$OPB.*xo2Cx3k)]KK~sd#S9gxS6`S*s"],
  w 19 43 0 140334 140896 24 2327 ["%9&B8uQ`Z1mCW?22;F+w&Uo:Y@GPmhc<u^=>"],
  w 19 42 0 150271 150896 27 2599 ["';O_:hG]ritW_H!:sj;(^cV;lfaTdn!(FG2?`?P^N"],
  w 19 41 0 160208 160833 30 2879 ["#TCvoBYg3}ZP[I!_7p8>WQH!?[*1w_xg>hz}JCOkB&gG{2"]]

private def r19_3 : List (Chunk 19) := [
  w 19 40 0 170145 170832 33 3149 ["$#Tk4[mPM}x(/bWTR-IW,3D_;%@!94#FEMy=ePPf^Lk=AV=(%iJ"],
  w 19 39 0 180082 180832 37 3511 ["7+<mV'O{jXZx2X+FC(BMxFQ/x94y!Z$yYKg:_hGwk{=s*9Z&>hl~TROw"],
  w 19 38 0 190019 190769 40 3779 ["UIP{+FzR8E]aPx9g=SFz9F18=7.42vy=MNvH'n<]N4N]kI3e+@oqfmw+zb0Sg"],
  w 19 37 0 200018 200768 43 4037 ["`ufo:|cEqP4g*p;{)v3D_:|Q&NzQ/p%|<}rbD:/@rIw`!f}7dB;kZCyWLHRj+H0:","f$"]]

private def r19_4 : List (Chunk 19) := [
  w 19 36 0 210017 210768 46 4281 [";fUQ#9#m.2={:knOC.E=B^zTuyV;4xd{nq*$#lDCSA=gots,2HFgGZ%+2v_>zozg","$^S$?#U?0"],
  w 19 35 0 220016 220705 48 4439 [",w2ATrBRJR3gBb!f$ikB4Mh;yG{aL-#RvM~DNLSGM8Q5gLVI9_e*vLZ&Ov4>V2[.","6s{*-a~:SqlB"],
  w 19 34 0 230015 230704 50 4583 ["|*DH:ULX&h-&E_>(%W6h3LrBT@R#^<z,=F.2I35Zs;]J{bU5D{2DbqG,M;geh.sk","%Fz^y0r4oN@oSVzdr"],
  w 19 33 0 240014 240704 52 4721 ["-1yIf'binE$GJRM_1ku[8ZAyR7/DI^Qv-[divJ7O)5;6Ir_?$vmOeOI]MyRP>n_k","4AjJhsFJ4:i?t|>qeep2"]]

private def r19_5 : List (Chunk 19) := [
  w 19 32 0 250013 250641 53 4769 ["+-cQY~DOF;M]Sok*zwo8!#s@fZjYXMRXl]sUhl/W=V-.Ps~sQ;;|l+b0O)g1N`7N","2:>@)kw~CjzWGqWnbtIJ:(B"],
  w 19 31 0 260012 260640 54 4815 [">l0yzc}b[|z`5P`5o}@dCq9/cqO1X^aXAQ+XZVbQH<]tBTtE'U/s|V)=d6u,'xzV","%y'-~VJ|32>^0g/8%q3cGXe3E"],
  w 19 30 0 270011 270640 55 4843 ["]2*QP&[7|7uDh]lA10s4D,GJ(5rr5en7M$%R-)yshY>TarVR)0(AjCSd#[+5Btd>","$_!)J4WSM)e^NJZG>RAVfdj|fcG."],
  w 19 29 0 280010 280577 55 4801 ["h]/nFCqPyz~@4Rv];G5CN/DfJNxMr3KyePL3XCx/iq#{x+IA)^u0oWy:Vi%mcZn6","%<]o)7DT5uI+{u`aP)<U;1b{l$`x"]]

private def r19_6 : List (Chunk 19) := [
  w 19 28 0 290009 290576 55 4741 ["W$QF*U~~4>2K/F{e`I5CmDs=B(?Ih.Sjil?+81'ab6]K6m(r6nT(dJgoT}%b,}#.","+0-eAHEYbfi(8F`K3k#$v!I;DGWB="],
  w 19 27 0 300008 300576 55 4683 ["R&MQ07@+JXFDy/7VQ0(w,`(K!/#RH/Sm#<w2L/'V&w/RN~[QhW;9J<G=FQZVZ2G_","+0iX8Fa4|abt+vfWA#n8/DelWpz^5"],
  w 19 26 0 310007 310513 54 4539 ["kl@8O3|+nC#Yj*Z6<3hxqY1$Y~-+woWD+v{z:2YtOwSw=>w}@mM3W-*<]CS3%?+_","#Cg9_@U1]/?GH4^8+8RRb3cUsxK8o"],
  w 19 25 0 320006 320512 53 4401 ["U%PQ0l=asCio(|jF.[oWMaly^)zEMTmw]4&5q}TY0G-zN`]W/I$!3;Yg:o/>>XTR","'^`K]'@1d5;7QzL[DA2EY7B#;e4"]]

private def r19_7 : List (Chunk 19) := [
  w 19 24 0 330005 330512 52 4241 ["ZMl3Lm|-4US-e/oIs`yIqOaAsNa9Iu{E!v|VNcw{>9F]$rN6Sq0&>WI<NzLw`*^6","c~}J315h,?whX_g:7}GEI.S`=:"],
  w 19 23 0 340004 340449 50 4027 ["{fm$|[Z-<t!/P|A[z=C(nD`p6Y$deDDB$upEqC~5=!Vom+$6pN7@j^GUO5';b#|_","0$1trR693DSGTVV)VV}`D+c"],
  w 19 22 0 350003 350448 48 3791 ["iUz04?`Y_VNZtV.K3=!H|Uf_$1+J7.tgy{NA-hulq$%`W,5xs>}p0{WdJOQAI^JZ",")8POrRuX!k1%Gf'=)&c~V"],
  w 19 21 0 360002 360448 46 3565 ["0[~Z`]WpXjr:KNNvc^$S}8'EL{Eb|SAp*2X<[uk}lg9HMs^'&GiTe*%DRE14{Z;.","#Am7Fd6Mi}ctSCB2ed"]]

private def r19_8 : List (Chunk 19) := [
  w 19 20 0 370001 370385 43 3257 ["f-XkBOF|&mpB#eJ:<_5V'W65nt>CQR_V<4s69q<v+QYP#;s@Q&@!qe'MzzuHoBM6","%;2`D,A:aF<2@W"],
  w 19 19 0 380000 380384 40 2963 ["|ePU/UO+<O4m}nVcX`-K:pn'`M;b:%FEUy>A%S|#XCtbEsw-G1A8vqc8RxF5@IXR","$Q*)vT'9V"],
  w 19 18 0 390000 390384 37 2643 [")-y?y|p2sRt:K%|{Rj8*A|Wn;yV!.;sz3p{f|ojLh!t%*oPn+$:dD2uwMt6^9B+7","'CZIp"],
  w 19 17 0 400000 400321 33 2285 ["5*`QE.]ym_&@[L_pzdM9n~a`U$7rf;zKi%0I}PUp?9EU|Jq33}SpwR4K:;BSY`"]]

private def r19_9 : List (Chunk 19) := [
  w 19 16 0 410000 410320 30 2003 ["0^pRoV51y-'gl#<RRDqwFGQ+?m5H1f:}[{@Y8o>J~}{}'v1aPA6O70zX["],
  w 19 15 0 420000 420320 27 1735 ["-8YT/i*i@~'lWFTP0A]gfQfnNMw>RXD0{Mio_&^3WiUZ/#ken:o#"],
  w 19 14 0 430000 430257 24 1487 ["+V<TvL4mCh8e;2(idJBaw6j^*.cN#!XRI?$3'#p#G6JpZ!t"],
  w 19 13 0 440000 440256 21 1253 [")AHdvnq6=(czsI~@0I7(O0b%{@Nxf*'<Rd_Z`zO7*C"]]

private def r19_10 : List (Chunk 19) := [
  w 19 12 0 450000 450256 19 1083 ["#CJega=x$}{i>ScK#TG5@-^vY7t)AwWc60u0KGW"],
  w 19 11 0 460000 460193 16 879 ["#/c>BB/fnD^IAcZ)}e-;/cdT?N}/<`BN|x"],
  w 19 10 0 470000 470192 14 735 ["5[BU~{!`;'WRJsmR[2P;e0A[V8Pmd7"],
  w 19 9 0 480000 480192 12 601 ["%^<PlG<+8|vLyY:`o,@1/t)(F;x"]]

private def r19_11 : List (Chunk 19) := [
  w 19 8 0 490000 490129 10 479 ["fmZ&DF?5fsh68qmOUCc.-$K"],
  w 19 7 0 500000 500128 8 367 [".X6@E:eno)0*%zE/l>zp"],
  w 19 6 0 510000 510128 7 303 ["V&9#{M;M[>7-RM+,i+"],
  w 19 5 0 520000 520065 5 208 ["%h`d@k5dIjNthW"]]

private def r19_12 : List (Chunk 19) := [
  w 19 4 0 530000 530064 4 158 ["1RXR8%=Lx/{}"],
  w 19 3 0 540000 540064 3 112 ["9(HQUP^@4"],
  w 19 2 0 550000 550001 2 71 ["Fr0&_]"],
  w 19 1 0 560000 560000 1 34 ["Xg]"]]

private def r19_13 : List (Chunk 19) := [
  w 19 0 0 570000 570000 1 31 ["Xi$"]]
private def chunks19:List (Chunk 19):=r19_0 ++ r19_1 ++ r19_2 ++ r19_3 ++ r19_4 ++ r19_5 ++ r19_6 ++ r19_7 ++ r19_8 ++ r19_9 ++ r19_10 ++ r19_11 ++ r19_12 ++ r19_13
def rows19:=rowsFrom chunks19

theorem good19 : ∀ r ∈ rows19,good 19 r=true:=rowsFrom_good chunks19

theorem sorted19 : rows19.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks19 0 (by decide +kernel)).1

theorem mass19 (i : Fin 57) :
    bandCount 19 (i.val:ℤ) 56 14≤(rows19.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks19).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 19 (j:ℤ) 56 14≤mass j chunks19))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total19 : (rows19.map (price 19)).sum = 124915 :=
  (total_eq chunks19).trans (by decide +kernel)


end Final50RankReceipt

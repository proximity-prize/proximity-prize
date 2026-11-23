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



private def r10_0 : List (Chunk 10) := [
  w 10 30 0 640 640 1 102 [],
  w 10 29 0 10577 10577 1 102 [],
  w 10 28 0 20514 20576 2 204 [],
  w 10 27 0 30451 30576 3 302 ["#*s"]]

private def r10_1 : List (Chunk 10) := [
  w 10 26 0 40388 40513 4 404 ["*i{"],
  w 10 25 0 50325 50512 5 502 ["$-B?w"],
  w 10 24 0 60262 60512 7 698 [")fl=O`&"],
  w 10 23 0 70199 70449 8 796 ["#s75qzFRc"]]

private def r10_2 : List (Chunk 10) := [
  w 10 22 0 80136 80448 10 992 ["%[M&--|a0<k"],
  w 10 21 0 90073 90448 12 1180 [">`y7^*B`$2;]#g"],
  w 10 20 0 100010 100385 14 1376 ["YP@:_V7E$:e!r?$Z"],
  w 10 19 0 110009 110384 15 1462 ["GDZ*vM>|A]3shOEfTmk"]]

private def r10_3 : List (Chunk 10) := [
  w 10 18 0 120008 120384 17 1642 ["$tTt|NYh1h*;Mrs?DzNY#WN"],
  w 10 17 0 130007 130321 17 1630 ["*$xZL1C3o)cAB_'[p*H&Jz`N"],
  w 10 16 0 140006 140320 18 1712 ["#yn2U{>@,D8l-biHS|pkv$tx4!"],
  w 10 15 0 150005 150320 18 1688 ["(dw>jX>)'o@e<T3Fju16]Yz?.=w"]]

private def r10_4 : List (Chunk 10) := [
  w 10 14 0 160004 160257 18 1676 ["(dw?#wbv0N6DSCa|1jtTivayjP2"],
  w 10 13 0 170003 170256 17 1562 ["p8dl*o=.GHI.*r;&v,x?BefU5g"],
  w 10 12 0 180002 180256 17 1538 ["#!<Y[|FzT$T@}KDX)blvJ~b`%,!"],
  w 10 11 0 190001 190193 15 1338 ["Qa9v&]y#sUcsKit]W%1X'p{{"]]

private def r10_5 : List (Chunk 10) := [
  w 10 10 0 200000 200192 14 1228 ["$/'$zJ8nX}@@#3F]K`_b-Ug"],
  w 10 9 0 210000 210192 12 1020 ["#<EqCxJQpJ&N]3k`Nk>[x"],
  w 10 8 0 220000 220129 10 828 ["7},B?(R!d0ZNVzk!t"],
  w 10 7 0 230000 230128 8 644 ["&)J@%.CaxKJZW'"]]

private def r10_6 : List (Chunk 10) := [
  w 10 6 0 240000 240128 7 542 ["57%t.Axw^>]["],
  w 10 5 0 250000 250065 5 378 ["%VINs<pnp"],
  w 10 4 0 260000 260064 4 292 ["0hHJJ9p"],
  w 10 3 0 270000 270064 3 210 ["gMG]K"]]

private def r10_7 : List (Chunk 10) := [
  w 10 2 0 280000 280001 2 136 ["%(};"],
  w 10 1 0 290000 290000 1 66 [".d"],
  w 10 0 0 300000 300000 1 62 ["0+"]]
private def chunks10:List (Chunk 10):=r10_0 ++ r10_1 ++ r10_2 ++ r10_3 ++ r10_4 ++ r10_5 ++ r10_6 ++ r10_7
def rows10:=rowsFrom chunks10

theorem good10 : ∀ r ∈ rows10,good 10 r=true:=rowsFrom_good chunks10

theorem sorted10 : rows10.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks10 0 (by decide +kernel)).1

theorem mass10 (i : Fin 57) :
    bandCount 10 (i.val:ℤ) 56 14≤(rows10.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks10).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 10 (j:ℤ) 56 14≤mass j chunks10))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total10 : (rows10.map (price 10)).sum = 26312 :=
  (total_eq chunks10).trans (by decide +kernel)



private def r11_0 : List (Chunk 11) := [
  w 11 33 0 704 704 1 102 [],
  w 11 32 0 10641 10641 1 102 [],
  w 11 31 0 20578 20640 2 204 [],
  w 11 30 0 30515 30640 3 302 ["#*s"]]

private def r11_1 : List (Chunk 11) := [
  w 11 29 0 40452 40577 4 404 ["*i{"],
  w 11 28 0 50389 50576 5 502 ["$-B?w"],
  w 11 27 0 60326 60576 7 698 [")fl=O`&"],
  w 11 26 0 70263 70513 8 796 ["#s75qzFRc"]]

private def r11_2 : List (Chunk 11) := [
  w 11 25 0 80200 80512 10 992 ["%[M&--|a0<k"],
  w 11 24 0 90137 90512 12 1180 [">`y7^*B`$2;]#g"],
  w 11 23 0 100074 100449 14 1376 ["YP@:_V7E$:e!r?$Z"],
  w 11 22 0 110011 110448 16 1564 ["%9!sj9iQih'U$%z+sHP:"]]

private def r11_3 : List (Chunk 11) := [
  w 11 21 0 120010 120448 18 1744 ["9*I-jsq#D!e5my}U%Ysk.^o"],
  w 11 20 0 130009 130385 19 1830 ["1TCuaOEUDhQ09v&,F2}Av[2VZJ"],
  w 11 19 0 140008 140384 20 1912 ["%i/!W|DNeb1)L}Ekc&2?m}mh{7cZ"],
  w 11 18 0 150007 150384 21 1982 ["%/H[eqVm%J7iD0y(UXi$W{4-}HMoJ'_"]]

private def r11_4 : List (Chunk 11) := [
  w 11 17 0 160006 160321 21 1970 ["%/H[p>mLt}5zQKVYu@Fzhz.?-PARHQg"],
  w 11 16 0 170005 170320 21 1946 ["*hHS.<{.O/}~]035..=I48}Yr^WI^fW."],
  w 11 15 0 180004 180320 21 1922 [",L9f/XAR!HU9b'g6|T|a4ElLV)*(zT%6"],
  w 11 14 0 190003 190257 20 1808 ["#>;{xo}M`D4jI!NEhYm0m+NCDmvFJGys"]]

private def r11_5 : List (Chunk 11) := [
  w 11 13 0 200002 200256 19 1698 ["'G/4rc}NiB<=PFBJpnzZL+NFkLxfx."],
  w 11 12 0 210001 210256 18 1572 ["k:wRMzcxHC$sz|/$gQ@ganS{bt~5g"],
  w 11 11 0 220000 220193 16 1380 ["/HFLMSZ$NybdaO$:/+DkSIP|UF"],
  w 11 10 0 230000 230192 14 1172 ["(xfXS=p)Qh_YchWkx{sp-`6t"]]

private def r11_6 : List (Chunk 11) := [
  w 11 9 0 240000 240192 12 972 ["#L}{Y-jEb2qxN6Gx2Vby["],
  w 11 8 0 250000 250129 10 788 [";'[[?ct)b30_z:p4l"],
  w 11 7 0 260000 260128 8 612 ["&_(jz(E9*x5rN3"],
  w 11 6 0 270000 270128 7 514 ["7XVpSKd)dioC"]]

private def r11_7 : List (Chunk 11) := [
  w 11 5 0 280000 280065 5 358 ["&!m|$i%Ll"],
  w 11 4 0 290000 290064 4 276 ["2V?nX'G"],
  w 11 3 0 300000 300064 3 198 ["n|4T["],
  w 11 2 0 310000 310001 2 128 ["%G|'"]]

private def r11_8 : List (Chunk 11) := [
  w 11 1 0 320000 320000 1 62 ["0+"],
  w 11 0 0 330000 330000 1 58 ["1O"]]
private def chunks11:List (Chunk 11):=r11_0 ++ r11_1 ++ r11_2 ++ r11_3 ++ r11_4 ++ r11_5 ++ r11_6 ++ r11_7 ++ r11_8
def rows11:=rowsFrom chunks11

theorem good11 : ∀ r ∈ rows11,good 11 r=true:=rowsFrom_good chunks11

theorem sorted11 : rows11.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks11 0 (by decide +kernel)).1

theorem mass11 (i : Fin 57) :
    bandCount 11 (i.val:ℤ) 56 14≤(rows11.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks11).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 11 (j:ℤ) 56 14≤mass j chunks11))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total11 : (rows11.map (price 11)).sum = 33124 :=
  (total_eq chunks11).trans (by decide +kernel)



private def r12_0 : List (Chunk 12) := [
  w 12 36 0 768 768 1 102 [],
  w 12 35 0 10705 10705 1 102 [],
  w 12 34 0 20642 20704 2 204 [],
  w 12 33 0 30579 30704 3 302 ["#*s"]]

private def r12_1 : List (Chunk 12) := [
  w 12 32 0 40516 40641 4 404 ["*i{"],
  w 12 31 0 50453 50640 5 502 ["$-B?w"],
  w 12 30 0 60390 60640 7 698 [")fl=O`&"],
  w 12 29 0 70327 70577 8 796 ["#s75qzFRc"]]

private def r12_2 : List (Chunk 12) := [
  w 12 28 0 80264 80576 10 992 ["%[M&--|a0<k"],
  w 12 27 0 90201 90576 12 1180 [">`y7^*B`$2;]#g"],
  w 12 26 0 100138 100513 14 1376 ["YP@:_V7E$:e!r?$Z"],
  w 12 25 0 110075 110512 16 1564 ["%9!sj9iQih'U$%z+sHP:"]]

private def r12_3 : List (Chunk 12) := [
  w 12 24 0 120012 120512 19 1846 ["$!fG$9$k,{'heQUsJ>r$;+4Z"],
  w 12 23 0 130011 130449 20 1932 ["#BDz3Iz*M$&+8)6Bv/Mqj:|JVvN"],
  w 12 22 0 140010 140448 22 2112 [")<%::MZORw!`hm[+i7^z+a6Sql_u+N"],
  w 12 21 0 150009 150448 23 2182 ["(*7v&Co~p*/Z&5ro2FJ9*[@gh}>/c0Hdo"]]

private def r12_4 : List (Chunk 12) := [
  w 12 20 0 160008 160385 24 2264 ["#MUE[Ywvu([4,!]B3FY4[[Km|%OTOu=J^s:"],
  w 12 19 0 170007 170384 24 2240 ["&+8<f=2BS+gQo~LffxD%>/4P(V=K-=)7L=^F"],
  w 12 18 0 180006 180384 25 2306 ["#3'${nCD)I#h#7k7^Xr}|<XG0/DHN=(sC[VbR{"],
  w 12 17 0 190005 190321 24 2192 ["/]-sQBA<c'wv?]e[)DidC+u6RHS<,J`BjDO(2"]]

private def r12_5 : List (Chunk 12) := [
  w 12 16 0 200004 200320 24 2168 ["/]7'>E.4JC8ZF.pgH?Hm]0s69Cp2o_yZQ([J:"],
  w 12 15 0 210003 210320 23 2042 ["#}@CDn;'7.YhriByZ)Y}t'j#Y_g~7k7A)[#/."],
  w 12 14 0 220002 220257 22 1932 ["*3S=MLHFol(LG.?.^fy:Jp{Q`>_Ll^[OD[N"],
  w 12 13 0 230001 230256 20 1724 ["&7>!hCAWuvSc=t'[(-sKw6UJpF2f=CQ=F"]]

private def r12_6 : List (Chunk 12) := [
  w 12 12 0 240000 240256 19 1602 ["5yDn#$P~|>EIHvRG{Lr(K@TI`V@Y:EV"],
  w 12 11 0 250000 250193 16 1316 ["LVIU7ta&([G3(*UPf+`lkMG|q$["],
  w 12 10 0 260000 260192 14 1116 [")v/2r=a_aQ{nu4h^5}2mY0NC"],
  w 12 9 0 270000 270192 12 924 ["#^X(o@,9Rx`D@9%2sC)9?"]]

private def r12_7 : List (Chunk 12) := [
  w 12 8 0 280000 280129 10 748 [">/.u@A80`5cp?WuFd"],
  w 12 7 0 290000 290128 8 580 ["'6d7r!Fn:F~,E?"],
  w 12 6 0 300000 300128 7 486 ["9{+lyUN8k7$+"],
  w 12 5 0 310000 310065 5 338 ["&K4K377+h"]]

private def r12_8 : List (Chunk 12) := [
  w 12 4 0 320000 320064 4 260 ["4E74fq|"],
  w 12 3 0 330000 330064 3 186 ["vL~Ll"],
  w 12 2 0 340000 340001 2 120 ["%gzp"],
  w 12 1 0 350000 350000 1 58 ["1O"]]

private def r12_9 : List (Chunk 12) := [
  w 12 0 0 360000 360000 1 54 ["2t"]]
private def chunks12:List (Chunk 12):=r12_0 ++ r12_1 ++ r12_2 ++ r12_3 ++ r12_4 ++ r12_5 ++ r12_6 ++ r12_7 ++ r12_8 ++ r12_9
def rows12:=rowsFrom chunks12

theorem good12 : ∀ r ∈ rows12,good 12 r=true:=rowsFrom_good chunks12

theorem sorted12 : rows12.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks12 0 (by decide +kernel)).1

theorem mass12 (i : Fin 57) :
    bandCount 12 (i.val:ℤ) 56 14≤(rows12.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks12).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 12 (j:ℤ) 56 14≤mass j chunks12))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total12 : (rows12.map (price 12)).sum = 40950 :=
  (total_eq chunks12).trans (by decide +kernel)



private def r13_0 : List (Chunk 13) := [
  w 13 39 0 832 832 1 102 [],
  w 13 38 0 10769 10769 1 102 [],
  w 13 37 0 20706 20768 2 204 [],
  w 13 36 0 30643 30768 3 302 ["#*s"]]

private def r13_1 : List (Chunk 13) := [
  w 13 35 0 40580 40705 4 404 ["*i{"],
  w 13 34 0 50517 50704 5 502 ["$-B?w"],
  w 13 33 0 60454 60704 7 698 [")fl=O`&"],
  w 13 32 0 70391 70641 8 796 ["#s75qzFRc"]]

private def r13_2 : List (Chunk 13) := [
  w 13 31 0 80328 80640 10 992 ["%[M&--|a0<k"],
  w 13 30 0 90265 90640 12 1180 [">`y7^*B`$2;]#g"],
  w 13 29 0 100202 100577 14 1376 ["YP@:_V7E$:e!r?$Z"],
  w 13 28 0 110139 110576 16 1564 ["%9!sj9iQih'U$%z+sHP:"]]

private def r13_3 : List (Chunk 13) := [
  w 13 27 0 120076 120576 19 1846 ["$!fG$9$k,{'heQUsJ>r$;+4Z"],
  w 13 26 0 130013 130513 21 2034 [",n%WQMVfg2Blw[ir71mq41jRY9o"],
  w 13 25 0 140012 140512 23 2214 ["]:<,-kv{9>'D(N{q+t5VpGk@qG=.no"],
  w 13 24 0 150011 150512 25 2382 ["-kM*W`pwE.M%[$m2@Ax&2baMdDm>z?N0ev6"]]

private def r13_4 : List (Chunk 13) := [
  w 13 23 0 160010 160449 26 2464 ["$qG5FU5/c)z8!y*zBL?}p,1uakPI`369%DOTc"],
  w 13 22 0 170009 170448 27 2534 ["#wbg4nD4R3:q3?)SsEU?{JlNM'^mPT6N^`0_z7'N"],
  w 13 21 0 180008 180448 28 2600 ["U);7,N7G?DwMZz,U@,'x|i^b9yd/xe<#Y.&MtQ#D!"],
  w 13 20 0 190007 190385 28 2576 ["#T.89&_=.FQgT[u4U1*OPKG9|1:{F<Cv~9M0~_y|@VZ"]]

private def r13_5 : List (Chunk 13) := [
  w 13 19 0 200006 200384 28 2552 ["#T/;~A!fxrp)e/o!Vw[mtYj&.IYgRQV*ak,c^C~RI|>"],
  w 13 18 0 210005 210384 28 2512 ["&~~TUg<?Wu2m:dgNf9VdBYooPu=|l.YF?&ai2F52YY2:"],
  w 13 17 0 220004 220321 27 2402 ["6`(ik*:}$`b5AhavGO]{k!{%3_J~E,bb'[0AhMj,b&"],
  w 13 16 0 230003 230320 26 2276 ["$W^pMww9uz7?|RrL)5H#WkQs2>UwA)D2vYs.lnhRSN"]]

private def r13_6 : List (Chunk 13) := [
  w 13 15 0 240002 240320 25 2154 [".1l(ZE-/Hul]=l7zq(^xA5[?,drV9+vspO7LwJ$s"],
  w 13 14 0 250001 250257 23 1946 ["(<Nq%b9CgR'pc?cZ`vN?=DVMYtGk24EG4T7C)V"],
  w 13 13 0 260000 260256 21 1746 ["#1G8&A}w{1QR{i#eZPDm91N{-^Y~CIVOi+N"],
  w 13 12 0 270000 270256 19 1526 ["a>#ql+l-rxCC2;/ZP.ykV+Jh.:g2%gn?"]]

private def r13_7 : List (Chunk 13) := [
  w 13 11 0 280000 280193 16 1252 ["Qm#_<[>363W)D=oe;h8lfFt8O&t"],
  w 13 10 0 290000 290192 14 1060 ["*sTj3=R7p<;&)^xOO~Nk(^fp"],
  w 13 9 0 300000 300192 12 876 ["#o33'RK-DaMn2;_JV/LV#"],
  w 13 8 0 310000 310129 10 708 ["A6_1@|Y7^89#buzX["]]

private def r13_8 : List (Chunk 13) := [
  w 13 7 0 320000 320128 8 548 ["'lAbiyHEIsiC<K"],
  w 13 6 0 330000 330128 7 458 ["<?]iA`9Gqb5p"],
  w 13 5 0 340000 340065 5 318 ["&tWxAcHgd"],
  w 13 4 0 350000 350064 4 244 ["64.Wt_S"]]

private def r13_9 : List (Chunk 13) := [
  w 13 3 0 360000 360064 3 174 ["}{kD|"],
  w 13 2 0 370000 370001 2 112 ["&)y["],
  w 13 1 0 380000 380000 1 54 ["2t"],
  w 13 0 0 390000 390000 1 50 ["4;"]]
private def chunks13:List (Chunk 13):=r13_0 ++ r13_1 ++ r13_2 ++ r13_3 ++ r13_4 ++ r13_5 ++ r13_6 ++ r13_7 ++ r13_8 ++ r13_9
def rows13:=rowsFrom chunks13

theorem good13 : ∀ r ∈ rows13,good 13 r=true:=rowsFrom_good chunks13

theorem sorted13 : rows13.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks13 0 (by decide +kernel)).1

theorem mass13 (i : Fin 57) :
    bandCount 13 (i.val:ℤ) 56 14≤(rows13.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks13).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 13 (j:ℤ) 56 14≤mass j chunks13))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total13 : (rows13.map (price 13)).sum = 49840 :=
  (total_eq chunks13).trans (by decide +kernel)



private def r14_0 : List (Chunk 14) := [
  w 14 42 0 896 896 1 102 [],
  w 14 41 0 10833 10833 1 102 [],
  w 14 40 0 20770 20832 2 204 [],
  w 14 39 0 30707 30832 3 302 ["#*s"]]

private def r14_1 : List (Chunk 14) := [
  w 14 38 0 40644 40769 4 404 ["*i{"],
  w 14 37 0 50581 50768 5 502 ["$-B?w"],
  w 14 36 0 60518 60768 7 698 [")fl=O`&"],
  w 14 35 0 70455 70705 8 796 ["#s75qzFRc"]]

private def r14_2 : List (Chunk 14) := [
  w 14 34 0 80392 80704 10 992 ["%[M&--|a0<k"],
  w 14 33 0 90329 90704 12 1180 [">`y7^*B`$2;]#g"],
  w 14 32 0 100266 100641 14 1376 ["YP@:_V7E$:e!r?$Z"],
  w 14 31 0 110203 110640 16 1564 ["%9!sj9iQih'U$%z+sHP:"]]

private def r14_3 : List (Chunk 14) := [
  w 14 30 0 120140 120640 19 1846 ["$!fG$9$k,{'heQUsJ>r$;+4Z"],
  w 14 29 0 130077 130577 21 2034 [",n%WQMVfg2Blw[ir71mq41jRY9o"],
  w 14 28 0 140014 140576 24 2316 ["'(,:t$A=a$JL{Uvekr'cXf<<an8C,XZ"],
  w 14 27 0 150013 150576 26 2484 ["#$=gg`DjA')g>{8KH]jFCKSIlb$LQXUp;n7g"]]

private def r14_4 : List (Chunk 14) := [
  w 14 26 0 160012 160513 28 2664 ["'QymiH9P12zN1e_lkFdcC*E^B`g.jo]a@S%.&D2"],
  w 14 25 0 170011 170512 29 2734 ["%e$bPALempYWJ=j-/rkFIe[eI2a5BS6!1?Qb4(@IgJ"],
  w 14 24 0 180010 180512 31 2894 ["9x&B3bWUUfR[3`.B'#58%P,b`u2A=u8m{<;_/Z``MZITB"],
  w 14 23 0 190009 190449 31 2870 ["eV_-XM%^pHIiJz-ZyPm%,z.k-~$t4?8+ju8D.h-mOnsdr6"]]

private def r14_5 : List (Chunk 14) := [
  w 14 22 0 200008 200448 32 2936 ["2,({e+W{/K4>v5G(UIA5_*0jIb1+x8'3K~Zl3;QN6Wq6'`K_"],
  w 14 21 0 210007 210448 32 2896 ["V.0||f>4|r>Pv_+sI.3zRQW$#wgmw8kzT(8qXI-piAJs:.xt>"],
  w 14 20 0 220006 220385 32 2872 ["V.0~@KctW%uX5OEdNi|jS5zE2*wV'yKOOi/$u{nI2%GPM(CYV"],
  w 14 19 0 230005 230384 31 2746 ["(QU^]`}A]HBodCR@g;8i%`#sT}&q,E+Y-SHz9[mD+|pIl4G~&"]]

private def r14_6 : List (Chunk 14) := [
  w 14 18 0 240004 240384 31 2706 [")IW+$FUYA|JRQska#;X/^@.CI0EMPpW13D]0dt0^jk!gj04'>"],
  w 14 17 0 250003 250321 29 2498 ["%p.Ys2N?[R(j8V4#q5KVf[!stB0-R:FyJ><:p9hbvC)F?Xs"],
  w 14 16 0 260002 260320 28 2376 ["1rSD}23I*CW8aPhnj%A*oh`s(J9;8;{u4dDWFeE>}#!:J"],
  w 14 15 0 270001 270320 26 2156 ["+4`-`[HqWG/`n)opsK^W`ZbBOz.d>PQsk$wt6WUvHC."]]

private def r14_7 : List (Chunk 14) := [
  w 14 14 0 280000 280257 24 1956 ["#d3/N7uhT%PpW<^GYwbg3(]><Xd[Zs$T5?!=GQ5&"],
  w 14 13 0 290000 290256 21 1662 ["%^ZKAWNZKY;Y$NS;3^pLxz${3(J-suh'(YUp"],
  w 14 12 0 300000 300256 19 1450 ["h-aorBYMnAg._;sQD,[U33t1t5r4=]`h"],
  w 14 11 0 310000 310193 16 1188 ["W%YhABy@Chg|aQ+xoFnla@BQ.)/"]]

private def r14_8 : List (Chunk 14) := [
  w 14 10 0 320000 320192 14 1004 ["+p{CQ=Cn!&W:;++Ak!khT.~?"],
  w 14 9 0 330000 330192 12 828 ["$!k=<ej~6I<:$>;c9xpsd"],
  w 14 8 0 340000 340129 10 668 ["D>1JAY{>[:l4(6!kS"],
  w 14 7 0 350000 350128 8 516 ["(C}/asIzYBSZ3W"]]

private def r14_9 : List (Chunk 14) := [
  w 14 6 0 360000 360128 7 430 [">b1egj$Vx/GW"],
  w 14 5 0 370000 370065 5 298 ["'?|GP1ZE`"],
  w 14 4 0 380000 380064 4 228 ["8#%|%L+"],
  w 14 3 0 390000 390064 3 162 ["#(LW=/"]]

private def r14_10 : List (Chunk 14) := [
  w 14 2 0 400000 400001 2 104 ["&HxG"],
  w 14 1 0 410000 410000 1 50 ["4;"],
  w 14 0 0 420000 420000 1 46 ["5`"]]
private def chunks14:List (Chunk 14):=r14_0 ++ r14_1 ++ r14_2 ++ r14_3 ++ r14_4 ++ r14_5 ++ r14_6 ++ r14_7 ++ r14_8 ++ r14_9 ++ r14_10
def rows14:=rowsFrom chunks14

theorem good14 : ∀ r ∈ rows14,good 14 r=true:=rowsFrom_good chunks14

theorem sorted14 : rows14.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks14 0 (by decide +kernel)).1

theorem mass14 (i : Fin 57) :
    bandCount 14 (i.val:ℤ) 56 14≤(rows14.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks14).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 14 (j:ℤ) 56 14≤mass j chunks14))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total14 : (rows14.map (price 14)).sum = 59840 :=
  (total_eq chunks14).trans (by decide +kernel)


end Final50RankReceipt

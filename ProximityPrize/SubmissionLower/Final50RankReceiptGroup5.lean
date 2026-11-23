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



private def r5_0 : List (Chunk 5) := [
  w 5 15 0 320 320 1 102 [],
  w 5 14 0 10257 10257 1 102 [],
  w 5 13 0 20194 20256 2 204 [],
  w 5 12 0 30131 30256 3 302 ["#*s"]]

private def r5_1 : List (Chunk 5) := [
  w 5 11 0 40068 40193 4 404 ["*i{"],
  w 5 10 0 50005 50192 5 502 ["$-B?w"],
  w 5 9 0 60004 60192 6 596 ["{|_y5."],
  w 5 8 0 70003 70129 6 592 ["$bWOl8.:"]]

private def r5_2 : List (Chunk 5) := [
  w 5 7 0 80002 80128 6 588 ["$b]dHGS>"],
  w 5 6 0 90001 90128 6 576 ["-!!c%]/IV"],
  w 5 5 0 100000 100065 5 478 ["OLJ;q_{"],
  w 5 4 0 110000 110064 4 372 ["'atRb:#"]]

private def r5_3 : List (Chunk 5) := [
  w 5 3 0 120000 120064 3 270 ["@}K'W"],
  w 5 2 0 130000 130001 2 176 ["#F&C"],
  w 5 1 0 140000 140000 1 86 ["'h"],
  w 5 0 0 150000 150000 1 82 [")/"]]
private def chunks5:List (Chunk 5):=r5_0 ++ r5_1 ++ r5_2 ++ r5_3
def rows5:=rowsFrom chunks5

theorem good5 : ∀ r ∈ rows5,good 5 r=true:=rowsFrom_good chunks5

theorem sorted5 : rows5.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks5 0 (by decide +kernel)).1

theorem mass5 (i : Fin 57) :
    bandCount 5 (i.val:ℤ) 56 14≤(rows5.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks5).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 5 (j:ℤ) 56 14≤mass j chunks5))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total5 : (rows5.map (price 5)).sum = 5432 :=
  (total_eq chunks5).trans (by decide +kernel)



private def r6_0 : List (Chunk 6) := [
  w 6 18 0 384 384 1 102 [],
  w 6 17 0 10321 10321 1 102 [],
  w 6 16 0 20258 20320 2 204 [],
  w 6 15 0 30195 30320 3 302 ["#*s"]]

private def r6_1 : List (Chunk 6) := [
  w 6 14 0 40132 40257 4 404 ["*i{"],
  w 6 13 0 50069 50256 5 502 ["$-B?w"],
  w 6 12 0 60006 60256 7 698 [")fl=O`&"],
  w 6 11 0 70005 70193 7 694 ["7R^}Cx(*"]]

private def r6_2 : List (Chunk 6) := [
  w 6 10 0 80004 80192 8 788 ["'5C-`~{_Y&"],
  w 6 9 0 90003 90192 8 776 ["7<|A{Xn%e3."],
  w 6 8 0 100002 100129 8 772 ["7<|C6XEmiH!"],
  w 6 7 0 110001 110128 7 666 ["$_vaWFm75&J"]]

private def r6_3 : List (Chunk 6) := [
  w 6 6 0 120000 120128 7 654 ["%Q&@#Ga:V;o"],
  w 6 5 0 130000 130065 5 458 ["#mtV8H):#"],
  w 6 4 0 140000 140064 4 356 [")Okvp'W"],
  w 6 3 0 150000 150064 3 258 ["HN7|h"]]

private def r6_4 : List (Chunk 6) := [
  w 6 2 0 160000 160001 2 168 ["#f%/"],
  w 6 1 0 170000 170000 1 82 [")/"],
  w 6 0 0 180000 180000 1 78 ["*S"]]
private def chunks6:List (Chunk 6):=r6_0 ++ r6_1 ++ r6_2 ++ r6_3 ++ r6_4
def rows6:=rowsFrom chunks6

theorem good6 : ∀ r ∈ rows6,good 6 r=true:=rowsFrom_good chunks6

theorem sorted6 : rows6.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks6 0 (by decide +kernel)).1

theorem mass6 (i : Fin 57) :
    bandCount 6 (i.val:ℤ) 56 14≤(rows6.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks6).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 6 (j:ℤ) 56 14≤mass j chunks6))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total6 : (rows6.map (price 6)).sum = 8064 :=
  (total_eq chunks6).trans (by decide +kernel)



private def r7_0 : List (Chunk 7) := [
  w 7 21 0 448 448 1 102 [],
  w 7 20 0 10385 10385 1 102 [],
  w 7 19 0 20322 20384 2 204 [],
  w 7 18 0 30259 30384 3 302 ["#*s"]]

private def r7_1 : List (Chunk 7) := [
  w 7 17 0 40196 40321 4 404 ["*i{"],
  w 7 16 0 50133 50320 5 502 ["$-B?w"],
  w 7 15 0 60070 60320 7 698 [")fl=O`&"],
  w 7 14 0 70007 70257 8 796 ["#s75qzFRc"]]

private def r7_2 : List (Chunk 7) := [
  w 7 13 0 80006 80256 9 890 ["Kat#E~d:kB"],
  w 7 12 0 90005 90256 10 976 ["K6%5Z3hzeDup_"],
  w 7 11 0 100004 100193 10 972 ["K6%8&f$#if^JZ"],
  w 7 10 0 110003 110192 10 960 ["#8dF:[9(ZE$$Qho"]]

private def r7_3 : List (Chunk 7) := [
  w 7 9 0 120002 120192 10 948 ["#^>H*{4Pyr,<Jw{"],
  w 7 8 0 130001 130129 9 842 ["4w&i|-K6%0+P'>"],
  w 7 7 0 140000 140128 8 740 ["q20N?WSg^c;o"],
  w 7 6 0 150000 150128 7 626 ["..J~x$ZIIy'G"]]

private def r7_4 : List (Chunk 7) := [
  w 7 5 0 160000 160065 5 438 ["$9;&Ft:u|"],
  w 7 4 0 170000 170064 4 340 ["+>c<}r/"],
  w 7 3 0 180000 180064 3 246 ["O}$tx"],
  w 7 2 0 190000 190001 2 160 ["$(#x"]]

private def r7_5 : List (Chunk 7) := [
  w 7 1 0 200000 200000 1 78 ["*S"],
  w 7 0 0 210000 210000 1 74 ["+x"]]
private def chunks7:List (Chunk 7):=r7_0 ++ r7_1 ++ r7_2 ++ r7_3 ++ r7_4 ++ r7_5
def rows7:=rowsFrom chunks7

theorem good7 : ∀ r ∈ rows7,good 7 r=true:=rowsFrom_good chunks7

theorem sorted7 : rows7.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks7 0 (by decide +kernel)).1

theorem mass7 (i : Fin 57) :
    bandCount 7 (i.val:ℤ) 56 14≤(rows7.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks7).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 7 (j:ℤ) 56 14≤mass j chunks7))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total7 : (rows7.map (price 7)).sum = 11400 :=
  (total_eq chunks7).trans (by decide +kernel)



private def r8_0 : List (Chunk 8) := [
  w 8 24 0 512 512 1 102 [],
  w 8 23 0 10449 10449 1 102 [],
  w 8 22 0 20386 20448 2 204 [],
  w 8 21 0 30323 30448 3 302 ["#*s"]]

private def r8_1 : List (Chunk 8) := [
  w 8 20 0 40260 40385 4 404 ["*i{"],
  w 8 19 0 50197 50384 5 502 ["$-B?w"],
  w 8 18 0 60134 60384 7 698 [")fl=O`&"],
  w 8 17 0 70071 70321 8 796 ["#s75qzFRc"]]

private def r8_2 : List (Chunk 8) := [
  w 8 16 0 80008 80320 10 992 ["%[M&--|a0<k"],
  w 8 15 0 90007 90320 11 1078 ["%Wg;ctT)[j%4h6"],
  w 8 14 0 100006 100257 12 1172 ["rkB!z()fY#$tg#N"],
  w 8 13 0 110005 110256 12 1160 ["$H&OqkvZl__|&[996"]]

private def r8_3 : List (Chunk 8) := [
  w 8 12 0 120004 120256 13 1242 ["is&A0Tyx3Ns&+y!BP!"],
  w 8 11 0 130003 130193 12 1136 ["*r!T<ugCxJqVp6L/Fk"],
  w 8 10 0 140002 140192 12 1124 ["*r+F~bMavXVEZEDDSo"],
  w 8 9 0 150001 150192 11 1010 ["#DRaGpgZ'kZ*U]3-FJ"]]

private def r8_4 : List (Chunk 8) := [
  w 8 8 0 160000 160129 10 908 ["'awgErdBZL7Z!,_{"],
  w 8 7 0 170000 170128 8 708 ["$y1H5:@TXOu,il"],
  w 8 6 0 180000 180128 7 598 ["0O|{@.EXPF9/"],
  w 8 5 0 190000 190065 5 418 ["$b_RUBLSx"]]

private def r8_5 : List (Chunk 8) := [
  w 8 4 0 200000 200064 4 324 ["--Ya._d"],
  w 8 3 0 210000 210064 3 234 ["WMnm+"],
  w 8 2 0 220000 220001 2 152 ["$G!d"],
  w 8 1 0 230000 230000 1 74 ["+x"]]

private def r8_6 : List (Chunk 8) := [
  w 8 0 0 240000 240000 1 70 ["-?"]]
private def chunks8:List (Chunk 8):=r8_0 ++ r8_1 ++ r8_2 ++ r8_3 ++ r8_4 ++ r8_5 ++ r8_6
def rows8:=rowsFrom chunks8

theorem good8 : ∀ r ∈ rows8,good 8 r=true:=rowsFrom_good chunks8

theorem sorted8 : rows8.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks8 0 (by decide +kernel)).1

theorem mass8 (i : Fin 57) :
    bandCount 8 (i.val:ℤ) 56 14≤(rows8.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks8).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 8 (j:ℤ) 56 14≤mass j chunks8))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total8 : (rows8.map (price 8)).sum = 15510 :=
  (total_eq chunks8).trans (by decide +kernel)



private def r9_0 : List (Chunk 9) := [
  w 9 27 0 576 576 1 102 [],
  w 9 26 0 10513 10513 1 102 [],
  w 9 25 0 20450 20512 2 204 [],
  w 9 24 0 30387 30512 3 302 ["#*s"]]

private def r9_1 : List (Chunk 9) := [
  w 9 23 0 40324 40449 4 404 ["*i{"],
  w 9 22 0 50261 50448 5 502 ["$-B?w"],
  w 9 21 0 60198 60448 7 698 [")fl=O`&"],
  w 9 20 0 70135 70385 8 796 ["#s75qzFRc"]]

private def r9_2 : List (Chunk 9) := [
  w 9 19 0 80072 80384 10 992 ["%[M&--|a0<k"],
  w 9 18 0 90009 90384 12 1180 [">`y7^*B`$2;]#g"],
  w 9 17 0 100008 100321 13 1274 ["(y<k)VR`sk*9+w-o"],
  w 9 16 0 110007 110320 14 1360 ["&`o#,Iw-1Kj7Xb1{yqB"]]

private def r9_3 : List (Chunk 9) := [
  w 9 15 0 120006 120320 15 1442 ["#O3%B_roZE8@ivW:0vo.Z"],
  w 9 14 0 130005 130257 15 1430 ["&/fGR#^LeB!m';]Z4dRiFZ"],
  w 9 13 0 140004 140256 15 1418 ["&/jU,I.%]4nX]U0),(`j!{"],
  w 9 12 0 150003 150256 15 1394 ["0A:.W2|T#zO#rL+#.H9}VPc"]]

private def r9_4 : List (Chunk 9) := [
  w 9 11 0 160002 160193 14 1292 ["^::>8{GEDrt`yRNyCEt8s"],
  w 9 10 0 170001 170192 13 1178 [")GY!(@I~}G$e'~u3RY|jV"],
  w 9 9 0 180000 180192 12 1068 ["FWKfnr_DE`+}[4Mil<B"],
  w 9 8 0 190000 190129 10 868 ["4uY)>J0xf.(>4]em|"]]

private def r9_5 : List (Chunk 9) := [
  w 9 7 0 200000 200128 8 676 ["%Pls-4B,h|`C`x"],
  w 9 6 0 210000 210128 7 570 ["2rPwf80hVqJt"],
  w 9 5 0 220000 220065 5 398 ["%.&!dn_2t"],
  w 9 4 0 230000 230064 4 308 [".yQ'<L;"]]

private def r9_6 : List (Chunk 9) := [
  w 9 3 0 240000 240064 3 222 ["_|Ze;"],
  w 9 2 0 250000 250001 2 144 ["$f~O"],
  w 9 1 0 260000 260000 1 70 ["-?"],
  w 9 0 0 270000 270000 1 66 [".d"]]
private def chunks9:List (Chunk 9):=r9_0 ++ r9_1 ++ r9_2 ++ r9_3 ++ r9_4 ++ r9_5 ++ r9_6
def rows9:=rowsFrom chunks9

theorem good9 : ∀ r ∈ rows9,good 9 r=true:=rowsFrom_good chunks9

theorem sorted9 : rows9.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks9 0 (by decide +kernel)).1

theorem mass9 (i : Fin 57) :
    bandCount 9 (i.val:ℤ) 56 14≤(rows9.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks9).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 9 (j:ℤ) 56 14≤mass j chunks9))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total9 : (rows9.map (price 9)).sum = 20460 :=
  (total_eq chunks9).trans (by decide +kernel)


end Final50RankReceipt

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



private def r0_0 : List (Chunk 0) := [
  w 0 0 0 0 0 1 102 []]
private def chunks0:List (Chunk 0):=r0_0
def rows0:=rowsFrom chunks0

theorem good0 : ∀ r ∈ rows0,good 0 r=true:=rowsFrom_good chunks0

theorem sorted0 : rows0.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks0 0 (by decide +kernel)).1

theorem mass0 (i : Fin 57) :
    bandCount 0 (i.val:ℤ) 56 14≤(rows0.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks0).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 0 (j:ℤ) 56 14≤mass j chunks0))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total0 : (rows0.map (price 0)).sum = 102 :=
  (total_eq chunks0).trans (by decide +kernel)



private def r1_0 : List (Chunk 1) := [
  w 1 3 0 64 64 1 102 [],
  w 1 2 0 10001 10001 1 102 [],
  w 1 1 0 20000 20000 1 102 [],
  w 1 0 0 30000 30000 1 98 ["#W"]]
private def chunks1:List (Chunk 1):=r1_0
def rows1:=rowsFrom chunks1

theorem good1 : ∀ r ∈ rows1,good 1 r=true:=rowsFrom_good chunks1

theorem sorted1 : rows1.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks1 0 (by decide +kernel)).1

theorem mass1 (i : Fin 57) :
    bandCount 1 (i.val:ℤ) 56 14≤(rows1.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks1).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 1 (j:ℤ) 56 14≤mass j chunks1))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total1 : (rows1.map (price 1)).sum = 404 :=
  (total_eq chunks1).trans (by decide +kernel)



private def r2_0 : List (Chunk 2) := [
  w 2 6 0 128 128 1 102 [],
  w 2 5 0 10065 10065 1 102 [],
  w 2 4 0 20002 20064 2 204 [],
  w 2 3 0 30001 30064 2 200 [".Z"]]

private def r2_1 : List (Chunk 2) := [
  w 2 2 0 40000 40001 2 200 [".Z"],
  w 2 1 0 50000 50000 1 98 ["#W"],
  w 2 0 0 60000 60000 1 94 ["$|"]]
private def chunks2:List (Chunk 2):=r2_0 ++ r2_1
def rows2:=rowsFrom chunks2

theorem good2 : ∀ r ∈ rows2,good 2 r=true:=rowsFrom_good chunks2

theorem sorted2 : rows2.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks2 0 (by decide +kernel)).1

theorem mass2 (i : Fin 57) :
    bandCount 2 (i.val:ℤ) 56 14≤(rows2.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks2).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 2 (j:ℤ) 56 14≤mass j chunks2))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total2 : (rows2.map (price 2)).sum = 1000 :=
  (total_eq chunks2).trans (by decide +kernel)



private def r3_0 : List (Chunk 3) := [
  w 3 9 0 192 192 1 102 [],
  w 3 8 0 10129 10129 1 102 [],
  w 3 7 0 20066 20128 2 204 [],
  w 3 6 0 30003 30128 3 302 ["#*s"]]

private def r3_1 : List (Chunk 3) := [
  w 3 5 0 40002 40065 3 302 ["#*s"],
  w 3 4 0 50001 50064 3 298 ["%&n6"],
  w 3 3 0 60000 60064 3 294 ["'gXB"],
  w 3 2 0 70000 70001 2 192 ["e(l"]]

private def r3_2 : List (Chunk 3) := [
  w 3 1 0 80000 80000 1 94 ["$|"],
  w 3 0 0 90000 90000 1 90 ["&C"]]
private def chunks3:List (Chunk 3):=r3_0 ++ r3_1 ++ r3_2
def rows3:=rowsFrom chunks3

theorem good3 : ∀ r ∈ rows3,good 3 r=true:=rowsFrom_good chunks3

theorem sorted3 : rows3.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks3 0 (by decide +kernel)).1

theorem mass3 (i : Fin 57) :
    bandCount 3 (i.val:ℤ) 56 14≤(rows3.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks3).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 3 (j:ℤ) 56 14≤mass j chunks3))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total3 : (rows3.map (price 3)).sum = 1980 :=
  (total_eq chunks3).trans (by decide +kernel)



private def r4_0 : List (Chunk 4) := [
  w 4 12 0 256 256 1 102 [],
  w 4 11 0 10193 10193 1 102 [],
  w 4 10 0 20130 20192 2 204 [],
  w 4 9 0 30067 30192 3 302 ["#*s"]]

private def r4_1 : List (Chunk 4) := [
  w 4 8 0 40004 40129 4 404 ["*i{"],
  w 4 7 0 50003 50128 4 400 [":HSg"],
  w 4 6 0 60002 60128 5 494 ["--5,jF"],
  w 4 5 0 70001 70065 4 392 ["#Eut{{"]]

private def r4_2 : List (Chunk 4) := [
  w 4 4 0 80000 80064 4 388 ["#ExWg*"],
  w 4 3 0 90000 90064 3 282 ["9N_/G"],
  w 4 2 0 100000 100001 2 184 ["#''W"],
  w 4 1 0 110000 110000 1 90 ["&C"]]

private def r4_3 : List (Chunk 4) := [
  w 4 0 0 120000 120000 1 86 ["'h"]]
private def chunks4:List (Chunk 4):=r4_0 ++ r4_1 ++ r4_2 ++ r4_3
def rows4:=rowsFrom chunks4

theorem good4 : ∀ r ∈ rows4,good 4 r=true:=rowsFrom_good chunks4

theorem sorted4 : rows4.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks4 0 (by decide +kernel)).1

theorem mass4 (i : Fin 57) :
    bandCount 4 (i.val:ℤ) 56 14≤(rows4.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks4).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 4 (j:ℤ) 56 14≤mass j chunks4))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total4 : (rows4.map (price 4)).sum = 3430 :=
  (total_eq chunks4).trans (by decide +kernel)


end Final50RankReceipt

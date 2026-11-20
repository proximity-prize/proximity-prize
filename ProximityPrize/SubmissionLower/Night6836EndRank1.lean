/- Apache-2.0. Original retuned 68.36 gate checks at rank 1. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part1_0 : List Nat := [0,1,2,3]
private theorem paidpart1_0 : part1_0.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_1 : List Nat := [4,5,6,7]
private theorem paidpart1_1 : part1_1.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_2 : List Nat := [8,9,10,11]
private theorem paidpart1_2 : part1_2.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_3 : List Nat := [12,13,14,15]
private theorem paidpart1_3 : part1_3.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_4 : List Nat := [16,17,18,19]
private theorem paidpart1_4 : part1_4.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_5 : List Nat := [20,21,22,23]
private theorem paidpart1_5 : part1_5.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_6 : List Nat := [24,25,26,27]
private theorem paidpart1_6 : part1_6.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_7 : List Nat := [28,29,30,31]
private theorem paidpart1_7 : part1_7.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_8 : List Nat := [32,33,34,35]
private theorem paidpart1_8 : part1_8.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_9 : List Nat := [36,37,38,39]
private theorem paidpart1_9 : part1_9.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_10 : List Nat := [40,41,42,43]
private theorem paidpart1_10 : part1_10.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_11 : List Nat := [44,45,46,47]
private theorem paidpart1_11 : part1_11.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_12 : List Nat := [48,49,50,51]
private theorem paidpart1_12 : part1_12.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_13 : List Nat := [52,53,54,55]
private theorem paidpart1_13 : part1_13.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_14 : List Nat := [56,57,58,59]
private theorem paidpart1_14 : part1_14.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_15 : List Nat := [60,61,62,63]
private theorem paidpart1_15 : part1_15.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_16 : List Nat := [64,65,66,67]
private theorem paidpart1_16 : part1_16.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_17 : List Nat := [68,69,70,71]
private theorem paidpart1_17 : part1_17.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_18 : List Nat := [72,73,74,75]
private theorem paidpart1_18 : part1_18.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
private def part1_19 : List Nat := [76]
private theorem paidpart1_19 : part1_19.all (fun k => checkEnd 1 (k+1))=true := by decide +kernel
theorem rank1 : checkedRank 1 = true := by
  unfold checkedRank
  have parts : List.range (maxY 1+2-1) = part1_0 ++ part1_1 ++ part1_2 ++ part1_3 ++ part1_4 ++ part1_5 ++ part1_6 ++ part1_7 ++ part1_8 ++ part1_9 ++ part1_10 ++ part1_11 ++ part1_12 ++ part1_13 ++ part1_14 ++ part1_15 ++ part1_16 ++ part1_17 ++ part1_18 ++ part1_19 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart1_0,paidpart1_1,paidpart1_2,paidpart1_3,paidpart1_4,paidpart1_5,paidpart1_6,paidpart1_7,paidpart1_8,paidpart1_9,paidpart1_10,paidpart1_11,paidpart1_12,paidpart1_13,paidpart1_14,paidpart1_15,paidpart1_16,paidpart1_17,paidpart1_18,paidpart1_19, Bool.true_and]
#print axioms rank1
end Koala6836.FastEnd

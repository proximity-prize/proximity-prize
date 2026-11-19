/- Apache-2.0. Original retuned 68.36 gate checks at rank 2. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part2_0 : List Nat := [0,1,2,3]
private theorem paidpart2_0 : part2_0.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_1 : List Nat := [4,5,6,7]
private theorem paidpart2_1 : part2_1.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_2 : List Nat := [8,9,10,11]
private theorem paidpart2_2 : part2_2.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_3 : List Nat := [12,13,14,15]
private theorem paidpart2_3 : part2_3.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_4 : List Nat := [16,17,18,19]
private theorem paidpart2_4 : part2_4.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_5 : List Nat := [20,21,22,23]
private theorem paidpart2_5 : part2_5.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_6 : List Nat := [24,25,26,27]
private theorem paidpart2_6 : part2_6.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_7 : List Nat := [28,29,30,31]
private theorem paidpart2_7 : part2_7.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_8 : List Nat := [32,33,34,35]
private theorem paidpart2_8 : part2_8.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_9 : List Nat := [36,37,38,39]
private theorem paidpart2_9 : part2_9.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_10 : List Nat := [40,41,42,43]
private theorem paidpart2_10 : part2_10.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_11 : List Nat := [44,45,46,47]
private theorem paidpart2_11 : part2_11.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_12 : List Nat := [48,49,50,51]
private theorem paidpart2_12 : part2_12.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_13 : List Nat := [52,53,54,55]
private theorem paidpart2_13 : part2_13.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_14 : List Nat := [56,57,58,59]
private theorem paidpart2_14 : part2_14.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_15 : List Nat := [60,61,62,63]
private theorem paidpart2_15 : part2_15.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_16 : List Nat := [64,65,66,67]
private theorem paidpart2_16 : part2_16.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_17 : List Nat := [68,69,70,71]
private theorem paidpart2_17 : part2_17.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
private def part2_18 : List Nat := [72,73,74,75]
private theorem paidpart2_18 : part2_18.all (fun k => checkEnd 2 (k+2))=true := by decide +kernel
theorem rank2 : checkedRank 2 = true := by
  unfold checkedRank
  have parts : List.range (maxY 2+2-2) = part2_0 ++ part2_1 ++ part2_2 ++ part2_3 ++ part2_4 ++ part2_5 ++ part2_6 ++ part2_7 ++ part2_8 ++ part2_9 ++ part2_10 ++ part2_11 ++ part2_12 ++ part2_13 ++ part2_14 ++ part2_15 ++ part2_16 ++ part2_17 ++ part2_18 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart2_0,paidpart2_1,paidpart2_2,paidpart2_3,paidpart2_4,paidpart2_5,paidpart2_6,paidpart2_7,paidpart2_8,paidpart2_9,paidpart2_10,paidpart2_11,paidpart2_12,paidpart2_13,paidpart2_14,paidpart2_15,paidpart2_16,paidpart2_17,paidpart2_18, Bool.true_and]
#print axioms rank2
end Koala6836.FastEnd

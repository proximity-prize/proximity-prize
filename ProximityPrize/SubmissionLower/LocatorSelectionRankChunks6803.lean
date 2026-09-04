import ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic

/-! Short local-rank receipts for the 68.03 A, TCap, and B kernels. -/

namespace ProximityPrize.SubmissionLower.LocatorSelectionRankChunks6803

open scoped BigOperators
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

def rankRowA (r : ℕ) : ℕ :=
  let M := min r 130000
  let h := min (r + 1) (98 - r)
  rectangularCount (M + 1) (29 + 1) 0 130000 -
    rectangularCount (M + 1 - h) (29 + 1 - h) h 130000

def rankRowTCap (r : ℕ) : ℕ :=
  let M := min r 6679
  let h := min (r + 1) (181 - r)
  rectangularCount (M + 1) (56 + 1) 0 6679 -
    rectangularCount (M + 1 - h) (56 + 1 - h) h 6679

def rankRowB (r : ℕ) : ℕ :=
  let M := min r 14261
  let h := min (r + 1) (111 - r)
  rectangularCount (M + 1) (34 + 1) 0 14261 -
    rectangularCount (M + 1 - h) (34 + 1 - h) h 14261

theorem rankA_0 :
    (∑ i ∈ Finset.range 64, rankRowA i) = 8109847200 := by
  decide

theorem rankA_64 :
    (∑ i ∈ Finset.range 34, rankRowA (64 + i)) = 6374607285 := by
  decide

theorem rankTCap_0 :
    (∑ i ∈ Finset.range 64, rankRowTCap i) = 786171360 := by
  decide

theorem rankTCap_64 :
    (∑ i ∈ Finset.range 64, rankRowTCap (64 + i)) = 2321412168 := by
  decide

theorem rankTCap_128 :
    (∑ i ∈ Finset.range 53, rankRowTCap (128 + i)) = 1578358656 := by
  decide

theorem rankB_0 :
    (∑ i ∈ Finset.range 64, rankRowB i) = 1035507200 := by
  decide

theorem rankB_64 :
    (∑ i ∈ Finset.range 47, rankRowB (64 + i)) = 1312420690 := by
  decide

end ProximityPrize.SubmissionLower.LocatorSelectionRankChunks6803

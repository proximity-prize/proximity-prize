import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Fast040
import ProximityPrize.SubmissionLower.Fast044
set_option Elab.async false

section PackSource_K1_13_1_1BudgetC
set_option autoImplicit true
namespace K1_13_1_1

set_option maxRecDepth 30000
set_option Elab.async false
set_option maxHeartbeats 4000000

private theorem budgetCSumRangeSucc (n : ℕ) (f : ℕ → ℕ) :
    sumRange (n + 1) f = sumRange n f + f n := rfl

private theorem budgetCSumRangeAdd (n m : ℕ) (f : ℕ → ℕ) :
    sumRange (n + m) f = sumRange n f + sumRange m (fun r => f (r + n)) := by
  induction m with
  | zero => simp [sumRange]
  | succ m ih =>
    rw [Nat.add_succ, budgetCSumRangeSucc, ih, budgetCSumRangeSucc,
      Nat.add_assoc, Nat.add_comm n m]

private theorem budgetCAppendBlocks (s n m a b : ℕ)
    (ha : sumRange n (fastBlock s) = a)
    (hb : sumRange m (fun r => fastBlock s (r + n)) = b) :
    sumRange (n + m) (fastBlock s) = a + b :=
  (budgetCSumRangeAdd n m (fastBlock s)).trans (congrArg₂ Nat.add ha hb)

private theorem budgetCGradeFromBlocks (s a : ℕ)
    (h : sumRange 138 (fastBlock s) = a) : fastGrade s = a := h

-- Check up to 6 active offsets per declaration, plus one zero tail per grade.
-- The grade totals use only the checked chunk equalities and addition.

private theorem budgetCGrade36From0 :
    sumRange 6 (fastBlock 36) = 3110 := by decide +kernel
private theorem budgetCGrade36From6 :
    sumRange 6 (fun r => fastBlock 36 (r + 6)) = 8264 := by decide +kernel
private theorem budgetCGrade36From12 :
    sumRange 6 (fun r => fastBlock 36 (r + 12)) = 12673 := by decide +kernel
private theorem budgetCGrade36From18 :
    sumRange 6 (fun r => fastBlock 36 (r + 18)) = 15947 := by decide +kernel
private theorem budgetCGrade36From24 :
    sumRange 6 (fun r => fastBlock 36 (r + 24)) = 18148 := by decide +kernel
private theorem budgetCGrade36From30 :
    sumRange 6 (fun r => fastBlock 36 (r + 30)) = 19485 := by decide +kernel
private theorem budgetCGrade36From36 :
    sumRange 6 (fun r => fastBlock 36 (r + 36)) = 20174 := by decide +kernel
private theorem budgetCGrade36From42 :
    sumRange 6 (fun r => fastBlock 36 (r + 42)) = 20431 := by decide +kernel
private theorem budgetCGrade36From48 :
    sumRange 6 (fun r => fastBlock 36 (r + 48)) = 20472 := by decide +kernel
private theorem budgetCGrade36From54 :
    sumRange 6 (fun r => fastBlock 36 (r + 54)) = 17362 := by decide +kernel
private theorem budgetCGrade36From60 :
    sumRange 6 (fun r => fastBlock 36 (r + 60)) = 12208 := by decide +kernel
private theorem budgetCGrade36From66 :
    sumRange 6 (fun r => fastBlock 36 (r + 66)) = 7799 := by decide +kernel
private theorem budgetCGrade36From72 :
    sumRange 6 (fun r => fastBlock 36 (r + 72)) = 4525 := by decide +kernel
private theorem budgetCGrade36From78 :
    sumRange 6 (fun r => fastBlock 36 (r + 78)) = 2324 := by decide +kernel
private theorem budgetCGrade36From84 :
    sumRange 6 (fun r => fastBlock 36 (r + 84)) = 987 := by decide +kernel
private theorem budgetCGrade36From90 :
    sumRange 6 (fun r => fastBlock 36 (r + 90)) = 298 := by decide +kernel
private theorem budgetCGrade36From96 :
    sumRange 6 (fun r => fastBlock 36 (r + 96)) = 41 := by decide +kernel
private theorem budgetCGrade36From102 :
    sumRange 36 (fun r => fastBlock 36 (r + 102)) = 0 := by decide +kernel

private theorem grade36 : fastGrade 36 = 184248 := by
  have h6 := budgetCGrade36From0
  have h12 := budgetCAppendBlocks 36 6 6 3110 8264
    h6 budgetCGrade36From6
  have h18 := budgetCAppendBlocks 36 12 6 11374 12673
    h12 budgetCGrade36From12
  have h24 := budgetCAppendBlocks 36 18 6 24047 15947
    h18 budgetCGrade36From18
  have h30 := budgetCAppendBlocks 36 24 6 39994 18148
    h24 budgetCGrade36From24
  have h36 := budgetCAppendBlocks 36 30 6 58142 19485
    h30 budgetCGrade36From30
  have h42 := budgetCAppendBlocks 36 36 6 77627 20174
    h36 budgetCGrade36From36
  have h48 := budgetCAppendBlocks 36 42 6 97801 20431
    h42 budgetCGrade36From42
  have h54 := budgetCAppendBlocks 36 48 6 118232 20472
    h48 budgetCGrade36From48
  have h60 := budgetCAppendBlocks 36 54 6 138704 17362
    h54 budgetCGrade36From54
  have h66 := budgetCAppendBlocks 36 60 6 156066 12208
    h60 budgetCGrade36From60
  have h72 := budgetCAppendBlocks 36 66 6 168274 7799
    h66 budgetCGrade36From66
  have h78 := budgetCAppendBlocks 36 72 6 176073 4525
    h72 budgetCGrade36From72
  have h84 := budgetCAppendBlocks 36 78 6 180598 2324
    h78 budgetCGrade36From78
  have h90 := budgetCAppendBlocks 36 84 6 182922 987
    h84 budgetCGrade36From84
  have h96 := budgetCAppendBlocks 36 90 6 183909 298
    h90 budgetCGrade36From90
  have h102 := budgetCAppendBlocks 36 96 6 184207 41
    h96 budgetCGrade36From96
  have h138 := budgetCAppendBlocks 36 102 36 184248 0
    h102 budgetCGrade36From102
  exact budgetCGradeFromBlocks 36 184248 h138

private theorem budgetCGrade37From0 :
    sumRange 6 (fastBlock 37) = 3223 := by decide +kernel
private theorem budgetCGrade37From6 :
    sumRange 6 (fun r => fastBlock 37 (r + 6)) = 8494 := by decide +kernel
private theorem budgetCGrade37From12 :
    sumRange 6 (fun r => fastBlock 37 (r + 12)) = 12925 := by decide +kernel
private theorem budgetCGrade37From18 :
    sumRange 6 (fun r => fastBlock 37 (r + 18)) = 16199 := by decide +kernel
private theorem budgetCGrade37From24 :
    sumRange 6 (fun r => fastBlock 37 (r + 24)) = 18400 := by decide +kernel
private theorem budgetCGrade37From30 :
    sumRange 6 (fun r => fastBlock 37 (r + 30)) = 19737 := by decide +kernel
private theorem budgetCGrade37From36 :
    sumRange 6 (fun r => fastBlock 37 (r + 36)) = 20426 := by decide +kernel
private theorem budgetCGrade37From42 :
    sumRange 6 (fun r => fastBlock 37 (r + 42)) = 20683 := by decide +kernel
private theorem budgetCGrade37From48 :
    sumRange 6 (fun r => fastBlock 37 (r + 48)) = 20570 := by decide +kernel
private theorem budgetCGrade37From54 :
    sumRange 6 (fun r => fastBlock 37 (r + 54)) = 16590 := by decide +kernel
private theorem budgetCGrade37From60 :
    sumRange 6 (fun r => fastBlock 37 (r + 60)) = 11418 := by decide +kernel
private theorem budgetCGrade37From66 :
    sumRange 6 (fun r => fastBlock 37 (r + 66)) = 7172 := by decide +kernel
private theorem budgetCGrade37From72 :
    sumRange 6 (fun r => fastBlock 37 (r + 72)) = 4089 := by decide +kernel
private theorem budgetCGrade37From78 :
    sumRange 6 (fun r => fastBlock 37 (r + 78)) = 2047 := by decide +kernel
private theorem budgetCGrade37From84 :
    sumRange 6 (fun r => fastBlock 37 (r + 84)) = 833 := by decide +kernel
private theorem budgetCGrade37From90 :
    sumRange 6 (fun r => fastBlock 37 (r + 90)) = 231 := by decide +kernel
private theorem budgetCGrade37From96 :
    sumRange 5 (fun r => fastBlock 37 (r + 96)) = 25 := by decide +kernel
private theorem budgetCGrade37From101 :
    sumRange 37 (fun r => fastBlock 37 (r + 101)) = 0 := by decide +kernel

private theorem grade37 : fastGrade 37 = 183062 := by
  have h6 := budgetCGrade37From0
  have h12 := budgetCAppendBlocks 37 6 6 3223 8494
    h6 budgetCGrade37From6
  have h18 := budgetCAppendBlocks 37 12 6 11717 12925
    h12 budgetCGrade37From12
  have h24 := budgetCAppendBlocks 37 18 6 24642 16199
    h18 budgetCGrade37From18
  have h30 := budgetCAppendBlocks 37 24 6 40841 18400
    h24 budgetCGrade37From24
  have h36 := budgetCAppendBlocks 37 30 6 59241 19737
    h30 budgetCGrade37From30
  have h42 := budgetCAppendBlocks 37 36 6 78978 20426
    h36 budgetCGrade37From36
  have h48 := budgetCAppendBlocks 37 42 6 99404 20683
    h42 budgetCGrade37From42
  have h54 := budgetCAppendBlocks 37 48 6 120087 20570
    h48 budgetCGrade37From48
  have h60 := budgetCAppendBlocks 37 54 6 140657 16590
    h54 budgetCGrade37From54
  have h66 := budgetCAppendBlocks 37 60 6 157247 11418
    h60 budgetCGrade37From60
  have h72 := budgetCAppendBlocks 37 66 6 168665 7172
    h66 budgetCGrade37From66
  have h78 := budgetCAppendBlocks 37 72 6 175837 4089
    h72 budgetCGrade37From72
  have h84 := budgetCAppendBlocks 37 78 6 179926 2047
    h78 budgetCGrade37From78
  have h90 := budgetCAppendBlocks 37 84 6 181973 833
    h84 budgetCGrade37From84
  have h96 := budgetCAppendBlocks 37 90 6 182806 231
    h90 budgetCGrade37From90
  have h101 := budgetCAppendBlocks 37 96 5 183037 25
    h96 budgetCGrade37From96
  have h138 := budgetCAppendBlocks 37 101 37 183062 0
    h101 budgetCGrade37From101
  exact budgetCGradeFromBlocks 37 183062 h138

private theorem budgetCGrade38From0 :
    sumRange 6 (fastBlock 38) = 3327 := by decide +kernel
private theorem budgetCGrade38From6 :
    sumRange 6 (fun r => fastBlock 38 (r + 6)) = 8697 := by decide +kernel
private theorem budgetCGrade38From12 :
    sumRange 6 (fun r => fastBlock 38 (r + 12)) = 13141 := by decide +kernel
private theorem budgetCGrade38From18 :
    sumRange 6 (fun r => fastBlock 38 (r + 18)) = 16415 := by decide +kernel
private theorem budgetCGrade38From24 :
    sumRange 6 (fun r => fastBlock 38 (r + 24)) = 18616 := by decide +kernel
private theorem budgetCGrade38From30 :
    sumRange 6 (fun r => fastBlock 38 (r + 30)) = 19953 := by decide +kernel
private theorem budgetCGrade38From36 :
    sumRange 6 (fun r => fastBlock 38 (r + 36)) = 20642 := by decide +kernel
private theorem budgetCGrade38From42 :
    sumRange 6 (fun r => fastBlock 38 (r + 42)) = 20899 := by decide +kernel
private theorem budgetCGrade38From48 :
    sumRange 6 (fun r => fastBlock 38 (r + 48)) = 20461 := by decide +kernel
private theorem budgetCGrade38From54 :
    sumRange 6 (fun r => fastBlock 38 (r + 54)) = 15755 := by decide +kernel
private theorem budgetCGrade38From60 :
    sumRange 6 (fun r => fastBlock 38 (r + 60)) = 10636 := by decide +kernel
private theorem budgetCGrade38From66 :
    sumRange 6 (fun r => fastBlock 38 (r + 66)) = 6578 := by decide +kernel
private theorem budgetCGrade38From72 :
    sumRange 6 (fun r => fastBlock 38 (r + 72)) = 3682 := by decide +kernel
private theorem budgetCGrade38From78 :
    sumRange 6 (fun r => fastBlock 38 (r + 78)) = 1793 := by decide +kernel
private theorem budgetCGrade38From84 :
    sumRange 6 (fun r => fastBlock 38 (r + 84)) = 696 := by decide +kernel
private theorem budgetCGrade38From90 :
    sumRange 6 (fun r => fastBlock 38 (r + 90)) = 175 := by decide +kernel
private theorem budgetCGrade38From96 :
    sumRange 4 (fun r => fastBlock 38 (r + 96)) = 14 := by decide +kernel
private theorem budgetCGrade38From100 :
    sumRange 38 (fun r => fastBlock 38 (r + 100)) = 0 := by decide +kernel

private theorem grade38 : fastGrade 38 = 181480 := by
  have h6 := budgetCGrade38From0
  have h12 := budgetCAppendBlocks 38 6 6 3327 8697
    h6 budgetCGrade38From6
  have h18 := budgetCAppendBlocks 38 12 6 12024 13141
    h12 budgetCGrade38From12
  have h24 := budgetCAppendBlocks 38 18 6 25165 16415
    h18 budgetCGrade38From18
  have h30 := budgetCAppendBlocks 38 24 6 41580 18616
    h24 budgetCGrade38From24
  have h36 := budgetCAppendBlocks 38 30 6 60196 19953
    h30 budgetCGrade38From30
  have h42 := budgetCAppendBlocks 38 36 6 80149 20642
    h36 budgetCGrade38From36
  have h48 := budgetCAppendBlocks 38 42 6 100791 20899
    h42 budgetCGrade38From42
  have h54 := budgetCAppendBlocks 38 48 6 121690 20461
    h48 budgetCGrade38From48
  have h60 := budgetCAppendBlocks 38 54 6 142151 15755
    h54 budgetCGrade38From54
  have h66 := budgetCAppendBlocks 38 60 6 157906 10636
    h60 budgetCGrade38From60
  have h72 := budgetCAppendBlocks 38 66 6 168542 6578
    h66 budgetCGrade38From66
  have h78 := budgetCAppendBlocks 38 72 6 175120 3682
    h72 budgetCGrade38From72
  have h84 := budgetCAppendBlocks 38 78 6 178802 1793
    h78 budgetCGrade38From78
  have h90 := budgetCAppendBlocks 38 84 6 180595 696
    h84 budgetCGrade38From84
  have h96 := budgetCAppendBlocks 38 90 6 181291 175
    h90 budgetCGrade38From90
  have h100 := budgetCAppendBlocks 38 96 4 181466 14
    h96 budgetCGrade38From96
  have h138 := budgetCAppendBlocks 38 100 38 181480 0
    h100 budgetCGrade38From100
  exact budgetCGradeFromBlocks 38 181480 h138

private theorem budgetCGrade39From0 :
    sumRange 6 (fastBlock 39) = 3419 := by decide +kernel
private theorem budgetCGrade39From6 :
    sumRange 6 (fun r => fastBlock 39 (r + 6)) = 8870 := by decide +kernel
private theorem budgetCGrade39From12 :
    sumRange 6 (fun r => fastBlock 39 (r + 12)) = 13321 := by decide +kernel
private theorem budgetCGrade39From18 :
    sumRange 6 (fun r => fastBlock 39 (r + 18)) = 16595 := by decide +kernel
private theorem budgetCGrade39From24 :
    sumRange 6 (fun r => fastBlock 39 (r + 24)) = 18796 := by decide +kernel
private theorem budgetCGrade39From30 :
    sumRange 6 (fun r => fastBlock 39 (r + 30)) = 20133 := by decide +kernel
private theorem budgetCGrade39From36 :
    sumRange 6 (fun r => fastBlock 39 (r + 36)) = 20822 := by decide +kernel
private theorem budgetCGrade39From42 :
    sumRange 6 (fun r => fastBlock 39 (r + 42)) = 21079 := by decide +kernel
private theorem budgetCGrade39From48 :
    sumRange 6 (fun r => fastBlock 39 (r + 48)) = 20134 := by decide +kernel
private theorem budgetCGrade39From54 :
    sumRange 6 (fun r => fastBlock 39 (r + 54)) = 14881 := by decide +kernel
private theorem budgetCGrade39From60 :
    sumRange 6 (fun r => fastBlock 39 (r + 60)) = 9878 := by decide +kernel
private theorem budgetCGrade39From66 :
    sumRange 6 (fun r => fastBlock 39 (r + 66)) = 6017 := by decide +kernel
private theorem budgetCGrade39From72 :
    sumRange 6 (fun r => fastBlock 39 (r + 72)) = 3303 := by decide +kernel
private theorem budgetCGrade39From78 :
    sumRange 6 (fun r => fastBlock 39 (r + 78)) = 1561 := by decide +kernel
private theorem budgetCGrade39From84 :
    sumRange 6 (fun r => fastBlock 39 (r + 84)) = 575 := by decide +kernel
private theorem budgetCGrade39From90 :
    sumRange 6 (fun r => fastBlock 39 (r + 90)) = 129 := by decide +kernel
private theorem budgetCGrade39From96 :
    sumRange 3 (fun r => fastBlock 39 (r + 96)) = 7 := by decide +kernel
private theorem budgetCGrade39From99 :
    sumRange 39 (fun r => fastBlock 39 (r + 99)) = 0 := by decide +kernel

private theorem grade39 : fastGrade 39 = 179520 := by
  have h6 := budgetCGrade39From0
  have h12 := budgetCAppendBlocks 39 6 6 3419 8870
    h6 budgetCGrade39From6
  have h18 := budgetCAppendBlocks 39 12 6 12289 13321
    h12 budgetCGrade39From12
  have h24 := budgetCAppendBlocks 39 18 6 25610 16595
    h18 budgetCGrade39From18
  have h30 := budgetCAppendBlocks 39 24 6 42205 18796
    h24 budgetCGrade39From24
  have h36 := budgetCAppendBlocks 39 30 6 61001 20133
    h30 budgetCGrade39From30
  have h42 := budgetCAppendBlocks 39 36 6 81134 20822
    h36 budgetCGrade39From36
  have h48 := budgetCAppendBlocks 39 42 6 101956 21079
    h42 budgetCGrade39From42
  have h54 := budgetCAppendBlocks 39 48 6 123035 20134
    h48 budgetCGrade39From48
  have h60 := budgetCAppendBlocks 39 54 6 143169 14881
    h54 budgetCGrade39From54
  have h66 := budgetCAppendBlocks 39 60 6 158050 9878
    h60 budgetCGrade39From60
  have h72 := budgetCAppendBlocks 39 66 6 167928 6017
    h66 budgetCGrade39From66
  have h78 := budgetCAppendBlocks 39 72 6 173945 3303
    h72 budgetCGrade39From72
  have h84 := budgetCAppendBlocks 39 78 6 177248 1561
    h78 budgetCGrade39From78
  have h90 := budgetCAppendBlocks 39 84 6 178809 575
    h84 budgetCGrade39From84
  have h96 := budgetCAppendBlocks 39 90 6 179384 129
    h90 budgetCGrade39From90
  have h99 := budgetCAppendBlocks 39 96 3 179513 7
    h96 budgetCGrade39From96
  have h138 := budgetCAppendBlocks 39 99 39 179520 0
    h99 budgetCGrade39From99
  exact budgetCGradeFromBlocks 39 179520 h138

private theorem budgetCGrade40From0 :
    sumRange 6 (fastBlock 40) = 3502 := by decide +kernel
private theorem budgetCGrade40From6 :
    sumRange 6 (fun r => fastBlock 40 (r + 6)) = 9017 := by decide +kernel
private theorem budgetCGrade40From12 :
    sumRange 6 (fun r => fastBlock 40 (r + 12)) = 13471 := by decide +kernel
private theorem budgetCGrade40From18 :
    sumRange 6 (fun r => fastBlock 40 (r + 18)) = 16745 := by decide +kernel
private theorem budgetCGrade40From24 :
    sumRange 6 (fun r => fastBlock 40 (r + 24)) = 18946 := by decide +kernel
private theorem budgetCGrade40From30 :
    sumRange 6 (fun r => fastBlock 40 (r + 30)) = 20283 := by decide +kernel
private theorem budgetCGrade40From36 :
    sumRange 6 (fun r => fastBlock 40 (r + 36)) = 20972 := by decide +kernel
private theorem budgetCGrade40From42 :
    sumRange 6 (fun r => fastBlock 40 (r + 42)) = 21229 := by decide +kernel
private theorem budgetCGrade40From48 :
    sumRange 6 (fun r => fastBlock 40 (r + 48)) = 19588 := by decide +kernel
private theorem budgetCGrade40From54 :
    sumRange 6 (fun r => fastBlock 40 (r + 54)) = 13992 := by decide +kernel
private theorem budgetCGrade40From60 :
    sumRange 6 (fun r => fastBlock 40 (r + 60)) = 9152 := by decide +kernel
private theorem budgetCGrade40From66 :
    sumRange 6 (fun r => fastBlock 40 (r + 66)) = 5488 := by decide +kernel
private theorem budgetCGrade40From72 :
    sumRange 6 (fun r => fastBlock 40 (r + 72)) = 2951 := by decide +kernel
private theorem budgetCGrade40From78 :
    sumRange 6 (fun r => fastBlock 40 (r + 78)) = 1350 := by decide +kernel
private theorem budgetCGrade40From84 :
    sumRange 6 (fun r => fastBlock 40 (r + 84)) = 469 := by decide +kernel
private theorem budgetCGrade40From90 :
    sumRange 6 (fun r => fastBlock 40 (r + 90)) = 92 := by decide +kernel
private theorem budgetCGrade40From96 :
    sumRange 2 (fun r => fastBlock 40 (r + 96)) = 3 := by decide +kernel
private theorem budgetCGrade40From98 :
    sumRange 40 (fun r => fastBlock 40 (r + 98)) = 0 := by decide +kernel

private theorem grade40 : fastGrade 40 = 177250 := by
  have h6 := budgetCGrade40From0
  have h12 := budgetCAppendBlocks 40 6 6 3502 9017
    h6 budgetCGrade40From6
  have h18 := budgetCAppendBlocks 40 12 6 12519 13471
    h12 budgetCGrade40From12
  have h24 := budgetCAppendBlocks 40 18 6 25990 16745
    h18 budgetCGrade40From18
  have h30 := budgetCAppendBlocks 40 24 6 42735 18946
    h24 budgetCGrade40From24
  have h36 := budgetCAppendBlocks 40 30 6 61681 20283
    h30 budgetCGrade40From30
  have h42 := budgetCAppendBlocks 40 36 6 81964 20972
    h36 budgetCGrade40From36
  have h48 := budgetCAppendBlocks 40 42 6 102936 21229
    h42 budgetCGrade40From42
  have h54 := budgetCAppendBlocks 40 48 6 124165 19588
    h48 budgetCGrade40From48
  have h60 := budgetCAppendBlocks 40 54 6 143753 13992
    h54 budgetCGrade40From54
  have h66 := budgetCAppendBlocks 40 60 6 157745 9152
    h60 budgetCGrade40From60
  have h72 := budgetCAppendBlocks 40 66 6 166897 5488
    h66 budgetCGrade40From66
  have h78 := budgetCAppendBlocks 40 72 6 172385 2951
    h72 budgetCGrade40From72
  have h84 := budgetCAppendBlocks 40 78 6 175336 1350
    h78 budgetCGrade40From78
  have h90 := budgetCAppendBlocks 40 84 6 176686 469
    h84 budgetCGrade40From84
  have h96 := budgetCAppendBlocks 40 90 6 177155 92
    h90 budgetCGrade40From90
  have h98 := budgetCAppendBlocks 40 96 2 177247 3
    h96 budgetCGrade40From96
  have h138 := budgetCAppendBlocks 40 98 40 177250 0
    h98 budgetCGrade40From98
  exact budgetCGradeFromBlocks 40 177250 h138

private theorem budgetCGrade41From0 :
    sumRange 6 (fastBlock 41) = 3573 := by decide +kernel
private theorem budgetCGrade41From6 :
    sumRange 6 (fun r => fastBlock 41 (r + 6)) = 9136 := by decide +kernel
private theorem budgetCGrade41From12 :
    sumRange 6 (fun r => fastBlock 41 (r + 12)) = 13591 := by decide +kernel
private theorem budgetCGrade41From18 :
    sumRange 6 (fun r => fastBlock 41 (r + 18)) = 16865 := by decide +kernel
private theorem budgetCGrade41From24 :
    sumRange 6 (fun r => fastBlock 41 (r + 24)) = 19066 := by decide +kernel
private theorem budgetCGrade41From30 :
    sumRange 6 (fun r => fastBlock 41 (r + 30)) = 20403 := by decide +kernel
private theorem budgetCGrade41From36 :
    sumRange 6 (fun r => fastBlock 41 (r + 36)) = 21092 := by decide +kernel
private theorem budgetCGrade41From42 :
    sumRange 6 (fun r => fastBlock 41 (r + 42)) = 21349 := by decide +kernel
private theorem budgetCGrade41From48 :
    sumRange 6 (fun r => fastBlock 41 (r + 48)) = 18824 := by decide +kernel
private theorem budgetCGrade41From54 :
    sumRange 6 (fun r => fastBlock 41 (r + 54)) = 13111 := by decide +kernel
private theorem budgetCGrade41From60 :
    sumRange 6 (fun r => fastBlock 41 (r + 60)) = 8459 := by decide +kernel
private theorem budgetCGrade41From66 :
    sumRange 6 (fun r => fastBlock 41 (r + 66)) = 4991 := by decide +kernel
private theorem budgetCGrade41From72 :
    sumRange 6 (fun r => fastBlock 41 (r + 72)) = 2625 := by decide +kernel
private theorem budgetCGrade41From78 :
    sumRange 6 (fun r => fastBlock 41 (r + 78)) = 1159 := by decide +kernel
private theorem budgetCGrade41From84 :
    sumRange 6 (fun r => fastBlock 41 (r + 84)) = 377 := by decide +kernel
private theorem budgetCGrade41From90 :
    sumRange 6 (fun r => fastBlock 41 (r + 90)) = 63 := by decide +kernel
private theorem budgetCGrade41From96 :
    sumRange 1 (fun r => fastBlock 41 (r + 96)) = 1 := by decide +kernel
private theorem budgetCGrade41From97 :
    sumRange 41 (fun r => fastBlock 41 (r + 97)) = 0 := by decide +kernel

private theorem grade41 : fastGrade 41 = 174685 := by
  have h6 := budgetCGrade41From0
  have h12 := budgetCAppendBlocks 41 6 6 3573 9136
    h6 budgetCGrade41From6
  have h18 := budgetCAppendBlocks 41 12 6 12709 13591
    h12 budgetCGrade41From12
  have h24 := budgetCAppendBlocks 41 18 6 26300 16865
    h18 budgetCGrade41From18
  have h30 := budgetCAppendBlocks 41 24 6 43165 19066
    h24 budgetCGrade41From24
  have h36 := budgetCAppendBlocks 41 30 6 62231 20403
    h30 budgetCGrade41From30
  have h42 := budgetCAppendBlocks 41 36 6 82634 21092
    h36 budgetCGrade41From36
  have h48 := budgetCAppendBlocks 41 42 6 103726 21349
    h42 budgetCGrade41From42
  have h54 := budgetCAppendBlocks 41 48 6 125075 18824
    h48 budgetCGrade41From48
  have h60 := budgetCAppendBlocks 41 54 6 143899 13111
    h54 budgetCGrade41From54
  have h66 := budgetCAppendBlocks 41 60 6 157010 8459
    h60 budgetCGrade41From60
  have h72 := budgetCAppendBlocks 41 66 6 165469 4991
    h66 budgetCGrade41From66
  have h78 := budgetCAppendBlocks 41 72 6 170460 2625
    h72 budgetCGrade41From72
  have h84 := budgetCAppendBlocks 41 78 6 173085 1159
    h78 budgetCGrade41From78
  have h90 := budgetCAppendBlocks 41 84 6 174244 377
    h84 budgetCGrade41From84
  have h96 := budgetCAppendBlocks 41 90 6 174621 63
    h90 budgetCGrade41From90
  have h97 := budgetCAppendBlocks 41 96 1 174684 1
    h96 budgetCGrade41From96
  have h138 := budgetCAppendBlocks 41 97 41 174685 0
    h97 budgetCGrade41From97
  exact budgetCGradeFromBlocks 41 174685 h138

private theorem budgetCGrade42From0 :
    sumRange 6 (fastBlock 42) = 3635 := by decide +kernel
private theorem budgetCGrade42From6 :
    sumRange 6 (fun r => fastBlock 42 (r + 6)) = 9232 := by decide +kernel
private theorem budgetCGrade42From12 :
    sumRange 6 (fun r => fastBlock 42 (r + 12)) = 13687 := by decide +kernel
private theorem budgetCGrade42From18 :
    sumRange 6 (fun r => fastBlock 42 (r + 18)) = 16961 := by decide +kernel
private theorem budgetCGrade42From24 :
    sumRange 6 (fun r => fastBlock 42 (r + 24)) = 19162 := by decide +kernel
private theorem budgetCGrade42From30 :
    sumRange 6 (fun r => fastBlock 42 (r + 30)) = 20499 := by decide +kernel
private theorem budgetCGrade42From36 :
    sumRange 6 (fun r => fastBlock 42 (r + 36)) = 21188 := by decide +kernel
private theorem budgetCGrade42From42 :
    sumRange 6 (fun r => fastBlock 42 (r + 42)) = 21445 := by decide +kernel
private theorem budgetCGrade42From48 :
    sumRange 6 (fun r => fastBlock 42 (r + 48)) = 17851 := by decide +kernel
private theorem budgetCGrade42From54 :
    sumRange 6 (fun r => fastBlock 42 (r + 54)) = 12254 := by decide +kernel
private theorem budgetCGrade42From60 :
    sumRange 6 (fun r => fastBlock 42 (r + 60)) = 7799 := by decide +kernel
private theorem budgetCGrade42From66 :
    sumRange 6 (fun r => fastBlock 42 (r + 66)) = 4525 := by decide +kernel
private theorem budgetCGrade42From72 :
    sumRange 6 (fun r => fastBlock 42 (r + 72)) = 2324 := by decide +kernel
private theorem budgetCGrade42From78 :
    sumRange 6 (fun r => fastBlock 42 (r + 78)) = 987 := by decide +kernel
private theorem budgetCGrade42From84 :
    sumRange 6 (fun r => fastBlock 42 (r + 84)) = 298 := by decide +kernel
private theorem budgetCGrade42From90 :
    sumRange 6 (fun r => fastBlock 42 (r + 90)) = 41 := by decide +kernel
private theorem budgetCGrade42From96 :
    sumRange 42 (fun r => fastBlock 42 (r + 96)) = 0 := by decide +kernel

private theorem grade42 : fastGrade 42 = 171888 := by
  have h6 := budgetCGrade42From0
  have h12 := budgetCAppendBlocks 42 6 6 3635 9232
    h6 budgetCGrade42From6
  have h18 := budgetCAppendBlocks 42 12 6 12867 13687
    h12 budgetCGrade42From12
  have h24 := budgetCAppendBlocks 42 18 6 26554 16961
    h18 budgetCGrade42From18
  have h30 := budgetCAppendBlocks 42 24 6 43515 19162
    h24 budgetCGrade42From24
  have h36 := budgetCAppendBlocks 42 30 6 62677 20499
    h30 budgetCGrade42From30
  have h42 := budgetCAppendBlocks 42 36 6 83176 21188
    h36 budgetCGrade42From36
  have h48 := budgetCAppendBlocks 42 42 6 104364 21445
    h42 budgetCGrade42From42
  have h54 := budgetCAppendBlocks 42 48 6 125809 17851
    h48 budgetCGrade42From48
  have h60 := budgetCAppendBlocks 42 54 6 143660 12254
    h54 budgetCGrade42From54
  have h66 := budgetCAppendBlocks 42 60 6 155914 7799
    h60 budgetCGrade42From60
  have h72 := budgetCAppendBlocks 42 66 6 163713 4525
    h66 budgetCGrade42From66
  have h78 := budgetCAppendBlocks 42 72 6 168238 2324
    h72 budgetCGrade42From72
  have h84 := budgetCAppendBlocks 42 78 6 170562 987
    h78 budgetCGrade42From78
  have h90 := budgetCAppendBlocks 42 84 6 171549 298
    h84 budgetCGrade42From84
  have h96 := budgetCAppendBlocks 42 90 6 171847 41
    h90 budgetCGrade42From90
  have h138 := budgetCAppendBlocks 42 96 42 171888 0
    h96 budgetCGrade42From96
  exact budgetCGradeFromBlocks 42 171888 h138

private theorem budgetCGrade43From0 :
    sumRange 6 (fastBlock 43) = 3685 := by decide +kernel
private theorem budgetCGrade43From6 :
    sumRange 6 (fun r => fastBlock 43 (r + 6)) = 9304 := by decide +kernel
private theorem budgetCGrade43From12 :
    sumRange 6 (fun r => fastBlock 43 (r + 12)) = 13759 := by decide +kernel
private theorem budgetCGrade43From18 :
    sumRange 6 (fun r => fastBlock 43 (r + 18)) = 17033 := by decide +kernel
private theorem budgetCGrade43From24 :
    sumRange 6 (fun r => fastBlock 43 (r + 24)) = 19234 := by decide +kernel
private theorem budgetCGrade43From30 :
    sumRange 6 (fun r => fastBlock 43 (r + 30)) = 20571 := by decide +kernel
private theorem budgetCGrade43From36 :
    sumRange 6 (fun r => fastBlock 43 (r + 36)) = 21260 := by decide +kernel
private theorem budgetCGrade43From42 :
    sumRange 6 (fun r => fastBlock 43 (r + 42)) = 21337 := by decide +kernel
private theorem budgetCGrade43From48 :
    sumRange 6 (fun r => fastBlock 43 (r + 48)) = 16863 := by decide +kernel
private theorem budgetCGrade43From54 :
    sumRange 6 (fun r => fastBlock 43 (r + 54)) = 11429 := by decide +kernel
private theorem budgetCGrade43From60 :
    sumRange 6 (fun r => fastBlock 43 (r + 60)) = 7172 := by decide +kernel
private theorem budgetCGrade43From66 :
    sumRange 6 (fun r => fastBlock 43 (r + 66)) = 4089 := by decide +kernel
private theorem budgetCGrade43From72 :
    sumRange 6 (fun r => fastBlock 43 (r + 72)) = 2047 := by decide +kernel
private theorem budgetCGrade43From78 :
    sumRange 6 (fun r => fastBlock 43 (r + 78)) = 833 := by decide +kernel
private theorem budgetCGrade43From84 :
    sumRange 6 (fun r => fastBlock 43 (r + 84)) = 231 := by decide +kernel
private theorem budgetCGrade43From90 :
    sumRange 5 (fun r => fastBlock 43 (r + 90)) = 25 := by decide +kernel
private theorem budgetCGrade43From95 :
    sumRange 43 (fun r => fastBlock 43 (r + 95)) = 0 := by decide +kernel

private theorem grade43 : fastGrade 43 = 168872 := by
  have h6 := budgetCGrade43From0
  have h12 := budgetCAppendBlocks 43 6 6 3685 9304
    h6 budgetCGrade43From6
  have h18 := budgetCAppendBlocks 43 12 6 12989 13759
    h12 budgetCGrade43From12
  have h24 := budgetCAppendBlocks 43 18 6 26748 17033
    h18 budgetCGrade43From18
  have h30 := budgetCAppendBlocks 43 24 6 43781 19234
    h24 budgetCGrade43From24
  have h36 := budgetCAppendBlocks 43 30 6 63015 20571
    h30 budgetCGrade43From30
  have h42 := budgetCAppendBlocks 43 36 6 83586 21260
    h36 budgetCGrade43From36
  have h48 := budgetCAppendBlocks 43 42 6 104846 21337
    h42 budgetCGrade43From42
  have h54 := budgetCAppendBlocks 43 48 6 126183 16863
    h48 budgetCGrade43From48
  have h60 := budgetCAppendBlocks 43 54 6 143046 11429
    h54 budgetCGrade43From54
  have h66 := budgetCAppendBlocks 43 60 6 154475 7172
    h60 budgetCGrade43From60
  have h72 := budgetCAppendBlocks 43 66 6 161647 4089
    h66 budgetCGrade43From66
  have h78 := budgetCAppendBlocks 43 72 6 165736 2047
    h72 budgetCGrade43From72
  have h84 := budgetCAppendBlocks 43 78 6 167783 833
    h78 budgetCGrade43From78
  have h90 := budgetCAppendBlocks 43 84 6 168616 231
    h84 budgetCGrade43From84
  have h95 := budgetCAppendBlocks 43 90 5 168847 25
    h90 budgetCGrade43From90
  have h138 := budgetCAppendBlocks 43 95 43 168872 0
    h95 budgetCGrade43From95
  exact budgetCGradeFromBlocks 43 168872 h138

private theorem budgetCGrade44From0 :
    sumRange 6 (fastBlock 44) = 3726 := by decide +kernel
private theorem budgetCGrade44From6 :
    sumRange 6 (fun r => fastBlock 44 (r + 6)) = 9358 := by decide +kernel
private theorem budgetCGrade44From12 :
    sumRange 6 (fun r => fastBlock 44 (r + 12)) = 13813 := by decide +kernel
private theorem budgetCGrade44From18 :
    sumRange 6 (fun r => fastBlock 44 (r + 18)) = 17087 := by decide +kernel
private theorem budgetCGrade44From24 :
    sumRange 6 (fun r => fastBlock 44 (r + 24)) = 19288 := by decide +kernel
private theorem budgetCGrade44From30 :
    sumRange 6 (fun r => fastBlock 44 (r + 30)) = 20625 := by decide +kernel
private theorem budgetCGrade44From36 :
    sumRange 6 (fun r => fastBlock 44 (r + 36)) = 21314 := by decide +kernel
private theorem budgetCGrade44From42 :
    sumRange 6 (fun r => fastBlock 44 (r + 42)) = 21026 := by decide +kernel
private theorem budgetCGrade44From48 :
    sumRange 6 (fun r => fastBlock 44 (r + 48)) = 15883 := by decide +kernel
private theorem budgetCGrade44From54 :
    sumRange 6 (fun r => fastBlock 44 (r + 54)) = 10637 := by decide +kernel
private theorem budgetCGrade44From60 :
    sumRange 6 (fun r => fastBlock 44 (r + 60)) = 6578 := by decide +kernel
private theorem budgetCGrade44From66 :
    sumRange 6 (fun r => fastBlock 44 (r + 66)) = 3682 := by decide +kernel
private theorem budgetCGrade44From72 :
    sumRange 6 (fun r => fastBlock 44 (r + 72)) = 1793 := by decide +kernel
private theorem budgetCGrade44From78 :
    sumRange 6 (fun r => fastBlock 44 (r + 78)) = 696 := by decide +kernel
private theorem budgetCGrade44From84 :
    sumRange 6 (fun r => fastBlock 44 (r + 84)) = 175 := by decide +kernel
private theorem budgetCGrade44From90 :
    sumRange 4 (fun r => fastBlock 44 (r + 90)) = 14 := by decide +kernel
private theorem budgetCGrade44From94 :
    sumRange 44 (fun r => fastBlock 44 (r + 94)) = 0 := by decide +kernel

private theorem grade44 : fastGrade 44 = 165695 := by
  have h6 := budgetCGrade44From0
  have h12 := budgetCAppendBlocks 44 6 6 3726 9358
    h6 budgetCGrade44From6
  have h18 := budgetCAppendBlocks 44 12 6 13084 13813
    h12 budgetCGrade44From12
  have h24 := budgetCAppendBlocks 44 18 6 26897 17087
    h18 budgetCGrade44From18
  have h30 := budgetCAppendBlocks 44 24 6 43984 19288
    h24 budgetCGrade44From24
  have h36 := budgetCAppendBlocks 44 30 6 63272 20625
    h30 budgetCGrade44From30
  have h42 := budgetCAppendBlocks 44 36 6 83897 21314
    h36 budgetCGrade44From36
  have h48 := budgetCAppendBlocks 44 42 6 105211 21026
    h42 budgetCGrade44From42
  have h54 := budgetCAppendBlocks 44 48 6 126237 15883
    h48 budgetCGrade44From48
  have h60 := budgetCAppendBlocks 44 54 6 142120 10637
    h54 budgetCGrade44From54
  have h66 := budgetCAppendBlocks 44 60 6 152757 6578
    h60 budgetCGrade44From60
  have h72 := budgetCAppendBlocks 44 66 6 159335 3682
    h66 budgetCGrade44From66
  have h78 := budgetCAppendBlocks 44 72 6 163017 1793
    h72 budgetCGrade44From72
  have h84 := budgetCAppendBlocks 44 78 6 164810 696
    h78 budgetCGrade44From78
  have h90 := budgetCAppendBlocks 44 84 6 165506 175
    h84 budgetCGrade44From84
  have h94 := budgetCAppendBlocks 44 90 4 165681 14
    h90 budgetCGrade44From90
  have h138 := budgetCAppendBlocks 44 94 44 165695 0
    h94 budgetCGrade44From94
  exact budgetCGradeFromBlocks 44 165695 h138

private theorem budgetCGrade45From0 :
    sumRange 6 (fastBlock 45) = 3755 := by decide +kernel
private theorem budgetCGrade45From6 :
    sumRange 6 (fun r => fastBlock 45 (r + 6)) = 9394 := by decide +kernel
private theorem budgetCGrade45From12 :
    sumRange 6 (fun r => fastBlock 45 (r + 12)) = 13849 := by decide +kernel
private theorem budgetCGrade45From18 :
    sumRange 6 (fun r => fastBlock 45 (r + 18)) = 17123 := by decide +kernel
private theorem budgetCGrade45From24 :
    sumRange 6 (fun r => fastBlock 45 (r + 24)) = 19324 := by decide +kernel
private theorem budgetCGrade45From30 :
    sumRange 6 (fun r => fastBlock 45 (r + 30)) = 20661 := by decide +kernel
private theorem budgetCGrade45From36 :
    sumRange 6 (fun r => fastBlock 45 (r + 36)) = 21350 := by decide +kernel
private theorem budgetCGrade45From42 :
    sumRange 6 (fun r => fastBlock 45 (r + 42)) = 20514 := by decide +kernel
private theorem budgetCGrade45From48 :
    sumRange 6 (fun r => fastBlock 45 (r + 48)) = 14927 := by decide +kernel
private theorem budgetCGrade45From54 :
    sumRange 6 (fun r => fastBlock 45 (r + 54)) = 9878 := by decide +kernel
private theorem budgetCGrade45From60 :
    sumRange 6 (fun r => fastBlock 45 (r + 60)) = 6017 := by decide +kernel
private theorem budgetCGrade45From66 :
    sumRange 6 (fun r => fastBlock 45 (r + 66)) = 3303 := by decide +kernel
private theorem budgetCGrade45From72 :
    sumRange 6 (fun r => fastBlock 45 (r + 72)) = 1561 := by decide +kernel
private theorem budgetCGrade45From78 :
    sumRange 6 (fun r => fastBlock 45 (r + 78)) = 575 := by decide +kernel
private theorem budgetCGrade45From84 :
    sumRange 6 (fun r => fastBlock 45 (r + 84)) = 129 := by decide +kernel
private theorem budgetCGrade45From90 :
    sumRange 3 (fun r => fastBlock 45 (r + 90)) = 7 := by decide +kernel
private theorem budgetCGrade45From93 :
    sumRange 45 (fun r => fastBlock 45 (r + 93)) = 0 := by decide +kernel

private theorem grade45 : fastGrade 45 = 162367 := by
  have h6 := budgetCGrade45From0
  have h12 := budgetCAppendBlocks 45 6 6 3755 9394
    h6 budgetCGrade45From6
  have h18 := budgetCAppendBlocks 45 12 6 13149 13849
    h12 budgetCGrade45From12
  have h24 := budgetCAppendBlocks 45 18 6 26998 17123
    h18 budgetCGrade45From18
  have h30 := budgetCAppendBlocks 45 24 6 44121 19324
    h24 budgetCGrade45From24
  have h36 := budgetCAppendBlocks 45 30 6 63445 20661
    h30 budgetCGrade45From30
  have h42 := budgetCAppendBlocks 45 36 6 84106 21350
    h36 budgetCGrade45From36
  have h48 := budgetCAppendBlocks 45 42 6 105456 20514
    h42 budgetCGrade45From42
  have h54 := budgetCAppendBlocks 45 48 6 125970 14927
    h48 budgetCGrade45From48
  have h60 := budgetCAppendBlocks 45 54 6 140897 9878
    h54 budgetCGrade45From54
  have h66 := budgetCAppendBlocks 45 60 6 150775 6017
    h60 budgetCGrade45From60
  have h72 := budgetCAppendBlocks 45 66 6 156792 3303
    h66 budgetCGrade45From66
  have h78 := budgetCAppendBlocks 45 72 6 160095 1561
    h72 budgetCGrade45From72
  have h84 := budgetCAppendBlocks 45 78 6 161656 575
    h78 budgetCGrade45From78
  have h90 := budgetCAppendBlocks 45 84 6 162231 129
    h84 budgetCGrade45From84
  have h93 := budgetCAppendBlocks 45 90 3 162360 7
    h90 budgetCGrade45From90
  have h138 := budgetCAppendBlocks 45 93 45 162367 0
    h93 budgetCGrade45From93
  exact budgetCGradeFromBlocks 45 162367 h138

private theorem budgetCGrade46From0 :
    sumRange 6 (fastBlock 46) = 3776 := by decide +kernel
private theorem budgetCGrade46From6 :
    sumRange 6 (fun r => fastBlock 46 (r + 6)) = 9418 := by decide +kernel
private theorem budgetCGrade46From12 :
    sumRange 6 (fun r => fastBlock 46 (r + 12)) = 13873 := by decide +kernel
private theorem budgetCGrade46From18 :
    sumRange 6 (fun r => fastBlock 46 (r + 18)) = 17147 := by decide +kernel
private theorem budgetCGrade46From24 :
    sumRange 6 (fun r => fastBlock 46 (r + 24)) = 19348 := by decide +kernel
private theorem budgetCGrade46From30 :
    sumRange 6 (fun r => fastBlock 46 (r + 30)) = 20685 := by decide +kernel
private theorem budgetCGrade46From36 :
    sumRange 6 (fun r => fastBlock 46 (r + 36)) = 21374 := by decide +kernel
private theorem budgetCGrade46From42 :
    sumRange 6 (fun r => fastBlock 46 (r + 42)) = 19813 := by decide +kernel
private theorem budgetCGrade46From48 :
    sumRange 6 (fun r => fastBlock 46 (r + 48)) = 14003 := by decide +kernel
private theorem budgetCGrade46From54 :
    sumRange 6 (fun r => fastBlock 46 (r + 54)) = 9152 := by decide +kernel
private theorem budgetCGrade46From60 :
    sumRange 6 (fun r => fastBlock 46 (r + 60)) = 5488 := by decide +kernel
private theorem budgetCGrade46From66 :
    sumRange 6 (fun r => fastBlock 46 (r + 66)) = 2951 := by decide +kernel
private theorem budgetCGrade46From72 :
    sumRange 6 (fun r => fastBlock 46 (r + 72)) = 1350 := by decide +kernel
private theorem budgetCGrade46From78 :
    sumRange 6 (fun r => fastBlock 46 (r + 78)) = 469 := by decide +kernel
private theorem budgetCGrade46From84 :
    sumRange 6 (fun r => fastBlock 46 (r + 84)) = 92 := by decide +kernel
private theorem budgetCGrade46From90 :
    sumRange 2 (fun r => fastBlock 46 (r + 90)) = 3 := by decide +kernel
private theorem budgetCGrade46From92 :
    sumRange 46 (fun r => fastBlock 46 (r + 92)) = 0 := by decide +kernel

private theorem grade46 : fastGrade 46 = 158942 := by
  have h6 := budgetCGrade46From0
  have h12 := budgetCAppendBlocks 46 6 6 3776 9418
    h6 budgetCGrade46From6
  have h18 := budgetCAppendBlocks 46 12 6 13194 13873
    h12 budgetCGrade46From12
  have h24 := budgetCAppendBlocks 46 18 6 27067 17147
    h18 budgetCGrade46From18
  have h30 := budgetCAppendBlocks 46 24 6 44214 19348
    h24 budgetCGrade46From24
  have h36 := budgetCAppendBlocks 46 30 6 63562 20685
    h30 budgetCGrade46From30
  have h42 := budgetCAppendBlocks 46 36 6 84247 21374
    h36 budgetCGrade46From36
  have h48 := budgetCAppendBlocks 46 42 6 105621 19813
    h42 budgetCGrade46From42
  have h54 := budgetCAppendBlocks 46 48 6 125434 14003
    h48 budgetCGrade46From48
  have h60 := budgetCAppendBlocks 46 54 6 139437 9152
    h54 budgetCGrade46From54
  have h66 := budgetCAppendBlocks 46 60 6 148589 5488
    h60 budgetCGrade46From60
  have h72 := budgetCAppendBlocks 46 66 6 154077 2951
    h66 budgetCGrade46From66
  have h78 := budgetCAppendBlocks 46 72 6 157028 1350
    h72 budgetCGrade46From72
  have h84 := budgetCAppendBlocks 46 78 6 158378 469
    h78 budgetCGrade46From78
  have h90 := budgetCAppendBlocks 46 84 6 158847 92
    h84 budgetCGrade46From84
  have h92 := budgetCAppendBlocks 46 90 2 158939 3
    h90 budgetCGrade46From90
  have h138 := budgetCAppendBlocks 46 92 46 158942 0
    h92 budgetCGrade46From92
  exact budgetCGradeFromBlocks 46 158942 h138

private theorem budgetCGrade47From0 :
    sumRange 6 (fastBlock 47) = 3787 := by decide +kernel
private theorem budgetCGrade47From6 :
    sumRange 6 (fun r => fastBlock 47 (r + 6)) = 9430 := by decide +kernel
private theorem budgetCGrade47From12 :
    sumRange 6 (fun r => fastBlock 47 (r + 12)) = 13885 := by decide +kernel
private theorem budgetCGrade47From18 :
    sumRange 6 (fun r => fastBlock 47 (r + 18)) = 17159 := by decide +kernel
private theorem budgetCGrade47From24 :
    sumRange 6 (fun r => fastBlock 47 (r + 24)) = 19360 := by decide +kernel
private theorem budgetCGrade47From30 :
    sumRange 6 (fun r => fastBlock 47 (r + 30)) = 20697 := by decide +kernel
private theorem budgetCGrade47From36 :
    sumRange 6 (fun r => fastBlock 47 (r + 36)) = 21386 := by decide +kernel
private theorem budgetCGrade47From42 :
    sumRange 6 (fun r => fastBlock 47 (r + 42)) = 18936 := by decide +kernel
private theorem budgetCGrade47From48 :
    sumRange 6 (fun r => fastBlock 47 (r + 48)) = 13112 := by decide +kernel
private theorem budgetCGrade47From54 :
    sumRange 6 (fun r => fastBlock 47 (r + 54)) = 8459 := by decide +kernel
private theorem budgetCGrade47From60 :
    sumRange 6 (fun r => fastBlock 47 (r + 60)) = 4991 := by decide +kernel
private theorem budgetCGrade47From66 :
    sumRange 6 (fun r => fastBlock 47 (r + 66)) = 2625 := by decide +kernel
private theorem budgetCGrade47From72 :
    sumRange 6 (fun r => fastBlock 47 (r + 72)) = 1159 := by decide +kernel
private theorem budgetCGrade47From78 :
    sumRange 6 (fun r => fastBlock 47 (r + 78)) = 377 := by decide +kernel
private theorem budgetCGrade47From84 :
    sumRange 6 (fun r => fastBlock 47 (r + 84)) = 63 := by decide +kernel
private theorem budgetCGrade47From90 :
    sumRange 1 (fun r => fastBlock 47 (r + 90)) = 1 := by decide +kernel
private theorem budgetCGrade47From91 :
    sumRange 47 (fun r => fastBlock 47 (r + 91)) = 0 := by decide +kernel

private theorem grade47 : fastGrade 47 = 155427 := by
  have h6 := budgetCGrade47From0
  have h12 := budgetCAppendBlocks 47 6 6 3787 9430
    h6 budgetCGrade47From6
  have h18 := budgetCAppendBlocks 47 12 6 13217 13885
    h12 budgetCGrade47From12
  have h24 := budgetCAppendBlocks 47 18 6 27102 17159
    h18 budgetCGrade47From18
  have h30 := budgetCAppendBlocks 47 24 6 44261 19360
    h24 budgetCGrade47From24
  have h36 := budgetCAppendBlocks 47 30 6 63621 20697
    h30 budgetCGrade47From30
  have h42 := budgetCAppendBlocks 47 36 6 84318 21386
    h36 budgetCGrade47From36
  have h48 := budgetCAppendBlocks 47 42 6 105704 18936
    h42 budgetCGrade47From42
  have h54 := budgetCAppendBlocks 47 48 6 124640 13112
    h48 budgetCGrade47From48
  have h60 := budgetCAppendBlocks 47 54 6 137752 8459
    h54 budgetCGrade47From54
  have h66 := budgetCAppendBlocks 47 60 6 146211 4991
    h60 budgetCGrade47From60
  have h72 := budgetCAppendBlocks 47 66 6 151202 2625
    h66 budgetCGrade47From66
  have h78 := budgetCAppendBlocks 47 72 6 153827 1159
    h72 budgetCGrade47From72
  have h84 := budgetCAppendBlocks 47 78 6 154986 377
    h78 budgetCGrade47From78
  have h90 := budgetCAppendBlocks 47 84 6 155363 63
    h84 budgetCGrade47From84
  have h91 := budgetCAppendBlocks 47 90 1 155426 1
    h90 budgetCGrade47From90
  have h138 := budgetCAppendBlocks 47 91 47 155427 0
    h91 budgetCGrade47From91
  exact budgetCGradeFromBlocks 47 155427 h138

private theorem budgetCGrade48From0 :
    sumRange 6 (fastBlock 48) = 3793 := by decide +kernel
private theorem budgetCGrade48From6 :
    sumRange 6 (fun r => fastBlock 48 (r + 6)) = 9436 := by decide +kernel
private theorem budgetCGrade48From12 :
    sumRange 6 (fun r => fastBlock 48 (r + 12)) = 13891 := by decide +kernel
private theorem budgetCGrade48From18 :
    sumRange 6 (fun r => fastBlock 48 (r + 18)) = 17165 := by decide +kernel
private theorem budgetCGrade48From24 :
    sumRange 6 (fun r => fastBlock 48 (r + 24)) = 19366 := by decide +kernel
private theorem budgetCGrade48From30 :
    sumRange 6 (fun r => fastBlock 48 (r + 30)) = 20703 := by decide +kernel
private theorem budgetCGrade48From36 :
    sumRange 6 (fun r => fastBlock 48 (r + 36)) = 21392 := by decide +kernel
private theorem budgetCGrade48From42 :
    sumRange 6 (fun r => fastBlock 48 (r + 42)) = 17897 := by decide +kernel
private theorem budgetCGrade48From48 :
    sumRange 6 (fun r => fastBlock 48 (r + 48)) = 12254 := by decide +kernel
private theorem budgetCGrade48From54 :
    sumRange 6 (fun r => fastBlock 48 (r + 54)) = 7799 := by decide +kernel
private theorem budgetCGrade48From60 :
    sumRange 6 (fun r => fastBlock 48 (r + 60)) = 4525 := by decide +kernel
private theorem budgetCGrade48From66 :
    sumRange 6 (fun r => fastBlock 48 (r + 66)) = 2324 := by decide +kernel
private theorem budgetCGrade48From72 :
    sumRange 6 (fun r => fastBlock 48 (r + 72)) = 987 := by decide +kernel
private theorem budgetCGrade48From78 :
    sumRange 6 (fun r => fastBlock 48 (r + 78)) = 298 := by decide +kernel
private theorem budgetCGrade48From84 :
    sumRange 6 (fun r => fastBlock 48 (r + 84)) = 41 := by decide +kernel
private theorem budgetCGrade48From90 :
    sumRange 48 (fun r => fastBlock 48 (r + 90)) = 0 := by decide +kernel

private theorem grade48 : fastGrade 48 = 151871 := by
  have h6 := budgetCGrade48From0
  have h12 := budgetCAppendBlocks 48 6 6 3793 9436
    h6 budgetCGrade48From6
  have h18 := budgetCAppendBlocks 48 12 6 13229 13891
    h12 budgetCGrade48From12
  have h24 := budgetCAppendBlocks 48 18 6 27120 17165
    h18 budgetCGrade48From18
  have h30 := budgetCAppendBlocks 48 24 6 44285 19366
    h24 budgetCGrade48From24
  have h36 := budgetCAppendBlocks 48 30 6 63651 20703
    h30 budgetCGrade48From30
  have h42 := budgetCAppendBlocks 48 36 6 84354 21392
    h36 budgetCGrade48From36
  have h48 := budgetCAppendBlocks 48 42 6 105746 17897
    h42 budgetCGrade48From42
  have h54 := budgetCAppendBlocks 48 48 6 123643 12254
    h48 budgetCGrade48From48
  have h60 := budgetCAppendBlocks 48 54 6 135897 7799
    h54 budgetCGrade48From54
  have h66 := budgetCAppendBlocks 48 60 6 143696 4525
    h60 budgetCGrade48From60
  have h72 := budgetCAppendBlocks 48 66 6 148221 2324
    h66 budgetCGrade48From66
  have h78 := budgetCAppendBlocks 48 72 6 150545 987
    h72 budgetCGrade48From72
  have h84 := budgetCAppendBlocks 48 78 6 151532 298
    h78 budgetCGrade48From78
  have h90 := budgetCAppendBlocks 48 84 6 151830 41
    h84 budgetCGrade48From84
  have h138 := budgetCAppendBlocks 48 90 48 151871 0
    h90 budgetCGrade48From90
  exact budgetCGradeFromBlocks 48 151871 h138

private theorem sumStep (f : ℕ → ℕ) (n a b : ℕ)
    (ha : sumRange n f = a) (hb : f n = b) :
    sumRange (n + 1) f = a + b :=
  (show sumRange (n + 1) f = sumRange n f + f n from rfl).trans (congrArg₂ Nat.add ha hb)

private def gradeFrom (i : ℕ) : ℕ := fastGrade (i + 36)

private theorem prefix36 : sumRange 1 gradeFrom = 184248 :=
  sumStep gradeFrom 0 0 184248 rfl grade36
private theorem prefix37 : sumRange 2 gradeFrom = 367310 :=
  sumStep gradeFrom 1 184248 183062 prefix36 grade37
private theorem prefix38 : sumRange 3 gradeFrom = 548790 :=
  sumStep gradeFrom 2 367310 181480 prefix37 grade38
private theorem prefix39 : sumRange 4 gradeFrom = 728310 :=
  sumStep gradeFrom 3 548790 179520 prefix38 grade39
private theorem prefix40 : sumRange 5 gradeFrom = 905560 :=
  sumStep gradeFrom 4 728310 177250 prefix39 grade40
private theorem prefix41 : sumRange 6 gradeFrom = 1080245 :=
  sumStep gradeFrom 5 905560 174685 prefix40 grade41
private theorem prefix42 : sumRange 7 gradeFrom = 1252133 :=
  sumStep gradeFrom 6 1080245 171888 prefix41 grade42
private theorem prefix43 : sumRange 8 gradeFrom = 1421005 :=
  sumStep gradeFrom 7 1252133 168872 prefix42 grade43
private theorem prefix44 : sumRange 9 gradeFrom = 1586700 :=
  sumStep gradeFrom 8 1421005 165695 prefix43 grade44
private theorem prefix45 : sumRange 10 gradeFrom = 1749067 :=
  sumStep gradeFrom 9 1586700 162367 prefix44 grade45
private theorem prefix46 : sumRange 11 gradeFrom = 1908009 :=
  sumStep gradeFrom 10 1749067 158942 prefix45 grade46
private theorem prefix47 : sumRange 12 gradeFrom = 2063436 :=
  sumStep gradeFrom 11 1908009 155427 prefix46 grade47
theorem budgetC : sumRange 13 (fun i => fastGrade (i + 36)) = 2215307 :=
  sumStep gradeFrom 12 2063436 151871 prefix47 grade48

end K1_13_1_1
end PackSource_K1_13_1_1BudgetC

section PackSource_K1_14_6Defs
set_option autoImplicit true
namespace K1_14_6

noncomputable section

open K1 K1_14 Polynomial
open scoped BigOperators

def taylorPower (d : ℕ) : ℕ := 2 * d - 1

def ordinateBound (d e : ℕ) : ℕ := 1 + taylorPower d * (e - 1)

def parameterBound (d b : ℕ) : ℕ := taylorPower d * b

def mixedDegree (d e b : ℕ) : ℕ :=
  e * (parameterBound d b)^2 + 2 * b * ordinateBound d e * parameterBound d b

abbrev Biform := MvPolynomial (Option (Fin 2)) FX

def rootPoint (z : K) (S : K[X]) : Option (Fin 2) → FX
  | none => atX S
  | some i => (![seedEmbedding z, (seedEmbedding z)^p] : Fin 2 → FX) i

/-- The common Taylor denominator and the numerator of each value of the
reconstructed polynomial. The variable `none` is the ordinate Y. -/
structure TaylorChart (d e b : ℕ) where
  denominator : Biform
  numerator : K → Biform
  denominator_bound : denominator ∈
    MvPolynomial.restrictBidegree (Fin 2) FX (ordinateBound d e) (parameterBound d b)
  numerator_bound : ∀ x, numerator x ∈
    MvPolynomial.restrictBidegree (Fin 2) FX (ordinateBound d e) (parameterBound d b)

def TaylorChart.Recovers {d e b} (C : TaylorChart d e b) (z : K) (S : K[X]) : Prop :=
  let ev := MvPolynomial.eval (rootPoint z S)
  ev C.denominator ≠ 0 ∧
    ∀ x : K, ev (C.numerator x) = ev C.denominator * seedEmbedding (S.eval x)

abbrev ClosedField := AlgebraicClosure FX

abbrev ChartVariables (d e b : ℕ) :=
  ↥(MvPolynomial.bidegreeExponents (Fin 2) (ordinateBound d e) (parameterBound d b))

abbrev LinearRing (d e b : ℕ) := MvPolynomial (ChartVariables d e b) ClosedField

/-- Regular marked source points in the bidegree monomial embedding.
Value sections are linear there after clearing the common denominator. -/
structure LinearCover (T : Finset K) (s : K → K[X]) (d e b : ℕ) where
  point : K → ChartVariables d e b → ClosedField
  injective : Set.InjOn point (T : Set K)
  cut : K → K → LinearRing d e b
  cut_degree : ∀ x a, (cut x a).totalDegree ≤ 1
  cut_eval : ∀ γ ∈ T, ∀ x a, MvPolynomial.aeval (point γ) (cut x a) = 0 ↔ (s γ).eval x = a
  components : Finset (Ideal (LinearRing d e b))
  is_prime : ∀ P ∈ components, P.IsPrime
  dimension : ∀ P ∈ components, (MvPolynomial.affineHilbertPolynomial P).natDegree = 2
  covers : ∀ γ ∈ T, ∃ P ∈ components, point γ ∈ MvPolynomial.zeroLocus ClosedField P
  component_count : components.card ≤ e
  degree_sum : ∑ P ∈ components, MvPolynomial.affineDegree P ≤ (mixedDegree d e b : ℚ)

/-- Component slices inherit the degree, injectivity and agreements of
distinct selected polynomials against the same word. -/
structure FixedWord (w : I → K) (T : Finset K) (s : K → K[X]) (d : ℕ) : Prop where
  distinct : Set.InjOn s (T : Set K)
  degree : ∀ γ ∈ T, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ T, ∃ B : Finset I, 180265 ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i

theorem FixedWord.mono {w T s d} (h : FixedWord w T s d) {U : Finset K} (hU : U ⊆ T) :
    FixedWord w U s d :=
  ⟨h.distinct.mono hU, fun γ hγ => h.degree γ (hU hγ), fun γ hγ => h.hits γ (hU hγ)⟩

end
end K1_14_6
end PackSource_K1_14_6Defs

section PackSource_K1_14_6Incidence
set_option autoImplicit true
namespace K1_14_6

noncomputable section

open Polynomial Finset K1 ProximityPrize.Benchmark
open scoped BigOperators

/-- First and second moments of the node occupancies of equally sized supports. -/
private theorem occupancy {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (marks : Finset α) (nodes : Finset ι) (B : α → Finset ι) (x t cap : ℕ)
    (hB : ∀ a ∈ marks, B a ⊆ nodes ∧ (B a).card = x)
    (hpair : ∀ a ∈ marks, ∀ b ∈ marks, a ≠ b → (B a ∩ B b).card ≤ t)
    (hocc : ∀ i ∈ nodes, (marks.filter fun a => i ∈ B a).card ≤ cap) :
    (marks.card * x)^2 ≤ nodes.card * (marks.card * (x + (marks.card - 1)*t)) ∧
      marks.card * x ≤ nodes.card * cap := by
  classical
  let occ (i : ι) := (marks.filter fun a => i ∈ B a).card
  have section_eq (V : Finset ι) (hV : V ⊆ nodes) :
      (nodes.filter fun i => i ∈ V) = V := by
    ext i
    exact mem_filter.trans ⟨And.right, fun hi => ⟨hV hi, hi⟩⟩
  have first : ∑ i ∈ nodes, occ i = marks.card * x := by
    calc
      _ = ∑ a ∈ marks, (B a).card := by
        simp only [occ, card_filter]
        rw [sum_comm]
        refine sum_congr rfl fun a ha => ?_
        rw [sum_boole, Nat.cast_id, section_eq _ (hB a ha).1]
      _ = _ := by rw [sum_congr rfl (fun a ha => (hB a ha).2), sum_const, smul_eq_mul]
  have second : ∑ i ∈ nodes, occ i ^ 2 =
      ∑ a ∈ marks, ∑ b ∈ marks, (B a ∩ B b).card := by
    simp only [occ, sq, card_filter]
    simp_rw [sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun a ha => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    have identity (i : ι) :
        (if i ∈ B a then 1 else 0 : ℕ) * (if i ∈ B b then 1 else 0) =
          if i ∈ B a ∩ B b then 1 else 0 := by
      by_cases h₁ : i ∈ B a <;> by_cases h₂ : i ∈ B b <;> simp [h₁, h₂]
    simp_rw [identity]
    rw [sum_boole, Nat.cast_id, section_eq _ (inter_subset_left.trans (hB a ha).1)]
  have row (a : α) (ha : a ∈ marks) :
      ∑ b ∈ marks, (B a ∩ B b).card ≤ x + (marks.card - 1) * t := by
    rw [← add_sum_erase marks _ ha, inter_self, (hB a ha).2]
    refine Nat.add_le_add_left ?_ _
    calc
      _ ≤ ∑ b ∈ marks.erase a, t := sum_le_sum fun b hb =>
        hpair a ha b (mem_of_mem_erase hb) (ne_of_mem_erase hb).symm
      _ = _ := by rw [sum_const, card_erase_of_mem ha, smul_eq_mul]
  have second_le : ∑ i ∈ nodes, occ i ^ 2 ≤ marks.card * (x + (marks.card - 1) * t) := by
    rw [second]
    exact (sum_le_sum row).trans_eq (by rw [sum_const, smul_eq_mul])
  have cs := sq_sum_le_card_mul_sum_sq (s := nodes) (f := occ)
  rw [first] at cs
  refine ⟨cs.trans (Nat.mul_le_mul_left _ second_le), ?_⟩
  rw [← first, ← smul_eq_mul, ← sum_const]
  exact sum_le_sum hocc

private theorem incidence_arithmetic (m x gap cap : ℕ)
    (hm : 0 < m) (hg : 0 < gap) (hx : gap ≤ x)
    (hsecond : (m*x)^2 ≤ (x+81879) * (m * (x + (m-1)*(x-gap))))
    (hfirst : m*x ≤ (x+81879)*cap) :
    gap*m ≤ 81879*cap + gap := by
  have hcancel : m*x^2 ≤ (x+81879) * (x + (m-1)*(x-gap)) := by
    apply Nat.le_of_mul_le_mul_left _ hm
    calc
      _ = (m*x)^2 := by ring
      _ ≤ _ := hsecond
      _ = _ := by ring
  have hM : ((m - 1 : ℕ) : ℤ) = (m : ℤ)-1 := Int.ofNat_sub (by omega)
  have hX : ((x - gap : ℕ) : ℤ) = (x : ℤ)-gap := Int.ofNat_sub hx
  have hcancelZ := Int.ofNat_le.mpr hcancel
  push_cast [hM, hX] at hcancelZ
  have hfirstZ := Int.ofNat_le.mpr hfirst
  push_cast at hfirstZ
  have secondZ : ((m : ℤ)*81879 - ((m : ℤ)-1)*gap)*x ≥
      ((m : ℤ)-1)*81879*gap := by
    nlinarith only [hcancelZ]
  have firstZ : ((m : ℤ)-(cap : ℤ))*x ≤ (cap : ℤ)*81879 := by
    nlinarith only [hfirstZ]
  by_contra! h
  have hbadZ : (81879 : ℤ)*cap + gap < (gap : ℤ)*m := by exact_mod_cast h
  have hbad : (cap : ℤ)*81879 < ((m : ℤ)-1)*gap := by nlinarith only [hbadZ]
  have hxpos : 0 < (x : ℤ) := by omega
  have cmp : (m : ℤ)*81879 - ((m : ℤ)-1)*gap < ((m : ℤ)-(cap : ℤ))*81879 := by
    linarith only [hbad]
  have left := mul_lt_mul_of_pos_right cmp hxpos
  have right := mul_le_mul_of_nonneg_right firstZ (by norm_num : (0 : ℤ) ≤ 81879)
  have impossible := secondZ.trans_lt (left.trans_le (show
      ((m : ℤ)-(cap : ℤ))*81879*x ≤ (cap : ℤ)*81879*81879 from by
        convert right using 1
        ring))
  have bigger := mul_lt_mul_of_pos_right hbad (by norm_num : (0 : ℤ) < 81879)
  nlinarith only [impossible, bigger]

/-- A uniform occupancy cap on the nonpersistent nodes gives the fixed-word
bound with the actual degree parameter in the agreement gap. -/
theorem section_capacity {w T s d} (h : FixedWord w T s d) (hd : d < 180265) (cap : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ T, (s γ).eval (node i) ≠ w i) →
      (T.filter fun γ => (s γ).eval (node i) = w i).card ≤ cap) :
    (180265 - d) * T.card ≤ 81879 * cap + (180265 - d) := by
  classical
  by_cases hm : T.card ≤ 1
  · have hb := Nat.mul_le_mul_left (180265 - d) hm
    simp only [Nat.mul_one] at hb
    omega
  let hits (γ : K) : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
  let common : Finset I := univ.filter fun i => ∀ γ ∈ T, (s γ).eval (node i) = w i
  let nodes : Finset I := univ \ common
  have common_le (γ : K) (hγ : γ ∈ T) : common ⊆ hits γ := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ : K) (hγ : γ ∈ T) : 180265 ≤ (hits γ).card := by
    obtain ⟨B, hB, hval⟩ := h.hits γ hγ
    exact hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hval i hi⟩)
  have pair_count (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (hits a ∩ hits b).card ≤ d := by
    let P := s a - s b
    have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (h.distinct ha hb eq)
    refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective
      P hp _ ?_).trans ((natDegree_sub_le _ _).trans (max_le (h.degree a ha) (h.degree b hb)))
    intro i hi
    change ((s a) - (s b)).eval (node i) = 0
    rw [eval_sub, (mem_filter.mp (mem_inter.mp hi).1).2, (mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < T.card)
  have hcommon : common.card ≤ d :=
    (card_le_card (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x := 180265 - common.card
  let t := d - common.card
  have ht : t = x - (180265 - d) := by dsimp [t, x]; omega
  have hx : 180265 - d ≤ x := by dsimp [x]; omega
  have hnodes : nodes.card = x + 81879 := by
    rw [card_sdiff_of_subset (subset_univ common), card_univ, IRSProfile.card_index]
    dsimp [x]
    omega
  have exists_trim (γ : K) : ∃ B : Finset I, γ ∈ T → B ⊆ hits γ \ common ∧ B.card = x := by
    by_cases hγ : γ ∈ T
    · have hc := hit_count γ hγ
      have hsize : x ≤ (hits γ \ common).card := by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨B, hB, hcard⟩ := exists_subset_card_eq hsize
      exact ⟨B, fun _ => ⟨hB, hcard⟩⟩
    · exact ⟨∅, fun h => (hγ h).elim⟩
  choose B hB using exists_trim
  have into_nodes (γ : K) (hγ : γ ∈ T) : B γ ⊆ nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a : K) (ha : a ∈ T) (b : K) (hb : b ∈ T) (hab : a ≠ b) :
      (B a ∩ B b).card ≤ t := by
    have cover : (B a ∩ B b) ∪ common ⊆ hits a ∩ hits b := by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hB a ha).1 (mem_inter.mp hi).1)).1,
          (mem_sdiff.mp ((hB b hb).1 (mem_inter.mp hi).2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hi, common_le b hb hi⟩
    have disj : Disjoint (B a ∩ B b) common := disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc := (card_le_card cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i : I) (hi : i ∈ nodes) : (T.filter fun γ => i ∈ B γ).card ≤ cap := by
    have proper : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i := by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, hc⟩)
    refine (card_le_card ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ, hi⟩ := mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ, (mem_filter.mp (mem_sdiff.mp ((hB γ hγ).1 hi)).1).2⟩
  obtain ⟨second, first⟩ := occupancy T nodes B x t cap
    (fun γ hγ => ⟨into_nodes γ hγ, (hB γ hγ).2⟩) overlap occ_le
  rw [hnodes, ht] at second
  rw [hnodes] at first
  exact incidence_arithmetic _ _ _ _ (by omega) (by omega) hx second first

end
end K1_14_6
end PackSource_K1_14_6Incidence

section PackSource_K1_14_6_1Differential
set_option autoImplicit true
set_option autoImplicit false

namespace K1_14_6_1

noncomputable section

open K1 K1_14 K1_14_6
open scoped Polynomial

private abbrev Dual := TrivSqZeroExt FX FX
private abbrev incl := algebraMap L[X] FX

/-- The value and first derivative at the generic abscissa. -/
private def polyJet : L[X] →+* Dual where
  toFun g := (incl g, incl g.derivative)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' g h := by
    apply TrivSqZeroExt.ext
    · change incl (g + h) = incl g + incl h
      exact map_add _ _ _
    · change incl ((g + h).derivative) = incl g.derivative + incl h.derivative
      rw [map_add, map_add]
  map_mul' g h := by
    apply TrivSqZeroExt.ext
    · change incl (g * h) = incl g * incl h
      exact map_mul _ _ _
    · change incl ((g * h).derivative) =
        incl g * incl h.derivative + incl g.derivative * incl h
      rw [Polynomial.derivative_mul, map_add, map_mul, map_mul, add_comm]

private theorem polyJet_fst (g : L[X]) : (polyJet g).fst = incl g := rfl

private def rationalJet : FX →+* Dual :=
  IsLocalization.lift (M := nonZeroDivisors L[X]) (g := polyJet)
    (fun g => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
      (isUnit_iff_ne_zero.mpr (by
        rw [polyJet_fst]
        simpa only [map_zero] using (IsFractionRing.injective L[X] FX).ne (mem_nonZeroDivisors_iff_ne_zero.mp g.2))))

private theorem rationalJet_incl (g : L[X]) : rationalJet (incl g) = polyJet g := by
  exact IsLocalization.lift_eq _ _

private theorem rationalJet_fst (a : FX) : (rationalJet a).fst = a := by
  have h : (TrivSqZeroExt.fstHom FX FX FX).toRingHom.comp rationalJet = RingHom.id FX := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors L[X])
    apply RingHom.ext
    intro g
    exact congrArg TrivSqZeroExt.fst (rationalJet_incl g)
  exact RingHom.congr_fun h a

def Dx : FX →+ FX :=
  (TrivSqZeroExt.sndHom (R := FX) (M := FX)).toAddMonoidHom.comp rationalJet.toAddMonoidHom

theorem Dx_mul (a b : FX) : Dx (a * b) = a * Dx b + Dx a * b := by
  change (rationalJet (a * b)).snd = _
  rw [map_mul]
  change (rationalJet a).fst * Dx b + Dx a * (rationalJet b).fst = _
  rw [rationalJet_fst, rationalJet_fst]

theorem Dx_atX (g : K[X]) : Dx (atX g) = atX g.derivative := by
  change (rationalJet (incl (liftPoly g))).snd = _
  rw [rationalJet_incl]
  change incl (liftPoly g).derivative = incl (liftPoly g.derivative)
  rw [liftPoly, Polynomial.derivative_map, liftPoly]

private theorem Dx_seed (z : K) : Dx (seedEmbedding z) = 0 := by
  change (rationalJet (incl (Polynomial.C (algebraMap K L z)))).snd = _
  rw [rationalJet_incl]
  change incl (Polynomial.derivative (Polynomial.C (algebraMap K L z))) = _
  simp

theorem Dx_pow (a : FX) (n : ℕ) : Dx (a ^ n) = (n : FX) * a ^ (n - 1) * Dx a := by
  cases n with
  | zero =>
    change (rationalJet (a ^ 0)).snd = _
    simp
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ a (n + 1), Dx_mul, ih]
      push_cast
      simp only [pow_succ a n]
      ring

open MvPolynomial

/-- Coefficient differentiation holds both seed variables and the ordinate fixed. -/
def partialX : Biform →+ Biform :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom Dx).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

theorem coeff_partialX (P : Biform) (m : Option (Fin 2) →₀ ℕ) :
    (partialX P).coeff m = Dx (P.coeff m) := rfl

private theorem partialX_C (a : FX) : partialX (C a) = C (Dx a) := by
  ext m
  classical
  by_cases h : (0 : Option (Fin 2) →₀ ℕ) = m <;> simp [coeff_partialX, coeff_C, h]

private theorem partialX_mul_X (Q : Biform) (i : Option (Fin 2)) :
    partialX (Q * MvPolynomial.X i) = partialX Q * MvPolynomial.X i := by
  classical
  ext m
  simp only [coeff_partialX, coeff_mul_X']
  split <;> simp

/-- Chain rule at a marked polynomial, with the two graph coordinates constant. -/
theorem Dx_eval (z : K) (S : K[X]) (P : Biform) :
    Dx (eval (rootPoint z S) P) =
      eval (rootPoint z S) (partialX P) +
        atX S.derivative * eval (rootPoint z S) (pderiv none P) := by
  classical
  let ev := eval (rootPoint z S)
  change Dx (ev P) = ev (partialX P) + atX S.derivative * ev (pderiv none P)
  induction P using MvPolynomial.induction_on with
  | C a => simp [ev, partialX_C]
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, mul_add]
    ring
  | mul_X P i hP =>
    have hi : Dx (rootPoint z S i) =
        atX S.derivative * ev (pderiv none (MvPolynomial.X i)) := by
      cases i with
      | none => simp [rootPoint, ev, Dx_atX]
      | some j =>
        fin_cases j <;> simp [rootPoint, ev, pderiv_X, Dx_seed, Dx_pow]
    simp only [map_mul, Dx_mul, hP, partialX_mul_X, pderiv_mul, map_add]
    rw [show ev (MvPolynomial.X i) = rootPoint z S i by simp [ev], hi]
    ring

end
end K1_14_6_1
end PackSource_K1_14_6_1Differential

section PackSource_K1_14_6_1Recurrence
set_option autoImplicit true
set_option autoImplicit false

namespace K1_14_6_1

noncomputable section

open K1 K1_14 K1_14_6 MvPolynomial
open scoped Polynomial BigOperators

local notation "Y" => MvPolynomial.X (R := FX) (none : Option (Fin 2))
local notation "Pdy" => pderiv (R := FX) (none : Option (Fin 2))

abbrev flatten (f : Equation) : Biform := (optionEquivLeft FX (Fin 2)).symm f
abbrev separant (f : Biform) : Biform := Pdy f

/-- The tangent derivative multiplied by the separant. -/
def tangent (f P : Biform) : Biform :=
  separant f * partialX P - partialX f * Pdy P

/-- Numerator of the ordinary derivative of order n+1 over separant^(2*n+1). -/
def cleared (f : Biform) : ℕ → Biform
  | 0 => -partialX f
  | n + 1 => separant f * tangent f (cleared f n) -
      C ((2*n+1 : ℕ) : FX) * tangent f (separant f) * cleared f n

abbrev markEval (z : K) (S : K[X]) : Biform →+* FX := eval (rootPoint z S)

theorem eval_flatten (z : K) (S : K[X]) (f : Equation) :
    markEval z S (flatten f) = atMark f z S := by
  change eval (rootPoint z S) (flatten f) = _
  rw [show rootPoint z S = fun i => i.elim (atX S) ![seedEmbedding z, (seedEmbedding z)^p] by
    funext i
    cases i <;> rfl]
  rw [optionEquivLeft_elim_eval, AlgEquiv.apply_symm_apply, Polynomial.eval_map]
  rfl

theorem eval_separant (z : K) (S : K[X]) (f : Equation) :
    markEval z S (separant (flatten f)) = atMark f.derivative z S := by
  have h : separant (flatten f) = flatten f.derivative := by
    apply (optionEquivLeft FX (Fin 2)).injective
    rw [optionEquivLeft_pderiv_none, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rw [h, eval_flatten]

private theorem eval_tangent (f P : Biform) (z : K) (S : K[X])
    (hf : markEval z S f = 0) :
    markEval z S (tangent f P) = markEval z S (separant f) * Dx (markEval z S P) := by
  have h := Dx_eval z S f
  change Dx (markEval z S f) = _ at h
  rw [hf, map_zero] at h
  rw [Dx_eval, tangent, map_sub, map_mul, map_mul]
  linear_combination -markEval z S (Pdy P) * (Eq.symm h)

private theorem cleared_product_rule (m : ℕ) (a v : FX) :
    a * (a * Dx (a^m * v)) - (m : FX) * (a * Dx a) * (a^m * v) =
      a^(m+2) * Dx v := by
  cases m with
  | zero => simp [pow_two, mul_assoc]
  | succ m =>
    rw [Dx_mul, Dx_pow, Nat.succ_sub_one, pow_add a (m+1) 2, pow_succ' a m]
    ring

abbrev derivativeAt (S : K[X]) (n : ℕ) : FX :=
  atX (((Polynomial.derivative (R := K))^[n]) S)

theorem eval_cleared (f : Biform) (z : K) (S : K[X])
    (hf : markEval z S f = 0) (n : ℕ) :
    markEval z S (cleared f n) = markEval z S (separant f) ^ (2*n+1) * derivativeAt S (n+1) := by
  induction n with
  | zero =>
    have h := Dx_eval z S f
    change Dx (markEval z S f) = _ at h
    rw [hf, map_zero] at h
    simp only [cleared, map_neg, Nat.mul_zero, Nat.zero_add, pow_one]
    change -markEval z S (partialX f) = markEval z S (separant f) * atX S.derivative
    linear_combination -(Eq.symm h)
  | succ n ih =>
    rw [cleared, map_sub, map_mul, map_mul, map_mul, eval_C, eval_tangent _ _ _ _ hf,
      eval_tangent _ _ _ _ hf, ih, cleared_product_rule,
      show 2*(n+1)+1 = 2*n+1+2 by omega, Dx_atX]
    congr 1
    exact congrArg atX (Function.iterate_succ_apply' _ _ _).symm

end
end K1_14_6_1
end PackSource_K1_14_6_1Recurrence

section PackSource_K1_14_6Capacity
set_option autoImplicit true
namespace K1_14_6

noncomputable section

open Finset K1 MvPolynomial
open scoped BigOperators Polynomial

private theorem card_le_sum_cover {α β : Type*} (U : Finset α) (Ps : Finset β)
    (part : β → Finset α) (h : ∀ γ ∈ U, ∃ P ∈ Ps, γ ∈ part P) :
    U.card ≤ ∑ P ∈ Ps, (part P).card := by
  classical
  exact (card_le_card fun γ hγ => mem_biUnion.mpr (h γ hγ)).trans card_biUnion_le

def curveFactor (d : ℕ) : ℕ := 81879 / (180265 - d) + 1

private def LinearCover.slice {T s d e b} (C : LinearCover T s d e b)
    (U : Finset K) (P : Ideal (LinearRing d e b)) : Finset K := by
  classical
  exact U.filter fun γ => C.point γ ∈ zeroLocus ClosedField P

private def LinearCover.section {T s d e b} (C : LinearCover T s d e b)
    (P : Ideal (LinearRing d e b)) (x a : K) : Finset (Ideal (LinearRing d e b)) :=
  (P ⊔ Ideal.span {C.cut x a}).minimalPrimesFinset

/-- A nonpersistent value section is a proper linear cut. Its minimal
primes cover the hitting marks and spend at most the parent's degree. -/
private theorem LinearCover.cut_data {T s d e b} (C : LinearCover T s d e b) {U : Finset K}
    (hU : U ⊆ T) {P : Ideal (LinearRing d e b)} (hP : P.IsPrime)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P)
    {x a : K} (hmiss : ∃ γ ∈ U, (s γ).eval x ≠ a) :
    (let V := U.filter fun γ => (s γ).eval x = a
     V.card ≤ ∑ Q ∈ C.section P x a, (C.slice V Q).card) ∧
    (∀ Q ∈ C.section P x a, Q.IsPrime ∧
      (affineHilbertPolynomial Q).natDegree + 1 = (affineHilbertPolynomial P).natDegree) ∧
    (∑ Q ∈ C.section P x a, affineDegree Q) ≤ affineDegree P := by
  classical
  let prime := hP
  have hproper : C.cut x a ∉ P := by
    obtain ⟨γ, hγ, hv⟩ := hmiss
    intro hp
    exact hv ((C.cut_eval γ (hU hγ) x a).mp (hpoints γ hγ _ hp))
  refine ⟨?_, ?_, ?_⟩
  · dsimp only
    apply card_le_sum_cover
    intro γ hγ
    obtain ⟨hγU, hv⟩ := mem_filter.mp hγ
    have hp : C.point γ ∈ zeroLocus ClosedField (P ⊔ Ideal.span {C.cut x a}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hpoints γ hγU, (C.cut_eval γ (hU hγU) x a).mpr hv⟩
    obtain ⟨Q, hQ, hγQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hp (by simp)
    exact ⟨Q, Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ, hγQ⟩⟩
  · intro Q hQ
    have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
    exact ⟨hmin.isPrime, principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin⟩
  · simpa only [LinearCover.section, Nat.cast_one, one_mul] using
      principalCut_sum_affineDegree_minimalPrimes_le hproper (C.cut_degree x a)

private theorem LinearCover.zero_dim_count {T s d e b} (C : LinearCover T s d e b)
    {U : Finset K} (hU : U ⊆ T) (P : Ideal (LinearRing d e b))
    (hP : (affineHilbertPolynomial P).natDegree = 0)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P) : (U.card : ℚ) ≤ affineDegree P := by
  classical
  let image := U.image C.point
  have hc : image.card = U.card := card_image_of_injOn (C.injective.mono hU)
  have hsub : (image : Set _) ⊆ zeroLocus ClosedField P := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hx
    exact hpoints γ hγ
  obtain ⟨hfinite, hdegree⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K := ClosedField) P hP
  have hn := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, hc] at hn
  exact (Nat.cast_le.mpr hn).trans hdegree

/-- In dimension one the leading coefficient is the difference of two
successive integer Hilbert-function values, and is positive for a prime. -/
private theorem curve_degree_nat {k σ : Type*} [Field k] [Finite σ]
    (P : Ideal (MvPolynomial σ k)) (hP : P.IsPrime)
    (hdim : (affineHilbertPolynomial P).natDegree = 1) :
    ∃ δ : ℕ, 0 < δ ∧ affineDegree P = (δ : ℚ) := by
  let H := affineHilbertPolynomial P
  have hlin : H = Polynomial.C (H.coeff 0) + Polynomial.C (H.coeff 1) * Polynomial.X := by
    have hH : H.natDegree < 2 := by change (affineHilbertPolynomial P).natDegree < 2; omega
    simpa [Finset.sum_range_succ] using H.as_sum_range_C_mul_X_pow' hH
  have evalH (u : ℚ) : H.eval u = H.coeff 0 + H.coeff 1 * u := by
    conv_lhs => rw [hlin]
    simp
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial P
  let m := affineHilbertFunction P (N + 1)
  let n := affineHilbertFunction P N
  have hdiff : affineDegree P = (m : ℚ) - (n : ℚ) := by
    rw [affineDegree, hdim, Nat.factorial_one, Nat.cast_one, one_mul, Polynomial.leadingCoeff, hdim]
    dsimp only [m, n]
    rw [← hN (N+1) (by omega), ← hN N le_rfl]
    change H.coeff 1 = H.eval ((N+1 : ℕ) : ℚ) - H.eval (N : ℚ)
    rw [evalH, evalH, Nat.cast_add, Nat.cast_one]
    ring
  have hmn : n < m := by
    have hpos := affineDegree_pos hP.ne_top
    rw [hdiff] at hpos
    exact_mod_cast sub_pos.mp hpos
  exact ⟨m-n, Nat.sub_pos_of_lt hmn, hdiff.trans (Nat.cast_sub hmn.le).symm⟩

private theorem LinearCover.curve_count {T s d e b w} (C : LinearCover T s d e b)
    {U : Finset K} (hU : U ⊆ T) (hword : FixedWord w U s d) (hd : d < 180265)
    (P : Ideal (LinearRing d e b)) (hP : P.IsPrime)
    (hdim : (affineHilbertPolynomial P).natDegree = 1)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P) :
    (U.card : ℚ) ≤ (curveFactor d : ℚ) * affineDegree P := by
  classical
  obtain ⟨δ, hδ, hδdeg⟩ := curve_degree_nat P hP hdim
  have hsection (i : I) (hi : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ δ := by
    let V := U.filter fun γ => (s γ).eval (node i) = w i
    let Qs := C.section P (node i) (w i)
    obtain ⟨hsum, dims, degree⟩ := C.cut_data hU hP hpoints hi
    have hone (Q : Ideal (LinearRing d e b)) (hQ : Q ∈ Qs) :
        ((C.slice V Q).card : ℚ) ≤ affineDegree Q := by
      have hQdim := (dims Q hQ).2
      rw [hdim] at hQdim
      exact C.zero_dim_count ((filter_subset _ _).trans ((filter_subset _ _).trans hU))
        Q (by omega) (fun _ hγ => (mem_filter.mp hγ).2)
    have hsumQ : (V.card : ℚ) ≤ ∑ Q ∈ Qs, ((C.slice V Q).card : ℚ) := by
      exact_mod_cast hsum
    have hbound := hsumQ.trans ((sum_le_sum hone).trans (degree.trans_eq hδdeg))
    exact_mod_cast hbound
  have hcount := section_capacity hword hd δ hsection
  let gap := 180265 - d
  have hgap : 0 < gap := Nat.sub_pos_of_lt hd
  have hfactor : 81879 < gap * curveFactor d := by
    change 81879 < gap * (81879 / gap + 1)
    rw [Nat.mul_add, Nat.mul_one]
    have heq := Nat.mod_add_div 81879 gap
    have hr := Nat.mod_lt 81879 hgap
    omega
  suffices hcard : U.card ≤ curveFactor d * δ by
    rw [hδdeg, ← Nat.cast_mul]
    exact_mod_cast hcard
  by_contra! hbad
  have hstep := Nat.mul_le_mul_left gap (show curveFactor d * δ + 1 ≤ U.card by omega)
  rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] at hstep
  have hstrict := Nat.mul_lt_mul_of_pos_right hfactor hδ
  change gap * U.card ≤ 81879 * δ + gap at hcount
  omega

private theorem LinearCover.surface_count {T s d e b w} (C : LinearCover T s d e b)
    {U : Finset K} (hU : U ⊆ T) (hword : FixedWord w U s d) (hd : d < 180265)
    (P : Ideal (LinearRing d e b)) (hP : P.IsPrime)
    (hdim : (affineHilbertPolynomial P).natDegree = 2)
    (hpoints : ∀ γ ∈ U, C.point γ ∈ zeroLocus ClosedField P) :
    ((180265 - d : ℕ) : ℚ) * U.card ≤
      81879 * (curveFactor d : ℚ) * affineDegree P + ((180265 - d : ℕ) : ℚ) := by
  classical
  let r := (curveFactor d : ℚ) * affineDegree P
  have hr : 0 ≤ r := mul_nonneg (Nat.cast_nonneg _) (affineDegree_nonneg P)
  have hsection (i : I) (hi : ∃ γ ∈ U, (s γ).eval (node i) ≠ w i) :
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ ⌊r⌋₊ := by
    apply (Nat.le_floor_iff hr).mpr
    let V := U.filter fun γ => (s γ).eval (node i) = w i
    let Qs := C.section P (node i) (w i)
    obtain ⟨hsum, dims, degree⟩ := C.cut_data hU hP hpoints hi
    have hone (Q : Ideal (LinearRing d e b)) (hQ : Q ∈ Qs) :
        ((C.slice V Q).card : ℚ) ≤ (curveFactor d : ℚ) * affineDegree Q := by
      obtain ⟨hpr, hdimQ⟩ := dims Q hQ
      rw [hdim] at hdimQ
      have hVU : C.slice V Q ⊆ U := (filter_subset _ _).trans (filter_subset _ _)
      exact C.curve_count (hVU.trans hU) (hword.mono hVU) hd Q hpr (by omega)
        (fun _ hγ => (mem_filter.mp hγ).2)
    have hsumQ : (V.card : ℚ) ≤ ∑ Q ∈ Qs, ((C.slice V Q).card : ℚ) := by
      exact_mod_cast hsum
    refine hsumQ.trans ((sum_le_sum hone).trans ?_)
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left degree (Nat.cast_nonneg _)
  have hcount := section_capacity hword hd ⌊r⌋₊ hsection
  have hcountQ : ((180265 - d : ℕ) : ℚ) * U.card ≤
      81879 * (⌊r⌋₊ : ℚ) + ((180265 - d : ℕ) : ℚ) := by exact_mod_cast hcount
  have hfloor := Nat.floor_le hr
  dsimp only [r] at hfloor
  linarith only [hcountQ, hfloor]

/-- Sum the fixed-word bound over the regular source components, with one
additive allowance for each component and one shared mixed degree budget. -/
theorem LinearCover.count {T s d e b w} (C : LinearCover T s d e b)
    (hword : FixedWord w T s d) (hd : d < 180265) :
    (180265 - d) * T.card ≤ 81879 * curveFactor d * mixedDegree d e b + (180265 - d) * e := by
  classical
  let gap : ℕ := 180265 - d
  have hcover : T.card ≤ ∑ P ∈ C.components, (C.slice T P).card := by
    apply card_le_sum_cover
    intro γ hγ
    obtain ⟨P, hP, hpoint⟩ := C.covers γ hγ
    exact ⟨P, hP, mem_filter.mpr ⟨hγ, hpoint⟩⟩
  have hcoverQ : (T.card : ℚ) ≤ ∑ P ∈ C.components, ((C.slice T P).card : ℚ) := by
    exact_mod_cast hcover
  have hone (P : Ideal (LinearRing d e b)) (hP : P ∈ C.components) :
      (gap : ℚ) * ((C.slice T P).card : ℚ) ≤
        81879 * (curveFactor d : ℚ) * affineDegree P + (gap : ℚ) :=
    C.surface_count (filter_subset _ _) (hword.mono (filter_subset _ _)) hd
      P (C.is_prime P hP) (C.dimension P hP) (fun _ hγ => (mem_filter.mp hγ).2)
  have hcount : (gap : ℚ) * T.card ≤
      81879 * (curveFactor d : ℚ) * (mixedDegree d e b : ℚ) + (gap : ℚ) * e := by
    calc
      _ ≤ (gap : ℚ) * ∑ P ∈ C.components, ((C.slice T P).card : ℚ) :=
        mul_le_mul_of_nonneg_left hcoverQ (Nat.cast_nonneg _)
      _ = ∑ P ∈ C.components, (gap : ℚ) * ((C.slice T P).card : ℚ) := mul_sum ..
      _ ≤ ∑ P ∈ C.components, (81879 * (curveFactor d : ℚ) * affineDegree P + (gap : ℚ)) :=
        sum_le_sum hone
      _ = 81879 * (curveFactor d : ℚ) * (∑ P ∈ C.components, affineDegree P) +
          (gap : ℚ) * (C.components.card : ℚ) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_comm (C.components.card : ℚ)]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left C.degree_sum (by positivity))
        (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr C.component_count) (Nat.cast_nonneg _))
  exact_mod_cast hcount

end
end K1_14_6
end PackSource_K1_14_6Capacity

section PackSource_K1_14_6_2Source
set_option autoImplicit true
namespace K1_14_6_2

noncomputable section

open MvPolynomial UniqueFactorizationMonoid
open scoped Polynomial BigOperators

variable {F : Type*} [Field F]

abbrev SourcePolynomial (F : Type*) [Field F] := Polynomial (MvPolynomial (Fin 2) F)

/-- Present the ordinate and the two seeds in a single multivariate ring. -/
def flatten : SourcePolynomial F ≃ₐ[F] MvPolynomial (Option (Fin 2)) F :=
  (optionEquivLeft F (Fin 2)).symm

theorem eval_flatten (f : SourcePolynomial F) (x : Option (Fin 2) → F) :
    MvPolynomial.eval x (flatten f) =
      f.eval₂ (MvPolynomial.eval (x ∘ some)) (x none) := by
  have hx : (fun i => Option.elim i (x none) (x ∘ some)) = x := by
    funext i
    cases i <;> rfl
  rw [Polynomial.eval₂_eq_eval_map]
  have h := optionEquivLeft_elim_eval F (Fin 2) (x ∘ some) (x none) (flatten f)
  rw [hx, show optionEquivLeft F (Fin 2) (flatten f) = f from
    (optionEquivLeft F (Fin 2)).apply_symm_apply f] at h
  exact h

private theorem flatten_bound (f : SourcePolynomial F) {e b : ℕ}
    (he : f.natDegree ≤ e) (hb : ∀ i, (f.coeff i).totalDegree ≤ b) :
    flatten f ∈ restrictBidegree (Fin 2) F e b := by
  rw [mem_restrictBidegree]
  intro m hm
  have hc : (f.coeff (m none)).coeff m.some ≠ 0 := by
    have hh := optionEquivLeft_coeff_some_coeff_none F (Fin 2) m (flatten f)
    rw [show optionEquivLeft F (Fin 2) (flatten f) = f from
      (optionEquivLeft F (Fin 2)).apply_symm_apply f] at hh
    rw [hh]
    exact MvPolynomial.mem_support_iff.mp hm
  exact ⟨(Polynomial.le_natDegree_of_ne_zero fun h => hc (by simp [h])).trans he,
    (le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)).trans (hb _)⟩

private theorem factor_span_minimal {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {f g : R}
    (hf : f ≠ 0) (hg : g ∈ factors f) :
    Ideal.span {g} ∈ (Ideal.span {f}).minimalPrimes := by
  have hp := prime_of_factor g hg
  refine ⟨⟨Ideal.isPrime_span_singleton_of_prime hp, (Ideal.span_singleton_le_iff_mem _).mpr
    (Ideal.mem_span_singleton.mpr (dvd_of_mem_factors hg))⟩, ?_⟩
  intro Q hQ hle
  have hfQ : f ∈ Q := hQ.2 (Ideal.subset_span (Set.mem_singleton f))
  have hprod : (factors f).prod ∈ Q :=
    ((Ideal.span_singleton_le_iff_mem _).mpr hfQ)
      (Ideal.mem_span_singleton.mpr (factors_prod hf).dvd')
  obtain ⟨q, hq, hqQ⟩ := (hQ.1.multiset_prod_mem_iff_exists_mem _).mp hprod
  have hdiv : g ∣ q := Ideal.mem_span_singleton.mp (hle hqQ)
  have hassoc := hp.associated_of_dvd (prime_of_factor q hq) hdiv
  rw [Ideal.span_singleton_eq_span_singleton.mpr hassoc]
  exact (Ideal.span_singleton_le_iff_mem _).mpr hqQ

private theorem comap_span_flatten (f : SourcePolynomial F) :
    (Ideal.span {f}).comap (optionEquivLeft F (Fin 2)).toRingHom =
      Ideal.span {flatten f} := by
  ext g
  simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
  change f ∣ optionEquivLeft F (Fin 2) g ↔ flatten f ∣ g
  constructor
  · intro h
    simpa only [AlgEquiv.symm_apply_apply, flatten] using
      map_dvd (optionEquivLeft F (Fin 2)).symm h
  · intro h
    simpa only [AlgEquiv.apply_symm_apply, flatten] using
      map_dvd (optionEquivLeft F (Fin 2)) h

private theorem positiveDegrees_card_le {R : Type*} [Semiring R]
    (fs : Multiset R[X]) :
    (fs.filter (fun g => 0 < g.natDegree)).card ≤ (fs.map Polynomial.natDegree).sum := by
  induction fs using Multiset.induction_on with
  | empty => simp
  | cons g fs ih =>
    by_cases hg : 0 < g.natDegree <;> simp [hg] <;> omega

private theorem positiveFactors_card_le [DecidableEq (SourcePolynomial F)]
    (f : SourcePolynomial F) (hf : f ≠ 0) :
    ((factors f).filter fun g => 0 < g.natDegree).toFinset.card ≤ f.natDegree := by
  obtain ⟨u, hu⟩ := factors_prod hf
  have hnz : (0 : SourcePolynomial F) ∉ factors f :=
    fun hz => (prime_of_factor 0 hz).ne_zero rfl
  have hdeg : ((factors f).prod).natDegree = f.natDegree := calc
    _ = ((factors f).prod * (u : SourcePolynomial F)).natDegree := by
      rw [Polynomial.natDegree_mul (Multiset.prod_ne_zero hnz) (Units.ne_zero u),
        Polynomial.natDegree_coe_units, add_zero]
    _ = _ := congrArg Polynomial.natDegree hu
  exact (Multiset.toFinset_card_le _).trans <| (positiveDegrees_card_le _).trans_eq <|
    (Polynomial.natDegree_multiset_prod _ hnz).symm.trans hdeg

/-- A regular root lies on a factor of positive ordinate degree. -/
private theorem positive_factor_at_root {R E : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Field E]
    (f : R[X]) (hf : f ≠ 0) (ev : R →+* E) (v : E)
    (hroot : f.eval₂ ev v = 0) (hreg : f.derivative.eval₂ ev v ≠ 0) :
    ∃ g ∈ factors f, 0 < g.natDegree ∧ g.eval₂ ev v = 0 := by
  let ev' := Polynomial.eval₂RingHom ev v
  obtain ⟨u, hu⟩ := factors_prod hf
  change ev' f = 0 at hroot
  rw [← hu, map_mul, mul_eq_zero] at hroot
  have hz := hroot.resolve_right (Units.ne_zero (Units.map ev'.toMonoidHom u))
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff] at hz
  obtain ⟨g, hg, hgz⟩ := Multiset.mem_map.mp hz
  change g.eval₂ ev v = 0 at hgz
  refine ⟨g, hg, Nat.pos_of_ne_zero ?_, hgz⟩
  intro hd
  obtain ⟨q, hq⟩ := dvd_of_mem_factors hg
  have hder : g.derivative = 0 := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.derivative_C]
  exact hreg (by rw [hq, Polynomial.derivative_mul]; simp [hder, hgz])

/-- The embedded components covering the simple-root locus share a single mixed degree budget. -/
theorem regularComponents {a c e b : ℕ} (ha : 0 < a) (hc : 0 < c)
    (f : SourcePolynomial F) (hf : f ≠ 0) (he : f.natDegree ≤ e)
    (hb : ∀ i, (f.coeff i).totalDegree ≤ b) :
    ∃ Q : Finset (Ideal (MvPolynomial (bidegreeExponents (Fin 2) a c) F)),
      (∀ P ∈ Q, P.IsPrime ∧ (affineHilbertPolynomial P).natDegree = 2) ∧
      Q.card ≤ e ∧
      (∑ P ∈ Q, affineDegree P) ≤ (e * c ^ 2 + 2 * b * a * c : ℕ) ∧
      ∀ x : Option (Fin 2) → F, f.eval₂ (MvPolynomial.eval (x ∘ some)) (x none) = 0 →
        f.derivative.eval₂ (MvPolynomial.eval (x ∘ some)) (x none) ≠ 0 →
        ∃ P ∈ Q, monomialPoint (bidegreeExponents (Fin 2) a c) x ∈ zeroLocus F P := by
  classical
  let phi := bidegreeMap (Fin 2) F a c
  let fs := ((factors f).filter (fun g => 0 < g.natDegree)).toFinset
  let component := fun g : SourcePolynomial F => (Ideal.span {flatten g}).comap phi
  let Q := fs.image component
  have hminimal {g : SourcePolynomial F} (hg : g ∈ fs) :
      component g ∈ ((Ideal.span {flatten f}).comap phi).minimalPrimes := by
    have hfac := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hg)).1
    have h := Ideal.minimalPrimes_comap_of_surjective
      (f := (optionEquivLeft F (Fin 2)).toRingHom)
      (optionEquivLeft F (Fin 2)).surjective (factor_span_minimal hf hfac)
    rw [comap_span_flatten, comap_span_flatten] at h
    exact Ideal.minimalPrimes_comap_of_surjective (bidegreeMap_surjective ha hc) h
  refine ⟨Q, ?_, Finset.card_image_le.trans ((positiveFactors_card_le f hf).trans he), ?_, ?_⟩
  · intro P hP
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hP
    have hp := (hminimal hg).isPrime
    have hg0 := (prime_of_factor g
      (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hg)).1).ne_zero
    have hflat : flatten g ≠ 0 := by
      simpa only [map_zero] using (flatten : SourcePolynomial F ≃ₐ[F] _).injective.ne hg0
    have hproper : Ideal.span {flatten g} ≠ ⊤ := by
      intro ht
      exact hp.ne_top (by simp [component, ht])
    exact ⟨hp, by
      simpa [component, phi, Nat.card_eq_fintype_card] using
        natDegree_affineHilbertPolynomial_comap_bidegreeMap_span_singleton ha hc hflat hproper⟩
  · have hsub : Q ⊆ ((Ideal.span {flatten f}).comap phi).minimalPrimesFinset := by
      intro P hP
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hP
      exact Ideal.mem_minimalPrimesFinset.mpr (hminimal hg)
    have hflat : flatten f ≠ 0 := by
      simpa only [map_zero] using (flatten : SourcePolynomial F ≃ₐ[F] _).injective.ne hf
    have hbound := affineDegree_comap_bidegreeMap_span_singleton_le ha hc hflat
      (flatten_bound f he hb)
    have hsum := sum_affineDegree_minimalPrimes_comap_bidegreeMap_span_singleton_le ha hc
      (flatten f)
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _ => affineDegree_nonneg P)).trans
      (hsum.trans (by simpa [phi, Nat.card_eq_fintype_card] using hbound))
  · intro x hroot hreg
    obtain ⟨g, hg, hd, hz⟩ := positive_factor_at_root f hf _ _ hroot hreg
    refine ⟨component g, Finset.mem_image.mpr
      ⟨g, Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr ⟨hg, hd⟩), rfl⟩, ?_⟩
    change monomialPoint _ x ∈ zeroLocus F ((Ideal.span {flatten g}).comap phi)
    rw [show phi = monomialMap F (bidegreeExponents (Fin 2) a c) from
      bidegreeMap_eq_monomialMap a c,
      monomialPoint_mem_zeroLocus_comap_iff (fun i => single_mem_bidegreeExponents ha hc i),
      mem_zeroLocus_iff_le_ker_aeval, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    change MvPolynomial.eval x (flatten g) = 0
    rwa [eval_flatten]

end
end K1_14_6_2
end PackSource_K1_14_6_2Source

section PackSource_K1_14_6_1Bidegree
set_option autoImplicit true
set_option autoImplicit false

namespace K1_14_6_1

noncomputable section

open K1_14 K1_14_6 MvPolynomial

local notation "Y" => MvPolynomial.X (R := FX) (none : Option (Fin 2))

abbrev box (a b : ℕ) := restrictBidegree (Fin 2) FX a b

private theorem flatten_bound {f : Equation} {e b : ℕ}
    (he : f.natDegree ≤ e) (hb : SeedBound f b) : flatten f ∈ box e b := by
  rw [mem_restrictBidegree]
  intro m hm
  have hc : m.some ∈ (f.coeff (m none)).support := by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    have h := optionEquivLeft_coeff_coeff FX (flatten f) (m none) m.some
    simp only [AlgEquiv.apply_symm_apply, Finsupp.optionElim_some] at h
    exact h.trans_ne hm
  have hc' : f.coeff (m none) ≠ 0 := by
    intro h
    simp [h] at hc
  exact ⟨(Polynomial.le_natDegree_of_ne_zero hc').trans he,
    (le_totalDegree hc).trans (hb (m none))⟩

private theorem partialX_bound {P : Biform} {a b : ℕ}
    (hP : P ∈ box a b) : partialX P ∈ box a b := by
  rw [mem_restrictBidegree] at hP ⊢
  intro m hm
  apply hP m
  contrapose! hm
  rw [notMem_support_iff] at hm ⊢
  rw [coeff_partialX, hm, map_zero]

private theorem separant_bound' {P : Biform} {a b : ℕ}
    (hP : P ∈ box a b) : separant P ∈ box (a-1) b := by
  rw [mem_restrictBidegree_iff_weightedTotalDegree_le] at hP ⊢
  exact ⟨(weightedTotalDegree_pderiv_le_sub _ _ _).trans (Nat.sub_le_sub_right hP.1 1),
    (weightedTotalDegree_pderiv_le _ _ _).trans hP.2⟩

theorem separant_bound {f : Equation} {e b : ℕ}
    (he : f.natDegree ≤ e) (hb : SeedBound f b) :
    separant (flatten f) ∈ box (e-1) b :=
  separant_bound' (flatten_bound he hb)

private theorem tangent_bound {f P : Biform} {e b a c : ℕ}
    (hf : f ∈ box e b) (hP : P ∈ box a c) (he : 0 < e) :
    tangent f P ∈ box (a+(e-1)) (c+b) := by
  have h1 := mul_mem_restrictBidegree (separant_bound' hf) (partialX_bound hP)
  unfold tangent
  apply (box _ _).sub_mem
  · simpa only [Nat.add_comm] using h1
  · by_cases ha : a = 0
    · have hzero : P.degreeOf none = 0 := by
        apply Nat.eq_zero_of_le_zero
        apply degreeOf_le_iff.mpr
        intro m hm
        simpa only [ha] using ((mem_restrictBidegree.mp hP) m hm).1
      rw [show pderiv none P = 0 from pderiv_eq_zero_of_degreeOf_eq_zero hzero, mul_zero]
      exact (box _ _).zero_mem
    · have h2 := mul_mem_restrictBidegree (partialX_bound hf) (separant_bound' hP)
      rwa [show e+(a-1) = a+(e-1) by omega, Nat.add_comm b c] at h2

theorem cleared_bound {f : Equation} {e b : ℕ} (he : 0 < e)
    (hfe : f.natDegree ≤ e) (hb : SeedBound f b) (n : ℕ) :
    cleared (flatten f) n ∈ box (1+(2*n+1)*(e-1)) ((2*n+1)*b) := by
  have hf := flatten_bound hfe hb
  induction n with
  | zero =>
    have h := (box _ _).neg_mem (partialX_bound hf)
    simpa only [cleared, Nat.mul_zero, Nat.zero_add, Nat.one_mul, show 1+(e-1) = e by omega]
      using h
  | succ n ih =>
    have ha := separant_bound' hf
    have h1 := mul_mem_restrictBidegree ha (tangent_bound hf ih he)
    have h2 := mul_mem_restrictBidegree (tangent_bound hf ha he) ih
    have h2' := (box _ _).smul_mem (((2*n+1 : ℕ) : FX)) h2
    rw [cleared]
    apply (box _ _).sub_mem
    · convert h1 using 2 <;> ring
    · rw [mul_assoc]
      rw [← MvPolynomial.smul_eq_C_mul]
      convert h2' using 2 <;> ring

theorem box_pow {P : Biform} {a b : ℕ} (hP : P ∈ box a b) (n : ℕ) :
    P ^ n ∈ box (n*a) (n*b) := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.zero_mul, mem_restrictBidegree]
    simp [support_one]
  | succ n ih =>
    simpa only [pow_succ, Nat.succ_mul] using mul_mem_restrictBidegree ih hP

theorem ordinate_mem : Y ∈ box 1 0 := by
  classical
  rw [mem_restrictBidegree, MvPolynomial.support_X]
  intro m hm
  rw [Finset.mem_singleton] at hm
  subst m
  simp

end
end K1_14_6_1
end PackSource_K1_14_6_1Bidegree

section PackSource_K1_14_6Split
set_option autoImplicit true
namespace K1_14_6

noncomputable section

open K1 K1_14 Polynomial

/-- The implicit recurrence, cleared to a common denominator, recovers the
value of every actual degree-bounded simple polynomial root. -/
def c1 : Prop :=
  ∀ d e b : ℕ, 0 < d → d < p → ∀ f : Equation,
    0 < f.natDegree → f.natDegree ≤ e → SeedBound f b →
    ∃ C : TaylorChart d e b, ∀ (z : K) (S : K[X]), S.natDegree ≤ d →
      atMark f z S = 0 → atMark f.derivative z S ≠ 0 → C.Recovers z S

/-- Linearize the bounded Taylor value forms on the regular source. The
source primes use one shared mixed degree budget and at most e components. -/
def c2 : Prop :=
  ∀ d e b : ℕ, 0 < d → 0 < b → ∀ f : Equation,
    0 < f.natDegree → f.natDegree ≤ e → f.IsPrimitive →
    (f.map (algebraMap Seeds (FractionRing Seeds))).Separable → SeedBound f b →
    ∀ (T : Finset K) (z : K → K) (s : K → K[X]), Set.InjOn z (T : Set K) →
      (∀ γ ∈ T, atMark f (z γ) (s γ) = 0 ∧ atMark f.derivative (z γ) (s γ) ≠ 0) →
      ∀ C : TaylorChart d e b, (∀ γ ∈ T, C.Recovers (z γ) (s γ)) →
        Nonempty (LinearCover T s d e b)

theorem of_children (h1 : c1) (h2 : c2) : K1_14.c6 := by
  intro u del M Γ F _hlo hhi f hf hseed T hT hroots
  let w := M.overhead
  let d := 131071 + (band w).endpoint
  let e := (band w).yBound
  let b := (band w).seedBound
  have hend : w ≤ ((band w).endpoint : ℤ) := by
    unfold band
    split_ifs with hfirst hsecond hthird
    · exact hfirst
    · exact hsecond
    · exact hthird
    · exact hhi
  have hd0 : 0 < d := by dsimp only [d]; omega
  have hd : d < 180265 := by
    dsimp only [d, band]
    split_ifs <;> decide
  have hdp : d < p := hd.trans (by decide)
  have hb0 : 0 < b := by
    dsimp only [b, band]
    split_ifs <;> decide
  obtain ⟨hf0, hfe, hprimitive, hsep⟩ := hf
  have hword : FixedWord M.word T F.scalar d := by
    refine ⟨F.distinct.mono hT, ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT hγ)).scalar_degree with hzero | hdeg
      · simp [hzero]
      · have hcast : ((F.scalar γ).natDegree : ℤ) ≤ (d : ℤ) := by
          dsimp only [d]
          push_cast
          exact hdeg.trans (add_le_add_right hend _)
        exact_mod_cast hcast
    · intro γ hγ
      let m := F.mark γ (hT hγ)
      exact ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩
  have hlabel : Set.InjOn M.label (T : Set K) := by
    intro γ _ η _ h
    exact sub_left_inj.mp h
  obtain ⟨C, hC⟩ := h1 d e b hd0 hdp f hf0 hfe hseed
  obtain ⟨cover⟩ := h2 d e b hd0 hb0 f hf0 hfe hprimitive hsep hseed T M.label F.scalar
    hlabel hroots C (fun γ hγ => hC _ _ (hword.degree γ hγ) (hroots γ hγ).1 (hroots γ hγ).2)
  have hcount := cover.count hword hd
  let gap := 180265 - d
  let total := 81879 * curveFactor d * mixedDegree d e b
  have hgap : 0 < gap := Nat.sub_pos_of_lt hd
  change gap * T.card ≤ total + gap * e at hcount
  change T.card ≤ (total + (gap - 1)) / gap + e
  have hmul : (T.card - e) * gap ≤ total + (gap - 1) := by
    rw [Nat.sub_mul, Nat.mul_comm T.card, Nat.mul_comm e]
    omega
  have hdiv := (Nat.le_div_iff_mul_le hgap).mpr hmul
  omega

end
end K1_14_6
end PackSource_K1_14_6Split

section PackSource_K1_14_6_2Proof
set_option autoImplicit true
namespace K1_14_6_2

noncomputable section

open K1 K1_14 K1_14_6 MvPolynomial
open scoped Polynomial

private abbrev ι : FX →+* ClosedField := algebraMap FX ClosedField

private def closedPoint (z : K) (S : K[X]) : Option (Fin 2) → ClosedField :=
  ι ∘ rootPoint z S

private theorem eval_extend {σ : Type*} (x : σ → FX) (P : MvPolynomial σ FX) :
    MvPolynomial.eval (ι ∘ x) (MvPolynomial.map ι P) = ι (MvPolynomial.eval x P) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_comp]

private def extendEquation (f : Equation) : SourcePolynomial ClosedField :=
  f.map (MvPolynomial.map ι)

private theorem extendEquation_eval (f : Equation) (z : K) (S : K[X]) :
    (extendEquation f).eval₂ (MvPolynomial.eval (closedPoint z S ∘ some))
      (closedPoint z S none) = ι (atMark f z S) := by
  change (f.map (MvPolynomial.map ι)).eval₂ _ (ι (atX S)) = _
  rw [Polynomial.eval₂_map, atMark, Polynomial.hom_eval₂]
  congr 1
  apply RingHom.ext
  intro g
  exact eval_extend (rootPoint z S ∘ some) g

private theorem extend_mem {P : Biform} {a c : ℕ}
    (hP : P ∈ restrictBidegree (Fin 2) FX a c) :
    MvPolynomial.map ι P ∈ restrictBidegree (Fin 2) ClosedField a c := by
  rw [mem_restrictBidegree] at hP ⊢
  intro m hm
  exact hP m (support_map_subset _ _ hm)

private theorem eval_valueCut {d e b : ℕ} (C : TaylorChart d e b)
    {z : K} {S : K[X]} (h : C.Recovers z S) (x a : K) :
    MvPolynomial.eval (closedPoint z S)
      (MvPolynomial.map ι (C.numerator x - seedEmbedding a • C.denominator)) = 0 ↔
      S.eval x = a := by
  obtain ⟨hD, hN⟩ := h
  rw [closedPoint, eval_extend, map_sub, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.eval_C, hN x]
  rw [← map_zero ι, ι.injective.eq_iff, sub_eq_zero, mul_comm (seedEmbedding a),
    mul_right_inj' hD]
  exact seedEmbedding.injective.eq_iff

theorem proof : K1_14_6.c2 := by
  classical
  intro d e b hd hb f hf0 hfe _hprimitive _hseparable hfseed T z s hz hroots C hC
  let a := ordinateBound d e
  let c := parameterBound d b
  have ha : 0 < a := by simp [a, ordinateBound]
  have hc : 0 < c := by
    change 0 < taylorPower d * b
    exact Nat.mul_pos (by unfold taylorPower; omega) hb
  let F := extendEquation f
  have hnat : F.natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (MvPolynomial.map_injective _ ι.injective) f
  have hF : F ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (by rw [hnat]; exact hf0)
  have hcoeff : ∀ j, (F.coeff j).totalDegree ≤ b := by
    intro j
    change ((f.map (MvPolynomial.map ι)).coeff j).totalDegree ≤ b
    rw [Polynomial.coeff_map]
    exact (Finset.sup_mono (support_map_subset _ _)).trans (hfseed j)
  obtain ⟨components, hdim, hcount, hsum, hcover⟩ :=
    regularComponents ha hc F hF (hnat.trans_le hfe) hcoeff
  let pt := fun γ => monomialPoint (bidegreeExponents (Fin 2) a c) (closedPoint (z γ) (s γ))
  let sectionPoly := fun x y => MvPolynomial.map ι (C.numerator x - seedEmbedding y • C.denominator)
  have hsection (x y : K) : sectionPoly x y ∈ restrictBidegree (Fin 2) ClosedField a c :=
    extend_mem (Submodule.sub_mem _ (C.numerator_bound x)
      (Submodule.smul_mem _ _ C.denominator_bound))
  let cut := fun x y => bidegreeLift (sectionPoly x y) (hsection x y)
  refine ⟨⟨pt, ?_, cut, fun x y => totalDegree_bidegreeLift_le_one _ _, ?_,
    components, fun P hP => (hdim P hP).1, fun P hP => (hdim P hP).2, ?_, hcount, ?_⟩⟩
  · intro γ hγ η hη hpt
    have hcoords : closedPoint (z γ) (s γ) = closedPoint (z η) (s η) :=
      monomialPoint_injective (fun i => single_mem_bidegreeExponents ha hc i) hpt
    have hfirst := congrFun hcoords (some (0 : Fin 2))
    change ι (seedEmbedding (z γ)) = ι (seedEmbedding (z η)) at hfirst
    exact hz hγ hη (seedEmbedding.injective (ι.injective hfirst))
  · intro γ hγ x y
    change aeval (monomialPoint _ (closedPoint (z γ) (s γ))) (bidegreeLift _ _) = 0 ↔ _
    rw [aeval_monomialPoint, ← bidegreeMap_eq_monomialMap, bidegreeMap_bidegreeLift]
    exact eval_valueCut C (hC γ hγ) x y
  · intro γ hγ
    apply hcover (closedPoint (z γ) (s γ))
    · rw [show F = extendEquation f from rfl, extendEquation_eval, (hroots γ hγ).1, map_zero]
    · rw [show F.derivative = extendEquation f.derivative from Polynomial.derivative_map _ _,
        extendEquation_eval]
      simpa only [map_zero] using ι.injective.ne (hroots γ hγ).2
  · exact hsum

end
end K1_14_6_2
end PackSource_K1_14_6_2Proof

section PackSource_K1_13_5_5Defs
set_option autoImplicit true
namespace K1_13_5_5

noncomputable section

open K1_13 MvPolynomial
open scoped BigOperators Polynomial

abbrev CoeffIndex := Fin taylorLength
abbrev CoeffRing := MvPolynomial CoeffIndex Geom
abbrev FreshField := FractionRing Geom[X]
abbrev FreshCoeffRing := MvPolynomial CoeffIndex FreshField
abbrev FreshJetRing := MvPolynomial (Fin 3) FreshField

/-- The coefficient coordinates of an actual polynomial of degree at most 133671. -/
def coeffPoint (P : Geom[X]) : CoeffIndex → Geom := fun a => P.coeff a.val

/-- The j-th Hasse jet at x as a linear form on the coefficient space. -/
def jetForm {F : Type*} [Field F] (x : F) (j : ℕ) : MvPolynomial CoeffIndex F :=
  ∑ a : CoeffIndex, C ((a.val.choose j : F) * x ^ (a.val - j)) * MvPolynomial.X a

def freshCenter : FreshField := algebraMap Geom[X] FreshField Polynomial.X

def freshRow (f : Row 3) : FreshJetRing :=
  MvPolynomial.map (algebraMap Geom[X] FreshField) f

def freshIdeal (P : Ideal CoeffRing) : Ideal FreshCoeffRing :=
  P.map (MvPolynomial.map (algebraMap Geom FreshField))

def freshProjection : FreshJetRing →ₐ[FreshField] FreshCoeffRing :=
  MvPolynomial.aeval fun j => jetForm freshCenter j.val

/-- The image is the hypersurface g over the independent abscissa field.
On the open where d is invertible, the displayed identities give a rational inverse. -/
structure FreshChart (P : Ideal CoeffRing) (g d : FreshJetRing) : Prop where
  prime : P.IsPrime
  equation_ne : g ≠ 0
  image : (freshIdeal P).comap freshProjection = Ideal.span {g}
  regular_open : d ∉ Ideal.span {g}
  recover : ∀ a : CoeffIndex, ∃ (v : FreshJetRing) (m : ℕ),
    freshProjection d ^ m * MvPolynomial.X a - freshProjection v ∈ freshIdeal P

end

end K1_13_5_5
end PackSource_K1_13_5_5Defs


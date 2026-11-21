import ProximityPrize.SubmissionLower.RankCharge82190

set_option Elab.async false
set_option linter.unusedVariables false
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
namespace RankCharge82190

def schedule15 (r : ℕ) : Method :=
  if r < 81 then (.source) else (if r < 84 then (.pascal) else (.target))

theorem total15 : grade 15 schedule15 = 60450 := by
  let f := fun r => value 15 r (schedule15 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 0 rfl
  have h12 := six h6 76 rfl
  have h18 := six h12 515 rfl
  have h24 := six h18 1455 rfl
  have h30 := six h24 2708 rfl
  have h36 := six h30 3853 rfl
  have h42 := six h36 4538 rfl
  have h48 := six h42 4795 rfl
  have h54 := six h48 4836 rfl
  have h60 := six h54 4836 rfl
  have h66 := six h60 4836 rfl
  have h72 := six h66 4836 rfl
  have h78 := six h72 4836 rfl
  have h84 := six h78 4825 rfl
  have h90 := six h84 4598 rfl
  have h96 := six h90 3913 rfl
  have h102 := six h96 2768 rfl
  have h108 := six h102 1515 rfl
  have h114 := six h108 575 rfl
  have h120 := six h114 129 rfl
  have h126 := six h120 7 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule16 (r : ℕ) : Method :=
  if r < 78 then (.source) else (if r < 83 then (.pascal) else (.target))

theorem total16 : grade 16 schedule16 = 70226 := by
  let f := fun r => value 16 r (schedule16 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4 rfl
  have h12 := six h6 185 rfl
  have h18 := six h12 866 rfl
  have h24 := six h18 2075 rfl
  have h30 := six h24 3499 rfl
  have h36 := six h30 4708 rfl
  have h42 := six h36 5396 rfl
  have h48 := six h42 5653 rfl
  have h54 := six h48 5694 rfl
  have h60 := six h54 5694 rfl
  have h66 := six h60 5694 rfl
  have h72 := six h66 5694 rfl
  have h78 := six h72 5694 rfl
  have h84 := six h78 5615 rfl
  have h90 := six h84 5118 rfl
  have h96 := six h90 4067 rfl
  have h102 := six h96 2667 rfl
  have h108 := six h102 1339 rfl
  have h114 := six h108 469 rfl
  have h120 := six h114 92 rfl
  have h126 := six h120 3 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule17 (r : ℕ) : Method :=
  if r < 75 then (.source) else (if r < 82 then (.pascal) else (.target))

theorem total17 : grade 17 schedule17 = 80665 := by
  let f := fun r => value 17 r (schedule17 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 24 rfl
  have h12 := six h6 372 rfl
  have h18 := six h12 1340 rfl
  have h24 := six h18 2809 rfl
  have h30 := six h24 4386 rfl
  have h36 := six h30 5643 rfl
  have h42 := six h36 6332 rfl
  have h48 := six h42 6589 rfl
  have h54 := six h48 6630 rfl
  have h60 := six h54 6630 rfl
  have h66 := six h60 6630 rfl
  have h72 := six h66 6630 rfl
  have h78 := six h72 6619 rfl
  have h84 := six h78 6357 rfl
  have h90 := six h84 5494 rfl
  have h96 := six h90 4085 rfl
  have h102 := six h96 2496 rfl
  have h108 := six h102 1158 rfl
  have h114 := six h108 377 rfl
  have h120 := six h114 63 rfl
  have h126 := six h120 1 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule18 (r : ℕ) : Method :=
  if r < 72 then (.source) else (if r < 81 then (.pascal) else (.target))

theorem total18 : grade 18 schedule18 = 91728 := by
  let f := fun r => value 18 r (schedule18 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 80 rfl
  have h12 := six h6 658 rfl
  have h18 := six h12 1942 rfl
  have h24 := six h18 3654 rfl
  have h30 := six h24 5366 rfl
  have h36 := six h30 6657 rfl
  have h42 := six h36 7346 rfl
  have h48 := six h42 7603 rfl
  have h54 := six h48 7644 rfl
  have h60 := six h54 7644 rfl
  have h66 := six h60 7644 rfl
  have h72 := six h66 7644 rfl
  have h78 := six h72 7564 rfl
  have h84 := six h78 6986 rfl
  have h90 := six h84 5702 rfl
  have h96 := six h90 3990 rfl
  have h102 := six h96 2278 rfl
  have h108 := six h102 987 rfl
  have h114 := six h108 298 rfl
  have h120 := six h114 41 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule19 (r : ℕ) : Method :=
  if r < 71 then (.source) else (if r < 80 then (.pascal) else (.target))

theorem total19 : grade 19 schedule19 = 103163 := by
  let f := fun r => value 19 r (schedule19 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 178 rfl
  have h12 := six h6 1045 rfl
  have h18 := six h12 2652 rfl
  have h24 := six h18 4589 rfl
  have h30 := six h24 6418 rfl
  have h36 := six h30 7731 rfl
  have h42 := six h36 8420 rfl
  have h48 := six h42 8677 rfl
  have h54 := six h48 8718 rfl
  have h60 := six h54 8718 rfl
  have h66 := six h60 8718 rfl
  have h72 := six h66 8714 rfl
  have h78 := six h72 8453 rfl
  have h84 := six h78 7448 rfl
  have h90 := six h84 5754 rfl
  have h96 := six h90 3805 rfl
  have h102 := six h96 2036 rfl
  have h108 := six h102 833 rfl
  have h114 := six h108 231 rfl
  have h120 := six h114 25 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

end RankCharge82190

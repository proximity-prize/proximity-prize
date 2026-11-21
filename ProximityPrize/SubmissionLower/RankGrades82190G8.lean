import ProximityPrize.SubmissionLower.RankCharge82190

set_option Elab.async false
set_option linter.unusedVariables false
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
namespace RankCharge82190

def schedule40 (r : ℕ) : Method :=
  if r < 50 then (.source) else (if r < 59 then (.pascal) else (.target))

theorem total40 : grade 40 schedule40 = 183300 := by
  let f := fun r => value 40 r (schedule40 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 3782 rfl
  have h12 := six h6 9621 rfl
  have h18 := six h12 14190 rfl
  have h24 := six h18 17471 rfl
  have h30 := six h24 19672 rfl
  have h36 := six h30 21009 rfl
  have h42 := six h36 21698 rfl
  have h48 := six h42 21955 rfl
  have h54 := six h48 20174 rfl
  have h60 := six h54 14198 rfl
  have h66 := six h60 9177 rfl
  have h72 := six h66 5488 rfl
  have h78 := six h72 2951 rfl
  have h84 := six h78 1350 rfl
  have h90 := six h84 469 rfl
  have h96 := six h90 92 rfl
  have h102 := six h96 3 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule41 (r : ℕ) : Method :=
  if r < 49 then (.source) else (if r < 58 then (.pascal) else (.target))

theorem total41 : grade 41 schedule41 = 180614 := by
  let f := fun r => value 41 r (schedule41 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 3853 rfl
  have h12 := six h6 9740 rfl
  have h18 := six h12 14310 rfl
  have h24 := six h18 17591 rfl
  have h30 := six h24 19792 rfl
  have h36 := six h30 21129 rfl
  have h42 := six h36 21818 rfl
  have h48 := six h42 22075 rfl
  have h54 := six h48 19345 rfl
  have h60 := six h54 13272 rfl
  have h66 := six h60 8473 rfl
  have h72 := six h66 4991 rfl
  have h78 := six h72 2625 rfl
  have h84 := six h78 1159 rfl
  have h90 := six h84 377 rfl
  have h96 := six h90 63 rfl
  have h102 := six h96 1 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule42 (r : ℕ) : Method :=
  if r < 48 then (.source) else (if r < 57 then (.pascal) else (.target))

theorem total42 : grade 42 schedule42 = 177696 := by
  let f := fun r => value 42 r (schedule42 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 3915 rfl
  have h12 := six h6 9836 rfl
  have h18 := six h12 14406 rfl
  have h24 := six h18 17687 rfl
  have h30 := six h24 19888 rfl
  have h36 := six h30 21225 rfl
  have h42 := six h36 21914 rfl
  have h48 := six h42 22171 rfl
  have h54 := six h48 18297 rfl
  have h60 := six h54 12376 rfl
  have h66 := six h60 7806 rfl
  have h72 := six h66 4525 rfl
  have h78 := six h72 2324 rfl
  have h84 := six h78 987 rfl
  have h90 := six h84 298 rfl
  have h96 := six h90 41 rfl
  have h102 := six h96 0 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule43 (r : ℕ) : Method :=
  if r < 47 then (.source) else (if r < 56 then (.pascal) else (.target))

theorem total43 : grade 43 schedule43 = 174559 := by
  let f := fun r => value 43 r (schedule43 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 3965 rfl
  have h12 := six h6 9908 rfl
  have h18 := six h12 14478 rfl
  have h24 := six h18 17759 rfl
  have h30 := six h24 19960 rfl
  have h36 := six h30 21297 rfl
  have h42 := six h36 21986 rfl
  have h48 := six h42 22048 rfl
  have h54 := six h48 17240 rfl
  have h60 := six h54 11518 rfl
  have h66 := six h60 7175 rfl
  have h72 := six h66 4089 rfl
  have h78 := six h72 2047 rfl
  have h84 := six h78 833 rfl
  have h90 := six h84 231 rfl
  have h96 := six h90 25 rfl
  have h102 := six h96 0 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule44 (r : ℕ) : Method :=
  if r < 46 then (.source) else (if r < 55 then (.pascal) else (.target))

theorem total44 : grade 44 schedule44 = 171261 := by
  let f := fun r => value 44 r (schedule44 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4006 rfl
  have h12 := six h6 9962 rfl
  have h18 := six h12 14532 rfl
  have h24 := six h18 17813 rfl
  have h30 := six h24 20014 rfl
  have h36 := six h30 21351 rfl
  have h42 := six h36 22040 rfl
  have h48 := six h42 21708 rfl
  have h54 := six h48 16197 rfl
  have h60 := six h54 10699 rfl
  have h66 := six h60 6579 rfl
  have h72 := six h66 3682 rfl
  have h78 := six h72 1793 rfl
  have h84 := six h78 696 rfl
  have h90 := six h84 175 rfl
  have h96 := six h90 14 rfl
  have h102 := six h96 0 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

end RankCharge82190

import ProximityPrize.SubmissionLower.RankCharge82190

set_option Elab.async false
set_option linter.unusedVariables false
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
namespace RankCharge82190

def schedule80 (r : ℕ) : Method :=
  if r < 14 then (.source) else (if r < 19 then (.rows) else (.target))

theorem total80 : grade 80 schedule80 = 51608 := by
  let f := fun r => value 80 r (schedule80 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 10040 rfl
  have h18 := six h12 13861 rfl
  have h24 := six h18 10695 rfl
  have h30 := six h24 6579 rfl
  have h36 := six h30 3682 rfl
  have h42 := six h36 1793 rfl
  have h48 := six h42 696 rfl
  have h54 := six h48 175 rfl
  have h60 := six h54 14 rfl
  have h66 := six h60 0 rfl
  have h72 := six h66 0 rfl
  have h78 := six h72 0 rfl
  have h84 := six h78 0 rfl
  have h90 := six h84 0 rfl
  have h96 := six h90 0 rfl
  have h102 := six h96 0 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule81 (r : ℕ) : Method :=
  if r < 14 then (.source) else (if r < 18 then (.rows) else (.target))

theorem total81 : grade 81 schedule81 = 49121 := by
  let f := fun r => value 81 r (schedule81 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 10040 rfl
  have h18 := six h12 13497 rfl
  have h24 := six h18 9919 rfl
  have h30 := six h24 6017 rfl
  have h36 := six h30 3303 rfl
  have h42 := six h36 1561 rfl
  have h48 := six h42 575 rfl
  have h54 := six h48 129 rfl
  have h60 := six h54 7 rfl
  have h66 := six h60 0 rfl
  have h72 := six h66 0 rfl
  have h78 := six h72 0 rfl
  have h84 := six h78 0 rfl
  have h90 := six h84 0 rfl
  have h96 := six h90 0 rfl
  have h102 := six h96 0 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule82 (r : ℕ) : Method :=
  if r < 13 then (.source) else (if r < 17 then (.rows) else (.target))

theorem total82 : grade 82 schedule82 = 46700 := by
  let f := fun r => value 82 r (schedule82 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 10040 rfl
  have h18 := six h12 13057 rfl
  have h24 := six h18 9177 rfl
  have h30 := six h24 5488 rfl
  have h36 := six h30 2951 rfl
  have h42 := six h36 1350 rfl
  have h48 := six h42 469 rfl
  have h54 := six h48 92 rfl
  have h60 := six h54 3 rfl
  have h66 := six h60 0 rfl
  have h72 := six h66 0 rfl
  have h78 := six h72 0 rfl
  have h84 := six h78 0 rfl
  have h90 := six h84 0 rfl
  have h96 := six h90 0 rfl
  have h102 := six h96 0 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule83 (r : ℕ) : Method :=
  if r < 13 then (.source) else (if r < 16 then (.rows) else (.target))

theorem total83 : grade 83 schedule83 = 44340 := by
  let f := fun r => value 83 r (schedule83 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 10040 rfl
  have h18 := six h12 12538 rfl
  have h24 := six h18 8473 rfl
  have h30 := six h24 4991 rfl
  have h36 := six h30 2625 rfl
  have h42 := six h36 1159 rfl
  have h48 := six h42 377 rfl
  have h54 := six h48 63 rfl
  have h60 := six h54 1 rfl
  have h66 := six h60 0 rfl
  have h72 := six h66 0 rfl
  have h78 := six h72 0 rfl
  have h84 := six h78 0 rfl
  have h90 := six h84 0 rfl
  have h96 := six h90 0 rfl
  have h102 := six h96 0 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule84 (r : ℕ) : Method :=
  if r < 12 then (.source) else (if r < 15 then (.rows) else (.target))

theorem total84 : grade 84 schedule84 = 42048 := by
  let f := fun r => value 84 r (schedule84 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 10040 rfl
  have h18 := six h12 11954 rfl
  have h24 := six h18 7806 rfl
  have h30 := six h24 4525 rfl
  have h36 := six h30 2324 rfl
  have h42 := six h36 987 rfl
  have h48 := six h42 298 rfl
  have h54 := six h48 41 rfl
  have h60 := six h54 0 rfl
  have h66 := six h60 0 rfl
  have h72 := six h66 0 rfl
  have h78 := six h72 0 rfl
  have h84 := six h78 0 rfl
  have h90 := six h84 0 rfl
  have h96 := six h90 0 rfl
  have h102 := six h96 0 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

end RankCharge82190

import ProximityPrize.SubmissionLower.RankCharge82190

set_option Elab.async false
set_option linter.unusedVariables false
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
namespace RankCharge82190

def schedule95 (r : ℕ) : Method :=
  if r < 9 then (if r < 7 then (.source) else (.rows)) else (if r < 10 then (.factor ⟨⟨3,0,0,0⟩,0⟩) else (.target))

theorem total95 : grade 95 schedule95 = 21132 := by
  let f := fun r => value 95 r (schedule95 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 7843 rfl
  have h18 := six h12 4991 rfl
  have h24 := six h18 2625 rfl
  have h30 := six h24 1159 rfl
  have h36 := six h30 377 rfl
  have h42 := six h36 63 rfl
  have h48 := six h42 1 rfl
  have h54 := six h48 0 rfl
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

def schedule96 (r : ℕ) : Method :=
  if r < 9 then (if r < 6 then (.source) else (.rows)) else (if r < 10 then (.factor ⟨⟨2,0,0,0⟩,0⟩) else (.target))

theorem total96 : grade 96 schedule96 = 19628 := by
  let f := fun r => value 96 r (schedule96 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 7380 rfl
  have h18 := six h12 4525 rfl
  have h24 := six h18 2324 rfl
  have h30 := six h24 987 rfl
  have h36 := six h30 298 rfl
  have h42 := six h36 41 rfl
  have h48 := six h42 0 rfl
  have h54 := six h48 0 rfl
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

def schedule97 (r : ℕ) : Method :=
  if r < 8 then (if r < 6 then (.source) else (.rows)) else (if r < 9 then (.factor ⟨⟨5,0,0,0⟩,0⟩) else (if r < 10 then (.factor ⟨⟨1,0,0,0⟩,0⟩) else (.target)))

theorem total97 : grade 97 schedule97 = 18186 := by
  let f := fun r => value 97 r (schedule97 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 6888 rfl
  have h18 := six h12 4089 rfl
  have h24 := six h18 2047 rfl
  have h30 := six h24 833 rfl
  have h36 := six h30 231 rfl
  have h42 := six h36 25 rfl
  have h48 := six h42 0 rfl
  have h54 := six h48 0 rfl
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

def schedule98 (r : ℕ) : Method :=
  if r < 8 then (if r < 5 then (.source) else (.rows)) else (if r < 9 then (.factor ⟨⟨4,0,0,0⟩,0⟩) else (.target))

theorem total98 : grade 98 schedule98 = 16811 := by
  let f := fun r => value 98 r (schedule98 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4067 rfl
  have h12 := six h6 6384 rfl
  have h18 := six h12 3682 rfl
  have h24 := six h18 1793 rfl
  have h30 := six h24 696 rfl
  have h36 := six h30 175 rfl
  have h42 := six h36 14 rfl
  have h48 := six h42 0 rfl
  have h54 := six h48 0 rfl
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

def schedule99 (r : ℕ) : Method :=
  if r < 7 then (if r < 5 then (.source) else (.rows)) else (if r < 8 then (.factor ⟨⟨7,0,0,0⟩,0⟩) else (if r < 9 then (.factor ⟨⟨3,0,0,0⟩,0⟩) else (.target)))

theorem total99 : grade 99 schedule99 = 15497 := by
  let f := fun r => value 99 r (schedule99 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4040 rfl
  have h12 := six h6 5882 rfl
  have h18 := six h12 3303 rfl
  have h24 := six h18 1561 rfl
  have h30 := six h24 575 rfl
  have h36 := six h30 129 rfl
  have h42 := six h36 7 rfl
  have h48 := six h42 0 rfl
  have h54 := six h48 0 rfl
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

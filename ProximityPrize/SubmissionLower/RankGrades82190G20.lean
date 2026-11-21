import ProximityPrize.SubmissionLower.RankCharge82190

set_option Elab.async false
set_option linter.unusedVariables false
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
namespace RankCharge82190

def schedule100 (r : ℕ) : Method :=
  if r < 7 then (if r < 4 then (.source) else (.rows)) else (if r < 8 then (.factor ⟨⟨6,0,0,0⟩,0⟩) else (if r < 9 then (.factor ⟨⟨2,0,0,0⟩,0⟩) else (.target)))

theorem total100 : grade 100 schedule100 = 14248 := by
  let f := fun r => value 100 r (schedule100 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 3992 rfl
  have h12 := six h6 5391 rfl
  have h18 := six h12 2951 rfl
  have h24 := six h18 1350 rfl
  have h30 := six h24 469 rfl
  have h36 := six h30 92 rfl
  have h42 := six h36 3 rfl
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

def schedule101 (r : ℕ) : Method :=
  if r < 7 then (if r < 4 then (.source) else (if r < 6 then (.rows) else (.factor ⟨⟨9,1,0,0⟩,0⟩))) else (if r < 8 then (.factor ⟨⟨5,0,0,0⟩,0⟩) else (if r < 9 then (.factor ⟨⟨1,0,0,0⟩,0⟩) else (.target)))

theorem total101 : grade 101 schedule101 = 13072 := by
  let f := fun r => value 101 r (schedule101 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 3915 rfl
  have h12 := six h6 4932 rfl
  have h18 := six h12 2625 rfl
  have h24 := six h18 1159 rfl
  have h30 := six h24 377 rfl
  have h36 := six h30 63 rfl
  have h42 := six h36 1 rfl
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

def schedule102 (r : ℕ) : Method :=
  if r < 6 then (if r < 3 then (.source) else (if r < 5 then (.rows) else (.factor ⟨⟨12,2,0,0⟩,0⟩))) else (if r < 7 then (.factor ⟨⟨8,0,0,0⟩,0⟩) else (if r < 8 then (.factor ⟨⟨4,0,0,0⟩,0⟩) else (.target)))

theorem total102 : grade 102 schedule102 = 11952 := by
  let f := fun r => value 102 r (schedule102 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 3830 rfl
  have h12 := six h6 4472 rfl
  have h18 := six h12 2324 rfl
  have h24 := six h18 987 rfl
  have h30 := six h24 298 rfl
  have h36 := six h30 41 rfl
  have h42 := six h36 0 rfl
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

def schedule103 (r : ℕ) : Method :=
  if r < 6 then (if r < 3 then (.source) else (if r < 5 then (.rows) else (.factor ⟨⟨11,1,0,0⟩,0⟩))) else (if r < 7 then (.factor ⟨⟨7,0,0,0⟩,0⟩) else (if r < 8 then (.factor ⟨⟨3,0,0,0⟩,0⟩) else (.target)))

theorem total103 : grade 103 schedule103 = 10878 := by
  let f := fun r => value 103 r (schedule103 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 3691 rfl
  have h12 := six h6 4051 rfl
  have h18 := six h12 2047 rfl
  have h24 := six h18 833 rfl
  have h30 := six h24 231 rfl
  have h36 := six h30 25 rfl
  have h42 := six h36 0 rfl
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

def schedule104 (r : ℕ) : Method :=
  if r < 5 then (if r < 3 then (.source) else (if r < 4 then (.factor ⟨⟨18,5,0,0⟩,5⟩) else (.factor ⟨⟨11,1,0,0⟩,0⟩))) else (if r < 7 then (if r < 6 then (.factor ⟨⟨9,0,0,0⟩,0⟩) else (.factor ⟨⟨5,0,0,0⟩,0⟩)) else (if r < 8 then (.factor ⟨⟨1,0,0,0⟩,0⟩) else (.target)))

theorem total104 : grade 104 schedule104 = 9893 := by
  let f := fun r => value 104 r (schedule104 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 3563 rfl
  have h12 := six h6 3652 rfl
  have h18 := six h12 1793 rfl
  have h24 := six h18 696 rfl
  have h30 := six h24 175 rfl
  have h36 := six h30 14 rfl
  have h42 := six h36 0 rfl
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

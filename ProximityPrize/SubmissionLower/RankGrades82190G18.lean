import ProximityPrize.SubmissionLower.RankCharge82190

set_option Elab.async false
set_option linter.unusedVariables false
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
namespace RankCharge82190

def schedule90 (r : ℕ) : Method :=
  if r < 9 then (.source) else (if r < 11 then (.rows) else (.target))

theorem total90 : grade 90 schedule90 = 29650 := by
  let f := fun r => value 90 r (schedule90 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 9596 rfl
  have h18 := six h12 7806 rfl
  have h24 := six h18 4525 rfl
  have h30 := six h24 2324 rfl
  have h36 := six h30 987 rfl
  have h42 := six h36 298 rfl
  have h48 := six h42 41 rfl
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

def schedule91 (r : ℕ) : Method :=
  if r < 9 then (.source) else (if r < 11 then (.rows) else (.target))

theorem total91 : grade 91 schedule91 = 27810 := by
  let f := fun r => value 91 r (schedule91 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 9337 rfl
  have h18 := six h12 7175 rfl
  have h24 := six h18 4089 rfl
  have h30 := six h24 2047 rfl
  have h36 := six h30 833 rfl
  have h42 := six h36 231 rfl
  have h48 := six h42 25 rfl
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

def schedule92 (r : ℕ) : Method :=
  if r < 10 then (if r < 8 then (.source) else (.rows)) else (if r < 11 then (.factor ⟨⟨2,0,0,0⟩,0⟩) else (.target))

theorem total92 : grade 92 schedule92 = 26046 := by
  let f := fun r => value 92 r (schedule92 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 9034 rfl
  have h18 := six h12 6579 rfl
  have h24 := six h18 3682 rfl
  have h30 := six h24 1793 rfl
  have h36 := six h30 696 rfl
  have h42 := six h36 175 rfl
  have h48 := six h42 14 rfl
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

def schedule93 (r : ℕ) : Method :=
  if r < 10 then (if r < 8 then (.source) else (.rows)) else (if r < 11 then (.factor ⟨⟨1,0,0,0⟩,0⟩) else (.target))

theorem total93 : grade 93 schedule93 = 24339 := by
  let f := fun r => value 93 r (schedule93 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 8674 rfl
  have h18 := six h12 6017 rfl
  have h24 := six h18 3303 rfl
  have h30 := six h24 1561 rfl
  have h36 := six h30 575 rfl
  have h42 := six h36 129 rfl
  have h48 := six h42 7 rfl
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

def schedule94 (r : ℕ) : Method :=
  if r < 9 then (if r < 7 then (.source) else (.rows)) else (if r < 10 then (.factor ⟨⟨4,0,0,0⟩,0⟩) else (.target))

theorem total94 : grade 94 schedule94 = 22707 := by
  let f := fun r => value 94 r (schedule94 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 8281 rfl
  have h18 := six h12 5488 rfl
  have h24 := six h18 2951 rfl
  have h30 := six h24 1350 rfl
  have h36 := six h30 469 rfl
  have h42 := six h36 92 rfl
  have h48 := six h42 3 rfl
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

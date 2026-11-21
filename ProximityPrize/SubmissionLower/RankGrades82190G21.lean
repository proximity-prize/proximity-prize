import ProximityPrize.SubmissionLower.RankCharge82190

set_option Elab.async false
set_option linter.unusedVariables false
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
namespace RankCharge82190

def schedule105 (r : ℕ) : Method :=
  if r < 4 then (if r < 2 then (.source) else (if r < 3 then (.factor ⟨⟨24,6,0,0⟩,8⟩) else (.factor ⟨⟨16,4,0,0⟩,3⟩))) else (if r < 6 then (if r < 5 then (.factor ⟨⟨12,2,0,0⟩,0⟩) else (.factor ⟨⟨8,0,0,0⟩,0⟩)) else (if r < 7 then (.factor ⟨⟨4,0,0,0⟩,0⟩) else (.target)))

theorem total105 : grade 105 schedule105 = 8945 := by
  let f := fun r => value 105 r (schedule105 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 3391 rfl
  have h12 := six h6 3282 rfl
  have h18 := six h12 1561 rfl
  have h24 := six h18 575 rfl
  have h30 := six h24 129 rfl
  have h36 := six h30 7 rfl
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

def schedule106 (r : ℕ) : Method :=
  if r < 4 then (if r < 2 then (.source) else (if r < 3 then (.factor ⟨⟨22,6,0,0⟩,6⟩) else (.factor ⟨⟨14,3,0,0⟩,1⟩))) else (if r < 6 then (if r < 5 then (.factor ⟨⟨10,1,0,0⟩,0⟩) else (.factor ⟨⟨6,0,0,0⟩,0⟩)) else (if r < 7 then (.factor ⟨⟨2,0,0,0⟩,0⟩) else (.target)))

theorem total106 : grade 106 schedule106 = 8043 := by
  let f := fun r => value 106 r (schedule106 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 3197 rfl
  have h12 := six h6 2932 rfl
  have h18 := six h12 1350 rfl
  have h24 := six h18 469 rfl
  have h30 := six h24 92 rfl
  have h36 := six h30 3 rfl
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

def schedule107 (r : ℕ) : Method :=
  if r < 3 then (if r < 1 then (.source) else (if r < 2 then (.factor ⟨⟨24,7,0,0⟩,0⟩) else (.factor ⟨⟨16,5,0,0⟩,4⟩))) else (if r < 5 then (if r < 4 then (.factor ⟨⟨12,2,0,0⟩,0⟩) else (.factor ⟨⟨8,0,0,0⟩,0⟩)) else (if r < 6 then (.factor ⟨⟨4,0,0,0⟩,0⟩) else (.target)))

theorem total107 : grade 107 schedule107 = 7173 := by
  let f := fun r => value 107 r (schedule107 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 2973 rfl
  have h12 := six h6 2600 rfl
  have h18 := six h12 1159 rfl
  have h24 := six h18 377 rfl
  have h30 := six h24 63 rfl
  have h36 := six h30 1 rfl
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

def schedule108 (r : ℕ) : Method :=
  if r < 3 then (if r < 1 then (.source) else (if r < 2 then (.factor ⟨⟨21,6,0,0⟩,2⟩) else (.factor ⟨⟨15,4,0,0⟩,2⟩))) else (if r < 5 then (if r < 4 then (.factor ⟨⟨9,1,0,0⟩,0⟩) else (.factor ⟨⟨5,0,0,0⟩,0⟩)) else (if r < 6 then (.factor ⟨⟨1,0,0,0⟩,0⟩) else (.target)))

theorem total108 : grade 108 schedule108 = 6297 := by
  let f := fun r => value 108 r (schedule108 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 2700 rfl
  have h12 := six h6 2271 rfl
  have h18 := six h12 987 rfl
  have h24 := six h18 298 rfl
  have h30 := six h24 41 rfl
  have h36 := six h30 0 rfl
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

def schedule109 (r : ℕ) : Method :=
  if r < 3 then (if r < 1 then (.factor ⟨⟨23,7,0,0⟩,0⟩) else (if r < 2 then (.factor ⟨⟨16,5,0,0⟩,4⟩) else (.factor ⟨⟨12,3,0,0⟩,0⟩))) else (if r < 4 then (.factor ⟨⟨8,0,0,0⟩,0⟩) else (if r < 5 then (.factor ⟨⟨4,0,0,0⟩,0⟩) else (.target)))

theorem total109 : grade 109 schedule109 = 5577 := by
  let f := fun r => value 109 r (schedule109 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 2490 rfl
  have h12 := six h6 1998 rfl
  have h18 := six h12 833 rfl
  have h24 := six h18 231 rfl
  have h30 := six h24 25 rfl
  have h36 := six h30 0 rfl
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

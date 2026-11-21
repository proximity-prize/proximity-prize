import ProximityPrize.SubmissionLower.RankCharge82190

set_option Elab.async false
set_option linter.unusedVariables false
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
namespace RankCharge82190

def schedule110 (r : ℕ) : Method :=
  if r < 3 then (if r < 1 then (.factor ⟨⟨20,6,0,0⟩,3⟩) else (if r < 2 then (.factor ⟨⟨15,4,0,0⟩,2⟩) else (.factor ⟨⟨8,0,0,0⟩,0⟩))) else (if r < 4 then (.factor ⟨⟨5,0,0,0⟩,0⟩) else (if r < 5 then (.factor ⟨⟨1,0,0,0⟩,0⟩) else (.target)))

theorem total110 : grade 110 schedule110 = 4755 := by
  let f := fun r => value 110 r (schedule110 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 2171 rfl
  have h12 := six h6 1699 rfl
  have h18 := six h12 696 rfl
  have h24 := six h18 175 rfl
  have h30 := six h24 14 rfl
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

def schedule111 (r : ℕ) : Method :=
  if r < 2 then (if r < 1 then (.factor ⟨⟨16,5,0,0⟩,4⟩) else (.factor ⟨⟨12,3,0,0⟩,0⟩)) else (if r < 3 then (.factor ⟨⟨8,1,0,0⟩,0⟩) else (if r < 4 then (.factor ⟨⟨4,0,0,0⟩,0⟩) else (.target)))

theorem total111 : grade 111 schedule111 = 4151 := by
  let f := fun r => value 111 r (schedule111 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 1966 rfl
  have h12 := six h6 1474 rfl
  have h18 := six h12 575 rfl
  have h24 := six h18 129 rfl
  have h30 := six h24 7 rfl
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

def schedule112 (r : ℕ) : Method :=
  if r < 2 then (if r < 1 then (.factor ⟨⟨14,5,0,0⟩,4⟩) else (.factor ⟨⟨9,2,0,0⟩,0⟩)) else (if r < 3 then (.factor ⟨⟨5,0,0,0⟩,0⟩) else (if r < 4 then (.factor ⟨⟨1,0,0,0⟩,0⟩) else (.target)))

theorem total112 : grade 112 schedule112 = 3387 := by
  let f := fun r => value 112 r (schedule112 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 1624 rfl
  have h12 := six h6 1200 rfl
  have h18 := six h12 468 rfl
  have h24 := six h18 92 rfl
  have h30 := six h24 3 rfl
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

def schedule113 (r : ℕ) : Method :=
  if r < 2 then (if r < 1 then (.factor ⟨⟨12,3,0,0⟩,0⟩) else (.factor ⟨⟨8,1,0,0⟩,0⟩)) else (if r < 3 then (.factor ⟨⟨4,0,0,0⟩,0⟩) else (.target))

theorem total113 : grade 113 schedule113 = 2895 := by
  let f := fun r => value 113 r (schedule113 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 1435 rfl
  have h12 := six h6 1020 rfl
  have h18 := six h12 376 rfl
  have h24 := six h18 63 rfl
  have h30 := six h24 1 rfl
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

def schedule114 (r : ℕ) : Method :=
  if r < 2 then (if r < 1 then (.factor ⟨⟨9,2,0,0⟩,0⟩) else (.factor ⟨⟨5,0,0,0⟩,0⟩)) else (if r < 3 then (.factor ⟨⟨1,0,0,0⟩,0⟩) else (.target))

theorem total114 : grade 114 schedule114 = 2208 := by
  let f := fun r => value 114 r (schedule114 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 1099 rfl
  have h12 := six h6 774 rfl
  have h18 := six h12 294 rfl
  have h24 := six h18 41 rfl
  have h30 := six h24 0 rfl
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

import ProximityPrize.SubmissionLower.RankCharge82190

set_option Elab.async false
set_option linter.unusedVariables false
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
namespace RankCharge82190

def schedule45 (r : ℕ) : Method :=
  if r < 45 then (.source) else (if r < 54 then (.pascal) else (.target))

theorem total45 : grade 45 schedule45 = 167812 := by
  let f := fun r => value 45 r (schedule45 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4035 rfl
  have h12 := six h6 9998 rfl
  have h18 := six h12 14568 rfl
  have h24 := six h18 17849 rfl
  have h30 := six h24 20050 rfl
  have h36 := six h30 21387 rfl
  have h42 := six h36 22076 rfl
  have h48 := six h42 21154 rfl
  have h54 := six h48 15184 rfl
  have h60 := six h54 9919 rfl
  have h66 := six h60 6017 rfl
  have h72 := six h66 3303 rfl
  have h78 := six h72 1561 rfl
  have h84 := six h78 575 rfl
  have h90 := six h84 129 rfl
  have h96 := six h90 7 rfl
  have h102 := six h96 0 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule46 (r : ℕ) : Method :=
  if r < 44 then (.source) else (if r < 53 then (.pascal) else (.target))

theorem total46 : grade 46 schedule46 = 164266 := by
  let f := fun r => value 46 r (schedule46 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4056 rfl
  have h12 := six h6 10022 rfl
  have h18 := six h12 14592 rfl
  have h24 := six h18 17873 rfl
  have h30 := six h24 20074 rfl
  have h36 := six h30 21411 rfl
  have h42 := six h36 22100 rfl
  have h48 := six h42 20399 rfl
  have h54 := six h48 14209 rfl
  have h60 := six h54 9177 rfl
  have h66 := six h60 5488 rfl
  have h72 := six h66 2951 rfl
  have h78 := six h72 1350 rfl
  have h84 := six h78 469 rfl
  have h90 := six h84 92 rfl
  have h96 := six h90 3 rfl
  have h102 := six h96 0 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule47 (r : ℕ) : Method :=
  if r < 43 then (.source) else (if r < 52 then (.pascal) else (.target))

theorem total47 : grade 47 schedule47 = 160630 := by
  let f := fun r => value 47 r (schedule47 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4067 rfl
  have h12 := six h6 10034 rfl
  have h18 := six h12 14604 rfl
  have h24 := six h18 17885 rfl
  have h30 := six h24 20086 rfl
  have h36 := six h30 21423 rfl
  have h42 := six h36 22112 rfl
  have h48 := six h42 19457 rfl
  have h54 := six h48 13273 rfl
  have h60 := six h54 8473 rfl
  have h66 := six h60 4991 rfl
  have h72 := six h66 2625 rfl
  have h78 := six h72 1159 rfl
  have h84 := six h78 377 rfl
  have h90 := six h84 63 rfl
  have h96 := six h90 1 rfl
  have h102 := six h96 0 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule48 (r : ℕ) : Method :=
  if r < 43 then (if r < 42 then (.source) else (.rows)) else (if r < 51 then (.pascal) else (.target))

theorem total48 : grade 48 schedule48 = 156949 := by
  let f := fun r => value 48 r (schedule48 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 10040 rfl
  have h18 := six h12 14610 rfl
  have h24 := six h18 17891 rfl
  have h30 := six h24 20092 rfl
  have h36 := six h30 21429 rfl
  have h42 := six h36 22118 rfl
  have h48 := six h42 18339 rfl
  have h54 := six h48 12376 rfl
  have h60 := six h54 7806 rfl
  have h66 := six h60 4525 rfl
  have h72 := six h66 2324 rfl
  have h78 := six h72 987 rfl
  have h84 := six h78 298 rfl
  have h90 := six h84 41 rfl
  have h96 := six h90 0 rfl
  have h102 := six h96 0 rfl
  have h108 := six h102 0 rfl
  have h114 := six h108 0 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule49 (r : ℕ) : Method :=
  if r < 42 then (if r < 41 then (.source) else (.rows)) else (if r < 50 then (.pascal) else (.target))

theorem total49 : grade 49 schedule49 = 153233 := by
  let f := fun r => value 49 r (schedule49 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 4073 rfl
  have h12 := six h6 10040 rfl
  have h18 := six h12 14610 rfl
  have h24 := six h18 17891 rfl
  have h30 := six h24 20092 rfl
  have h36 := six h30 21429 rfl
  have h42 := six h36 21929 rfl
  have h48 := six h42 17251 rfl
  have h54 := six h48 11518 rfl
  have h60 := six h54 7175 rfl
  have h66 := six h60 4089 rfl
  have h72 := six h66 2047 rfl
  have h78 := six h72 833 rfl
  have h84 := six h78 231 rfl
  have h90 := six h84 25 rfl
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

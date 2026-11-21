import ProximityPrize.SubmissionLower.RankCharge82190

set_option Elab.async false
set_option linter.unusedVariables false
set_option maxRecDepth 24000
set_option maxHeartbeats 4000000
namespace RankCharge82190

def schedule20 (r : ℕ) : Method :=
  if r < 70 then (.source) else (if r < 79 then (.pascal) else (.target))

theorem total20 : grade 20 schedule20 = 114660 := by
  let f := fun r => value 20 r (schedule20 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 317 rfl
  have h12 := six h6 1522 rfl
  have h18 := six h12 3443 rfl
  have h24 := six h18 5587 rfl
  have h30 := six h24 7515 rfl
  have h36 := six h30 8841 rfl
  have h42 := six h36 9530 rfl
  have h48 := six h42 9787 rfl
  have h54 := six h48 9828 rfl
  have h60 := six h54 9828 rfl
  have h66 := six h60 9828 rfl
  have h72 := six h66 9798 rfl
  have h78 := six h72 9213 rfl
  have h84 := six h78 7720 rfl
  have h90 := six h84 5673 rfl
  have h96 := six h90 3553 rfl
  have h102 := six h96 1792 rfl
  have h108 := six h102 696 rfl
  have h114 := six h108 175 rfl
  have h120 := six h114 14 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule21 (r : ℕ) : Method :=
  if r < 69 then (.source) else (if r < 78 then (.pascal) else (.target))

theorem total21 : grade 21 schedule21 = 125925 := by
  let f := fun r => value 21 r (schedule21 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 496 rfl
  have h12 := six h6 2070 rfl
  have h18 := six h12 4288 rfl
  have h24 := six h18 6621 rfl
  have h30 := six h24 8630 rfl
  have h36 := six h30 9963 rfl
  have h42 := six h36 10652 rfl
  have h48 := six h42 10909 rfl
  have h54 := six h48 10950 rfl
  have h60 := six h54 10950 rfl
  have h66 := six h60 10950 rfl
  have h72 := six h66 10837 rfl
  have h78 := six h72 9783 rfl
  have h84 := six h78 7815 rfl
  have h90 := six h84 5482 rfl
  have h96 := six h90 3257 rfl
  have h102 := six h96 1561 rfl
  have h108 := six h102 575 rfl
  have h114 := six h108 129 rfl
  have h120 := six h114 7 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule22 (r : ℕ) : Method :=
  if r < 68 then (.source) else (if r < 77 then (.pascal) else (.target))

theorem total22 : grade 22 schedule22 = 136680 := by
  let f := fun r => value 22 r (schedule22 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 712 rfl
  have h12 := six h6 2663 rfl
  have h18 := six h12 5160 rfl
  have h24 := six h18 7664 rfl
  have h30 := six h24 9737 rfl
  have h36 := six h30 11073 rfl
  have h42 := six h36 11762 rfl
  have h48 := six h42 12019 rfl
  have h54 := six h48 12060 rfl
  have h60 := six h54 12060 rfl
  have h66 := six h60 12060 rfl
  have h72 := six h66 11757 rfl
  have h78 := six h72 10139 rfl
  have h84 := six h78 7756 rfl
  have h90 := six h84 5204 rfl
  have h96 := six h90 2940 rfl
  have h102 := six h96 1350 rfl
  have h108 := six h102 469 rfl
  have h114 := six h108 92 rfl
  have h120 := six h114 3 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule23 (r : ℕ) : Method :=
  if r < 67 then (.source) else (if r < 76 then (.pascal) else (.target))

theorem total23 : grade 23 schedule23 = 146663 := by
  let f := fun r => value 23 r (schedule23 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 955 rfl
  have h12 := six h6 3274 rfl
  have h18 := six h12 6032 rfl
  have h24 := six h18 8689 rfl
  have h30 := six h24 10810 rfl
  have h36 := six h30 12147 rfl
  have h42 := six h36 12836 rfl
  have h48 := six h42 13093 rfl
  have h54 := six h48 13134 rfl
  have h60 := six h54 13134 rfl
  have h66 := six h60 13134 rfl
  have h72 := six h66 12478 rfl
  have h78 := six h72 10294 rfl
  have h84 := six h78 7567 rfl
  have h90 := six h84 4862 rfl
  have h96 := six h90 2624 rfl
  have h102 := six h96 1159 rfl
  have h108 := six h102 377 rfl
  have h114 := six h108 63 rfl
  have h120 := six h114 1 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

def schedule24 (r : ℕ) : Method :=
  if r < 66 then (.source) else (if r < 75 then (.pascal) else (.target))

theorem total24 : grade 24 schedule24 = 155628 := by
  let f := fun r => value 24 r (schedule24 r)
  have h0 : K1_13_1_1.sumRange 0 f = 0 := rfl
  have h6 := six h0 1206 rfl
  have h12 := six h6 3876 rfl
  have h18 := six h12 6877 rfl
  have h24 := six h18 9669 rfl
  have h30 := six h24 11824 rfl
  have h36 := six h30 13161 rfl
  have h42 := six h36 13850 rfl
  have h48 := six h42 14107 rfl
  have h54 := six h48 14148 rfl
  have h60 := six h54 14148 rfl
  have h66 := six h60 14148 rfl
  have h72 := six h66 12942 rfl
  have h78 := six h72 10272 rfl
  have h84 := six h78 7271 rfl
  have h90 := six h84 4479 rfl
  have h96 := six h90 2324 rfl
  have h102 := six h96 987 rfl
  have h108 := six h102 298 rfl
  have h114 := six h108 41 rfl
  have h120 := six h114 0 rfl
  have h126 := six h120 0 rfl
  have h132 := six h126 0 rfl
  have h138 := six h132 0 rfl
  exact h138

end RankCharge82190

import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0600

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_5488_1189 :
    P1_7_1.groupedPoleMoment 5488 1189 ≤ 24903571529391 :=
  _root_.PoleAffine6970.certified 5488 1189 24903571529391 (by decide) (by decide +kernel)

private theorem pole_5494_1213 :
    P1_7_1.groupedPoleMoment 5494 1213 ≤ 25383464767379 :=
  _root_.PoleAffine6970.certified 5494 1213 25383464767379 (by decide) (by decide +kernel)

private theorem pole_5496_1189 :
    P1_7_1.groupedPoleMoment 5496 1189 ≤ 25020597788251 :=
  _root_.PoleAffine6970.certified 5496 1189 25020597788251 (by decide) (by decide +kernel)

private theorem pole_5499_1213 :
    P1_7_1.groupedPoleMoment 5499 1213 ≤ 25457931418119 :=
  _root_.PoleAffine6970.certified 5499 1213 25457931418119 (by decide) (by decide +kernel)

private theorem pole_5500_1189 :
    P1_7_1.groupedPoleMoment 5500 1189 ≤ 25079250895001 :=
  _root_.PoleAffine6970.certified 5500 1189 25079250895001 (by decide) (by decide +kernel)

private theorem pole_5502_1213 :
    P1_7_1.groupedPoleMoment 5502 1213 ≤ 25502682687359 :=
  _root_.PoleAffine6970.certified 5502 1213 25502682687359 (by decide) (by decide +kernel)

private theorem pole_5504_1197 :
    P1_7_1.groupedPoleMoment 5504 1197 ≤ 25269814668608 :=
  _root_.PoleAffine6970.certified 5504 1197 25269814668608 (by decide) (by decide +kernel)

private theorem pole_5506_1213 :
    P1_7_1.groupedPoleMoment 5506 1213 ≤ 25562434272925 :=
  _root_.PoleAffine6970.certified 5506 1213 25562434272925 (by decide) (by decide +kernel)

private theorem pole_5507_1213 :
    P1_7_1.groupedPoleMoment 5507 1213 ≤ 25577387039299 :=
  _root_.Research6969.PackedRanks.PackedRanks306To308.moment5507_1213

private theorem pole_5507_1244 :
    P1_7_1.groupedPoleMoment 5507 1244 ≤ 26084011577468 :=
  _root_.Research6969.PackedRanks.PackedRanks306To308.moment5507_1244

theorem bank_3936_5488_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3936,5488,1189,u⟩,1834118800998400,24903571529391⟩ :=
  bank_checked 3936 5488 1189 u 1834118800998400 24903571529391
    (by decide) (by decide) (by decide) (by decide) pole_5488_1189

theorem bank_3950_5494_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3950,5494,1213,u⟩,1877062482395136,25383464767379⟩ :=
  bank_checked 3950 5494 1213 u 1877062482395136 25383464767379
    (by decide) (by decide) (by decide) (by decide) pole_5494_1213

theorem bank_3943_5496_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3943,5496,1189,u⟩,1841424233922560,25020597788251⟩ :=
  bank_checked 3943 5496 1189 u 1841424233922560 25020597788251
    (by decide) (by decide) (by decide) (by decide) pole_5496_1189

theorem bank_3961_5499_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3961,5499,1213,u⟩,1888787979829248,25457931418119⟩ :=
  bank_checked 3961 5499 1213 u 1888787979829248 25457931418119
    (by decide) (by decide) (by decide) (by decide) pole_5499_1213

theorem bank_3944_5500_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3944,5500,1189,u⟩,1842469115002880,25079250895001⟩ :=
  bank_checked 3944 5500 1189 u 1842469115002880 25079250895001
    (by decide) (by decide) (by decide) (by decide) pole_5500_1189

theorem bank_3963_5502_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3963,5502,1213,u⟩,1890924025610240,25502682687359⟩ :=
  bank_checked 3963 5502 1213 u 1890924025610240 25502682687359
    (by decide) (by decide) (by decide) (by decide) pole_5502_1213

theorem bank_3961_5504_1197 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3961,5504,1197,u⟩,1869808724869120,25269814668608⟩ :=
  bank_checked 3961 5504 1197 u 1869808724869120 25269814668608
    (by decide) (by decide) (by decide) (by decide) pole_5504_1197

theorem bank_3965_5506_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3965,5506,1213,u⟩,1893061344362496,25562434272925⟩ :=
  bank_checked 3965 5506 1213 u 1893061344362496 25562434272925
    (by decide) (by decide) (by decide) (by decide) pole_5506_1213

theorem bank_3956_5507_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3956,5507,1213,u⟩,1883453434626048,25577387039299⟩ :=
  bank_checked 3956 5507 1213 u 1883453434626048 25577387039299
    (by decide) (by decide) (by decide) (by decide) pole_5507_1213

theorem bank_3971_5507_1244 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3971,5507,1244,u⟩,1936184665702400,26084011577468⟩ :=
  bank_checked 3971 5507 1244 u 1936184665702400 26084011577468
    (by decide) (by decide) (by decide) (by decide) pole_5507_1244

theorem bank_3969_5507_1244 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3969,5507,1244,u⟩,1933998970634240,26084011577468⟩ :=
  bank_checked 3969 5507 1244 u 1933998970634240 26084011577468
    (by decide) (by decide) (by decide) (by decide) pole_5507_1244

theorem bank_3966_5507_1244 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3966,5507,1244,u⟩,1930722875801600,26084011577468⟩ :=
  bank_checked 3966 5507 1244 u 1930722875801600 26084011577468
    (by decide) (by decide) (by decide) (by decide) pole_5507_1244

end Research6970.Height2313.CommonBankRanks

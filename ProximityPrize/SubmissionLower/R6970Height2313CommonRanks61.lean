import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0600
import ProximityPrize.SubmissionLower.Z6969Pack0601
import ProximityPrize.SubmissionLower.Z6969Pack0602
import ProximityPrize.SubmissionLower.Z6969Pack0603

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

private theorem pole_5509_1213 :
    P1_7_1.groupedPoleMoment 5509 1213 ≤ 25607310424524 :=
  _root_.Research6969.PackedRanks.PackedRanks306To308.moment5509_1213

private theorem pole_5510_1244 :
    P1_7_1.groupedPoleMoment 5510 1244 ≤ 26129827888718 :=
  _root_.Research6969.PackedRanks.PackedRanks309To311.moment5510_1244

private theorem pole_5511_1213 :
    P1_7_1.groupedPoleMoment 5511 1213 ≤ 25637257621145 :=
  _root_.Research6969.PackedRanks.PackedRanks312To314.moment5511_1213

private theorem pole_5511_1217 :
    P1_7_1.groupedPoleMoment 5511 1217 ≤ 25703033668012 :=
  _root_.PoleAffine6970.certified 5511 1217 25703033668012 (by decide) (by decide +kernel)

private theorem pole_5512_1177 :
    P1_7_1.groupedPoleMoment 5512 1177 ≤ 25056506437126 :=
  _root_.PoleAffine6970.certified 5512 1177 25056506437126 (by decide) (by decide +kernel)

private theorem pole_5512_1189 :
    P1_7_1.groupedPoleMoment 5512 1189 ≤ 25255771038451 :=
  _root_.Research6969.PackedRanks.PackedRanks315To317.moment5512_1189

private theorem pole_5512_1205 :
    P1_7_1.groupedPoleMoment 5512 1205 ≤ 25520385136463 :=
  _root_.PoleAffine6970.certified 5512 1205 25520385136463 (by decide) (by decide +kernel)

private theorem pole_5512_1213 :
    P1_7_1.groupedPoleMoment 5512 1213 ≤ 25652240151764 :=
  _root_.Research6969.PackedRanks.PackedRanks315To317.moment5512_1213

private theorem pole_5513_1188 :
    P1_7_1.groupedPoleMoment 5513 1188 ≤ 25253930148456 :=
  _root_.PoleAffine6970.certified 5513 1188 25253930148456 (by decide) (by decide +kernel)

private theorem pole_5513_1189 :
    P1_7_1.groupedPoleMoment 5513 1189 ≤ 25270519066641 :=
  _root_.PoleAffine6970.certified 5513 1189 25270519066641 (by decide) (by decide +kernel)

theorem bank_3965_5509_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3965,5509,1213,u⟩,1893061344362496,25607310424524⟩ :=
  bank_checked 3965 5509 1213 u 1893061344362496 25607310424524
    (by decide) (by decide) (by decide) (by decide) pole_5509_1213

theorem bank_3965_5510_1244 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3965,5510,1244,u⟩,1929631496929280,26129827888718⟩ :=
  bank_checked 3965 5510 1244 u 1929631496929280 26129827888718
    (by decide) (by decide) (by decide) (by decide) pole_5510_1244

theorem bank_3960_5511_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3960,5511,1213,u⟩,1887720434302976,25637257621145⟩ :=
  bank_checked 3960 5511 1213 u 1887720434302976 25637257621145
    (by decide) (by decide) (by decide) (by decide) pole_5511_1213

theorem bank_3967_5511_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3967,5511,1213,u⟩,1895199936086016,25637257621145⟩ :=
  bank_checked 3967 5511 1213 u 1895199936086016 25637257621145
    (by decide) (by decide) (by decide) (by decide) pole_5511_1213

theorem bank_3969_5511_1217 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3969,5511,1217,u⟩,1902091514150912,25703033668012⟩ :=
  bank_checked 3969 5511 1217 u 1902091514150912 25703033668012
    (by decide) (by decide) (by decide) (by decide) pole_5511_1217

theorem bank_3950_5512_1177 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3950,5512,1177,u⟩,1834497685585920,25056506437126⟩ :=
  bank_checked 3950 5512 1177 u 1834497685585920 25056506437126
    (by decide) (by decide) (by decide) (by decide) pole_5512_1177

theorem bank_3959_5512_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3959,5512,1189,u⟩,1858179765370880,25255771038451⟩ :=
  bank_checked 3959 5512 1189 u 1858179765370880 25255771038451
    (by decide) (by decide) (by decide) (by decide) pole_5512_1189

theorem bank_3968_5512_1205 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3968,5512,1205,u⟩,1886752633257984,25520385136463⟩ :=
  bank_checked 3968 5512 1205 u 1886752633257984 25520385136463
    (by decide) (by decide) (by decide) (by decide) pole_5512_1205

theorem bank_3958_5512_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3958,5512,1213,u⟩,1885586297978880,25652240151764⟩ :=
  bank_checked 3958 5512 1213 u 1885586297978880 25652240151764
    (by decide) (by decide) (by decide) (by decide) pole_5512_1213

theorem bank_3967_5512_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3967,5512,1213,u⟩,1895199936086016,25652240151764⟩ :=
  bank_checked 3967 5512 1213 u 1895199936086016 25652240151764
    (by decide) (by decide) (by decide) (by decide) pole_5512_1213

theorem bank_3968_5512_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3968,5512,1213,u⟩,1896269709312000,25652240151764⟩ :=
  bank_checked 3968 5512 1213 u 1896269709312000 25652240151764
    (by decide) (by decide) (by decide) (by decide) pole_5512_1213

theorem bank_3952_5513_1188 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3952,5513,1188,u⟩,1849652950859776,25253930148456⟩ :=
  bank_checked 3952 5513 1188 u 1849652950859776 25253930148456
    (by decide) (by decide) (by decide) (by decide) pole_5513_1188

theorem bank_3953_5513_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3953,5513,1189,u⟩,1851887082536960,25270519066641⟩ :=
  bank_checked 3953 5513 1189 u 1851887082536960 25270519066641
    (by decide) (by decide) (by decide) (by decide) pole_5513_1189

end Research6970.Height2313.CommonBankRanks

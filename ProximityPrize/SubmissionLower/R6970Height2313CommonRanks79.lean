import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0628

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

private theorem pole_13955_3070 :
    P1_7_1.groupedPoleMoment 13955 3070 ≤ 1052683166434338 :=
  _root_.Research6969.PackedRanks.PackedRanks387To387.moment13955_3070

private theorem pole_13966_3086 :
    P1_7_1.groupedPoleMoment 13966 3086 ≤ 1059638678388221 :=
  _root_.PoleAffine6970.certified 13966 3086 1059638678388221 (by decide) (by decide +kernel)

private theorem pole_13986_3102 :
    P1_7_1.groupedPoleMoment 13986 3102 ≤ 1068827738108783 :=
  _root_.PoleAffine6970.certified 13986 3102 1068827738108783 (by decide) (by decide +kernel)

private theorem pole_14649_3223 :
    P1_7_1.groupedPoleMoment 14649 3223 ≤ 1278297696123811 :=
  _root_.PoleAffine6970.certified 14649 3223 1278297696123811 (by decide) (by decide +kernel)

private theorem pole_14650_3223 :
    P1_7_1.groupedPoleMoment 14650 3223 ≤ 1278578742564135 :=
  _root_.PoleAffine6970.certified 14650 3223 1278578742564135 (by decide) (by decide +kernel)

theorem bank_10011_13955_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10011,13955,3070,u⟩,30503388091777024,1052683166434338⟩ :=
  bank_checked 10011 13955 3070 u 30503388091777024 1052683166434338
    (by decide) (by decide) (by decide) (by decide) pole_13955_3070

theorem bank_10047_13966_3086 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10047,13966,3086,u⟩,30871306119413760,1059638678388221⟩ :=
  bank_checked 10047 13966 3086 u 30871306119413760 1059638678388221
    (by decide) (by decide) (by decide) (by decide) pole_13966_3086

theorem bank_10049_13986_3102 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10049,13986,3102,u⟩,31006604324503552,1068827738108783⟩ :=
  bank_checked 10049 13986 3102 u 31006604324503552 1068827738108783
    (by decide) (by decide) (by decide) (by decide) pole_13986_3102

theorem bank_10499_14649_3223 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10499,14649,3223,u⟩,35212191177113600,1278297696123811⟩ :=
  bank_checked 10499 14649 3223 u 35212191177113600 1278297696123811
    (by decide) (by decide) (by decide) (by decide) pole_14649_3223

theorem bank_10499_14650_3223 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10499,14650,3223,u⟩,35212191177113600,1278578742564135⟩ :=
  bank_checked 10499 14650 3223 u 35212191177113600 1278578742564135
    (by decide) (by decide) (by decide) (by decide) pole_14650_3223

end Research6970.Height2313.CommonBankRanks

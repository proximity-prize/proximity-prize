import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2313.OrdinaryCubicRanks

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

private theorem pole_2929_662 :
    P1_7_1.groupedPoleMoment 2929 662 ≤ 2090961110089 :=
  _root_.PoleAffine6970.certified 2929 662 2090961110089 (by decide) (by decide +kernel)

private theorem pole_4045_897 :
    P1_7_1.groupedPoleMoment 4045 897 ≤ 7488345307134 :=
  _root_.PoleAffine6970.certified 4045 897 7488345307134 (by decide) (by decide +kernel)

private theorem pole_4062_893 :
    P1_7_1.groupedPoleMoment 4062 893 ≤ 7563813743010 :=
  _root_.PoleAffine6970.certified 4062 893 7563813743010 (by decide) (by decide +kernel)

private theorem pole_4109_900 :
    P1_7_1.groupedPoleMoment 4109 900 ≤ 7897067162757 :=
  _root_.PoleAffine6970.certified 4109 900 7897067162757 (by decide) (by decide +kernel)

private theorem pole_4120_900 :
    P1_7_1.groupedPoleMoment 4120 900 ≤ 7965324963082 :=
  _root_.PoleAffine6970.certified 4120 900 7965324963082 (by decide) (by decide +kernel)

theorem bank_2964_4120_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2964,4120,900,u⟩,786631879557120,7965324963082⟩ :=
  bank_checked 2964 4120 900 u 786631879557120 7965324963082
    (by decide) (by decide) (by decide) (by decide) pole_4120_900

theorem bank_2955_4109_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2955,4109,900,u⟩,781296308060160,7897067162757⟩ :=
  bank_checked 2955 4109 900 u 781296308060160 7897067162757
    (by decide) (by decide) (by decide) (by decide) pole_4109_900

theorem bank_2924_4062_893 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2924,4062,893,u⟩,758553969950720,7563813743010⟩ :=
  bank_checked 2924 4062 893 u 758553969950720 7563813743010
    (by decide) (by decide) (by decide) (by decide) pole_4062_893

theorem bank_2913_4045_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2913,4045,897,u⟩,754736031072256,7488345307134⟩ :=
  bank_checked 2913 4045 897 u 754736031072256 7488345307134
    (by decide) (by decide) (by decide) (by decide) pole_4045_897

theorem bank_2111_2929_662 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2111,2929,662,u⟩,291407134720000,2090961110089⟩ :=
  bank_checked 2111 2929 662 u 291407134720000 2090961110089
    (by decide) (by decide) (by decide) (by decide) pole_2929_662

theorem bank_2914_4045_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2914,4045,897,u⟩,755316422868992,7488345307134⟩ :=
  bank_checked 2914 4045 897 u 755316422868992 7488345307134
    (by decide) (by decide) (by decide) (by decide) pole_4045_897

end Research6970.Height2313.OrdinaryCubicRanks

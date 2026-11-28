import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0626
import ProximityPrize.SubmissionLower.Z6969Pack0627

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

private theorem pole_13952_3078 :
    P1_7_1.groupedPoleMoment 13952 3078 ≤ 1054088797470548 :=
  _root_.PoleAffine6970.certified 13952 3078 1054088797470548 (by decide) (by decide +kernel)

private theorem pole_13952_3150 :
    P1_7_1.groupedPoleMoment 13952 3150 ≤ 1073212809809009 :=
  _root_.Research6969.PackedRanks.PackedRanks381To383.moment13952_3150

private theorem pole_13953_3010 :
    P1_7_1.groupedPoleMoment 13953 3010 ≤ 1036125345444439 :=
  _root_.Research6969.PackedRanks.PackedRanks381To383.moment13953_3010

private theorem pole_13953_3026 :
    P1_7_1.groupedPoleMoment 13953 3026 ≤ 1040421890790919 :=
  _root_.PoleAffine6970.certified 13953 3026 1040421890790919 (by decide) (by decide +kernel)

private theorem pole_13953_3042 :
    P1_7_1.groupedPoleMoment 13953 3042 ≤ 1044710637160035 :=
  _root_.PoleAffine6970.certified 13953 3042 1044710637160035 (by decide) (by decide +kernel)

private theorem pole_13953_3070 :
    P1_7_1.groupedPoleMoment 13953 3070 ≤ 1052197377228338 :=
  _root_.Research6969.PackedRanks.PackedRanks381To383.moment13953_3070

private theorem pole_13954_3010 :
    P1_7_1.groupedPoleMoment 13954 3010 ≤ 1036364370066239 :=
  _root_.Research6969.PackedRanks.PackedRanks384To386.moment13954_3010

private theorem pole_13954_3018 :
    P1_7_1.groupedPoleMoment 13954 3018 ≤ 1038514136880293 :=
  _root_.PoleAffine6970.certified 13954 3018 1038514136880293 (by decide) (by decide +kernel)

private theorem pole_13954_3070 :
    P1_7_1.groupedPoleMoment 13954 3070 ≤ 1052440252760428 :=
  _root_.Research6969.PackedRanks.PackedRanks384To386.moment13954_3070

private theorem pole_13955_3010 :
    P1_7_1.groupedPoleMoment 13955 3010 ≤ 1036603432174989 :=
  _root_.Research6969.PackedRanks.PackedRanks384To386.moment13955_3010

theorem bank_10049_13952_3078 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10049,13952,3078,u⟩,30824208543252480,1054088797470548⟩ :=
  bank_checked 10049 13952 3078 u 30824208543252480 1054088797470548
    (by decide) (by decide) (by decide) (by decide) pole_13952_3078

theorem bank_10053_13952_3150 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10053,13952,3150,u⟩,31397668750884864,1073212809809009⟩ :=
  bank_checked 10053 13952 3150 u 31397668750884864 1073212809809009
    (by decide) (by decide) (by decide) (by decide) pole_13952_3150

theorem bank_10008_13953_3010 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10008,13953,3010,u⟩,30028351888687104,1036125345444439⟩ :=
  bank_checked 10008 13953 3010 u 30028351888687104 1036125345444439
    (by decide) (by decide) (by decide) (by decide) pole_13953_3010

theorem bank_10031_13953_3010 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10031,13953,3010,u⟩,30182935399235584,1036125345444439⟩ :=
  bank_checked 10031 13953 3010 u 30182935399235584 1036125345444439
    (by decide) (by decide) (by decide) (by decide) pole_13953_3010

theorem bank_10042_13953_3026 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10042,13953,3026,u⟩,30379594832936960,1040421890790919⟩ :=
  bank_checked 10042 13953 3026 u 30379594832936960 1040421890790919
    (by decide) (by decide) (by decide) (by decide) pole_13953_3026

theorem bank_10044_13953_3042 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10044,13953,3042,u⟩,30515504591142912,1044710637160035⟩ :=
  bank_checked 10044 13953 3042 u 30515504591142912 1044710637160035
    (by decide) (by decide) (by decide) (by decide) pole_13953_3042

theorem bank_10001_13953_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10001,13953,3070,u⟩,30435188770340864,1052197377228338⟩ :=
  bank_checked 10001 13953 3070 u 30435188770340864 1052197377228338
    (by decide) (by decide) (by decide) (by decide) pole_13953_3070

theorem bank_10043_13953_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10043,13953,3070,u⟩,30722166910091264,1052197377228338⟩ :=
  bank_checked 10043 13953 3070 u 30722166910091264 1052197377228338
    (by decide) (by decide) (by decide) (by decide) pole_13953_3070

theorem bank_10005_13953_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10005,13953,3070,u⟩,30462458838384640,1052197377228338⟩ :=
  bank_checked 10005 13953 3070 u 30462458838384640 1052197377228338
    (by decide) (by decide) (by decide) (by decide) pole_13953_3070

theorem bank_10041_13953_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10041,13953,3070,u⟩,30708469082619904,1052197377228338⟩ :=
  bank_checked 10041 13953 3070 u 30708469082619904 1052197377228338
    (by decide) (by decide) (by decide) (by decide) pole_13953_3070

theorem bank_10032_13954_3010 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10032,13954,3010,u⟩,30189665893220352,1036364370066239⟩ :=
  bank_checked 10032 13954 3010 u 30189665893220352 1036364370066239
    (by decide) (by decide) (by decide) (by decide) pole_13954_3010

theorem bank_10041_13954_3018 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10041,13954,3018,u⟩,30311585010679808,1038514136880293⟩ :=
  bank_checked 10041 13954 3018 u 30311585010679808 1038514136880293
    (by decide) (by decide) (by decide) (by decide) pole_13954_3018

theorem bank_10016_13954_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10016,13954,3070,u⟩,30537517941653504,1052440252760428⟩ :=
  bank_checked 10016 13954 3070 u 30537517941653504 1052440252760428
    (by decide) (by decide) (by decide) (by decide) pole_13954_3070

theorem bank_10044_13954_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10044,13954,3070,u⟩,30729017031393280,1052440252760428⟩ :=
  bank_checked 10044 13954 3070 u 30729017031393280 1052440252760428
    (by decide) (by decide) (by decide) (by decide) pole_13954_3070

theorem bank_10008_13955_3010 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10008,13955,3010,u⟩,30028351888687104,1036603432174989⟩ :=
  bank_checked 10008 13955 3010 u 30028351888687104 1036603432174989
    (by decide) (by decide) (by decide) (by decide) pole_13955_3010

end Research6970.Height2313.CommonBankRanks

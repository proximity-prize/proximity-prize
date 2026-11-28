import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0623
import ProximityPrize.SubmissionLower.Z6969Pack0625

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

private theorem pole_13937_3086 :
    P1_7_1.groupedPoleMoment 13937 3086 ≤ 1052567864777801 :=
  _root_.PoleAffine6970.certified 13937 3086 1052567864777801 (by decide) (by decide +kernel)

private theorem pole_13946_3014 :
    P1_7_1.groupedPoleMoment 13946 3014 ≤ 1035526291565475 :=
  _root_.PoleAffine6970.certified 13946 3014 1035526291565475 (by decide) (by decide +kernel)

private theorem pole_13948_3070 :
    P1_7_1.groupedPoleMoment 13948 3070 ≤ 1050983571587703 :=
  _root_.Research6969.PackedRanks.PackedRanks375To377.moment13948_3070

private theorem pole_13948_3086 :
    P1_7_1.groupedPoleMoment 13948 3086 ≤ 1055246105378606 :=
  _root_.PoleAffine6970.certified 13948 3086 1055246105378606 (by decide) (by decide +kernel)

private theorem pole_13948_3150 :
    P1_7_1.groupedPoleMoment 13948 3150 ≤ 1072221490229155 :=
  _root_.Research6969.PackedRanks.PackedRanks375To377.moment13948_3150

private theorem pole_13950_3070 :
    P1_7_1.groupedPoleMoment 13950 3070 ≤ 1051468979452278 :=
  _root_.Research6969.PackedRanks.PackedRanks375To377.moment13950_3070

private theorem pole_13950_3078 :
    P1_7_1.groupedPoleMoment 13950 3078 ≤ 1053602214882697 :=
  _root_.PoleAffine6970.certified 13950 3078 1053602214882697 (by decide) (by decide +kernel)

private theorem pole_13950_3102 :
    P1_7_1.groupedPoleMoment 13950 3102 ≤ 1059990587953193 :=
  _root_.PoleAffine6970.certified 13950 3102 1059990587953193 (by decide) (by decide +kernel)

private theorem pole_13950_3150 :
    P1_7_1.groupedPoleMoment 13950 3150 ≤ 1072717072025530 :=
  _root_.Research6969.PackedRanks.PackedRanks378To380.moment13950_3150

private theorem pole_13952_3070 :
    P1_7_1.groupedPoleMoment 13952 3070 ≤ 1051954539834997 :=
  _root_.Research6969.PackedRanks.PackedRanks378To380.moment13952_3070

theorem bank_10000_13937_3086 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10000,13937,3086,u⟩,30548737977483264,1052567864777801⟩ :=
  bank_checked 10000 13937 3086 u 30548737977483264 1052567864777801
    (by decide) (by decide) (by decide) (by decide) pole_13937_3086

theorem bank_10000_13946_3014 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10000,13946,3014,u⟩,30005043269468160,1035526291565475⟩ :=
  bank_checked 10000 13946 3014 u 30005043269468160 1035526291565475
    (by decide) (by decide) (by decide) (by decide) pole_13946_3014

theorem bank_10008_13948_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10008,13948,3070,u⟩,30482919842381824,1050983571587703⟩ :=
  bank_checked 10008 13948 3070 u 30482919842381824 1050983571587703
    (by decide) (by decide) (by decide) (by decide) pole_13948_3070

theorem bank_10045_13948_3086 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10045,13948,3086,u⟩,30857543399768064,1055246105378606⟩ :=
  bank_checked 10045 13948 3086 u 30857543399768064 1055246105378606
    (by decide) (by decide) (by decide) (by decide) pole_13948_3086

theorem bank_10005_13948_3150 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10005,13948,3150,u⟩,31062458345717760,1072221490229155⟩ :=
  bank_checked 10005 13948 3150 u 31062458345717760 1072221490229155
    (by decide) (by decide) (by decide) (by decide) pole_13948_3150

theorem bank_10050_13948_3150 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10050,13948,3150,u⟩,31376662344499200,1072221490229155⟩ :=
  bank_checked 10050 13948 3150 u 31376662344499200 1072221490229155
    (by decide) (by decide) (by decide) (by decide) pole_13948_3150

theorem bank_10006_13950_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10006,13950,3070,u⟩,30469278368006144,1051468979452278⟩ :=
  bank_checked 10006 13950 3070 u 30469278368006144 1051468979452278
    (by decide) (by decide) (by decide) (by decide) pole_13950_3070

theorem bank_10039_13950_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10039,13950,3070,u⟩,30694774475325440,1051468979452278⟩ :=
  bank_checked 10039 13950 3070 u 30694774475325440 1051468979452278
    (by decide) (by decide) (by decide) (by decide) pole_13950_3070

theorem bank_10047_13950_3078 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10047,13950,3078,u⟩,30810471804174336,1053602214882697⟩ :=
  bank_checked 10047 13950 3078 u 30810471804174336 1053602214882697
    (by decide) (by decide) (by decide) (by decide) pole_13950_3078

theorem bank_10047_13950_3102 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10047,13950,3102,u⟩,30992780033523712,1059990587953193⟩ :=
  bank_checked 10047 13950 3102 u 30992780033523712 1059990587953193
    (by decide) (by decide) (by decide) (by decide) pole_13950_3102

theorem bank_10059_13950_3150 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10059,13950,3150,u⟩,31439703866081280,1072717072025530⟩ :=
  bank_checked 10059 13950 3150 u 31439703866081280 1072717072025530
    (by decide) (by decide) (by decide) (by decide) pole_13950_3150

theorem bank_10051_13950_3150 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10051,13950,3150,u⟩,31383663653945344,1072717072025530⟩ :=
  bank_checked 10051 13950 3150 u 31383663653945344 1072717072025530
    (by decide) (by decide) (by decide) (by decide) pole_13950_3150

theorem bank_10040_13952_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10040,13952,3070,u⟩,30701621376450560,1051954539834997⟩ :=
  bank_checked 10040 13952 3070 u 30701621376450560 1051954539834997
    (by decide) (by decide) (by decide) (by decide) pole_13952_3070

end Research6970.Height2313.CommonBankRanks

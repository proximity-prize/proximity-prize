import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0649

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

private theorem pole_3907_835 :
    P1_7_1.groupedPoleMoment 3907 835 ≤ 6333230515528 :=
  _root_.PoleAffine6970.certified 3907 835 6333230515528 (by decide) (by decide +kernel)

private theorem pole_3907_854 :
    P1_7_1.groupedPoleMoment 3907 854 ≤ 6445344460182 :=
  _root_.Research6969.PackedRanks.TerminalRanks72To75.moment3907_854

private theorem pole_3907_880 :
    P1_7_1.groupedPoleMoment 3907 880 ≤ 6597390577237 :=
  _root_.PoleAffine6970.certified 3907 880 6597390577237 (by decide) (by decide +kernel)

private theorem pole_3909_878 :
    P1_7_1.groupedPoleMoment 3909 878 ≤ 6596616429360 :=
  _root_.PoleAffine6970.certified 3909 878 6596616429360 (by decide) (by decide +kernel)

private theorem pole_3909_882 :
    P1_7_1.groupedPoleMoment 3909 882 ≤ 6619929415349 :=
  _root_.PoleAffine6970.certified 3909 882 6619929415349 (by decide) (by decide +kernel)

private theorem pole_3913_876 :
    P1_7_1.groupedPoleMoment 3913 876 ≤ 6606676994431 :=
  _root_.PoleAffine6970.certified 3913 876 6606676994431 (by decide) (by decide +kernel)

private theorem pole_3913_882 :
    P1_7_1.groupedPoleMoment 3913 882 ≤ 6641779624741 :=
  _root_.PoleAffine6970.certified 3913 882 6641779624741 (by decide) (by decide +kernel)

private theorem pole_3921_870 :
    P1_7_1.groupedPoleMoment 3921 870 ≤ 6614859312501 :=
  _root_.PoleAffine6970.certified 3921 870 6614859312501 (by decide) (by decide +kernel)

private theorem pole_3922_870 :
    P1_7_1.groupedPoleMoment 3922 870 ≤ 6620293810739 :=
  _root_.PoleAffine6970.certified 3922 870 6620293810739 (by decide) (by decide +kernel)

private theorem pole_3984_871 :
    P1_7_1.groupedPoleMoment 3984 871 ≤ 6969433801209 :=
  _root_.PoleAffine6970.certified 3984 871 6969433801209 (by decide) (by decide +kernel)

theorem bank_2800_3907_835 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2800,3907,835,u⟩,654158360739840,6333230515528⟩ :=
  bank_checked 2800 3907 835 u 654158360739840 6333230515528
    (by decide) (by decide) (by decide) (by decide) pole_3907_835

theorem bank_2810_3907_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2810,3907,854,u⟩,670792923217920,6445344460182⟩ :=
  bank_checked 2810 3907 854 u 670792923217920 6445344460182
    (by decide) (by decide) (by decide) (by decide) pole_3907_854

theorem bank_2811_3907_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2811,3907,854,u⟩,671327256576000,6445344460182⟩ :=
  bank_checked 2811 3907 854 u 671327256576000 6445344460182
    (by decide) (by decide) (by decide) (by decide) pole_3907_854

theorem bank_2816_3907_880 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2816,3907,880,u⟩,689515385585664,6597390577237⟩ :=
  bank_checked 2816 3907 880 u 689515385585664 6597390577237
    (by decide) (by decide) (by decide) (by decide) pole_3907_880

theorem bank_2816_3909_878 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2816,3909,878,u⟩,688328825110528,6596616429360⟩ :=
  bank_checked 2816 3909 878 u 688328825110528 6596616429360
    (by decide) (by decide) (by decide) (by decide) pole_3909_878

theorem bank_2816_3909_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2816,3909,882,u⟩,690700839813120,6619929415349⟩ :=
  bank_checked 2816 3909 882 u 690700839813120 6619929415349
    (by decide) (by decide) (by decide) (by decide) pole_3909_882

theorem bank_2821_3913_876 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2821,3913,876,u⟩,689878117122048,6606676994431⟩ :=
  bank_checked 2821 3913 876 u 689878117122048 6606676994431
    (by decide) (by decide) (by decide) (by decide) pole_3913_876

theorem bank_2821_3913_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2821,3913,882,u⟩,693453055590400,6641779624741⟩ :=
  bank_checked 2821 3913 882 u 693453055590400 6641779624741
    (by decide) (by decide) (by decide) (by decide) pole_3913_882

theorem bank_2825_3921_870 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2825,3921,870,u⟩,688474539950080,6614859312501⟩ :=
  bank_checked 2825 3921 870 u 688474539950080 6614859312501
    (by decide) (by decide) (by decide) (by decide) pole_3921_870

theorem bank_2825_3922_870 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2825,3922,870,u⟩,688474539950080,6620293810739⟩ :=
  bank_checked 2825 3922 870 u 688474539950080 6620293810739
    (by decide) (by decide) (by decide) (by decide) pole_3922_870

theorem bank_2860_3984_871 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2860,3984,871,u⟩,708336323395584,6969433801209⟩ :=
  bank_checked 2860 3984 871 u 708336323395584 6969433801209
    (by decide) (by decide) (by decide) (by decide) pole_3984_871

end Research6970.Height2313.CommonBankRanks

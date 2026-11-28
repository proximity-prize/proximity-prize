import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0595

section Pack_R6970Height2313CommonRanks45

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks45_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3839_854 :
    P1_7_1.groupedPoleMoment 3839 854 ≤ 6091074552402 :=
  _root_.PoleAffine6970.certified 3839 854 6091074552402 (by decide) (by decide +kernel)

private theorem pole_3841_854 :
    P1_7_1.groupedPoleMoment 3841 854 ≤ 6101300343282 :=
  _root_.PoleAffine6970.certified 3841 854 6101300343282 (by decide) (by decide +kernel)

private theorem pole_3842_830 :
    P1_7_1.groupedPoleMoment 3842 830 ≤ 5972384579105 :=
  _root_.PoleAffine6970.certified 3842 830 5972384579105 (by decide) (by decide +kernel)

private theorem pole_3842_854 :
    P1_7_1.groupedPoleMoment 3842 854 ≤ 6106417618032 :=
  _root_.PoleAffine6970.certified 3842 854 6106417618032 (by decide) (by decide +kernel)

private theorem pole_3852_866 :
    P1_7_1.groupedPoleMoment 3852 866 ≤ 6224865038545 :=
  _root_.Research6969.PackedRanks.PackedRanks276To278.moment3852_866

private theorem pole_3855_854 :
    P1_7_1.groupedPoleMoment 3855 854 ≤ 6173208282882 :=
  _root_.PoleAffine6970.certified 3855 854 6173208282882 (by decide) (by decide +kernel)

private theorem pole_3857_854 :
    P1_7_1.groupedPoleMoment 3857 854 ≤ 6183527699682 :=
  _root_.PoleAffine6970.certified 3857 854 6183527699682 (by decide) (by decide +kernel)

private theorem pole_3857_861 :
    P1_7_1.groupedPoleMoment 3857 861 ≤ 6222886282400 :=
  _root_.PoleAffine6970.certified 3857 861 6222886282400 (by decide) (by decide +kernel)

private theorem pole_3858_834 :
    P1_7_1.groupedPoleMoment 3858 834 ≤ 6075528370197 :=
  _root_.PoleAffine6970.certified 3858 834 6075528370197 (by decide) (by decide +kernel)

private theorem pole_3864_812 :
    P1_7_1.groupedPoleMoment 3864 812 ≤ 5979768862673 :=
  _root_.PoleAffine6970.certified 3864 812 5979768862673 (by decide) (by decide +kernel)

theorem bank_2766_3839_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2766,3839,854,u⟩,647504147251200,6091074552402⟩ :=
  pack_R6970Height2313CommonRanks45_bank_checked 2766 3839 854 u 647504147251200 6091074552402
    (by decide) (by decide) (by decide) (by decide) pole_3839_854

theorem bank_2767_3841_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2767,3841,854,u⟩,648028618752000,6101300343282⟩ :=
  pack_R6970Height2313CommonRanks45_bank_checked 2767 3841 854 u 648028618752000 6101300343282
    (by decide) (by decide) (by decide) (by decide) pole_3841_854

theorem bank_2754_3842_830 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2754,3842,830,u⟩,627492187013120,5972384579105⟩ :=
  pack_R6970Height2313CommonRanks45_bank_checked 2754 3842 830 u 627492187013120 5972384579105
    (by decide) (by decide) (by decide) (by decide) pole_3842_830

theorem bank_2768_3842_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2768,3842,854,u⟩,648553314385920,6106417618032⟩ :=
  pack_R6970Height2313CommonRanks45_bank_checked 2768 3842 854 u 648553314385920 6106417618032
    (by decide) (by decide) (by decide) (by decide) pole_3842_854

theorem bank_2777_3852_866 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2777,3852,866,u⟩,660231795507200,6224865038545⟩ :=
  pack_R6970Height2313CommonRanks45_bank_checked 2777 3852 866 u 660231795507200 6224865038545
    (by decide) (by decide) (by decide) (by decide) pole_3852_866

theorem bank_2777_3855_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2777,3855,854,u⟩,653285661081600,6173208282882⟩ :=
  pack_R6970Height2313CommonRanks45_bank_checked 2777 3855 854 u 653285661081600 6173208282882
    (by decide) (by decide) (by decide) (by decide) pole_3855_854

theorem bank_2778_3857_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2778,3857,854,u⟩,653812598046720,6183527699682⟩ :=
  pack_R6970Height2313CommonRanks45_bank_checked 2778 3857 854 u 653812598046720 6183527699682
    (by decide) (by decide) (by decide) (by decide) pole_3857_854

theorem bank_2779_3857_861 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2779,3857,861,u⟩,658403560521728,6222886282400⟩ :=
  pack_R6970Height2313CommonRanks45_bank_checked 2779 3857 861 u 658403560521728 6222886282400
    (by decide) (by decide) (by decide) (by decide) pole_3857_861

theorem bank_2776_3858_834 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2776,3858,834,u⟩,641102151680000,6075528370197⟩ :=
  pack_R6970Height2313CommonRanks45_bank_checked 2776 3858 834 u 641102151680000 6075528370197
    (by decide) (by decide) (by decide) (by decide) pole_3858_834

theorem bank_2777_3864_812 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2777,3864,812,u⟩,628650759421952,5979768862673⟩ :=
  pack_R6970Height2313CommonRanks45_bank_checked 2777 3864 812 u 628650759421952 5979768862673
    (by decide) (by decide) (by decide) (by decide) pole_3864_812

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks45

section Pack_R6970Height2313CommonRanks51

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks51_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3989_885 :
    P1_7_1.groupedPoleMoment 3989 885 ≤ 7085003902524 :=
  _root_.Research6969.PackedRanks.PackedRanks279To281.moment3989_885

private theorem pole_4001_866 :
    P1_7_1.groupedPoleMoment 4001 866 ≤ 7033975845920 :=
  _root_.PoleAffine6970.certified 4001 866 7033975845920 (by decide) (by decide +kernel)

private theorem pole_4021_882 :
    P1_7_1.groupedPoleMoment 4021 882 ≤ 7250467565269 :=
  _root_.PoleAffine6970.certified 4021 882 7250467565269 (by decide) (by decide +kernel)

private theorem pole_4041_897 :
    P1_7_1.groupedPoleMoment 4041 897 ≤ 7464523841124 :=
  _root_.PoleAffine6970.certified 4041 897 7464523841124 (by decide) (by decide +kernel)

private theorem pole_4044_900 :
    P1_7_1.groupedPoleMoment 4044 900 ≤ 7501830777122 :=
  _root_.PoleAffine6970.certified 4044 900 7501830777122 (by decide) (by decide +kernel)

private theorem pole_4045_897 :
    P1_7_1.groupedPoleMoment 4045 897 ≤ 7488345307134 :=
  _root_.PoleAffine6970.certified 4045 897 7488345307134 (by decide) (by decide +kernel)

private theorem pole_4062_893 :
    P1_7_1.groupedPoleMoment 4062 893 ≤ 7563813743010 :=
  _root_.PoleAffine6970.certified 4062 893 7563813743010 (by decide) (by decide +kernel)

private theorem pole_4066_890 :
    P1_7_1.groupedPoleMoment 4066 890 ≤ 7567966147450 :=
  _root_.PoleAffine6970.certified 4066 890 7567966147450 (by decide) (by decide +kernel)

private theorem pole_4102_896 :
    P1_7_1.groupedPoleMoment 4102 896 ≤ 7826642207395 :=
  _root_.PoleAffine6970.certified 4102 896 7826642207395 (by decide) (by decide +kernel)

private theorem pole_4103_870 :
    P1_7_1.groupedPoleMoment 4103 870 ≤ 7654838454885 :=
  _root_.PoleAffine6970.certified 4103 870 7654838454885 (by decide) (by decide +kernel)

theorem bank_2874_3989_885 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2874,3989,885,u⟩,724847903375360,7085003902524⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2874 3989 885 u 724847903375360 7085003902524
    (by decide) (by decide) (by decide) (by decide) pole_3989_885

theorem bank_2868_4001_866 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2868,4001,866,u⟩,709662672158720,7033975845920⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2868 4001 866 u 709662672158720 7033975845920
    (by decide) (by decide) (by decide) (by decide) pole_4001_866

theorem bank_2887_4021_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2887,4021,882,u⟩,730324645445632,7250467565269⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2887 4021 882 u 730324645445632 7250467565269
    (by decide) (by decide) (by decide) (by decide) pole_4021_882

theorem bank_2911_4041_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2911,4041,897,u⟩,753575953694720,7464523841124⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2911 4041 897 u 753575953694720 7464523841124
    (by decide) (by decide) (by decide) (by decide) pole_4041_897

theorem bank_2913_4044_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2913,4044,900,u⟩,756649935765504,7501830777122⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2913 4044 900 u 756649935765504 7501830777122
    (by decide) (by decide) (by decide) (by decide) pole_4044_900

theorem bank_2899_4045_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2899,4045,897,u⟩,746635263475712,7488345307134⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2899 4045 897 u 746635263475712 7488345307134
    (by decide) (by decide) (by decide) (by decide) pole_4045_897

theorem bank_2914_4045_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2914,4045,897,u⟩,755316422868992,7488345307134⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2914 4045 897 u 755316422868992 7488345307134
    (by decide) (by decide) (by decide) (by decide) pole_4045_897

theorem bank_2924_4062_893 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2924,4062,893,u⟩,758553969950720,7563813743010⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2924 4062 893 u 758553969950720 7563813743010
    (by decide) (by decide) (by decide) (by decide) pole_4062_893

theorem bank_2926_4066_890 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2926,4066,890,u⟩,757775095824384,7567966147450⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2926 4066 890 u 757775095824384 7567966147450
    (by decide) (by decide) (by decide) (by decide) pole_4066_890

theorem bank_2941_4102_896 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2941,4102,896,u⟩,770422526967808,7826642207395⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2941 4102 896 u 770422526967808 7826642207395
    (by decide) (by decide) (by decide) (by decide) pole_4102_896

theorem bank_2942_4102_896 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2942,4102,896,u⟩,771008974028800,7826642207395⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2942 4102 896 u 771008974028800 7826642207395
    (by decide) (by decide) (by decide) (by decide) pole_4102_896

theorem bank_2953_4102_896 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2953,4102,896,u⟩,777475411148800,7826642207395⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2953 4102 896 u 777475411148800 7826642207395
    (by decide) (by decide) (by decide) (by decide) pole_4102_896

theorem bank_2948_4103_870 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2948,4103,870,u⟩,757337177718784,7654838454885⟩ :=
  pack_R6970Height2313CommonRanks51_bank_checked 2948 4103 870 u 757337177718784 7654838454885
    (by decide) (by decide) (by decide) (by decide) pole_4103_870

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks51

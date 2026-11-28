import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.AlternateBanks

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

private theorem pole_3776_825 :
    P1_7_1.groupedPoleMoment 3776 825 ≤ 5621896547854 :=
  _root_.PoleAffine6970.certified 3776 825 5621896547854 (by decide) (by decide +kernel)

private theorem pole_3776_831 :
    P1_7_1.groupedPoleMoment 3776 831 ≤ 5653701255008 :=
  _root_.PoleAffine6970.certified 3776 831 5653701255008 (by decide) (by decide +kernel)

private theorem pole_3778_823 :
    P1_7_1.groupedPoleMoment 3778 823 ≤ 5620849169783 :=
  _root_.PoleAffine6970.certified 3778 823 5620849169783 (by decide) (by decide +kernel)

private theorem pole_3778_829 :
    P1_7_1.groupedPoleMoment 3778 829 ≤ 5652736585466 :=
  _root_.PoleAffine6970.certified 3778 829 5652736585466 (by decide) (by decide +kernel)

private theorem pole_3903_882 :
    P1_7_1.groupedPoleMoment 3903 882 ≤ 6587245977411 :=
  _root_.PoleAffine6970.certified 3903 882 6587245977411 (by decide) (by decide +kernel)

private theorem pole_3909_866 :
    P1_7_1.groupedPoleMoment 3909 866 ≤ 6526459954192 :=
  _root_.PoleAffine6970.certified 3909 866 6526459954192 (by decide) (by decide +kernel)

private theorem pole_4000_891 :
    P1_7_1.groupedPoleMoment 4000 891 ≤ 7185760147881 :=
  _root_.PoleAffine6970.certified 4000 891 7185760147881 (by decide) (by decide +kernel)

private theorem pole_4018_894 :
    P1_7_1.groupedPoleMoment 4018 894 ≤ 7309497647653 :=
  _root_.PoleAffine6970.certified 4018 894 7309497647653 (by decide) (by decide +kernel)

private theorem pole_4024_896 :
    P1_7_1.groupedPoleMoment 4024 896 ≤ 7357477638067 :=
  _root_.PoleAffine6970.certified 4024 896 7357477638067 (by decide) (by decide +kernel)

private theorem pole_4024_897 :
    P1_7_1.groupedPoleMoment 4024 897 ≤ 7363857928874 :=
  _root_.PoleAffine6970.certified 4024 897 7363857928874 (by decide) (by decide +kernel)

private theorem pole_4042_899 :
    P1_7_1.groupedPoleMoment 4042 899 ≤ 7483419204340 :=
  _root_.PoleAffine6970.certified 4042 899 7483419204340 (by decide) (by decide +kernel)

private theorem pole_4044_897 :
    P1_7_1.groupedPoleMoment 4044 897 ≤ 7482385097044 :=
  _root_.PoleAffine6970.certified 4044 897 7482385097044 (by decide) (by decide +kernel)

private theorem pole_4053_871 :
    P1_7_1.groupedPoleMoment 4053 871 ≤ 7365407792617 :=
  _root_.PoleAffine6970.certified 4053 871 7365407792617 (by decide) (by decide +kernel)

private theorem pole_4057_870 :
    P1_7_1.groupedPoleMoment 4057 870 ≤ 7382197498349 :=
  _root_.PoleAffine6970.certified 4057 870 7382197498349 (by decide) (by decide +kernel)

private theorem pole_4065_889 :
    P1_7_1.groupedPoleMoment 4065 889 ≤ 7555358193921 :=
  _root_.PoleAffine6970.certified 4065 889 7555358193921 (by decide) (by decide +kernel)

private theorem pole_4089_900 :
    P1_7_1.groupedPoleMoment 4089 900 ≤ 7773983507927 :=
  _root_.PoleAffine6970.certified 4089 900 7773983507927 (by decide) (by decide +kernel)

private theorem pole_4096_897 :
    P1_7_1.groupedPoleMoment 4096 897 ≤ 7796619583454 :=
  _root_.PoleAffine6970.certified 4096 897 7796619583454 (by decide) (by decide +kernel)

private theorem pole_4119_900 :
    P1_7_1.groupedPoleMoment 4119 900 ≤ 7959103188672 :=
  _root_.PoleAffine6970.certified 4119 900 7959103188672 (by decide) (by decide +kernel)

private theorem pole_4122_900 :
    P1_7_1.groupedPoleMoment 4122 900 ≤ 7977778435516 :=
  _root_.PoleAffine6970.certified 4122 900 7977778435516 (by decide) (by decide +kernel)

private theorem pole_4136_892 :
    P1_7_1.groupedPoleMoment 4136 892 ≤ 8009367556385 :=
  _root_.PoleAffine6970.certified 4136 892 8009367556385 (by decide) (by decide +kernel)

private theorem pole_4160_900 :
    P1_7_1.groupedPoleMoment 4160 900 ≤ 8216917752362 :=
  _root_.PoleAffine6970.certified 4160 900 8216917752362 (by decide) (by decide +kernel)

private theorem pole_4166_897 :
    P1_7_1.groupedPoleMoment 4166 897 ≤ 8233640579999 :=
  _root_.PoleAffine6970.certified 4166 897 8233640579999 (by decide) (by decide +kernel)

private theorem pole_4172_900 :
    P1_7_1.groupedPoleMoment 4172 900 ≤ 8293436172066 :=
  _root_.PoleAffine6970.certified 4172 900 8293436172066 (by decide) (by decide +kernel)

private theorem pole_4183_900 :
    P1_7_1.groupedPoleMoment 4183 900 ≤ 8364002353312 :=
  _root_.PoleAffine6970.certified 4183 900 8364002353312 (by decide) (by decide +kernel)

private theorem pole_4184_899 :
    P1_7_1.groupedPoleMoment 4184 899 ≤ 8363177779690 :=
  _root_.PoleAffine6970.certified 4184 899 8363177779690 (by decide) (by decide +kernel)

private theorem pole_4184_900 :
    P1_7_1.groupedPoleMoment 4184 900 ≤ 8370437628682 :=
  _root_.PoleAffine6970.certified 4184 900 8370437628682 (by decide) (by decide +kernel)

theorem bank_2719_3778_823 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2719,3778,823,u⟩,605873829314560,5620849169783⟩ :=
  bank_checked 2719 3778 823 u 605873829314560 5620849169783
    (by decide) (by decide) (by decide) (by decide) pole_3778_823

theorem bank_2908_4057_870 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2908,4057,870,u⟩,734563800449024,7382197498349⟩ :=
  bank_checked 2908 4057 870 u 734563800449024 7382197498349
    (by decide) (by decide) (by decide) (by decide) pole_4057_870

theorem bank_2917_4053_871 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2917,4053,871,u⟩,740304460185600,7365407792617⟩ :=
  bank_checked 2917 4053 871 u 740304460185600 7365407792617
    (by decide) (by decide) (by decide) (by decide) pole_4053_871

theorem bank_2718_3776_825 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2718,3776,825,u⟩,606494188109824,5621896547854⟩ :=
  bank_checked 2718 3776 825 u 606494188109824 5621896547854
    (by decide) (by decide) (by decide) (by decide) pole_3776_825

theorem bank_2720_3778_829 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2720,3778,829,u⟩,609731465707520,5652736585466⟩ :=
  bank_checked 2720 3778 829 u 609731465707520 5652736585466
    (by decide) (by decide) (by decide) (by decide) pole_3778_829

theorem bank_2719_3776_831 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2719,3776,831,u⟩,610346276487168,5653701255008⟩ :=
  bank_checked 2719 3776 831 u 610346276487168 5653701255008
    (by decide) (by decide) (by decide) (by decide) pole_3776_831

theorem bank_2816_3909_866 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2816,3909,866,u⟩,681185996177408,6526459954192⟩ :=
  bank_checked 2816 3909 866 u 681185996177408 6526459954192
    (by decide) (by decide) (by decide) (by decide) pole_3909_866

theorem bank_2895_4018_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2895,4018,894,u⟩,742441122529280,7309497647653⟩ :=
  bank_checked 2895 4018 894 u 742441122529280 7309497647653
    (by decide) (by decide) (by decide) (by decide) pole_4018_894

theorem bank_2894_4018_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2894,4018,894,u⟩,741866775511040,7309497647653⟩ :=
  bank_checked 2894 4018 894 u 741866775511040 7309497647653
    (by decide) (by decide) (by decide) (by decide) pole_4018_894

theorem bank_2898_4024_896 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2898,4024,896,u⟩,745427748782080,7357477638067⟩ :=
  bank_checked 2898 4024 896 u 745427748782080 7357477638067
    (by decide) (by decide) (by decide) (by decide) pole_4024_896

theorem bank_2899_4024_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2899,4024,897,u⟩,746635263475712,7363857928874⟩ :=
  bank_checked 2899 4024 897 u 746635263475712 7363857928874
    (by decide) (by decide) (by decide) (by decide) pole_4024_897

theorem bank_2882_4000_891 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2882,4000,891,u⟩,733122598010880,7185760147881⟩ :=
  bank_checked 2882 4000 891 u 733122598010880 7185760147881
    (by decide) (by decide) (by decide) (by decide) pole_4000_891

theorem bank_2899_4024_896 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2899,4024,896,u⟩,746004084686848,7357477638067⟩ :=
  bank_checked 2899 4024 896 u 746004084686848 7357477638067
    (by decide) (by decide) (by decide) (by decide) pole_4024_896

theorem bank_2941_4096_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2941,4096,897,u⟩,771075984588800,7796619583454⟩ :=
  bank_checked 2941 4096 897 u 771075984588800 7796619583454
    (by decide) (by decide) (by decide) (by decide) pole_4096_897

theorem bank_2997_4166_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2997,4166,897,u⟩,804309564915712,8233640579999⟩ :=
  bank_checked 2997 4166 897 u 804309564915712 8233640579999
    (by decide) (by decide) (by decide) (by decide) pole_4166_897

theorem bank_3002_4172_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3002,4172,900,u⟩,809370767327232,8293436172066⟩ :=
  bank_checked 3002 4172 900 u 809370767327232 8293436172066
    (by decide) (by decide) (by decide) (by decide) pole_4172_900

theorem bank_2976_4136_892 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2976,4136,892,u⟩,788395471667200,8009367556385⟩ :=
  bank_checked 2976 4136 892 u 788395471667200 8009367556385
    (by decide) (by decide) (by decide) (by decide) pole_4136_892

theorem bank_2913_4044_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2913,4044,897,u⟩,754736031072256,7482385097044⟩ :=
  bank_checked 2913 4044 897 u 754736031072256 7482385097044
    (by decide) (by decide) (by decide) (by decide) pole_4044_897

theorem bank_2924_4065_889 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2924,4065,889,u⟩,755969882849280,7555358193921⟩ :=
  bank_checked 2924 4065 889 u 755969882849280 7555358193921
    (by decide) (by decide) (by decide) (by decide) pole_4065_889

theorem bank_2965_4119_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2965,4119,900,u⟩,787225901793280,7959103188672⟩ :=
  bank_checked 2965 4119 900 u 787225901793280 7959103188672
    (by decide) (by decide) (by decide) (by decide) pole_4119_900

theorem bank_3001_4184_899 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3001,4184,899,u⟩,808082866176000,8363177779690⟩ :=
  bank_checked 3001 4184 899 u 808082866176000 8363177779690
    (by decide) (by decide) (by decide) (by decide) pole_4184_899

theorem bank_2912_4042_899 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2912,4042,899,u⟩,755431047168000,7483419204340⟩ :=
  bank_checked 2912 4042 899 u 755431047168000 7483419204340
    (by decide) (by decide) (by decide) (by decide) pole_4042_899

theorem bank_2983_4160_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2983,4160,900,u⟩,797958690832384,8216917752362⟩ :=
  bank_checked 2983 4160 900 u 797958690832384 8216917752362
    (by decide) (by decide) (by decide) (by decide) pole_4160_900

theorem bank_2954_4122_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2954,4122,900,u⟩,780704647741440,7977778435516⟩ :=
  bank_checked 2954 4122 900 u 780704647741440 7977778435516
    (by decide) (by decide) (by decide) (by decide) pole_4122_900

theorem bank_2944_4089_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2944,4089,900,u⟩,774801035100160,7773983507927⟩ :=
  bank_checked 2944 4089 900 u 774801035100160 7773983507927
    (by decide) (by decide) (by decide) (by decide) pole_4089_900

theorem bank_2814_3903_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2814,3903,882,u⟩,689601573814272,6587245977411⟩ :=
  bank_checked 2814 3903 882 u 689601573814272 6587245977411
    (by decide) (by decide) (by decide) (by decide) pole_3903_882

theorem bank_3002_4184_899 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3002,4184,899,u⟩,808685076480000,8363177779690⟩ :=
  bank_checked 3002 4184 899 u 808685076480000 8363177779690
    (by decide) (by decide) (by decide) (by decide) pole_4184_899

theorem bank_3003_4184_899 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3003,4184,899,u⟩,809287522713600,8363177779690⟩ :=
  bank_checked 3003 4184 899 u 809287522713600 8363177779690
    (by decide) (by decide) (by decide) (by decide) pole_4184_899

theorem bank_3003_4184_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3003,4184,900,u⟩,809973764849664,8370437628682⟩ :=
  bank_checked 3003 4184 900 u 809973764849664 8370437628682
    (by decide) (by decide) (by decide) (by decide) pole_4184_900

theorem bank_2999_4184_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2999,4184,900,u⟩,807563191910400,8370437628682⟩ :=
  bank_checked 2999 4184 900 u 807563191910400 8370437628682
    (by decide) (by decide) (by decide) (by decide) pole_4184_900

theorem bank_3003_4183_900 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3003,4183,900,u⟩,809973764849664,8364002353312⟩ :=
  bank_checked 3003 4183 900 u 809973764849664 8364002353312
    (by decide) (by decide) (by decide) (by decide) pole_4183_900

end Research6970.Height2313.Research6969.AlternateBanks

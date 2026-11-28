import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0641
import ProximityPrize.SubmissionLower.Z6969Pack0646

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

private theorem pole_3891_854 :
    P1_7_1.groupedPoleMoment 3891 854 ≤ 6360758671782 :=
  _root_.PoleAffine6970.certified 3891 854 6360758671782 (by decide) (by decide +kernel)

private theorem pole_3896_850 :
    P1_7_1.groupedPoleMoment 3896 850 ≤ 6363799590291 :=
  _root_.PoleAffine6970.certified 3896 850 6363799590291 (by decide) (by decide +kernel)

private theorem pole_3896_852 :
    P1_7_1.groupedPoleMoment 3896 852 ≤ 6375459527244 :=
  _root_.PoleAffine6970.certified 3896 852 6375459527244 (by decide) (by decide +kernel)

private theorem pole_3896_853 :
    P1_7_1.groupedPoleMoment 3896 853 ≤ 6381285980181 :=
  _root_.PoleAffine6970.certified 3896 853 6381285980181 (by decide) (by decide +kernel)

private theorem pole_3896_882 :
    P1_7_1.groupedPoleMoment 3896 882 ≤ 6549254417644 :=
  _root_.Research6969.PackedRanks.TerminalRanks56To59.moment3896_882

private theorem pole_3897_870 :
    P1_7_1.groupedPoleMoment 3897 870 ≤ 6485340504589 :=
  _root_.PoleAffine6970.certified 3897 870 6485340504589 (by decide) (by decide +kernel)

private theorem pole_3897_881 :
    P1_7_1.groupedPoleMoment 3897 881 ≤ 6548907208321 :=
  _root_.PoleAffine6970.certified 3897 881 6548907208321 (by decide) (by decide +kernel)

private theorem pole_3899_854 :
    P1_7_1.groupedPoleMoment 3899 854 ≤ 6402956544702 :=
  _root_.PoleAffine6970.certified 3899 854 6402956544702 (by decide) (by decide +kernel)

private theorem pole_3900_854 :
    P1_7_1.groupedPoleMoment 3900 854 ≤ 6408244632207 :=
  _root_.PoleAffine6970.certified 3900 854 6408244632207 (by decide) (by decide +kernel)

private theorem pole_3901_834 :
    P1_7_1.groupedPoleMoment 3901 834 ≤ 6296101689637 :=
  _root_.Research6969.PackedRanks.OrdRanks4To5.moment3901_834

theorem bank_2800_3891_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2800,3891,854,u⟩,665461916958720,6360758671782⟩ :=
  bank_checked 2800 3891 854 u 665461916958720 6360758671782
    (by decide) (by decide) (by decide) (by decide) pole_3891_854

theorem bank_2804_3896_850 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2804,3896,850,u⟩,665212455485440,6363799590291⟩ :=
  bank_checked 2804 3896 850 u 665212455485440 6363799590291
    (by decide) (by decide) (by decide) (by decide) pole_3896_850

theorem bank_2805_3896_852 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2805,3896,852,u⟩,666934584279040,6375459527244⟩ :=
  bank_checked 2805 3896 852 u 666934584279040 6375459527244
    (by decide) (by decide) (by decide) (by decide) pole_3896_852

theorem bank_2805_3896_853 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2805,3896,853,u⟩,667529745268736,6381285980181⟩ :=
  bank_checked 2805 3896 853 u 667529745268736 6381285980181
    (by decide) (by decide) (by decide) (by decide) pole_3896_853

theorem bank_2807_3896_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2807,3896,882,u⟩,685761434222592,6549254417644⟩ :=
  bank_checked 2807 3896 882 u 685761434222592 6549254417644
    (by decide) (by decide) (by decide) (by decide) pole_3896_882

theorem bank_2808_3897_870 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2808,3897,870,u⟩,679228649242624,6485340504589⟩ :=
  bank_checked 2808 3897 870 u 679228649242624 6485340504589
    (by decide) (by decide) (by decide) (by decide) pole_3897_870

theorem bank_2810_3897_881 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2810,3897,881,u⟩,686816268386304,6548907208321⟩ :=
  bank_checked 2810 3897 881 u 686816268386304 6548907208321
    (by decide) (by decide) (by decide) (by decide) pole_3897_881

theorem bank_2807_3899_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2807,3899,854,u⟩,669191267942400,6402956544702⟩ :=
  bank_checked 2807 3899 854 u 669191267942400 6402956544702
    (by decide) (by decide) (by decide) (by decide) pole_3899_854

theorem bank_2808_3900_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2808,3900,854,u⟩,669724928901120,6408244632207⟩ :=
  bank_checked 2808 3900 854 u 669724928901120 6408244632207
    (by decide) (by decide) (by decide) (by decide) pole_3900_854

theorem bank_2800_3901_834 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2800,3901,834,u⟩,653560508579840,6296101689637⟩ :=
  bank_checked 2800 3901 834 u 653560508579840 6296101689637
    (by decide) (by decide) (by decide) (by decide) pole_3901_834

end Research6970.Height2313.CommonBankRanks

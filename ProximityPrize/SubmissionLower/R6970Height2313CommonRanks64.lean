import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0604
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0606
import ProximityPrize.SubmissionLower.Z6969Pack0607
import ProximityPrize.SubmissionLower.Z6969Pack0608

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

private theorem pole_6692_1512 :
    P1_7_1.groupedPoleMoment 6692 1512 ≤ 56871238465897 :=
  _root_.Research6969.PackedRanks.PackedRanks318To320.moment6692_1512

private theorem pole_6694_1474 :
    P1_7_1.groupedPoleMoment 6694 1474 ≤ 55810706074581 :=
  _root_.Research6969.PackedRanks.PackedRanks321To323.moment6694_1474

private theorem pole_6694_1512 :
    P1_7_1.groupedPoleMoment 6694 1512 ≤ 56926029739529 :=
  _root_.Research6969.PackedRanks.PackedRanks321To323.moment6694_1512

private theorem pole_6695_1512 :
    P1_7_1.groupedPoleMoment 6695 1512 ≤ 56953438854149 :=
  _root_.Research6969.PackedRanks.PackedRanks324To326.moment6695_1512

private theorem pole_6696_1474 :
    P1_7_1.groupedPoleMoment 6696 1474 ≤ 55864419956306 :=
  _root_.Research6969.PackedRanks.PackedRanks324To326.moment6696_1474

private theorem pole_6696_1512 :
    P1_7_1.groupedPoleMoment 6696 1512 ≤ 56980856955989 :=
  _root_.Research6969.PackedRanks.PackedRanks327To329.moment6696_1512

private theorem pole_6697_1474 :
    P1_7_1.groupedPoleMoment 6697 1474 ≤ 55891290082931 :=
  _root_.Research6969.PackedRanks.PackedRanks327To329.moment6697_1474

private theorem pole_6697_1478 :
    P1_7_1.groupedPoleMoment 6697 1478 ≤ 56009326793616 :=
  _root_.PoleAffine6970.certified 6697 1478 56009326793616 (by decide) (by decide +kernel)

private theorem pole_6697_1512 :
    P1_7_1.groupedPoleMoment 6697 1512 ≤ 57008284046562 :=
  _root_.Research6969.PackedRanks.PackedRanks330To332.moment6697_1512

private theorem pole_6698_1445 :
    P1_7_1.groupedPoleMoment 6698 1445 ≤ 55058665830093 :=
  _root_.Research6969.PackedRanks.PackedRanks330To332.moment6698_1445

theorem bank_4808_6692_1512 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4808,6692,1512,u⟩,3445982427611136,56871238465897⟩ :=
  bank_checked 4808 6692 1512 u 3445982427611136 56871238465897
    (by decide) (by decide) (by decide) (by decide) pole_6692_1512

theorem bank_4802_6692_1512 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4802,6692,1512,u⟩,3436345657393152,56871238465897⟩ :=
  bank_checked 4802 6692 1512 u 3436345657393152 56871238465897
    (by decide) (by decide) (by decide) (by decide) pole_6692_1512

theorem bank_4816_6694_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4816,6694,1474,u⟩,3392736362496000,55810706074581⟩ :=
  bank_checked 4816 6694 1474 u 3392736362496000 55810706074581
    (by decide) (by decide) (by decide) (by decide) pole_6694_1474

theorem bank_4819_6694_1512 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4819,6694,1512,u⟩,3463686924009472,56926029739529⟩ :=
  bank_checked 4819 6694 1512 u 3463686924009472 56926029739529
    (by decide) (by decide) (by decide) (by decide) pole_6694_1512

theorem bank_4820_6695_1512 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4820,6695,1512,u⟩,3465298803425280,56953438854149⟩ :=
  bank_checked 4820 6695 1512 u 3465298803425280 56953438854149
    (by decide) (by decide) (by decide) (by decide) pole_6695_1512

theorem bank_4819_6696_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4819,6696,1474,u⟩,3397470270259200,55864419956306⟩ :=
  bank_checked 4819 6696 1474 u 3397470270259200 55864419956306
    (by decide) (by decide) (by decide) (by decide) pole_6696_1474

theorem bank_4828_6696_1512 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4828,6696,1512,u⟩,3478208117211136,56980856955989⟩ :=
  bank_checked 4828 6696 1512 u 3478208117211136 56980856955989
    (by decide) (by decide) (by decide) (by decide) pole_6696_1512

theorem bank_4819_6697_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4819,6697,1474,u⟩,3397470270259200,55891290082931⟩ :=
  bank_checked 4819 6697 1474 u 3397470270259200 55891290082931
    (by decide) (by decide) (by decide) (by decide) pole_6697_1474

theorem bank_4821_6697_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4821,6697,1474,u⟩,3400628142080000,55891290082931⟩ :=
  bank_checked 4821 6697 1474 u 3400628142080000 55891290082931
    (by decide) (by decide) (by decide) (by decide) pole_6697_1474

theorem bank_4815_6697_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4815,6697,1474,u⟩,3391159166566400,55891290082931⟩ :=
  bank_checked 4815 6697 1474 u 3391159166566400 55891290082931
    (by decide) (by decide) (by decide) (by decide) pole_6697_1474

theorem bank_4824_6697_1478 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4824,6697,1478,u⟩,3412388399022080,56009326793616⟩ :=
  bank_checked 4824 6697 1478 u 3412388399022080 56009326793616
    (by decide) (by decide) (by decide) (by decide) pole_6697_1478

theorem bank_4821_6697_1512 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4821,6697,1512,u⟩,3466911079464960,57008284046562⟩ :=
  bank_checked 4821 6697 1512 u 3466911079464960 57008284046562
    (by decide) (by decide) (by decide) (by decide) pole_6697_1512

theorem bank_4803_6698_1445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4803,6698,1445,u⟩,3321662161813504,55058665830093⟩ :=
  bank_checked 4803 6698 1445 u 3321662161813504 55058665830093
    (by decide) (by decide) (by decide) (by decide) pole_6698_1445

theorem bank_4811_6698_1445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4811,6698,1445,u⟩,3334049849933824,55058665830093⟩ :=
  bank_checked 4811 6698 1445 u 3334049849933824 55058665830093
    (by decide) (by decide) (by decide) (by decide) pole_6698_1445

end Research6970.Height2313.CommonBankRanks

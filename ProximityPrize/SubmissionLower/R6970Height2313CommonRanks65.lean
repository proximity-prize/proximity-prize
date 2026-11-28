import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0609

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

private theorem pole_6698_1446 :
    P1_7_1.groupedPoleMoment 6698 1446 ≤ 55088401876903 :=
  _root_.PoleAffine6970.certified 6698 1446 55088401876903 (by decide) (by decide +kernel)

private theorem pole_6698_1448 :
    P1_7_1.groupedPoleMoment 6698 1448 ≤ 55147852767819 :=
  _root_.PoleAffine6970.certified 6698 1448 55147852767819 (by decide) (by decide +kernel)

private theorem pole_6698_1461 :
    P1_7_1.groupedPoleMoment 6698 1461 ≤ 55533598470879 :=
  _root_.PoleAffine6970.certified 6698 1461 55533598470879 (by decide) (by decide +kernel)

private theorem pole_6698_1474 :
    P1_7_1.groupedPoleMoment 6698 1474 ≤ 55918169002031 :=
  _root_.Research6969.PackedRanks.PackedRanks333To335.moment6698_1474

private theorem pole_6701_1470 :
    P1_7_1.groupedPoleMoment 6701 1470 ≤ 55880476263803 :=
  _root_.PoleAffine6970.certified 6701 1470 55880476263803 (by decide) (by decide +kernel)

private theorem pole_6702_1445 :
    P1_7_1.groupedPoleMoment 6702 1445 ≤ 55164552586387 :=
  _root_.PoleAffine6970.certified 6702 1445 55164552586387 (by decide) (by decide +kernel)

private theorem pole_6706_1493 :
    P1_7_1.groupedPoleMoment 6706 1493 ≤ 56695740716730 :=
  _root_.PoleAffine6970.certified 6706 1493 56695740716730 (by decide) (by decide +kernel)

private theorem pole_6706_1512 :
    P1_7_1.groupedPoleMoment 6706 1512 ≤ 57255532604349 :=
  _root_.PoleAffine6970.certified 6706 1512 57255532604349 (by decide) (by decide +kernel)

private theorem pole_6710_1445 :
    P1_7_1.groupedPoleMoment 6710 1445 ≤ 55376741286063 :=
  _root_.PoleAffine6970.certified 6710 1445 55376741286063 (by decide) (by decide +kernel)

private theorem pole_6722_1512 :
    P1_7_1.groupedPoleMoment 6722 1512 ≤ 57696887074637 :=
  _root_.PoleAffine6970.certified 6722 1512 57696887074637 (by decide) (by decide +kernel)

theorem bank_4802_6698_1446 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4802,6698,1446,u⟩,3321866325852160,55088401876903⟩ :=
  bank_checked 4802 6698 1446 u 3321866325852160 55088401876903
    (by decide) (by decide) (by decide) (by decide) pole_6698_1446

theorem bank_4803_6698_1448 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4803,6698,1448,u⟩,3326916058152960,55147852767819⟩ :=
  bank_checked 4803 6698 1448 u 3326916058152960 55147852767819
    (by decide) (by decide) (by decide) (by decide) pole_6698_1448

theorem bank_4822_6698_1461 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4822,6698,1461,u⟩,3379359256412160,55533598470879⟩ :=
  bank_checked 4822 6698 1461 u 3379359256412160 55533598470879
    (by decide) (by decide) (by decide) (by decide) pole_6698_1461

theorem bank_4811_6698_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4811,6698,1474,u⟩,3384854249472000,55918169002031⟩ :=
  bank_checked 4811 6698 1474 u 3384854249472000 55918169002031
    (by decide) (by decide) (by decide) (by decide) pole_6698_1474

theorem bank_4809_6698_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4809,6698,1474,u⟩,3381704110899200,55918169002031⟩ :=
  bank_checked 4809 6698 1474 u 3381704110899200 55918169002031
    (by decide) (by decide) (by decide) (by decide) pole_6698_1474

theorem bank_4808_6698_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4808,6698,1474,u⟩,3380129621606400,55918169002031⟩ :=
  bank_checked 4808 6698 1474 u 3380129621606400 55918169002031
    (by decide) (by decide) (by decide) (by decide) pole_6698_1474

theorem bank_4823_6701_1470 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4823,6701,1470,u⟩,3396762661289984,55880476263803⟩ :=
  bank_checked 4823 6701 1470 u 3396762661289984 55880476263803
    (by decide) (by decide) (by decide) (by decide) pole_6701_1470

theorem bank_4805_6702_1445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4805,6702,1445,u⟩,3324756809482240,55164552586387⟩ :=
  bank_checked 4805 6702 1445 u 3324756809482240 55164552586387
    (by decide) (by decide) (by decide) (by decide) pole_6702_1445

theorem bank_4832_6706_1493 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4832,6706,1493,u⟩,3451435488116736,56695740716730⟩ :=
  bank_checked 4832 6706 1493 u 3451435488116736 56695740716730
    (by decide) (by decide) (by decide) (by decide) pole_6706_1493

theorem bank_4835_6706_1512 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4835,6706,1512,u⟩,3489524589527040,57255532604349⟩ :=
  bank_checked 4835 6706 1512 u 3489524589527040 57255532604349
    (by decide) (by decide) (by decide) (by decide) pole_6706_1512

theorem bank_4811_6710_1445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4811,6710,1445,u⟩,3334049849933824,55376741286063⟩ :=
  bank_checked 4811 6710 1445 u 3334049849933824 55376741286063
    (by decide) (by decide) (by decide) (by decide) pole_6710_1445

theorem bank_4846_6722_1512 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4846,6722,1512,u⟩,3507346883215360,57696887074637⟩ :=
  bank_checked 4846 6722 1512 u 3507346883215360 57696887074637
    (by decide) (by decide) (by decide) (by decide) pole_6722_1512

end Research6970.Height2313.CommonBankRanks

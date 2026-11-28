import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0594
import ProximityPrize.SubmissionLower.Z6969Pack0645

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

private theorem pole_3626_819 :
    P1_7_1.groupedPoleMoment 3626 819 ≤ 4905972788959 :=
  _root_.Research6969.PackedRanks.PackedRanks264To266.moment3626_819

private theorem pole_3627_783 :
    P1_7_1.groupedPoleMoment 3627 783 ≤ 4741611634368 :=
  _root_.Research6969.PackedRanks.PackedRanks264To266.moment3627_783

private theorem pole_3627_789 :
    P1_7_1.groupedPoleMoment 3627 789 ≤ 4769913188218 :=
  _root_.PoleAffine6970.certified 3627 789 4769913188218 (by decide) (by decide +kernel)

private theorem pole_3627_791 :
    P1_7_1.groupedPoleMoment 3627 791 ≤ 4779330614481 :=
  _root_.PoleAffine6970.certified 3627 791 4779330614481 (by decide) (by decide +kernel)

private theorem pole_3627_793 :
    P1_7_1.groupedPoleMoment 3627 793 ≤ 4788739883894 :=
  _root_.Research6969.PackedRanks.TerminalRanks48To51.moment3627_793

private theorem pole_3627_798 :
    P1_7_1.groupedPoleMoment 3627 798 ≤ 4812227595495 :=
  _root_.Research6969.PackedRanks.PackedRanks267To269.moment3627_798

private theorem pole_3627_819 :
    P1_7_1.groupedPoleMoment 3627 819 ≤ 4910333421859 :=
  _root_.Research6969.PackedRanks.PackedRanks267To269.moment3627_819

private theorem pole_3628_783 :
    P1_7_1.groupedPoleMoment 3628 783 ≤ 4745819470168 :=
  _root_.Research6969.PackedRanks.PackedRanks270To272.moment3628_783

private theorem pole_3628_787 :
    P1_7_1.groupedPoleMoment 3628 787 ≤ 4764712808711 :=
  _root_.PoleAffine6970.certified 3628 787 4764712808711 (by decide) (by decide +kernel)

private theorem pole_3628_791 :
    P1_7_1.groupedPoleMoment 3628 791 ≤ 4783573219221 :=
  _root_.PoleAffine6970.certified 3628 791 4783573219221 (by decide) (by decide +kernel)

theorem bank_2607_3626_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2607,3626,819,u⟩,549365140684800,4905972788959⟩ :=
  bank_checked 2607 3626 819 u 549365140684800 4905972788959
    (by decide) (by decide) (by decide) (by decide) pole_3626_819

theorem bank_2614_3626_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2614,3626,819,u⟩,552677752176640,4905972788959⟩ :=
  bank_checked 2614 3626 819 u 552677752176640 4905972788959
    (by decide) (by decide) (by decide) (by decide) pole_3626_819

theorem bank_2615_3626_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2615,3626,819,u⟩,553151842222080,4905972788959⟩ :=
  bank_checked 2615 3626 819 u 553151842222080 4905972788959
    (by decide) (by decide) (by decide) (by decide) pole_3626_819

theorem bank_2604_3627_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2604,3627,783,u⟩,529573399756800,4741611634368⟩ :=
  bank_checked 2604 3627 783 u 529573399756800 4741611634368
    (by decide) (by decide) (by decide) (by decide) pole_3627_783

theorem bank_2608_3627_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2608,3627,783,u⟩,531394314895360,4741611634368⟩ :=
  bank_checked 2608 3627 783 u 531394314895360 4741611634368
    (by decide) (by decide) (by decide) (by decide) pole_3627_783

theorem bank_2607_3627_789 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2607,3627,789,u⟩,534033714380800,4769913188218⟩ :=
  bank_checked 2607 3627 789 u 534033714380800 4769913188218
    (by decide) (by decide) (by decide) (by decide) pole_3627_789

theorem bank_2611_3627_791 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2611,3627,791,u⟩,536901863866368,4779330614481⟩ :=
  bank_checked 2611 3627 791 u 536901863866368 4779330614481
    (by decide) (by decide) (by decide) (by decide) pole_3627_791

theorem bank_2606_3627_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2606,3627,793,u⟩,535631510110208,4788739883894⟩ :=
  bank_checked 2606 3627 793 u 535631510110208 4788739883894
    (by decide) (by decide) (by decide) (by decide) pole_3627_793

theorem bank_2604_3627_798 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2604,3627,798,u⟩,537271175741440,4812227595495⟩ :=
  bank_checked 2604 3627 798 u 537271175741440 4812227595495
    (by decide) (by decide) (by decide) (by decide) pole_3627_798

theorem bank_2605_3627_798 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2605,3627,798,u⟩,537733229182976,4812227595495⟩ :=
  bank_checked 2605 3627 798 u 537733229182976 4812227595495
    (by decide) (by decide) (by decide) (by decide) pole_3627_798

theorem bank_2607_3627_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2607,3627,819,u⟩,549365140684800,4910333421859⟩ :=
  bank_checked 2607 3627 819 u 549365140684800 4910333421859
    (by decide) (by decide) (by decide) (by decide) pole_3627_819

theorem bank_2615_3627_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2615,3627,819,u⟩,553151842222080,4910333421859⟩ :=
  bank_checked 2615 3627 819 u 553151842222080 4910333421859
    (by decide) (by decide) (by decide) (by decide) pole_3627_819

theorem bank_2608_3627_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2608,3627,819,u⟩,549837726023680,4910333421859⟩ :=
  bank_checked 2608 3627 819 u 549837726023680 4910333421859
    (by decide) (by decide) (by decide) (by decide) pole_3627_819

theorem bank_2604_3627_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2604,3627,819,u⟩,547948674416640,4910333421859⟩ :=
  bank_checked 2604 3627 819 u 547948674416640 4910333421859
    (by decide) (by decide) (by decide) (by decide) pole_3627_819

theorem bank_2611_3627_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2611,3627,819,u⟩,551256771788800,4910333421859⟩ :=
  bank_checked 2611 3627 819 u 551256771788800 4910333421859
    (by decide) (by decide) (by decide) (by decide) pole_3627_819

theorem bank_2602_3628_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2602,3628,783,u⟩,528664175312896,4745819470168⟩ :=
  bank_checked 2602 3628 783 u 528664175312896 4745819470168
    (by decide) (by decide) (by decide) (by decide) pole_3628_783

theorem bank_2601_3628_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3628,783,u⟩,528209871372288,4745819470168⟩ :=
  bank_checked 2601 3628 783 u 528209871372288 4745819470168
    (by decide) (by decide) (by decide) (by decide) pole_3628_783

theorem bank_2606_3628_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2606,3628,783,u⟩,530483446284288,4745819470168⟩ :=
  bank_checked 2606 3628 783 u 530483446284288 4745819470168
    (by decide) (by decide) (by decide) (by decide) pole_3628_783

theorem bank_2607_3628_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2607,3628,783,u⟩,530938777829376,4745819470168⟩ :=
  bank_checked 2607 3628 783 u 530938777829376 4745819470168
    (by decide) (by decide) (by decide) (by decide) pole_3628_783

theorem bank_2602_3628_787 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2602,3628,787,u⟩,530719010455552,4764712808711⟩ :=
  bank_checked 2602 3628 787 u 530719010455552 4764712808711
    (by decide) (by decide) (by decide) (by decide) pole_3628_787

theorem bank_2610_3628_791 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2610,3628,791,u⟩,536441886081024,4783573219221⟩ :=
  bank_checked 2610 3628 791 u 536441886081024 4783573219221
    (by decide) (by decide) (by decide) (by decide) pole_3628_791

end Research6970.Height2313.CommonBankRanks

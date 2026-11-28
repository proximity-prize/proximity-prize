import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0641
import ProximityPrize.SubmissionLower.Z6969Pack0644

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

private theorem pole_3618_793 :
    P1_7_1.groupedPoleMoment 3618 793 ≤ 4750593761744 :=
  _root_.PoleAffine6970.certified 3618 793 4750593761744 (by decide) (by decide +kernel)

private theorem pole_3618_798 :
    P1_7_1.groupedPoleMoment 3618 798 ≤ 4773887316825 :=
  _root_.PoleAffine6970.certified 3618 798 4773887316825 (by decide) (by decide +kernel)

private theorem pole_3620_775 :
    P1_7_1.groupedPoleMoment 3620 775 ≤ 4674619806217 :=
  _root_.Research6969.PackedRanks.TerminalRanks36To39.moment3620_775

private theorem pole_3620_776 :
    P1_7_1.groupedPoleMoment 3620 776 ≤ 4679328083011 :=
  _root_.PoleAffine6970.certified 3620 776 4679328083011 (by decide) (by decide +kernel)

private theorem pole_3620_777 :
    P1_7_1.groupedPoleMoment 3620 777 ≤ 4684034271577 :=
  _root_.PoleAffine6970.certified 3620 777 4684034271577 (by decide) (by decide +kernel)

private theorem pole_3620_809 :
    P1_7_1.groupedPoleMoment 3620 809 ≤ 4833555006109 :=
  _root_.PoleAffine6970.certified 3620 809 4833555006109 (by decide) (by decide +kernel)

private theorem pole_3621_793 :
    P1_7_1.groupedPoleMoment 3621 793 ≤ 4763286079225 :=
  _root_.Research6969.PackedRanks.OrdRanks0To3.moment3621_793

private theorem pole_3621_819 :
    P1_7_1.groupedPoleMoment 3621 819 ≤ 4884209183309 :=
  _root_.Research6969.PackedRanks.OrdRanks4To5.moment3621_819

private theorem pole_3622_775 :
    P1_7_1.groupedPoleMoment 3622 775 ≤ 4682933013901 :=
  _root_.PoleAffine6970.certified 3622 775 4682933013901 (by decide) (by decide +kernel)

private theorem pole_3622_779 :
    P1_7_1.groupedPoleMoment 3622 779 ≤ 4701788394678 :=
  _root_.PoleAffine6970.certified 3622 779 4701788394678 (by decide) (by decide +kernel)

theorem bank_2605_3618_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2605,3618,793,u⟩,535171619618816,4750593761744⟩ :=
  bank_checked 2605 3618 793 u 535171619618816 4750593761744
    (by decide) (by decide) (by decide) (by decide) pole_3618_793

theorem bank_2606_3618_798 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2606,3618,798,u⟩,538195492077568,4773887316825⟩ :=
  bank_checked 2606 3618 798 u 538195492077568 4773887316825
    (by decide) (by decide) (by decide) (by decide) pole_3618_798

theorem bank_2604_3620_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2604,3620,775,u⟩,525443022192640,4674619806217⟩ :=
  bank_checked 2604 3620 775 u 525443022192640 4674619806217
    (by decide) (by decide) (by decide) (by decide) pole_3620_775

theorem bank_2597_3620_776 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2597,3620,776,u⟩,522804981923840,4679328083011⟩ :=
  bank_checked 2597 3620 776 u 522804981923840 4679328083011
    (by decide) (by decide) (by decide) (by decide) pole_3620_776

theorem bank_2604_3620_777 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2604,3620,777,u⟩,526477262323712,4684034271577⟩ :=
  bank_checked 2604 3620 777 u 526477262323712 4684034271577
    (by decide) (by decide) (by decide) (by decide) pole_3620_777

theorem bank_2609_3620_809 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2609,3620,809,u⟩,545216719749120,4833555006109⟩ :=
  bank_checked 2609 3620 809 u 545216719749120 4833555006109
    (by decide) (by decide) (by decide) (by decide) pole_3620_809

theorem bank_2607_3621_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2607,3621,793,u⟩,536091608743936,4763286079225⟩ :=
  bank_checked 2607 3621 793 u 536091608743936 4763286079225
    (by decide) (by decide) (by decide) (by decide) pole_3621_793

theorem bank_2609_3621_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2609,3621,819,u⟩,550310526320640,4884209183309⟩ :=
  bank_checked 2609 3621 819 u 550310526320640 4884209183309
    (by decide) (by decide) (by decide) (by decide) pole_3621_819

theorem bank_2600_3622_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2600,3622,775,u⟩,523640687820800,4682933013901⟩ :=
  bank_checked 2600 3622 775 u 523640687820800 4682933013901
    (by decide) (by decide) (by decide) (by decide) pole_3622_775

theorem bank_2597_3622_779 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2597,3622,779,u⟩,524345068748800,4701788394678⟩ :=
  bank_checked 2597 3622 779 u 524345068748800 4701788394678
    (by decide) (by decide) (by decide) (by decide) pole_3622_779

end Research6970.Height2313.CommonBankRanks

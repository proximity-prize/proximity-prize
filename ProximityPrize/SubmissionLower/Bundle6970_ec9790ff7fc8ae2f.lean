import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0642
import ProximityPrize.SubmissionLower.Z6969Pack0652
import ProximityPrize.SubmissionLower.Z6969Pack0592
import ProximityPrize.SubmissionLower.Z6969Pack0644
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0645
import ProximityPrize.SubmissionLower.Z6969Pack0650
import ProximityPrize.SubmissionLower.Z6969Pack0646
import ProximityPrize.SubmissionLower.Z6969Pack0647
import ProximityPrize.SubmissionLower.Z6969Pack0648

section Pack_R6970Height2313CommonRanks23

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks23_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2505_539 :
    P1_7_1.groupedPoleMoment 2505 539 ≤ 1077212992491 :=
  _root_.PoleAffine6970.certified 2505 539 1077212992491 (by decide) (by decide +kernel)

private theorem pole_2511_540 :
    P1_7_1.groupedPoleMoment 2511 540 ≤ 1087105140167 :=
  _root_.PoleAffine6970.certified 2511 540 1087105140167 (by decide) (by decide +kernel)

private theorem pole_2776_604 :
    P1_7_1.groupedPoleMoment 2776 604 ≤ 1638230896114 :=
  _root_.PoleAffine6970.certified 2776 604 1638230896114 (by decide) (by decide +kernel)

private theorem pole_2782_598 :
    P1_7_1.groupedPoleMoment 2782 598 ≤ 1636863891369 :=
  _root_.PoleAffine6970.certified 2782 598 1636863891369 (by decide) (by decide +kernel)

private theorem pole_2782_602 :
    P1_7_1.groupedPoleMoment 2782 602 ≤ 1645394621605 :=
  _root_.PoleAffine6970.certified 2782 602 1645394621605 (by decide) (by decide +kernel)

private theorem pole_2782_610 :
    P1_7_1.groupedPoleMoment 2782 610 ≤ 1662397981334 :=
  _root_.Research6969.PackedRanks.TerminalRanks12To15.moment2782_610

private theorem pole_2784_610 :
    P1_7_1.groupedPoleMoment 2784 610 ≤ 1666247886835 :=
  _root_.Research6969.PackedRanks.TerminalRanks16To19.moment2784_610

private theorem pole_2787_610 :
    P1_7_1.groupedPoleMoment 2787 610 ≤ 1672034111214 :=
  _root_.Research6969.PackedRanks.TerminalRanks16To19.moment2787_610

private theorem pole_2787_630 :
    P1_7_1.groupedPoleMoment 2787 630 ≤ 1714466862180 :=
  _root_.Research6969.PackedRanks.TerminalRanks16To19.moment2787_630

private theorem pole_2788_630 :
    P1_7_1.groupedPoleMoment 2788 630 ≤ 1716449496361 :=
  _root_.Research6969.PackedRanks.TerminalRanks16To19.moment2788_630

theorem bank_1796_2505_539 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1796,2505,539,u⟩,173636753817600,1077212992491⟩ :=
  pack_R6970Height2313CommonRanks23_bank_checked 1796 2505 539 u 173636753817600 1077212992491
    (by decide) (by decide) (by decide) (by decide) pole_2505_539

theorem bank_1800_2511_540 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨1800,2511,540,u⟩,174749067509760,1087105140167⟩ :=
  pack_R6970Height2313CommonRanks23_bank_checked 1800 2511 540 u 174749067509760 1087105140167
    (by decide) (by decide) (by decide) (by decide) pole_2511_540

theorem bank_2000_2776_604 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2000,2776,604,u⟩,240862397726720,1638230896114⟩ :=
  pack_R6970Height2313CommonRanks23_bank_checked 2000 2776 604 u 240862397726720 1638230896114
    (by decide) (by decide) (by decide) (by decide) pole_2776_604

theorem bank_2000_2782_598 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2000,2782,598,u⟩,239038181933056,1636863891369⟩ :=
  pack_R6970Height2313CommonRanks23_bank_checked 2000 2782 598 u 239038181933056 1636863891369
    (by decide) (by decide) (by decide) (by decide) pole_2782_598

theorem bank_2002_2782_602 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2002,2782,602,u⟩,240792766513152,1645394621605⟩ :=
  pack_R6970Height2313CommonRanks23_bank_checked 2002 2782 602 u 240792766513152 1645394621605
    (by decide) (by decide) (by decide) (by decide) pole_2782_602

theorem bank_2003_2782_610 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2003,2782,610,u⟩,243494574096384,1662397981334⟩ :=
  pack_R6970Height2313CommonRanks23_bank_checked 2003 2782 610 u 243494574096384 1662397981334
    (by decide) (by decide) (by decide) (by decide) pole_2782_610

theorem bank_2002_2784_610 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2002,2784,610,u⟩,243222605463552,1666247886835⟩ :=
  pack_R6970Height2313CommonRanks23_bank_checked 2002 2784 610 u 243222605463552 1666247886835
    (by decide) (by decide) (by decide) (by decide) pole_2784_610

theorem bank_2005_2784_610 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2005,2784,610,u⟩,244038991872000,1666247886835⟩ :=
  pack_R6970Height2313CommonRanks23_bank_checked 2005 2784 610 u 244038991872000 1666247886835
    (by decide) (by decide) (by decide) (by decide) pole_2784_610

theorem bank_2003_2787_610 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2003,2787,610,u⟩,243494574096384,1672034111214⟩ :=
  pack_R6970Height2313CommonRanks23_bank_checked 2003 2787 610 u 243494574096384 1672034111214
    (by decide) (by decide) (by decide) (by decide) pole_2787_610

theorem bank_2009_2787_630 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2009,2787,630,u⟩,251198456463360,1714466862180⟩ :=
  pack_R6970Height2313CommonRanks23_bank_checked 2009 2787 630 u 251198456463360 1714466862180
    (by decide) (by decide) (by decide) (by decide) pole_2787_630

theorem bank_2002_2788_630 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2002,2788,630,u⟩,249240464392192,1716449496361⟩ :=
  pack_R6970Height2313CommonRanks23_bank_checked 2002 2788 630 u 249240464392192 1716449496361
    (by decide) (by decide) (by decide) (by decide) pole_2788_630

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks23

section Pack_R6970Height2313CommonRanks39

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks39_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3622_793 :
    P1_7_1.groupedPoleMoment 3622 793 ≤ 4767521972754 :=
  _root_.PoleAffine6970.certified 3622 793 4767521972754 (by decide) (by decide +kernel)

private theorem pole_3623_775 :
    P1_7_1.groupedPoleMoment 3623 775 ≤ 4687093383477 :=
  _root_.Research6969.PackedRanks.TerminalRanks36To39.moment3623_775

private theorem pole_3623_793 :
    P1_7_1.groupedPoleMoment 3623 793 ≤ 4771760428124 :=
  _root_.Research6969.PackedRanks.TerminalRanks40To43.moment3623_793

private theorem pole_3623_795 :
    P1_7_1.groupedPoleMoment 3623 795 ≤ 4781126977761 :=
  _root_.PoleAffine6970.certified 3623 795 4781126977761 (by decide) (by decide +kernel)

private theorem pole_3623_801 :
    P1_7_1.groupedPoleMoment 3623 801 ≤ 4809178421847 :=
  _root_.PoleAffine6970.certified 3623 801 4809178421847 (by decide) (by decide +kernel)

private theorem pole_3623_802 :
    P1_7_1.groupedPoleMoment 3623 802 ≤ 4813846676377 :=
  _root_.PoleAffine6970.certified 3623 802 4813846676377 (by decide) (by decide +kernel)

private theorem pole_3623_818 :
    P1_7_1.groupedPoleMoment 3623 818 ≤ 4888271640312 :=
  _root_.PoleAffine6970.certified 3623 818 4888271640312 (by decide) (by decide +kernel)

private theorem pole_3623_819 :
    P1_7_1.groupedPoleMoment 3623 819 ≤ 4892906717079 :=
  _root_.Research6969.PackedRanks.PackedRanks258To260.moment3623_819

private theorem pole_3624_775 :
    P1_7_1.groupedPoleMoment 3624 775 ≤ 4691256264577 :=
  _root_.Research6969.PackedRanks.TerminalRanks40To43.moment3624_775

private theorem pole_3624_783 :
    P1_7_1.groupedPoleMoment 3624 783 ≤ 4729003348328 :=
  _root_.PoleAffine6970.certified 3624 783 4729003348328 (by decide) (by decide +kernel)

theorem bank_2601_3622_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3622,793,u⟩,533334139076608,4767521972754⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2601 3622 793 u 533334139076608 4767521972754
    (by decide) (by decide) (by decide) (by decide) pole_3622_793

theorem bank_2605_3623_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2605,3623,775,u⟩,525894114344960,4687093383477⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2605 3623 775 u 525894114344960 4687093383477
    (by decide) (by decide) (by decide) (by decide) pole_3623_775

theorem bank_2604_3623_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2604,3623,793,u⟩,534711937269760,4771760428124⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2604 3623 793 u 534711937269760 4771760428124
    (by decide) (by decide) (by decide) (by decide) pole_3623_793

theorem bank_2602_3623_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2602,3623,793,u⟩,533793196998656,4771760428124⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2602 3623 793 u 533793196998656 4771760428124
    (by decide) (by decide) (by decide) (by decide) pole_3623_793

theorem bank_2609_3623_795 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2609,3623,795,u⟩,538041673318400,4781126977761⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2609 3623 795 u 538041673318400 4781126977761
    (by decide) (by decide) (by decide) (by decide) pole_3623_795

theorem bank_2608_3623_801 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2608,3623,801,u⟩,540658700124160,4809178421847⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2608 3623 801 u 540658700124160 4809178421847
    (by decide) (by decide) (by decide) (by decide) pole_3623_801

theorem bank_2610_3623_802 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2610,3623,802,u⟩,542100642856960,4813846676377⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2610 3623 802 u 542100642856960 4813846676377
    (by decide) (by decide) (by decide) (by decide) pole_3623_802

theorem bank_2612_3623_818 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2612,3623,818,u⟩,551220579926016,4888271640312⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2612 3623 818 u 551220579926016 4888271640312
    (by decide) (by decide) (by decide) (by decide) pole_3623_818

theorem bank_2603_3623_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2603,3623,819,u⟩,547476948910080,4892906717079⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2603 3623 819 u 547476948910080 4892906717079
    (by decide) (by decide) (by decide) (by decide) pole_3623_819

theorem bank_2606_3623_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2606,3623,819,u⟩,548892770304000,4892906717079⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2606 3623 819 u 548892770304000 4892906717079
    (by decide) (by decide) (by decide) (by decide) pole_3623_819

theorem bank_2602_3623_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2602,3623,819,u⟩,547005438361600,4892906717079⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2602 3623 819 u 547005438361600 4892906717079
    (by decide) (by decide) (by decide) (by decide) pole_3623_819

theorem bank_2606_3624_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2606,3624,775,u⟩,526345409921024,4691256264577⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2606 3624 775 u 526345409921024 4691256264577
    (by decide) (by decide) (by decide) (by decide) pole_3624_775

theorem bank_2604_3624_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2604,3624,783,u⟩,529573399756800,4729003348328⟩ :=
  pack_R6970Height2313CommonRanks39_bank_checked 2604 3624 783 u 529573399756800 4729003348328
    (by decide) (by decide) (by decide) (by decide) pole_3624_783

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks39

section Pack_R6970Height2313CommonRanks40

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks40_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3624_793 :
    P1_7_1.groupedPoleMoment 3624 793 ≤ 4776001446129 :=
  _root_.Research6969.PackedRanks.TerminalRanks40To43.moment3624_793

private theorem pole_3624_819 :
    P1_7_1.groupedPoleMoment 3624 819 ≤ 4897259437389 :=
  _root_.Research6969.PackedRanks.TerminalRanks44To47.moment3624_819

private theorem pole_3625_783 :
    P1_7_1.groupedPoleMoment 3625 783 ≤ 4733203574232 :=
  _root_.Research6969.PackedRanks.PackedRanks261To263.moment3625_783

private theorem pole_3625_793 :
    P1_7_1.groupedPoleMoment 3625 793 ≤ 4780245027563 :=
  _root_.Research6969.PackedRanks.TerminalRanks44To47.moment3625_793

private theorem pole_3625_819 :
    P1_7_1.groupedPoleMoment 3625 819 ≤ 4901614794409 :=
  _root_.Research6969.PackedRanks.PackedRanks261To263.moment3625_819

private theorem pole_3626_781 :
    P1_7_1.groupedPoleMoment 3626 781 ≤ 4727964653217 :=
  _root_.PoleAffine6970.certified 3626 781 4727964653217 (by decide) (by decide +kernel)

private theorem pole_3626_791 :
    P1_7_1.groupedPoleMoment 3626 791 ≤ 4775090569881 :=
  _root_.PoleAffine6970.certified 3626 791 4775090569881 (by decide) (by decide +kernel)

private theorem pole_3626_793 :
    P1_7_1.groupedPoleMoment 3626 793 ≤ 4784491173220 :=
  _root_.Research6969.PackedRanks.TerminalRanks48To51.moment3626_793

private theorem pole_3626_798 :
    P1_7_1.groupedPoleMoment 3626 798 ≤ 4807957255301 :=
  _root_.Research6969.PackedRanks.PackedRanks264To266.moment3626_798

private theorem pole_3626_815 :
    P1_7_1.groupedPoleMoment 3626 815 ≤ 4887369630386 :=
  _root_.PoleAffine6970.certified 3626 815 4887369630386 (by decide) (by decide +kernel)

theorem bank_2603_3624_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2603,3624,793,u⟩,534252463063040,4776001446129⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2603 3624 793 u 534252463063040 4776001446129
    (by decide) (by decide) (by decide) (by decide) pole_3624_793

theorem bank_2613_3624_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2613,3624,819,u⟩,552203877089280,4897259437389⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2613 3624 819 u 552203877089280 4897259437389
    (by decide) (by decide) (by decide) (by decide) pole_3624_819

theorem bank_2608_3624_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2608,3624,819,u⟩,549837726023680,4897259437389⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2608 3624 819 u 549837726023680 4897259437389
    (by decide) (by decide) (by decide) (by decide) pole_3624_819

theorem bank_2605_3625_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2605,3625,783,u⟩,530028320260096,4733203574232⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2605 3625 783 u 530028320260096 4733203574232
    (by decide) (by decide) (by decide) (by decide) pole_3625_783

theorem bank_2608_3625_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2608,3625,793,u⟩,536551915520000,4780245027563⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2608 3625 793 u 536551915520000 4780245027563
    (by decide) (by decide) (by decide) (by decide) pole_3625_793

theorem bank_2603_3625_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2603,3625,793,u⟩,534252463063040,4780245027563⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2603 3625 793 u 534252463063040 4780245027563
    (by decide) (by decide) (by decide) (by decide) pole_3625_793

theorem bank_2606_3625_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2606,3625,793,u⟩,535631510110208,4780245027563⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2606 3625 793 u 535631510110208 4780245027563
    (by decide) (by decide) (by decide) (by decide) pole_3625_793

theorem bank_2612_3625_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2612,3625,819,u⟩,551730216960000,4901614794409⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2612 3625 819 u 551730216960000 4901614794409
    (by decide) (by decide) (by decide) (by decide) pole_3625_819

theorem bank_2603_3625_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2603,3625,819,u⟩,547476948910080,4901614794409⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2603 3625 819 u 547476948910080 4901614794409
    (by decide) (by decide) (by decide) (by decide) pole_3625_819

theorem bank_2604_3625_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2604,3625,819,u⟩,547948674416640,4901614794409⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2604 3625 819 u 547948674416640 4901614794409
    (by decide) (by decide) (by decide) (by decide) pole_3625_819

theorem bank_2614_3625_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2614,3625,819,u⟩,552677752176640,4901614794409⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2614 3625 819 u 552677752176640 4901614794409
    (by decide) (by decide) (by decide) (by decide) pole_3625_819

theorem bank_2605_3625_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2605,3625,819,u⟩,548420614881280,4901614794409⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2605 3625 819 u 548420614881280 4901614794409
    (by decide) (by decide) (by decide) (by decide) pole_3625_819

theorem bank_2607_3625_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2607,3625,819,u⟩,549365140684800,4901614794409⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2607 3625 819 u 549365140684800 4901614794409
    (by decide) (by decide) (by decide) (by decide) pole_3625_819

theorem bank_2600_3626_781 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2600,3626,781,u⟩,526728636923904,4727964653217⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2600 3626 781 u 526728636923904 4727964653217
    (by decide) (by decide) (by decide) (by decide) pole_3626_781

theorem bank_2600_3626_791 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2600,3626,791,u⟩,531853527220224,4775090569881⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2600 3626 791 u 531853527220224 4775090569881
    (by decide) (by decide) (by decide) (by decide) pole_3626_791

theorem bank_2607_3626_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2607,3626,793,u⟩,536091608743936,4784491173220⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2607 3626 793 u 536091608743936 4784491173220
    (by decide) (by decide) (by decide) (by decide) pole_3626_793

theorem bank_2609_3626_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2609,3626,793,u⟩,537012430438400,4784491173220⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2609 3626 793 u 537012430438400 4784491173220
    (by decide) (by decide) (by decide) (by decide) pole_3626_793

theorem bank_2606_3626_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2606,3626,793,u⟩,535631510110208,4784491173220⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2606 3626 793 u 535631510110208 4784491173220
    (by decide) (by decide) (by decide) (by decide) pole_3626_793

theorem bank_2609_3626_798 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2609,3626,798,u⟩,539583537479680,4807957255301⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2609 3626 798 u 539583537479680 4807957255301
    (by decide) (by decide) (by decide) (by decide) pole_3626_798

theorem bank_2614_3626_815 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2614,3626,815,u⟩,550633901916160,4887369630386⟩ :=
  pack_R6970Height2313CommonRanks40_bank_checked 2614 3626 815 u 550633901916160 4887369630386
    (by decide) (by decide) (by decide) (by decide) pole_3626_815

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks40

section Pack_R6970Height2313CommonRanks48

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks48_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3901_853 :
    P1_7_1.groupedPoleMoment 3901 853 ≤ 6407686561801 :=
  _root_.PoleAffine6970.certified 3901 853 6407686561801 (by decide) (by decide +kernel)

private theorem pole_3901_854 :
    P1_7_1.groupedPoleMoment 3901 854 ≤ 6413535689982 :=
  _root_.Research6969.PackedRanks.TerminalRanks56To59.moment3901_854

private theorem pole_3901_855 :
    P1_7_1.groupedPoleMoment 3901 855 ≤ 6419382474065 :=
  _root_.PoleAffine6970.certified 3901 855 6419382474065 (by decide) (by decide +kernel)

private theorem pole_3901_882 :
    P1_7_1.groupedPoleMoment 3901 882 ≤ 6576375970149 :=
  _root_.Research6969.PackedRanks.TerminalRanks60To63.moment3901_882

private theorem pole_3902_854 :
    P1_7_1.groupedPoleMoment 3902 854 ≤ 6418829718882 :=
  _root_.Research6969.PackedRanks.TerminalRanks60To63.moment3902_854

private theorem pole_3902_857 :
    P1_7_1.groupedPoleMoment 3902 857 ≤ 6436378078562 :=
  _root_.PoleAffine6970.certified 3902 857 6436378078562 (by decide) (by decide +kernel)

private theorem pole_3902_858 :
    P1_7_1.groupedPoleMoment 3902 858 ≤ 6442222859746 :=
  _root_.PoleAffine6970.certified 3902 858 6442222859746 (by decide) (by decide +kernel)

private theorem pole_3902_882 :
    P1_7_1.groupedPoleMoment 3902 882 ≤ 6581809445307 :=
  _root_.Research6969.PackedRanks.TerminalRanks60To63.moment3902_882

private theorem pole_3903_854 :
    P1_7_1.groupedPoleMoment 3903 854 ≤ 6424126719762 :=
  _root_.Research6969.PackedRanks.TerminalRanks64To67.moment3903_854

private theorem pole_3903_882 :
    P1_7_1.groupedPoleMoment 3903 882 ≤ 6587245977411 :=
  _root_.Research6969.PackedRanks.TerminalRanks64To67.moment3903_882

theorem bank_2809_3901_853 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2809,3901,853,u⟩,669661892444160,6407686561801⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2809 3901 853 u 669661892444160 6407686561801
    (by decide) (by decide) (by decide) (by decide) pole_3901_853

theorem bank_2809_3901_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2809,3901,854,u⟩,670258813992960,6413535689982⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2809 3901 854 u 670258813992960 6413535689982
    (by decide) (by decide) (by decide) (by decide) pole_3901_854

theorem bank_2809_3901_855 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2809,3901,855,u⟩,670855447183360,6419382474065⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2809 3901 855 u 670855447183360 6419382474065
    (by decide) (by decide) (by decide) (by decide) pole_3901_855

theorem bank_2805_3901_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2805,3901,882,u⟩,684666334740480,6576375970149⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2805 3901 882 u 684666334740480 6576375970149
    (by decide) (by decide) (by decide) (by decide) pole_3901_882

theorem bank_2802_3901_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2802,3901,882,u⟩,683025421565952,6576375970149⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2802 3901 882 u 683025421565952 6576375970149
    (by decide) (by decide) (by decide) (by decide) pole_3901_882

theorem bank_2809_3902_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2809,3902,854,u⟩,670258813992960,6418829718882⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2809 3902 854 u 670258813992960 6418829718882
    (by decide) (by decide) (by decide) (by decide) pole_3902_854

theorem bank_2802_3902_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2802,3902,854,u⟩,666526325145600,6418829718882⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2802 3902 854 u 666526325145600 6418829718882
    (by decide) (by decide) (by decide) (by decide) pole_3902_854

theorem bank_2804_3902_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2804,3902,854,u⟩,667591629864960,6418829718882⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2804 3902 854 u 667591629864960 6418829718882
    (by decide) (by decide) (by decide) (by decide) pole_3902_854

theorem bank_2809_3902_857 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2809,3902,857,u⟩,672047850586112,6436378078562⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2809 3902 857 u 672047850586112 6436378078562
    (by decide) (by decide) (by decide) (by decide) pole_3902_857

theorem bank_2810_3902_858 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2810,3902,858,u⟩,673179779465216,6442222859746⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2810 3902 858 u 673179779465216 6442222859746
    (by decide) (by decide) (by decide) (by decide) pole_3902_858

theorem bank_2814_3902_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2814,3902,882,u⟩,689601573814272,6581809445307⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2814 3902 882 u 689601573814272 6581809445307
    (by decide) (by decide) (by decide) (by decide) pole_3902_882

theorem bank_2809_3902_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2809,3902,882,u⟩,686857459597312,6581809445307⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2809 3902 882 u 686857459597312 6581809445307
    (by decide) (by decide) (by decide) (by decide) pole_3902_882

theorem bank_2803_3903_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2803,3903,854,u⟩,667058865438720,6424126719762⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2803 3903 854 u 667058865438720 6424126719762
    (by decide) (by decide) (by decide) (by decide) pole_3903_854

theorem bank_2806_3903_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2806,3903,882,u⟩,685213768744960,6587245977411⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2806 3903 882 u 685213768744960 6587245977411
    (by decide) (by decide) (by decide) (by decide) pole_3903_882

theorem bank_2809_3903_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2809,3903,882,u⟩,686857459597312,6587245977411⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2809 3903 882 u 686857459597312 6587245977411
    (by decide) (by decide) (by decide) (by decide) pole_3903_882

theorem bank_2805_3903_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2805,3903,882,u⟩,684666334740480,6587245977411⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2805 3903 882 u 684666334740480 6587245977411
    (by decide) (by decide) (by decide) (by decide) pole_3903_882

theorem bank_2814_3903_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2814,3903,882,u⟩,689601573814272,6587245977411⟩ :=
  pack_R6970Height2313CommonRanks48_bank_checked 2814 3903 882 u 689601573814272 6587245977411
    (by decide) (by decide) (by decide) (by decide) pole_3903_882

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks48

section Pack_R6970Height2313CommonRanks49

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.CommonBankRanks

private theorem pack_R6970Height2313CommonRanks49_bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_3904_854 :
    P1_7_1.groupedPoleMoment 3904 854 ≤ 6429426693477 :=
  _root_.PoleAffine6970.certified 3904 854 6429426693477 (by decide) (by decide +kernel)

private theorem pole_3905_854 :
    P1_7_1.groupedPoleMoment 3905 854 ≤ 6434729640882 :=
  _root_.Research6969.PackedRanks.TerminalRanks64To67.moment3905_854

private theorem pole_3905_855 :
    P1_7_1.groupedPoleMoment 3905 855 ≤ 6440596481529 :=
  _root_.PoleAffine6970.certified 3905 855 6440596481529 (by decide) (by decide +kernel)

private theorem pole_3905_870 :
    P1_7_1.groupedPoleMoment 3905 870 ≤ 6528319804485 :=
  _root_.PoleAffine6970.certified 3905 870 6528319804485 (by decide) (by decide +kernel)

private theorem pole_3905_878 :
    P1_7_1.groupedPoleMoment 3905 878 ≤ 6574894765364 :=
  _root_.PoleAffine6970.certified 3905 878 6574894765364 (by decide) (by decide +kernel)

private theorem pole_3905_880 :
    P1_7_1.groupedPoleMoment 3905 880 ≤ 6586515963428 :=
  _root_.PoleAffine6970.certified 3905 880 6586515963428 (by decide) (by decide +kernel)

private theorem pole_3905_882 :
    P1_7_1.groupedPoleMoment 3905 882 ≤ 6598128215989 :=
  _root_.Research6969.PackedRanks.TerminalRanks64To67.moment3905_882

private theorem pole_3906_854 :
    P1_7_1.groupedPoleMoment 3906 854 ≤ 6440035562832 :=
  _root_.Research6969.PackedRanks.TerminalRanks68To71.moment3906_854

private theorem pole_3906_862 :
    P1_7_1.groupedPoleMoment 3906 862 ≤ 6486944896419 :=
  _root_.PoleAffine6970.certified 3906 862 6486944896419 (by decide) (by decide +kernel)

private theorem pole_3906_882 :
    P1_7_1.groupedPoleMoment 3906 882 ≤ 6603573924229 :=
  _root_.Research6969.PackedRanks.TerminalRanks68To71.moment3906_882

theorem bank_2805_3904_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2805,3904,854,u⟩,668124618424320,6429426693477⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2805 3904 854 u 668124618424320 6429426693477
    (by decide) (by decide) (by decide) (by decide) pole_3904_854

theorem bank_2803_3904_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2803,3904,854,u⟩,667058865438720,6429426693477⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2803 3904 854 u 667058865438720 6429426693477
    (by decide) (by decide) (by decide) (by decide) pole_3904_854

theorem bank_2808_3905_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2808,3905,854,u⟩,669724928901120,6434729640882⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2808 3905 854 u 669724928901120 6434729640882
    (by decide) (by decide) (by decide) (by decide) pole_3905_854

theorem bank_2805_3905_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2805,3905,854,u⟩,668124618424320,6434729640882⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2805 3905 854 u 668124618424320 6434729640882
    (by decide) (by decide) (by decide) (by decide) pole_3905_854

theorem bank_2810_3905_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2810,3905,854,u⟩,670792923217920,6434729640882⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2810 3905 854 u 670792923217920 6434729640882
    (by decide) (by decide) (by decide) (by decide) pole_3905_854

theorem bank_2810_3905_855 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2810,3905,855,u⟩,671390068899840,6440596481529⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2810 3905 855 u 671390068899840 6440596481529
    (by decide) (by decide) (by decide) (by decide) pole_3905_855

theorem bank_2814_3905_870 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2814,3905,870,u⟩,682484369981440,6528319804485⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2814 3905 870 u 682484369981440 6528319804485
    (by decide) (by decide) (by decide) (by decide) pole_3905_870

theorem bank_2813_3905_878 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2813,3905,878,u⟩,686686358732800,6574894765364⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2813 3905 878 u 686686358732800 6574894765364
    (by decide) (by decide) (by decide) (by decide) pole_3905_878

theorem bank_2814_3905_880 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2814,3905,880,u⟩,688418147532800,6586515963428⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2814 3905 880 u 688418147532800 6586515963428
    (by decide) (by decide) (by decide) (by decide) pole_3905_880

theorem bank_2810_3905_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2810,3905,882,u⟩,687405819494400,6598128215989⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2810 3905 882 u 687405819494400 6598128215989
    (by decide) (by decide) (by decide) (by decide) pole_3905_882

theorem bank_2804_3905_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2804,3905,882,u⟩,684119132209152,6598128215989⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2804 3905 882 u 684119132209152 6598128215989
    (by decide) (by decide) (by decide) (by decide) pole_3905_882

theorem bank_2807_3905_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2807,3905,882,u⟩,685761434222592,6598128215989⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2807 3905 882 u 685761434222592 6598128215989
    (by decide) (by decide) (by decide) (by decide) pole_3905_882

theorem bank_2816_3905_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2816,3905,882,u⟩,690700839813120,6598128215989⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2816 3905 882 u 690700839813120 6598128215989
    (by decide) (by decide) (by decide) (by decide) pole_3905_882

theorem bank_2803_3905_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2803,3905,882,u⟩,683572161150976,6598128215989⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2803 3905 882 u 683572161150976 6598128215989
    (by decide) (by decide) (by decide) (by decide) pole_3905_882

theorem bank_2813_3905_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2813,3905,882,u⟩,689052288024576,6598128215989⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2813 3905 882 u 689052288024576 6598128215989
    (by decide) (by decide) (by decide) (by decide) pole_3905_882

theorem bank_2809_3905_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2809,3905,882,u⟩,686857459597312,6598128215989⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2809 3905 882 u 686857459597312 6598128215989
    (by decide) (by decide) (by decide) (by decide) pole_3905_882

theorem bank_2808_3906_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2808,3906,854,u⟩,669724928901120,6440035562832⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2808 3906 854 u 669724928901120 6440035562832
    (by decide) (by decide) (by decide) (by decide) pole_3906_854

theorem bank_2809_3906_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2809,3906,854,u⟩,670258813992960,6440035562832⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2809 3906 854 u 670258813992960 6440035562832
    (by decide) (by decide) (by decide) (by decide) pole_3906_854

theorem bank_2813_3906_862 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2813,3906,862,u⟩,677178014171136,6486944896419⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2813 3906 862 u 677178014171136 6486944896419
    (by decide) (by decide) (by decide) (by decide) pole_3906_862

theorem bank_2816_3906_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2816,3906,882,u⟩,690700839813120,6603573924229⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2816 3906 882 u 690700839813120 6603573924229
    (by decide) (by decide) (by decide) (by decide) pole_3906_882

theorem bank_2808_3906_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2808,3906,882,u⟩,686309331173376,6603573924229⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2808 3906 882 u 686309331173376 6603573924229
    (by decide) (by decide) (by decide) (by decide) pole_3906_882

theorem bank_2806_3906_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2806,3906,882,u⟩,685213768744960,6603573924229⟩ :=
  pack_R6970Height2313CommonRanks49_bank_checked 2806 3906 882 u 685213768744960 6603573924229
    (by decide) (by decide) (by decide) (by decide) pole_3906_882

end Research6970.Height2313.CommonBankRanks
end Pack_R6970Height2313CommonRanks49

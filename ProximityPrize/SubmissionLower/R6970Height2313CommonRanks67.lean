import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0609
import ProximityPrize.SubmissionLower.Z6969Pack0610

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

private theorem pole_7889_1750 :
    P1_7_1.groupedPoleMoment 7889 1750 ≤ 108261549619854 :=
  _root_.PoleAffine6970.certified 7889 1750 108261549619854 (by decide) (by decide +kernel)

private theorem pole_7906_1716 :
    P1_7_1.groupedPoleMoment 7906 1716 ≤ 107361107788084 :=
  _root_.PoleAffine6970.certified 7906 1716 107361107788084 (by decide) (by decide +kernel)

private theorem pole_7920_1750 :
    P1_7_1.groupedPoleMoment 7920 1750 ≤ 109637722514009 :=
  _root_.PoleAffine6970.certified 7920 1750 109637722514009 (by decide) (by decide +kernel)

private theorem pole_7922_1716 :
    P1_7_1.groupedPoleMoment 7922 1716 ≤ 108062050923124 :=
  _root_.PoleAffine6970.certified 7922 1716 108062050923124 (by decide) (by decide +kernel)

private theorem pole_7938_1716 :
    P1_7_1.groupedPoleMoment 7938 1716 ≤ 108766099493044 :=
  _root_.PoleAffine6970.certified 7938 1716 108766099493044 (by decide) (by decide +kernel)

private theorem pole_7943_1758 :
    P1_7_1.groupedPoleMoment 7943 1758 ≤ 111059997495708 :=
  _root_.PoleAffine6970.certified 7943 1758 111059997495708 (by decide) (by decide +kernel)

private theorem pole_7946_1796 :
    P1_7_1.groupedPoleMoment 7946 1796 ≤ 113058766636997 :=
  _root_.Research6969.PackedRanks.PackedRanks333To335.moment7946_1796

private theorem pole_7948_1796 :
    P1_7_1.groupedPoleMoment 7948 1796 ≤ 113150499898987 :=
  _root_.Research6969.PackedRanks.PackedRanks336To338.moment7948_1796

private theorem pole_7949_1719 :
    P1_7_1.groupedPoleMoment 7949 1719 ≤ 109400975585001 :=
  _root_.PoleAffine6970.certified 7949 1719 109400975585001 (by decide) (by decide +kernel)

private theorem pole_7950_1750 :
    P1_7_1.groupedPoleMoment 7950 1750 ≤ 110980791054694 :=
  _root_.Research6969.PackedRanks.PackedRanks336To338.moment7950_1750

theorem bank_5684_7889_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5684,7889,1750,u⟩,5601989923962880,108261549619854⟩ :=
  bank_checked 5684 7889 1750 u 5601989923962880 108261549619854
    (by decide) (by decide) (by decide) (by decide) pole_7889_1750

theorem bank_5672_7906_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5672,7906,1716,u⟩,5492986119454720,107361107788084⟩ :=
  bank_checked 5672 7906 1716 u 5492986119454720 107361107788084
    (by decide) (by decide) (by decide) (by decide) pole_7906_1716

theorem bank_5683_7906_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5683,7906,1716,u⟩,5516850487623680,107361107788084⟩ :=
  bank_checked 5683 7906 1716 u 5516850487623680 107361107788084
    (by decide) (by decide) (by decide) (by decide) pole_7906_1716

theorem bank_5701_7920_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5701,7920,1750,u⟩,5639585936441344,109637722514009⟩ :=
  bank_checked 5701 7920 1750 u 5639585936441344 109637722514009
    (by decide) (by decide) (by decide) (by decide) pole_7920_1750

theorem bank_5682_7922_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5682,7922,1716,u⟩,5514678749102080,108062050923124⟩ :=
  bank_checked 5682 7922 1716 u 5514678749102080 108062050923124
    (by decide) (by decide) (by decide) (by decide) pole_7922_1716

theorem bank_5693_7938_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5693,7938,1716,u⟩,5538592628408320,108766099493044⟩ :=
  bank_checked 5693 7938 1716 u 5538592628408320 108766099493044
    (by decide) (by decide) (by decide) (by decide) pole_7938_1716

theorem bank_5692_7938_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5692,7938,1716,u⟩,5536416388874240,108766099493044⟩ :=
  bank_checked 5692 7938 1716 u 5536416388874240 108766099493044
    (by decide) (by decide) (by decide) (by decide) pole_7938_1716

theorem bank_5726_7943_1758 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5726,7943,1758,u⟩,5714887980351488,111059997495708⟩ :=
  bank_checked 5726 7943 1758 u 5714887980351488 111059997495708
    (by decide) (by decide) (by decide) (by decide) pole_7943_1758

theorem bank_5701_7946_1796 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5701,7946,1796,u⟩,5751590126092288,113058766636997⟩ :=
  bank_checked 5701 7946 1796 u 5751590126092288 113058766636997
    (by decide) (by decide) (by decide) (by decide) pole_7946_1796

theorem bank_5731_7948_1796 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5731,7948,1796,u⟩,5819686050070528,113150499898987⟩ :=
  bank_checked 5731 7948 1796 u 5819686050070528 113150499898987
    (by decide) (by decide) (by decide) (by decide) pole_7948_1796

theorem bank_5703_7948_1796 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5703,7948,1796,u⟩,5756116664320000,113150499898987⟩ :=
  bank_checked 5703 7948 1796 u 5756116664320000 113150499898987
    (by decide) (by decide) (by decide) (by decide) pole_7948_1796

theorem bank_5710_7949_1719 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5710,7949,1719,u⟩,5583086713569280,109400975585001⟩ :=
  bank_checked 5710 7949 1719 u 5583086713569280 109400975585001
    (by decide) (by decide) (by decide) (by decide) pole_7949_1719

theorem bank_5717_7950_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5717,7950,1750,u⟩,5675091598508032,110980791054694⟩ :=
  bank_checked 5717 7950 1750 u 5675091598508032 110980791054694
    (by decide) (by decide) (by decide) (by decide) pole_7950_1750

end Research6970.Height2313.CommonBankRanks

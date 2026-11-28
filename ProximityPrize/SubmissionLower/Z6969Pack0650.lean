import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0642

set_option Elab.async false

-- Source: Research6969.TerminalRanks32To35
section Z6969Source0897
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks32To35
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3207_724 : P1_7_1.groupedPoleMoment 3207 724 ≤ 3001726552718 :=
  _root_.PoleAffine6970.certified 3207 724 3001726552718 (by decide) (by decide +kernel)

theorem moment3208_702 : P1_7_1.groupedPoleMoment 3208 702 ≤ 2933547980091 :=
  _root_.PoleAffine6970.certified 3208 702 2933547980091 (by decide) (by decide +kernel)

theorem moment3208_724 : P1_7_1.groupedPoleMoment 3208 724 ≤ 3004743122568 :=
  _root_.PoleAffine6970.certified 3208 724 3004743122568 (by decide) (by decide +kernel)

theorem moment3209_685 : P1_7_1.groupedPoleMoment 3209 685 ≤ 2880896350916 :=
  _root_.PoleAffine6970.certified 3209 685 2880896350916 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks32To35

namespace Research6969.PackedRanks.TerminalRanks32To35
open Research6969.TerminalAuxBanks
theorem rank32 (u:ℕ) : P3_7_1.BankOK (bank32 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank32 u).shape (by change 2*724≤2300;decide) (by change 2300+724≤3207+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*724) 724=6*377903408742400:=by decide
  change 6*P1_7_1.nodeRows (bank32 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank32 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*724) 724 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank32 u).shape=377903408742400; omega, moment3207_724,by change 3207<K1.p;decide⟩
theorem rank33 (u:ℕ) : P3_7_1.BankOK (bank33 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank33 u).shape (by change 2*702≤2300;decide) (by change 2300+702≤3208+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*702) 702=6*369170633195520:=by decide
  change 6*P1_7_1.nodeRows (bank33 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank33 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*702) 702 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank33 u).shape=369170633195520; omega, moment3208_702,by change 3208<K1.p;decide⟩
theorem rank34 (u:ℕ) : P3_7_1.BankOK (bank34 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank34 u).shape (by change 2*724≤2300;decide) (by change 2300+724≤3208+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*724) 724=6*377903408742400:=by decide
  change 6*P1_7_1.nodeRows (bank34 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank34 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*724) 724 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank34 u).shape=377903408742400; omega, moment3208_724,by change 3208<K1.p;decide⟩
theorem rank35 (u:ℕ) : P3_7_1.BankOK (bank35 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank35 u).shape (by change 2*685≤2300;decide) (by change 2300+685≤3209+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*685) 685=6*362345092874240:=by decide
  change 6*P1_7_1.nodeRows (bank35 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank35 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*685) 685 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank35 u).shape=362345092874240; omega, moment3209_685,by change 3209<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks32To35
end Z6969Source0897

-- Source: Research6969.TerminalRanks44To47
section Z6969Source0898
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks44To47
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3624_819 : P1_7_1.groupedPoleMoment 3624 819 ≤ 4897259437389 :=
  _root_.PoleAffine6970.certified 3624 819 4897259437389 (by decide) (by decide +kernel)

theorem moment3625_775 : P1_7_1.groupedPoleMoment 3625 775 ≤ 4695421657977 :=
  _root_.PoleAffine6970.certified 3625 775 4695421657977 (by decide) (by decide +kernel)

theorem moment3625_793 : P1_7_1.groupedPoleMoment 3625 793 ≤ 4780245027563 :=
  _root_.PoleAffine6970.certified 3625 793 4780245027563 (by decide) (by decide +kernel)

theorem moment3626_775 : P1_7_1.groupedPoleMoment 3626 775 ≤ 4699589564453 :=
  _root_.PoleAffine6970.certified 3626 775 4699589564453 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks44To47

namespace Research6969.PackedRanks.TerminalRanks44To47
open Research6969.TerminalAuxBanks
theorem rank44 (u:ℕ) : P3_7_1.BankOK (bank44 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank44 u).shape (by change 2*819≤2600;decide) (by change 2600+819≤3624+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*819) 819=6*546063062138880:=by decide
  change 6*P1_7_1.nodeRows (bank44 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank44 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*819) 819 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank44 u).shape=546063062138880; omega, moment3624_819,by change 3624<K1.p;decide⟩
theorem rank45 (u:ℕ) : P3_7_1.BankOK (bank45 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank45 u).shape (by change 2*775≤2600;decide) (by change 2600+775≤3625+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*775) 775=6*523640687820800:=by decide
  change 6*P1_7_1.nodeRows (bank45 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank45 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*775) 775 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank45 u).shape=523640687820800; omega, moment3625_775,by change 3625<K1.p;decide⟩
theorem rank46 (u:ℕ) : P3_7_1.BankOK (bank46 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank46 u).shape (by change 2*793≤2600;decide) (by change 2600+793≤3625+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*793) 793=6*532875289296896:=by decide
  change 6*P1_7_1.nodeRows (bank46 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank46 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*793) 793 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank46 u).shape=532875289296896; omega, moment3625_793,by change 3625<K1.p;decide⟩
theorem rank47 (u:ℕ) : P3_7_1.BankOK (bank47 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank47 u).shape (by change 2*775≤2600;decide) (by change 2600+775≤3626+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*775) 775=6*523640687820800:=by decide
  change 6*P1_7_1.nodeRows (bank47 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank47 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*775) 775 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank47 u).shape=523640687820800; omega, moment3626_775,by change 3626<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks44To47
end Z6969Source0898

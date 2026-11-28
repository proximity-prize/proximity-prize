import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0642

set_option Elab.async false

-- Source: Research6969.TerminalRanks28To31
section Z6969Source0886
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks28To31
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3206_702 : P1_7_1.groupedPoleMoment 3206 702 ≤ 2927665016684 :=
  _root_.PoleAffine6970.certified 3206 702 2927665016684 (by decide) (by decide +kernel)

theorem moment3206_724 : P1_7_1.groupedPoleMoment 3206 724 ≤ 2998712046218 :=
  _root_.PoleAffine6970.certified 3206 724 2998712046218 (by decide) (by decide +kernel)

theorem moment3207_685 : P1_7_1.groupedPoleMoment 3207 685 ≤ 2875125099115 :=
  _root_.PoleAffine6970.certified 3207 685 2875125099115 (by decide) (by decide +kernel)

theorem moment3207_702 : P1_7_1.groupedPoleMoment 3207 702 ≤ 2930605494152 :=
  _root_.PoleAffine6970.certified 3207 702 2930605494152 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks28To31

namespace Research6969.PackedRanks.TerminalRanks28To31
open Research6969.TerminalAuxBanks
theorem rank28 (u:ℕ) : P3_7_1.BankOK (bank28 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank28 u).shape (by change 2*702≤2300;decide) (by change 2300+702≤3206+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*702) 702=6*369170633195520:=by decide
  change 6*P1_7_1.nodeRows (bank28 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank28 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*702) 702 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank28 u).shape=369170633195520; omega, moment3206_702,by change 3206<K1.p;decide⟩
theorem rank29 (u:ℕ) : P3_7_1.BankOK (bank29 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank29 u).shape (by change 2*724≤2300;decide) (by change 2300+724≤3206+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*724) 724=6*377903408742400:=by decide
  change 6*P1_7_1.nodeRows (bank29 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank29 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*724) 724 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank29 u).shape=377903408742400; omega, moment3206_724,by change 3206<K1.p;decide⟩
theorem rank30 (u:ℕ) : P3_7_1.BankOK (bank30 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank30 u).shape (by change 2*685≤2300;decide) (by change 2300+685≤3207+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*685) 685=6*362345092874240:=by decide
  change 6*P1_7_1.nodeRows (bank30 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank30 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*685) 685 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank30 u).shape=362345092874240; omega, moment3207_685,by change 3207<K1.p;decide⟩
theorem rank31 (u:ℕ) : P3_7_1.BankOK (bank31 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank31 u).shape (by change 2*702≤2300;decide) (by change 2300+702≤3207+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*702) 702=6*369170633195520:=by decide
  change 6*P1_7_1.nodeRows (bank31 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank31 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*702) 702 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank31 u).shape=369170633195520; omega, moment3207_702,by change 3207<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks28To31
end Z6969Source0886

-- Source: Research6969.TerminalRanks36To39
section Z6969Source0887
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks36To39
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3209_702 : P1_7_1.groupedPoleMoment 3209 702 ≤ 2936492475204 :=
  _root_.PoleAffine6970.certified 3209 702 2936492475204 (by decide) (by decide +kernel)

theorem moment3209_724 : P1_7_1.groupedPoleMoment 3209 724 ≤ 3007761756493 :=
  _root_.PoleAffine6970.certified 3209 724 3007761756493 (by decide) (by decide +kernel)

theorem moment3620_775 : P1_7_1.groupedPoleMoment 3620 775 ≤ 4674619806217 :=
  _root_.PoleAffine6970.certified 3620 775 4674619806217 (by decide) (by decide +kernel)

theorem moment3623_775 : P1_7_1.groupedPoleMoment 3623 775 ≤ 4687093383477 :=
  _root_.PoleAffine6970.certified 3623 775 4687093383477 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks36To39

namespace Research6969.PackedRanks.TerminalRanks36To39
open Research6969.TerminalAuxBanks
theorem rank36 (u:ℕ) : P3_7_1.BankOK (bank36 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank36 u).shape (by change 2*702≤2300;decide) (by change 2300+702≤3209+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*702) 702=6*369170633195520:=by decide
  change 6*P1_7_1.nodeRows (bank36 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank36 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*702) 702 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank36 u).shape=369170633195520; omega, moment3209_702,by change 3209<K1.p;decide⟩
theorem rank37 (u:ℕ) : P3_7_1.BankOK (bank37 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank37 u).shape (by change 2*724≤2300;decide) (by change 2300+724≤3209+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*724) 724=6*377903408742400:=by decide
  change 6*P1_7_1.nodeRows (bank37 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank37 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*724) 724 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank37 u).shape=377903408742400; omega, moment3209_724,by change 3209<K1.p;decide⟩
theorem rank38 (u:ℕ) : P3_7_1.BankOK (bank38 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank38 u).shape (by change 2*775≤2600;decide) (by change 2600+775≤3620+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*775) 775=6*523640687820800:=by decide
  change 6*P1_7_1.nodeRows (bank38 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank38 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*775) 775 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank38 u).shape=523640687820800; omega, moment3620_775,by change 3620<K1.p;decide⟩
theorem rank39 (u:ℕ) : P3_7_1.BankOK (bank39 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank39 u).shape (by change 2*775≤2600;decide) (by change 2600+775≤3623+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*775) 775=6*523640687820800:=by decide
  change 6*P1_7_1.nodeRows (bank39 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank39 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*775) 775 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank39 u).shape=523640687820800; omega, moment3623_775,by change 3623<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks36To39
end Z6969Source0887

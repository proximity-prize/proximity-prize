import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0642

set_option Elab.async false

-- Source: Research6969.TerminalRanks48To51
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks48To51
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3626_793 : P1_7_1.groupedPoleMoment 3626 793 ≤ 4784491173220 :=
  _root_.PoleAffine6970.certified 3626 793 4784491173220 (by decide) (by decide +kernel)

theorem moment3627_754 : P1_7_1.groupedPoleMoment 3627 754 ≤ 4603752129931 :=
  _root_.PoleAffine6970.certified 3627 754 4603752129931 (by decide) (by decide +kernel)

theorem moment3627_775 : P1_7_1.groupedPoleMoment 3627 775 ≤ 4703759984781 :=
  _root_.PoleAffine6970.certified 3627 775 4703759984781 (by decide) (by decide +kernel)

theorem moment3627_793 : P1_7_1.groupedPoleMoment 3627 793 ≤ 4788739883894 :=
  _root_.PoleAffine6970.certified 3627 793 4788739883894 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks48To51

namespace Research6969.PackedRanks.TerminalRanks48To51
open Research6969.TerminalAuxBanks
theorem rank48 (u:ℕ) : P3_7_1.BankOK (bank48 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank48 u).shape (by change 2*793≤2600;decide) (by change 2600+793≤3626+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*793) 793=6*532875289296896:=by decide
  change 6*P1_7_1.nodeRows (bank48 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank48 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*793) 793 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank48 u).shape=532875289296896; omega, moment3626_793,by change 3626<K1.p;decide⟩
theorem rank49 (u:ℕ) : P3_7_1.BankOK (bank49 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank49 u).shape (by change 2*754≤2600;decide) (by change 2600+754≤3627+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*754) 754=6*512754163384320:=by decide
  change 6*P1_7_1.nodeRows (bank49 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank49 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*754) 754 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank49 u).shape=512754163384320; omega, moment3627_754,by change 3627<K1.p;decide⟩
theorem rank50 (u:ℕ) : P3_7_1.BankOK (bank50 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank50 u).shape (by change 2*775≤2600;decide) (by change 2600+775≤3627+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*775) 775=6*523640687820800:=by decide
  change 6*P1_7_1.nodeRows (bank50 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank50 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*775) 775 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank50 u).shape=523640687820800; omega, moment3627_775,by change 3627<K1.p;decide⟩
theorem rank51 (u:ℕ) : P3_7_1.BankOK (bank51 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank51 u).shape (by change 2*793≤2600;decide) (by change 2600+793≤3627+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*793) 793=6*532875289296896:=by decide
  change 6*P1_7_1.nodeRows (bank51 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank51 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*793) 793 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank51 u).shape=532875289296896; omega, moment3627_793,by change 3627<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks48To51

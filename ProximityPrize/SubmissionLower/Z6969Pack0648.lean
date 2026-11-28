import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0642

set_option Elab.async false

-- Source: Research6969.TerminalRanks68To71
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks68To71
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3906_834 : P1_7_1.groupedPoleMoment 3906 834 ≤ 6322097677837 :=
  _root_.PoleAffine6970.certified 3906 834 6322097677837 (by decide) (by decide +kernel)

theorem moment3906_854 : P1_7_1.groupedPoleMoment 3906 854 ≤ 6440035562832 :=
  _root_.PoleAffine6970.certified 3906 854 6440035562832 (by decide) (by decide +kernel)

theorem moment3906_882 : P1_7_1.groupedPoleMoment 3906 882 ≤ 6603573924229 :=
  _root_.PoleAffine6970.certified 3906 882 6603573924229 (by decide) (by decide +kernel)

theorem moment3907_834 : P1_7_1.groupedPoleMoment 3907 834 ≤ 6327305614587 :=
  _root_.PoleAffine6970.certified 3907 834 6327305614587 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks68To71

namespace Research6969.PackedRanks.TerminalRanks68To71
open Research6969.TerminalAuxBanks
theorem rank68 (u:ℕ) : P3_7_1.BankOK (bank68 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank68 u).shape (by change 2*834≤2800;decide) (by change 2800+834≤3906+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*834) 834=6*653560508579840:=by decide
  change 6*P1_7_1.nodeRows (bank68 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank68 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*834) 834 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank68 u).shape=653560508579840; omega, moment3906_834,by change 3906<K1.p;decide⟩
theorem rank69 (u:ℕ) : P3_7_1.BankOK (bank69 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank69 u).shape (by change 2*854≤2800;decide) (by change 2800+854≤3906+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*854) 854=6*665461916958720:=by decide
  change 6*P1_7_1.nodeRows (bank69 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank69 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*854) 854 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank69 u).shape=665461916958720; omega, moment3906_854,by change 3906<K1.p;decide⟩
theorem rank70 (u:ℕ) : P3_7_1.BankOK (bank70 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank70 u).shape (by change 2*882≤2800;decide) (by change 2800+882≤3906+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*882) 882=6*681932636815360:=by decide
  change 6*P1_7_1.nodeRows (bank70 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank70 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*882) 882 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank70 u).shape=681932636815360; omega, moment3906_882,by change 3906<K1.p;decide⟩
theorem rank71 (u:ℕ) : P3_7_1.BankOK (bank71 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank71 u).shape (by change 2*834≤2800;decide) (by change 2800+834≤3907+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*834) 834=6*653560508579840:=by decide
  change 6*P1_7_1.nodeRows (bank71 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank71 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*834) 834 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank71 u).shape=653560508579840; omega, moment3907_834,by change 3907<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks68To71

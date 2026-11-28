import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0642

set_option Elab.async false

-- Source: Research6969.TerminalRanks60To63
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks60To63
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3901_882 : P1_7_1.groupedPoleMoment 3901 882 ≤ 6576375970149 :=
  _root_.PoleAffine6970.certified 3901 882 6576375970149 (by decide) (by decide +kernel)

theorem moment3902_834 : P1_7_1.groupedPoleMoment 3902 834 ≤ 6301295063987 :=
  _root_.PoleAffine6970.certified 3902 834 6301295063987 (by decide) (by decide +kernel)

theorem moment3902_854 : P1_7_1.groupedPoleMoment 3902 854 ≤ 6418829718882 :=
  _root_.PoleAffine6970.certified 3902 854 6418829718882 (by decide) (by decide +kernel)

theorem moment3902_882 : P1_7_1.groupedPoleMoment 3902 882 ≤ 6581809445307 :=
  _root_.PoleAffine6970.certified 3902 882 6581809445307 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks60To63

namespace Research6969.PackedRanks.TerminalRanks60To63
open Research6969.TerminalAuxBanks
theorem rank60 (u:ℕ) : P3_7_1.BankOK (bank60 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank60 u).shape (by change 2*882≤2800;decide) (by change 2800+882≤3901+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*882) 882=6*681932636815360:=by decide
  change 6*P1_7_1.nodeRows (bank60 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank60 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*882) 882 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank60 u).shape=681932636815360; omega, moment3901_882,by change 3901<K1.p;decide⟩
theorem rank61 (u:ℕ) : P3_7_1.BankOK (bank61 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank61 u).shape (by change 2*834≤2800;decide) (by change 2800+834≤3902+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*834) 834=6*653560508579840:=by decide
  change 6*P1_7_1.nodeRows (bank61 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank61 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*834) 834 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank61 u).shape=653560508579840; omega, moment3902_834,by change 3902<K1.p;decide⟩
theorem rank62 (u:ℕ) : P3_7_1.BankOK (bank62 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank62 u).shape (by change 2*854≤2800;decide) (by change 2800+854≤3902+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*854) 854=6*665461916958720:=by decide
  change 6*P1_7_1.nodeRows (bank62 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank62 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*854) 854 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank62 u).shape=665461916958720; omega, moment3902_854,by change 3902<K1.p;decide⟩
theorem rank63 (u:ℕ) : P3_7_1.BankOK (bank63 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank63 u).shape (by change 2*882≤2800;decide) (by change 2800+882≤3902+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*882) 882=6*681932636815360:=by decide
  change 6*P1_7_1.nodeRows (bank63 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank63 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*882) 882 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank63 u).shape=681932636815360; omega, moment3902_882,by change 3902<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks60To63

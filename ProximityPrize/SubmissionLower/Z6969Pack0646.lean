import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0642

set_option Elab.async false

-- Source: Research6969.TerminalRanks56To59
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks56To59
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3896_812 : P1_7_1.groupedPoleMoment 3896 812 ≤ 6140432144913 :=
  _root_.PoleAffine6970.certified 3896 812 6140432144913 (by decide) (by decide +kernel)

theorem moment3896_854 : P1_7_1.groupedPoleMoment 3896 854 ≤ 6387110095257 :=
  _root_.PoleAffine6970.certified 3896 854 6387110095257 (by decide) (by decide +kernel)

theorem moment3896_882 : P1_7_1.groupedPoleMoment 3896 882 ≤ 6549254417644 :=
  _root_.PoleAffine6970.certified 3896 882 6549254417644 (by decide) (by decide +kernel)

theorem moment3901_854 : P1_7_1.groupedPoleMoment 3901 854 ≤ 6413535689982 :=
  _root_.PoleAffine6970.certified 3901 854 6413535689982 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks56To59

namespace Research6969.PackedRanks.TerminalRanks56To59
open Research6969.TerminalAuxBanks
theorem rank56 (u:ℕ) : P3_7_1.BankOK (bank56 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank56 u).shape (by change 2*812≤2800;decide) (by change 2800+812≤3896+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*812) 812=6*640331821875200:=by decide
  change 6*P1_7_1.nodeRows (bank56 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank56 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*812) 812 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank56 u).shape=640331821875200; omega, moment3896_812,by change 3896<K1.p;decide⟩
theorem rank57 (u:ℕ) : P3_7_1.BankOK (bank57 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank57 u).shape (by change 2*854≤2800;decide) (by change 2800+854≤3896+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*854) 854=6*665461916958720:=by decide
  change 6*P1_7_1.nodeRows (bank57 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank57 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*854) 854 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank57 u).shape=665461916958720; omega, moment3896_854,by change 3896<K1.p;decide⟩
theorem rank58 (u:ℕ) : P3_7_1.BankOK (bank58 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank58 u).shape (by change 2*882≤2800;decide) (by change 2800+882≤3896+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*882) 882=6*681932636815360:=by decide
  change 6*P1_7_1.nodeRows (bank58 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank58 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*882) 882 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank58 u).shape=681932636815360; omega, moment3896_882,by change 3896<K1.p;decide⟩
theorem rank59 (u:ℕ) : P3_7_1.BankOK (bank59 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank59 u).shape (by change 2*854≤2800;decide) (by change 2800+854≤3901+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*854) 854=6*665461916958720:=by decide
  change 6*P1_7_1.nodeRows (bank59 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank59 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*854) 854 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank59 u).shape=665461916958720; omega, moment3901_854,by change 3901<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks56To59

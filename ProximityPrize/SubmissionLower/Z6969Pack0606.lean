import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks324To326
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks324To326
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment6695_1474 : P1_7_1.groupedPoleMoment 6695 1474 ≤ 55837558620681 :=
  _root_.PoleAffine6970.certified 6695 1474 55837558620681 (by decide) (by decide +kernel)

theorem moment6695_1512 : P1_7_1.groupedPoleMoment 6695 1512 ≤ 56953438854149 :=
  _root_.PoleAffine6970.certified 6695 1512 56953438854149 (by decide) (by decide +kernel)

theorem moment6696_1474 : P1_7_1.groupedPoleMoment 6696 1474 ≤ 55864419956306 :=
  _root_.PoleAffine6970.certified 6696 1474 55864419956306 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks324To326

namespace Research6969.PackedRanks.PackedRanks324To326
open Research6969.TransitionBanks
theorem rank324 (u:ℕ) : P3_7_1.BankOK (bank324 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank324 u).shape (by change 2*1474≤4800;decide) (by change 4800+1474≤6695+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474=6*3367547627110400:=by decide
  change 6*P1_7_1.nodeRows (bank324 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank324 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank324 u).shape=3367547627110400; omega, moment6695_1474,by change 6695<K1.p;decide⟩
theorem rank325 (u:ℕ) : P3_7_1.BankOK (bank325 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank325 u).shape (by change 2*1512≤4800;decide) (by change 4800+1512≤6695+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1512) 1512=6*3433136573644800:=by decide
  change 6*P1_7_1.nodeRows (bank325 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank325 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1512) 1512 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank325 u).shape=3433136573644800; omega, moment6695_1512,by change 6695<K1.p;decide⟩
theorem rank326 (u:ℕ) : P3_7_1.BankOK (bank326 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank326 u).shape (by change 2*1474≤4800;decide) (by change 4800+1474≤6696+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474=6*3367547627110400:=by decide
  change 6*P1_7_1.nodeRows (bank326 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank326 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank326 u).shape=3367547627110400; omega, moment6696_1474,by change 6696<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks324To326

import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks333To335
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks333To335
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment6698_1474 : P1_7_1.groupedPoleMoment 6698 1474 ≤ 55918169002031 :=
  _root_.PoleAffine6970.certified 6698 1474 55918169002031 (by decide) (by decide +kernel)

theorem moment7835_1720 : P1_7_1.groupedPoleMoment 7835 1720 ≤ 104477286568219 :=
  _root_.PoleAffine6970.certified 7835 1720 104477286568219 (by decide) (by decide +kernel)

theorem moment7946_1796 : P1_7_1.groupedPoleMoment 7946 1796 ≤ 113058766636997 :=
  _root_.PoleAffine6970.certified 7946 1796 113058766636997 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks333To335

namespace Research6969.PackedRanks.PackedRanks333To335
open Research6969.TransitionBanks
theorem rank333 (u:ℕ) : P3_7_1.BankOK (bank333 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank333 u).shape (by change 2*1474≤4800;decide) (by change 4800+1474≤6698+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474=6*3367547627110400:=by decide
  change 6*P1_7_1.nodeRows (bank333 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank333 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank333 u).shape=3367547627110400; omega, moment6698_1474,by change 6698<K1.p;decide⟩
theorem rank334 (u:ℕ) : P3_7_1.BankOK (bank334 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank334 u).shape (by change 2*1720≤5620;decide) (by change 5620+1720≤7835+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5620-2*1720) 1720=6*5390441861611520:=by decide
  change 6*P1_7_1.nodeRows (bank334 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank334 u).shape=262144*P1_7_1_2.sixPerNode (5620-2*1720) 1720 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank334 u).shape=5390441861611520; omega, moment7835_1720,by change 7835<K1.p;decide⟩
theorem rank335 (u:ℕ) : P3_7_1.BankOK (bank335 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank335 u).shape (by change 2*1796≤5700;decide) (by change 5700+1796≤7946+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1796) 1796=6*5749327563587584:=by decide
  change 6*P1_7_1.nodeRows (bank335 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank335 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1796) 1796 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank335 u).shape=5749327563587584; omega, moment7946_1796,by change 7946<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks333To335

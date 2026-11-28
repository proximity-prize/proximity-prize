import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks327To329
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks327To329
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment6696_1512 : P1_7_1.groupedPoleMoment 6696 1512 ≤ 56980856955989 :=
  _root_.PoleAffine6970.certified 6696 1512 56980856955989 (by decide) (by decide +kernel)

theorem moment6697_1445 : P1_7_1.groupedPoleMoment 6697 1445 ≤ 55032215749682 :=
  _root_.PoleAffine6970.certified 6697 1445 55032215749682 (by decide) (by decide +kernel)

theorem moment6697_1474 : P1_7_1.groupedPoleMoment 6697 1474 ≤ 55891290082931 :=
  _root_.PoleAffine6970.certified 6697 1474 55891290082931 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks327To329

namespace Research6969.PackedRanks.PackedRanks327To329
open Research6969.TransitionBanks
theorem rank327 (u:ℕ) : P3_7_1.BankOK (bank327 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank327 u).shape (by change 2*1512≤4800;decide) (by change 4800+1512≤6696+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1512) 1512=6*3433136573644800:=by decide
  change 6*P1_7_1.nodeRows (bank327 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank327 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1512) 1512 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank327 u).shape=3433136573644800; omega, moment6696_1512,by change 6696<K1.p;decide⟩
theorem rank328 (u:ℕ) : P3_7_1.BankOK (bank328 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank328 u).shape (by change 2*1445≤4800;decide) (by change 4800+1445≤6697+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1445) 1445=6*3317023033262080:=by decide
  change 6*P1_7_1.nodeRows (bank328 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank328 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1445) 1445 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank328 u).shape=3317023033262080; omega, moment6697_1445,by change 6697<K1.p;decide⟩
theorem rank329 (u:ℕ) : P3_7_1.BankOK (bank329 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank329 u).shape (by change 2*1474≤4800;decide) (by change 4800+1474≤6697+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474=6*3367547627110400:=by decide
  change 6*P1_7_1.nodeRows (bank329 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank329 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank329 u).shape=3367547627110400; omega, moment6697_1474,by change 6697<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks327To329

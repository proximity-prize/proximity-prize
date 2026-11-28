import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks315To317
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks315To317
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment5512_1189 : P1_7_1.groupedPoleMoment 5512 1189 ≤ 25255771038451 :=
  _root_.PoleAffine6970.certified 5512 1189 25255771038451 (by decide) (by decide +kernel)

theorem moment5512_1213 : P1_7_1.groupedPoleMoment 5512 1213 ≤ 25652240151764 :=
  _root_.PoleAffine6970.certified 5512 1213 25652240151764 (by decide) (by decide +kernel)

theorem moment6690_1474 : P1_7_1.groupedPoleMoment 6690 1474 ≤ 55703383755931 :=
  _root_.PoleAffine6970.certified 6690 1474 55703383755931 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks315To317

namespace Research6969.PackedRanks.PackedRanks315To317
open Research6969.TransitionBanks
theorem rank315 (u:ℕ) : P3_7_1.BankOK (bank315 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank315 u).shape (by change 2*1189≤3950;decide) (by change 3950+1189≤5512+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3950-2*1189) 1189=6*1848744952463360:=by decide
  change 6*P1_7_1.nodeRows (bank315 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank315 u).shape=262144*P1_7_1_2.sixPerNode (3950-2*1189) 1189 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank315 u).shape=1848744952463360; omega, moment5512_1189,by change 5512<K1.p;decide⟩
theorem rank316 (u:ℕ) : P3_7_1.BankOK (bank316 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank316 u).shape (by change 2*1213≤3950;decide) (by change 3950+1213≤5512+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3950-2*1213) 1213=6*1877062482395136:=by decide
  change 6*P1_7_1.nodeRows (bank316 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank316 u).shape=262144*P1_7_1_2.sixPerNode (3950-2*1213) 1213 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank316 u).shape=1877062482395136; omega, moment5512_1213,by change 5512<K1.p;decide⟩
theorem rank317 (u:ℕ) : P3_7_1.BankOK (bank317 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank317 u).shape (by change 2*1474≤4800;decide) (by change 4800+1474≤6690+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474=6*3367547627110400:=by decide
  change 6*P1_7_1.nodeRows (bank317 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank317 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank317 u).shape=3367547627110400; omega, moment6690_1474,by change 6690<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks315To317

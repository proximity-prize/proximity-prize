import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks318To320
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks318To320
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment6690_1512 : P1_7_1.groupedPoleMoment 6690 1512 ≤ 56816483122989 :=
  _root_.PoleAffine6970.certified 6690 1512 56816483122989 (by decide) (by decide +kernel)

theorem moment6692_1474 : P1_7_1.groupedPoleMoment 6692 1474 ≤ 55757027345056 :=
  _root_.PoleAffine6970.certified 6692 1474 55757027345056 (by decide) (by decide +kernel)

theorem moment6692_1512 : P1_7_1.groupedPoleMoment 6692 1512 ≤ 56871238465897 :=
  _root_.PoleAffine6970.certified 6692 1512 56871238465897 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks318To320

namespace Research6969.PackedRanks.PackedRanks318To320
open Research6969.TransitionBanks
theorem rank318 (u:ℕ) : P3_7_1.BankOK (bank318 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank318 u).shape (by change 2*1512≤4800;decide) (by change 4800+1512≤6690+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1512) 1512=6*3433136573644800:=by decide
  change 6*P1_7_1.nodeRows (bank318 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank318 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1512) 1512 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank318 u).shape=3433136573644800; omega, moment6690_1512,by change 6690<K1.p;decide⟩
theorem rank319 (u:ℕ) : P3_7_1.BankOK (bank319 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank319 u).shape (by change 2*1474≤4800;decide) (by change 4800+1474≤6692+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474=6*3367547627110400:=by decide
  change 6*P1_7_1.nodeRows (bank319 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank319 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank319 u).shape=3367547627110400; omega, moment6692_1474,by change 6692<K1.p;decide⟩
theorem rank320 (u:ℕ) : P3_7_1.BankOK (bank320 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank320 u).shape (by change 2*1512≤4800;decide) (by change 4800+1512≤6692+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1512) 1512=6*3433136573644800:=by decide
  change 6*P1_7_1.nodeRows (bank320 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank320 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1512) 1512 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank320 u).shape=3433136573644800; omega, moment6692_1512,by change 6692<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks318To320

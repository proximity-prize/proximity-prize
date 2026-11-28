import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks354To356
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks354To356
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment9625_2174 : P1_7_1.groupedPoleMoment 9625 2174 ≤ 243221551977378 :=
  _root_.PoleAffine6970.certified 9625 2174 243221551977378 (by decide) (by decide +kernel)

theorem moment9626_2077 : P1_7_1.groupedPoleMoment 9626 2077 ≤ 234809190715807 :=
  _root_.PoleAffine6970.certified 9626 2077 234809190715807 (by decide) (by decide +kernel)

theorem moment9626_2118 : P1_7_1.groupedPoleMoment 9626 2118 ≤ 238415548481346 :=
  _root_.PoleAffine6970.certified 9626 2118 238415548481346 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks354To356

namespace Research6969.PackedRanks.PackedRanks354To356
open Research6969.TransitionBanks
theorem rank354 (u:ℕ) : P3_7_1.BankOK (bank354 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank354 u).shape (by change 2*2174≤6900;decide) (by change 6900+2174≤9625+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2174) 2174=6*10196763128627200:=by decide
  change 6*P1_7_1.nodeRows (bank354 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank354 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2174) 2174 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank354 u).shape=10196763128627200; omega, moment9625_2174,by change 9625<K1.p;decide⟩
theorem rank355 (u:ℕ) : P3_7_1.BankOK (bank355 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank355 u).shape (by change 2*2077≤6900;decide) (by change 6900+2077≤9626+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2077) 2077=6*9849424459857920:=by decide
  change 6*P1_7_1.nodeRows (bank355 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank355 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2077) 2077 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank355 u).shape=9849424459857920; omega, moment9626_2077,by change 9626<K1.p;decide⟩
theorem rank356 (u:ℕ) : P3_7_1.BankOK (bank356 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank356 u).shape (by change 2*2118≤6900;decide) (by change 6900+2118≤9626+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2118) 2118=6*9997036108906496:=by decide
  change 6*P1_7_1.nodeRows (bank356 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank356 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2118) 2118 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank356 u).shape=9997036108906496; omega, moment9626_2118,by change 9626<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks354To356

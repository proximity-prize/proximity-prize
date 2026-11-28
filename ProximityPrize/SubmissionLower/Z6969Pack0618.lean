import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks360To362
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks360To362
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment9628_2118 : P1_7_1.groupedPoleMoment 9628 2118 ≤ 238575106344005 :=
  _root_.PoleAffine6970.certified 9628 2118 238575106344005 (by decide) (by decide +kernel)

theorem moment9629_2077 : P1_7_1.groupedPoleMoment 9629 2077 ≤ 235044796335102 :=
  _root_.PoleAffine6970.certified 9629 2077 235044796335102 (by decide) (by decide +kernel)

theorem moment11575_2548 : P1_7_1.groupedPoleMoment 11575 2548 ≤ 498569901356632 :=
  _root_.PoleAffine6970.certified 11575 2548 498569901356632 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks360To362

namespace Research6969.PackedRanks.PackedRanks360To362
open Research6969.TransitionBanks
theorem rank360 (u:ℕ) : P3_7_1.BankOK (bank360 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank360 u).shape (by change 2*2118≤6900;decide) (by change 6900+2118≤9628+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2118) 2118=6*9997036108906496:=by decide
  change 6*P1_7_1.nodeRows (bank360 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank360 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2118) 2118 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank360 u).shape=9997036108906496; omega, moment9628_2118,by change 9628<K1.p;decide⟩
theorem rank361 (u:ℕ) : P3_7_1.BankOK (bank361 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank361 u).shape (by change 2*2077≤6900;decide) (by change 6900+2077≤9629+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2077) 2077=6*9849424459857920:=by decide
  change 6*P1_7_1.nodeRows (bank361 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank361 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2077) 2077 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank361 u).shape=9849424459857920; omega, moment9629_2077,by change 9629<K1.p;decide⟩
theorem rank362 (u:ℕ) : P3_7_1.BankOK (bank362 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank362 u).shape (by change 2*2548≤8300;decide) (by change 8300+2548≤11575+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (8300-2*2548) 2548=6*17399709518790656:=by decide
  change 6*P1_7_1.nodeRows (bank362 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank362 u).shape=262144*P1_7_1_2.sixPerNode (8300-2*2548) 2548 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank362 u).shape=17399709518790656; omega, moment11575_2548,by change 11575<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks360To362

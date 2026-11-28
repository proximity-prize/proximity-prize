import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks366To368
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks366To368
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment11577_2615 : P1_7_1.groupedPoleMoment 11577 2615 ≤ 509018341309343 :=
  _root_.PoleAffine6970.certified 11577 2615 509018341309343 (by decide) (by decide +kernel)

theorem moment11579_2498 : P1_7_1.groupedPoleMoment 11579 2498 ≤ 491470625461013 :=
  _root_.PoleAffine6970.certified 11579 2498 491470625461013 (by decide) (by decide +kernel)

theorem moment11579_2548 : P1_7_1.groupedPoleMoment 11579 2548 ≤ 499124969898998 :=
  _root_.PoleAffine6970.certified 11579 2548 499124969898998 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks366To368

namespace Research6969.PackedRanks.PackedRanks366To368
open Research6969.TransitionBanks
theorem rank366 (u:ℕ) : P3_7_1.BankOK (bank366 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank366 u).shape (by change 2*2615≤8300;decide) (by change 8300+2615≤11577+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (8300-2*2615) 2615=6*17745461310914560:=by decide
  change 6*P1_7_1.nodeRows (bank366 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank366 u).shape=262144*P1_7_1_2.sixPerNode (8300-2*2615) 2615 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank366 u).shape=17745461310914560; omega, moment11577_2615,by change 11577<K1.p;decide⟩
theorem rank367 (u:ℕ) : P3_7_1.BankOK (bank367 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank367 u).shape (by change 2*2498≤8300;decide) (by change 8300+2498≤11579+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (8300-2*2498) 2498=6*17139238515245056:=by decide
  change 6*P1_7_1.nodeRows (bank367 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank367 u).shape=262144*P1_7_1_2.sixPerNode (8300-2*2498) 2498 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank367 u).shape=17139238515245056; omega, moment11579_2498,by change 11579<K1.p;decide⟩
theorem rank368 (u:ℕ) : P3_7_1.BankOK (bank368 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank368 u).shape (by change 2*2548≤8300;decide) (by change 8300+2548≤11579+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (8300-2*2548) 2548=6*17399709518790656:=by decide
  change 6*P1_7_1.nodeRows (bank368 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank368 u).shape=262144*P1_7_1_2.sixPerNode (8300-2*2548) 2548 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank368 u).shape=17399709518790656; omega, moment11579_2548,by change 11579<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks366To368

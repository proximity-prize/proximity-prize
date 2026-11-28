import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks372To374
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks372To374
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment11581_2548 : P1_7_1.groupedPoleMoment 11581 2548 ≤ 499402661779949 :=
  _root_.PoleAffine6970.certified 11581 2548 499402661779949 (by decide) (by decide +kernel)

theorem moment11582_2498 : P1_7_1.groupedPoleMoment 11582 2498 ≤ 491880571317053 :=
  _root_.PoleAffine6970.certified 11582 2498 491880571317053 (by decide) (by decide +kernel)

theorem moment11582_2548 : P1_7_1.groupedPoleMoment 11582 2548 ≤ 499541547131788 :=
  _root_.PoleAffine6970.certified 11582 2548 499541547131788 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks372To374

namespace Research6969.PackedRanks.PackedRanks372To374
open Research6969.TransitionBanks
theorem rank372 (u:ℕ) : P3_7_1.BankOK (bank372 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank372 u).shape (by change 2*2548≤8300;decide) (by change 8300+2548≤11581+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (8300-2*2548) 2548=6*17399709518790656:=by decide
  change 6*P1_7_1.nodeRows (bank372 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank372 u).shape=262144*P1_7_1_2.sixPerNode (8300-2*2548) 2548 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank372 u).shape=17399709518790656; omega, moment11581_2548,by change 11581<K1.p;decide⟩
theorem rank373 (u:ℕ) : P3_7_1.BankOK (bank373 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank373 u).shape (by change 2*2498≤8300;decide) (by change 8300+2498≤11582+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (8300-2*2498) 2498=6*17139238515245056:=by decide
  change 6*P1_7_1.nodeRows (bank373 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank373 u).shape=262144*P1_7_1_2.sixPerNode (8300-2*2498) 2498 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank373 u).shape=17139238515245056; omega, moment11582_2498,by change 11582<K1.p;decide⟩
theorem rank374 (u:ℕ) : P3_7_1.BankOK (bank374 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank374 u).shape (by change 2*2548≤8300;decide) (by change 8300+2548≤11582+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (8300-2*2548) 2548=6*17399709518790656:=by decide
  change 6*P1_7_1.nodeRows (bank374 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank374 u).shape=262144*P1_7_1_2.sixPerNode (8300-2*2548) 2548 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank374 u).shape=17399709518790656; omega, moment11582_2548,by change 11582<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks372To374

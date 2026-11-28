import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks369To371
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks369To371
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment11579_2615 : P1_7_1.groupedPoleMoment 11579 2615 ≤ 509301798386539 :=
  _root_.PoleAffine6970.certified 11579 2615 509301798386539 (by decide) (by decide +kernel)

theorem moment11580_2548 : P1_7_1.groupedPoleMoment 11580 2548 ≤ 499263802703202 :=
  _root_.PoleAffine6970.certified 11580 2548 499263802703202 (by decide) (by decide +kernel)

theorem moment11581_2498 : P1_7_1.groupedPoleMoment 11581 2498 ≤ 491743896877039 :=
  _root_.PoleAffine6970.certified 11581 2498 491743896877039 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks369To371

namespace Research6969.PackedRanks.PackedRanks369To371
open Research6969.TransitionBanks
theorem rank369 (u:ℕ) : P3_7_1.BankOK (bank369 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank369 u).shape (by change 2*2615≤8300;decide) (by change 8300+2615≤11579+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (8300-2*2615) 2615=6*17745461310914560:=by decide
  change 6*P1_7_1.nodeRows (bank369 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank369 u).shape=262144*P1_7_1_2.sixPerNode (8300-2*2615) 2615 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank369 u).shape=17745461310914560; omega, moment11579_2615,by change 11579<K1.p;decide⟩
theorem rank370 (u:ℕ) : P3_7_1.BankOK (bank370 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank370 u).shape (by change 2*2548≤8300;decide) (by change 8300+2548≤11580+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (8300-2*2548) 2548=6*17399709518790656:=by decide
  change 6*P1_7_1.nodeRows (bank370 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank370 u).shape=262144*P1_7_1_2.sixPerNode (8300-2*2548) 2548 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank370 u).shape=17399709518790656; omega, moment11580_2548,by change 11580<K1.p;decide⟩
theorem rank371 (u:ℕ) : P3_7_1.BankOK (bank371 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank371 u).shape (by change 2*2498≤8300;decide) (by change 8300+2498≤11581+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (8300-2*2498) 2498=6*17139238515245056:=by decide
  change 6*P1_7_1.nodeRows (bank371 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank371 u).shape=262144*P1_7_1_2.sixPerNode (8300-2*2498) 2498 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank371 u).shape=17139238515245056; omega, moment11581_2498,by change 11581<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks369To371

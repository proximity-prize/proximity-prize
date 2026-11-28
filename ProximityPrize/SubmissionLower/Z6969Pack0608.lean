import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks330To332
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks330To332
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment6697_1512 : P1_7_1.groupedPoleMoment 6697 1512 ≤ 57008284046562 :=
  _root_.PoleAffine6970.certified 6697 1512 57008284046562 (by decide) (by decide +kernel)

theorem moment6698_1421 : P1_7_1.groupedPoleMoment 6698 1421 ≤ 54342858960622 :=
  _root_.PoleAffine6970.certified 6698 1421 54342858960622 (by decide) (by decide +kernel)

theorem moment6698_1445 : P1_7_1.groupedPoleMoment 6698 1445 ≤ 55058665830093 :=
  _root_.PoleAffine6970.certified 6698 1445 55058665830093 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks330To332

namespace Research6969.PackedRanks.PackedRanks330To332
open Research6969.TransitionBanks
theorem rank330 (u:ℕ) : P3_7_1.BankOK (bank330 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank330 u).shape (by change 2*1512≤4800;decide) (by change 4800+1512≤6697+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1512) 1512=6*3433136573644800:=by decide
  change 6*P1_7_1.nodeRows (bank330 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank330 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1512) 1512 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank330 u).shape=3433136573644800; omega, moment6697_1512,by change 6697<K1.p;decide⟩
theorem rank331 (u:ℕ) : P3_7_1.BankOK (bank331 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank331 u).shape (by change 2*1421≤4800;decide) (by change 4800+1421≤6698+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1421) 1421=6*3274891856707584:=by decide
  change 6*P1_7_1.nodeRows (bank331 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank331 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1421) 1421 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank331 u).shape=3274891856707584; omega, moment6698_1421,by change 6698<K1.p;decide⟩
theorem rank332 (u:ℕ) : P3_7_1.BankOK (bank332 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank332 u).shape (by change 2*1445≤4800;decide) (by change 4800+1445≤6698+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1445) 1445=6*3317023033262080:=by decide
  change 6*P1_7_1.nodeRows (bank332 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank332 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1445) 1445 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank332 u).shape=3317023033262080; omega, moment6698_1445,by change 6698<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks330To332

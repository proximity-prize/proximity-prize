import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks351To353
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks351To353
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment9623_2118 : P1_7_1.groupedPoleMoment 9623 2118 ≤ 238176347849000 :=
  _root_.PoleAffine6970.certified 9623 2118 238176347849000 (by decide) (by decide +kernel)

theorem moment9623_2174 : P1_7_1.groupedPoleMoment 9623 2174 ≤ 243058712908678 :=
  _root_.PoleAffine6970.certified 9623 2174 243058712908678 (by decide) (by decide +kernel)

theorem moment9625_2118 : P1_7_1.groupedPoleMoment 9625 2118 ≤ 238335796784464 :=
  _root_.PoleAffine6970.certified 9625 2118 238335796784464 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks351To353

namespace Research6969.PackedRanks.PackedRanks351To353
open Research6969.TransitionBanks
theorem rank351 (u:ℕ) : P3_7_1.BankOK (bank351 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank351 u).shape (by change 2*2118≤6900;decide) (by change 6900+2118≤9623+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2118) 2118=6*9997036108906496:=by decide
  change 6*P1_7_1.nodeRows (bank351 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank351 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2118) 2118 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank351 u).shape=9997036108906496; omega, moment9623_2118,by change 9623<K1.p;decide⟩
theorem rank352 (u:ℕ) : P3_7_1.BankOK (bank352 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank352 u).shape (by change 2*2174≤6900;decide) (by change 6900+2174≤9623+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2174) 2174=6*10196763128627200:=by decide
  change 6*P1_7_1.nodeRows (bank352 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank352 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2174) 2174 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank352 u).shape=10196763128627200; omega, moment9623_2174,by change 9623<K1.p;decide⟩
theorem rank353 (u:ℕ) : P3_7_1.BankOK (bank353 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank353 u).shape (by change 2*2118≤6900;decide) (by change 6900+2118≤9625+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2118) 2118=6*9997036108906496:=by decide
  change 6*P1_7_1.nodeRows (bank353 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank353 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2118) 2118 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank353 u).shape=9997036108906496; omega, moment9625_2118,by change 9625<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks351To353

import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks348To350
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks348To350
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment7954_1750 : P1_7_1.groupedPoleMoment 7954 1750 ≤ 111160708353364 :=
  _root_.PoleAffine6970.certified 7954 1750 111160708353364 (by decide) (by decide +kernel)

theorem moment9621_2118 : P1_7_1.groupedPoleMoment 9621 2118 ≤ 238016971510476 :=
  _root_.PoleAffine6970.certified 9621 2118 238016971510476 (by decide) (by decide +kernel)

theorem moment9621_2174 : P1_7_1.groupedPoleMoment 9621 2174 ≤ 242895948111878 :=
  _root_.PoleAffine6970.certified 9621 2174 242895948111878 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks348To350

namespace Research6969.PackedRanks.PackedRanks348To350
open Research6969.TransitionBanks
theorem rank348 (u:ℕ) : P3_7_1.BankOK (bank348 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank348 u).shape (by change 2*1750≤5700;decide) (by change 5700+1750≤7954+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1750) 1750=6*5637370734182400:=by decide
  change 6*P1_7_1.nodeRows (bank348 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank348 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1750) 1750 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank348 u).shape=5637370734182400; omega, moment7954_1750,by change 7954<K1.p;decide⟩
theorem rank349 (u:ℕ) : P3_7_1.BankOK (bank349 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank349 u).shape (by change 2*2118≤6900;decide) (by change 6900+2118≤9621+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2118) 2118=6*9997036108906496:=by decide
  change 6*P1_7_1.nodeRows (bank349 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank349 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2118) 2118 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank349 u).shape=9997036108906496; omega, moment9621_2118,by change 9621<K1.p;decide⟩
theorem rank350 (u:ℕ) : P3_7_1.BankOK (bank350 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank350 u).shape (by change 2*2174≤6900;decide) (by change 6900+2174≤9621+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2174) 2174=6*10196763128627200:=by decide
  change 6*P1_7_1.nodeRows (bank350 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank350 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2174) 2174 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank350 u).shape=10196763128627200; omega, moment9621_2174,by change 9621<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks348To350

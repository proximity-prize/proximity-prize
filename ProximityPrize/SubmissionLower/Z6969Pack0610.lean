import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks336To338
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks336To338
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment7948_1750 : P1_7_1.groupedPoleMoment 7948 1750 ≤ 110890906752819 :=
  _root_.PoleAffine6970.certified 7948 1750 110890906752819 (by decide) (by decide +kernel)

theorem moment7948_1796 : P1_7_1.groupedPoleMoment 7948 1796 ≤ 113150499898987 :=
  _root_.PoleAffine6970.certified 7948 1796 113150499898987 (by decide) (by decide +kernel)

theorem moment7950_1750 : P1_7_1.groupedPoleMoment 7950 1750 ≤ 110980791054694 :=
  _root_.PoleAffine6970.certified 7950 1750 110980791054694 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks336To338

namespace Research6969.PackedRanks.PackedRanks336To338
open Research6969.TransitionBanks
theorem rank336 (u:ℕ) : P3_7_1.BankOK (bank336 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank336 u).shape (by change 2*1750≤5700;decide) (by change 5700+1750≤7948+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1750) 1750=6*5637370734182400:=by decide
  change 6*P1_7_1.nodeRows (bank336 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank336 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1750) 1750 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank336 u).shape=5637370734182400; omega, moment7948_1750,by change 7948<K1.p;decide⟩
theorem rank337 (u:ℕ) : P3_7_1.BankOK (bank337 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank337 u).shape (by change 2*1796≤5700;decide) (by change 5700+1796≤7948+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1796) 1796=6*5749327563587584:=by decide
  change 6*P1_7_1.nodeRows (bank337 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank337 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1796) 1796 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank337 u).shape=5749327563587584; omega, moment7948_1796,by change 7948<K1.p;decide⟩
theorem rank338 (u:ℕ) : P3_7_1.BankOK (bank338 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank338 u).shape (by change 2*1750≤5700;decide) (by change 5700+1750≤7950+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1750) 1750=6*5637370734182400:=by decide
  change 6*P1_7_1.nodeRows (bank338 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank338 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1750) 1750 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank338 u).shape=5637370734182400; omega, moment7950_1750,by change 7950<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks336To338

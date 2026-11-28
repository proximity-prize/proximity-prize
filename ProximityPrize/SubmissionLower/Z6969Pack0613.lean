import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks345To347
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks345To347
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment7953_1716 : P1_7_1.groupedPoleMoment 7953 1716 ≤ 109428971647179 :=
  _root_.PoleAffine6970.certified 7953 1716 109428971647179 (by decide) (by decide +kernel)

theorem moment7953_1750 : P1_7_1.groupedPoleMoment 7953 1750 ≤ 111115710437454 :=
  _root_.PoleAffine6970.certified 7953 1750 111115710437454 (by decide) (by decide +kernel)

theorem moment7954_1716 : P1_7_1.groupedPoleMoment 7954 1716 ≤ 109473260530676 :=
  _root_.PoleAffine6970.certified 7954 1716 109473260530676 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks345To347

namespace Research6969.PackedRanks.PackedRanks345To347
open Research6969.TransitionBanks
theorem rank345 (u:ℕ) : P3_7_1.BankOK (bank345 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank345 u).shape (by change 2*1716≤5700;decide) (by change 5700+1716≤7953+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1716) 1716=6*5553838907981824:=by decide
  change 6*P1_7_1.nodeRows (bank345 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank345 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1716) 1716 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank345 u).shape=5553838907981824; omega, moment7953_1716,by change 7953<K1.p;decide⟩
theorem rank346 (u:ℕ) : P3_7_1.BankOK (bank346 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank346 u).shape (by change 2*1750≤5700;decide) (by change 5700+1750≤7953+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1750) 1750=6*5637370734182400:=by decide
  change 6*P1_7_1.nodeRows (bank346 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank346 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1750) 1750 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank346 u).shape=5637370734182400; omega, moment7953_1750,by change 7953<K1.p;decide⟩
theorem rank347 (u:ℕ) : P3_7_1.BankOK (bank347 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank347 u).shape (by change 2*1716≤5700;decide) (by change 5700+1716≤7954+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1716) 1716=6*5553838907981824:=by decide
  change 6*P1_7_1.nodeRows (bank347 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank347 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1716) 1716 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank347 u).shape=5553838907981824; omega, moment7954_1716,by change 7954<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks345To347

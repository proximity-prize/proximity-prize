import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks342To344
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks342To344
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment7952_1716 : P1_7_1.groupedPoleMoment 7952 1716 ≤ 109384694947514 :=
  _root_.PoleAffine6970.certified 7952 1716 109384694947514 (by decide) (by decide +kernel)

theorem moment7952_1750 : P1_7_1.groupedPoleMoment 7952 1750 ≤ 111070724916873 :=
  _root_.PoleAffine6970.certified 7952 1750 111070724916873 (by decide) (by decide +kernel)

theorem moment7952_1796 : P1_7_1.groupedPoleMoment 7952 1796 ≤ 113334118485107 :=
  _root_.PoleAffine6970.certified 7952 1796 113334118485107 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks342To344

namespace Research6969.PackedRanks.PackedRanks342To344
open Research6969.TransitionBanks
theorem rank342 (u:ℕ) : P3_7_1.BankOK (bank342 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank342 u).shape (by change 2*1716≤5700;decide) (by change 5700+1716≤7952+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1716) 1716=6*5553838907981824:=by decide
  change 6*P1_7_1.nodeRows (bank342 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank342 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1716) 1716 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank342 u).shape=5553838907981824; omega, moment7952_1716,by change 7952<K1.p;decide⟩
theorem rank343 (u:ℕ) : P3_7_1.BankOK (bank343 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank343 u).shape (by change 2*1750≤5700;decide) (by change 5700+1750≤7952+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1750) 1750=6*5637370734182400:=by decide
  change 6*P1_7_1.nodeRows (bank343 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank343 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1750) 1750 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank343 u).shape=5637370734182400; omega, moment7952_1750,by change 7952<K1.p;decide⟩
theorem rank344 (u:ℕ) : P3_7_1.BankOK (bank344 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank344 u).shape (by change 2*1796≤5700;decide) (by change 5700+1796≤7952+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1796) 1796=6*5749327563587584:=by decide
  change 6*P1_7_1.nodeRows (bank344 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank344 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1796) 1796 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank344 u).shape=5749327563587584; omega, moment7952_1796,by change 7952<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks342To344

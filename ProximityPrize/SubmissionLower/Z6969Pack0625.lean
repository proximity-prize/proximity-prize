import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks378To380
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks378To380
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment13950_3150 : P1_7_1.groupedPoleMoment 13950 3150 ≤ 1072717072025530 :=
  _root_.PoleAffine6970.certified 13950 3150 1072717072025530 (by decide) (by decide +kernel)

theorem moment13952_3010 : P1_7_1.groupedPoleMoment 13952 3010 ≤ 1035886358306578 :=
  _root_.PoleAffine6970.certified 13952 3010 1035886358306578 (by decide) (by decide +kernel)

theorem moment13952_3070 : P1_7_1.groupedPoleMoment 13952 3070 ≤ 1051954539834997 :=
  _root_.PoleAffine6970.certified 13952 3070 1051954539834997 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks378To380

namespace Research6969.PackedRanks.PackedRanks378To380
open Research6969.TransitionBanks
theorem rank378 (u:ℕ) : P3_7_1.BankOK (bank378 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank378 u).shape (by change 2*3150≤10000;decide) (by change 10000+3150≤13950+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3150) 3150=6*31027650042265600:=by decide
  change 6*P1_7_1.nodeRows (bank378 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank378 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3150) 3150 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank378 u).shape=31027650042265600; omega, moment13950_3150,by change 13950<K1.p;decide⟩
theorem rank379 (u:ℕ) : P3_7_1.BankOK (bank379 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank379 u).shape (by change 2*3010≤10000;decide) (by change 10000+3010≤13952+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3010) 3010=6*29974681586237440:=by decide
  change 6*P1_7_1.nodeRows (bank379 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank379 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3010) 3010 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank379 u).shape=29974681586237440; omega, moment13952_3010,by change 13952<K1.p;decide⟩
theorem rank380 (u:ℕ) : P3_7_1.BankOK (bank380 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank380 u).shape (by change 2*3070≤10000;decide) (by change 10000+3070≤13952+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3070) 3070=6*30428373265940480:=by decide
  change 6*P1_7_1.nodeRows (bank380 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank380 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3070) 3070 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank380 u).shape=30428373265940480; omega, moment13952_3070,by change 13952<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks378To380

import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks381To383
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks381To383
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment13952_3150 : P1_7_1.groupedPoleMoment 13952 3150 ≤ 1073212809809009 :=
  _root_.PoleAffine6970.certified 13952 3150 1073212809809009 (by decide) (by decide +kernel)

theorem moment13953_3010 : P1_7_1.groupedPoleMoment 13953 3010 ≤ 1036125345444439 :=
  _root_.PoleAffine6970.certified 13953 3010 1036125345444439 (by decide) (by decide +kernel)

theorem moment13953_3070 : P1_7_1.groupedPoleMoment 13953 3070 ≤ 1052197377228338 :=
  _root_.PoleAffine6970.certified 13953 3070 1052197377228338 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks381To383

namespace Research6969.PackedRanks.PackedRanks381To383
open Research6969.TransitionBanks
theorem rank381 (u:ℕ) : P3_7_1.BankOK (bank381 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank381 u).shape (by change 2*3150≤10000;decide) (by change 10000+3150≤13952+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3150) 3150=6*31027650042265600:=by decide
  change 6*P1_7_1.nodeRows (bank381 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank381 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3150) 3150 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank381 u).shape=31027650042265600; omega, moment13952_3150,by change 13952<K1.p;decide⟩
theorem rank382 (u:ℕ) : P3_7_1.BankOK (bank382 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank382 u).shape (by change 2*3010≤10000;decide) (by change 10000+3010≤13953+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3010) 3010=6*29974681586237440:=by decide
  change 6*P1_7_1.nodeRows (bank382 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank382 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3010) 3010 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank382 u).shape=29974681586237440; omega, moment13953_3010,by change 13953<K1.p;decide⟩
theorem rank383 (u:ℕ) : P3_7_1.BankOK (bank383 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank383 u).shape (by change 2*3070≤10000;decide) (by change 10000+3070≤13953+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3070) 3070=6*30428373265940480:=by decide
  change 6*P1_7_1.nodeRows (bank383 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank383 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3070) 3070 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank383 u).shape=30428373265940480; omega, moment13953_3070,by change 13953<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks381To383

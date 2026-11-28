import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks375To377
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks375To377
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment13948_3070 : P1_7_1.groupedPoleMoment 13948 3070 ≤ 1050983571587703 :=
  _root_.PoleAffine6970.certified 13948 3070 1050983571587703 (by decide) (by decide +kernel)

theorem moment13948_3150 : P1_7_1.groupedPoleMoment 13948 3150 ≤ 1072221490229155 :=
  _root_.PoleAffine6970.certified 13948 3150 1072221490229155 (by decide) (by decide +kernel)

theorem moment13950_3070 : P1_7_1.groupedPoleMoment 13950 3070 ≤ 1051468979452278 :=
  _root_.PoleAffine6970.certified 13950 3070 1051468979452278 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks375To377

namespace Research6969.PackedRanks.PackedRanks375To377
open Research6969.TransitionBanks
theorem rank375 (u:ℕ) : P3_7_1.BankOK (bank375 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank375 u).shape (by change 2*3070≤10000;decide) (by change 10000+3070≤13948+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3070) 3070=6*30428373265940480:=by decide
  change 6*P1_7_1.nodeRows (bank375 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank375 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3070) 3070 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank375 u).shape=30428373265940480; omega, moment13948_3070,by change 13948<K1.p;decide⟩
theorem rank376 (u:ℕ) : P3_7_1.BankOK (bank376 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank376 u).shape (by change 2*3150≤10000;decide) (by change 10000+3150≤13948+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3150) 3150=6*31027650042265600:=by decide
  change 6*P1_7_1.nodeRows (bank376 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank376 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3150) 3150 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank376 u).shape=31027650042265600; omega, moment13948_3150,by change 13948<K1.p;decide⟩
theorem rank377 (u:ℕ) : P3_7_1.BankOK (bank377 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank377 u).shape (by change 2*3070≤10000;decide) (by change 10000+3070≤13950+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3070) 3070=6*30428373265940480:=by decide
  change 6*P1_7_1.nodeRows (bank377 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank377 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3070) 3070 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank377 u).shape=30428373265940480; omega, moment13950_3070,by change 13950<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks375To377

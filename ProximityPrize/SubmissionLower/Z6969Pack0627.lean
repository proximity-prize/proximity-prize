import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks384To386
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks384To386
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment13954_3010 : P1_7_1.groupedPoleMoment 13954 3010 ≤ 1036364370066239 :=
  _root_.PoleAffine6970.certified 13954 3010 1036364370066239 (by decide) (by decide +kernel)

theorem moment13954_3070 : P1_7_1.groupedPoleMoment 13954 3070 ≤ 1052440252760428 :=
  _root_.PoleAffine6970.certified 13954 3070 1052440252760428 (by decide) (by decide +kernel)

theorem moment13955_3010 : P1_7_1.groupedPoleMoment 13955 3010 ≤ 1036603432174989 :=
  _root_.PoleAffine6970.certified 13955 3010 1036603432174989 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks384To386

namespace Research6969.PackedRanks.PackedRanks384To386
open Research6969.TransitionBanks
theorem rank384 (u:ℕ) : P3_7_1.BankOK (bank384 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank384 u).shape (by change 2*3010≤10000;decide) (by change 10000+3010≤13954+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3010) 3010=6*29974681586237440:=by decide
  change 6*P1_7_1.nodeRows (bank384 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank384 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3010) 3010 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank384 u).shape=29974681586237440; omega, moment13954_3010,by change 13954<K1.p;decide⟩
theorem rank385 (u:ℕ) : P3_7_1.BankOK (bank385 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank385 u).shape (by change 2*3070≤10000;decide) (by change 10000+3070≤13954+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3070) 3070=6*30428373265940480:=by decide
  change 6*P1_7_1.nodeRows (bank385 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank385 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3070) 3070 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank385 u).shape=30428373265940480; omega, moment13954_3070,by change 13954<K1.p;decide⟩
theorem rank386 (u:ℕ) : P3_7_1.BankOK (bank386 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank386 u).shape (by change 2*3010≤10000;decide) (by change 10000+3010≤13955+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (10000-2*3010) 3010=6*29974681586237440:=by decide
  change 6*P1_7_1.nodeRows (bank386 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank386 u).shape=262144*P1_7_1_2.sixPerNode (10000-2*3010) 3010 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank386 u).shape=29974681586237440; omega, moment13955_3010,by change 13955<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks384To386

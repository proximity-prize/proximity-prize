import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks306To308
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks306To308
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment5507_1213 : P1_7_1.groupedPoleMoment 5507 1213 ≤ 25577387039299 :=
  _root_.PoleAffine6970.certified 5507 1213 25577387039299 (by decide) (by decide +kernel)

theorem moment5507_1244 : P1_7_1.groupedPoleMoment 5507 1244 ≤ 26084011577468 :=
  _root_.PoleAffine6970.certified 5507 1244 26084011577468 (by decide) (by decide +kernel)

theorem moment5509_1213 : P1_7_1.groupedPoleMoment 5509 1213 ≤ 25607310424524 :=
  _root_.PoleAffine6970.certified 5509 1213 25607310424524 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks306To308

namespace Research6969.PackedRanks.PackedRanks306To308
open Research6969.TransitionBanks
theorem rank306 (u:ℕ) : P3_7_1.BankOK (bank306 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank306 u).shape (by change 2*1213≤3950;decide) (by change 3950+1213≤5507+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3950-2*1213) 1213=6*1877062482395136:=by decide
  change 6*P1_7_1.nodeRows (bank306 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank306 u).shape=262144*P1_7_1_2.sixPerNode (3950-2*1213) 1213 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank306 u).shape=1877062482395136; omega, moment5507_1213,by change 5507<K1.p;decide⟩
theorem rank307 (u:ℕ) : P3_7_1.BankOK (bank307 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank307 u).shape (by change 2*1244≤3950;decide) (by change 3950+1244≤5507+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3950-2*1244) 1244=6*1913299978158080:=by decide
  change 6*P1_7_1.nodeRows (bank307 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank307 u).shape=262144*P1_7_1_2.sixPerNode (3950-2*1244) 1244 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank307 u).shape=1913299978158080; omega, moment5507_1244,by change 5507<K1.p;decide⟩
theorem rank308 (u:ℕ) : P3_7_1.BankOK (bank308 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank308 u).shape (by change 2*1213≤3950;decide) (by change 3950+1213≤5509+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3950-2*1213) 1213=6*1877062482395136:=by decide
  change 6*P1_7_1.nodeRows (bank308 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank308 u).shape=262144*P1_7_1_2.sixPerNode (3950-2*1213) 1213 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank308 u).shape=1877062482395136; omega, moment5509_1213,by change 5509<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks306To308

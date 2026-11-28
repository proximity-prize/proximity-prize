import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks309To311
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks309To311
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment5510_1189 : P1_7_1.groupedPoleMoment 5510 1189 ≤ 25226292539926 :=
  _root_.PoleAffine6970.certified 5510 1189 25226292539926 (by decide) (by decide +kernel)

theorem moment5510_1213 : P1_7_1.groupedPoleMoment 5510 1213 ≤ 25622281045803 :=
  _root_.PoleAffine6970.certified 5510 1213 25622281045803 (by decide) (by decide +kernel)

theorem moment5510_1244 : P1_7_1.groupedPoleMoment 5510 1244 ≤ 26129827888718 :=
  _root_.PoleAffine6970.certified 5510 1244 26129827888718 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks309To311

namespace Research6969.PackedRanks.PackedRanks309To311
open Research6969.TransitionBanks
theorem rank309 (u:ℕ) : P3_7_1.BankOK (bank309 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank309 u).shape (by change 2*1189≤3950;decide) (by change 3950+1189≤5510+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3950-2*1189) 1189=6*1848744952463360:=by decide
  change 6*P1_7_1.nodeRows (bank309 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank309 u).shape=262144*P1_7_1_2.sixPerNode (3950-2*1189) 1189 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank309 u).shape=1848744952463360; omega, moment5510_1189,by change 5510<K1.p;decide⟩
theorem rank310 (u:ℕ) : P3_7_1.BankOK (bank310 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank310 u).shape (by change 2*1213≤3950;decide) (by change 3950+1213≤5510+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3950-2*1213) 1213=6*1877062482395136:=by decide
  change 6*P1_7_1.nodeRows (bank310 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank310 u).shape=262144*P1_7_1_2.sixPerNode (3950-2*1213) 1213 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank310 u).shape=1877062482395136; omega, moment5510_1213,by change 5510<K1.p;decide⟩
theorem rank311 (u:ℕ) : P3_7_1.BankOK (bank311 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank311 u).shape (by change 2*1244≤3950;decide) (by change 3950+1244≤5510+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3950-2*1244) 1244=6*1913299978158080:=by decide
  change 6*P1_7_1.nodeRows (bank311 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank311 u).shape=262144*P1_7_1_2.sixPerNode (3950-2*1244) 1244 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank311 u).shape=1913299978158080; omega, moment5510_1244,by change 5510<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks309To311

import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks312To314
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks312To314
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment5511_1189 : P1_7_1.groupedPoleMoment 5511 1189 ≤ 25241028863276 :=
  _root_.PoleAffine6970.certified 5511 1189 25241028863276 (by decide) (by decide +kernel)

theorem moment5511_1213 : P1_7_1.groupedPoleMoment 5511 1213 ≤ 25637257621145 :=
  _root_.PoleAffine6970.certified 5511 1213 25637257621145 (by decide) (by decide +kernel)

theorem moment5512_1169 : P1_7_1.groupedPoleMoment 5512 1169 ≤ 24923274283249 :=
  _root_.PoleAffine6970.certified 5512 1169 24923274283249 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks312To314

namespace Research6969.PackedRanks.PackedRanks312To314
open Research6969.TransitionBanks
theorem rank312 (u:ℕ) : P3_7_1.BankOK (bank312 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank312 u).shape (by change 2*1189≤3950;decide) (by change 3950+1189≤5511+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3950-2*1189) 1189=6*1848744952463360:=by decide
  change 6*P1_7_1.nodeRows (bank312 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank312 u).shape=262144*P1_7_1_2.sixPerNode (3950-2*1189) 1189 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank312 u).shape=1848744952463360; omega, moment5511_1189,by change 5511<K1.p;decide⟩
theorem rank313 (u:ℕ) : P3_7_1.BankOK (bank313 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank313 u).shape (by change 2*1213≤3950;decide) (by change 3950+1213≤5511+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3950-2*1213) 1213=6*1877062482395136:=by decide
  change 6*P1_7_1.nodeRows (bank313 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank313 u).shape=262144*P1_7_1_2.sixPerNode (3950-2*1213) 1213 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank313 u).shape=1877062482395136; omega, moment5511_1213,by change 5511<K1.p;decide⟩
theorem rank314 (u:ℕ) : P3_7_1.BankOK (bank314 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank314 u).shape (by change 2*1169≤3950;decide) (by change 3950+1169≤5512+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3950-2*1169) 1169=6*1824966114017280:=by decide
  change 6*P1_7_1.nodeRows (bank314 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank314 u).shape=262144*P1_7_1_2.sixPerNode (3950-2*1169) 1169 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank314 u).shape=1824966114017280; omega, moment5512_1169,by change 5512<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks312To314

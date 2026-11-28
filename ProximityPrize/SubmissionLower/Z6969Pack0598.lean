import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks294To296
section Z6969Source0713
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks294To296
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment4459_1008 : P1_7_1.groupedPoleMoment 4459 1008 ≤ 11221829825062 :=
  _root_.PoleAffine6970.certified 4459 1008 11221829825062 (by decide) (by decide +kernel)

theorem moment4461_982 : P1_7_1.groupedPoleMoment 4461 982 ≤ 11012145571636 :=
  _root_.PoleAffine6970.certified 4461 982 11012145571636 (by decide) (by decide +kernel)

theorem moment4462_982 : P1_7_1.groupedPoleMoment 4462 982 ≤ 11020095796464 :=
  _root_.PoleAffine6970.certified 4462 982 11020095796464 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks294To296

namespace Research6969.PackedRanks.PackedRanks294To296
open Research6969.TransitionBanks
theorem rank294 (u:ℕ) : P3_7_1.BankOK (bank294 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank294 u).shape (by change 2*1008≤3200;decide) (by change 3200+1008≤4459+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3200-2*1008) 1008=6*1017717693874176:=by decide
  change 6*P1_7_1.nodeRows (bank294 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank294 u).shape=262144*P1_7_1_2.sixPerNode (3200-2*1008) 1008 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank294 u).shape=1017717693874176; omega, moment4459_1008,by change 4459<K1.p;decide⟩
theorem rank295 (u:ℕ) : P3_7_1.BankOK (bank295 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank295 u).shape (by change 2*982≤3200;decide) (by change 3200+982≤4461+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3200-2*982) 982=6*997767489781760:=by decide
  change 6*P1_7_1.nodeRows (bank295 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank295 u).shape=262144*P1_7_1_2.sixPerNode (3200-2*982) 982 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank295 u).shape=997767489781760; omega, moment4461_982,by change 4461<K1.p;decide⟩
theorem rank296 (u:ℕ) : P3_7_1.BankOK (bank296 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank296 u).shape (by change 2*982≤3200;decide) (by change 3200+982≤4462+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3200-2*982) 982=6*997767489781760:=by decide
  change 6*P1_7_1.nodeRows (bank296 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank296 u).shape=262144*P1_7_1_2.sixPerNode (3200-2*982) 982 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank296 u).shape=997767489781760; omega, moment4462_982,by change 4462<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks294To296
end Z6969Source0713

-- Source: Research6969.PackedRanks297To299
section Z6969Source0714
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks297To299
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment4463_982 : P1_7_1.groupedPoleMoment 4463 982 ≤ 11028049925768 :=
  _root_.PoleAffine6970.certified 4463 982 11028049925768 (by decide) (by decide +kernel)

theorem moment4463_1008 : P1_7_1.groupedPoleMoment 4463 1008 ≤ 11254299374432 :=
  _root_.PoleAffine6970.certified 4463 1008 11254299374432 (by decide) (by decide +kernel)

theorem moment4464_963 : P1_7_1.groupedPoleMoment 4464 963 ≤ 10869251283552 :=
  _root_.PoleAffine6970.certified 4464 963 10869251283552 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks297To299

namespace Research6969.PackedRanks.PackedRanks297To299
open Research6969.TransitionBanks
theorem rank297 (u:ℕ) : P3_7_1.BankOK (bank297 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank297 u).shape (by change 2*982≤3200;decide) (by change 3200+982≤4463+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3200-2*982) 982=6*997767489781760:=by decide
  change 6*P1_7_1.nodeRows (bank297 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank297 u).shape=262144*P1_7_1_2.sixPerNode (3200-2*982) 982 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank297 u).shape=997767489781760; omega, moment4463_982,by change 4463<K1.p;decide⟩
theorem rank298 (u:ℕ) : P3_7_1.BankOK (bank298 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank298 u).shape (by change 2*1008≤3200;decide) (by change 3200+1008≤4463+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3200-2*1008) 1008=6*1017717693874176:=by decide
  change 6*P1_7_1.nodeRows (bank298 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank298 u).shape=262144*P1_7_1_2.sixPerNode (3200-2*1008) 1008 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank298 u).shape=1017717693874176; omega, moment4463_1008,by change 4463<K1.p;decide⟩
theorem rank299 (u:ℕ) : P3_7_1.BankOK (bank299 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank299 u).shape (by change 2*963≤3200;decide) (by change 3200+963≤4464+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3200-2*963) 963=6*983050615259136:=by decide
  change 6*P1_7_1.nodeRows (bank299 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank299 u).shape=262144*P1_7_1_2.sixPerNode (3200-2*963) 963 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank299 u).shape=983050615259136; omega, moment4464_963,by change 4464<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks297To299
end Z6969Source0714

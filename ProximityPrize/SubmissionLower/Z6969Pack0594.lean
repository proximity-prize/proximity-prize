import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks270To272
section Z6969Source0704
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks270To272
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3628_783 : P1_7_1.groupedPoleMoment 3628 783 ≤ 4745819470168 :=
  _root_.PoleAffine6970.certified 3628 783 4745819470168 (by decide) (by decide +kernel)

theorem moment3628_798 : P1_7_1.groupedPoleMoment 3628 798 ≤ 4816500515660 :=
  _root_.PoleAffine6970.certified 3628 798 4816500515660 (by decide) (by decide +kernel)

theorem moment3691_830 : P1_7_1.groupedPoleMoment 3691 830 ≤ 5249056297887 :=
  _root_.PoleAffine6970.certified 3691 830 5249056297887 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks270To272

namespace Research6969.PackedRanks.PackedRanks270To272
open Research6969.TransitionBanks
theorem rank270 (u:ℕ) : P3_7_1.BankOK (bank270 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank270 u).shape (by change 2*783≤2600;decide) (by change 2600+783≤3628+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*783) 783=6*527755772952576:=by decide
  change 6*P1_7_1.nodeRows (bank270 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank270 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*783) 783 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank270 u).shape=527755772952576; omega, moment3628_783,by change 3628<K1.p;decide⟩
theorem rank271 (u:ℕ) : P3_7_1.BankOK (bank271 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank271 u).shape (by change 2*798≤2600;decide) (by change 2600+798≤3628+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*798) 798=6*535425056505856:=by decide
  change 6*P1_7_1.nodeRows (bank271 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank271 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*798) 798 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank271 u).shape=535425056505856; omega, moment3628_798,by change 3628<K1.p;decide⟩
theorem rank272 (u:ℕ) : P3_7_1.BankOK (bank272 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank272 u).shape (by change 2*830≤2652;decide) (by change 2652+830≤3691+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2652-2*830) 830=6*576642060910592:=by decide
  change 6*P1_7_1.nodeRows (bank272 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank272 u).shape=262144*P1_7_1_2.sixPerNode (2652-2*830) 830 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank272 u).shape=576642060910592; omega, moment3691_830,by change 3691<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks270To272
end Z6969Source0704

-- Source: Research6969.PackedRanks273To275
section Z6969Source0705
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks273To275
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3767_814 : P1_7_1.groupedPoleMoment 3767 814 ≤ 5520825894692 :=
  _root_.PoleAffine6970.certified 3767 814 5520825894692 (by decide) (by decide +kernel)

theorem moment3782_845 : P1_7_1.groupedPoleMoment 3782 845 ≤ 5756976302970 :=
  _root_.PoleAffine6970.certified 3782 845 5756976302970 (by decide) (by decide +kernel)

theorem moment3852_861 : P1_7_1.groupedPoleMoment 3852 861 ≤ 6196939591060 :=
  _root_.PoleAffine6970.certified 3852 861 6196939591060 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks273To275

namespace Research6969.PackedRanks.PackedRanks273To275
open Research6969.TransitionBanks
theorem rank273 (u:ℕ) : P3_7_1.BankOK (bank273 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank273 u).shape (by change 2*814≤2705;decide) (by change 2705+814≤3767+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2705-2*814) 814=6*593924919132160:=by decide
  change 6*P1_7_1.nodeRows (bank273 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank273 u).shape=262144*P1_7_1_2.sixPerNode (2705-2*814) 814 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank273 u).shape=593924919132160; omega, moment3767_814,by change 3767<K1.p;decide⟩
theorem rank274 (u:ℕ) : P3_7_1.BankOK (bank274 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank274 u).shape (by change 2*845≤2717;decide) (by change 2717+845≤3782+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2717-2*845) 845=6*617112204214272:=by decide
  change 6*P1_7_1.nodeRows (bank274 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank274 u).shape=262144*P1_7_1_2.sixPerNode (2717-2*845) 845 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank274 u).shape=617112204214272; omega, moment3782_845,by change 3782<K1.p;decide⟩
theorem rank275 (u:ℕ) : P3_7_1.BankOK (bank275 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank275 u).shape (by change 2*861≤2767;decide) (by change 2767+861≤3852+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2767-2*861) 861=6*652050240634880:=by decide
  change 6*P1_7_1.nodeRows (bank275 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank275 u).shape=262144*P1_7_1_2.sixPerNode (2767-2*861) 861 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank275 u).shape=652050240634880; omega, moment3852_861,by change 3852<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks273To275
end Z6969Source0705

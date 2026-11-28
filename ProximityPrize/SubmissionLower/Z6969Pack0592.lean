import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks258To260
section Z6969Source0699
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks258To260
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3623_798 : P1_7_1.groupedPoleMoment 3623 798 ≤ 4795161706555 :=
  _root_.PoleAffine6970.certified 3623 798 4795161706555 (by decide) (by decide +kernel)

theorem moment3623_819 : P1_7_1.groupedPoleMoment 3623 819 ≤ 4892906717079 :=
  _root_.PoleAffine6970.certified 3623 819 4892906717079 (by decide) (by decide +kernel)

theorem moment3624_798 : P1_7_1.groupedPoleMoment 3624 798 ≤ 4799424311630 :=
  _root_.PoleAffine6970.certified 3624 798 4799424311630 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks258To260

namespace Research6969.PackedRanks.PackedRanks258To260
open Research6969.TransitionBanks
theorem rank258 (u:ℕ) : P3_7_1.BankOK (bank258 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank258 u).shape (by change 2*798≤2600;decide) (by change 2600+798≤3623+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*798) 798=6*535425056505856:=by decide
  change 6*P1_7_1.nodeRows (bank258 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank258 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*798) 798 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank258 u).shape=535425056505856; omega, moment3623_798,by change 3623<K1.p;decide⟩
theorem rank259 (u:ℕ) : P3_7_1.BankOK (bank259 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank259 u).shape (by change 2*819≤2600;decide) (by change 2600+819≤3623+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*819) 819=6*546063062138880:=by decide
  change 6*P1_7_1.nodeRows (bank259 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank259 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*819) 819 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank259 u).shape=546063062138880; omega, moment3623_819,by change 3623<K1.p;decide⟩
theorem rank260 (u:ℕ) : P3_7_1.BankOK (bank260 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank260 u).shape (by change 2*798≤2600;decide) (by change 2600+798≤3624+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*798) 798=6*535425056505856:=by decide
  change 6*P1_7_1.nodeRows (bank260 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank260 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*798) 798 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank260 u).shape=535425056505856; omega, moment3624_798,by change 3624<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks258To260
end Z6969Source0699

-- Source: Research6969.PackedRanks261To263
section Z6969Source0700
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks261To263
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3625_783 : P1_7_1.groupedPoleMoment 3625 783 ≤ 4733203574232 :=
  _root_.PoleAffine6970.certified 3625 783 4733203574232 (by decide) (by decide +kernel)

theorem moment3625_798 : P1_7_1.groupedPoleMoment 3625 798 ≤ 4803689494279 :=
  _root_.PoleAffine6970.certified 3625 798 4803689494279 (by decide) (by decide +kernel)

theorem moment3625_819 : P1_7_1.groupedPoleMoment 3625 819 ≤ 4901614794409 :=
  _root_.PoleAffine6970.certified 3625 819 4901614794409 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks261To263

namespace Research6969.PackedRanks.PackedRanks261To263
open Research6969.TransitionBanks
theorem rank261 (u:ℕ) : P3_7_1.BankOK (bank261 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank261 u).shape (by change 2*783≤2600;decide) (by change 2600+783≤3625+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*783) 783=6*527755772952576:=by decide
  change 6*P1_7_1.nodeRows (bank261 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank261 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*783) 783 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank261 u).shape=527755772952576; omega, moment3625_783,by change 3625<K1.p;decide⟩
theorem rank262 (u:ℕ) : P3_7_1.BankOK (bank262 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank262 u).shape (by change 2*798≤2600;decide) (by change 2600+798≤3625+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*798) 798=6*535425056505856:=by decide
  change 6*P1_7_1.nodeRows (bank262 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank262 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*798) 798 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank262 u).shape=535425056505856; omega, moment3625_798,by change 3625<K1.p;decide⟩
theorem rank263 (u:ℕ) : P3_7_1.BankOK (bank263 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank263 u).shape (by change 2*819≤2600;decide) (by change 2600+819≤3625+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*819) 819=6*546063062138880:=by decide
  change 6*P1_7_1.nodeRows (bank263 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank263 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*819) 819 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank263 u).shape=546063062138880; omega, moment3625_819,by change 3625<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks261To263
end Z6969Source0700

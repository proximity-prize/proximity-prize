import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0592

set_option Elab.async false

-- Source: Research6969.PackedRanks264To266
section Z6969Source0701
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks264To266
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3626_798 : P1_7_1.groupedPoleMoment 3626 798 ≤ 4807957255301 :=
  _root_.PoleAffine6970.certified 3626 798 4807957255301 (by decide) (by decide +kernel)

theorem moment3626_819 : P1_7_1.groupedPoleMoment 3626 819 ≤ 4905972788959 :=
  _root_.PoleAffine6970.certified 3626 819 4905972788959 (by decide) (by decide +kernel)

theorem moment3627_783 : P1_7_1.groupedPoleMoment 3627 783 ≤ 4741611634368 :=
  _root_.PoleAffine6970.certified 3627 783 4741611634368 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks264To266

namespace Research6969.PackedRanks.PackedRanks264To266
open Research6969.TransitionBanks
theorem rank264 (u:ℕ) : P3_7_1.BankOK (bank264 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank264 u).shape (by change 2*798≤2600;decide) (by change 2600+798≤3626+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*798) 798=6*535425056505856:=by decide
  change 6*P1_7_1.nodeRows (bank264 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank264 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*798) 798 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank264 u).shape=535425056505856; omega, moment3626_798,by change 3626<K1.p;decide⟩
theorem rank265 (u:ℕ) : P3_7_1.BankOK (bank265 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank265 u).shape (by change 2*819≤2600;decide) (by change 2600+819≤3626+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*819) 819=6*546063062138880:=by decide
  change 6*P1_7_1.nodeRows (bank265 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank265 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*819) 819 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank265 u).shape=546063062138880; omega, moment3626_819,by change 3626<K1.p;decide⟩
theorem rank266 (u:ℕ) : P3_7_1.BankOK (bank266 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank266 u).shape (by change 2*783≤2600;decide) (by change 2600+783≤3627+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*783) 783=6*527755772952576:=by decide
  change 6*P1_7_1.nodeRows (bank266 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank266 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*783) 783 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank266 u).shape=527755772952576; omega, moment3627_783,by change 3627<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks264To266
end Z6969Source0701

-- Source: Research6969.PackedRanks267To269
section Z6969Source0702
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks267To269
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3627_798 : P1_7_1.groupedPoleMoment 3627 798 ≤ 4812227595495 :=
  _root_.PoleAffine6970.certified 3627 798 4812227595495 (by decide) (by decide +kernel)

theorem moment3627_819 : P1_7_1.groupedPoleMoment 3627 819 ≤ 4910333421859 :=
  _root_.PoleAffine6970.certified 3627 819 4910333421859 (by decide) (by decide +kernel)

theorem moment3628_770 : P1_7_1.groupedPoleMoment 3628 770 ≤ 4684185417862 :=
  _root_.PoleAffine6970.certified 3628 770 4684185417862 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks267To269

namespace Research6969.PackedRanks.PackedRanks267To269
open Research6969.TransitionBanks
theorem rank267 (u:ℕ) : P3_7_1.BankOK (bank267 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank267 u).shape (by change 2*798≤2600;decide) (by change 2600+798≤3627+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*798) 798=6*535425056505856:=by decide
  change 6*P1_7_1.nodeRows (bank267 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank267 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*798) 798 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank267 u).shape=535425056505856; omega, moment3627_798,by change 3627<K1.p;decide⟩
theorem rank268 (u:ℕ) : P3_7_1.BankOK (bank268 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank268 u).shape (by change 2*819≤2600;decide) (by change 2600+819≤3627+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*819) 819=6*546063062138880:=by decide
  change 6*P1_7_1.nodeRows (bank268 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank268 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*819) 819 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank268 u).shape=546063062138880; omega, moment3627_819,by change 3627<K1.p;decide⟩
theorem rank269 (u:ℕ) : P3_7_1.BankOK (bank269 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank269 u).shape (by change 2*770≤2600;decide) (by change 2600+770≤3628+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*770) 770=6*521059839508480:=by decide
  change 6*P1_7_1.nodeRows (bank269 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank269 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*770) 770 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank269 u).shape=521059839508480; omega, moment3628_770,by change 3628<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks267To269
end Z6969Source0702

-- Source: Research6969.TransitionBankChecks14
section Z6969Source0703
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

theorem rank252 (u : ℕ) : P3_7_1.BankOK (bank252 u) :=
  PackedRanks.PackedRanks252To254.rank252 u
theorem rank253 (u : ℕ) : P3_7_1.BankOK (bank253 u) :=
  PackedRanks.PackedRanks252To254.rank253 u
theorem rank254 (u : ℕ) : P3_7_1.BankOK (bank254 u) :=
  PackedRanks.PackedRanks252To254.rank254 u
theorem rank255 (u : ℕ) : P3_7_1.BankOK (bank255 u) :=
  PackedRanks.PackedRanks255To257.rank255 u
theorem rank256 (u : ℕ) : P3_7_1.BankOK (bank256 u) :=
  PackedRanks.PackedRanks255To257.rank256 u
theorem rank257 (u : ℕ) : P3_7_1.BankOK (bank257 u) :=
  PackedRanks.PackedRanks255To257.rank257 u
theorem rank258 (u : ℕ) : P3_7_1.BankOK (bank258 u) :=
  PackedRanks.PackedRanks258To260.rank258 u
theorem rank259 (u : ℕ) : P3_7_1.BankOK (bank259 u) :=
  PackedRanks.PackedRanks258To260.rank259 u
theorem rank260 (u : ℕ) : P3_7_1.BankOK (bank260 u) :=
  PackedRanks.PackedRanks258To260.rank260 u
theorem rank261 (u : ℕ) : P3_7_1.BankOK (bank261 u) :=
  PackedRanks.PackedRanks261To263.rank261 u
theorem rank262 (u : ℕ) : P3_7_1.BankOK (bank262 u) :=
  PackedRanks.PackedRanks261To263.rank262 u
theorem rank263 (u : ℕ) : P3_7_1.BankOK (bank263 u) :=
  PackedRanks.PackedRanks261To263.rank263 u
theorem rank264 (u : ℕ) : P3_7_1.BankOK (bank264 u) :=
  PackedRanks.PackedRanks264To266.rank264 u
theorem rank265 (u : ℕ) : P3_7_1.BankOK (bank265 u) :=
  PackedRanks.PackedRanks264To266.rank265 u
theorem rank266 (u : ℕ) : P3_7_1.BankOK (bank266 u) :=
  PackedRanks.PackedRanks264To266.rank266 u
theorem rank267 (u : ℕ) : P3_7_1.BankOK (bank267 u) :=
  PackedRanks.PackedRanks267To269.rank267 u
theorem rank268 (u : ℕ) : P3_7_1.BankOK (bank268 u) :=
  PackedRanks.PackedRanks267To269.rank268 u
theorem rank269 (u : ℕ) : P3_7_1.BankOK (bank269 u) :=
  PackedRanks.PackedRanks267To269.rank269 u
end Research6969.TransitionBanks
end Z6969Source0703

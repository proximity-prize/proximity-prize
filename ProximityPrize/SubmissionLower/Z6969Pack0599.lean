import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0597
import ProximityPrize.SubmissionLower.Z6969Pack0598

set_option Elab.async false

-- Source: Research6969.PackedRanks300To302
section Z6969Source0715
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks300To302
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment4464_982 : P1_7_1.groupedPoleMoment 4464 982 ≤ 11036007960531 :=
  _root_.PoleAffine6970.certified 4464 982 11036007960531 (by decide) (by decide +kernel)

theorem moment4464_1008 : P1_7_1.groupedPoleMoment 4464 1008 ≤ 11262426748352 :=
  _root_.PoleAffine6970.certified 4464 1008 11262426748352 (by decide) (by decide +kernel)

theorem moment4465_947 : P1_7_1.groupedPoleMoment 4465 947 ≤ 10735676910569 :=
  _root_.PoleAffine6970.certified 4465 947 10735676910569 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks300To302

namespace Research6969.PackedRanks.PackedRanks300To302
open Research6969.TransitionBanks
theorem rank300 (u:ℕ) : P3_7_1.BankOK (bank300 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank300 u).shape (by change 2*982≤3200;decide) (by change 3200+982≤4464+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3200-2*982) 982=6*997767489781760:=by decide
  change 6*P1_7_1.nodeRows (bank300 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank300 u).shape=262144*P1_7_1_2.sixPerNode (3200-2*982) 982 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank300 u).shape=997767489781760; omega, moment4464_982,by change 4464<K1.p;decide⟩
theorem rank301 (u:ℕ) : P3_7_1.BankOK (bank301 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank301 u).shape (by change 2*1008≤3200;decide) (by change 3200+1008≤4464+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3200-2*1008) 1008=6*1017717693874176:=by decide
  change 6*P1_7_1.nodeRows (bank301 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank301 u).shape=262144*P1_7_1_2.sixPerNode (3200-2*1008) 1008 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank301 u).shape=1017717693874176; omega, moment4464_1008,by change 4464<K1.p;decide⟩
theorem rank302 (u:ℕ) : P3_7_1.BankOK (bank302 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank302 u).shape (by change 2*947≤3200;decide) (by change 3200+947≤4465+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3200-2*947) 947=6*970564165959680:=by decide
  change 6*P1_7_1.nodeRows (bank302 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank302 u).shape=262144*P1_7_1_2.sixPerNode (3200-2*947) 947 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank302 u).shape=970564165959680; omega, moment4465_947,by change 4465<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks300To302
end Z6969Source0715

-- Source: Research6969.PackedRanks303To305
section Z6969Source0716
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks303To305
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment4465_963 : P1_7_1.groupedPoleMoment 4465 963 ≤ 10877088344236 :=
  _root_.PoleAffine6970.certified 4465 963 10877088344236 (by decide) (by decide +kernel)

theorem moment4465_982 : P1_7_1.groupedPoleMoment 4465 982 ≤ 11043969901736 :=
  _root_.PoleAffine6970.certified 4465 982 11043969901736 (by decide) (by decide +kernel)

theorem moment5504_1244 : P1_7_1.groupedPoleMoment 5504 1244 ≤ 26038250013848 :=
  _root_.PoleAffine6970.certified 5504 1244 26038250013848 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks303To305

namespace Research6969.PackedRanks.PackedRanks303To305
open Research6969.TransitionBanks
theorem rank303 (u:ℕ) : P3_7_1.BankOK (bank303 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank303 u).shape (by change 2*963≤3200;decide) (by change 3200+963≤4465+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3200-2*963) 963=6*983050615259136:=by decide
  change 6*P1_7_1.nodeRows (bank303 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank303 u).shape=262144*P1_7_1_2.sixPerNode (3200-2*963) 963 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank303 u).shape=983050615259136; omega, moment4465_963,by change 4465<K1.p;decide⟩
theorem rank304 (u:ℕ) : P3_7_1.BankOK (bank304 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank304 u).shape (by change 2*982≤3200;decide) (by change 3200+982≤4465+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3200-2*982) 982=6*997767489781760:=by decide
  change 6*P1_7_1.nodeRows (bank304 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank304 u).shape=262144*P1_7_1_2.sixPerNode (3200-2*982) 982 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank304 u).shape=997767489781760; omega, moment4465_982,by change 4465<K1.p;decide⟩
theorem rank305 (u:ℕ) : P3_7_1.BankOK (bank305 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank305 u).shape (by change 2*1244≤3950;decide) (by change 3950+1244≤5504+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3950-2*1244) 1244=6*1913299978158080:=by decide
  change 6*P1_7_1.nodeRows (bank305 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank305 u).shape=262144*P1_7_1_2.sixPerNode (3950-2*1244) 1244 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank305 u).shape=1913299978158080; omega, moment5504_1244,by change 5504<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks303To305
end Z6969Source0716

-- Source: Research6969.TransitionBankChecks16
section Z6969Source0717
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

theorem rank288 (u : ℕ) : P3_7_1.BankOK (bank288 u) :=
  PackedRanks.PackedRanks288To290.rank288 u
theorem rank289 (u : ℕ) : P3_7_1.BankOK (bank289 u) :=
  PackedRanks.PackedRanks288To290.rank289 u
theorem rank290 (u : ℕ) : P3_7_1.BankOK (bank290 u) :=
  PackedRanks.PackedRanks288To290.rank290 u
theorem rank291 (u : ℕ) : P3_7_1.BankOK (bank291 u) :=
  PackedRanks.PackedRanks291To293.rank291 u
theorem rank292 (u : ℕ) : P3_7_1.BankOK (bank292 u) :=
  PackedRanks.PackedRanks291To293.rank292 u
theorem rank293 (u : ℕ) : P3_7_1.BankOK (bank293 u) :=
  PackedRanks.PackedRanks291To293.rank293 u
theorem rank294 (u : ℕ) : P3_7_1.BankOK (bank294 u) :=
  PackedRanks.PackedRanks294To296.rank294 u
theorem rank295 (u : ℕ) : P3_7_1.BankOK (bank295 u) :=
  PackedRanks.PackedRanks294To296.rank295 u
theorem rank296 (u : ℕ) : P3_7_1.BankOK (bank296 u) :=
  PackedRanks.PackedRanks294To296.rank296 u
theorem rank297 (u : ℕ) : P3_7_1.BankOK (bank297 u) :=
  PackedRanks.PackedRanks297To299.rank297 u
theorem rank298 (u : ℕ) : P3_7_1.BankOK (bank298 u) :=
  PackedRanks.PackedRanks297To299.rank298 u
theorem rank299 (u : ℕ) : P3_7_1.BankOK (bank299 u) :=
  PackedRanks.PackedRanks297To299.rank299 u
theorem rank300 (u : ℕ) : P3_7_1.BankOK (bank300 u) :=
  PackedRanks.PackedRanks300To302.rank300 u
theorem rank301 (u : ℕ) : P3_7_1.BankOK (bank301 u) :=
  PackedRanks.PackedRanks300To302.rank301 u
theorem rank302 (u : ℕ) : P3_7_1.BankOK (bank302 u) :=
  PackedRanks.PackedRanks300To302.rank302 u
theorem rank303 (u : ℕ) : P3_7_1.BankOK (bank303 u) :=
  PackedRanks.PackedRanks303To305.rank303 u
theorem rank304 (u : ℕ) : P3_7_1.BankOK (bank304 u) :=
  PackedRanks.PackedRanks303To305.rank304 u
theorem rank305 (u : ℕ) : P3_7_1.BankOK (bank305 u) :=
  PackedRanks.PackedRanks303To305.rank305 u
end Research6969.TransitionBanks
end Z6969Source0717

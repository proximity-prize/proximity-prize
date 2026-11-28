import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0600
import ProximityPrize.SubmissionLower.Z6969Pack0601
import ProximityPrize.SubmissionLower.Z6969Pack0602
import ProximityPrize.SubmissionLower.Z6969Pack0603
import ProximityPrize.SubmissionLower.Z6969Pack0604

set_option Elab.async false

-- Source: Research6969.PackedRanks321To323
section Z6969Source0723
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks321To323
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment6694_1445 : P1_7_1.groupedPoleMoment 6694 1445 ≤ 54952917346103 :=
  _root_.PoleAffine6970.certified 6694 1445 54952917346103 (by decide) (by decide +kernel)

theorem moment6694_1474 : P1_7_1.groupedPoleMoment 6694 1474 ≤ 55810706074581 :=
  _root_.PoleAffine6970.certified 6694 1474 55810706074581 (by decide) (by decide +kernel)

theorem moment6694_1512 : P1_7_1.groupedPoleMoment 6694 1512 ≤ 56926029739529 :=
  _root_.PoleAffine6970.certified 6694 1512 56926029739529 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks321To323

namespace Research6969.PackedRanks.PackedRanks321To323
open Research6969.TransitionBanks
theorem rank321 (u:ℕ) : P3_7_1.BankOK (bank321 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank321 u).shape (by change 2*1445≤4800;decide) (by change 4800+1445≤6694+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1445) 1445=6*3317023033262080:=by decide
  change 6*P1_7_1.nodeRows (bank321 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank321 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1445) 1445 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank321 u).shape=3317023033262080; omega, moment6694_1445,by change 6694<K1.p;decide⟩
theorem rank322 (u:ℕ) : P3_7_1.BankOK (bank322 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank322 u).shape (by change 2*1474≤4800;decide) (by change 4800+1474≤6694+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474=6*3367547627110400:=by decide
  change 6*P1_7_1.nodeRows (bank322 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank322 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1474) 1474 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank322 u).shape=3367547627110400; omega, moment6694_1474,by change 6694<K1.p;decide⟩
theorem rank323 (u:ℕ) : P3_7_1.BankOK (bank323 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank323 u).shape (by change 2*1512≤4800;decide) (by change 4800+1512≤6694+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (4800-2*1512) 1512=6*3433136573644800:=by decide
  change 6*P1_7_1.nodeRows (bank323 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank323 u).shape=262144*P1_7_1_2.sixPerNode (4800-2*1512) 1512 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank323 u).shape=3433136573644800; omega, moment6694_1512,by change 6694<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks321To323
end Z6969Source0723

-- Source: Research6969.TransitionBankChecks17
section Z6969Source0724
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

theorem rank306 (u : ℕ) : P3_7_1.BankOK (bank306 u) :=
  PackedRanks.PackedRanks306To308.rank306 u
theorem rank307 (u : ℕ) : P3_7_1.BankOK (bank307 u) :=
  PackedRanks.PackedRanks306To308.rank307 u
theorem rank308 (u : ℕ) : P3_7_1.BankOK (bank308 u) :=
  PackedRanks.PackedRanks306To308.rank308 u
theorem rank309 (u : ℕ) : P3_7_1.BankOK (bank309 u) :=
  PackedRanks.PackedRanks309To311.rank309 u
theorem rank310 (u : ℕ) : P3_7_1.BankOK (bank310 u) :=
  PackedRanks.PackedRanks309To311.rank310 u
theorem rank311 (u : ℕ) : P3_7_1.BankOK (bank311 u) :=
  PackedRanks.PackedRanks309To311.rank311 u
theorem rank312 (u : ℕ) : P3_7_1.BankOK (bank312 u) :=
  PackedRanks.PackedRanks312To314.rank312 u
theorem rank313 (u : ℕ) : P3_7_1.BankOK (bank313 u) :=
  PackedRanks.PackedRanks312To314.rank313 u
theorem rank314 (u : ℕ) : P3_7_1.BankOK (bank314 u) :=
  PackedRanks.PackedRanks312To314.rank314 u
theorem rank315 (u : ℕ) : P3_7_1.BankOK (bank315 u) :=
  PackedRanks.PackedRanks315To317.rank315 u
theorem rank316 (u : ℕ) : P3_7_1.BankOK (bank316 u) :=
  PackedRanks.PackedRanks315To317.rank316 u
theorem rank317 (u : ℕ) : P3_7_1.BankOK (bank317 u) :=
  PackedRanks.PackedRanks315To317.rank317 u
theorem rank318 (u : ℕ) : P3_7_1.BankOK (bank318 u) :=
  PackedRanks.PackedRanks318To320.rank318 u
theorem rank319 (u : ℕ) : P3_7_1.BankOK (bank319 u) :=
  PackedRanks.PackedRanks318To320.rank319 u
theorem rank320 (u : ℕ) : P3_7_1.BankOK (bank320 u) :=
  PackedRanks.PackedRanks318To320.rank320 u
theorem rank321 (u : ℕ) : P3_7_1.BankOK (bank321 u) :=
  PackedRanks.PackedRanks321To323.rank321 u
theorem rank322 (u : ℕ) : P3_7_1.BankOK (bank322 u) :=
  PackedRanks.PackedRanks321To323.rank322 u
theorem rank323 (u : ℕ) : P3_7_1.BankOK (bank323 u) :=
  PackedRanks.PackedRanks321To323.rank323 u
end Research6969.TransitionBanks
end Z6969Source0724

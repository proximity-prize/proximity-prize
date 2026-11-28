import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0594
import ProximityPrize.SubmissionLower.Z6969Pack0595

set_option Elab.async false

-- Source: Research6969.PackedRanks282To284
section Z6969Source0708
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks282To284
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3991_892 : P1_7_1.groupedPoleMoment 3991 892 ≤ 7140033494115 :=
  _root_.PoleAffine6970.certified 3991 892 7140033494115 (by decide) (by decide +kernel)

theorem moment4037_875 : P1_7_1.groupedPoleMoment 4037 875 ≤ 7298293490304 :=
  _root_.PoleAffine6970.certified 4037 875 7298293490304 (by decide) (by decide +kernel)

theorem moment4038_864 : P1_7_1.groupedPoleMoment 4038 864 ≤ 7232363502162 :=
  _root_.PoleAffine6970.certified 4038 864 7232363502162 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks282To284

namespace Research6969.PackedRanks.PackedRanks282To284
open Research6969.TransitionBanks
theorem rank282 (u:ℕ) : P3_7_1.BankOK (bank282 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank282 u).shape (by change 2*892≤2867;decide) (by change 2867+892≤3991+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2867-2*892) 892=6*725217086799872:=by decide
  change 6*P1_7_1.nodeRows (bank282 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank282 u).shape=262144*P1_7_1_2.sixPerNode (2867-2*892) 892 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank282 u).shape=725217086799872; omega, moment3991_892,by change 3991<K1.p;decide⟩
theorem rank283 (u:ℕ) : P3_7_1.BankOK (bank283 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank283 u).shape (by change 2*875≤2899;decide) (by change 2899+875≤4037+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2899-2*875) 875=6*732681548595200:=by decide
  change 6*P1_7_1.nodeRows (bank283 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank283 u).shape=262144*P1_7_1_2.sixPerNode (2899-2*875) 875 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank283 u).shape=732681548595200; omega, moment4037_875,by change 4037<K1.p;decide⟩
theorem rank284 (u:ℕ) : P3_7_1.BankOK (bank284 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank284 u).shape (by change 2*864≤2899;decide) (by change 2899+864≤4038+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2899-2*864) 864=6*725650419220480:=by decide
  change 6*P1_7_1.nodeRows (bank284 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank284 u).shape=262144*P1_7_1_2.sixPerNode (2899-2*864) 864 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank284 u).shape=725650419220480; omega, moment4038_864,by change 4038<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks282To284
end Z6969Source0708

-- Source: Research6969.PackedRanks285To287
section Z6969Source0709
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks285To287
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment4038_875 : P1_7_1.groupedPoleMoment 4038 875 ≤ 7304113170170 :=
  _root_.PoleAffine6970.certified 4038 875 7304113170170 (by decide) (by decide +kernel)

theorem moment4063_890 : P1_7_1.groupedPoleMoment 4063 890 ≤ 7550005185904 :=
  _root_.PoleAffine6970.certified 4063 890 7550005185904 (by decide) (by decide +kernel)

theorem moment4063_892 : P1_7_1.groupedPoleMoment 4063 892 ≤ 7563211302447 :=
  _root_.PoleAffine6970.certified 4063 892 7563211302447 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks285To287

namespace Research6969.PackedRanks.PackedRanks285To287
open Research6969.TransitionBanks
theorem rank285 (u:ℕ) : P3_7_1.BankOK (bank285 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank285 u).shape (by change 2*875≤2899;decide) (by change 2899+875≤4038+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2899-2*875) 875=6*732681548595200:=by decide
  change 6*P1_7_1.nodeRows (bank285 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank285 u).shape=262144*P1_7_1_2.sixPerNode (2899-2*875) 875 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank285 u).shape=732681548595200; omega, moment4038_875,by change 4038<K1.p;decide⟩
theorem rank286 (u:ℕ) : P3_7_1.BankOK (bank286 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank286 u).shape (by change 2*890≤2917;decide) (by change 2917+890≤4063+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2917-2*890) 890=6*752568113037312:=by decide
  change 6*P1_7_1.nodeRows (bank286 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank286 u).shape=262144*P1_7_1_2.sixPerNode (2917-2*890) 890 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank286 u).shape=752568113037312; omega, moment4063_890,by change 4063<K1.p;decide⟩
theorem rank287 (u:ℕ) : P3_7_1.BankOK (bank287 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank287 u).shape (by change 2*892≤2917;decide) (by change 2917+892≤4063+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2917-2*892) 892=6*753852707766272:=by decide
  change 6*P1_7_1.nodeRows (bank287 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank287 u).shape=262144*P1_7_1_2.sixPerNode (2917-2*892) 892 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank287 u).shape=753852707766272; omega, moment4063_892,by change 4063<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks285To287
end Z6969Source0709

-- Source: Research6969.TransitionBankChecks15
section Z6969Source0710
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

theorem rank270 (u : ℕ) : P3_7_1.BankOK (bank270 u) :=
  PackedRanks.PackedRanks270To272.rank270 u
theorem rank271 (u : ℕ) : P3_7_1.BankOK (bank271 u) :=
  PackedRanks.PackedRanks270To272.rank271 u
theorem rank272 (u : ℕ) : P3_7_1.BankOK (bank272 u) :=
  PackedRanks.PackedRanks270To272.rank272 u
theorem rank273 (u : ℕ) : P3_7_1.BankOK (bank273 u) :=
  PackedRanks.PackedRanks273To275.rank273 u
theorem rank274 (u : ℕ) : P3_7_1.BankOK (bank274 u) :=
  PackedRanks.PackedRanks273To275.rank274 u
theorem rank275 (u : ℕ) : P3_7_1.BankOK (bank275 u) :=
  PackedRanks.PackedRanks273To275.rank275 u
theorem rank276 (u : ℕ) : P3_7_1.BankOK (bank276 u) :=
  PackedRanks.PackedRanks276To278.rank276 u
theorem rank277 (u : ℕ) : P3_7_1.BankOK (bank277 u) :=
  PackedRanks.PackedRanks276To278.rank277 u
theorem rank278 (u : ℕ) : P3_7_1.BankOK (bank278 u) :=
  PackedRanks.PackedRanks276To278.rank278 u
theorem rank279 (u : ℕ) : P3_7_1.BankOK (bank279 u) :=
  PackedRanks.PackedRanks279To281.rank279 u
theorem rank280 (u : ℕ) : P3_7_1.BankOK (bank280 u) :=
  PackedRanks.PackedRanks279To281.rank280 u
theorem rank281 (u : ℕ) : P3_7_1.BankOK (bank281 u) :=
  PackedRanks.PackedRanks279To281.rank281 u
theorem rank282 (u : ℕ) : P3_7_1.BankOK (bank282 u) :=
  PackedRanks.PackedRanks282To284.rank282 u
theorem rank283 (u : ℕ) : P3_7_1.BankOK (bank283 u) :=
  PackedRanks.PackedRanks282To284.rank283 u
theorem rank284 (u : ℕ) : P3_7_1.BankOK (bank284 u) :=
  PackedRanks.PackedRanks282To284.rank284 u
theorem rank285 (u : ℕ) : P3_7_1.BankOK (bank285 u) :=
  PackedRanks.PackedRanks285To287.rank285 u
theorem rank286 (u : ℕ) : P3_7_1.BankOK (bank286 u) :=
  PackedRanks.PackedRanks285To287.rank286 u
theorem rank287 (u : ℕ) : P3_7_1.BankOK (bank287 u) :=
  PackedRanks.PackedRanks285To287.rank287 u
end Research6969.TransitionBanks
end Z6969Source0710

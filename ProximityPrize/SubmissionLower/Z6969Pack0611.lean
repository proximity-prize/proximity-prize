import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0606
import ProximityPrize.SubmissionLower.Z6969Pack0607
import ProximityPrize.SubmissionLower.Z6969Pack0608
import ProximityPrize.SubmissionLower.Z6969Pack0609
import ProximityPrize.SubmissionLower.Z6969Pack0610

set_option Elab.async false

-- Source: Research6969.PackedRanks339To341
section Z6969Source0730
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks339To341
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment7950_1796 : P1_7_1.groupedPoleMoment 7950 1796 ≤ 113242283843565 :=
  _root_.PoleAffine6970.certified 7950 1796 113242283843565 (by decide) (by decide +kernel)

theorem moment7951_1750 : P1_7_1.groupedPoleMoment 7951 1750 ≤ 111025751789870 :=
  _root_.PoleAffine6970.certified 7951 1750 111025751789870 (by decide) (by decide +kernel)

theorem moment7951_1796 : P1_7_1.groupedPoleMoment 7951 1796 ≤ 113288194826317 :=
  _root_.PoleAffine6970.certified 7951 1796 113288194826317 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks339To341

namespace Research6969.PackedRanks.PackedRanks339To341
open Research6969.TransitionBanks
theorem rank339 (u:ℕ) : P3_7_1.BankOK (bank339 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank339 u).shape (by change 2*1796≤5700;decide) (by change 5700+1796≤7950+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1796) 1796=6*5749327563587584:=by decide
  change 6*P1_7_1.nodeRows (bank339 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank339 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1796) 1796 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank339 u).shape=5749327563587584; omega, moment7950_1796,by change 7950<K1.p;decide⟩
theorem rank340 (u:ℕ) : P3_7_1.BankOK (bank340 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank340 u).shape (by change 2*1750≤5700;decide) (by change 5700+1750≤7951+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1750) 1750=6*5637370734182400:=by decide
  change 6*P1_7_1.nodeRows (bank340 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank340 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1750) 1750 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank340 u).shape=5637370734182400; omega, moment7951_1750,by change 7951<K1.p;decide⟩
theorem rank341 (u:ℕ) : P3_7_1.BankOK (bank341 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank341 u).shape (by change 2*1796≤5700;decide) (by change 5700+1796≤7951+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (5700-2*1796) 1796=6*5749327563587584:=by decide
  change 6*P1_7_1.nodeRows (bank341 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank341 u).shape=262144*P1_7_1_2.sixPerNode (5700-2*1796) 1796 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank341 u).shape=5749327563587584; omega, moment7951_1796,by change 7951<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks339To341
end Z6969Source0730

-- Source: Research6969.TransitionBankChecks18
section Z6969Source0731
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

theorem rank324 (u : ℕ) : P3_7_1.BankOK (bank324 u) :=
  PackedRanks.PackedRanks324To326.rank324 u
theorem rank325 (u : ℕ) : P3_7_1.BankOK (bank325 u) :=
  PackedRanks.PackedRanks324To326.rank325 u
theorem rank326 (u : ℕ) : P3_7_1.BankOK (bank326 u) :=
  PackedRanks.PackedRanks324To326.rank326 u
theorem rank327 (u : ℕ) : P3_7_1.BankOK (bank327 u) :=
  PackedRanks.PackedRanks327To329.rank327 u
theorem rank328 (u : ℕ) : P3_7_1.BankOK (bank328 u) :=
  PackedRanks.PackedRanks327To329.rank328 u
theorem rank329 (u : ℕ) : P3_7_1.BankOK (bank329 u) :=
  PackedRanks.PackedRanks327To329.rank329 u
theorem rank330 (u : ℕ) : P3_7_1.BankOK (bank330 u) :=
  PackedRanks.PackedRanks330To332.rank330 u
theorem rank331 (u : ℕ) : P3_7_1.BankOK (bank331 u) :=
  PackedRanks.PackedRanks330To332.rank331 u
theorem rank332 (u : ℕ) : P3_7_1.BankOK (bank332 u) :=
  PackedRanks.PackedRanks330To332.rank332 u
theorem rank333 (u : ℕ) : P3_7_1.BankOK (bank333 u) :=
  PackedRanks.PackedRanks333To335.rank333 u
theorem rank334 (u : ℕ) : P3_7_1.BankOK (bank334 u) :=
  PackedRanks.PackedRanks333To335.rank334 u
theorem rank335 (u : ℕ) : P3_7_1.BankOK (bank335 u) :=
  PackedRanks.PackedRanks333To335.rank335 u
theorem rank336 (u : ℕ) : P3_7_1.BankOK (bank336 u) :=
  PackedRanks.PackedRanks336To338.rank336 u
theorem rank337 (u : ℕ) : P3_7_1.BankOK (bank337 u) :=
  PackedRanks.PackedRanks336To338.rank337 u
theorem rank338 (u : ℕ) : P3_7_1.BankOK (bank338 u) :=
  PackedRanks.PackedRanks336To338.rank338 u
theorem rank339 (u : ℕ) : P3_7_1.BankOK (bank339 u) :=
  PackedRanks.PackedRanks339To341.rank339 u
theorem rank340 (u : ℕ) : P3_7_1.BankOK (bank340 u) :=
  PackedRanks.PackedRanks339To341.rank340 u
theorem rank341 (u : ℕ) : P3_7_1.BankOK (bank341 u) :=
  PackedRanks.PackedRanks339To341.rank341 u
end Research6969.TransitionBanks
end Z6969Source0731

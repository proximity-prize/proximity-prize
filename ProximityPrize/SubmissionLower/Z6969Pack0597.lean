import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks288To290
section Z6969Source0711
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks288To290
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment4063_893 : P1_7_1.groupedPoleMoment 4063 893 ≤ 7569810562400 :=
  _root_.PoleAffine6970.certified 4063 893 7569810562400 (by decide) (by decide +kernel)

theorem moment4064_890 : P1_7_1.groupedPoleMoment 4064 890 ≤ 7555988947369 :=
  _root_.PoleAffine6970.certified 4064 890 7555988947369 (by decide) (by decide +kernel)

theorem moment4117_893 : P1_7_1.groupedPoleMoment 4117 893 ≤ 7898464820375 :=
  _root_.PoleAffine6970.certified 4117 893 7898464820375 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks288To290

namespace Research6969.PackedRanks.PackedRanks288To290
open Research6969.TransitionBanks
theorem rank288 (u:ℕ) : P3_7_1.BankOK (bank288 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank288 u).shape (by change 2*893≤2917;decide) (by change 2917+893≤4063+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2917-2*893) 893=6*754494559748096:=by decide
  change 6*P1_7_1.nodeRows (bank288 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank288 u).shape=262144*P1_7_1_2.sixPerNode (2917-2*893) 893 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank288 u).shape=754494559748096; omega, moment4063_893,by change 4063<K1.p;decide⟩
theorem rank289 (u:ℕ) : P3_7_1.BankOK (bank289 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank289 u).shape (by change 2*890≤2917;decide) (by change 2917+890≤4064+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2917-2*890) 890=6*752568113037312:=by decide
  change 6*P1_7_1.nodeRows (bank289 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank289 u).shape=262144*P1_7_1_2.sixPerNode (2917-2*890) 890 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank289 u).shape=752568113037312; omega, moment4064_890,by change 4064<K1.p;decide⟩
theorem rank290 (u:ℕ) : P3_7_1.BankOK (bank290 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank290 u).shape (by change 2*893≤2956;decide) (by change 2956+893≤4117+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2956-2*893) 893=6*777257512337408:=by decide
  change 6*P1_7_1.nodeRows (bank290 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank290 u).shape=262144*P1_7_1_2.sixPerNode (2956-2*893) 893 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank290 u).shape=777257512337408; omega, moment4117_893,by change 4117<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks288To290
end Z6969Source0711

-- Source: Research6969.PackedRanks291To293
section Z6969Source0712
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks291To293
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment4133_896 : P1_7_1.groupedPoleMoment 4133 896 ≤ 8018620391390 :=
  _root_.PoleAffine6970.certified 4133 896 8018620391390 (by decide) (by decide +kernel)

theorem moment4137_897 : P1_7_1.groupedPoleMoment 4137 897 ≤ 8050621479572 :=
  _root_.PoleAffine6970.certified 4137 897 8050621479572 (by decide) (by decide +kernel)

theorem moment4182_898 : P1_7_1.groupedPoleMoment 4182 898 ≤ 8343071159337 :=
  _root_.PoleAffine6970.certified 4182 898 8343071159337 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks291To293

namespace Research6969.PackedRanks.PackedRanks291To293
open Research6969.TransitionBanks
theorem rank291 (u:ℕ) : P3_7_1.BankOK (bank291 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank291 u).shape (by change 2*896≤2967;decide) (by change 2967+896≤4133+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2967-2*896) 896=6*785746572083200:=by decide
  change 6*P1_7_1.nodeRows (bank291 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank291 u).shape=262144*P1_7_1_2.sixPerNode (2967-2*896) 896 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank291 u).shape=785746572083200; omega, moment4133_896,by change 4133<K1.p;decide⟩
theorem rank292 (u:ℕ) : P3_7_1.BankOK (bank292 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank292 u).shape (by change 2*897≤2970;decide) (by change 2970+897≤4137+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2970-2*897) 897=6*788194070364160:=by decide
  change 6*P1_7_1.nodeRows (bank292 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank292 u).shape=262144*P1_7_1_2.sixPerNode (2970-2*897) 897 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank292 u).shape=788194070364160; omega, moment4137_897,by change 4137<K1.p;decide⟩
theorem rank293 (u:ℕ) : P3_7_1.BankOK (bank293 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank293 u).shape (by change 2*898≤3013;decide) (by change 3013+898≤4182+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3013-2*898) 898=6*814632873492480:=by decide
  change 6*P1_7_1.nodeRows (bank293 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank293 u).shape=262144*P1_7_1_2.sixPerNode (3013-2*898) 898 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank293 u).shape=814632873492480; omega, moment4182_898,by change 4182<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks291To293
end Z6969Source0712

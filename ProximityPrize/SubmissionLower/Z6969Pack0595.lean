import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558

set_option Elab.async false

-- Source: Research6969.PackedRanks276To278
section Z6969Source0706
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks276To278
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3852_866 : P1_7_1.groupedPoleMoment 3852 866 ≤ 6224865038545 :=
  _root_.PoleAffine6970.certified 3852 866 6224865038545 (by decide) (by decide +kernel)

theorem moment3913_874 : P1_7_1.groupedPoleMoment 3913 874 ≤ 6594957993633 :=
  _root_.PoleAffine6970.certified 3913 874 6594957993633 (by decide) (by decide +kernel)

theorem moment3913_880 : P1_7_1.groupedPoleMoment 3913 880 ≤ 6630087774248 :=
  _root_.PoleAffine6970.certified 3913 880 6630087774248 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks276To278

namespace Research6969.PackedRanks.PackedRanks276To278
open Research6969.TransitionBanks
theorem rank276 (u:ℕ) : P3_7_1.BankOK (bank276 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank276 u).shape (by change 2*866≤2767;decide) (by change 2767+866≤3852+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2767-2*866) 866=6*654914606858240:=by decide
  change 6*P1_7_1.nodeRows (bank276 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank276 u).shape=262144*P1_7_1_2.sixPerNode (2767-2*866) 866 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank276 u).shape=654914606858240; omega, moment3852_866,by change 3852<K1.p;decide⟩
theorem rank277 (u:ℕ) : P3_7_1.BankOK (bank277 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank277 u).shape (by change 2*874≤2811;decide) (by change 2811+874≤3913+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2811-2*874) 874=6*683226234880000:=by decide
  change 6*P1_7_1.nodeRows (bank277 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank277 u).shape=262144*P1_7_1_2.sixPerNode (2811-2*874) 874 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank277 u).shape=683226234880000; omega, moment3913_874,by change 3913<K1.p;decide⟩
theorem rank278 (u:ℕ) : P3_7_1.BankOK (bank278 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank278 u).shape (by change 2*880≤2811;decide) (by change 2811+880≤3913+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2811-2*880) 880=6*686774022569984:=by decide
  change 6*P1_7_1.nodeRows (bank278 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank278 u).shape=262144*P1_7_1_2.sixPerNode (2811-2*880) 880 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank278 u).shape=686774022569984; omega, moment3913_880,by change 3913<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks276To278
end Z6969Source0706

-- Source: Research6969.PackedRanks279To281
section Z6969Source0707
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks279To281
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3923_851 : P1_7_1.groupedPoleMoment 3923 851 ≤ 6512804695549 :=
  _root_.PoleAffine6970.certified 3923 851 6512804695549 (by decide) (by decide +kernel)

theorem moment3987_891 : P1_7_1.groupedPoleMoment 3987 891 ≤ 7110809743963 :=
  _root_.PoleAffine6970.certified 3987 891 7110809743963 (by decide) (by decide +kernel)

theorem moment3989_885 : P1_7_1.groupedPoleMoment 3989 885 ≤ 7085003902524 :=
  _root_.PoleAffine6970.certified 3989 885 7085003902524 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks279To281

namespace Research6969.PackedRanks.PackedRanks279To281
open Research6969.TransitionBanks
theorem rank279 (u:ℕ) : P3_7_1.BankOK (bank279 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank279 u).shape (by change 2*851≤2817;decide) (by change 2817+851≤3923+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2817-2*851) 851=6*672733997301760:=by decide
  change 6*P1_7_1.nodeRows (bank279 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank279 u).shape=262144*P1_7_1_2.sixPerNode (2817-2*851) 851 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank279 u).shape=672733997301760; omega, moment3923_851,by change 3923<K1.p;decide⟩
theorem rank280 (u:ℕ) : P3_7_1.BankOK (bank280 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank280 u).shape (by change 2*891≤2864;decide) (by change 2864+891≤3987+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2864-2*891) 891=6*722903184703488:=by decide
  change 6*P1_7_1.nodeRows (bank280 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank280 u).shape=262144*P1_7_1_2.sixPerNode (2864-2*891) 891 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank280 u).shape=722903184703488; omega, moment3987_891,by change 3987<K1.p;decide⟩
theorem rank281 (u:ℕ) : P3_7_1.BankOK (bank281 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank281 u).shape (by change 2*885≤2864;decide) (by change 2864+885≤3989+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2864-2*885) 885=6*719210963271680:=by decide
  change 6*P1_7_1.nodeRows (bank281 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank281 u).shape=262144*P1_7_1_2.sixPerNode (2864-2*885) 885 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank281 u).shape=719210963271680; omega, moment3989_885,by change 3989<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks279To281
end Z6969Source0707

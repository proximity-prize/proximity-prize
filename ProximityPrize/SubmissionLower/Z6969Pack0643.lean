import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0642

set_option Elab.async false

-- Source: Research6969.TerminalRanks20To23
section Z6969Source0884
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks20To23
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment2789_610 : P1_7_1.groupedPoleMoment 2789 610 ≤ 1675899178680 :=
  _root_.PoleAffine6970.certified 2789 610 1675899178680 (by decide) (by decide +kernel)

theorem moment2789_630 : P1_7_1.groupedPoleMoment 2789 630 ≤ 1718433691636 :=
  _root_.PoleAffine6970.certified 2789 630 1718433691636 (by decide) (by decide +kernel)

theorem moment2790_630 : P1_7_1.groupedPoleMoment 2790 630 ≤ 1720419448636 :=
  _root_.PoleAffine6970.certified 2790 630 1720419448636 (by decide) (by decide +kernel)

theorem moment3201_702 : P1_7_1.groupedPoleMoment 3201 702 ≤ 2912992731804 :=
  _root_.PoleAffine6970.certified 3201 702 2912992731804 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks20To23

namespace Research6969.PackedRanks.TerminalRanks20To23
open Research6969.TerminalAuxBanks
theorem rank20 (u:ℕ) : P3_7_1.BankOK (bank20 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank20 u).shape (by change 2*610≤2000;decide) (by change 2000+610≤2789+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2000-2*610) 610=6*242679148707840:=by decide
  change 6*P1_7_1.nodeRows (bank20 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank20 u).shape=262144*P1_7_1_2.sixPerNode (2000-2*610) 610 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank20 u).shape=242679148707840; omega, moment2789_610,by change 2789<K1.p;decide⟩
theorem rank21 (u:ℕ) : P3_7_1.BankOK (bank21 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank21 u).shape (by change 2*630≤2000;decide) (by change 2000+630≤2789+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2000-2*630) 630=6*248682526801920:=by decide
  change 6*P1_7_1.nodeRows (bank21 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank21 u).shape=262144*P1_7_1_2.sixPerNode (2000-2*630) 630 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank21 u).shape=248682526801920; omega, moment2789_630,by change 2789<K1.p;decide⟩
theorem rank22 (u:ℕ) : P3_7_1.BankOK (bank22 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank22 u).shape (by change 2*630≤2000;decide) (by change 2000+630≤2790+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2000-2*630) 630=6*248682526801920:=by decide
  change 6*P1_7_1.nodeRows (bank22 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank22 u).shape=262144*P1_7_1_2.sixPerNode (2000-2*630) 630 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank22 u).shape=248682526801920; omega, moment2790_630,by change 2790<K1.p;decide⟩
theorem rank23 (u:ℕ) : P3_7_1.BankOK (bank23 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank23 u).shape (by change 2*702≤2300;decide) (by change 2300+702≤3201+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*702) 702=6*369170633195520:=by decide
  change 6*P1_7_1.nodeRows (bank23 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank23 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*702) 702 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank23 u).shape=369170633195520; omega, moment3201_702,by change 3201<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks20To23
end Z6969Source0884

-- Source: Research6969.TerminalRanks24To27
section Z6969Source0885
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks24To27
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3203_702 : P1_7_1.groupedPoleMoment 3203 702 ≤ 2918855628076 :=
  _root_.PoleAffine6970.certified 3203 702 2918855628076 (by decide) (by decide +kernel)

theorem moment3203_724 : P1_7_1.groupedPoleMoment 3203 724 ≤ 2989680899568 :=
  _root_.PoleAffine6970.certified 3203 724 2989680899568 (by decide) (by decide +kernel)

theorem moment3204_702 : P1_7_1.groupedPoleMoment 3204 702 ≤ 2921790084349 :=
  _root_.PoleAffine6970.certified 3204 702 2921790084349 (by decide) (by decide +kernel)

theorem moment3204_724 : P1_7_1.groupedPoleMoment 3204 724 ≤ 2992689220368 :=
  _root_.PoleAffine6970.certified 3204 724 2992689220368 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks24To27

namespace Research6969.PackedRanks.TerminalRanks24To27
open Research6969.TerminalAuxBanks
theorem rank24 (u:ℕ) : P3_7_1.BankOK (bank24 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank24 u).shape (by change 2*702≤2300;decide) (by change 2300+702≤3203+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*702) 702=6*369170633195520:=by decide
  change 6*P1_7_1.nodeRows (bank24 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank24 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*702) 702 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank24 u).shape=369170633195520; omega, moment3203_702,by change 3203<K1.p;decide⟩
theorem rank25 (u:ℕ) : P3_7_1.BankOK (bank25 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank25 u).shape (by change 2*724≤2300;decide) (by change 2300+724≤3203+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*724) 724=6*377903408742400:=by decide
  change 6*P1_7_1.nodeRows (bank25 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank25 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*724) 724 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank25 u).shape=377903408742400; omega, moment3203_724,by change 3203<K1.p;decide⟩
theorem rank26 (u:ℕ) : P3_7_1.BankOK (bank26 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank26 u).shape (by change 2*702≤2300;decide) (by change 2300+702≤3204+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*702) 702=6*369170633195520:=by decide
  change 6*P1_7_1.nodeRows (bank26 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank26 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*702) 702 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank26 u).shape=369170633195520; omega, moment3204_702,by change 3204<K1.p;decide⟩
theorem rank27 (u:ℕ) : P3_7_1.BankOK (bank27 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank27 u).shape (by change 2*724≤2300;decide) (by change 2300+724≤3204+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2300-2*724) 724=6*377903408742400:=by decide
  change 6*P1_7_1.nodeRows (bank27 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank27 u).shape=262144*P1_7_1_2.sixPerNode (2300-2*724) 724 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank27 u).shape=377903408742400; omega, moment3204_724,by change 3204<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks24To27
end Z6969Source0885

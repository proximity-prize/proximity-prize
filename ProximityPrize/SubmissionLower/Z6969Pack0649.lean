import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0642
import ProximityPrize.SubmissionLower.Z6969Pack0641
import ProximityPrize.SubmissionLower.Z6969Pack0640
import ProximityPrize.SubmissionLower.Z6969Pack0643
import ProximityPrize.SubmissionLower.Z6969Pack0644
import ProximityPrize.SubmissionLower.Z6969Pack0645
import ProximityPrize.SubmissionLower.Z6969Pack0646
import ProximityPrize.SubmissionLower.Z6969Pack0647
import ProximityPrize.SubmissionLower.Z6969Pack0648
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound

set_option Elab.async false

-- Source: Research6969.TerminalRanks72To75
section Z6969Source0892
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks72To75
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3907_854 : P1_7_1.groupedPoleMoment 3907 854 ≤ 6445344460182 :=
  _root_.PoleAffine6970.certified 3907 854 6445344460182 (by decide) (by decide +kernel)

theorem moment4175_870 : P1_7_1.groupedPoleMoment 4175 870 ≤ 8095188217725 :=
  _root_.PoleAffine6970.certified 4175 870 8095188217725 (by decide) (by decide +kernel)

theorem moment4175_894 : P1_7_1.groupedPoleMoment 4175 894 ≤ 8269353083383 :=
  _root_.PoleAffine6970.certified 4175 894 8269353083383 (by decide) (by decide +kernel)

theorem moment4178_894 : P1_7_1.groupedPoleMoment 4178 894 ≤ 8288484232853 :=
  _root_.PoleAffine6970.certified 4178 894 8288484232853 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks72To75

namespace Research6969.PackedRanks.TerminalRanks72To75
open Research6969.TerminalAuxBanks
theorem rank72 (u:ℕ) : P3_7_1.BankOK (bank72 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank72 u).shape (by change 2*854≤2800;decide) (by change 2800+854≤3907+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*854) 854=6*665461916958720:=by decide
  change 6*P1_7_1.nodeRows (bank72 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank72 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*854) 854 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank72 u).shape=665461916958720; omega, moment3907_854,by change 3907<K1.p;decide⟩
theorem rank73 (u:ℕ) : P3_7_1.BankOK (bank73 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank73 u).shape (by change 2*870≤3000;decide) (by change 3000+870≤4175+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3000-2*870) 870=6*787488727367680:=by decide
  change 6*P1_7_1.nodeRows (bank73 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank73 u).shape=262144*P1_7_1_2.sixPerNode (3000-2*870) 870 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank73 u).shape=787488727367680; omega, moment4175_870,by change 4175<K1.p;decide⟩
theorem rank74 (u:ℕ) : P3_7_1.BankOK (bank74 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank74 u).shape (by change 2*894≤3000;decide) (by change 3000+894≤4175+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3000-2*894) 894=6*804053213511680:=by decide
  change 6*P1_7_1.nodeRows (bank74 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank74 u).shape=262144*P1_7_1_2.sixPerNode (3000-2*894) 894 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank74 u).shape=804053213511680; omega, moment4175_894,by change 4175<K1.p;decide⟩
theorem rank75 (u:ℕ) : P3_7_1.BankOK (bank75 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank75 u).shape (by change 2*894≤3000;decide) (by change 3000+894≤4178+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (3000-2*894) 894=6*804053213511680:=by decide
  change 6*P1_7_1.nodeRows (bank75 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank75 u).shape=262144*P1_7_1_2.sixPerNode (3000-2*894) 894 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank75 u).shape=804053213511680; omega, moment4178_894,by change 4178<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks72To75
end Z6969Source0892

-- Source: Research6969.OrdSource00
section Z6969Source0893
set_option autoImplicit true
namespace Research6969.OrdSource
set_option maxHeartbeats 0
set_option maxRecDepth 20000
private def src0:PhysicalWindow.Request := ⟨⟨⟨2800,3906,882,28173⟩,681932636815360,6603573924229⟩,32,1,1,128659,36⟩
private theorem shift0_2314 : (PhysicalWindow.Triangular src0) 2314 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift0_2325 : (PhysicalWindow.Triangular src0) 2325 2354 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift0_2355 : (PhysicalWindow.Triangular src0) 2355 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover0 : PhysicalWindow.Cover (PhysicalWindow.Triangular src0) 2411 2314 [2324, 2354, 2411] := by
  exact ⟨by decide, by decide, shift0_2314, by decide, by decide, shift0_2325, by decide, by decide, shift0_2355, rfl⟩
def row0:OrdinaryBounds.Source 2314 2411:=
  ⟨src0,⟨Research6969.PackedRanks.TerminalRanks68To71.rank70 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover0⟩⟩
private def src1:PhysicalWindow.Request := ⟨⟨⟨2600,3626,793,28173⟩,532875289296896,4784491173220⟩,63,1,1,128659,48⟩
private theorem shift1_2314 : (PhysicalWindow.Triangular src1) 2314 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift1_2330 : (PhysicalWindow.Triangular src1) 2330 2374 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift1_2375 : (PhysicalWindow.Triangular src1) 2375 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover1 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1) 2411 2314 [2329, 2374, 2411] := by
  exact ⟨by decide, by decide, shift1_2314, by decide, by decide, shift1_2330, by decide, by decide, shift1_2375, rfl⟩
def row1:OrdinaryBounds.Source 2314 2411:=
  ⟨src1,⟨Research6969.PackedRanks.TerminalRanks48To51.rank48 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover1⟩⟩
private def src2:PhysicalWindow.Request := ⟨⟨⟨2600,3626,819,25043⟩,546063062138880,4905972788959⟩,63,1,1,128659,48⟩
private theorem shift2_2314 : (PhysicalWindow.Triangular src2) 2314 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift2_2326 : (PhysicalWindow.Triangular src2) 2326 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift2_2360 : (PhysicalWindow.Triangular src2) 2360 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover2 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2) 2411 2314 [2325, 2359, 2411] := by
  exact ⟨by decide, by decide, shift2_2314, by decide, by decide, shift2_2326, by decide, by decide, shift2_2360, rfl⟩
def row2:OrdinaryBounds.Source 2314 2411:=
  ⟨src2,⟨Research6969.TransitionBanks.rank265 25043, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover2⟩⟩
def row3:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src8,⟨Research6969.PackedRanks.TerminalRanks28To31.rank31 25043, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover8⟩⟩
def row4:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src9,⟨Research6969.PackedRanks.TerminalRanks60To63.rank62 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover9⟩⟩
private def src5:PhysicalWindow.Request := ⟨⟨⟨2800,3901,834,45081⟩,653560508579840,6296101689637⟩,195,1,1,128659,161⟩
private theorem shift5_2314 : (PhysicalWindow.Triangular src5) 2314 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift5_2317 : (PhysicalWindow.Triangular src5) 2317 2325 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift5_2326 : (PhysicalWindow.Triangular src5) 2326 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift5_2352 : (PhysicalWindow.Triangular src5) 2352 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover5 : PhysicalWindow.Cover (PhysicalWindow.Triangular src5) 2411 2314 [2316, 2325, 2351, 2411] := by
  exact ⟨by decide, by decide, shift5_2314, by decide, by decide, shift5_2317, by decide, by decide, shift5_2326, by decide, by decide, shift5_2352, rfl⟩
def row5:OrdinaryBounds.Source 2314 2411:=
  ⟨src5,⟨Research6969.PackedRanks.OrdRanks4To5.rank5 45081, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover5⟩⟩
def row6:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src14,⟨Research6969.PackedRanks.TerminalRanks24To27.rank25 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover14⟩⟩
def row7:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src15,⟨Research6969.PackedRanks.TerminalRanks16To19.rank16 50419, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover15⟩⟩
private def src8:PhysicalWindow.Request := ⟨⟨⟨2600,3620,775,63811⟩,523640687820800,4674619806217⟩,250,1,1,128659,513⟩
private theorem shift8_2314 : (PhysicalWindow.Triangular src8) 2314 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift8_2320 : (PhysicalWindow.Triangular src8) 2320 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift8_2337 : (PhysicalWindow.Triangular src8) 2337 2385 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift8_2386 : (PhysicalWindow.Triangular src8) 2386 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover8 : PhysicalWindow.Cover (PhysicalWindow.Triangular src8) 2411 2314 [2319, 2336, 2385, 2411] := by
  exact ⟨by decide, by decide, shift8_2314, by decide, by decide, shift8_2320, by decide, by decide, shift8_2337, by decide, by decide, shift8_2386, rfl⟩
def row8:OrdinaryBounds.Source 2314 2411:=
  ⟨src8,⟨Research6969.PackedRanks.TerminalRanks36To39.rank38 63811, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover8⟩⟩
def row9:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src18,⟨Research6969.PackedRanks.TerminalRanks20To23.rank23 79852, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover18⟩⟩
def row10:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src20,⟨Research6969.PackedRanks.TerminalRanks56To59.rank57 112233, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover20⟩⟩
def row11:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src21,⟨Research6969.PackedRanks.TerminalRanks0To3.rank2 54645, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover21⟩⟩
def row12:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src23,⟨Research6969.PackedRanks.TerminalRanks0To3.rank1 53925, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover23⟩⟩
private def src13:PhysicalWindow.Request := ⟨⟨⟨720,1001,220,67332⟩,11385734430720,28064233768⟩,85,1,1,128659,16385⟩
private theorem shift13_2314 : (PhysicalWindow.Triangular src13) 2314 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift13_2320 : (PhysicalWindow.Triangular src13) 2320 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift13_2338 : (PhysicalWindow.Triangular src13) 2338 2392 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift13_2393 : (PhysicalWindow.Triangular src13) 2393 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover13 : PhysicalWindow.Cover (PhysicalWindow.Triangular src13) 2411 2314 [2319, 2337, 2392, 2411] := by
  exact ⟨by decide, by decide, shift13_2314, by decide, by decide, shift13_2320, by decide, by decide, shift13_2338, by decide, by decide, shift13_2393, rfl⟩
def row13:OrdinaryBounds.Source 2314 2411:=
  ⟨src13,⟨Research6969.PackedRanks.OrdRanks0To3.rank0 67332, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover13⟩⟩
def row14:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src24,⟨Research6969.PackedRanks.TerminalRanks0To3.rank0 94584, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover24⟩⟩
def row15:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src38,⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover38⟩⟩
end Research6969.OrdSource
end Z6969Source0893

-- Source: Research6969.PhysicalChecks004
section Z6969Source0894
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src52 : Request := ⟨⟨⟨2800,3905,882,26837⟩,681932636815360,6598128215989⟩,63,2,1,257319,43⟩
theorem cover52 : PhysicalWindow.Cover (PhysicalWindow.Triangular src52) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src53 : Request := ⟨⟨⟨2600,3626,793,26833⟩,532875289296896,4784491173220⟩,63,2,1,257319,45⟩
theorem cover53 : PhysicalWindow.Cover (PhysicalWindow.Triangular src53) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src54 : Request := ⟨⟨⟨2600,3626,793,28173⟩,532875289296896,4784491173220⟩,63,2,1,257319,45⟩
theorem cover54 : PhysicalWindow.Cover (PhysicalWindow.Triangular src54) 2411 2314 [2323, 2352, 2411] := triangleCover (by decide +kernel)
def src55 : Request := ⟨⟨⟨2652,3691,830,31417⟩,576642060910592,5249056297887⟩,70,2,1,257319,45⟩
theorem cover55 : PhysicalWindow.Cover (PhysicalWindow.Triangular src55) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src56 : Request := ⟨⟨⟨2811,3913,874,28120⟩,683226234880000,6594957993633⟩,71,2,1,257319,45⟩
theorem cover56 : PhysicalWindow.Cover (PhysicalWindow.Triangular src56) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src57 : Request := ⟨⟨⟨2767,3852,866,28077⟩,654914606858240,6224865038545⟩,73,2,1,257319,46⟩
theorem cover57 : PhysicalWindow.Cover (PhysicalWindow.Triangular src57) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src58 : Request := ⟨⟨⟨2300,3207,724,27091⟩,377903408742400,3001726552718⟩,63,2,1,257319,47⟩
theorem cover58 : PhysicalWindow.Cover (PhysicalWindow.Triangular src58) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src59 : Request := ⟨⟨⟨2300,3207,724,28173⟩,377903408742400,3001726552718⟩,63,2,1,257319,47⟩
theorem cover59 : PhysicalWindow.Cover (PhysicalWindow.Triangular src59) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src60 : Request := ⟨⟨⟨2300,3207,702,28173⟩,369170633195520,2930605494152⟩,63,2,1,257319,48⟩
theorem cover60 : PhysicalWindow.Cover (PhysicalWindow.Triangular src60) 2411 2314 [2320, 2340, 2397, 2411] := triangleCover (by decide +kernel)
def src61 : Request := ⟨⟨⟨2300,3207,724,23869⟩,377903408742400,3001726552718⟩,63,2,1,257319,48⟩
theorem cover61 : PhysicalWindow.Cover (PhysicalWindow.Triangular src61) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src62 : Request := ⟨⟨⟨2300,3207,702,23906⟩,369170633195520,2930605494152⟩,63,2,1,257319,49⟩
theorem cover62 : PhysicalWindow.Cover (PhysicalWindow.Triangular src62) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src63 : Request := ⟨⟨⟨2300,3207,702,25043⟩,369170633195520,2930605494152⟩,63,2,1,257319,49⟩
theorem cover63 : PhysicalWindow.Cover (PhysicalWindow.Triangular src63) 2411 2314 [2324, 2355, 2411] := triangleCover (by decide +kernel)
def src64 : Request := ⟨⟨⟨2800,3905,882,30467⟩,681932636815360,6598128215989⟩,85,2,1,257319,50⟩
theorem cover64 : PhysicalWindow.Cover (PhysicalWindow.Triangular src64) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src65 : Request := ⟨⟨⟨2800,3905,882,31694⟩,681932636815360,6598128215989⟩,85,2,1,257319,50⟩
theorem cover65 : PhysicalWindow.Cover (PhysicalWindow.Triangular src65) 2411 2314 [2320, 2340, 2396, 2411] := triangleCover (by decide +kernel)
def src66 : Request := ⟨⟨⟨2800,3905,854,30758⟩,665461916958720,6434729640882⟩,85,2,1,257319,51⟩
theorem cover66 : PhysicalWindow.Cover (PhysicalWindow.Triangular src66) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src67 : Request := ⟨⟨⟨2800,3905,854,31694⟩,665461916958720,6434729640882⟩,85,2,1,257319,51⟩
theorem cover67 : PhysicalWindow.Cover (PhysicalWindow.Triangular src67) 2411 2314 [2319, 2336, 2384, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0894

-- Source: Research6969.PhysicalChecks005
section Z6969Source0895
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src68 : Request := ⟨⟨⟨2800,3905,854,31694⟩,665461916958720,6434729640882⟩,85,2,1,257319,52⟩
theorem cover68 : PhysicalWindow.Cover (PhysicalWindow.Triangular src68) 2411 2314 [2333, 2390, 2411] := triangleCover (by decide +kernel)
def src69 : Request := ⟨⟨⟨2800,3905,882,27027⟩,681932636815360,6598128215989⟩,85,2,1,257319,52⟩
theorem cover69 : PhysicalWindow.Cover (PhysicalWindow.Triangular src69) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src70 : Request := ⟨⟨⟨2600,3625,819,31694⟩,546063062138880,4901614794409⟩,85,2,1,257319,53⟩
theorem cover70 : PhysicalWindow.Cover (PhysicalWindow.Triangular src70) 2411 2314 [2324, 2355, 2411] := triangleCover (by decide +kernel)
def src71 : Request := ⟨⟨⟨2800,3905,854,27446⟩,665461916958720,6434729640882⟩,85,2,1,257319,53⟩
theorem cover71 : PhysicalWindow.Cover (PhysicalWindow.Triangular src71) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src72 : Request := ⟨⟨⟨2600,3625,793,31694⟩,532875289296896,4780245027563⟩,85,2,1,257319,54⟩
theorem cover72 : PhysicalWindow.Cover (PhysicalWindow.Triangular src72) 2411 2314 [2323, 2351, 2411] := triangleCover (by decide +kernel)
def src73 : Request := ⟨⟨⟨2600,3625,819,26892⟩,546063062138880,4901614794409⟩,85,2,1,257319,54⟩
theorem cover73 : PhysicalWindow.Cover (PhysicalWindow.Triangular src73) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src74 : Request := ⟨⟨⟨2600,3625,793,27416⟩,532875289296896,4780245027563⟩,85,2,1,257319,55⟩
theorem cover74 : PhysicalWindow.Cover (PhysicalWindow.Triangular src74) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src75 : Request := ⟨⟨⟨2600,3625,793,28173⟩,532875289296896,4780245027563⟩,85,2,1,257319,55⟩
theorem cover75 : PhysicalWindow.Cover (PhysicalWindow.Triangular src75) 2411 2314 [2321, 2343, 2406, 2411] := triangleCover (by decide +kernel)
def src76 : Request := ⟨⟨⟨2600,3625,775,31694⟩,523640687820800,4695421657977⟩,85,2,1,257319,56⟩
theorem cover76 : PhysicalWindow.Cover (PhysicalWindow.Triangular src76) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src77 : Request := ⟨⟨⟨2600,3625,819,24753⟩,546063062138880,4901614794409⟩,85,2,1,257319,56⟩
theorem cover77 : PhysicalWindow.Cover (PhysicalWindow.Triangular src77) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src78 : Request := ⟨⟨⟨2600,3625,775,31694⟩,523640687820800,4695421657977⟩,85,2,1,257319,57⟩
theorem cover78 : PhysicalWindow.Cover (PhysicalWindow.Triangular src78) 2411 2314 [2328, 2371, 2411] := triangleCover (by decide +kernel)
def src79 : Request := ⟨⟨⟨2600,3625,819,24021⟩,546063062138880,4901614794409⟩,85,2,1,257319,57⟩
theorem cover79 : PhysicalWindow.Cover (PhysicalWindow.Triangular src79) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src80 : Request := ⟨⟨⟨2600,3625,775,28173⟩,523640687820800,4695421657977⟩,85,2,1,257319,58⟩
theorem cover80 : PhysicalWindow.Cover (PhysicalWindow.Triangular src80) 2411 2314 [2322, 2348, 2411] := triangleCover (by decide +kernel)
def src81 : Request := ⟨⟨⟨2600,3625,793,24494⟩,532875289296896,4780245027563⟩,85,2,1,257319,58⟩
theorem cover81 : PhysicalWindow.Cover (PhysicalWindow.Triangular src81) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src82 : Request := ⟨⟨⟨2300,3207,724,26989⟩,377903408742400,3001726552718⟩,85,2,1,257319,59⟩
theorem cover82 : PhysicalWindow.Cover (PhysicalWindow.Triangular src82) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src83 : Request := ⟨⟨⟨2300,3207,724,28173⟩,377903408742400,3001726552718⟩,85,2,1,257319,59⟩
theorem cover83 : PhysicalWindow.Cover (PhysicalWindow.Triangular src83) 2411 2314 [2319, 2336, 2384, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0895

-- Source: Research6969.PhysicalChecks006
section Z6969Source0896
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src84 : Request := ⟨⟨⟨2300,3207,702,28173⟩,369170633195520,2930605494152⟩,85,2,1,257319,61⟩
theorem cover84 : PhysicalWindow.Cover (PhysicalWindow.Triangular src84) 2411 2314 [2327, 2367, 2411] := triangleCover (by decide +kernel)
def src85 : Request := ⟨⟨⟨2300,3207,724,23957⟩,377903408742400,3001726552718⟩,85,2,1,257319,61⟩
theorem cover85 : PhysicalWindow.Cover (PhysicalWindow.Triangular src85) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src86 : Request := ⟨⟨⟨2800,3903,854,35655⟩,665461916958720,6424126719762⟩,115,2,1,257319,65⟩
theorem cover86 : PhysicalWindow.Cover (PhysicalWindow.Triangular src86) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src87 : Request := ⟨⟨⟨2800,3903,882,31059⟩,681932636815360,6587245977411⟩,115,2,1,257319,65⟩
theorem cover87 : PhysicalWindow.Cover (PhysicalWindow.Triangular src87) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src88 : Request := ⟨⟨⟨2800,3902,834,40111⟩,653560508579840,6301295063987⟩,150,2,1,257319,97⟩
theorem cover88 : PhysicalWindow.Cover (PhysicalWindow.Triangular src88) 2411 2314 [2328, 2371, 2411] := triangleCover (by decide +kernel)
def src89 : Request := ⟨⟨⟨2800,3902,854,31475⟩,665461916958720,6418829718882⟩,150,2,1,257319,97⟩
theorem cover89 : PhysicalWindow.Cover (PhysicalWindow.Triangular src89) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src90 : Request := ⟨⟨⟨2300,3204,702,35337⟩,369170633195520,2921790084349⟩,150,2,1,257319,129⟩
theorem cover90 : PhysicalWindow.Cover (PhysicalWindow.Triangular src90) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src91 : Request := ⟨⟨⟨2300,3204,702,35722⟩,369170633195520,2921790084349⟩,150,2,1,257319,129⟩
theorem cover91 : PhysicalWindow.Cover (PhysicalWindow.Triangular src91) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src92 : Request := ⟨⟨⟨2300,3203,702,50764⟩,369170633195520,2918855628076⟩,195,2,1,257319,257⟩
theorem cover92 : PhysicalWindow.Cover (PhysicalWindow.Triangular src92) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src93 : Request := ⟨⟨⟨3000,4178,894,60667⟩,804053213511680,8288484232853⟩,250,2,1,257319,257⟩
theorem cover93 : PhysicalWindow.Cover (PhysicalWindow.Triangular src93) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src94 : Request := ⟨⟨⟨1200,1670,378,35412⟩,53798525730816,221692026804⟩,115,2,1,257319,513⟩
theorem cover94 : PhysicalWindow.Cover (PhysicalWindow.Triangular src94) 2411 2314 [2319, 2337, 2389, 2411] := triangleCover (by decide +kernel)
def src95 : Request := ⟨⟨⟨2600,3620,775,61328⟩,523640687820800,4674619806217⟩,250,2,1,257319,513⟩
theorem cover95 : PhysicalWindow.Cover (PhysicalWindow.Triangular src95) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src96 : Request := ⟨⟨⟨2300,3201,702,79852⟩,369170633195520,2912992731804⟩,250,2,1,257319,1025⟩
theorem cover96 : PhysicalWindow.Cover (PhysicalWindow.Triangular src96) 2411 2314 [2321, 2343, 2406, 2411] := triangleCover (by decide +kernel)
def src97 : Request := ⟨⟨⟨3000,4175,894,118360⟩,804053213511680,8269353083383⟩,325,2,1,257319,1025⟩
theorem cover97 : PhysicalWindow.Cover (PhysicalWindow.Triangular src97) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src98 : Request := ⟨⟨⟨2800,3896,854,107855⟩,665461916958720,6387110095257⟩,325,2,1,257319,2049⟩
theorem cover98 : PhysicalWindow.Cover (PhysicalWindow.Triangular src98) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src99 : Request := ⟨⟨⟨2800,3896,854,112233⟩,665461916958720,6387110095257⟩,325,2,1,257319,2049⟩
theorem cover99 : PhysicalWindow.Cover (PhysicalWindow.Triangular src99) 2411 2314 [2320, 2340, 2397, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0896

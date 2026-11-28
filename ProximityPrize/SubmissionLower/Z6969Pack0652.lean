import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0642
import ProximityPrize.SubmissionLower.Z6969Pack0640
import ProximityPrize.SubmissionLower.Z6969Pack0649
import ProximityPrize.SubmissionLower.Z6969Pack0644
import ProximityPrize.SubmissionLower.Z6969Pack0650
import ProximityPrize.SubmissionLower.Z6969Pack0648
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0641
import ProximityPrize.SubmissionLower.Z6969Pack0643
import ProximityPrize.SubmissionLower.Z6969Pack0646
import ProximityPrize.SubmissionLower.Z6969Pack0647
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound

set_option Elab.async false

-- merged module Z6969Pack0651
section Merged_Z6969Pack0651

-- Source: Research6969.TerminalRanks64To67
section Z6969Source0899
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks64To67
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3903_854 : P1_7_1.groupedPoleMoment 3903 854 ≤ 6424126719762 :=
  _root_.PoleAffine6970.certified 3903 854 6424126719762 (by decide) (by decide +kernel)

theorem moment3903_882 : P1_7_1.groupedPoleMoment 3903 882 ≤ 6587245977411 :=
  _root_.PoleAffine6970.certified 3903 882 6587245977411 (by decide) (by decide +kernel)

theorem moment3905_854 : P1_7_1.groupedPoleMoment 3905 854 ≤ 6434729640882 :=
  _root_.PoleAffine6970.certified 3905 854 6434729640882 (by decide) (by decide +kernel)

theorem moment3905_882 : P1_7_1.groupedPoleMoment 3905 882 ≤ 6598128215989 :=
  _root_.PoleAffine6970.certified 3905 882 6598128215989 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks64To67

namespace Research6969.PackedRanks.TerminalRanks64To67
open Research6969.TerminalAuxBanks
theorem rank64 (u:ℕ) : P3_7_1.BankOK (bank64 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank64 u).shape (by change 2*854≤2800;decide) (by change 2800+854≤3903+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*854) 854=6*665461916958720:=by decide
  change 6*P1_7_1.nodeRows (bank64 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank64 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*854) 854 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank64 u).shape=665461916958720; omega, moment3903_854,by change 3903<K1.p;decide⟩
theorem rank65 (u:ℕ) : P3_7_1.BankOK (bank65 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank65 u).shape (by change 2*882≤2800;decide) (by change 2800+882≤3903+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*882) 882=6*681932636815360:=by decide
  change 6*P1_7_1.nodeRows (bank65 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank65 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*882) 882 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank65 u).shape=681932636815360; omega, moment3903_882,by change 3903<K1.p;decide⟩
theorem rank66 (u:ℕ) : P3_7_1.BankOK (bank66 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank66 u).shape (by change 2*854≤2800;decide) (by change 2800+854≤3905+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*854) 854=6*665461916958720:=by decide
  change 6*P1_7_1.nodeRows (bank66 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank66 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*854) 854 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank66 u).shape=665461916958720; omega, moment3905_854,by change 3905<K1.p;decide⟩
theorem rank67 (u:ℕ) : P3_7_1.BankOK (bank67 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank67 u).shape (by change 2*882≤2800;decide) (by change 2800+882≤3905+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2800-2*882) 882=6*681932636815360:=by decide
  change 6*P1_7_1.nodeRows (bank67 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank67 u).shape=262144*P1_7_1_2.sixPerNode (2800-2*882) 882 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank67 u).shape=681932636815360; omega, moment3905_882,by change 3905<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks64To67
end Z6969Source0899

-- Source: Research6969.OrdSource01
section Z6969Source0900
set_option autoImplicit true
namespace Research6969.OrdSource
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def row16:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src40,⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover40⟩⟩
def row17:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src43,⟨Research6969.TransitionBanks.rank268 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover43⟩⟩
private def src18:PhysicalWindow.Request := ⟨⟨⟨2800,3906,882,28173⟩,681932636815360,6603573924229⟩,32,2,1,257319,33⟩
private theorem shift18_2314 : (PhysicalWindow.Triangular src18) 2314 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift18_2317 : (PhysicalWindow.Triangular src18) 2317 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift18_2325 : (PhysicalWindow.Triangular src18) 2325 2346 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift18_2347 : (PhysicalWindow.Triangular src18) 2347 2408 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift18_2409 : (PhysicalWindow.Triangular src18) 2409 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover18 : PhysicalWindow.Cover (PhysicalWindow.Triangular src18) 2411 2314 [2316, 2324, 2346, 2408, 2411] := by
  exact ⟨by decide, by decide, shift18_2314, by decide, by decide, shift18_2317, by decide, by decide, shift18_2325, by decide, by decide, shift18_2347, by decide, by decide, shift18_2409, rfl⟩
def row18:OrdinaryBounds.Source 2314 2411:=
  ⟨src18,⟨Research6969.PackedRanks.TerminalRanks68To71.rank70 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover18⟩⟩
private def src19:PhysicalWindow.Request := ⟨⟨⟨2800,3906,882,31694⟩,681932636815360,6603573924229⟩,45,2,1,257319,36⟩
private theorem shift19_2314 : (PhysicalWindow.Triangular src19) 2314 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift19_2318 : (PhysicalWindow.Triangular src19) 2318 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift19_2329 : (PhysicalWindow.Triangular src19) 2329 2359 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift19_2360 : (PhysicalWindow.Triangular src19) 2360 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover19 : PhysicalWindow.Cover (PhysicalWindow.Triangular src19) 2411 2314 [2317, 2328, 2359, 2411] := by
  exact ⟨by decide, by decide, shift19_2314, by decide, by decide, shift19_2318, by decide, by decide, shift19_2329, by decide, by decide, shift19_2360, rfl⟩
def row19:OrdinaryBounds.Source 2314 2411:=
  ⟨src19,⟨Research6969.PackedRanks.TerminalRanks68To71.rank70 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover19⟩⟩
def row20:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src49,⟨Research6969.PackedRanks.TerminalRanks32To35.rank33 25043, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover49⟩⟩
private def src21:PhysicalWindow.Request := ⟨⟨⟨2300,3208,724,22261⟩,377903408742400,3004743122568⟩,45,2,1,257319,41⟩
private theorem shift21_2314 : (PhysicalWindow.Triangular src21) 2314 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift21_2320 : (PhysicalWindow.Triangular src21) 2320 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift21_2337 : (PhysicalWindow.Triangular src21) 2337 2384 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift21_2385 : (PhysicalWindow.Triangular src21) 2385 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover21 : PhysicalWindow.Cover (PhysicalWindow.Triangular src21) 2411 2314 [2319, 2336, 2384, 2411] := by
  exact ⟨by decide, by decide, shift21_2314, by decide, by decide, shift21_2320, by decide, by decide, shift21_2337, by decide, by decide, shift21_2385, rfl⟩
def row21:OrdinaryBounds.Source 2314 2411:=
  ⟨src21,⟨Research6969.PackedRanks.TerminalRanks32To35.rank34 22261, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover21⟩⟩
def row22:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src60,⟨Research6969.PackedRanks.TerminalRanks28To31.rank31 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover60⟩⟩
private def src23:PhysicalWindow.Request := ⟨⟨⟨2300,3207,724,25043⟩,377903408742400,3001726552718⟩,63,2,1,257319,48⟩
private theorem shift23_2314 : (PhysicalWindow.Triangular src23) 2314 2323 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift23_2324 : (PhysicalWindow.Triangular src23) 2324 2351 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift23_2352 : (PhysicalWindow.Triangular src23) 2352 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover23 : PhysicalWindow.Cover (PhysicalWindow.Triangular src23) 2411 2314 [2323, 2351, 2411] := by
  exact ⟨by decide, by decide, shift23_2314, by decide, by decide, shift23_2324, by decide, by decide, shift23_2352, rfl⟩
def row23:OrdinaryBounds.Source 2314 2411:=
  ⟨src23,⟨Research6969.PackedRanks.TerminalRanks32To35.rank32 25043, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover23⟩⟩
def row24:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src67,⟨Research6969.PackedRanks.TerminalRanks64To67.rank66 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover67⟩⟩
def row25:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src78,⟨Research6969.PackedRanks.TerminalRanks44To47.rank45 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover78⟩⟩
private def src26:PhysicalWindow.Request := ⟨⟨⟨2600,3625,819,25043⟩,546063062138880,4901614794409⟩,85,2,1,257319,57⟩
private theorem shift26_2314 : (PhysicalWindow.Triangular src26) 2314 2330 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift26_2331 : (PhysicalWindow.Triangular src26) 2331 2378 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift26_2379 : (PhysicalWindow.Triangular src26) 2379 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover26 : PhysicalWindow.Cover (PhysicalWindow.Triangular src26) 2411 2314 [2330, 2378, 2411] := by
  exact ⟨by decide, by decide, shift26_2314, by decide, by decide, shift26_2331, by decide, by decide, shift26_2379, rfl⟩
def row26:OrdinaryBounds.Source 2314 2411:=
  ⟨src26,⟨Research6969.TransitionBanks.rank263 25043, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover26⟩⟩
def row27:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src84,⟨Research6969.PackedRanks.TerminalRanks28To31.rank31 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover84⟩⟩
private def src28:PhysicalWindow.Request := ⟨⟨⟨2300,3207,724,25043⟩,377903408742400,3001726552718⟩,85,2,1,257319,61⟩
private theorem shift28_2314 : (PhysicalWindow.Triangular src28) 2314 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift28_2327 : (PhysicalWindow.Triangular src28) 2327 2362 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift28_2363 : (PhysicalWindow.Triangular src28) 2363 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover28 : PhysicalWindow.Cover (PhysicalWindow.Triangular src28) 2411 2314 [2326, 2362, 2411] := by
  exact ⟨by decide, by decide, shift28_2314, by decide, by decide, shift28_2327, by decide, by decide, shift28_2363, rfl⟩
def row28:OrdinaryBounds.Source 2314 2411:=
  ⟨src28,⟨Research6969.PackedRanks.TerminalRanks32To35.rank32 25043, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover28⟩⟩
def row29:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src86,⟨Research6969.PackedRanks.TerminalRanks64To67.rank64 35655, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover86⟩⟩
private def src30:PhysicalWindow.Request := ⟨⟨⟨2800,3903,882,31694⟩,681932636815360,6587245977411⟩,115,2,1,257319,65⟩
private theorem shift30_2314 : (PhysicalWindow.Triangular src30) 2314 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift30_2320 : (PhysicalWindow.Triangular src30) 2320 2336 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift30_2337 : (PhysicalWindow.Triangular src30) 2337 2383 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift30_2384 : (PhysicalWindow.Triangular src30) 2384 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover30 : PhysicalWindow.Cover (PhysicalWindow.Triangular src30) 2411 2314 [2319, 2336, 2383, 2411] := by
  exact ⟨by decide, by decide, shift30_2314, by decide, by decide, shift30_2320, by decide, by decide, shift30_2337, by decide, by decide, shift30_2384, rfl⟩
def row30:OrdinaryBounds.Source 2314 2411:=
  ⟨src30,⟨Research6969.PackedRanks.TerminalRanks64To67.rank65 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover30⟩⟩
private def src31:PhysicalWindow.Request := ⟨⟨⟨2300,3206,724,31694⟩,377903408742400,2998712046218⟩,115,2,1,257319,81⟩
private theorem shift31_2314 : (PhysicalWindow.Triangular src31) 2314 2316 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift31_2317 : (PhysicalWindow.Triangular src31) 2317 2324 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift31_2325 : (PhysicalWindow.Triangular src31) 2325 2347 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift31_2348 : (PhysicalWindow.Triangular src31) 2348 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover31 : PhysicalWindow.Cover (PhysicalWindow.Triangular src31) 2411 2314 [2316, 2324, 2347, 2411] := by
  exact ⟨by decide, by decide, shift31_2314, by decide, by decide, shift31_2317, by decide, by decide, shift31_2325, by decide, by decide, shift31_2348, rfl⟩
def row31:OrdinaryBounds.Source 2314 2411:=
  ⟨src31,⟨Research6969.PackedRanks.TerminalRanks28To31.rank29 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover31⟩⟩
end Research6969.OrdSource
end Z6969Source0900

-- Source: Research6969.PhysicalChecks007
section Z6969Source0901
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src100 : Request := ⟨⟨⟨1000,1391,305,54645⟩,30406634373120,104212783664⟩,115,2,1,257319,4097⟩
theorem cover100 : PhysicalWindow.Cover (PhysicalWindow.Triangular src100) 2411 2314 [2323, 2353, 2411] := triangleCover (by decide +kernel)
def src101 : Request := ⟨⟨⟨2800,3896,812,154121⟩,640331821875200,6140432144913⟩,325,2,1,257319,4097⟩
theorem cover101 : PhysicalWindow.Cover (PhysicalWindow.Triangular src101) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src102 : Request := ⟨⟨⟨2000,2782,610,175105⟩,242679148707840,1662397981334⟩,250,2,1,257319,8193⟩
theorem cover102 : PhysicalWindow.Cover (PhysicalWindow.Triangular src102) 2411 2314 [2319, 2336, 2384, 2411] := triangleCover (by decide +kernel)
def src103 : Request := ⟨⟨⟨1200,1669,366,119707⟩,52501327642624,215795999824⟩,150,2,1,257319,32769⟩
theorem cover103 : PhysicalWindow.Cover (PhysicalWindow.Triangular src103) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src104 : Request := ⟨⟨⟨2800,3905,882,32533⟩,681932636815360,6598128215989⟩,85,2,1,278103,49⟩
theorem cover104 : PhysicalWindow.Cover (PhysicalWindow.Triangular src104) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src105 : Request := ⟨⟨⟨2800,3905,882,35655⟩,681932636815360,6598128215989⟩,85,2,1,278103,49⟩
theorem cover105 : PhysicalWindow.Cover (PhysicalWindow.Triangular src105) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
def src106 : Request := ⟨⟨⟨2300,3207,724,31694⟩,377903408742400,3001726552718⟩,85,2,1,283522,58⟩
theorem cover106 : PhysicalWindow.Cover (PhysicalWindow.Triangular src106) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src107 : Request := ⟨⟨⟨2600,3625,793,24201⟩,532875289296896,4780245027563⟩,85,2,1,283522,58⟩
theorem cover107 : PhysicalWindow.Cover (PhysicalWindow.Triangular src107) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src108 : Request := ⟨⟨⟨2300,3207,724,21893⟩,377903408742400,3001726552718⟩,63,2,1,285209,49⟩
theorem cover108 : PhysicalWindow.Cover (PhysicalWindow.Triangular src108) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src109 : Request := ⟨⟨⟨2800,3905,882,35655⟩,681932636815360,6598128215989⟩,85,2,1,285209,49⟩
theorem cover109 : PhysicalWindow.Cover (PhysicalWindow.Triangular src109) 2411 2314 [2322, 2347, 2411] := triangleCover (by decide +kernel)
def src110 : Request := ⟨⟨⟨2600,3625,793,31694⟩,532875289296896,4780245027563⟩,85,2,1,285209,53⟩
theorem cover110 : PhysicalWindow.Cover (PhysicalWindow.Triangular src110) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
def src111 : Request := ⟨⟨⟨2600,3625,819,27578⟩,546063062138880,4901614794409⟩,85,2,1,285209,53⟩
theorem cover111 : PhysicalWindow.Cover (PhysicalWindow.Triangular src111) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src112 : Request := ⟨⟨⟨2600,3625,793,31694⟩,532875289296896,4780245027563⟩,85,2,1,287630,53⟩
theorem cover112 : PhysicalWindow.Cover (PhysicalWindow.Triangular src112) 2411 2314 [2319, 2336, 2384, 2411] := triangleCover (by decide +kernel)
def src113 : Request := ⟨⟨⟨2600,3625,819,27493⟩,546063062138880,4901614794409⟩,85,2,1,287630,53⟩
theorem cover113 : PhysicalWindow.Cover (PhysicalWindow.Triangular src113) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src114 : Request := ⟨⟨⟨2800,3905,882,31471⟩,681932636815360,6598128215989⟩,85,2,1,288407,49⟩
theorem cover114 : PhysicalWindow.Cover (PhysicalWindow.Triangular src114) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src115 : Request := ⟨⟨⟨2800,3905,882,31694⟩,681932636815360,6598128215989⟩,85,2,1,288407,49⟩
theorem cover115 : PhysicalWindow.Cover (PhysicalWindow.Triangular src115) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0901

-- Source: Research6969.TerminalRanks12To15
section Z6969Source0902
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks12To15
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment2439_551 : P1_7_1.groupedPoleMoment 2439 551 ≤ 1005558840057 :=
  _root_.PoleAffine6970.certified 2439 551 1005558840057 (by decide) (by decide +kernel)

theorem moment2440_534 : P1_7_1.groupedPoleMoment 2440 534 ≤ 982675143308 :=
  _root_.PoleAffine6970.certified 2440 534 982675143308 (by decide) (by decide +kernel)

theorem moment2782_596 : P1_7_1.groupedPoleMoment 2782 596 ≤ 1632591172707 :=
  _root_.PoleAffine6970.certified 2782 596 1632591172707 (by decide) (by decide +kernel)

theorem moment2782_610 : P1_7_1.groupedPoleMoment 2782 610 ≤ 1662397981334 :=
  _root_.PoleAffine6970.certified 2782 610 1662397981334 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks12To15

namespace Research6969.PackedRanks.TerminalRanks12To15
open Research6969.TerminalAuxBanks
theorem rank12 (u:ℕ) : P3_7_1.BankOK (bank12 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank12 u).shape (by change 2*551≤1750;decide) (by change 1750+551≤2439+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (1750-2*551) 551=6*166595992223744:=by decide
  change 6*P1_7_1.nodeRows (bank12 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank12 u).shape=262144*P1_7_1_2.sixPerNode (1750-2*551) 551 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank12 u).shape=166595992223744; omega, moment2439_551,by change 2439<K1.p;decide⟩
theorem rank13 (u:ℕ) : P3_7_1.BankOK (bank13 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank13 u).shape (by change 2*534≤1750;decide) (by change 1750+534≤2440+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (1750-2*534) 534=6*162688810352640:=by decide
  change 6*P1_7_1.nodeRows (bank13 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank13 u).shape=262144*P1_7_1_2.sixPerNode (1750-2*534) 534 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank13 u).shape=162688810352640; omega, moment2440_534,by change 2440<K1.p;decide⟩
theorem rank14 (u:ℕ) : P3_7_1.BankOK (bank14 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank14 u).shape (by change 2*596≤2000;decide) (by change 2000+596≤2782+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2000-2*596) 596=6*238428431581184:=by decide
  change 6*P1_7_1.nodeRows (bank14 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank14 u).shape=262144*P1_7_1_2.sixPerNode (2000-2*596) 596 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank14 u).shape=238428431581184; omega, moment2782_596,by change 2782<K1.p;decide⟩
theorem rank15 (u:ℕ) : P3_7_1.BankOK (bank15 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank15 u).shape (by change 2*610≤2000;decide) (by change 2000+610≤2782+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2000-2*610) 610=6*242679148707840:=by decide
  change 6*P1_7_1.nodeRows (bank15 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank15 u).shape=262144*P1_7_1_2.sixPerNode (2000-2*610) 610 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank15 u).shape=242679148707840; omega, moment2782_610,by change 2782<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks12To15
end Z6969Source0902

end Merged_Z6969Pack0651

-- merged module Z6969Pack0652
section Merged_Z6969Pack0652

-- Source: Research6969.TerminalRanks40To43
section Z6969Source0903
set_option autoImplicit true
namespace Research6969.PackedRanks.TerminalRanks40To43
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment3623_793 : P1_7_1.groupedPoleMoment 3623 793 ≤ 4771760428124 :=
  _root_.PoleAffine6970.certified 3623 793 4771760428124 (by decide) (by decide +kernel)

theorem moment3624_754 : P1_7_1.groupedPoleMoment 3624 754 ≤ 4591524798476 :=
  _root_.PoleAffine6970.certified 3624 754 4591524798476 (by decide) (by decide +kernel)

theorem moment3624_775 : P1_7_1.groupedPoleMoment 3624 775 ≤ 4691256264577 :=
  _root_.PoleAffine6970.certified 3624 775 4691256264577 (by decide) (by decide +kernel)

theorem moment3624_793 : P1_7_1.groupedPoleMoment 3624 793 ≤ 4776001446129 :=
  _root_.PoleAffine6970.certified 3624 793 4776001446129 (by decide) (by decide +kernel)

end Research6969.PackedRanks.TerminalRanks40To43

namespace Research6969.PackedRanks.TerminalRanks40To43
open Research6969.TerminalAuxBanks
theorem rank40 (u:ℕ) : P3_7_1.BankOK (bank40 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank40 u).shape (by change 2*793≤2600;decide) (by change 2600+793≤3623+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*793) 793=6*532875289296896:=by decide
  change 6*P1_7_1.nodeRows (bank40 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank40 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*793) 793 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank40 u).shape=532875289296896; omega, moment3623_793,by change 3623<K1.p;decide⟩
theorem rank41 (u:ℕ) : P3_7_1.BankOK (bank41 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank41 u).shape (by change 2*754≤2600;decide) (by change 2600+754≤3624+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*754) 754=6*512754163384320:=by decide
  change 6*P1_7_1.nodeRows (bank41 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank41 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*754) 754 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank41 u).shape=512754163384320; omega, moment3624_754,by change 3624<K1.p;decide⟩
theorem rank42 (u:ℕ) : P3_7_1.BankOK (bank42 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank42 u).shape (by change 2*775≤2600;decide) (by change 2600+775≤3624+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*775) 775=6*523640687820800:=by decide
  change 6*P1_7_1.nodeRows (bank42 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank42 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*775) 775 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank42 u).shape=523640687820800; omega, moment3624_775,by change 3624<K1.p;decide⟩
theorem rank43 (u:ℕ) : P3_7_1.BankOK (bank43 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank43 u).shape (by change 2*793≤2600;decide) (by change 2600+793≤3624+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (2600-2*793) 793=6*532875289296896:=by decide
  change 6*P1_7_1.nodeRows (bank43 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank43 u).shape=262144*P1_7_1_2.sixPerNode (2600-2*793) 793 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank43 u).shape=532875289296896; omega, moment3624_793,by change 3624<K1.p;decide⟩
end Research6969.PackedRanks.TerminalRanks40To43
end Z6969Source0903

-- Source: Research6969.OrdSource02
section Z6969Source0904
set_option autoImplicit true
namespace Research6969.OrdSource
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def row32:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src88,⟨Research6969.PackedRanks.TerminalRanks60To63.rank61 40111, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover88⟩⟩
private def src33:PhysicalWindow.Request := ⟨⟨⟨2800,3902,854,31694⟩,665461916958720,6418829718882⟩,150,2,1,257319,97⟩
private theorem shift33_2314 : (PhysicalWindow.Triangular src33) 2314 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift33_2318 : (PhysicalWindow.Triangular src33) 2318 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift33_2330 : (PhysicalWindow.Triangular src33) 2330 2363 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift33_2364 : (PhysicalWindow.Triangular src33) 2364 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover33 : PhysicalWindow.Cover (PhysicalWindow.Triangular src33) 2411 2314 [2317, 2329, 2363, 2411] := by
  exact ⟨by decide, by decide, shift33_2314, by decide, by decide, shift33_2318, by decide, by decide, shift33_2330, by decide, by decide, shift33_2364, rfl⟩
def row33:OrdinaryBounds.Source 2314 2411:=
  ⟨src33,⟨Research6969.PackedRanks.TerminalRanks60To63.rank62 31694, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover33⟩⟩
private def src34:PhysicalWindow.Request := ⟨⟨⟨1450,2020,432,25043⟩,90926432911360,453693330393⟩,85,2,1,257319,121⟩
private theorem shift34_2314 : (PhysicalWindow.Triangular src34) 2314 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift34_2318 : (PhysicalWindow.Triangular src34) 2318 2329 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift34_2330 : (PhysicalWindow.Triangular src34) 2330 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift34_2365 : (PhysicalWindow.Triangular src34) 2365 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover34 : PhysicalWindow.Cover (PhysicalWindow.Triangular src34) 2411 2314 [2317, 2329, 2364, 2411] := by
  exact ⟨by decide, by decide, shift34_2314, by decide, by decide, shift34_2318, by decide, by decide, shift34_2330, by decide, by decide, shift34_2365, rfl⟩
def row34:OrdinaryBounds.Source 2314 2411:=
  ⟨src34,⟨Research6969.PackedRanks.OrdRanks0To3.rank2 25043, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover34⟩⟩
private def src35:PhysicalWindow.Request := ⟨⟨⟨2600,3623,793,28173⟩,532875289296896,4771760428124⟩,150,2,1,257319,121⟩
private theorem shift35_2314 : (PhysicalWindow.Triangular src35) 2314 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift35_2327 : (PhysicalWindow.Triangular src35) 2327 2363 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift35_2364 : (PhysicalWindow.Triangular src35) 2364 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover35 : PhysicalWindow.Cover (PhysicalWindow.Triangular src35) 2411 2314 [2326, 2363, 2411] := by
  exact ⟨by decide, by decide, shift35_2314, by decide, by decide, shift35_2327, by decide, by decide, shift35_2364, rfl⟩
def row35:OrdinaryBounds.Source 2314 2411:=
  ⟨src35,⟨Research6969.PackedRanks.TerminalRanks40To43.rank40 28173, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover35⟩⟩
private def src36:PhysicalWindow.Request := ⟨⟨⟨2800,3901,834,45081⟩,653560508579840,6296101689637⟩,195,2,1,257319,161⟩
private theorem shift36_2314 : (PhysicalWindow.Triangular src36) 2314 2326 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift36_2327 : (PhysicalWindow.Triangular src36) 2327 2364 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift36_2365 : (PhysicalWindow.Triangular src36) 2365 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover36 : PhysicalWindow.Cover (PhysicalWindow.Triangular src36) 2411 2314 [2326, 2364, 2411] := by
  exact ⟨by decide, by decide, shift36_2314, by decide, by decide, shift36_2327, by decide, by decide, shift36_2365, rfl⟩
def row36:OrdinaryBounds.Source 2314 2411:=
  ⟨src36,⟨Research6969.PackedRanks.OrdRanks4To5.rank5 45081, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover36⟩⟩
def row37:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src92,⟨Research6969.PackedRanks.TerminalRanks24To27.rank24 50764, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover92⟩⟩
private def src38:PhysicalWindow.Request := ⟨⟨⟨3000,4178,894,64247⟩,804053213511680,8288484232853⟩,250,2,1,257319,257⟩
private theorem shift38_2314 : (PhysicalWindow.Triangular src38) 2314 2319 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift38_2320 : (PhysicalWindow.Triangular src38) 2320 2337 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift38_2338 : (PhysicalWindow.Triangular src38) 2338 2388 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift38_2389 : (PhysicalWindow.Triangular src38) 2389 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover38 : PhysicalWindow.Cover (PhysicalWindow.Triangular src38) 2411 2314 [2319, 2337, 2388, 2411] := by
  exact ⟨by decide, by decide, shift38_2314, by decide, by decide, shift38_2320, by decide, by decide, shift38_2338, by decide, by decide, shift38_2389, rfl⟩
def row38:OrdinaryBounds.Source 2314 2411:=
  ⟨src38,⟨Research6969.PackedRanks.TerminalRanks72To75.rank75 64247, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover38⟩⟩
private def src39:PhysicalWindow.Request := ⟨⟨⟨2600,3620,775,63811⟩,523640687820800,4674619806217⟩,250,2,1,257319,513⟩
private theorem shift39_2314 : (PhysicalWindow.Triangular src39) 2314 2321 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift39_2322 : (PhysicalWindow.Triangular src39) 2322 2344 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift39_2345 : (PhysicalWindow.Triangular src39) 2345 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover39 : PhysicalWindow.Cover (PhysicalWindow.Triangular src39) 2411 2314 [2321, 2344, 2411] := by
  exact ⟨by decide, by decide, shift39_2314, by decide, by decide, shift39_2322, by decide, by decide, shift39_2345, rfl⟩
def row39:OrdinaryBounds.Source 2314 2411:=
  ⟨src39,⟨Research6969.PackedRanks.TerminalRanks36To39.rank38 63811, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover39⟩⟩
def row40:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src96,⟨Research6969.PackedRanks.TerminalRanks20To23.rank23 79852, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover96⟩⟩
private def src41:PhysicalWindow.Request := ⟨⟨⟨3000,4175,894,127905⟩,804053213511680,8269353083383⟩,325,2,1,257319,1025⟩
private theorem shift41_2314 : (PhysicalWindow.Triangular src41) 2314 2317 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift41_2318 : (PhysicalWindow.Triangular src41) 2318 2328 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift41_2329 : (PhysicalWindow.Triangular src41) 2329 2360 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift41_2361 : (PhysicalWindow.Triangular src41) 2361 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover41 : PhysicalWindow.Cover (PhysicalWindow.Triangular src41) 2411 2314 [2317, 2328, 2360, 2411] := by
  exact ⟨by decide, by decide, shift41_2314, by decide, by decide, shift41_2318, by decide, by decide, shift41_2329, by decide, by decide, shift41_2361, rfl⟩
def row41:OrdinaryBounds.Source 2314 2411:=
  ⟨src41,⟨Research6969.PackedRanks.TerminalRanks72To75.rank74 127905, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover41⟩⟩
def row42:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src99,⟨Research6969.PackedRanks.TerminalRanks56To59.rank57 112233, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover99⟩⟩
def row43:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src100,⟨Research6969.PackedRanks.TerminalRanks0To3.rank2 54645, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover100⟩⟩
def row44:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src102,⟨Research6969.PackedRanks.TerminalRanks12To15.rank15 175105, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover102⟩⟩
private def src45:PhysicalWindow.Request := ⟨⟨⟨1200,1669,378,121332⟩,53798525730816,221264762670⟩,150,2,1,257319,16385⟩
private theorem shift45_2314 : (PhysicalWindow.Triangular src45) 2314 2318 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift45_2319 : (PhysicalWindow.Triangular src45) 2319 2332 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift45_2333 : (PhysicalWindow.Triangular src45) 2333 2373 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift45_2374 : (PhysicalWindow.Triangular src45) 2374 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover45 : PhysicalWindow.Cover (PhysicalWindow.Triangular src45) 2411 2314 [2318, 2332, 2373, 2411] := by
  exact ⟨by decide, by decide, shift45_2314, by decide, by decide, shift45_2319, by decide, by decide, shift45_2333, by decide, by decide, shift45_2374, rfl⟩
def row45:OrdinaryBounds.Source 2314 2411:=
  ⟨src45,⟨Research6969.PackedRanks.OrdRanks0To3.rank1 121332, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover45⟩⟩
def row46:OrdinaryBounds.Source 2314 2411:=
  ⟨PhysicalCatalogue.src103,⟨Research6969.PackedRanks.TerminalRanks0To3.rank3 119707, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,PhysicalCatalogue.cover103⟩⟩
private def src47:PhysicalWindow.Request := ⟨⟨⟨2800,3907,854,45124⟩,665461916958720,6445344460182⟩,22,2,1,299354,27⟩
private theorem shift47_2314 : (PhysicalWindow.Triangular src47) 2314 2315 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift47_2316 : (PhysicalWindow.Triangular src47) 2316 2321 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift47_2322 : (PhysicalWindow.Triangular src47) 2322 2338 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift47_2339 : (PhysicalWindow.Triangular src47) 2339 2385 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem shift47_2386 : (PhysicalWindow.Triangular src47) 2386 2411 := Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel)
private theorem cover47 : PhysicalWindow.Cover (PhysicalWindow.Triangular src47) 2411 2314 [2315, 2321, 2338, 2385, 2411] := by
  exact ⟨by decide, by decide, shift47_2314, by decide, by decide, shift47_2316, by decide, by decide, shift47_2322, by decide, by decide, shift47_2339, by decide, by decide, shift47_2386, rfl⟩
def row47:OrdinaryBounds.Source 2314 2411:=
  ⟨src47,⟨Research6969.PackedRanks.TerminalRanks72To75.rank72 45124, by unfold Research6966.TerminalBanks.inside;decide +kernel,
   by decide,rfl,by decide,by decide,by decide,by unfold Lower6960.HelperSource.WidthGuard;decide +kernel⟩,
   ⟨_,cover47⟩⟩
end Research6969.OrdSource
end Z6969Source0904

-- Source: Research6969.PhysicalChecks017
section Z6969Source0905
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1144 : Request := ⟨⟨⟨2300,3207,702,27559⟩,369170633195520,2930605494152⟩,85,3,1,385979,57⟩
theorem cover1144 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1144) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src1145 : Request := ⟨⟨⟨2300,3207,702,28173⟩,369170633195520,2930605494152⟩,85,3,1,385979,57⟩
theorem cover1145 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1145) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src1146 : Request := ⟨⟨⟨2000,2788,630,28173⟩,248682526801920,1716449496361⟩,85,3,1,385979,65⟩
theorem cover1146 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1146) 2411 2314 [2322, 2348, 2411] := triangleCover (by decide +kernel)
def src1147 : Request := ⟨⟨⟨2800,3903,854,30071⟩,665461916958720,6424126719762⟩,115,3,1,385979,65⟩
theorem cover1147 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1147) 2411 2314 [2314, 2317, 2326, 2351, 2411] := triangleCover (by decide +kernel)
def src1148 : Request := ⟨⟨⟨2000,2787,630,31694⟩,248682526801920,1714466862180⟩,115,3,1,385979,97⟩
theorem cover1148 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1148) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src1149 : Request := ⟨⟨⟨2600,3623,819,34180⟩,546063062138880,4892906717079⟩,150,3,1,385979,97⟩
theorem cover1149 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1149) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src1150 : Request := ⟨⟨⟨1750,2438,551,28225⟩,166595992223744,1004231319985⟩,115,3,1,385979,129⟩
theorem cover1150 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1150) 2411 2314 [2319, 2336, 2384, 2411] := triangleCover (by decide +kernel)
def src1151 : Request := ⟨⟨⟨2300,3204,702,32557⟩,369170633195520,2921790084349⟩,150,3,1,385979,129⟩
theorem cover1151 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1151) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src1152 : Request := ⟨⟨⟨2300,3203,702,50764⟩,369170633195520,2918855628076⟩,195,3,1,385979,257⟩
theorem cover1152 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1152) 2411 2314 [2323, 2352, 2411] := triangleCover (by decide +kernel)
def src1153 : Request := ⟨⟨⟨3000,4178,894,57690⟩,804053213511680,8288484232853⟩,250,3,1,385979,257⟩
theorem cover1153 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1153) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src1154 : Request := ⟨⟨⟨1200,1670,378,35412⟩,53798525730816,221692026804⟩,115,3,1,385979,513⟩
theorem cover1154 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1154) 2411 2314 [2323, 2352, 2411] := triangleCover (by decide +kernel)
def src1155 : Request := ⟨⟨⟨2600,3620,775,60527⟩,523640687820800,4674619806217⟩,250,3,1,385979,513⟩
theorem cover1155 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1155) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src1156 : Request := ⟨⟨⟨2300,3201,702,79852⟩,369170633195520,2912992731804⟩,250,3,1,385979,1025⟩
theorem cover1156 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1156) 2411 2314 [2322, 2347, 2411] := triangleCover (by decide +kernel)
def src1157 : Request := ⟨⟨⟨3000,4175,894,114478⟩,804053213511680,8269353083383⟩,325,3,1,385979,1025⟩
theorem cover1157 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1157) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src1158 : Request := ⟨⟨⟨1750,2435,522,70068⟩,159899889172480,959076692411⟩,195,3,1,385979,2049⟩
theorem cover1158 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1158) 2411 2314 [2328, 2372, 2411] := triangleCover (by decide +kernel)
def src1159 : Request := ⟨⟨⟨2800,3896,854,107556⟩,665461916958720,6387110095257⟩,325,3,1,385979,2049⟩
theorem cover1159 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1159) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0905

end Merged_Z6969Pack0652
